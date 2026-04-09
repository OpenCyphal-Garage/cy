//                            ____                   ______            __          __
//                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
//                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
//                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
//                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
//                             /_/                     /____/_/
//
// A Cy platform layer for Cyphal/CAN with v1.0 interoperability.
// This module is fully platform-agnostic; platform I/O is delegated to the cy_can_vtable_t provided by the user.
//
// See cy_can_socketcan.h for a Linux SocketCAN implementation of the vtable.
// Baremetal/RTOS-based platforms are expected to provide their own vtable implementations, perhaps using the GNU/Linux
// implementation as a reference.
//
// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#pragma once

#include <cy.h>
#include <canard.h>

#ifdef __cplusplus
extern "C"
{
#endif

/// A received CAN frame (classic or FD).
typedef struct cy_can_rx_t
{
    cy_us_t       timestamp;   ///< Monotonic reception timestamp in microseconds, in cy_can_vtable_t::now() timebase.
    uint32_t      can_id;      ///< 29-bit extended CAN ID.
    uint_least8_t iface_index; ///< The redundant interface the frame was received from.
    uint_least8_t len;         ///< Data length: 0-8 for classic CAN, 0-64 for CAN FD.
    bool          fd;          ///< True if this is a CAN FD frame.
    uint_least8_t data[64];
} cy_can_rx_t;

/// Platform-specific CAN driver abstraction. A single vtable manages ALL redundant interfaces.
/// All functions are non-blocking except rx(), which may block up to the specified deadline.
typedef struct
{
    /// Transmit a classic CAN frame (up to 8 bytes) on the given interface.
    /// Returns true if the frame should be removed from the upstream TX queue (i.e., if the frame was accepted
    /// for transmission or if it encountered a fatal failure and no further attempts are needed).
    /// Returns false if the underlying CAN controller is not ready to accept a new frame (e.g., no free TX mailbox);
    /// the caller will retry later.
    bool (*tx_classic)(void* user, uint_least8_t iface_index, uint32_t can_id, const void* data, uint_least8_t len);

    /// Transmit a CAN FD frame (up to 64 bytes) on the given interface.
    /// Set to NULL if the underlying driver does not support CAN FD; all interfaces share the same FD capability.
    bool (*tx_fd)(void* user, uint_least8_t iface_index, uint32_t can_id, const void* data, uint_least8_t len);

    /// Poll all redundant interfaces for a received frame. Returns true if a frame was received.
    /// The implementation may block up to the given deadline; baremetal implementations may ignore the deadline
    /// and return immediately if no frame is available.
    /// The tx_pending_iface_bitmap indicates which interfaces have pending TX frames; the implementation should
    /// also unblock when any of those interfaces become writable, to allow the caller to retry transmissions.
    bool (*rx)(void* user, cy_can_rx_t* out_frame, cy_us_t deadline, uint_least8_t tx_pending_iface_bitmap);

    /// Replace the hardware acceptance filter configuration with the supplied filter set.
    /// This callback is optional; if NULL, libcanard filtering is disabled even if filter_count passed to cy_can_new()
    /// is nonzero. The callback is only invoked from cy_spin...().
    bool (*filter)(void* user, size_t filter_count, const canard_filter_t* filters);

    /// Returns the current monotonic time in microseconds. Must be non-negative and non-decreasing.
    cy_us_t (*now)(void* user);

    /// Standard realloc semantics; if size is zero, the call shall behave as free.
    void* (*realloc)(void* user, void* ptr, size_t size);
} cy_can_vtable_t;

/// Create a new CAN platform instance. The node-ID will be allocated automatically by libcanard.
/// The constructor will invoke vtable realloc() immediately.
///
/// The filter_count is the number of acceptance filters available to libcanard; pass zero to disable filtering.
/// Filtering is also disabled if vtable->filter is NULL.
///
/// The PRNG seed must be distinct across reboots in quick succession, and it should be hashed with the node's UID,
/// such that distinct nodes are likely to have distinct seed, and the same node after a reboot starts with a new seed.
/// See cy_platform_vtable_t documentation for recommendations on how to implement PRNG seeding on an embedded system.
///
/// Returns NULL on failure. The iface_count must be in [1, CANARD_IFACE_COUNT].
cy_platform_t* cy_can_new(const uint_least8_t          iface_count,
                          const size_t                 tx_queue_capacity,
                          const size_t                 filter_count,
                          const uint64_t               prng_seed,
                          const cy_can_vtable_t* const vtable,
                          void* const                  user);

/// Returns the user context pointer that was passed to cy_can_new().
void* cy_can_user(const cy_platform_t* const base);

/// Requires the Cy instance to be unlinked first and all Cy-allocated resources freed.
void cy_can_destroy(cy_platform_t* const base);

// =====================================================================================================================
//                                      LEGACY UAVCAN V0 / DRONECAN WIRE COMPATIBILITY API
// =====================================================================================================================

// This is a compact sidecar API that is not part of the main stack, used only to provide limited interoperability
// with legacy UAVCAN v0 / DroneCAN nodes. It runs as part of the main event loop.

typedef struct cy_can_v0_subscription_t cy_can_v0_subscription_t;

/// Callback for legacy UAVCAN v0 / DroneCAN message transfers.
/// The payload expires upon return and is always single-fragment: payload.next==NULL.
typedef void (*cy_can_v0_on_transfer_t)(cy_can_v0_subscription_t* const subscription,
                                        const cy_us_t                   timestamp,
                                        const cy_prio_t                 priority,
                                        const uint_least8_t             source_node_id,
                                        const uint_least8_t             transfer_id,
                                        const cy_bytes_t                payload);

/// Register a legacy UAVCAN v0 / DroneCAN message subscription on the local cy_can instance.
/// The platform must originate from cy_can_new(); to progress transfers, spin the attached Cy instance regularly.
///
/// The extent is the maximum application payload size in bytes, excluding the legacy transfer CRC.
/// The transfer-ID timeout may be negative, in which case the default timeout from libcanard is used.
///
/// At most one local v0 message subscription may exist for a given data type ID. Returns NULL on invalid arguments,
/// duplicate local subscription, or memory exhaustion.
cy_can_v0_subscription_t* cy_can_v0_subscribe(cy_platform_t* const base,
                                              const uint16_t       data_type_id,
                                              const uint16_t       crc_seed,
                                              const size_t         extent,
                                              const cy_us_t        transfer_id_timeout);

/// Application-owned arbitrary context shared with the callback.
/// Safe to invoke with NULL: returns CY_USER_CONTEXT_EMPTY or has no effect.
cy_user_context_t cy_can_v0_subscription_context(const cy_can_v0_subscription_t* const subscription);
void cy_can_v0_subscription_context_set(cy_can_v0_subscription_t* const subscription, const cy_user_context_t context);

/// Optional callback invoked when a matching transfer is received.
cy_can_v0_on_transfer_t cy_can_v0_subscription_callback(const cy_can_v0_subscription_t* const subscription);
void                    cy_can_v0_subscription_callback_set(cy_can_v0_subscription_t* const subscription,
                                                            const cy_can_v0_on_transfer_t   callback);

/// Destroy a v0 message subscription. No effect if the pointer is NULL.
void cy_can_v0_unsubscribe(cy_can_v0_subscription_t* const self);

/// Publish a legacy UAVCAN v0 / DroneCAN message transfer.
/// The CRC seed is relevant only for multi-frame transfers; it can be derived from the data type signature using
/// canard_v0_crc_seed_from_data_type_signature().
/// Returns CY_OK, CY_ERR_MEMORY, CY_ERR_CAPACITY, or CY_ERR_ARGUMENT.
cy_err_t cy_can_v0_publish(cy_platform_t* const base,
                           const cy_us_t        deadline,
                           const cy_prio_t      priority,
                           const uint16_t       data_type_id,
                           const uint16_t       crc_seed,
                           const uint_least8_t  transfer_id,
                           const cy_bytes_t     payload);

#ifdef __cplusplus
}
#endif
