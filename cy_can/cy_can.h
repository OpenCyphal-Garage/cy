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

#ifdef __cplusplus
extern "C"
{
#endif

/// A received CAN frame (classic or FD).
typedef struct
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

    /// Returns the current monotonic time in microseconds. Must be non-negative and non-decreasing.
    cy_us_t (*now)(void* user);

    /// Standard realloc semantics; if size is zero, the call shall behave as free.
    void* (*realloc)(void* user, void* ptr, size_t size);

    /// Returns a random 64-bit unsigned integer. See cy_platform_vtable_t for the seeding recommendations.
    uint64_t (*random)(void* user);
} cy_can_vtable_t;

/// Diagnostic statistics sampled from both cy_can and the underlying libcanard instance.
typedef struct
{
    size_t   subject_writer_count;
    size_t   subject_reader_count;
    uint64_t v10_rx_count; ///< 13-bit (v1.0) transfers received.
    uint64_t v11_rx_count; ///< 16-bit (v1.1) transfers received.
    uint64_t oom_count;    ///< cy_can-level OOM (message wrapper allocation failures, etc.).
    // Canard-level counters.
    uint64_t canard_err_oom;
    uint64_t canard_err_tx_capacity;
    uint64_t canard_err_tx_sacrifice;
    uint64_t canard_err_tx_expiration;
    uint64_t canard_err_rx_frame;
    uint64_t canard_err_rx_transfer;
    uint64_t canard_err_collision;
} cy_can_stats_t;

/// Create a new CAN platform instance. Node-ID is allocated automatically via libcanard occupancy tracking.
/// Returns NULL on failure. The iface_count must be in [1, CANARD_IFACE_COUNT].
cy_platform_t* cy_can_new(const uint_least8_t          iface_count,
                          const size_t                 tx_queue_capacity,
                          const cy_can_vtable_t* const vtable,
                          void* const                  user);

cy_can_stats_t cy_can_stats(const cy_platform_t* const base);

/// Returns the user context pointer that was passed to cy_can_new().
void* cy_can_user(const cy_platform_t* const base);

/// Requires the Cy instance to be unlinked first and all Cy-allocated resources freed.
void cy_can_destroy(cy_platform_t* const base);

#ifdef __cplusplus
}
#endif
