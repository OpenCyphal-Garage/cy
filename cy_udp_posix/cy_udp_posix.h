///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// A Cy platform layer for POSIX-like OSes using standard BSD sockets and libUDPard for Cyphal over UDP.
/// It can be adapted for other socket-based APIs with minimal changes.
///
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#pragma once

#include "udp_wrapper.h"
#include <cy_platform.h>
#include <udpard.h>

#ifdef __cplusplus
extern "C"
{
#endif

#define CY_UDP_POSIX_IFACE_COUNT_MAX UDPARD_IFACE_COUNT_MAX

typedef struct cy_udp_posix_t       cy_udp_posix_t;
typedef struct cy_udp_posix_topic_t cy_udp_posix_topic_t;

struct cy_udp_posix_t
{
    cy_t                 base;
    size_t               n_topics;
    udpard_mem_t         mem;
    udpard_tx_t          udpard_tx;
    udpard_rx_t          udpard_rx;
    udpard_rx_port_p2p_t p2p_port;
    udp_wrapper_t        sock[CY_UDP_POSIX_IFACE_COUNT_MAX]; ///< All TX and P2P RX.
    uint32_t             local_ip[CY_UDP_POSIX_IFACE_COUNT_MAX];
    uint16_t             local_tx_port[CY_UDP_POSIX_IFACE_COUNT_MAX];
    uint16_t             iface_bitmap; ///< Bitmap of valid interfaces based on local_ip[].
    uint64_t             prng_state;

    /// Handler for errors occurring while reading from the socket of the topic on the specified iface.
    /// The default handler is provided which will use CY_TRACE() to report the error.
    /// This is used to initialize the corresponding field in cy_udp_posix_topic_t when a new topic is created.
    /// This is also used to report RX socket errors for P2P transfers with the topic set to NULL.
    /// Changes to this handler will not affect existing topics.
    void (*rx_sock_err_handler)(cy_udp_posix_t*       cy,
                                cy_udp_posix_topic_t* topic,
                                uint_fast8_t          iface_index,
                                uint32_t              err_no);

    /// Handler for errors occurring while writing into a tx socket on the specified iface.
    /// These are platform-specific.
    /// The default handler is provided which will use CY_TRACE() to report the error.
    void (*tx_sock_err_handler)(cy_udp_posix_t* cy, uint_fast8_t iface_index, uint32_t err_no);

    size_t   mem_allocated_fragments;
    size_t   mem_allocated_bytes;
    uint64_t mem_oom_count;
};

/// A simple helper that returns monotonic time in microseconds. The time value is always non-negative.
cy_us_t cy_udp_posix_now(void);

/// If the namespace is NULL or empty, the value from CYPHAL_NAMESPACE environment variable is used;
/// if the environment variable is also not set, it defaults to an empty string.
///
/// The home may be empty, in which case it defaults to the UID in zero-padded lowercase hex; e.g., `0000000000abcdef`.
///
/// Unused interfaces should have zero addresses; to parse IP address strings see udp_wrapper_parse_iface_address().
cy_err_t cy_udp_posix_new(cy_udp_posix_t* const cy,
                          const uint64_t        uid,
                          const wkv_str_t       home,
                          const wkv_str_t       namespace_,
                          const uint32_t        local_iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX],
                          const size_t          tx_queue_capacity);

/// A shortcut constructor helper that automatically assigns the node parameters that fit most applications:
/// - A semi-random EUI-64: a few of the most-significant bits are host-specific, the rest are random.
/// - The home name is set to hex UID (16 lowercase hex digits).
/// - The namespace is read from the CYPHAL_NAMESPACE environment variable; if not set, empty namespace is used.
/// - The local interfaces are chosen per the defaults configured on the local system.
/// - The TX queue capacity is set to a reasonable large value.
cy_err_t cy_udp_posix_new_simple(cy_udp_posix_t* const cy);

/// Keep running the event loop until the deadline is reached or until the first error.
/// If the deadline is not in the future, the function will process pending events once and return without blocking.
/// If the deadline is in the future and there are currently no events to process, the function will block until the
/// deadline is reached or until an event arrives. The function may return early even if no events are available.
/// The current monotonic time is as defined in cy_udp_posix_now().
cy_err_t cy_udp_posix_spin_until(cy_udp_posix_t* const cy, const cy_us_t deadline);

/// Wait for events (blocking), process them, and return. Invoke this in a tight superloop to maintain liveness.
/// The function is guaranteed to return no later than in the heartbeat period, or in a few ms, whichever is sooner.
cy_err_t cy_udp_posix_spin_once(cy_udp_posix_t* const cy);

void cy_udp_posix_destroy(cy_udp_posix_t* const cy);

#ifdef __cplusplus
}
#endif
