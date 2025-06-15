///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#pragma once

#include "udp_wrapper.h"
#include <cy_platform.h>
#include <udpard.h>

#define CY_UDP_POSIX_IFACE_COUNT_MAX           UDPARD_NETWORK_INTERFACE_COUNT_MAX
#define CY_UDP_POSIX_NODE_ID_BLOOM_64BIT_WORDS 128

struct cy_udp_posix_t;

struct cy_udp_posix_topic_t
{
    struct cy_topic_t           base;
    struct UdpardRxSubscription sub;
    struct udp_wrapper_rx_t     sock_rx[CY_UDP_POSIX_IFACE_COUNT_MAX];

    /// The count of out-of-memory errors that occurred while processing this topic.
    /// Every OOM implies that either a frame or a full transfer were lost.
    uint64_t rx_oom_count;

    /// Initialized from the eponymous field of cy_udp_posix_t when a new topic is created.
    void (*rx_sock_err_handler)(struct cy_udp_posix_t*       cy_udp,
                                struct cy_udp_posix_topic_t* topic,
                                uint_fast8_t                 iface_index,
                                uint32_t                     err_no);
};

struct cy_udp_posix_t
{
    struct cy_t base;

    /// Maximum seen value across all topics since initialization.
    size_t response_extent_with_overhead;

    uint64_t            node_id_bloom_storage[CY_UDP_POSIX_NODE_ID_BLOOM_64BIT_WORDS];
    struct cy_bloom64_t node_id_bloom;

    struct UdpardMemoryResource    mem;
    struct UdpardRxMemoryResources rx_mem;

    struct UdpardRxRPCDispatcher rpc_rx_dispatcher;
    struct UdpardRxRPCPort       rpc_rx_port_topic_response;

    uint32_t local_iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX];

    struct
    {
        struct UdpardTx         udpard_tx;
        struct udp_wrapper_tx_t sock;
        uint16_t                local_port;
        uint64_t                frames_expired; ///< Number of tx frames that have timed out while waiting in the queue.
    } tx[CY_UDP_POSIX_IFACE_COUNT_MAX];

    struct
    {
        struct udp_wrapper_rx_t sock;
        /// The count of out-of-memory errors that occurred while reading from this socket.
        /// Every OOM implies that either a frame or a full transfer were lost.
        uint64_t oom_count;
    } rpc_rx[CY_UDP_POSIX_IFACE_COUNT_MAX];

    /// Handler for errors occurring while reading from the socket of the topic on the specified iface.
    /// The default handler is provided which will use CY_TRACE() to report the error.
    /// This is only used to initialize the corresponding field of cy_udp_posix_topic_t when a new topic is created.
    /// Changes to this handler will not affect existing topics.
    void (*rx_sock_err_handler)(struct cy_udp_posix_t*       cy_udp,
                                struct cy_udp_posix_topic_t* topic,
                                uint_fast8_t                 iface_index,
                                uint32_t                     err_no);

    /// Handler for errors occurring while writing into a tx socket on the specified iface.
    /// These are platform-specific.
    /// The default handler is provided which will use CY_TRACE() to report the error.
    void (*tx_sock_err_handler)(struct cy_udp_posix_t* cy_udp, uint_fast8_t iface_index, uint32_t err_no);

    /// Handler for errors occurring while reading from an RPC RX socket on the specified iface.
    /// These are platform-specific.
    /// The default handler is provided which will use CY_TRACE() to report the error.
    void (*rpc_rx_sock_err_handler)(struct cy_udp_posix_t* topic, uint_fast8_t iface_index, uint32_t err_no);

    size_t   mem_allocated_fragments;
    uint64_t mem_oom_count;
};

/// A simple helper that returns monotonic time in microseconds. The time value is always non-negative.
cy_us_t cy_udp_posix_now(void);

/// The namespace may be NULL or empty, in which case it defaults to "~".
///
/// Unused interfaces should have address either 0 or 0xFFFFFFFF;
/// to parse IP addresses from string see udp_wrapper_parse_iface_address().
///
/// The local node ID should be set to CY_NODE_ID_INVALID unless manual configuration is required.
cy_err_t               cy_udp_posix_new(struct cy_udp_posix_t* const cy_udp,
                                        const uint64_t               uid,
                                        const struct wkv_str_t       namespace_,
                                        const uint32_t               local_iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX],
                                        const size_t                 tx_queue_capacity_per_iface);
static inline cy_err_t cy_udp_posix_new_c(struct cy_udp_posix_t* const cy_udp,
                                          const uint64_t               uid,
                                          const char* const            namespace_,
                                          const uint32_t local_iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX],
                                          const size_t   tx_queue_capacity_per_iface)
{
    return cy_udp_posix_new(cy_udp, uid, wkv_key(namespace_), local_iface_address, tx_queue_capacity_per_iface);
}

/// Keep running the event loop until the deadline is reached or until the first error.
/// If the deadline is not in the future, the function will process pending events once and return without blocking.
/// If the deadline is in the future and there are currently no events to process, the function will block until the
/// deadline is reached or until an event arrives. The function may return early even if no events are available.
/// The current monotonic time is as defined in cy_udp_posix_now().
cy_err_t cy_udp_posix_spin_until(struct cy_udp_posix_t* const cy_udp, const cy_us_t deadline);

/// Wait for events (blocking), process them, and return. Invoke this in a tight superloop to keep the system alive.
/// The function is guaranteed to return no later than in the heartbeat period, or in a few ms, which ever is sooner.
cy_err_t cy_udp_posix_spin_once(struct cy_udp_posix_t* const cy_udp);
