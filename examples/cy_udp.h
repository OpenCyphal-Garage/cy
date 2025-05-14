/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#pragma once

#include "udp.h"
#include <cy.h>
#include <udpard.h>

#define CY_UDP_IFACE_COUNT_MAX           UDPARD_NETWORK_INTERFACE_COUNT_MAX
#define CY_UDP_NODE_ID_BLOOM_64BIT_WORDS 128

/// Responses to all topics that are addressed to our node are delivered using the same RPC port, which needs an extent.
/// In LibUDPard, the extent does not really affect memory allocation, because libudpard does not defragment received
/// transfers; meaning that the extent value can be arbitrarily large.
#define CY_UDP_TOPIC_RESPONSE_EXTENT (1024ULL * 1024ULL * 1024ULL)

struct cy_udp_topic_t
{
    struct cy_topic_t           base;
    struct UdpardRxSubscription sub;
    struct udp_rx_t             sock_rx[CY_UDP_IFACE_COUNT_MAX];

    /// The count of out-of-memory errors that occurred while processing this topic.
    /// Every OOM implies that either a frame or a full transfer were lost.
    uint64_t rx_oom_count;

    /// Handler for errors occurring while reading from the socket of this topic on the specified iface.
    /// These are platform-specific.
    /// The default handler is provided which will use CY_TRACE() to report the error.
    void (*rx_sock_err_handler)(struct cy_udp_topic_t* topic, uint_fast8_t iface_index, int16_t error);
};

struct cy_udp_t
{
    struct cy_t                    base;
    uint64_t                       node_id_bloom_storage[CY_UDP_NODE_ID_BLOOM_64BIT_WORDS];
    struct cy_udp_topic_t          heartbeat_topic;
    struct UdpardMemoryResource    mem;
    struct UdpardRxMemoryResources rx_mem;

    struct UdpardRxRPCDispatcher rpc_rx_dispatcher;
    struct UdpardRxRPCPort       rpc_rx_port_topic_response;

    uint32_t local_iface_address[CY_UDP_IFACE_COUNT_MAX];

    struct
    {
        struct UdpardTx udpard_tx;
        struct udp_tx_t sock;
        uint16_t        local_port;
        uint64_t        frames_expired; ///< Number of tx frames that have timed out while waiting in the queue.
    } tx[CY_UDP_IFACE_COUNT_MAX];

    struct
    {
        struct udp_rx_t sock;
        /// The count of out-of-memory errors that occurred while reading from this socket.
        /// Every OOM implies that either a frame or a full transfer were lost.
        uint64_t oom_count;
    } rpc_rx[CY_UDP_IFACE_COUNT_MAX];

    /// Handler for errors occurring while writing into a tx socket on the specified iface.
    /// These are platform-specific.
    /// The default handler is provided which will use CY_TRACE() to report the error.
    void (*tx_sock_err_handler)(struct cy_udp_t* cy_udp, uint_fast8_t iface_index, int16_t error);

    /// Handler for errors occurring while reading from an RPC RX socket on the specified iface.
    /// These are platform-specific.
    /// The default handler is provided which will use CY_TRACE() to report the error.
    void (*rpc_rx_sock_err_handler)(struct cy_udp_t* topic, uint_fast8_t iface_index, int16_t error);

    size_t   mem_allocated_fragments;
    size_t   mem_allocated_bytes;
    uint64_t mem_oom_count;
};

/// A convenience wrapper over clock_gettime(CLOCK_MONOTIC).
cy_us_t cy_udp_now(void);

/// The namespace may be NULL or empty, in which case it defaults to "~".
///
/// Unused interfaces should have address either 0 or 0xFFFFFFFF;
/// to parse IP addresses from string see udp_parse_iface_address().
///
/// The local node ID should be set to CY_NODE_ID_INVALID unless manual configuration is required.
cy_err_t cy_udp_new(struct cy_udp_t* const cy_udp,
                    const uint64_t         uid,
                    const char* const      namespace_,
                    const uint32_t         local_iface_address[CY_UDP_IFACE_COUNT_MAX],
                    const uint16_t         local_node_id,
                    const size_t           tx_queue_capacity_per_iface);

/// Wait for events (blocking), process them, and return. Invoke this in a tight superloop to keep the system alive.
/// The function is guaranteed to return no later than in the heartbeat period, as configured in the Cy instance.
cy_err_t cy_udp_spin_once(struct cy_udp_t* const cy_udp);

/// Keep running the event loop until the deadline is reached or until the first error.
/// If the deadline is not in the future, the function will process pending events once and return without blocking.
/// If the deadline is in the future and there are currently no events to process, the function will block until the
/// deadline is reached or until an event arrives. The function may return early even if no events are available.
/// The current monotonic time is as defined in cy_udp_now().
cy_err_t cy_udp_spin_until(struct cy_udp_t* const cy_udp, const cy_us_t deadline);

bool cy_udp_topic_new(struct cy_udp_t* const              cy_udp,
                      struct cy_udp_topic_t* const        topic,
                      const char* const                   name,
                      const struct cy_topic_hint_t* const optional_hints);

/// Trivial convenience wrapper over cy_subscribe().
static inline cy_err_t cy_udp_subscribe(struct cy_udp_topic_t* const     topic,
                                        struct cy_subscription_t* const  sub,
                                        const size_t                     extent,
                                        const cy_us_t                    transfer_id_timeout,
                                        const cy_subscription_callback_t callback)
{
    return cy_subscribe(&topic->base, sub, extent, transfer_id_timeout, callback);
}

static inline cy_err_t cy_udp_publish(struct cy_udp_topic_t* const       topic,
                                      const cy_us_t                      tx_deadline,
                                      const struct cy_payload_t          payload,
                                      const cy_us_t                      response_deadline,
                                      struct cy_response_future_t* const response_future)
{
    return cy_publish(&topic->base, tx_deadline, payload, response_deadline, response_future);
}

/// Trivial convenience wrapper over cy_publish1().
static inline cy_err_t cy_udp_publish1(struct cy_udp_topic_t* const topic,
                                       const cy_us_t                tx_deadline,
                                       const struct cy_payload_t    payload)
{
    return cy_publish1(&topic->base, tx_deadline, payload);
}
