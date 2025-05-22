///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#include "cy_udp_posix.h"

#ifndef __USE_POSIX199309
#define __USE_POSIX199309 // NOLINT(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp)
#endif
#include "udp_wrapper.h"

#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/// Maximum expected incoming datagram size. If larger jumbo frames are expected, this value should be increased.
#ifndef CY_UDP_SOCKET_READ_BUFFER_SIZE
#define CY_UDP_SOCKET_READ_BUFFER_SIZE 2000
#endif

/// Responses to all topics that are addressed to our node are delivered using the same RPC port, which needs an extent.
/// In LibUDPard, the extent does not really affect memory allocation, because libudpard does not defragment received
/// transfers; meaning that the extent value can be arbitrarily large.
#define CY_UDP_POSIX_TOPIC_RESPONSE_EXTENT (1024ULL * 1024ULL * 1024ULL)

static int64_t min_i64(const int64_t a, const int64_t b)
{
    return (a < b) ? a : b;
}

static void default_tx_sock_err_handler(struct cy_udp_posix_t* const cy_udp,
                                        const uint_fast8_t           iface_index,
                                        const int16_t                error)
{
    CY_TRACE(&cy_udp->base, "TX socket error on iface #%u: %d", iface_index, error);
}

static void default_rpc_rx_sock_err_handler(struct cy_udp_posix_t* const cy_udp,
                                            const uint_fast8_t           iface_index,
                                            const int16_t                error)
{
    CY_TRACE(&cy_udp->base, "RPC RX socket error on iface #%u: %d", iface_index, error);
}

static void default_rx_sock_err_handler(struct cy_udp_posix_topic_t* const topic,
                                        const uint_fast8_t                 iface_index,
                                        const int16_t                      error)
{
    CY_TRACE(topic->base.cy, "RX socket error on iface #%u topic '%s': %d", iface_index, topic->base.name, error);
}

static bool is_valid_ip(const uint32_t ip)
{
    return (ip > 0) && (ip < UINT32_MAX);
}

static void* mem_alloc(void* const user, const size_t size)
{
    struct cy_udp_posix_t* const cy_udp = (struct cy_udp_posix_t*)user;
    void* const                  out    = malloc(size);
    if (size > 0) {
        if (out != NULL) {
            cy_udp->mem_allocated_fragments++;
        } else {
            cy_udp->mem_oom_count++;
        }
    }
    // CY_TRACE(&cy_udp->base, "mem_alloc(%zu) -> %p", size, out);
    return out;
}

static void mem_free(void* const user, const size_t size, void* const pointer)
{
    struct cy_udp_posix_t* const cy_udp = (struct cy_udp_posix_t*)user;
    (void)size;
    // CY_TRACE(&cy_udp->base, "mem_free(%zu, %p)", size, pointer);
    if (pointer != NULL) {
        assert(cy_udp->mem_allocated_fragments > 0);
        cy_udp->mem_allocated_fragments--;
        memset(pointer, 0xA5, size); // a simple diagnostic aid
        free(pointer);
    }
}

static void purge_tx(struct cy_udp_posix_t* const cy_udp, const uint_fast8_t iface_index)
{
    struct UdpardTx* const     tx = &cy_udp->tx[iface_index].udpard_tx;
    const struct UdpardTxItem* it = NULL;
    while ((it = udpardTxPeek(tx))) {
        udpardTxFree(tx->memory, udpardTxPop(tx, it));
    }
}

// ----------------------------------------  PLATFORM INTERFACE  ----------------------------------------

static cy_us_t platform_now(const struct cy_t* const cy)
{
    (void)cy;
    return cy_udp_posix_now();
}

static uint64_t platform_prng(const struct cy_t* const cy)
{
    (void)cy;
    struct timespec ts;
    const int       res = clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    assert(res == 0);
    return (uint64_t)ts.tv_nsec;
}

static void platform_buffer_release(struct cy_t* const cy, const struct cy_buffer_owned_t buf)
{
    const struct cy_udp_posix_t* const cy_udp = (struct cy_udp_posix_t*)cy;
    static_assert(sizeof(struct UdpardFragment) == sizeof(struct cy_buffer_owned_t), "");
    static_assert(offsetof(struct UdpardFragment, next) == offsetof(struct cy_buffer_owned_t, base.next), "");
    static_assert(offsetof(struct UdpardFragment, view) == offsetof(struct cy_buffer_owned_t, base.view), "");
    static_assert(offsetof(struct UdpardFragment, origin) == offsetof(struct cy_buffer_owned_t, origin), "");
    udpardRxFragmentFree(*(struct UdpardFragment*)&buf, cy_udp->rx_mem.fragment, cy_udp->rx_mem.payload);
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static cy_err_t platform_node_id_set(struct cy_t* const cy)
{
    assert(cy != NULL);
    assert(cy->node_id <= UDPARD_NODE_ID_MAX);
    struct cy_udp_posix_t* const cy_udp = (struct cy_udp_posix_t*)cy;
    // The udpard tx pipeline has a node-ID pointer that already points into the cy_t structure,
    // so it does not require updating. We need to reconfigure the RPC plane though.

    // Initialize and start the UDP RPC dispatcher.
    cy_err_t res = udpardRxRPCDispatcherInit(&cy_udp->rpc_rx_dispatcher, cy_udp->rx_mem);
    assert(res >= 0); // infallible by design
    struct UdpardUDPIPEndpoint ep = { 0 };
    res                           = udpardRxRPCDispatcherStart(&cy_udp->rpc_rx_dispatcher, cy->node_id, &ep);
    assert(res >= 0); // infallible by design

    // Start the RPC ports, all of them. Topic responses are sent as RPC requests. Shut up, it makes sense.
    res = udpardRxRPCDispatcherListen(&cy_udp->rpc_rx_dispatcher,
                                      &cy_udp->rpc_rx_port_topic_response,
                                      CY_RPC_SERVICE_ID_TOPIC_RESPONSE,
                                      true,
                                      CY_UDP_POSIX_TOPIC_RESPONSE_EXTENT);
    assert(res >= 0); // infallible by design
    // https://github.com/pavel-kirienko/cy/issues/8
    // https://github.com/OpenCyphal/libudpard/issues/63 (applies to requests only in this case)
    cy_udp->rpc_rx_port_topic_response.port.transfer_id_timeout_usec = 0;

    // Now it is finally time to open the multicast RX sockets.
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        cy_udp->rpc_rx[i].sock      = udp_wrapper_rx_new();
        cy_udp->rpc_rx[i].oom_count = 0;
    }
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        if (is_valid_ip(cy_udp->local_iface_address[i])) {
            res = udp_wrapper_rx_init(&cy_udp->rpc_rx[i].sock,
                                      cy_udp->local_iface_address[i],
                                      ep.ip_address,
                                      ep.udp_port,
                                      cy_udp->tx[i].local_port);
            if (res < 0) {
                break;
            }
        }
    }

    // Cleanup on error.
    if (res < 0) {
        for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
            udp_wrapper_rx_close(&cy_udp->rpc_rx[i].sock);
        }
    }
    return res;
}

static void platform_node_id_clear(struct cy_t* const cy)
{
    assert(cy != NULL);
    struct cy_udp_posix_t* const cy_udp = (struct cy_udp_posix_t*)cy;

    // Turn off the RPC plane. Close the sockets and stop the RPC ports. The RPC dispatcher holds no resources.
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        udp_wrapper_rx_close(&cy_udp->rpc_rx[i].sock);
    }
    {
        const cy_err_t res =
          udpardRxRPCDispatcherCancel(&cy_udp->rpc_rx_dispatcher, CY_RPC_SERVICE_ID_TOPIC_RESPONSE, true);
        assert(res >= 0); // infallible by design
    }

    // The udpard tx pipeline has a node-ID pointer that already points into the cy_t structure,
    // so it does not require updating.
    // Purge the tx queues to avoid further collisions.
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        purge_tx(cy_udp, i);
    }
}

static struct cy_bloom64_t* platform_node_id_bloom(struct cy_t* const cy)
{
    assert(cy != NULL);
    struct cy_udp_posix_t* const cy_udp = (struct cy_udp_posix_t*)cy;
    return &cy_udp->node_id_bloom;
}

static cy_err_t platform_request(struct cy_t* const                  cy,
                                 const uint16_t                      service_id,
                                 const struct cy_transfer_metadata_t metadata,
                                 const cy_us_t                       tx_deadline,
                                 const struct cy_buffer_borrowed_t   payload)
{
    CY_BUFFER_GATHER_ON_STACK(linear_payload, payload);
    struct cy_udp_posix_t* const cy_udp = (struct cy_udp_posix_t*)cy;
    cy_err_t                     res    = 0;
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        if (cy_udp->tx[i].udpard_tx.queue_capacity > 0) {
            const int32_t e =
              udpardTxRequest(&cy_udp->tx[i].udpard_tx,
                              (UdpardMicrosecond)tx_deadline,
                              (enum UdpardPriority)metadata.priority,
                              service_id,
                              metadata.remote_node_id,
                              metadata.transfer_id,
                              (struct UdpardPayload){ .size = linear_payload.size, .data = linear_payload.data },
                              NULL);
            // NOLINTNEXTLINE(*-narrowing-conversions, *-avoid-nested-conditional-operator)
            res = (e < 0) ? (cy_err_t)e : ((res < 0) ? res : (cy_err_t)e);
        }
    }
    return res;
}

static struct cy_topic_t* platform_topic_new(struct cy_t* const cy)
{
    struct cy_udp_posix_topic_t* const topic =
      (struct cy_udp_posix_topic_t*)mem_alloc(cy, sizeof(struct cy_udp_posix_topic_t));
    if (topic != NULL) {
        memset(topic, 0, sizeof(struct cy_udp_posix_topic_t));
        for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
            topic->sock_rx[i] = udp_wrapper_rx_new();
        }
        topic->rx_sock_err_handler = default_rx_sock_err_handler;
    }
    return (struct cy_topic_t*)topic;
}

static void platform_topic_destroy(struct cy_topic_t* const topic)
{
    struct cy_udp_posix_topic_t* const udp_topic = (struct cy_udp_posix_topic_t*)topic;
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        udp_wrapper_rx_close(&udp_topic->sock_rx[i]);
    }
    mem_free(topic->cy, sizeof(struct cy_udp_posix_topic_t), topic);
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static cy_err_t platform_topic_publish(struct cy_topic_t* const          topic,
                                       const cy_us_t                     tx_deadline,
                                       const struct cy_buffer_borrowed_t payload)
{
    CY_BUFFER_GATHER_ON_STACK(linear_payload, payload);
    struct cy_udp_posix_t* const cy_udp = (struct cy_udp_posix_t*)topic->cy;
    cy_err_t                     res    = 0;
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        if (cy_udp->tx[i].udpard_tx.queue_capacity > 0) {
            const int32_t e =
              udpardTxPublish(&cy_udp->tx[i].udpard_tx,
                              (UdpardMicrosecond)tx_deadline,
                              (enum UdpardPriority)topic->pub_priority,
                              cy_topic_get_subject_id(topic),
                              topic->pub_transfer_id,
                              (struct UdpardPayload){ .size = linear_payload.size, .data = linear_payload.data },
                              NULL);
            // NOLINTNEXTLINE(*-narrowing-conversions, *-avoid-nested-conditional-operator)
            res = (e < 0) ? (cy_err_t)e : ((res < 0) ? res : (cy_err_t)e);
        }
    }
    return res;
}

static cy_err_t platform_topic_subscribe(struct cy_topic_t* const cy_topic)
{
    struct cy_udp_posix_topic_t* const topic  = (struct cy_udp_posix_topic_t*)cy_topic;
    const struct cy_udp_posix_t* const cy_udp = (struct cy_udp_posix_t*)cy_topic->cy;

    // Set up the udpard subscription. This does not yet allocate any resources.
    cy_err_t res = (cy_err_t)udpardRxSubscriptionInit(&topic->sub, //
                                                      cy_topic_get_subject_id(cy_topic),
                                                      cy_topic->sub_extent,
                                                      cy_udp->rx_mem);
    if (res < 0) {
        return res; // No cleanup needed, no resources allocated yet.
    }

    // Open the sockets for this subscription.
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        topic->sock_rx[i] = udp_wrapper_rx_new();
        if ((res >= 0) && is_valid_ip(cy_udp->local_iface_address[i])) {
            res = udp_wrapper_rx_init(&topic->sock_rx[i],
                                      cy_udp->local_iface_address[i],
                                      topic->sub.udp_ip_endpoint.ip_address,
                                      topic->sub.udp_ip_endpoint.udp_port,
                                      cy_udp->tx[i].local_port);
        }
    }

    // Cleanup on error.
    if (res < 0) {
        for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
            udp_wrapper_rx_close(&topic->sock_rx[i]);
        }
    }
    return res;
}

static void platform_topic_unsubscribe(struct cy_topic_t* const cy_topic)
{
    udpardRxSubscriptionFree(&((struct cy_udp_posix_topic_t*)cy_topic)->sub);
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        udp_wrapper_rx_close(&((struct cy_udp_posix_topic_t*)cy_topic)->sock_rx[i]);
    }
}

static void platform_topic_handle_resubscription_error(struct cy_topic_t* const cy_topic, const cy_err_t error)
{
    CY_TRACE(cy_topic->cy, "Resubscription error on topic '%s': %d", cy_topic->name, error);
    // Currently, we don't do anything here. What we could do is to put all failed topics into some list,
    // and attempt to resubscribe to them every now and then from the spin functions.
}

static const struct cy_platform_t g_platform = {
    .now            = platform_now,
    .prng           = platform_prng,
    .buffer_release = platform_buffer_release,

    .node_id_set   = platform_node_id_set,
    .node_id_clear = platform_node_id_clear,
    .node_id_bloom = platform_node_id_bloom,

    .request = platform_request,

    .topic_new                         = platform_topic_new,
    .topic_destroy                     = platform_topic_destroy,
    .topic_publish                     = platform_topic_publish,
    .topic_subscribe                   = platform_topic_subscribe,
    .topic_unsubscribe                 = platform_topic_unsubscribe,
    .topic_handle_resubscription_error = platform_topic_handle_resubscription_error,

    .node_id_max      = UDPARD_NODE_ID_MAX,
    .transfer_id_mask = UINT64_MAX,
};

// ----------------------------------------  END OF PLATFORM INTERFACE  ----------------------------------------

cy_us_t cy_udp_posix_now(void)
{
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) { // NOLINT(*-include-cleaner)
        return 0;
    }
    return (ts.tv_sec * 1000000) + (ts.tv_nsec / 1000);
}

cy_err_t cy_udp_posix_new(struct cy_udp_posix_t* const cy_udp,
                          const uint64_t               uid,
                          const char* const            namespace_,
                          const uint32_t               local_iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX],
                          const size_t                 tx_queue_capacity_per_iface)
{
    assert(cy_udp != NULL);
    memset(cy_udp, 0, sizeof(*cy_udp));
    // Set up the memory resources. We could use block pool allocator here as well!
    cy_udp->mem.allocate                  = mem_alloc;
    cy_udp->mem.deallocate                = mem_free;
    cy_udp->mem.user_reference            = cy_udp;
    cy_udp->rx_mem.session                = cy_udp->mem;
    cy_udp->rx_mem.fragment               = cy_udp->mem;
    cy_udp->rx_mem.payload.deallocate     = mem_free;
    cy_udp->rx_mem.payload.user_reference = cy_udp;
    cy_udp->tx_sock_err_handler           = default_tx_sock_err_handler;
    cy_udp->rpc_rx_sock_err_handler       = default_rpc_rx_sock_err_handler;

    cy_udp->node_id_bloom.storage  = cy_udp->node_id_bloom_storage;
    cy_udp->node_id_bloom.n_bits   = sizeof(cy_udp->node_id_bloom_storage) * CHAR_BIT;
    cy_udp->node_id_bloom.popcount = 0;

    // Initialize the udpard tx pipelines. They are all initialized always even if the corresponding iface is disabled,
    // for regularity, because an unused tx pipline needs no resources, so it's not a problem.
    cy_err_t res = 0;
    for (uint_fast8_t i = 0; (i < CY_UDP_POSIX_IFACE_COUNT_MAX) && (res >= 0); i++) {
        cy_udp->local_iface_address[i] = 0;
        cy_udp->tx[i].sock             = udp_wrapper_tx_new();
        cy_udp->rpc_rx[i].sock         = udp_wrapper_rx_new();
        res                            = (cy_err_t)udpardTxInit(
          &cy_udp->tx[i].udpard_tx, &cy_udp->base.node_id, tx_queue_capacity_per_iface, cy_udp->mem);
    }
    if (res < 0) {
        return res; // Cleanup not required -- no resources allocated yet.
    }
    // FYI: the RPC dispatcher is only initialized ad-hoc when setting the node-ID.

    // Initialize the bottom layer first. Rx sockets are initialized per subscription, so not here.
    for (uint_fast8_t i = 0; (i < CY_UDP_POSIX_IFACE_COUNT_MAX) && (res >= 0); i++) {
        if (is_valid_ip(local_iface_address[i])) {
            cy_udp->local_iface_address[i] = local_iface_address[i];
            res = udp_wrapper_tx_init(&cy_udp->tx[i].sock, local_iface_address[i], &cy_udp->tx[i].local_port);
        } else {
            cy_udp->tx[i].udpard_tx.queue_capacity = 0;
        }
    }

    // Initialize Cy. It will not emit any transfers; this only happens from cy_heartbeat() and cy_publish().
    if (res >= 0) {
        res = cy_new(&cy_udp->base, &g_platform, uid, UDPARD_NODE_ID_UNSET, namespace_);
    }

    // Cleanup on error.
    if (res < 0) {
        for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
            purge_tx(cy_udp, i);
            udp_wrapper_tx_close(&cy_udp->tx[i].sock); // The handle may be invalid, but we don't care.
        }
    }
    return res;
}

/// Write as many frames as possible from the tx queues to the network interfaces without blocking.
static void tx_offload(struct cy_udp_posix_t* const cy_udp)
{
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        if (cy_udp->tx[i].udpard_tx.queue_capacity > 0) {
            const struct UdpardTxItem* tqi = udpardTxPeek(&cy_udp->tx[i].udpard_tx);
            const cy_us_t              ts  = cy_udp_posix_now(); // Do not call it for every frame, it's costly.
            while (tqi != NULL) {
                // Attempt transmission only if the frame is not yet timed out while waiting in the TX queue.
                // Otherwise, just drop it and move on to the next one.
                if ((tqi->deadline_usec == 0) || (tqi->deadline_usec > (UdpardMicrosecond)ts)) {
                    const int16_t send_res = udp_wrapper_tx_send(&cy_udp->tx[i].sock,
                                                                 tqi->destination.ip_address,
                                                                 tqi->destination.udp_port,
                                                                 tqi->dscp,
                                                                 tqi->datagram_payload.size,
                                                                 tqi->datagram_payload.data);
                    if (send_res == 0) {
                        break; // Socket no longer writable, stop sending for now to retry later.
                    }
                    if (send_res < 0) {
                        assert(cy_udp->tx_sock_err_handler != NULL);
                        cy_udp->tx_sock_err_handler(cy_udp, i, send_res);
                    }
                } else {
                    cy_udp->tx[i].frames_expired++;
                }
                udpardTxFree(cy_udp->tx[i].udpard_tx.memory, udpardTxPop(&cy_udp->tx[i].udpard_tx, tqi));
                tqi = udpardTxPeek(&cy_udp->tx[i].udpard_tx);
            }
        }
    }
}

static struct cy_transfer_metadata_t make_metadata(const struct UdpardRxTransfer* const tr)
{
    return (struct cy_transfer_metadata_t){ .priority       = (enum cy_prio_t)tr->priority,
                                            .remote_node_id = tr->source_node_id,
                                            .transfer_id    = tr->transfer_id };
}

static struct cy_buffer_owned_t make_rx_buffer(const struct UdpardFragment head)
{
    static_assert(sizeof(struct UdpardFragment) == sizeof(struct cy_buffer_owned_t), "");
    static_assert(offsetof(struct UdpardFragment, next) == offsetof(struct cy_buffer_owned_t, base.next), "");
    static_assert(offsetof(struct UdpardFragment, view) == offsetof(struct cy_buffer_owned_t, base.view), "");
    static_assert(offsetof(struct UdpardFragment, origin) == offsetof(struct cy_buffer_owned_t, origin), "");
    return (struct cy_buffer_owned_t){
        .base   = {
            .next = (struct cy_buffer_borrowed_t*)head.next,
            .view = { .size = head.view.size, .data = head.view.data },
        },
        .origin = { .size = head.origin.size, .data = head.origin.data },
    };
}

static void ingest_topic_frame(struct cy_udp_posix_topic_t* const topic,
                               const cy_us_t                      ts,
                               const uint_fast8_t                 iface_index,
                               const struct UdpardMutablePayload  dgram)
{
    const struct cy_udp_posix_t* const cy_udp = (struct cy_udp_posix_t*)topic->base.cy;
    if (cy_topic_has_local_subscribers(&topic->base) && topic->base.subscribed) {
        struct UdpardRxTransfer transfer = { 0 }; // udpard takes ownership of the dgram payload buffer.
        const int_fast8_t       er =
          udpardRxSubscriptionReceive(&topic->sub, (UdpardMicrosecond)ts, dgram, iface_index, &transfer);
        if (er == 1) {
            const struct cy_transfer_owned_t tr = { .timestamp = (cy_us_t)transfer.timestamp_usec,
                                                    .metadata  = make_metadata(&transfer),
                                                    .payload   = make_rx_buffer(transfer.payload) };
            cy_ingest_topic_transfer(&topic->base, tr);
        } else if (er == 0) {
            (void)0; // Transfer is not yet completed, nothing to do for now.
        } else if (er == -UDPARD_ERROR_MEMORY) {
            topic->rx_oom_count++;
        } else {
            assert(false); // Unreachable -- internal error: unanticipated UDPARD error state (not possible).
        }
    } else { // The subscription was disabled while processing other socket reads. Ignore it.
        cy_udp->mem.deallocate(cy_udp->mem.user_reference, CY_UDP_SOCKET_READ_BUFFER_SIZE, dgram.data);
    }
}

static void ingest_rpc_frame(struct cy_udp_posix_t* const      cy_udp,
                             const cy_us_t                     ts,
                             const uint_fast8_t                iface_index,
                             const struct UdpardMutablePayload dgram)
{
    struct UdpardRxRPCTransfer transfer = { 0 }; // udpard takes ownership of the dgram payload buffer.
    struct UdpardRxRPCPort*    port     = NULL;
    const int_fast8_t          er       = udpardRxRPCDispatcherReceive(
      &cy_udp->rpc_rx_dispatcher, (UdpardMicrosecond)ts, dgram, iface_index, &port, &transfer);
    if (er == 1) {
        assert(port != NULL);
        if (port == &cy_udp->rpc_rx_port_topic_response) {
            assert(port->service_id == CY_RPC_SERVICE_ID_TOPIC_RESPONSE);
            const struct cy_transfer_owned_t tr = { .timestamp = (cy_us_t)transfer.base.timestamp_usec,
                                                    .metadata  = make_metadata(&transfer.base),
                                                    .payload   = make_rx_buffer(transfer.base.payload) };
            cy_ingest_topic_response_transfer(&cy_udp->base, tr);
        } else {
            assert(false); // Forgot to handle?
        }
    } else if (er == 0) {
        (void)0; // Transfer is not yet completed, nothing to do for now.
    } else if (er == -UDPARD_ERROR_MEMORY) {
        cy_udp->rpc_rx[iface_index].oom_count++;
    } else {
        assert(false); // Unreachable -- internal error: unanticipated UDPARD error state (not possible).
    }
}

static void read_socket(struct cy_udp_posix_t* const       cy_udp,
                        const cy_us_t                      ts,
                        struct cy_udp_posix_topic_t* const topic,
                        struct udp_wrapper_rx_t* const     sock,
                        const uint_fast8_t                 iface_index)
{
    // Allocate memory that we will read the data into. The ownership of this memory will be transferred
    // to LibUDPard, which will free it when it is no longer needed.
    // A deeply embedded system may be able to transfer this memory directly from the NIC driver to eliminate copy.
    struct UdpardMutablePayload dgram = {
        .size = CY_UDP_SOCKET_READ_BUFFER_SIZE,
        .data = cy_udp->mem.allocate(cy_udp->mem.user_reference, CY_UDP_SOCKET_READ_BUFFER_SIZE),
    };
    if (NULL == dgram.data) { // ReSharper disable once CppRedundantDereferencingAndTakingAddress
        ++*((topic != NULL) ? &topic->rx_oom_count : &cy_udp->rpc_rx[iface_index].oom_count);
        return;
    }

    // Read the data from the socket into the buffer we just allocated.
    const int16_t rx_result = udp_wrapper_rx_receive(sock, &dgram.size, dgram.data);
    if (rx_result < 0) {
        // We end up here if the socket was closed while processing another datagram.
        // This happens if a subscriber chose to unsubscribe dynamically or caused the node-ID to be changed.
        cy_udp->mem.deallocate(cy_udp->mem.user_reference, CY_UDP_SOCKET_READ_BUFFER_SIZE, dgram.data);
        if (topic != NULL) {
            assert(topic->rx_sock_err_handler != NULL);
            topic->rx_sock_err_handler(topic, iface_index, rx_result);
        } else {
            assert(cy_udp->rpc_rx_sock_err_handler != NULL);
            cy_udp->rpc_rx_sock_err_handler(cy_udp, iface_index, rx_result);
        }
        return;
    }
    if (rx_result == 0) { // Nothing to read OR dgram dropped by filters (own traffic or wrong iface).
        cy_udp->mem.deallocate(cy_udp->mem.user_reference, CY_UDP_SOCKET_READ_BUFFER_SIZE, dgram.data);
        return;
    }

    // Check for address collisions. This must be done at the frame level because if there are multiple nodes
    // sitting at our ID, we may be unable to receive any multiframe transfers from them.
    // TODO: the header needs to be verified (version & CRC) and it has to be done by LibUDPard; perhaps we need
    // to expose something like bool udpardRxFrameParse(payload, out_transfer_metadata)?
    // Alternatively, it could be an optional out-parameter of udpardRxSubscriptionReceive()?
    {
        const uint16_t src_nid = (uint16_t)(((const uint8_t*)dgram.data)[2] | //
                                            (((uint32_t)((const uint8_t*)dgram.data)[3]) << 8U));
        if ((src_nid <= UDPARD_NODE_ID_MAX) && (src_nid == cy_udp->base.node_id)) {
            cy_notify_node_id_collision(&cy_udp->base);
        }
    }

    // Pass the data buffer into LibUDPard then into Cy for further processing. It takes ownership of the buffer.
    if (topic != NULL) {
        ingest_topic_frame(topic, ts, iface_index, dgram);
    } else {
        ingest_rpc_frame(cy_udp, ts, iface_index, dgram);
    }
}

static cy_err_t spin_once_until(struct cy_udp_posix_t* const cy_udp, const cy_us_t deadline)
{
    tx_offload(cy_udp); // Free up space in the TX queues and ensure all TX sockets are blocked.

    // Fill out the TX awaitable array. May be empty if there's nothing to transmit at the moment.
    size_t                   tx_count                               = 0;
    struct udp_wrapper_tx_t* tx_await[CY_UDP_POSIX_IFACE_COUNT_MAX] = { 0 };
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        if (cy_udp->tx[i].udpard_tx.queue_size > 0) { // There's something to transmit!
            tx_await[tx_count] = &cy_udp->tx[i].sock;
            tx_count++;
        }
    }

    // Fill out the RX awaitable array. The total number of RX sockets is the interface count times number of topics
    // we are subscribed to plus RPC RX sockets (whose number is not dependent on the number of RPC ports).
    // Currently, we don't have a simple value that says how many topics we are subscribed to,
    // so we simply use the total number of topics; it's a bit wasteful but it's not a huge deal and we definitely
    // don't want to scan the topic index to count the ones we are subscribed to.
    // This is a rather cumbersome operation as we need to traverse the topic tree; perhaps we should switch to epoll?
    const size_t                 max_rx_count = CY_UDP_POSIX_IFACE_COUNT_MAX * (cy_udp->base.topic_count + 1);
    size_t                       rx_count     = 0;
    struct udp_wrapper_rx_t*     rx_await[max_rx_count]; // Initialization is not possible and is very wasteful anyway.
    struct cy_udp_posix_topic_t* rx_topics[max_rx_count];
    uint_fast8_t                 rx_iface_indexes[max_rx_count];
    for (struct cy_udp_posix_topic_t* topic = (struct cy_udp_posix_topic_t*)cy_topic_iter_first(&cy_udp->base);
         topic != NULL;
         topic = (struct cy_udp_posix_topic_t*)cy_topic_iter_next(&topic->base)) {
        if (cy_topic_has_local_subscribers(&topic->base)) {
            for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
                if (is_valid_ip(cy_udp->local_iface_address[i])) {
                    assert(udp_wrapper_rx_is_initialized(&topic->sock_rx[i]));
                    assert(rx_count < max_rx_count);
                    rx_await[rx_count]         = &topic->sock_rx[i];
                    rx_topics[rx_count]        = topic;
                    rx_iface_indexes[rx_count] = i;
                    rx_count++;
                }
            }
        }
    }
    // Add the RPC RX sockets.
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        if (is_valid_ip(cy_udp->local_iface_address[i]) && udp_wrapper_rx_is_initialized(&cy_udp->rpc_rx[i].sock)) {
            rx_await[rx_count]         = &cy_udp->rpc_rx[i].sock;
            rx_topics[rx_count]        = NULL; // No topic associated with this socket.
            rx_iface_indexes[rx_count] = i;
            rx_count++;
        }
    }

    // Do a blocking wait.
    const cy_us_t wait_timeout = deadline - min_i64(cy_udp_posix_now(), deadline);
    cy_err_t      res          = udp_wrapper_wait(wait_timeout, tx_count, tx_await, rx_count, rx_await);
    if (res >= 0) {
        const cy_us_t ts = cy_udp_posix_now(); // immediately after unblocking

        // Process readable handles. The writable ones will be taken care of later.
        for (size_t i = 0; i < rx_count; i++) {
            if (rx_await[i] != NULL) {
                read_socket(cy_udp, ts, rx_topics[i], rx_await[i], rx_iface_indexes[i]);
            }
        }

        // Remember that we need to periodically poll cy_update() even if no traffic is received.
        // The update needs to be invoked after all incoming transfers are handled in this cycle, not before.
        assert(res >= 0);
        res = cy_update(&cy_udp->base);

        // While handling the events, we could have generated additional TX items, so we need to process them again.
        // We do it even in case of failure such that transient errors do not stall the TX queue.
        tx_offload(cy_udp);
    }
    return res;
}

cy_err_t cy_udp_posix_spin_until(struct cy_udp_posix_t* const cy_udp, const cy_us_t deadline)
{
    cy_err_t res = 0;
    while (res >= 0) {
        res = spin_once_until(cy_udp, min_i64(deadline, cy_udp->base.heartbeat_next));
        if (deadline <= cy_udp_posix_now()) {
            break;
        }
    }
    return res;
}

cy_err_t cy_udp_posix_spin_once(struct cy_udp_posix_t* const cy_udp)
{
    assert(cy_udp != NULL);
    return spin_once_until(cy_udp, min_i64(cy_udp_posix_now() + 2000, cy_udp->base.heartbeat_next));
}
