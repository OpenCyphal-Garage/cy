/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#include "cy_udp.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

#ifndef __USE_POSIX199309
#define __USE_POSIX199309 // NOLINT(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp)
#endif
#include <time.h>

/// Maximum expected incoming datagram size. If larger jumbo frames are expected, this value should be increased.
#define RX_BUFFER_SIZE 2000

static int64_t min_i64(const int64_t a, const int64_t b)
{
    return (a < b) ? a : b;
}

static void default_tx_sock_err_handler(struct cy_udp_t* const cy_udp,
                                        const uint_fast8_t     iface_index,
                                        const int16_t          error)
{
    CY_TRACE(&cy_udp->base, "TX socket error on iface #%u: %d", iface_index, error);
}

static void default_rx_sock_err_handler(struct cy_udp_topic_t* const topic,
                                        const uint_fast8_t           iface_index,
                                        const int16_t                error)
{
    CY_TRACE(topic->base.cy, "RX socket error on iface #%u topic '%s': %d", iface_index, topic->base.name, error);
}

cy_us_t cy_udp_now(void)
{
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) { // NOLINT(*-include-cleaner)
        return 0;
    }
    return (ts.tv_sec * 1000000) + (ts.tv_nsec / 1000);
}

static void* mem_alloc(void* const user, const size_t size)
{
    struct cy_udp_t* const cy_udp = (struct cy_udp_t*)user;
    void* const            out    = malloc(size);
    if (size > 0) {
        if (out != NULL) {
            cy_udp->mem_allocated_bytes += size;
            cy_udp->mem_allocated_fragments++;
        } else {
            cy_udp->mem_oom_count++;
        }
    }
    return out;
}

static void mem_free(void* const user, const size_t size, void* const pointer)
{
    struct cy_udp_t* const cy_udp = (struct cy_udp_t*)user;
    if (pointer != NULL) {
        assert(cy_udp->mem_allocated_bytes >= size);
        assert(cy_udp->mem_allocated_fragments > 0);
        cy_udp->mem_allocated_bytes -= size;
        cy_udp->mem_allocated_fragments--;
        free(pointer);
    }
}

static void purge_tx(struct cy_udp_t* const cy_udp, const uint_fast8_t iface_index)
{
    struct UdpardTx* const     tx = &cy_udp->io[iface_index].tx;
    const struct UdpardTxItem* it = NULL;
    while ((it = udpardTxPeek(tx))) {
        udpardTxFree(tx->memory, udpardTxPop(tx, it));
    }
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static cy_us_t now(struct cy_t* const cy)
{
    (void)cy;
    return cy_udp_now();
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static cy_err_t transport_set_node_id(struct cy_t* const cy)
{
    assert(cy != NULL);
    // The udpard tx pipeline has a node-ID pointer that already points into the cy_t structure,
    // so it does not require updating.
    // Currently, there is literally nothing to do. When we add services, we will need to change the RPC multicast
    // group membership, which might be some hairy business as we'll need to close and reopen sockets.
    // Cyphal/CAN transports will need to reconfigure the CAN acceptance filters.
    return 0;
}

static void transport_clear_node_id(struct cy_t* const cy)
{
    assert(cy != NULL);
    struct cy_udp_t* const cy_udp = (struct cy_udp_t*)cy;
    // The udpard tx pipeline has a node-ID pointer that already points into the cy_t structure,
    // so it does not require updating.
    // Purge the tx queues to avoid further collisions.
    for (uint_fast8_t i = 0; i < CY_UDP_IFACE_COUNT_MAX; i++) {
        purge_tx(cy_udp, i);
    }
    // When we add services, we will need to change the RPC multicast group membership,
    // which might be some hairy business as we'll need to close and reopen sockets.
    // Cyphal/CAN transports will need to reconfigure the CAN acceptance filters.
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static cy_err_t transport_publish(struct cy_topic_t* const  topic,
                                  const cy_us_t             tx_deadline,
                                  const struct cy_payload_t payload)
{
    struct cy_udp_t* const cy_udp = (struct cy_udp_t*)topic->cy;
    cy_err_t               res    = 0;
    for (uint_fast8_t i = 0; i < CY_UDP_IFACE_COUNT_MAX; i++) {
        if (cy_udp->io[i].tx.queue_capacity > 0) {
            const int32_t e = udpardTxPublish(&cy_udp->io[i].tx,
                                              (UdpardMicrosecond)tx_deadline,
                                              (enum UdpardPriority)topic->pub_priority,
                                              cy_topic_get_subject_id(topic),
                                              topic->pub_transfer_id,
                                              (struct UdpardPayload){ .size = payload.size, .data = payload.data },
                                              NULL);
            // NOLINTNEXTLINE(*-narrowing-conversions, *-avoid-nested-conditional-operator)
            res = (e < 0) ? (cy_err_t)e : ((res < 0) ? res : (cy_err_t)e);
        }
    }
    return res;
}

static cy_err_t transport_request(struct cy_t* const              cy,
                                  const uint16_t                  service_id,
                                  const struct cy_transfer_meta_t metadata,
                                  cy_us_t                         tx_deadline,
                                  struct cy_payload_t             payload)
{
    struct cy_udp_t* const cy_udp = (struct cy_udp_t*)cy;
    cy_err_t               res    = 0;
    for (uint_fast8_t i = 0; i < CY_UDP_IFACE_COUNT_MAX; i++) {
        if (cy_udp->io[i].tx.queue_capacity > 0) {
            const int32_t e = udpardTxRequest(&cy_udp->io[i].tx,
                                              (UdpardMicrosecond)tx_deadline,
                                              (enum UdpardPriority)metadata.priority,
                                              service_id,
                                              metadata.remote_node_id,
                                              metadata.transfer_id,
                                              (struct UdpardPayload){ .size = payload.size, .data = payload.data },
                                              NULL);
            // NOLINTNEXTLINE(*-narrowing-conversions, *-avoid-nested-conditional-operator)
            res = (e < 0) ? (cy_err_t)e : ((res < 0) ? res : (cy_err_t)e);
        }
    }
    return res;
}

static bool is_valid_ip(const uint32_t ip)
{
    return (ip > 0) && (ip < UINT32_MAX);
}

static cy_err_t transport_subscribe(struct cy_topic_t* const cy_topic)
{
    struct cy_udp_topic_t* const topic  = (struct cy_udp_topic_t*)cy_topic;
    const struct cy_udp_t* const cy_udp = (struct cy_udp_t*)cy_topic->cy;

    // Set up the udpard subscription. This does not yet allocate any resources.
    cy_err_t res = (cy_err_t)udpardRxSubscriptionInit(&topic->sub, //
                                                      cy_topic_get_subject_id(cy_topic),
                                                      cy_topic->sub_extent,
                                                      cy_udp->rx_mem);
    if (res < 0) {
        return res; // No cleanup needed, no resources allocated yet.
    }

    // Open the sockets for this subscription.
    for (uint_fast8_t i = 0; i < CY_UDP_IFACE_COUNT_MAX; i++) {
        topic->sock_rx[i].fd = -1;
        if ((res >= 0) && is_valid_ip(cy_udp->io[i].local_iface_address)) {
            res = udp_rx_init(&topic->sock_rx[i],
                              cy_udp->io[i].local_iface_address,
                              topic->sub.udp_ip_endpoint.ip_address,
                              topic->sub.udp_ip_endpoint.udp_port,
                              cy_udp->io[i].tx_local_port);
        }
    }

    // Cleanup on error.
    if (res < 0) {
        for (uint_fast8_t i = 0; i < CY_UDP_IFACE_COUNT_MAX; i++) {
            udp_rx_close(&topic->sock_rx[i]);
        }
    }
    return res;
}

static void transport_unsubscribe(struct cy_topic_t* const cy_topic)
{
    udpardRxSubscriptionFree(&((struct cy_udp_topic_t*)cy_topic)->sub);
    for (uint_fast8_t i = 0; i < CY_UDP_IFACE_COUNT_MAX; i++) {
        udp_rx_close(&((struct cy_udp_topic_t*)cy_topic)->sock_rx[i]);
    }
}

static void transport_handle_resubscription_error(struct cy_topic_t* const cy_topic, const cy_err_t error)
{
    CY_TRACE(cy_topic->cy, "Resubscription error on topic '%s': %d", cy_topic->name, error);
    // Currently, we don't do anything here. What we could do is to put all failed topics into some list,
    // and attempt to resubscribe to them every now and then from the spin functions.
}

cy_err_t cy_udp_new(struct cy_udp_t* const cy_udp,
                    const uint64_t         uid,
                    const char* const      namespace_,
                    const uint32_t         local_iface_address[CY_UDP_IFACE_COUNT_MAX],
                    const uint16_t         local_node_id,
                    const size_t           tx_queue_capacity_per_iface)
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

    // Initialize the udpard tx pipelines. They are all initialized always even if the corresponding iface is disabled,
    // for regularity, because an unused tx pipline needs no resources, so it's not a problem.
    cy_err_t res = 0;
    for (uint_fast8_t i = 0; (i < CY_UDP_IFACE_COUNT_MAX) && (res >= 0); i++) {
        cy_udp->io[i].local_iface_address = 0;
        cy_udp->io[i].tx_sock.fd          = -1;
        res =
          (cy_err_t)udpardTxInit(&cy_udp->io[i].tx, &cy_udp->base.node_id, tx_queue_capacity_per_iface, cy_udp->mem);
    }
    if (res < 0) {
        return res; // Cleanup not required -- no resources allocated yet.
    }

    // Initialize the bottom layer first. Rx sockets are initialized per subscription, so not here.
    for (uint_fast8_t i = 0; (i < CY_UDP_IFACE_COUNT_MAX) && (res >= 0); i++) {
        if (is_valid_ip(local_iface_address[i])) {
            cy_udp->io[i].local_iface_address = local_iface_address[i];
            res = udp_tx_init(&cy_udp->io[i].tx_sock, local_iface_address[i], &cy_udp->io[i].tx_local_port);
        } else {
            cy_udp->io[i].tx.queue_capacity = 0;
        }
    }

    // Initialize Cy. It will not emit any transfers; this only happens from cy_heartbeat() and cy_publish().
    if (res >= 0) {
        res = cy_new(&cy_udp->base,
                     uid,
                     local_node_id,
                     UDPARD_NODE_ID_MAX,
                     CY_UDP_NODE_ID_BLOOM_64BIT_WORDS,
                     cy_udp->node_id_bloom_storage,
                     namespace_,
                     &cy_udp->heartbeat_topic.base,
                     &now,
                     (struct cy_transport_io_t){ .set_node_id               = transport_set_node_id,
                                                 .clear_node_id             = transport_clear_node_id,
                                                 .publish                   = transport_publish,
                                                 .request                   = transport_request,
                                                 .subscribe                 = transport_subscribe,
                                                 .unsubscribe               = transport_unsubscribe,
                                                 .handle_resubscription_err = transport_handle_resubscription_error });
    }

    // Cleanup on error.
    if (res < 0) {
        for (uint_fast8_t i = 0; i < CY_UDP_IFACE_COUNT_MAX; i++) {
            purge_tx(cy_udp, i);
            udp_tx_close(&cy_udp->io[i].tx_sock); // The handle may be invalid, but we don't care.
        }
    }
    return res;
}

/// Write as many frames as possible from the tx queues to the network interfaces without blocking.
static void tx_offload(struct cy_udp_t* const cy_udp)
{
    for (uint_fast8_t i = 0; i < CY_UDP_IFACE_COUNT_MAX; i++) {
        if (cy_udp->io[i].tx.queue_capacity > 0) {
            const struct UdpardTxItem* tqi = udpardTxPeek(&cy_udp->io[i].tx);
            const cy_us_t              ts  = cy_udp_now(); // Do not call it for every frame, it's costly.
            while (tqi != NULL) {
                // Attempt transmission only if the frame is not yet timed out while waiting in the TX queue.
                // Otherwise, just drop it and move on to the next one.
                if ((tqi->deadline_usec == 0) || (tqi->deadline_usec > (UdpardMicrosecond)ts)) {
                    const int16_t send_res = udp_tx_send(&cy_udp->io[i].tx_sock,
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
                    cy_udp->io[i].tx_timeout_count++;
                }
                udpardTxFree(cy_udp->io[i].tx.memory, udpardTxPop(&cy_udp->io[i].tx, tqi));
                tqi = udpardTxPeek(&cy_udp->io[i].tx);
            }
        }
    }
}

static void ingest_topic(struct cy_udp_topic_t* const topic, const struct UdpardRxTransfer* const transfer)
{
    // TODO: make Cy accept multipart payload so that we don't have to copy the data here.
    bool        payload_freed = false;
    const void* data          = transfer->payload.view.data;
    if (transfer->payload.next != NULL) {
        void* const dest = malloc(transfer->payload_size);
        data             = dest;
        if (dest != NULL) {
            const size_t sz = udpardGather(transfer->payload, transfer->payload_size, dest);
            assert(sz == transfer->payload_size);
            udpardRxFragmentFree(transfer->payload, topic->sub.memory.fragment, topic->sub.memory.payload);
            payload_freed = true;
        } else {
            topic->rx_oom_count++;
            goto hell;
        }
    }

    cy_ingest(&topic->base,
              (cy_us_t)transfer->timestamp_usec,
              (struct cy_transfer_meta_t){ .priority       = (enum cy_prio_t)transfer->priority,
                                           .remote_node_id = transfer->source_node_id,
                                           .transfer_id    = transfer->transfer_id },
              (struct cy_payload_t){ .size = transfer->payload_size, .data = data });

hell:
    if (!payload_freed) {
        udpardRxFragmentFree(transfer->payload, topic->sub.memory.fragment, topic->sub.memory.payload);
    }
}

static cy_err_t spin_once_until(struct cy_udp_t* const cy_udp, const cy_us_t deadline)
{
    tx_offload(cy_udp); // Free up space in the TX queues and ensure all TX sockets are blocked.

    // Fill out the TX awaitable array. May be empty if there's nothing to transmit at the moment.
    size_t           tx_count                         = 0;
    struct udp_tx_t* tx_await[CY_UDP_IFACE_COUNT_MAX] = { 0 };
    for (uint_fast8_t i = 0; i < CY_UDP_IFACE_COUNT_MAX; i++) {
        if (cy_udp->io[i].tx.queue_size > 0) { // There's something to transmit!
            tx_await[tx_count] = &cy_udp->io[i].tx_sock;
            tx_count++;
        }
    }

    // Fill out the RX awaitable array. The total number of RX sockets is the interface count times number of topics
    // we are subscribed to. Currently, we don't have a simple value that says how many topics we are subscribed to,
    // so we simply use the total number of topics; it's a bit wasteful but it's not a huge deal and we definitely
    // don't want to scan the topic index to count the ones we are subscribed to.
    // This is a rather cumbersome operation as we need to traverse the topic tree; perhaps we should switch to epoll?
    const size_t           max_rx_count = CY_UDP_IFACE_COUNT_MAX * cy_udp->base.topic_count;
    size_t                 rx_count     = 0;
    struct udp_rx_t*       rx_await[max_rx_count]; // Initialization is not possible and is very wasteful anyway.
    struct cy_udp_topic_t* rx_topics[max_rx_count];
    uint_fast8_t           rx_iface_indexes[max_rx_count];
    for (struct cy_udp_topic_t* topic = (struct cy_udp_topic_t*)cy_topic_iter_first(&cy_udp->base); topic != NULL;
         topic                        = (struct cy_udp_topic_t*)cy_topic_iter_next(&topic->base)) {
        if (cy_topic_has_local_subscribers(&topic->base)) {
            for (uint_fast8_t i = 0; i < CY_UDP_IFACE_COUNT_MAX; i++) {
                if (is_valid_ip(cy_udp->io[i].local_iface_address)) {
                    assert(topic->sock_rx[i].fd >= 0);
                    assert(rx_count < max_rx_count);
                    rx_await[rx_count]         = &topic->sock_rx[i];
                    rx_topics[rx_count]        = topic;
                    rx_iface_indexes[rx_count] = i;
                    rx_count++;
                }
            }
        }
    }

    // Do a blocking wait.
    const cy_us_t wait_timeout = deadline - min_i64(cy_udp_now(), deadline);
    cy_err_t      res          = udp_wait(wait_timeout, tx_count, tx_await, rx_count, rx_await);
    if (res < 0) {
        goto hell;
    }
    const cy_us_t ts = cy_udp_now(); // immediately after unblocking

    // Process readable handles. The writable ones will be taken care of later.
    for (size_t i = 0; i < rx_count; i++) {
        if (rx_await[i] == NULL) {
            continue; // Not ready for reading.
        }
        const uint_fast8_t           iface_index = rx_iface_indexes[i];
        struct cy_udp_topic_t* const topic       = rx_topics[i];

        // Allocate memory that we will read the data into. The ownership of this memory will be transferred
        // to LibUDPard, which will free it when it is no longer needed.
        // A deeply embedded system may be able to transfer this memory directly from the NIC driver to eliminate copy.
        struct UdpardMutablePayload dgram = {
            .size = RX_BUFFER_SIZE,
            .data = cy_udp->mem.allocate(cy_udp->mem.user_reference, RX_BUFFER_SIZE),
        };
        if (NULL == dgram.data) {
            topic->rx_oom_count++;
            continue;
        }

        // Read the data from the socket into the buffer we just allocated.
        const int16_t rx_result = udp_rx_receive(rx_await[i], &dgram.size, dgram.data);
        if (rx_result < 0) {
            // We end up here if the socket was closed while processing another datagram.
            // This happens if a subscriber chose to unsubscribe dynamically.
            cy_udp->mem.deallocate(cy_udp->mem.user_reference, RX_BUFFER_SIZE, dgram.data);
            assert(topic->rx_sock_err_handler != NULL);
            topic->rx_sock_err_handler(topic, iface_index, rx_result);
            continue;
        }
        if (rx_result == 0) { // Nothing to read OR dgram dropped by filters (own traffic or wrong iface).
            cy_udp->mem.deallocate(cy_udp->mem.user_reference, RX_BUFFER_SIZE, dgram.data);
            continue;
        }

        // Check for address collisions. This must be done at the frame level because if there are multiple nodes
        // sitting at our ID, we may be unable to receive any multiframe transfers from them.
        // TODO: the header needs to be verified (version & CRC) and it has to be done by LibUDPard; perhaps we need
        // to expose something like bool udpardRxFrameParse(payload, out_transfer_metadata)?
        // Alternatively, it could be an optional out-parameter of udpardRxSubscriptionReceive()?
        {
            const uint16_t src_nid = (uint16_t)(((const uint8_t*)dgram.data)[2] | //
                                                (((uint16_t)((const uint8_t*)dgram.data)[3]) << 8U));
            if ((src_nid <= UDPARD_NODE_ID_MAX) && (src_nid == cy_udp->base.node_id)) {
                cy_notify_node_id_collision(&cy_udp->base);
            }
        }

        // Pass the data buffer into LibUDPard then into Cy for further processing. It takes ownership of the buffer.
        if (cy_topic_has_local_subscribers(&topic->base)) {
            struct UdpardRxTransfer transfer = { 0 }; // udpard takes ownership of the dgram payload buffer.
            const int_fast8_t       er =
              udpardRxSubscriptionReceive(&topic->sub, (UdpardMicrosecond)ts, dgram, iface_index, &transfer);
            if (er == 1) {
                ingest_topic(topic, &transfer);
            } else if (er == 0) {
                (void)0; // Transfer is not yet completed, nothing to do for now.
            } else if (er == -UDPARD_ERROR_MEMORY) {
                topic->rx_oom_count++;
            } else {
                assert(false); // Unreachable -- internal error: unanticipated UDPARD error state (not possible).
            }
        } else { // The subscription was disabled while processing other socket reads. Ignore it.
            cy_udp->mem.deallocate(cy_udp->mem.user_reference, RX_BUFFER_SIZE, dgram.data);
        }
    }

    // Remember that we need to periodically poll cy_heartbeat() even if no traffic is received.
    // The update needs to be invoked after all incoming transfers are handled in this cycle, not before.
    assert(res >= 0);
    res = cy_heartbeat(&cy_udp->base);

    // While handling the events, we could have generated additional TX items, so we need to process them again.
    // We do it even in case of failure such that transient errors do not stall the TX queue.
    tx_offload(cy_udp);

hell:
    return res;
}

cy_err_t cy_udp_spin_once(struct cy_udp_t* const cy_udp)
{
    assert(cy_udp != NULL);
    return spin_once_until(cy_udp, cy_udp->base.heartbeat_next);
}

cy_err_t cy_udp_spin_until(struct cy_udp_t* const cy_udp, const cy_us_t deadline)
{
    cy_err_t res = 0;
    while (res >= 0) {
        res = spin_once_until(cy_udp, min_i64(deadline, cy_udp->base.heartbeat_next));
        if (deadline <= cy_udp_now()) {
            break;
        }
    }
    return res;
}

bool cy_udp_topic_new(struct cy_udp_t* const              cy_udp,
                      struct cy_udp_topic_t* const        topic,
                      const char* const                   name,
                      const struct cy_topic_hint_t* const optional_hints)
{
    assert(cy_udp != NULL);
    assert(topic != NULL);
    assert(name != NULL);
    memset(topic, 0, sizeof(*topic));
    topic->rx_sock_err_handler = default_rx_sock_err_handler;
    return cy_topic_new(&cy_udp->base, &topic->base, name, optional_hints);
}
