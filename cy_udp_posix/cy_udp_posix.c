///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#include "cy_udp_posix.h"

#ifndef __USE_POSIX199309 // NOLINT(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp)
#define __USE_POSIX199309 // NOLINT(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp)
#endif
#include "udp_wrapper.h"

#define RAPIDHASH_COMPACT
#include <rapidhash.h>

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <errno.h>
#include <stdio.h>

/// Maximum expected incoming datagram size. If larger jumbo frames are expected, this value should be increased.
#ifndef CY_UDP_SOCKET_READ_BUFFER_SIZE
#define CY_UDP_SOCKET_READ_BUFFER_SIZE 2000
#endif

/// Some arbitrary initial extent for P2P transfers. Will be increased as needed, but never decreased.
#define P2P_INITIAL_EXTENT 1024U

static int64_t min_i64(const int64_t a, const int64_t b) { return (a < b) ? a : b; }
static int64_t min_i64_3(const int64_t a, const int64_t b, const int64_t c) { return min_i64(a, min_i64(b, c)); }

static void default_tx_sock_err_handler(cy_udp_posix_t* const cy_udp,
                                        const uint_fast8_t    iface_index,
                                        const uint32_t        err_no)
{
    CY_TRACE(&cy_udp->base, "⚠️ TX socket error on iface #%u: %u", iface_index, (unsigned)err_no);
}

static void default_rx_sock_err_handler(cy_udp_posix_t* const       cy_udp,
                                        cy_udp_posix_topic_t* const topic,
                                        const uint_fast8_t          iface_index,
                                        const uint32_t              err_no)
{
    CY_TRACE(
      &cy_udp->base, "⚠️ RX socket error on iface #%u topic '%s': %u", iface_index, topic->base.name, (unsigned)err_no);
}

static bool is_valid_ip(const uint32_t ip) { return (ip > 0) && (ip < UINT32_MAX); }

static void* mem_alloc(void* const user, const size_t size)
{
    cy_udp_posix_t* const cy_udp = (cy_udp_posix_t*)user;
    void* const           out    = malloc(size);
    if (size > 0) {
        if (out != NULL) {
            cy_udp->mem_allocated_fragments++;
        } else {
            cy_udp->mem_oom_count++;
        }
    }
    return out;
}

static void mem_free(void* const user, const size_t size, void* const pointer)
{
    cy_udp_posix_t* const cy_udp = (cy_udp_posix_t*)user;
    (void)size;
    if (pointer != NULL) {
        assert(cy_udp->mem_allocated_fragments > 0);
        cy_udp->mem_allocated_fragments--;
        memset(pointer, 0xA5, size); // a simple diagnostic aid
        free(pointer);
    }
}

static void purge_tx(cy_udp_posix_t* const cy_udp, const uint_fast8_t iface_index)
{
    udpard_tx_t* const tx  = &cy_udp->udpard_tx[iface_index];
    udpard_tx_item_t*  it  = NULL;
    const udpard_us_t  now = cy_udp_posix_now();
    while ((it = udpard_tx_peek(tx, now))) {
        udpard_tx_pop(tx, it);
        udpard_tx_free(tx->memory, it);
    }
}

static cy_err_t err_from_udp_wrapper(const int16_t e)
{
    switch (e) {
        case -EINVAL:
            return CY_ERR_ARGUMENT;
        case -ENOMEM:
            return CY_ERR_MEMORY;
        default:
            return (e < 0) ? CY_ERR_MEDIA : CY_OK;
    }
}

static udpard_remote_t response_context_to_remote(const cy_response_context_t* const ctx)
{
    udpard_remote_t rem = { .uid = ctx->u64[3] };
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        rem.endpoints[i].ip   = ctx->u64[i] & UINT32_MAX;
        rem.endpoints[i].port = (uint16_t)(ctx->u64[i] >> 32U);
    }
    return rem;
}

static cy_response_context_t remote_to_response_context(const udpard_remote_t* const remote)
{
    cy_response_context_t ctx = { 0 };
    ctx.u64[3]                = remote->uid;
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        ctx.u64[i] = ((uint64_t)remote->endpoints[i].port << 32U) | (uint64_t)remote->endpoints[i].ip;
    }
    return ctx;
}

static cy_err_t tx_push(cy_udp_posix_t* const   cy_udp,
                        const cy_us_t           tx_deadline,
                        const cy_prio_t         priority,
                        const uint64_t          transfer_id,
                        const uint64_t          topic_hash,
                        const udpard_udpip_ep_t dest_ep[UDPARD_NETWORK_INTERFACE_COUNT_MAX],
                        const cy_bytes_t        payload,
                        const bool              ack_required)
{
    CY_BUFFER_GATHER_ON_STACK(linear_payload, payload);
    cy_err_t          res = CY_OK;
    const udpard_us_t now = cy_udp_posix_now();
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        if (cy_udp->udpard_tx[i].queue_capacity > 0) {
            const uint64_t err_oom = cy_udp->udpard_tx[i].errors_oom;
            const uint64_t err_cap = cy_udp->udpard_tx[i].errors_capacity;
            const uint32_t n_frames =
              udpard_tx_push(&cy_udp->udpard_tx[i],
                             now,
                             tx_deadline,
                             (udpard_prio_t)priority,
                             topic_hash,
                             dest_ep[i],
                             transfer_id,
                             (udpard_bytes_t){ .size = linear_payload.size, .data = linear_payload.data },
                             ack_required,
                             NULL);
            // On error, keep going but remember the last error encountered.
            if (n_frames == 0) {
                if (err_oom < cy_udp->udpard_tx[i].errors_oom) {
                    res = CY_ERR_MEMORY;
                } else if (err_cap < cy_udp->udpard_tx[i].errors_capacity) {
                    res = CY_ERR_CAPACITY;
                } else {
                    res = CY_ERR_ARGUMENT;
                }
            }
        }
    }
    return res;
}

// ----------------------------------------  PLATFORM INTERFACE  ----------------------------------------

static cy_us_t platform_now(const cy_t* const cy)
{
    (void)cy;
    return cy_udp_posix_now();
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void* platform_realloc(cy_t* const cy, void* const ptr, const size_t new_size)
{
    (void)cy;
    if (new_size > 0) {
        return realloc(ptr, new_size);
    }
    free(ptr);
    return NULL;
}

static uint64_t platform_random(const cy_t* const cy)
{
    // This works only if the true RTC is available.
    // This is not safe for monotonic boot time clocks because it would return the same sequence after every reboot.
    // In that case, an application-specific source of randomness should be used instead (e.g., noinit memory or ADC).
    const uint64_t seed[2] = { (uint64_t)cy_udp_posix_now(), ((cy_udp_posix_t*)cy)->udpard_tx[0].local_uid };
    return rapidhash(seed, sizeof(seed));
}

static void platform_buffer_release(cy_t* const cy, const cy_buffer_owned_t buf)
{
    const cy_udp_posix_t* const cy_udp = (cy_udp_posix_t*)cy;
    (void)cy_udp;
    (void)buf;
    CY_TRACE(cy, "💣 TODO: RELEASE BUFFER CORRECTLY! size=%zu", buf.origin.size); // TODO FIXME
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static cy_err_t platform_p2p(cy_t* const                 cy,
                             cy_topic_t* const           topic,
                             const cy_response_context_t context,
                             const cy_prio_t             priority,
                             const cy_us_t               tx_deadline,
                             const cy_buffer_borrowed_t  payload,
                             const bool                  ack_required)
{
    (void)topic;
    cy_udp_posix_t* const cy_udp = (cy_udp_posix_t*)cy;
    const udpard_remote_t remote = response_context_to_remote(&context);
    return tx_push((cy_udp_posix_t*)cy,
                   tx_deadline,
                   priority,
                   cy_udp->p2p_transfer_id++,
                   remote.uid,
                   remote.endpoints,
                   payload,
                   ack_required);
}

static cy_topic_t* platform_topic_new(cy_t* const cy)
{
    cy_udp_posix_t* const       cy_udp = (cy_udp_posix_t*)cy;
    cy_udp_posix_topic_t* const topic  = (cy_udp_posix_topic_t*)mem_alloc(cy, sizeof(cy_udp_posix_topic_t));
    if (topic != NULL) {
        memset(topic, 0, sizeof(cy_udp_posix_topic_t));
        for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
            topic->rx_sock[i] = udp_wrapper_new();
        }
        topic->rx_sock_err_handler = cy_udp->rx_sock_err_handler;
        cy_udp->n_topics++;
    }
    return (cy_topic_t*)topic;
}

static void platform_topic_destroy(cy_t* const cy, cy_topic_t* const topic)
{
    cy_udp_posix_t* const       cy_udp    = (cy_udp_posix_t*)cy;
    cy_udp_posix_topic_t* const udp_topic = (cy_udp_posix_topic_t*)topic;
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        udp_wrapper_close(&udp_topic->rx_sock[i]);
    }
    mem_free(cy, sizeof(cy_udp_posix_topic_t), topic);
    cy_udp->n_topics--;
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static cy_err_t platform_topic_publish(cy_t* const                cy,
                                       cy_publisher_t* const      pub,
                                       const cy_us_t              tx_deadline,
                                       const cy_buffer_borrowed_t payload,
                                       const bool                 ack_required)
{
    udpard_udpip_ep_t endpoints[UDPARD_NETWORK_INTERFACE_COUNT_MAX] = {
        udpard_make_subject_endpoint(cy_topic_subject_id(cy, pub->topic)),
    };
    for (size_t i = 1; i < UDPARD_NETWORK_INTERFACE_COUNT_MAX; i++) {
        endpoints[i] = endpoints[0];
    }
    return tx_push((cy_udp_posix_t*)cy,
                   tx_deadline,
                   pub->priority,
                   pub->topic->pub_transfer_id,
                   pub->topic->hash,
                   endpoints,
                   payload,
                   ack_required);
}

static cy_err_t platform_topic_subscribe(cy_t* const                    cy,
                                         cy_topic_t* const              cy_topic,
                                         const cy_subscription_params_t params)
{
    cy_udp_posix_topic_t* const topic  = (cy_udp_posix_topic_t*)cy_topic;
    const cy_udp_posix_t* const cy_udp = (cy_udp_posix_t*)cy;

    // Set up the udpard port. This does not yet allocate any resources.
    const udpard_rx_mem_resources_t rx_mem = { .fragment = cy_udp->mem, .session = cy_udp->mem };
    if (!udpard_rx_port_new(&topic->rx_port, topic->base.hash, params.extent, params.reordering_window, rx_mem)) {
        return CY_ERR_ARGUMENT;
    }
    const udpard_udpip_ep_t endpoint = udpard_make_subject_endpoint(cy_topic_subject_id(cy, cy_topic));

    // Open the sockets for this port.
    cy_err_t res = CY_OK;
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        topic->rx_sock[i] = udp_wrapper_new();
        if ((res == CY_OK) && udp_wrapper_is_open(&cy_udp->sock[i])) {
            res = err_from_udp_wrapper(
              udp_wrapper_open_multicast(&topic->rx_sock[i], cy_udp->local_ip[i], endpoint.ip, endpoint.port));
        }
    }

    // Cleanup on error.
    if (res != CY_OK) {
        for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
            udp_wrapper_close(&topic->rx_sock[i]);
        }
    }
    return res;
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void platform_topic_unsubscribe(cy_t* const cy, cy_topic_t* const cy_topic)
{
    cy_udp_posix_topic_t* const topic  = (cy_udp_posix_topic_t*)cy_topic;
    cy_udp_posix_t* const       cy_udp = (cy_udp_posix_t*)cy;
    udpard_rx_port_free(&cy_udp->udpard_rx, &topic->rx_port);
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        udp_wrapper_close(&((cy_udp_posix_topic_t*)cy_topic)->rx_sock[i]);
    }
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void platform_topic_advertise(cy_t* const       cy,
                                     cy_topic_t* const cy_topic,
                                     const size_t      response_extent_with_overhead)
{
    (void)cy_topic;
    cy_udp_posix_t* const cy_udp = (cy_udp_posix_t*)cy;
    if (response_extent_with_overhead > cy_udp->p2p_port.extent) {
        // This may sometimes, under very specific circumstances involving out-of-order frame arrival,
        // disrupt some in-progress transfers, but it's unlikely and we use reliable delivery for P2P anyway.
        cy_udp->p2p_port.extent = response_extent_with_overhead;
        CY_TRACE(&cy_udp->base, //
                 "📏 Response (extent+overhead) increased to %zu bytes",
                 cy_udp->p2p_port.extent);
    }
}

static void platform_topic_on_subscription_error(cy_t* const cy, cy_topic_t* const cy_topic, const cy_err_t error)
{
    CY_TRACE(cy, "⚠️ Subscription error on topic '%s': %d", (cy_topic != NULL) ? cy_topic->name : "", error);
}

static const cy_platform_t g_platform = {
    .now            = platform_now,
    .realloc        = platform_realloc,
    .random         = platform_random,
    .buffer_release = platform_buffer_release,

    .p2p = platform_p2p,

    .topic_new                   = platform_topic_new,
    .topic_destroy               = platform_topic_destroy,
    .topic_publish               = platform_topic_publish,
    .topic_subscribe             = platform_topic_subscribe,
    .topic_unsubscribe           = platform_topic_unsubscribe,
    .topic_advertise             = platform_topic_advertise,
    .topic_on_subscription_error = platform_topic_on_subscription_error,
};

// ----------------------------------------  END OF PLATFORM INTERFACE  ----------------------------------------

cy_us_t cy_udp_posix_now(void)
{
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) { // NOLINT(*-include-cleaner)
        abort();
    }
    return (ts.tv_sec * 1000000) + (ts.tv_nsec / 1000);
}

cy_err_t cy_udp_posix_new(cy_udp_posix_t* const cy_udp,
                          const uint64_t        uid,
                          const wkv_str_t       name,
                          const wkv_str_t       namespace_,
                          const uint32_t        local_iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX],
                          const size_t          tx_queue_capacity_per_iface)
{
    assert(cy_udp != NULL);
    memset(cy_udp, 0, sizeof(*cy_udp));
    cy_udp->n_topics = 0;
    // Set up the memory resources. We could use block pool allocator here as well!
    // At the moment we use a very simple configuration though.
    cy_udp->mem.alloc               = mem_alloc;
    cy_udp->mem.free                = mem_free;
    cy_udp->mem.user                = cy_udp;
    cy_udp->rx_sock_err_handler     = default_rx_sock_err_handler;
    cy_udp->tx_sock_err_handler     = default_tx_sock_err_handler;
    cy_udp->mem_allocated_fragments = 0;
    cy_udp->mem_oom_count           = 0;

    // Initialize the udpard tx pipelines. They are all initialized always even if the corresponding iface is disabled,
    // for regularity, because an unused tx pipline needs no resources, so it's not a problem.
    cy_err_t res = CY_OK;
    for (uint_fast8_t i = 0; (i < CY_UDP_POSIX_IFACE_COUNT_MAX) && (res == CY_OK); i++) {
        cy_udp->sock[i]                        = udp_wrapper_new();
        const udpard_tx_mem_resources_t tx_mem = { .fragment = cy_udp->mem, .payload = cy_udp->mem };
        if (!udpard_tx_new(&cy_udp->udpard_tx[i], uid, tx_queue_capacity_per_iface, tx_mem)) {
            res = CY_ERR_ARGUMENT;
        }
    }
    if (res != CY_OK) {
        return res; // Cleanup not required -- no resources allocated yet.
    }

    // Initialize the udpard P2P RX port.
    const udpard_rx_mem_resources_t rx_mem = { .fragment = cy_udp->mem, .session = cy_udp->mem };
    if (!udpard_rx_port_new(
          &cy_udp->p2p_port, uid, P2P_INITIAL_EXTENT, UDPARD_RX_REORDERING_WINDOW_UNORDERED, rx_mem)) {
        return CY_ERR_ARGUMENT; // Cleanup not required -- no resources allocated yet.
    }

    // Initialize the instance sockets.
    for (uint_fast8_t i = 0; (i < CY_UDP_POSIX_IFACE_COUNT_MAX) && (res == CY_OK); i++) {
        if (is_valid_ip(local_iface_address[i])) {
            cy_udp->local_ip[i] = local_iface_address[i];
            res                 = err_from_udp_wrapper(
              udp_wrapper_open_unicast(&cy_udp->sock[i], local_iface_address[i], &cy_udp->local_tx_port[i]));
        } else {
            cy_udp->local_ip[i]                 = 0;
            cy_udp->local_tx_port[i]            = 0;
            cy_udp->udpard_tx[i].queue_capacity = 0;
        }
    }

    // Initialize Cy. It will not emit any transfers; this only happens from cy_heartbeat() and cy_publish().
    if (res == CY_OK) {
        const char name_copy[CY_NAMESPACE_NAME_MAX + 1] = { 0 };
        wkv_str_t  name_key                             = name;
        if (name_key.len == 0) {
            (void)snprintf((char*)name_copy, sizeof(name_copy), "#%016llx", (unsigned long long)uid);
            name_key = wkv_key(name_copy);
        }
        res = cy_new(&cy_udp->base, &g_platform, name_key, namespace_, CY_UDP_POSIX_SUBJECT_ID_MODULUS_MAX);
    }

    if (res == CY_OK) {
        cy_udp->p2p_transfer_id = platform_random((cy_t*)cy_udp);
    }

    // Cleanup on error.
    if (res != CY_OK) {
        for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
            purge_tx(cy_udp, i);
            udp_wrapper_close(&cy_udp->sock[i]); // The handle may be invalid, but we don't care.
        }
    }
    return res;
}

/// Write as many frames as possible from the tx queues to the network interfaces without blocking.
static void tx_offload(cy_udp_posix_t* const cy_udp)
{
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        if (cy_udp->udpard_tx[i].queue_capacity > 0) {
            const cy_us_t     now = cy_udp_posix_now(); // Do not call it for every frame, it's costly.
            udpard_tx_item_t* tqi = udpard_tx_peek(&cy_udp->udpard_tx[i], now);
            while (tqi != NULL) {
                const int16_t send_res = udp_wrapper_send(&cy_udp->sock[i],
                                                          tqi->destination.ip,
                                                          tqi->destination.port,
                                                          cy_udp->map_priority_to_dscp[tqi->priority],
                                                          tqi->datagram_payload.size,
                                                          tqi->datagram_payload.data);
                if (send_res == 0) {
                    break; // The socket is no longer writable, stop sending for now to retry later.
                }
                if (send_res < 0) {
                    assert(cy_udp->tx_sock_err_handler != NULL);
                    cy_udp->tx_sock_err_handler(cy_udp, i, (uint32_t)-send_res);
                }
                udpard_tx_pop(&cy_udp->udpard_tx[i], tqi);
                udpard_tx_free(cy_udp->udpard_tx[i].memory, tqi);
                tqi = udpard_tx_peek(&cy_udp->udpard_tx[i], now);
            }
        }
    }
}

static cy_transfer_metadata_t make_metadata(const struct udpard_rx_transfer_t* const tr)
{
    return (cy_transfer_metadata_t){ .priority    = (cy_prio_t)tr->priority,
                                     .context     = remote_to_response_context(&tr->remote),
                                     .transfer_id = tr->transfer_id };
}

static cy_buffer_owned_t make_rx_buffer(const struct UdpardFragment head)
{
    static_assert(sizeof(struct UdpardFragment) == sizeof(cy_buffer_owned_t), "");
    static_assert(offsetof(struct UdpardFragment, next) == offsetof(cy_buffer_owned_t, base.next), "");
    static_assert(offsetof(struct UdpardFragment, view) == offsetof(cy_buffer_owned_t, base.view), "");
    static_assert(offsetof(struct UdpardFragment, origin) == offsetof(cy_buffer_owned_t, origin), "");
    return ( cy_buffer_owned_t){
        .base   = {
            .next = ( cy_buffer_borrowed_t*)head.next,
            .view = { .size = head.view.size, .data = head.view.data },
        },
        .origin = { .size = head.origin.size, .data = head.origin.data },
    };
}

static void ingest_topic_frame(cy_udp_posix_t* const       cy_udp,
                               cy_udp_posix_topic_t* const topic,
                               const cy_us_t               ts,
                               const uint_fast8_t          iface_index,
                               const udpard_bytes_mut_t    dgram)
{
    if ((topic->base.couplings != NULL) && topic->base.subscribed) {
        udpard_rx_transfer_t transfer = { 0 }; // udpard takes ownership of the dgram payload buffer.
        const int_fast8_t er = udpard_rx_port_push(&cy_udp->udpard_rx, &topic->port, ts, dgram, iface_index, &transfer);
        if (er == 1) {
            const cy_transfer_owned_t tr = { .timestamp = (cy_us_t)transfer.timestamp_usec,
                                             .metadata  = make_metadata(&transfer),
                                             .payload   = make_rx_buffer(transfer.payload) };
            cy_ingest(&cy_udp->base, &topic->base, tr);
        } else if (er == 0) {
            (void)0; // Transfer is not yet completed, nothing to do for now.
        } else if (er == -UDPARD_ERROR_MEMORY) {
            topic->rx_oom_count++;
        } else {
            assert(false); // Unreachable -- internal error: unanticipated UDPARD error state (not possible).
        }
    } else { // The subscription was disabled while processing other socket reads. Ignore it.
        cy_udp->mem.free(cy_udp->mem.user, CY_UDP_SOCKET_READ_BUFFER_SIZE, dgram.data);
    }
}

static void ingest_rpc_frame(cy_udp_posix_t* const    cy_udp,
                             const cy_us_t            ts,
                             const uint_fast8_t       iface_index,
                             const udpard_bytes_mut_t dgram)
{
    struct UdpardRxRPCTransfer transfer = { 0 }; // udpard takes ownership of the dgram payload buffer.
    struct UdpardRxRPCPort*    port     = NULL;
    const int_fast8_t          er       = udpardRxRPCDispatcherReceive(
      &cy_udp->rpc_rx_dispatcher, (UdpardMicrosecond)ts, dgram, iface_index, &port, &transfer);
    if (er == 1) {
        assert(port != NULL);
        if (port == &cy_udp->rpc_rx_port_topic_response) {
            assert(port->service_id == P2P_SERVICE_ID);
            const cy_transfer_owned_t tr = { .timestamp = (cy_us_t)transfer.base.timestamp_usec,
                                             .metadata  = make_metadata(&transfer.base),
                                             .payload   = make_rx_buffer(transfer.base.payload) };
            cy_ingest_p2p(&cy_udp->base, tr);
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

static void read_socket(cy_udp_posix_t* const       cy_udp,
                        const cy_us_t               ts,
                        cy_udp_posix_topic_t* const topic,
                        udp_wrapper_t* const        sock,
                        const uint_fast8_t          iface_index)
{
    // Allocate memory that we will read the data into. The ownership of this memory will be transferred
    // to LibUDPard, which will free it when it is no longer needed.
    // A deeply embedded system may be able to transfer this memory directly from the NIC driver to eliminate copy.
    udpard_bytes_mut_t dgram = {
        .size = CY_UDP_SOCKET_READ_BUFFER_SIZE,
        .data = cy_udp->mem.alloc(cy_udp->mem.user, CY_UDP_SOCKET_READ_BUFFER_SIZE),
    };
    if (NULL == dgram.data) { // ReSharper disable once CppRedundantDereferencingAndTakingAddress
        ((topic != NULL) ? topic->rx_sock_err_handler
                         : cy_udp->rx_sock_err_handler)(cy_udp, topic, iface_index, ENOMEM);
        return;
    }

    // Read the data from the socket into the buffer we just allocated.
    udpard_udpip_ep_t remote_ep = { 0 };
    const int16_t     rx_result = udp_wrapper_receive(sock, &dgram.size, dgram.data, &remote_ep.ip, &remote_ep.port);
    if (rx_result < 0) {
        // We end up here if the socket was closed while processing another datagram.
        // This happens if a subscriber chose to unsubscribe dynamically or caused the node-ID to be changed.
        cy_udp->mem.free(cy_udp->mem.user, CY_UDP_SOCKET_READ_BUFFER_SIZE, dgram.data);
        ((topic != NULL) ? topic->rx_sock_err_handler
                         : cy_udp->rx_sock_err_handler)(cy_udp, topic, iface_index, (uint32_t)-rx_result);
        return;
    }
    if (rx_result == 0) { // Nothing to read OR dgram dropped by filters.
        cy_udp->mem.free(cy_udp->mem.user, CY_UDP_SOCKET_READ_BUFFER_SIZE, dgram.data);
        return;
    }
    // Ignore packets we sent ourselves. This can happen with multicast depending on the socket implementation.
    if ((remote_ep.ip == cy_udp->local_ip[iface_index]) && (remote_ep.port == cy_udp->local_tx_port[iface_index])) {
        cy_udp->mem.free(cy_udp->mem.user, CY_UDP_SOCKET_READ_BUFFER_SIZE, dgram.data);
        return;
    }

    // Realloc the buffer to fit the actual size of the datagram to avoid inner fragmentation.
    void* const dgram_realloc = realloc(dgram.data, dgram.size);
    if (dgram_realloc != NULL) {
        dgram.data = dgram_realloc;
    }

    // Pass the data buffer into LibUDPard then into Cy for further processing. It takes ownership of the buffer.
    if (topic != NULL) {
        ingest_topic_frame(cy_udp, topic, ts, iface_index, dgram);
    } else {
        ingest_rpc_frame(cy_udp, ts, iface_index, dgram);
    }
}

static cy_err_t spin_once_until(cy_udp_posix_t* const cy_udp, const cy_us_t deadline)
{
    tx_offload(cy_udp); // Free up space in the TX queues and ensure all TX sockets are blocked before waiting.

    // Fill out the TX awaitable array. May be empty if there's nothing to transmit at the moment.
    size_t         tx_count                               = 0;
    udp_wrapper_t* tx_await[CY_UDP_POSIX_IFACE_COUNT_MAX] = { 0 };
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        if (cy_udp->udpard_tx[i].queue_size > 0) { // There's something to transmit!
            tx_await[tx_count] = &cy_udp->sock[i];
            tx_count++;
        }
    }

    // Fill out the RX awaitable array. The total number of RX sockets is the interface count times number of topics
    // we are subscribed to plus P2P RX sockets (exactly one per iface).  Currently, we don't have a simple value that
    // says how many topics we are subscribed to, so we simply use the total number of topics.
    // This is a rather cumbersome operation as we need to traverse the topic tree; perhaps we should switch to epoll?
    const size_t          max_rx_count = CY_UDP_POSIX_IFACE_COUNT_MAX * (cy_udp->n_topics + 1);
    size_t                rx_count     = 0;
    udp_wrapper_t*        rx_await[max_rx_count]; // Initialization is not possible and is very wasteful anyway.
    cy_udp_posix_topic_t* rx_topics[max_rx_count];
    uint_fast8_t          rx_iface_indexes[max_rx_count];
    for (cy_udp_posix_topic_t* topic = (cy_udp_posix_topic_t*)cy_topic_iter_first(&cy_udp->base); topic != NULL;
         topic                       = (cy_udp_posix_topic_t*)cy_topic_iter_next(&topic->base)) {
        if (topic->base.couplings != NULL) {
            for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
                if (is_valid_ip(cy_udp->local_ip[i])) {
                    assert(udp_wrapper_is_open(&topic->rx_sock[i]));
                    assert(rx_count < max_rx_count);
                    rx_await[rx_count]         = &topic->rx_sock[i];
                    rx_topics[rx_count]        = topic;
                    rx_iface_indexes[rx_count] = i;
                    rx_count++;
                }
            }
        }
    }
    // Add the P2P socket for reading.
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        if (udp_wrapper_is_open(&cy_udp->sock[i])) {
            rx_await[rx_count]         = &cy_udp->sock[i];
            rx_topics[rx_count]        = NULL; // A P2P socket has no associated topic.
            rx_iface_indexes[rx_count] = i;
            rx_count++;
        }
    }

    // Do a blocking wait.
    const cy_us_t wait_timeout = deadline - min_i64(cy_udp_posix_now(), deadline);
    cy_err_t      res = err_from_udp_wrapper(udp_wrapper_wait(wait_timeout, tx_count, tx_await, rx_count, rx_await));
    if (res == CY_OK) {
        const cy_us_t ts = cy_udp_posix_now(); // immediately after unblocking

        // Process readable handles. The writable ones will be taken care of later.
        for (size_t i = 0; i < rx_count; i++) {
            if (rx_await[i] != NULL) {
                read_socket(cy_udp, ts, rx_topics[i], rx_await[i], rx_iface_indexes[i]);
            }
        }

        // Remember that we need to periodically poll cy_update() even if no traffic is received.
        // The update should be invoked after all incoming transfers are handled in this cycle, not before.
        assert(res == CY_OK);
        res = cy_update(&cy_udp->base);

        // While handling the events, we could have generated additional TX items, so we need to process them again.
        // We do it even in case of failure such that transient errors do not stall the TX queue.
        tx_offload(cy_udp);
    }
    return res;
}

cy_err_t cy_udp_posix_spin_until(cy_udp_posix_t* const cy_udp, const cy_us_t deadline)
{
    cy_err_t res = CY_OK;
    while (res == CY_OK) {
        const cy_us_t dl = min_i64_3(deadline, cy_udp->base.heartbeat_next, cy_udp->base.heartbeat_next_urgent);
        res              = spin_once_until(cy_udp, dl);
        if (deadline <= cy_udp_posix_now()) {
            break;
        }
    }
    return res;
}

cy_err_t cy_udp_posix_spin_once(cy_udp_posix_t* const cy_udp)
{
    assert(cy_udp != NULL);
    const cy_us_t dl = min_i64_3(cy_udp_posix_now() + 1000, //
                                 cy_udp->base.heartbeat_next,
                                 cy_udp->base.heartbeat_next_urgent);
    return spin_once_until(cy_udp, dl);
}
