///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

// Blanket-disable the const ptr warning because we have a lot of vtable functions here.
// ReSharper disable CppParameterMayBeConstPtrOrRef

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
#include <limits.h>

/// Maximum expected incoming datagram size. If larger jumbo frames are expected, this value should be increased.
#ifndef CY_UDP_SOCKET_READ_BUFFER_SIZE
#define CY_UDP_SOCKET_READ_BUFFER_SIZE 2000
#endif

static size_t  smaller(const size_t a, const size_t b) { return (a < b) ? a : b; }
static int64_t min_i64(const int64_t a, const int64_t b) { return (a < b) ? a : b; }
static int64_t min_i64_3(const int64_t a, const int64_t b, const int64_t c) { return min_i64(a, min_i64(b, c)); }

/// Taken from https://github.com/pavel-kirienko/o1heap
static uint_fast8_t clz_size(const size_t x)
{
    assert(x > 0);
    size_t       t = ((size_t)1U) << ((sizeof(size_t) * CHAR_BIT) - 1U);
    uint_fast8_t r = 0;
    while ((x & t) == 0) {
        t >>= 1U;
        r++;
    }
    return r;
}

/// Rounds the argument up to the nearest power of 2. Undefined for x < 2.
static size_t ceil_pow2(const size_t x)
{
    assert(x >= 2U); // NOLINTNEXTLINE redundant cast to the same type.
    return ((size_t)1U) << ((sizeof(x) * CHAR_BIT) - ((uint_fast8_t)clz_size(x - 1U)));
}

static bool is_valid_ip(const uint32_t ip) { return (ip > 0) && (ip < UINT32_MAX); }

static void* mem_alloc(void* const user, const size_t size)
{
    cy_udp_posix_t* const cy  = (cy_udp_posix_t*)user;
    void* const           out = malloc(size);
    if (size > 0) {
        if (out != NULL) {
            cy->mem_allocated_fragments++;
            cy->mem_allocated_bytes += size;
        } else {
            cy->mem_oom_count++;
        }
    }
    return out;
}

static void mem_free(void* const user, const size_t size, void* const pointer)
{
    cy_udp_posix_t* const cy = (cy_udp_posix_t*)user;
    (void)size;
    if (pointer != NULL) {
        assert(cy->mem_allocated_fragments > 0);
        cy->mem_allocated_fragments--;
        assert(cy->mem_allocated_bytes >= size);
        cy->mem_allocated_bytes -= size;
        memset(pointer, 0xA5, size); // a simple diagnostic aid
        free(pointer);
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

static uint64_t prng64(uint64_t* const state, const uint64_t local_uid)
{
    *state += 0xA0761D6478BD642FULL; // add Wyhash seed (64-bit prime)
    return rapidhash_withSeed(state, sizeof(uint64_t), local_uid);
}

static cy_feedback_context_t feedback_context_unbox(const udpard_user_context_t ctx)
{
    static_assert(sizeof(cy_feedback_context_t) <= sizeof(udpard_user_context_t), "");
    cy_feedback_context_t out;
    memcpy(&out, &ctx, sizeof(out));
    return out;
}

static udpard_user_context_t feedback_context_box(const cy_feedback_context_t ctx)
{
    static_assert(sizeof(cy_feedback_context_t) <= sizeof(udpard_user_context_t), "");
    udpard_user_context_t out = { .ptr = { NULL } };
    memcpy(&out, &ctx, sizeof(ctx));
    return out;
}

static udpard_bytes_scattered_t cy_bytes_to_udpard_bytes(const cy_bytes_t message)
{
    // Instead of converting the entire payload chain, we can just statically validate that the memory layouts
    // are compatible. We cannot make neither libudpard nor cy depend on each other, but perhaps in the future
    // we could introduce a tiny single header providing some common definitions for both, to eliminate such aliasing.
    static_assert(offsetof(udpard_bytes_scattered_t, bytes.size) == offsetof(cy_bytes_t, size), "");
    static_assert(offsetof(udpard_bytes_scattered_t, bytes.data) == offsetof(cy_bytes_t, data), "");
    static_assert(offsetof(udpard_bytes_scattered_t, next) == offsetof(cy_bytes_t, next), "");
    return (udpard_bytes_scattered_t){ .bytes = { .size = message.size, .data = message.data },
                                       .next  = (const udpard_bytes_scattered_t*)message.next };
}

// ----------------------------------------  MESSAGE BUFFER  ----------------------------------------

static void v_message_destroy(cy_message_t* const self)
{
    const udpard_mem_resource_t mem = { .user = self->state[1], .alloc = &mem_alloc, .free = &mem_free };
    udpard_fragment_free_all((udpard_fragment_t*)self->state[0], mem);
}

static size_t v_message_read(cy_message_t* const self, const size_t offset, const size_t size, void* const dest)
{
    const udpard_fragment_t** cursor = (const udpard_fragment_t**)&self->state[0];
    return udpard_fragment_gather(cursor, offset, size, dest);
}

/// Specialization for single-fragment messages.
static size_t v_message_read_1(cy_message_t* const self, const size_t offset, const size_t size, void* const dest)
{
    const udpard_fragment_t* const frag = (const udpard_fragment_t*)self->state[0];
    assert((frag->index_offset.lr[0] == NULL) && (frag->index_offset.lr[1] == NULL));
    size_t out = 0;
    if (offset < frag->view.size) {
        out = smaller(size, frag->view.size - offset);
        memcpy(dest, ((const char*)frag->view.data) + offset, out);
    }
    return out;
}

static cy_message_t make_message(const size_t size, udpard_fragment_t* const frag, const udpard_mem_resource_t mem)
{
    static const cy_message_vtable_t vtable        = { .destroy = v_message_destroy, .read = v_message_read };
    static const cy_message_vtable_t vtable_1frame = { .destroy = v_message_destroy, .read = v_message_read_1 };
    return (cy_message_t){ .state  = { frag, mem.user },
                           .size   = size,
                           .vtable = (frag->view.size == size) ? &vtable_1frame : &vtable };
}

// ----------------------------------------  RESPONDER  ----------------------------------------

typedef struct responder_context_t
{
    uint64_t        topic_hash;
    uint64_t        transfer_id;
    udpard_remote_t remote;
    udpard_prio_t   priority;
} responder_context_t;

/// Invoked by libudpard when a response transmission attempt completes, whether successfully or not.
static void on_response_feedback(udpard_tx_t* const tx, const udpard_tx_feedback_t fb)
{
    assert(tx->user != NULL);
    assert(fb.acknowledgements <= 1);
    cy_on_response_feedback(tx->user, feedback_context_unbox(fb.user), fb.acknowledgements != 0);
}

/// Invoked by Cy when the application desires to respond to a message received earlier.
static cy_err_t v_respond(const cy_responder_t* const self,
                          const cy_us_t               tx_deadline,
                          const cy_bytes_t            message,
                          const cy_feedback_context_t context)
{
    responder_context_t ctx;
    static_assert(sizeof(ctx) <= sizeof(self->state), "");
    memcpy(&ctx, self->state, sizeof(ctx));
    cy_udp_posix_t* const cy         = (cy_udp_posix_t*)self->cy;
    const uint64_t        e_oom      = cy->udpard_tx.errors_oom;
    const uint64_t        e_capacity = cy->udpard_tx.errors_capacity;
    //
    const uint32_t res = udpard_tx_push_p2p(&cy->udpard_tx,
                                            cy_udp_posix_now(),
                                            tx_deadline,
                                            ctx.priority,
                                            ctx.topic_hash,
                                            ctx.transfer_id,
                                            ctx.remote,
                                            cy_bytes_to_udpard_bytes(message),
                                            on_response_feedback,
                                            feedback_context_box(context));
    CY_TRACE(&cy->base,
             "💬 T%016llx #%llu N%016llx res=%u",
             (unsigned long long)ctx.topic_hash,
             (unsigned long long)ctx.transfer_id,
             (unsigned long long)ctx.remote.uid,
             res);
    if (res > 0U) {
        return CY_OK;
    }
    if (cy->udpard_tx.errors_oom > e_oom) {
        return CY_ERR_MEMORY;
    }
    if (cy->udpard_tx.errors_capacity > e_capacity) {
        return CY_ERR_CAPACITY;
    }
    return CY_ERR_ARGUMENT;
}

/// When a message is received, a responder is created to allow responding to it later, if needed.
static cy_responder_t make_responder(cy_t* const           cy,
                                     const uint64_t        topic_hash,
                                     const uint64_t        transfer_id,
                                     const udpard_prio_t   priority,
                                     const udpard_remote_t remote)
{
    static const cy_responder_vtable_t vtable  = { .respond = v_respond };
    cy_responder_t                     out     = { .cy = cy, .vtable = &vtable };
    const responder_context_t          context = {
                 .topic_hash = topic_hash, .transfer_id = transfer_id, .remote = remote, .priority = priority
    };
    out.cy = cy;
    static_assert(sizeof(context) <= sizeof(out.state), "");
    memcpy(out.state, &context, sizeof(context));
    return out;
}

// ----------------------------------------  TOPIC VTABLE  ----------------------------------------

typedef struct
{
    uint64_t source_uid;
    uint64_t transfer_id;
} transfer_uid_t;

struct cy_udp_posix_topic_t
{
    cy_topic_t       base;
    uint64_t         pub_transfer_id;
    udpard_rx_port_t rx_port;
    udp_wrapper_t    rx_sock[CY_UDP_POSIX_IFACE_COUNT_MAX];
    void (*rx_sock_err_handler)(cy_udp_posix_t*       cy_udp,
                                cy_udp_posix_topic_t* topic,
                                uint_fast8_t          iface_index,
                                uint32_t              err_no);
    /// The history is only used with stateless subscriptions to reject the most obvious duplicates.
    /// It is essentially optional, but it is expected to save quite a bit of processing on busy topics,
    /// in particular in the heartbeat topic when used in a large network with redundant interfaces.
    transfer_uid_t history[2];
};

static void on_topic_feedback(udpard_tx_t* const tx, const udpard_tx_feedback_t fb)
{
    assert(tx->user != NULL);
    cy_on_message_feedback(tx->user, feedback_context_unbox(fb.user), fb.acknowledgements);
}

static cy_err_t v_topic_publish(cy_topic_t* const                  self,
                                const cy_us_t                      tx_deadline,
                                const cy_prio_t                    priority,
                                const cy_bytes_t                   message,
                                const cy_feedback_context_t* const reliable_context,
                                uint64_t* const                    out_transfer_id,
                                const size_t                       response_extent)
{
    cy_udp_posix_t* const   cy                                = (cy_udp_posix_t*)self->cy;
    const udpard_udpip_ep_t ep                                = udpard_make_subject_endpoint(cy_topic_subject_id(self));
    udpard_udpip_ep_t       endpoints[UDPARD_IFACE_COUNT_MAX] = { { 0 } };
    for (size_t i = 0; i < UDPARD_IFACE_COUNT_MAX; i++) {
        if ((cy->iface_mask & (1U << i)) != 0U) {
            endpoints[i] = ep;
        }
    }
    const uint64_t transfer_id = ((cy_udp_posix_topic_t*)self)->pub_transfer_id++;
    if (out_transfer_id != NULL) {
        *out_transfer_id = transfer_id;
    }
    // In this transport, the P2P response extent is trivial to change -- just update a variable; no need for any
    // complex reconfiguration. We are aware that changing the extent may sometimes, under very specific circumstances
    // involving out-of-order frame arrival, cause some in-progress transfers to be lost, but it's exceedingly unlikely
    // and we use reliable delivery for P2P anyway. To minimize the impact, we round it to some arbitrary threshold.
    const size_t response_extent_final = ceil_pow2(response_extent + UDPARD_P2P_HEADER_BYTES);
    if (response_extent_final > cy->p2p_port.base.extent) {
        cy->p2p_port.base.extent = response_extent_final * 2U; // Keep changes minimal.
        CY_TRACE(&cy->base, "📏 P2P response (extent+overhead) increased to %zu bytes", cy->p2p_port.base.extent);
    }
    const uint64_t e_oom      = cy->udpard_tx.errors_oom;
    const uint64_t e_capacity = cy->udpard_tx.errors_capacity;
    const uint32_t res =
      udpard_tx_push(&cy->udpard_tx,
                     cy_udp_posix_now(),
                     tx_deadline,
                     (udpard_prio_t)priority,
                     self->hash,
                     endpoints,
                     transfer_id,
                     cy_bytes_to_udpard_bytes(message),
                     (reliable_context != NULL) ? on_topic_feedback : NULL,
                     (reliable_context != NULL) ? feedback_context_box(*reliable_context) : UDPARD_USER_CONTEXT_NULL);
    if (res > 0U) {
        return CY_OK;
    }
    if (cy->udpard_tx.errors_oom > e_oom) {
        return CY_ERR_MEMORY;
    }
    if (cy->udpard_tx.errors_capacity > e_capacity) {
        return CY_ERR_CAPACITY;
    }
    return CY_ERR_ARGUMENT;
}

static bool topic_is_subscribed(const cy_udp_posix_topic_t* const self)
{
    for (size_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        if (udp_wrapper_is_open(&self->rx_sock[i])) {
            return true;
        }
    }
    return false;
}

static void v_on_msg(udpard_rx_t* const rx, udpard_rx_port_t* const port, const udpard_rx_transfer_t tr)
{
    cy_udp_posix_t* const cy    = rx->user;
    cy_topic_t* const     topic = port->user;
    assert((cy != NULL) && (topic != NULL));
    const cy_message_t   msg  = make_message(tr.payload_size_stored, tr.payload, cy->mem);
    const cy_responder_t resp = make_responder(&cy->base, port->topic_hash, tr.transfer_id, tr.priority, tr.remote);
    cy_on_message(topic, tr.timestamp, msg, resp);
}

static void v_on_msg_stateless(udpard_rx_t* const rx, udpard_rx_port_t* const port, const udpard_rx_transfer_t tr)
{
    cy_udp_posix_topic_t* const topic = port->user;
    assert(topic != NULL);
    static_assert(sizeof(topic->history) / sizeof(topic->history[0]) == 2, "");
    // In the stateless mode, libudpard does not bother deduplicating messages. The heartbeat subscriber does not
    // care about duplicates, so we could just pass all messages as-is and it will work fine, but it would waste
    // CPU cycles because each message requires some log-time index lookups.
    // We can mitigate this by applying a very simple filter that is cheap and computationally negligible.
    // It doesn't have to remove all duplicates -- removing the most obvious ones is sufficient to be useful.
    const bool dup =
      ((topic->history[0].transfer_id == tr.transfer_id) && (topic->history[0].source_uid == tr.remote.uid)) ||
      ((topic->history[1].transfer_id == tr.transfer_id) && (topic->history[1].source_uid == tr.remote.uid));
    if (!dup) {
        topic->history[1]             = topic->history[0];
        topic->history[0].transfer_id = tr.transfer_id;
        topic->history[0].source_uid  = tr.remote.uid;
        v_on_msg(rx, port, tr);
    } else {
        CY_TRACE(topic->base.cy,
                 "🍒️ T%016llx #%llu N%016llx duplicate transfer dropped",
                 (unsigned long long)port->topic_hash,
                 (unsigned long long)tr.transfer_id,
                 (unsigned long long)tr.remote.uid);
    }
}

static void v_on_collision(udpard_rx_t* const rx, udpard_rx_port_t* const port, const udpard_remote_t remote)
{
    (void)rx;
    (void)remote;
    assert(port->user != NULL);
    cy_on_topic_collision(port->user);
}

static cy_err_t v_topic_subscribe(cy_topic_t* const self, const size_t extent, cy_us_t reordering_window)
{
    cy_udp_posix_topic_t* const self_low = (cy_udp_posix_topic_t*)self;
    const cy_udp_posix_t* const cy       = (cy_udp_posix_t*)self->cy;
    assert(!topic_is_subscribed(self_low));
    // We special-case the heartbeat topic to have STATELESS reassembly strategy to conserve CPU and RAM.
    // Currently, the user API doesn't have the ability to select STATELESS mode, as it is uncertain if it
    // will be useful for the application. It is useful for the network stack because the heartbeat topic
    // is a bottleneck to be aware of -- every node publishes on it and every node is subscribed, so there is
    // a lot of traffic, while the protocol stack itself is invariant to heartbeat message reordering/duplicates.
    if (reordering_window < 0) {
        reordering_window = (self->hash == CY_HEARTBEAT_TOPIC_HASH) ? UDPARD_RX_REORDERING_WINDOW_STATELESS
                                                                    : UDPARD_RX_REORDERING_WINDOW_UNORDERED;
    }
    const bool stateless = (reordering_window == UDPARD_RX_REORDERING_WINDOW_STATELESS);

    // Set up the udpard port. This does not yet allocate any resources.
    static const udpard_rx_port_vtable_t vtbl   = { .on_message = v_on_msg, .on_collision = v_on_collision };
    static const udpard_rx_port_vtable_t vtbl_s = { .on_message = v_on_msg_stateless, .on_collision = v_on_collision };
    const udpard_rx_port_vtable_t*       vt     = stateless ? &vtbl_s : &vtbl;
    const udpard_rx_mem_resources_t      rx_mem = { .fragment = cy->mem, .session = cy->mem };
    if (!udpard_rx_port_new(&self_low->rx_port, self->hash, extent, reordering_window, rx_mem, vt)) {
        return CY_ERR_ARGUMENT;
    }
    self_low->rx_port.user           = self;
    const udpard_udpip_ep_t endpoint = udpard_make_subject_endpoint(cy_topic_subject_id(self));

    // Open the sockets for this port.
    cy_err_t res = CY_OK;
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        self_low->rx_sock[i] = udp_wrapper_new();
        if ((res == CY_OK) && udp_wrapper_is_open(&cy->sock[i])) {
            res = err_from_udp_wrapper(
              udp_wrapper_open_multicast(&self_low->rx_sock[i], cy->local_ip[i], endpoint.ip, endpoint.port));
        }
    }

    // Cleanup on error.
    if (res != CY_OK) {
        for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
            udp_wrapper_close(&self_low->rx_sock[i]);
        }
    }
    CY_TRACE(self->cy,
             "🔔 '%s' (extent=%zu reordering_window=%lld) res=%d",
             self->name,
             extent,
             (long long)reordering_window,
             (int)res);
    return res;
}

static void v_topic_unsubscribe(cy_topic_t* const self)
{
    cy_udp_posix_topic_t* const topic = (cy_udp_posix_topic_t*)self;
    cy_udp_posix_t* const       cy    = (cy_udp_posix_t*)self->cy;
    assert(topic_is_subscribed(topic));
    udpard_rx_port_free(&cy->udpard_rx, &topic->rx_port);
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        udp_wrapper_close(&topic->rx_sock[i]);
    }
    CY_TRACE(self->cy, "🔕 '%s'", self->name);
}

static void v_topic_destroy(cy_topic_t* const topic)
{
    CY_TRACE(topic->cy, "🗑️ '%s'", topic->name);
    cy_udp_posix_t* const       cy        = (cy_udp_posix_t*)topic->cy;
    cy_udp_posix_topic_t* const udp_topic = (cy_udp_posix_topic_t*)topic;
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        udp_wrapper_close(&udp_topic->rx_sock[i]);
    }
    mem_free(cy, sizeof(cy_udp_posix_topic_t), topic);
    cy->n_topics--;
}

static const cy_topic_vtable_t topic_vtable = { .publish     = v_topic_publish,
                                                .subscribe   = v_topic_subscribe,
                                                .unsubscribe = v_topic_unsubscribe,
                                                .destroy     = v_topic_destroy };

static cy_topic_t* v_topic_new(cy_t* const self)
{
    cy_udp_posix_t* const       cy    = (cy_udp_posix_t*)self;
    cy_udp_posix_topic_t* const topic = (cy_udp_posix_topic_t*)mem_alloc(cy, sizeof(cy_udp_posix_topic_t));
    if (topic != NULL) {
        memset(topic, 0, sizeof(cy_udp_posix_topic_t));
        topic->base.vtable     = &topic_vtable;
        topic->pub_transfer_id = prng64(&cy->prng_state, cy->udpard_tx.local_uid);
        for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
            topic->rx_sock[i] = udp_wrapper_new();
        }
        topic->rx_sock_err_handler = cy->rx_sock_err_handler;
        cy->n_topics++;
        CY_TRACE(self, "🆕 n_topics=%zu", cy->n_topics);
    }
    return (cy_topic_t*)topic;
}

// ----------------------------------------  CY VTABLE  ----------------------------------------

static cy_us_t v_now(const cy_t* const cy)
{
    (void)cy;
    return cy_udp_posix_now();
}

static void* v_realloc(cy_t* const cy, void* const ptr, const size_t new_size)
{
    (void)cy;
    // TODO: currently we do not track the memory usage by Cy, but it would be useful to do so.
    if (new_size > 0) {
        return realloc(ptr, new_size);
    }
    free(ptr);
    return NULL;
}

static uint64_t v_random(cy_t* const cy)
{
    return prng64(&((cy_udp_posix_t*)cy)->prng_state, ((cy_udp_posix_t*)cy)->udpard_tx.local_uid);
}

static void v_on_subscription_error(cy_t* const cy, cy_topic_t* const cy_topic, const cy_err_t error)
{
    // No action is needed -- Cy will keep attempting to repair the media until it succeeds.
    CY_TRACE(cy, "⚠️ Subscription error on topic '%s': %d", (cy_topic != NULL) ? cy_topic->name : "", error);
}

static const cy_vtable_t cy_vtable = { .now                   = v_now,
                                       .realloc               = v_realloc,
                                       .random                = v_random,
                                       .new_topic             = v_topic_new,
                                       .on_subscription_error = v_on_subscription_error };

// ----------------------------------------  END OF PLATFORM INTERFACE  ----------------------------------------

cy_us_t cy_udp_posix_now(void)
{
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) { // NOLINT(*-include-cleaner)
        abort();
    }
    return (ts.tv_sec * 1000000) + (ts.tv_nsec / 1000);
}

static void default_tx_sock_err_handler(cy_udp_posix_t* const cy, const uint_fast8_t iface_index, const uint32_t err_no)
{
    CY_TRACE(&cy->base, "⚠️ TX socket error on iface #%u: %u", iface_index, (unsigned)err_no);
}

static void default_rx_sock_err_handler(cy_udp_posix_t* const       cy,
                                        cy_udp_posix_topic_t* const topic,
                                        const uint_fast8_t          iface_index,
                                        const uint32_t              err_no)
{
    const char* const topic_name = (topic != NULL) ? topic->base.name : "";
    CY_TRACE(&cy->base, "⚠️ RX socket error on iface #%u topic '%s': %u", iface_index, topic_name, (unsigned)err_no);
}

static void v_on_p2p_msg(udpard_rx_t* const rx, udpard_rx_port_p2p_t* const port, const udpard_rx_transfer_p2p_t tr)
{
    cy_udp_posix_t* const cy = rx->user;
    assert((cy != NULL) && (port == &cy->p2p_port));
    (void)port;
    const cy_message_t msg = make_message(tr.base.payload_size_stored, tr.base.payload, cy->mem);
    cy_on_response(&cy->base, tr.base.timestamp, tr.topic_hash, tr.base.transfer_id, msg);
}

static bool v_tx_eject(udpard_tx_t* const tx, udpard_tx_ejection_t* const ej)
{
    cy_udp_posix_t* const cy = (cy_udp_posix_t*)tx->user;
    assert(cy != NULL);
    assert((cy->iface_mask & (1U << ej->iface_index)) != 0); // the caller must ensure this
    assert(ej->now <= ej->deadline);
    // The libudpard TX API provides us with an opportunity to retain the ownership of the datagram payload
    // via reference counting. This is useful in kernel space or in embedded systems with low-level NIC drivers,
    // but the Berkeley socket API does not allow us to take advantage of that -- the data will be copied into the
    // kernel space anyway. Therefore, we simply send it with copying and do not bother with reference counting.
    const int16_t res = udp_wrapper_send(&cy->sock[ej->iface_index], //
                                         ej->destination.ip,
                                         ej->destination.port,
                                         ej->dscp,
                                         ej->datagram.size,
                                         ej->datagram.data);
    if (res < 0) {
        assert(cy->tx_sock_err_handler != NULL);
        cy->tx_sock_err_handler(cy, ej->iface_index, (uint32_t)-res);
    }
    return res != 0; // either transmitted successfully or dropped due to error
}

cy_err_t cy_udp_posix_new(cy_udp_posix_t* const cy,
                          const uint64_t        uid,
                          const wkv_str_t       home,
                          const wkv_str_t       namespace_,
                          const uint32_t        local_iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX],
                          const size_t          tx_queue_capacity)
{
    assert(cy != NULL);
    memset(cy, 0, sizeof(*cy));
    cy->n_topics = 0;
    // We could use block pool allocators here if preferred.
    // Also, in the spirit of the PX4 UAVCAN driver, we could use a high-watermark allocator, where we graft memory
    // blocks from an ordinary heap (doesn't have to be constant-complexity even), and return them into
    // size-segregated free lists on deallocation.
    // This should suit most systems without the need for manual sizing of each fixed-size block pool.
    // Libudpard has a natural cap for the maximum memory usage based on the number of interfaces and queue sizes,
    // which helps avoiding heap exhaustion in this scenario; also, if exhaustion does occur, we can shrink the
    // least used pools on-the-fly.
    cy->mem                     = (udpard_mem_resource_t){ .user = cy, .alloc = &mem_alloc, .free = &mem_free };
    cy->iface_mask              = 0;
    cy->rx_sock_err_handler     = default_rx_sock_err_handler;
    cy->tx_sock_err_handler     = default_tx_sock_err_handler;
    cy->mem_allocated_fragments = 0;
    cy->mem_oom_count           = 0;

    // This PRNG state seed is only valid if a true RTC is available. Otherwise, use other sources of entropy.
    // Refer to cy_platform.h docs for some hints on how to make it work on an MCU without a TRNG nor RTC.
    cy->prng_state = (uint64_t)time(NULL);

    // Set up the TX and RX pipelines.
    static const udpard_tx_vtable_t tx_vtable = { .eject = v_tx_eject };
    const udpard_rx_mem_resources_t rx_mem    = { .fragment = cy->mem, .session = cy->mem };
    udpard_tx_mem_resources_t       tx_mem    = { .transfer = cy->mem };
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        cy->sock[i] = udp_wrapper_new();
        if (is_valid_ip(local_iface_address[i])) {
            cy->local_ip[i] = local_iface_address[i];
            cy->iface_mask |= 1U << i;
        } else {
            cy->local_ip[i] = 0;
        }
        tx_mem.payload[i] = cy->mem;
    }
    if (cy->iface_mask == 0) {
        return CY_ERR_ARGUMENT;
    }
    if (!udpard_tx_new(&cy->udpard_tx, uid, prng64(&cy->prng_state, uid), tx_queue_capacity, tx_mem, &tx_vtable)) {
        return CY_ERR_ARGUMENT; // Cleanup not required -- no resources allocated yet.
    }
    udpard_rx_new(&cy->udpard_rx, &cy->udpard_tx); // infallible
    cy->udpard_tx.user = cy;
    cy->udpard_rx.user = cy;

    // Initialize the udpard P2P RX port. We start with a zero initial extent, which will be increased ad-hoc.
    static const udpard_rx_port_p2p_vtable_t rx_p2p_vtable = { .on_message = v_on_p2p_msg };
    if (!udpard_rx_port_new_p2p(&cy->p2p_port, uid, 0, rx_mem, &rx_p2p_vtable)) {
        return CY_ERR_ARGUMENT; // Cleanup not required -- no resources allocated yet.
    }

    // Initialize the sockets.
    cy_err_t res = CY_OK;
    for (uint_fast8_t i = 0; (i < CY_UDP_POSIX_IFACE_COUNT_MAX) && (res == CY_OK); i++) {
        if ((cy->iface_mask & (1U << i)) != 0) {
            res = err_from_udp_wrapper(udp_wrapper_open_unicast(&cy->sock[i], cy->local_ip[i], &cy->local_tx_port[i]));
        }
    }

    // Initialize Cy. It will not emit any transfers yet.
    if (res == CY_OK) {
        char      name_copy[CY_NAMESPACE_NAME_MAX + 1];
        wkv_str_t name_key = home;
        if (!cy_name_is_valid(name_key)) {
            name_copy[0] = '#';
            (void)cy_u64_to_hex(uid, &name_copy[1]);
            name_key = wkv_key(name_copy);
        }
        // Here we assume that any transport that Cyphal/UDP may work with in a redundant set will have
        // a subject-ID modulus of at least 23 bits. If that is not the case and a smaller modulus is needed,
        // we will need to modify this to accept the modulus from the user.
        // Also, if/when we add support for IPv6, we will want to extend the modulus to 32 bits.
        res = cy_new(&cy->base, &cy_vtable, name_key, namespace_, CY_SUBJECT_ID_MODULUS_23bit);
    }

    // Cleanup on error.
    if (res != CY_OK) {
        udpard_rx_port_free(&cy->udpard_rx, &cy->p2p_port.base);
        udpard_tx_free(&cy->udpard_tx);
        for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
            udp_wrapper_close(&cy->sock[i]); // The handle may be invalid, but we don't care.
        }
    }
    return res;
}

static void read_socket(cy_udp_posix_t* const       cy,
                        const cy_us_t               ts,
                        cy_udp_posix_topic_t* const topic,
                        udp_wrapper_t* const        sock,
                        const uint_fast8_t          iface_index)
{
    assert((cy->iface_mask & (1U << iface_index)) != 0);
    assert(is_valid_ip(cy->local_ip[iface_index]));
    assert(udp_wrapper_is_open(sock));

    // Allocate memory that we will read the data into. The ownership of this memory will be transferred
    // to LibUDPard, which will free it when it is no longer needed.
    // A deeply embedded system may be able to transfer this memory directly from the NIC driver to eliminate copy.
    udpard_bytes_mut_t dgram = { .size = CY_UDP_SOCKET_READ_BUFFER_SIZE,
                                 .data = cy->mem.alloc(cy->mem.user, CY_UDP_SOCKET_READ_BUFFER_SIZE) };
    if (NULL == dgram.data) { // ReSharper disable once CppRedundantDereferencingAndTakingAddress
        ((topic != NULL) ? topic->rx_sock_err_handler : cy->rx_sock_err_handler)(cy, topic, iface_index, ENOMEM);
        return;
    }

    // Read the data from the socket into the buffer we just allocated.
    udpard_udpip_ep_t remote_ep = { 0 };
    const int16_t     rx_result = udp_wrapper_receive(sock, &dgram.size, dgram.data, &remote_ep.ip, &remote_ep.port);
    if (rx_result < 0) {
        // We end up here if the socket was closed while processing another datagram.
        // This happens if a subscriber chose to unsubscribe dynamically or caused the node-ID to be changed.
        cy->mem.free(cy->mem.user, CY_UDP_SOCKET_READ_BUFFER_SIZE, dgram.data);
        ((topic != NULL) ? topic->rx_sock_err_handler
                         : cy->rx_sock_err_handler)(cy, topic, iface_index, (uint32_t)-rx_result);
        return;
    }
    if (rx_result == 0) { // Nothing to read OR dgram dropped by filters.
        cy->mem.free(cy->mem.user, CY_UDP_SOCKET_READ_BUFFER_SIZE, dgram.data);
        return;
    }
    // Ignore packets we sent ourselves. This can happen with multicast depending on the socket implementation.
    if ((remote_ep.ip == cy->local_ip[iface_index]) && (remote_ep.port == cy->local_tx_port[iface_index])) {
        cy->mem.free(cy->mem.user, CY_UDP_SOCKET_READ_BUFFER_SIZE, dgram.data);
        return;
    }

    // Realloc the buffer to fit the actual size of the datagram to avoid inner fragmentation.
    void* const dgram_realloc = realloc(dgram.data, dgram.size);
    if (dgram_realloc != NULL) { // Sensible realloc implementations always succeed when shrinking.
        dgram.data = dgram_realloc;
        cy->mem_allocated_bytes -= (CY_UDP_SOCKET_READ_BUFFER_SIZE - dgram.size);
    }

    // Pass the data buffer into LibUDPard then into Cy for further processing. It takes ownership of the buffer.
    udpard_rx_port_t* const    port          = (topic != NULL) ? &topic->rx_port : &cy->p2p_port.base;
    const udpard_mem_deleter_t dgram_deleter = { .user = cy, .free = mem_free };
    const bool pushok = udpard_rx_port_push(&cy->udpard_rx, port, ts, remote_ep, dgram, dgram_deleter, iface_index);
    assert(pushok); // Push can only fail on invalid arguments, which we validate, so it must never fail.
    (void)pushok;
}

static cy_err_t spin_once_until(cy_udp_posix_t* const cy, const cy_us_t deadline)
{
    // Free up space in the TX queues and ensure all TX sockets are blocked before waiting.
    // This may invoke writes on sockets that are not really writeable but this is totally fine.
    udpard_tx_poll(&cy->udpard_tx, cy_udp_posix_now(), cy->iface_mask);

    // Fill out the TX awaitable array. May be empty if there's nothing to transmit at the moment.
    size_t         tx_count                               = 0;
    udp_wrapper_t* tx_await[CY_UDP_POSIX_IFACE_COUNT_MAX] = { 0 };
    const uint32_t tx_pending_iface_mask                  = udpard_tx_pending_iface_mask(&cy->udpard_tx);
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        if ((tx_pending_iface_mask & (1U << i)) != 0) {
            assert((cy->iface_mask & (1U << i)) != 0);
            tx_await[tx_count] = &cy->sock[i];
            tx_count++;
        }
    }
    // Fill out the RX awaitable array. The total number of RX sockets is the interface count times the number of topics
    // we are subscribed to plus P2P RX sockets (exactly one per iface). Currently, we don't have a simple value that
    // says how many topics we are subscribed to, so we simply use the total number of topics.
    // This is a rather cumbersome operation as we need to traverse the topic tree; perhaps we should switch to epoll?
    const size_t          max_rx_count = CY_UDP_POSIX_IFACE_COUNT_MAX * (cy->n_topics + 1);
    size_t                rx_count     = 0;
    udp_wrapper_t*        rx_await[max_rx_count]; // Initialization is not possible and is very wasteful anyway.
    cy_udp_posix_topic_t* rx_topics[max_rx_count];
    uint_fast8_t          rx_iface_indexes[max_rx_count];
    for (cy_udp_posix_topic_t* topic = (cy_udp_posix_topic_t*)cy_topic_iter_first(&cy->base); topic != NULL;
         topic                       = (cy_udp_posix_topic_t*)cy_topic_iter_next(&topic->base)) {
        if (cy_topic_has_subscribers(&topic->base)) {
            for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
                if (udp_wrapper_is_open(&topic->rx_sock[i])) {
                    assert(rx_count < max_rx_count);
                    rx_await[rx_count]         = &topic->rx_sock[i];
                    rx_topics[rx_count]        = topic;
                    rx_iface_indexes[rx_count] = i;
                    rx_count++;
                }
            }
        }
    }
    // Note that we may add the same socket both for reading and writing, which is fine.
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        if (udp_wrapper_is_open(&cy->sock[i])) {
            assert(rx_count < max_rx_count);
            rx_await[rx_count]         = &cy->sock[i];
            rx_topics[rx_count]        = NULL; // A P2P socket has no associated topic.
            rx_iface_indexes[rx_count] = i;
            rx_count++;
        }
    }

    // Do a blocking wait using the descriptors we have just prepared.
    const cy_us_t wait_timeout = deadline - min_i64(cy_udp_posix_now(), deadline);
    cy_err_t      res = err_from_udp_wrapper(udp_wrapper_wait(wait_timeout, tx_count, tx_await, rx_count, rx_await));
    if (res == CY_OK) {
        const cy_us_t now = cy_udp_posix_now(); // after unblocking
        for (size_t i = 0; i < rx_count; i++) {
            if (rx_await[i] != NULL) {
                read_socket(cy, now, rx_topics[i], rx_await[i], rx_iface_indexes[i]);
            }
        }
        // Remember that we need to periodically poll cy_update() even if no traffic is received.
        // The update should be invoked after all incoming transfers are handled in this cycle, not before.
        assert(res == CY_OK);
        res = cy_update(&cy->base);
        // While handling the events, we could have generated additional TX items, so we need to process them again.
        // We do it even in case of failure such that transient errors do not stall the TX queue.
        // We blindly attempt to transmit on all sockets disregarding their writeability state; if this becomes
        // a performance concern, we should consult with the wait results.
        udpard_tx_poll(&cy->udpard_tx, now, cy->iface_mask);
    }
    return res;
}

cy_err_t cy_udp_posix_spin_until(cy_udp_posix_t* const cy, const cy_us_t deadline)
{
    cy_err_t res = CY_OK;
    while (res == CY_OK) {
        const cy_us_t dl = min_i64_3(deadline, cy->base.heartbeat_next, cy->base.heartbeat_next_urgent);
        res              = spin_once_until(cy, dl);
        if (deadline <= cy_udp_posix_now()) {
            break;
        }
    }
    return res;
}

cy_err_t cy_udp_posix_spin_once(cy_udp_posix_t* const cy)
{
    assert(cy != NULL);
    const cy_us_t dl = min_i64_3(cy_udp_posix_now() + 1000, //
                                 cy->base.heartbeat_next,
                                 cy->base.heartbeat_next_urgent);
    return spin_once_until(cy, dl);
}

void cy_udp_posix_destroy(cy_udp_posix_t* const cy)
{
    if (cy != NULL) {
        cy_destroy(&cy->base);
        assert(cy->n_topics == 0); // cy_destroy() must clean up.
        udpard_rx_port_free(&cy->udpard_rx, &cy->p2p_port.base);
        udpard_tx_free(&cy->udpard_tx);
        for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
            udp_wrapper_close(&cy->sock[i]); // The handle may be invalid, but we don't care.
        }
    }
}
