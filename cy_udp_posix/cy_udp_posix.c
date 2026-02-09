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
#include "eui64.h"
#include "udp_wrapper.h"

#include <cy_platform.h>
#include <udpard.h>

#define RAPIDHASH_COMPACT
#include <rapidhash.h>

#ifndef __USE_POSIX199309 // NOLINT(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp)
#define __USE_POSIX199309 // NOLINT(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp)
#endif
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <errno.h>
#include <stdio.h>
#include <limits.h>

#if (CY_UDP_POSIX_IFACE_COUNT_MAX) != (UDPARD_IFACE_COUNT_MAX)
#error "CY_UDP_POSIX_IFACE_COUNT_MAX != UDPARD_IFACE_COUNT_MAX"
#endif

/// Maximum expected incoming datagram size. If larger jumbo frames are expected, this value should be increased.
/// Frames are always resized to the actual data size immediately after reading.
#ifndef CY_UDP_SOCKET_READ_BUFFER_SIZE
#define CY_UDP_SOCKET_READ_BUFFER_SIZE 2000
#endif

typedef struct cy_udp_posix_t
{
    cy_platform_t base;
    udpard_mem_t  mem;

    udpard_tx_t      udpard_tx;
    udpard_rx_t      udpard_rx;
    udpard_rx_port_t p2p_port;

    udp_wrapper_t sock[CY_UDP_POSIX_IFACE_COUNT_MAX]; ///< All TX and P2P RX.
    uint32_t      local_ip[CY_UDP_POSIX_IFACE_COUNT_MAX];
    uint16_t      local_tx_port[CY_UDP_POSIX_IFACE_COUNT_MAX];
    uint16_t      iface_bitmap; ///< Bitmap of valid interfaces based on local_ip[].

    uint64_t prng_state;

    cy_udp_posix_stats_t stats;
} cy_udp_posix_t;

static size_t  smaller(const size_t a, const size_t b) { return (a < b) ? a : b; }
static int64_t min_i64(const int64_t a, const int64_t b) { return (a < b) ? a : b; }
static int64_t min_i64_3(const int64_t a, const int64_t b, const int64_t c) { return min_i64(a, min_i64(b, c)); }

/// A simple hash for two u64 arguments based on the SplitMix64 finalizer.
/// Much better than a simple xor while not being too heavy.
static uint64_t hash2_u64(const uint64_t a, const uint64_t b)
{
    uint64_t x = a ^ (b + 0x9e3779b97f4a7c15ULL);
    x ^= (a >> 32U) ^ (b << 32U);
    x ^= x >> 30U;
    x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27U;
    x *= 0x94d049bb133111ebULL;
    x ^= x >> 31U;
    return x;
}

static bool is_valid_ip(const uint32_t ip) { return (ip > 0) && (ip < UINT32_MAX); }

static void* mem_alloc(void* const user, const size_t size)
{
    cy_udp_posix_t* const self = (cy_udp_posix_t*)user;
    void* const           out  = malloc(size);
    if (size > 0) {
        if (out != NULL) {
            self->stats.mem.allocated_fragments++;
            self->stats.mem.allocated_bytes += size;
        } else {
            self->stats.mem.oom_count++;
        }
    }
    return out;
}

static void* mem_alloc_zero(void* const user, const size_t size)
{
    void* const out = mem_alloc(user, size);
    if (out != NULL) {
        memset(out, 0, size);
    }
    return out;
}

static void mem_free(void* const user, const size_t size, void* const pointer)
{
    cy_udp_posix_t* const self = (cy_udp_posix_t*)user;
    (void)size;
    if (pointer != NULL) {
        assert(self->stats.mem.allocated_fragments > 0);
        self->stats.mem.allocated_fragments--;
        assert(self->stats.mem.allocated_bytes >= size);
        self->stats.mem.allocated_bytes -= size;
        memset(pointer, 0xA5, size); // a simple diagnostic aid
        free(pointer);
    }
}

static udpard_rx_mem_resources_t make_udpard_rx_mem_resources(cy_udp_posix_t* const self)
{
    return (udpard_rx_mem_resources_t){ .session = self->mem, .slot = self->mem, .fragment = self->mem };
}

static const udpard_mem_vtable_t mem_vtable = { .base = { .free = mem_free }, .alloc = mem_alloc };

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

typedef struct
{
    cy_message_t       base;
    cy_udp_posix_t*    owner;
    udpard_fragment_t* fragment;
    size_t             skip;
    size_t             size;
} message_t;

static void v_message_skip(cy_message_t* const base, const size_t offset)
{
    message_t* const self = (message_t*)base;
    self->skip += offset;
    self->size -= smaller(offset, self->size);
}

static size_t v_message_read(const cy_message_t* const base, const size_t offset, const size_t size, void* const dest)
{
    message_t* const self   = (message_t*)base;
    size_t           result = 0;
    if (offset < self->size) {
        const size_t to_read = smaller(size, self->size - offset);
        if (to_read > 0) {
            const udpard_fragment_t* cursor = self->fragment;
            result                          = udpard_fragment_gather(&cursor, offset + self->skip, to_read, dest);
        }
    }
    return result;
}

/// Specialization for single-fragment messages.
static size_t v_message_read_1(const cy_message_t* const base, const size_t offset, const size_t size, void* const dest)
{
    message_t* const self = (message_t*)base;
    assert((self->fragment->index_offset.lr[0] == NULL) && (self->fragment->index_offset.lr[1] == NULL));
    size_t out = 0;
    if (offset < self->size) {
        out = smaller(size, self->size - offset);
        memcpy(dest, ((const char*)self->fragment->view.data) + self->skip + offset, out);
    }
    return out;
}

static size_t v_message_size(const cy_message_t* const base) { return ((message_t*)base)->size; }

static void v_message_destroy(cy_message_t* const base)
{
    message_t* const self = (message_t*)base;
    udpard_fragment_free_all(self->fragment, udpard_make_deleter(self->owner->mem));
    self->fragment = NULL;
    mem_free(self->owner, sizeof(message_t), self);
}

static cy_message_t* make_message(cy_udp_posix_t* const owner, const size_t size, udpard_fragment_t* const frag)
{
    static const cy_message_vtable_t vtable = {
        .skip = v_message_skip, .read = v_message_read, .size = v_message_size, .destroy = v_message_destroy
    };
    static const cy_message_vtable_t vtable_1frame = {
        .skip = v_message_skip, .read = v_message_read_1, .size = v_message_size, .destroy = v_message_destroy
    };
    message_t* const msg = mem_alloc_zero(owner, sizeof(message_t));
    if (msg != NULL) {
        msg->base     = CY_MESSAGE_INIT((frag->view.size == size) ? &vtable_1frame : &vtable);
        msg->owner    = owner;
        msg->fragment = frag;
        msg->skip     = 0;
        msg->size     = size;
    }
    return (cy_message_t*)msg;
}

// ---------------------------------------- SUBJECT WRITER ----------------------------------------

/// NB: Once constructed, Cy will keep writers alive as long as possible even if the application doesn't need one to
/// avoid losing the transfer-ID state.
typedef struct
{
    cy_subject_writer_t base;
    cy_t*               cy;
    uint64_t            next_transfer_id; ///< Random-initialized at the time of creation.
    udpard_udpip_ep_t   endpoints[UDPARD_IFACE_COUNT_MAX];
} subject_writer_t;

static cy_err_t v_subject_writer_send(cy_subject_writer_t* const base,
                                      const cy_us_t              deadline,
                                      const cy_prio_t            priority,
                                      const cy_bytes_t           message)
{
    subject_writer_t* const self  = (subject_writer_t*)base;
    cy_udp_posix_t* const   owner = (cy_udp_posix_t*)cy_platform(self->cy);
    // We may need better error reporting in libudpard, this is a little unwieldy.
    const uint64_t e_oom      = owner->udpard_tx.errors_oom;
    const uint64_t e_capacity = owner->udpard_tx.errors_capacity;
    //
    const bool ok = udpard_tx_push(&owner->udpard_tx,
                                   cy_udp_posix_now(),
                                   deadline,
                                   owner->iface_bitmap,
                                   (udpard_prio_t)priority,
                                   self->next_transfer_id++,
                                   cy_bytes_to_udpard_bytes(message),
                                   NULL,
                                   (udpard_user_context_t){ .ptr = { base } });
    if (ok) {
        return CY_OK;
    }
    if (owner->udpard_tx.errors_oom > e_oom) {
        return CY_ERR_MEMORY;
    }
    if (owner->udpard_tx.errors_capacity > e_capacity) {
        return CY_ERR_CAPACITY;
    }
    return CY_ERR_ARGUMENT;
}

static void v_destroy(cy_subject_writer_t* const base)
{
    subject_writer_t* const self  = (subject_writer_t*)base;
    cy_udp_posix_t* const   owner = (cy_udp_posix_t*)cy_platform(self->cy);
    assert(owner->stats.subject_writer_count > 0);
    owner->stats.subject_writer_count--;
    CY_TRACE(self->cy, "🔇 n_writers=%zu ptr=%p", owner->stats.subject_writer_count, (void*)self);
    mem_free(owner, sizeof(subject_writer_t), self);
}

static cy_subject_writer_t* v_subject_writer(cy_t* const cy, const uint32_t subject_id)
{
    assert(subject_id <= UDPARD_IPv4_SUBJECT_ID_MAX);
    cy_udp_posix_t* const owner = (cy_udp_posix_t*)cy_platform(cy);
    assert(subject_id <= (CY_PINNED_SUBJECT_ID_MAX + 1 + owner->base.subject_id_modulus));
    subject_writer_t* const self = mem_alloc_zero(owner, sizeof(subject_writer_t));
    if (self != NULL) {
        static const cy_subject_writer_vtable_t vtable = { .send = v_subject_writer_send, .destroy = v_destroy };
        self->base.vtable                              = &vtable;
        self->cy                                       = cy;
        self->next_transfer_id                         = prng64(&owner->prng_state, owner->udpard_tx.local_uid);
        for (size_t i = 0; i < UDPARD_IFACE_COUNT_MAX; i++) {
            if ((owner->iface_bitmap & (1U << i)) != 0) {
                self->endpoints[i] = udpard_make_subject_endpoint(subject_id);
            } else {
                self->endpoints[i] = (udpard_udpip_ep_t){ 0 };
            }
        }
        owner->stats.subject_writer_count++;
    }
    CY_TRACE(cy, "🔊 n_writers=%zu subject_id=%08x ptr=%p", owner->stats.subject_writer_count, subject_id, (void*)self);
    return (cy_subject_writer_t*)self;
}

// ---------------------------------------- SUBJECT READER ----------------------------------------

typedef struct
{
    cy_subject_reader_t base;
    cy_t*               cy;

    udpard_rx_port_t port;
    udp_wrapper_t    sock[CY_UDP_POSIX_IFACE_COUNT_MAX];

    /// The history is only used with stateless subscriptions to reject the most obvious duplicates.
    /// It is essentially optional, but it is expected to save quite a bit of processing on busy topics,
    /// in particular in the heartbeat topic when used in a large network with redundant interfaces.
    uint64_t history[2];
} subject_reader_t;

typedef struct
{
    udpard_udpip_ep_t endpoints[UDPARD_IFACE_COUNT_MAX];
    udpard_prio_t     priority;
} p2p_ctx_t;

static void v_on_msg(udpard_rx_t* const rx, udpard_rx_port_t* const port, const udpard_rx_transfer_t tr)
{
    cy_udp_posix_t* const   owner       = rx->user;
    subject_reader_t* const self        = port->user;
    cy_p2p_context_t        p2p_context = { { 0 } };
    {
        p2p_ctx_t inner = { .priority = tr.priority };
        for (size_t i = 0; i < UDPARD_IFACE_COUNT_MAX; i++) {
            inner.endpoints[i] = tr.remote.endpoints[i];
        }
        static_assert(sizeof(inner) <= sizeof(p2p_context), "");
        memcpy(&p2p_context, &inner, sizeof(inner));
    }
    const cy_message_ts_t msg = { .timestamp = tr.timestamp,
                                  .content   = make_message(owner, tr.payload_size_stored, tr.payload) };
    if (msg.content != NULL) {
        cy_on_message(self->cy, p2p_context, tr.remote.uid, &self->base, msg);
    } else {
        udpard_fragment_free_all(tr.payload, udpard_make_deleter(owner->mem));
    }
}

static void v_on_msg_stateless(udpard_rx_t* const rx, udpard_rx_port_t* const port, const udpard_rx_transfer_t tr)
{
    subject_reader_t* const self = port->user;
    static_assert(sizeof(self->history) / sizeof(self->history[0]) == 2, "");
    // In the stateless mode, libudpard does not bother deduplicating messages. The heartbeat subscriber does not
    // care about duplicates, so we could just pass all messages as-is and it will work fine, but it would waste
    // CPU cycles because each message requires some log-time index lookups.
    // We can mitigate this by applying a very simple filter that is cheap and computationally negligible.
    // It doesn't have to remove all duplicates -- removing the most obvious ones is sufficient to be useful.
    const uint64_t msg_fingerprint = hash2_u64(tr.transfer_id, tr.remote.uid);
    const bool     dup             = (self->history[0] == msg_fingerprint) || (self->history[1] == msg_fingerprint);
    if (!dup) {
        self->history[1] = self->history[0];
        self->history[0] = msg_fingerprint;
        v_on_msg(rx, port, tr);
    } else {
        CY_TRACE(self->cy,
                 "🍒️ S%08llx #%016llx N%016llx 👆%016llx duplicate dropped",
                 (unsigned long long)self->base.subject_id,
                 (unsigned long long)tr.transfer_id,
                 (unsigned long long)tr.remote.uid,
                 (unsigned long long)msg_fingerprint);
    }
}

static void v_subject_reader_destroy(cy_subject_reader_t* const base)
{
    subject_reader_t* const self  = (subject_reader_t*)base;
    cy_udp_posix_t* const   owner = (cy_udp_posix_t*)cy_platform(self->cy);
    assert(self->port.user == self);
    udpard_rx_port_free(&owner->udpard_rx, &self->port);
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        udp_wrapper_close(&self->sock[i]); // closing a non-open socket is a safe noop.
    }
    CY_TRACE(self->cy, "🔕 n_readers=%zu ptr=%p", owner->stats.subject_reader_count, (void*)self);
    mem_free(owner, sizeof(subject_reader_t), self);
    assert(owner->stats.subject_reader_count > 0);
    owner->stats.subject_reader_count--;
}

static cy_subject_reader_t* v_subject_reader(cy_t* const cy, const uint32_t subject_id, const size_t extent)
{
    assert(subject_id <= UDPARD_IPv4_SUBJECT_ID_MAX);
    cy_udp_posix_t* const owner = (cy_udp_posix_t*)cy_platform(cy);
    assert(subject_id <= (CY_PINNED_SUBJECT_ID_MAX + 1 + owner->base.subject_id_modulus));
    subject_reader_t* self = mem_alloc_zero(owner, sizeof(subject_reader_t));
    if (self != NULL) {
        static const cy_subject_reader_vtable_t reader_vtable = { .destroy = v_subject_reader_destroy };
        self->base.subject_id                                 = subject_id;
        self->base.vtable                                     = &reader_vtable;
        self->cy                                              = cy;

        // We special-case the heartbeat topic to have STATELESS reassembly strategy to conserve CPU and RAM.
        // It is useful for the network stack because the heartbeat topic is a bottleneck to be aware of -- every
        // node publishes on it and every node is subscribed, so there is a lot of traffic, while the protocol stack
        // itself is invariant to heartbeat message reordering/duplicates.
        const bool stateless = subject_id == CY_HEARTBEAT_TOPIC_HASH;
        bool       ok        = false;
        if (!stateless) {
            static const udpard_rx_port_vtable_t port_vtbl = { .on_message = v_on_msg };
            ok = udpard_rx_port_new(&self->port, extent, make_udpard_rx_mem_resources(owner), &port_vtbl);
        } else {
            static const udpard_rx_port_vtable_t port_vtbl = { .on_message = v_on_msg_stateless };
            ok = udpard_rx_port_new_stateless(&self->port, extent, make_udpard_rx_mem_resources(owner), &port_vtbl);
        }
        if (!ok) {
            mem_free(owner, sizeof(subject_reader_t), self);
            self = NULL;
            goto reject;
        }
        self->port.user = self;

        // Open the sockets for this port.
        const udpard_udpip_ep_t endpoint = udpard_make_subject_endpoint(subject_id);
        cy_err_t                res      = CY_OK;
        for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
            self->sock[i] = udp_wrapper_new();
            if ((res == CY_OK) && ((owner->iface_bitmap & (1U << i)) != 0)) {
                res = err_from_udp_wrapper(
                  udp_wrapper_open_multicast(&self->sock[i], owner->local_ip[i], endpoint.ip, endpoint.port));
            }
        }

        // Cleanup on error.
        if (res != CY_OK) {
            udpard_rx_port_free(&owner->udpard_rx, &self->port);
            for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
                udp_wrapper_close(&self->sock[i]);
            }
            mem_free(owner, sizeof(subject_reader_t), self);
            self = NULL;
            goto reject;
        }
        owner->stats.subject_reader_count++;
    }
reject:
    CY_TRACE(cy, "🔔 n_readers=%zu subject_id=%08x ptr=%p", owner->stats.subject_reader_count, subject_id, (void*)self);
    return (cy_subject_reader_t*)self;
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

/// Invoked by Cy when the application desires to respond to a message received earlier.
static cy_err_t v_p2p(cy_t* const                    cy,
                      const cy_p2p_context_t* const  p2p_context,
                      const cy_us_t                  deadline,
                      const uint64_t                 remote_id,
                      const cy_bytes_t               message,
                      cy_cancellation_token_t* const out_cancellation_token,
                      void* const                    reliable_context,
                      void (*const reliable_feedback)(void* reliable_context, bool acknowledged))
{
    cy_udp_posix_t* const cy_udp   = (cy_udp_posix_t*)cy;
    const bool            reliable = reliable_feedback != NULL;

    // Unbox the P2P context.
    p2p_ctx_t inner;
    static_assert(sizeof(inner) <= sizeof(cy_p2p_context_t), "");
    memcpy(&inner, p2p_context, sizeof(inner));
    udpard_remote_t remote = { .uid = remote_id };
    for (size_t i = 0; i < UDPARD_IFACE_COUNT_MAX; i++) {
        remote.endpoints[i] = inner.endpoints[i];
    }

    // Set up libudpard context for the callback.
    udpard_user_context_t udpard_context = UDPARD_USER_CONTEXT_NULL;
    if (reliable) {
        const p2p_feedback_context_t boxed = { .context = reliable_context, .feedback = reliable_feedback };
        static_assert(sizeof(boxed) <= sizeof(udpard_context), "");
        memcpy(&udpard_context, &boxed, sizeof(boxed)); // respect strict aliasing
    }

    // The other part of the cancellation token is set later.
    if (out_cancellation_token != NULL) {
        out_cancellation_token->id[0] = remote_id; // Takes the place of the topic hash in normal publications.
    }

    // Push the message.
    // We need better error reporting in libudpard, this is really unwieldy.
    const uint64_t e_oom      = cy_udp->udpard_tx.errors_oom;
    const uint64_t e_capacity = cy_udp->udpard_tx.errors_capacity;
    //
    const bool ok = udpard_tx_push_p2p(&cy_udp->udpard_tx,
                                       cy_udp_posix_now(),
                                       deadline,
                                       inner.priority,
                                       remote,
                                       cy_bytes_to_udpard_bytes(message),
                                       reliable ? on_p2p_feedback : NULL,
                                       udpard_context,
                                       (out_cancellation_token == NULL) ? NULL : &out_cancellation_token->id[1]);

    // Report the result.
    CY_TRACE(cy, "💬 N%016llx res=%u", (unsigned long long)remote.uid, ok);
    if (ok) {
        return CY_OK;
    }
    if (cy_udp->udpard_tx.errors_oom > e_oom) {
        return CY_ERR_MEMORY;
    }
    if (cy_udp->udpard_tx.errors_capacity > e_capacity) {
        return CY_ERR_CAPACITY;
    }
    return CY_ERR_ARGUMENT;
}

static const cy_vtable_t cy_vtable = { .now                   = v_now,
                                       .realloc               = v_realloc,
                                       .random                = v_random,
                                       .new_topic             = v_topic_new,
                                       .p2p                   = v_p2p,
                                       .cancel                = v_cancel,
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
static void v_on_p2p_msg(udpard_rx_t* const rx, udpard_rx_port_t* const port, const udpard_rx_transfer_t tr)
{
    cy_udp_posix_t* const cy = rx->user;
    assert((cy != NULL) && (port == &cy->p2p_port));
    (void)port;
    const cy_message_ts_t msg = { .timestamp = tr.timestamp,
                                  .content   = make_message(cy, tr.payload_size_stored, tr.payload) };
    cy_on_p2p(&cy->base, tr.remote.uid, msg);
}

static bool v_tx_eject_p2p(udpard_tx_t* const tx, udpard_tx_ejection_t* const ej, const udpard_udpip_ep_t destination)
{
    cy_udp_posix_t* const cy = (cy_udp_posix_t*)tx->user;
    assert(cy != NULL);
    assert((cy->iface_bitmap & (1U << ej->iface_index)) != 0); // the caller must ensure this
    assert(ej->now <= ej->deadline);
    // The libudpard TX API provides us with an opportunity to retain the ownership of the datagram payload
    // via reference counting. This is useful in kernel space or in embedded systems with low-level NIC drivers,
    // but the Berkeley socket API does not allow us to take advantage of that -- the data will be copied into the
    // kernel space anyway. Therefore, we simply send it with copying and do not bother with reference counting.
    const int16_t res = udp_wrapper_send(&cy->sock[ej->iface_index], //
                                         destination.ip,
                                         destination.port,
                                         ej->dscp,
                                         ej->datagram.size,
                                         ej->datagram.data);
    if (res < 0) {
        assert(cy->tx_sock_err_handler != NULL);
        cy->tx_sock_err_handler(cy, ej->iface_index, (uint32_t)-res);
    }
    return res != 0; // either transmitted successfully or dropped due to error
}

static bool v_tx_eject_subject(udpard_tx_t* const tx, udpard_tx_ejection_t* const ej)
{
    const subject_writer_t* const writer = ej->user.ptr[0];
    return v_tx_eject_p2p(tx, ej, writer->endpoints[0]); // TODO FIXME this is incorrect; supply endpoint at TX time!
}

static const udpard_tx_vtable_t tx_vtable = { .eject_subject = v_tx_eject_subject, .eject_p2p = v_tx_eject_p2p };

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
    cy->mem                     = (udpard_mem_t){ .vtable = &mem_vtable, .context = cy };
    cy->iface_bitmap            = 0;
    cy->rx_sock_err_handler     = default_rx_sock_err_handler;
    cy->tx_sock_err_handler     = default_tx_sock_err_handler;
    cy->mem_allocated_fragments = 0;
    cy->mem_oom_count           = 0;

    // This PRNG state seed is only valid if a true RTC is available. Otherwise, use other sources of entropy.
    // Refer to cy_platform.h docs for some hints on how to make it work on an MCU without a TRNG nor RTC.
    cy->prng_state = (uint64_t)time(NULL);

    // Set up the TX and RX pipelines.
    const udpard_rx_mem_resources_t rx_mem = { .fragment = cy->mem, .session = cy->mem };
    udpard_tx_mem_resources_t       tx_mem = { .transfer = cy->mem };
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        cy->sock[i] = udp_wrapper_new();
        if (is_valid_ip(local_iface_address[i])) {
            cy->local_ip[i] = local_iface_address[i];
            cy->iface_bitmap |= 1U << i;
        } else {
            cy->local_ip[i] = 0;
        }
        tx_mem.payload[i] = cy->mem;
    }
    if (cy->iface_bitmap == 0) {
        return CY_ERR_ARGUMENT;
    }
    if (!udpard_tx_new(&cy->udpard_tx, uid, prng64(&cy->prng_state, uid), tx_queue_capacity, tx_mem, &tx_vtable)) {
        return CY_ERR_ARGUMENT; // Cleanup not required -- no resources allocated yet.
    }
    udpard_rx_new(&cy->udpard_rx, &cy->udpard_tx); // infallible
    cy->udpard_tx.user = cy;
    cy->udpard_rx.user = cy;

    // Initialize the udpard P2P RX port.
    // We start with an arbitrarily chosen sensible initial extent, which will be increased later as needed.
    const size_t                         initial_extent = UDPARD_MTU_DEFAULT;
    static const udpard_rx_port_vtable_t rx_p2p_vtable  = { .on_message = v_on_p2p_msg, .on_collision = NULL };
    if (!udpard_rx_port_new(&cy->p2p_port, uid, initial_extent, udpard_rx_unordered, 0, rx_mem, &rx_p2p_vtable)) {
        return CY_ERR_ARGUMENT; // Cleanup not required -- no resources allocated yet.
    }

    // Initialize the sockets.
    cy_err_t res = CY_OK;
    for (uint_fast8_t i = 0; (i < CY_UDP_POSIX_IFACE_COUNT_MAX) && (res == CY_OK); i++) {
        if ((cy->iface_bitmap & (1U << i)) != 0) {
            res = err_from_udp_wrapper(udp_wrapper_open_unicast(&cy->sock[i], cy->local_ip[i], &cy->local_tx_port[i]));
        }
    }

    // Cleanup on error.
    if (res != CY_OK) {
        udpard_rx_port_free(&cy->udpard_rx, &cy->p2p_port);
        udpard_tx_free(&cy->udpard_tx);
        for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
            udp_wrapper_close(&cy->sock[i]); // The handle may be invalid, but we don't care.
        }
    }
    return res;
}

cy_err_t cy_udp_posix_new_simple(cy_udp_posix_t* const cy)
{
    const uint64_t uid = eui64_semirandom();
    if (uid == 0) {
        return CY_ERR_MEDIA;
    }
    uint32_t      ifaces[CY_UDP_POSIX_IFACE_COUNT_MAX] = { 0 };
    const int16_t n_if = udp_wrapper_get_default_ifaces(CY_UDP_POSIX_IFACE_COUNT_MAX, ifaces);
    if (n_if < 0) {
        return err_from_udp_wrapper(n_if);
    }
    assert(n_if > 0);
    const cy_err_t out = cy_udp_posix_new(cy, uid, wkv_key(""), wkv_key(""), ifaces, 50000);
#if CY_CONFIG_TRACE
    CY_TRACE(&cy->base, "🏷 Semirandom EUI-64 %016llx", (unsigned long long)uid);
    for (int16_t i = 0; i < n_if; i++) {
        const uint32_t f = ifaces[i];
        CY_TRACE(&cy->base,
                 "🔌 Autodetected default iface #%d of %d: %u.%u.%u.%u",
                 i,
                 n_if,
                 (f >> 24U) & 0xFFU,
                 (f >> 16U) & 0xFFU,
                 (f >> 8U) & 0xFFU,
                 f & 0xFFU);
    }
#endif
    return out;
}

static void read_socket(cy_udp_posix_t* const       cy,
                        const cy_us_t               ts,
                        cy_udp_posix_topic_t* const topic,
                        udp_wrapper_t* const        sock,
                        const uint_fast8_t          iface_index)
{
    assert((cy->iface_bitmap & (1U << iface_index)) != 0);
    assert(is_valid_ip(cy->local_ip[iface_index]));
    assert(udp_wrapper_is_open(sock));

    // Allocate memory that we will read the data into. The ownership of this memory will be transferred
    // to LibUDPard, which will free it when it is no longer needed.
    // A deeply embedded system may be able to transfer this memory directly from the NIC driver to eliminate copy.
    udpard_bytes_mut_t dgram = { .size = CY_UDP_SOCKET_READ_BUFFER_SIZE,
                                 .data = cy->mem.vtable->alloc(cy->mem.context, CY_UDP_SOCKET_READ_BUFFER_SIZE) };
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
        cy->mem.vtable->base.free(cy->mem.context, CY_UDP_SOCKET_READ_BUFFER_SIZE, dgram.data);
        ((topic != NULL) ? topic->rx_sock_err_handler
                         : cy->rx_sock_err_handler)(cy, topic, iface_index, (uint32_t)-rx_result);
        return;
    }
    if (rx_result == 0) { // Nothing to read OR dgram dropped by filters.
        cy->mem.vtable->base.free(cy->mem.context, CY_UDP_SOCKET_READ_BUFFER_SIZE, dgram.data);
        return;
    }
    // Ignore packets we sent ourselves. This can happen with multicast depending on the socket implementation.
    if ((remote_ep.ip == cy->local_ip[iface_index]) && (remote_ep.port == cy->local_tx_port[iface_index])) {
        cy->mem.vtable->base.free(cy->mem.context, CY_UDP_SOCKET_READ_BUFFER_SIZE, dgram.data);
        return;
    }

    // Realloc the buffer to fit the actual size of the datagram to avoid inner fragmentation.
    void* const dgram_realloc = realloc(dgram.data, dgram.size);
    if (dgram_realloc != NULL) { // Sensible realloc implementations always succeed when shrinking.
        dgram.data = dgram_realloc;
        cy->mem_allocated_bytes -= (CY_UDP_SOCKET_READ_BUFFER_SIZE - dgram.size);
    }

    // Pass the data buffer into LibUDPard then into Cy for further processing. It takes ownership of the buffer.
    const bool pushok = udpard_rx_port_push(&cy->udpard_rx,
                                            (topic != NULL) ? &topic->rx_port : &cy->p2p_port,
                                            ts,
                                            remote_ep,
                                            dgram,
                                            udpard_make_deleter(cy->mem),
                                            iface_index);
    assert(pushok); // Push can only fail on invalid arguments, which we validate, so it must never fail.
    (void)pushok;
}

static cy_err_t spin_once_until(cy_udp_posix_t* const cy, const cy_us_t deadline)
{
    // Free up space in the TX queues and ensure all TX sockets are blocked before waiting.
    // This may invoke writes on sockets that are not really writeable but this is totally fine.
    udpard_tx_poll(&cy->udpard_tx, cy_udp_posix_now(), cy->iface_bitmap);

    // Fill out the TX awaitable array. May be empty if there's nothing to transmit at the moment.
    size_t         tx_count                               = 0;
    udp_wrapper_t* tx_await[CY_UDP_POSIX_IFACE_COUNT_MAX] = { 0 };
    const uint16_t tx_pending_iface_bitmap                = udpard_tx_pending_ifaces(&cy->udpard_tx);
    for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        if ((tx_pending_iface_bitmap & (1U << i)) != 0) {
            assert((cy->iface_bitmap & (1U << i)) != 0);
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
        udpard_tx_poll(&cy->udpard_tx, now, cy->iface_bitmap);
        // Update expiration and reordering timers once.
        udpard_rx_poll(&cy->udpard_rx, now);
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

void cy_udp_posix_destroy(cy_udp_posix_t* const cy)
{
    if (cy != NULL) {
        assert(cy->n_topics == 0);
        udpard_rx_port_free(&cy->udpard_rx, &cy->p2p_port);
        udpard_tx_free(&cy->udpard_tx);
        for (uint_fast8_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
            udp_wrapper_close(&cy->sock[i]); // The handle may be invalid, but we don't care.
        }
    }
}
