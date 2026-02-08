///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>
///
/// -------------------------------------------------------------------------------------------------------------------
/// TRANSPORT LAYER REQUIREMENTS
///
/// The transport layer provides UNRELIABLE DEDUPLICATED (at most one) UNORDERED DELIVERY of messages either to;
///     - A GROUP OF SUBSCRIBERS on a given SUBJECT identified with a numerical subject-ID (IGMP group, CAN ID, etc).
///     - A specified REMOTE NODE direct PEER-TO-PEER.
///
/// The transport layer supports messages of arbitrary size, providing SEGMENTATION/REASSEMBLY transparently to the
/// higher layers.
///
/// The transport layer DOES NOT provide message ordering recovery or reliable delivery (messages may arrive out of
/// order or may not arrive at all).
///
/// The transport layer provides network participant discovery as a side effect of joining a specified subject.
///
/// --------------------------------------------------------------------------------------------------------------------
/// SESSION LAYER MESSAGE HEADER
///
/// Message transfers over non-pinned topics carry a header.
/// TODO: Pinned topics on CAN must have no header to ensure backward compatibility, sort this out later.
///
/// The message tags must be unique across reboots to avoid misattribution (use random init), also unique per message;
/// subsequent tags of a message must be incremented by one to allow ordering recovery and loss detection.
///
/// Response tags are not used for ordering recovery since there is a seqno available, and there is no risk of reboot
/// misattribution -- they are only needed for acknowledgement correlation and as such they are much narrower
/// and there is no monotonicity requirement, the sender can choose values arbitrarily. The correlation tag for
/// response ack is formed as seqno|(tag<<48) to ensure uniqueness.
///
/// The payload follows immediately after the header. The header fields are not naturally aligned to conserve space.
/// The type field is always in the first byte of the header. Void fields are sent zero and ignored on reception.
///
/// Message publications have no negative acknowledgements because they are inherently multicast: even if we can't
/// accept a message, someone else might be able to. For P2P NACKs are well-defined since these interactions are
/// always unicast.
///
/// type = 0: Best-effort message.
/// type = 1: Reliable message. Expects ack with the specified tag.
/// type = 2: Reliable message acknowledgement: message received by the session layer; there is a live subscription.
///
///     uint5  type
///     void3
///     uint56 tag              # For ordering recovery and for acknowledgement and response correlation.
///     uint64 topic_hash       # For subject allocation collision detection.
///     # Header size 16 bytes.
///
/// type = 3: Best-effort response to a message received earlier.
/// type = 4: Reliable response to a message received earlier.
/// type = 5: Reliable response acknowledgement: response received; there is a matching pending request.
/// type = 6: Reliable response negative-acknowledgement: response DISCARDED -- there is NO matching pending request.
///
///     uint5  type
///     void3
///     uint56 message_tag
///     uint48 seqno
///     uint16 tag
///     # Header size 16 bytes.
///
/// --------------------------------------------------------------------------------------------------------------------
///
/// The transport delivers deduplicated messages, but duplication due to retransmission in case of lost acks may still
/// occur (for the transport such messages are seen as distinct). To mitigate, additional deduplication is performed
/// at the session layer for reliable messages only based on their tags.

// ReSharper disable CppDFATimeOver
// ReSharper disable CppDFAConstantParameter
// ReSharper disable CppDFANullDereference

#include "cy_platform.h"

#define CAVL2_RELATION int32_t
#define CAVL2_T        cy_tree_t
#include <cavl2.h>
#include <olga_scheduler.h>

#define RAPIDHASH_COMPACT // because we hash strings <96 bytes long
#include <rapidhash.h>

#include <assert.h>
#include <string.h>

// TODO FIXME REMOVE WHEN REFACTORING DONE
#pragma GCC diagnostic ignored "-Wunused-function"

#if __STDC_VERSION__ < 201112L
#define static_assert(x, ...)        typedef char _static_assert_gl(_static_assertion_, __LINE__)[(x) ? 1 : -1]
#define _static_assert_gl(a, b)      _static_assert_gl_impl(a, b)
#define _static_assert_gl_impl(a, b) a##b
#endif

#if __STDC_VERSION__ >= 201112L
#define CY_THREAD_LOCAL _Thread_local
#else
#define CY_THREAD_LOCAL
#endif

#define KILO 1000LL
#define MEGA 1000000LL

/// The earliest and latest representable time in microseconds.
#define BIG_BANG   INT64_MIN
#define HEAT_DEATH INT64_MAX

/// The log-age of a newly created topic.
#define LAGE_MIN (-1)
/// A special log-age value that indicates that the gossip is a scout message (pattern match request).
#define LAGE_SCOUT (-2)

/// A topic created based on a pattern subscription will be deleted after it's been idle for this long.
/// Here, "idle" means no messages received from this topic and no gossips seen on the network.
/// Topics created explicitly by the application (without substitution tokens) are not affected by this timeout.
#define IMPLICIT_TOPIC_DEFAULT_TIMEOUT_us (3600 * MEGA)

/// Used to derive the actual ack timeout; see the publisher.
#define ACK_BASELINE_DEFAULT_TIMEOUT_us (16 * KILO)

/// Pending ack transfers will timeout from the tx buffer after this time if not transmitted (interface stalled).
#define ACK_TX_TIMEOUT MEGA

/// Soft states associated with a remote node publishing on a topic or P2P will be discarded when stale for this long.
#define SESSION_LIFETIME (60 * MEGA)

#define UINTMAX_BITS ((int)(sizeof(uintmax_t) * CHAR_BIT))

#define TREE_NULL ((cy_tree_t){ NULL, { NULL, NULL }, 0 })

static const wkv_str_t str_invalid = { .len = SIZE_MAX, .str = NULL };

typedef unsigned char byte_t;

/// The maximum header size is needed to calculate the extent correctly.
/// It is added to the serialized message size.
/// Later revisions of the protocol may increase this size, although it is best to avoid it if possible.
#define HEADER_MAX_BYTES 16U

#define HEADER_TYPE_MASK 31U
typedef enum
{
    header_msg_be   = 0,
    header_msg_rel  = 1,
    header_msg_ack  = 2,
    header_rsp_be   = 3,
    header_rsp_rel  = 4,
    header_rsp_ack  = 5,
    header_rsp_nack = 6,
} header_type_t;

#define SEQNO48_MASK ((1ULL << 48U) - 1ULL)

#define TAG56_MASK ((1ULL << 56U) - 1ULL)

/// The number of increments to a needed to reach a==b.
static inline uint64_t tag56_forward_distance(uint64_t a, uint64_t b)
{
    a &= TAG56_MASK;
    b &= TAG56_MASK;
    return (b - a) & TAG56_MASK; // in [0, 2^56)
}

static inline uint64_t tag56_add(const uint64_t a, const uint64_t b)
{
    return ((a & TAG56_MASK) + (b & TAG56_MASK)) & TAG56_MASK;
}

static size_t  larger(const size_t a, const size_t b) { return (a > b) ? a : b; }
static size_t  smaller(const size_t a, const size_t b) { return (a < b) ? a : b; }
static int64_t max_i64(const int64_t a, const int64_t b) { return (a > b) ? a : b; }
static int64_t min_i64(const int64_t a, const int64_t b) { return (a < b) ? a : b; }

/// Returns -1 if the argument is zero to allow contiguous comparison.
static int_fast8_t log2_floor(const uint64_t x) { return (int_fast8_t)((x == 0) ? -1 : (63 - __builtin_clzll(x))); }

/// The inverse of log2_floor() with the same special case: exp=-1 returns 0.
static cy_us_t pow2us(const int_fast8_t exp)
{
    if (exp < 0) {
        return 0;
    }
    if (exp > 62) {
        return INT64_MAX;
    }
    return 1LL << (uint_fast8_t)exp; // NOLINT(*-signed-bitwise)
}

/// The limits are inclusive. Returns min unless min < max.
static int64_t random_int(cy_t* const cy, const int64_t min, const int64_t max)
{
    if (min < max) {
        return (int64_t)(cy->vtable->random(cy) % (uint64_t)(max - min)) + min;
    }
    return min;
}
static int64_t dither_int(cy_t* const cy, const int64_t mean, const int64_t deviation)
{
    return mean + random_int(cy, -deviation, +deviation);
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void* wkv_realloc(wkv_t* const self, void* ptr, const size_t new_size)
{
    return ((cy_t*)self->context)->vtable->realloc((cy_t*)self->context, ptr, new_size);
}

static void* mem_alloc(cy_t* const cy, const size_t size) { return cy->vtable->realloc(cy, NULL, size); }
static void* mem_alloc_zero(cy_t* const cy, const size_t size)
{
    void* const out = mem_alloc(cy, size);
    if (out != NULL) {
        memset(out, 0, size);
    }
    return out;
}

static void mem_free(cy_t* const cy, void* ptr)
{
    if (ptr != NULL) {
        cy->vtable->realloc(cy, ptr, 0);
    }
}

/// Simply returns the value of the first hit. Useful for existence checks.
static void* wkv_cb_first(const wkv_event_t evt) { return evt.node->value; }

/// For debug invariant checking only; linear complexity.
static size_t cavl_count(cy_tree_t* const root)
{
    size_t count = 0;
    for (cy_tree_t* p = cavl2_min(root); p != NULL; p = cavl2_next_greater(p)) {
        count++;
    }
    return count;
}

#if CY_CONFIG_TRACE

/// Converts `bit_width` least significant bits rounded up to the nearest nibble to hexadecimal.
/// The output string must be at least ceil(bit_width/4)+1 chars long. It will be left-zero-padded and NUL-terminated.
static wkv_str_t to_hex(uint64_t value, const size_t bit_width, char* const out)
{
    if (out == NULL) {
        return str_invalid;
    }
    const size_t len = (bit_width + 3) / 4;
    for (int_fast8_t i = (int_fast8_t)(len - 1U); i >= 0; --i) {
        out[i] = "0123456789abcdef"[value & 15U];
        value >>= 4U;
    }
    out[len] = '\0';
    return (wkv_str_t){ .len = len, .str = out };
}

/// A human-friendly representation of the topic for logging and diagnostics.
typedef struct
{
    char str[CY_TOPIC_NAME_MAX + 32];
} topic_repr_t;
static topic_repr_t topic_repr(const cy_topic_t* const topic)
{
    assert(topic != NULL);
    topic_repr_t out = { 0 };
    char*        ptr = out.str;
    *ptr++           = 'T';
    ptr += to_hex(topic->hash, 64, ptr).len;
    *ptr++ = '@';
    ptr += to_hex(cy_topic_subject_id(topic), 32, ptr).len;
    *ptr++               = '\'';
    const wkv_str_t name = cy_topic_name(topic);
    memcpy(ptr, name.str, name.len);
    ptr += name.len;
    *ptr++ = '\'';
    *ptr   = '\0';
    assert((ptr - out.str) <= (ptrdiff_t)sizeof(out.str));
    return out;
}

#endif

// SERIALIZATION PRIMITIVES

static byte_t* serialize_u32(byte_t* ptr, const uint32_t value)
{
    for (size_t i = 0; i < 4; i++) {
        *ptr++ = (byte_t)((byte_t)(value >> (i * 8U)) & 0xFFU);
    }
    return ptr;
}
static byte_t* serialize_u40(byte_t* ptr, const uint64_t value)
{
    for (size_t i = 0; i < 5; i++) {
        *ptr++ = (byte_t)((byte_t)(value >> (i * 8U)) & 0xFFU);
    }
    return ptr;
}
static byte_t* serialize_u64(byte_t* ptr, const uint64_t value)
{
    for (size_t i = 0; i < 8; i++) {
        *ptr++ = (byte_t)((byte_t)(value >> (i * 8U)) & 0xFFU);
    }
    return ptr;
}
static uint64_t deserialize_u40(const byte_t* ptr)
{
    uint64_t value = 0;
    for (size_t i = 0; i < 5; i++) {
        value |= ((uint64_t)*ptr++ << (i * 8U));
    }
    return value;
}
static uint64_t deserialize_u56(const byte_t* ptr)
{
    uint64_t value = 0;
    for (size_t i = 0; i < 7; i++) {
        value |= ((uint64_t)*ptr++ << (i * 8U));
    }
    return value;
}
static uint64_t deserialize_u64(const byte_t* ptr)
{
    uint64_t value = 0;
    for (size_t i = 0; i < 8; i++) {
        value |= ((uint64_t)*ptr++ << (i * 8U));
    }
    return value;
}

// =====================================================================================================================
//                                                    LIST UTILITIES
// =====================================================================================================================

static bool is_listed(const cy_list_t* const list, const cy_list_member_t* const member)
{
    return (member->next != NULL) || (member->prev != NULL) || (list->head == member);
}

/// No effect if not in the list.
static void delist(cy_list_t* const list, cy_list_member_t* const member)
{
    if (member->next != NULL) {
        member->next->prev = member->prev;
    }
    if (member->prev != NULL) {
        member->prev->next = member->next;
    }
    if (list->head == member) {
        list->head = member->next;
    }
    if (list->tail == member) {
        list->tail = member->prev;
    }
    member->next = NULL;
    member->prev = NULL;
    assert((list->head != NULL) == (list->tail != NULL));
}

/// If the item is already in the list, it will be delisted first. Can be used for moving to the front.
static void enlist_head(cy_list_t* const list, cy_list_member_t* const member)
{
    delist(list, member);
    assert((member->next == NULL) && (member->prev == NULL));
    assert((list->head != NULL) == (list->tail != NULL));
    member->next = list->head;
    if (list->head != NULL) {
        list->head->prev = member;
    }
    list->head = member;
    if (list->tail == NULL) {
        list->tail = member;
    }
    assert((list->head != NULL) && (list->tail != NULL));
}

#define LIST_MEMBER(ptr, owner_type, owner_field) ((owner_type*)ptr_unbias((ptr), offsetof(owner_type, owner_field)))
static void* ptr_unbias(const void* const ptr, const size_t offset)
{
    return (ptr == NULL) ? NULL : (void*)((char*)ptr - offset);
}

#define LIST_TAIL(list, owner_type, owner_field) LIST_MEMBER((list).tail, owner_type, owner_field)

#define LIST_EMPTY       ((cy_list_t){ .head = NULL, .tail = NULL })
#define LIST_MEMBER_NULL ((cy_list_member_t){ .next = NULL, .prev = NULL })

// =====================================================================================================================
//                                                  MESSAGE BUFFER
// =====================================================================================================================

size_t cy_message_size(const cy_message_t* const msg) { return (msg != NULL) ? msg->vtable->size(msg) : 0; }

size_t cy_message_read(const cy_message_t* const msg, const size_t offset, const size_t size, void* const destination)
{
    return ((msg != NULL) && (msg->vtable != NULL) && (destination != NULL))
             ? msg->vtable->read(msg, offset, size, destination)
             : 0;
}

void cy_message_refcount_inc(cy_message_t* const msg)
{
    if (msg != NULL) {
        assert(msg->refcount > 0);
        msg->refcount++;
    }
}

void cy_message_refcount_dec(cy_message_t* const msg)
{
    if ((msg != NULL) && (msg->vtable != NULL)) {
        assert(msg->refcount > 0);
        msg->refcount--;
        if (msg->refcount == 0) {
            msg->vtable->destroy(msg);
        }
    }
}

static void message_skip(cy_message_t* const msg, const size_t offset)
{
    assert((msg != NULL) && (msg->vtable != NULL) && (msg->vtable->skip != NULL));
    msg->vtable->skip(msg, offset);
}

// =====================================================================================================================
//                                                      FUTURE
// =====================================================================================================================

typedef struct cy_future_vtable_t
{
    cy_future_status_t (*status)(const cy_future_t*);
    void* (*result)(cy_future_t*);
    void (*cancel)(cy_future_t*); ///< Pre: status() == pending; post: status() != pending.
    void (*timeout)(cy_future_t*);
    void (*finalize)(cy_future_t*); ///< Invoked immediately before destruction; pre: status() != pending.
} cy_future_vtable_t;

/// For simplicity, the base future provides built-in timeout and key lookup capabilities. This simplifies usage.
struct cy_future_t
{
    cy_tree_t index; ///< Futures are always indexed. This is the first field for ptr equivalence.
    uint64_t  key;   ///< Futures indexed on this unique key; the meaning depends on the future type.

    olga_event_t timeout; ///< Futures can always expire on timeout.
    cy_t*        cy;

    cy_user_context_t    context;
    cy_future_callback_t callback;

    const cy_future_vtable_t* vtable;
};

static void* future_new(cy_t* const cy, const cy_future_vtable_t* const vtbl, const size_t derived_size)
{
    assert(derived_size >= sizeof(cy_future_t));
    assert(vtbl != NULL);
    assert((vtbl->status != NULL) && (vtbl->result != NULL) && (vtbl->cancel != NULL) && (vtbl->timeout != NULL) &&
           (vtbl->finalize != NULL));
    cy_future_t* const future = (cy_future_t*)mem_alloc_zero(cy, derived_size);
    if (future != NULL) {
        future->index    = TREE_NULL;
        future->timeout  = OLGA_EVENT_INIT;
        future->cy       = cy;
        future->context  = CY_USER_CONTEXT_EMPTY;
        future->callback = NULL;
        future->vtable   = vtbl;
    }
    return future;
}

// FUTURE INDEXING

static int32_t future_cavl_compare(const void* const user, const cy_tree_t* const node)
{
    const uint64_t outer = *(const uint64_t*)user;
    const uint64_t inner = ((const cy_future_t*)node)->key;
    return (outer == inner) ? 0 : ((outer > inner) ? +1 : -1); // NOLINT(*-nested-conditional-operator)
}

/// Returns false if such key already exists (index not modified).
static bool future_index_insert(cy_future_t* const self, cy_tree_t** const index, const uint64_t key)
{
    self->key = key;
    return cavl2_find_or_insert(index, &self->index, future_cavl_compare, &self->key, cavl2_trivial_factory) ==
           &self->index;
}

/// MUST be inserted, otherwise UB.
static void future_index_remove(cy_future_t* const self, cy_tree_t** const index)
{
    assert(cavl2_is_inserted(*index, &self->index));
    cavl2_remove(index, &self->index);
}

static cy_future_t* future_index_lookup(cy_tree_t** const index, const uint64_t key)
{
    return (cy_future_t*)cavl2_find(*index, &key, future_cavl_compare);
}

// FUTURE TIMEOUT

static void future_timeout_trampoline(olga_t* const sched, olga_event_t* const event, const cy_us_t now)
{
    (void)sched;
    (void)now;
    cy_future_t* const self = (cy_future_t*)event->user;
    self->vtable->timeout(self);
}

static void future_deadline_arm(cy_future_t* const self, const cy_us_t deadline)
{
    olga_defer(self->cy->olga, deadline, self, future_timeout_trampoline, &self->timeout);
}

static void future_deadline_disarm(cy_future_t* const self) { olga_cancel(self->cy->olga, &self->timeout); }

// FUTURE HELPERS

/// Remember that the user callback may destroy the future!
/// The future pointer is thus invalidated after this function; any access counts as use-after-free.
static void future_notify(cy_future_t* const self)
{
    if (self->callback != NULL) {
        self->callback(self);
    }
}

static void future_cancel_and_notify(cy_future_t* const self)
{
    if (cy_future_status(self) == cy_future_pending) {
        future_deadline_disarm(self);
        self->vtable->cancel(self);
        assert(cy_future_status(self) != cy_future_pending);
        future_notify(self);
    }
}

/// Stub for futures that do not require finalization.
// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void future_noop(cy_future_t* const self) { (void)self; }

// FUTURE API

cy_future_status_t cy_future_status(const cy_future_t* const self) { return self->vtable->status(self); }
void*              cy_future_result(cy_future_t* const self) { return self->vtable->result(self); }

cy_user_context_t cy_future_context(const cy_future_t* const self) { return self->context; }
void cy_future_context_set(cy_future_t* const self, const cy_user_context_t context) { self->context = context; }

cy_future_callback_t cy_future_callback(const cy_future_t* const self) { return self->callback; }
void                 cy_future_callback_set(cy_future_t* const self, const cy_future_callback_t callback)
{
    const bool was_set = (self->callback != NULL);
    self->callback     = callback;
    if (!was_set && (cy_future_status(self) != cy_future_pending)) {
        future_notify(self);
    }
}

void cy_future_destroy(cy_future_t* const self)
{
    if (self != NULL) {
        self->callback = NULL; // Remember that a future may be destroyed from within its own callback.
        future_cancel_and_notify(self);
        self->vtable->finalize(self);
        mem_free(self->cy, self);
    }
}

// =====================================================================================================================
//                                                      TOPICS
// =====================================================================================================================

/// For each topic we are subscribed to, there is a single subscriber root.
/// The application can create an arbitrary number of subscribers per topic, which all go under the same root.
/// If pattern subscriptions are used, a single root may match multiple topics; the matching is tracked using
/// the coupling objects.
///
/// One interesting property of this design is that the application may create multiple subscribers matching the same
/// topic, each with possibly different parameters. The library attempts to resolve this conflict by merging the
/// parameters using simple heuristics.
typedef struct subscriber_root_t
{
    wkv_node_t* index_name;
    wkv_node_t* index_pattern; ///< NULL if this is a verbatim subscriber.

    /// If this is a pattern subscriber, we will need to publish a scout message.
    /// The entry is delisted when it no longer requires publishing scout messages.
    cy_list_member_t list_scout_pending;

    cy_t*            cy;
    cy_subscriber_t* head; ///< New subscribers are inserted at the head of the list.
} subscriber_root_t;

/// A single topic may match multiple names if patterns are used.
/// Each instance holds a pointer to the corresponding subscriber root and a pointer to the next match for this topic.
typedef struct cy_topic_coupling_t
{
    subscriber_root_t*          root;
    struct cy_topic_coupling_t* next;

    size_t            substitution_count; ///< The size of the following substitutions flex array.
    cy_substitution_t substitutions[];
} cy_topic_coupling_t;

static int32_t cavl_comp_topic_hash(const void* const user, const cy_tree_t* const node)
{
    const uint64_t          outer = *(uint64_t*)user;
    const cy_topic_t* const inner = CAVL2_TO_OWNER(node, cy_topic_t, index_hash);
    if (outer == inner->hash) {
        return 0;
    }
    return (outer > inner->hash) ? +1 : -1;
}

static int32_t cavl_comp_topic_subject_id(const void* const user, const cy_tree_t* const node)
{
    const uint32_t outer = *(const uint32_t*)user;
    const uint32_t inner = cy_topic_subject_id(CAVL2_TO_OWNER(node, cy_topic_t, index_subject_id));
    if (outer == inner) {
        return 0;
    }
    return (outer > inner) ? +1 : -1;
}

static void topic_destroy(cy_topic_t* const topic)
{
    (void)topic;
    assert(topic != NULL);
    // TODO implement
}

static int_fast8_t topic_lage(const cy_topic_t* const topic, const cy_us_t now)
{
    return log2_floor((uint64_t)max_i64(0, (now - topic->ts_origin) / MEGA));
}

/// CRDT merge operator on the topic log-age. Shift ts_origin into the past if needed.
static void topic_merge_lage(cy_topic_t* const topic, const cy_us_t now, const int_fast8_t r_lage)
{
    topic->ts_origin = min_i64(topic->ts_origin, now - (pow2us(r_lage) * MEGA));
}

static bool is_pinned(const uint64_t hash) { return hash <= CY_PINNED_SUBJECT_ID_MAX; }

/// This comparator is only applicable on subject-ID allocation conflicts. As such, hashes must be different.
static bool left_wins(const cy_topic_t* const left, const cy_us_t now, const int_fast8_t r_lage, const uint64_t r_hash)
{
    assert(left->hash != r_hash);
    const int_fast8_t l_lage = topic_lage(left, now);
    return (l_lage != r_lage) ? (l_lage > r_lage) : left->hash < r_hash; // older topic wins
}

/// A first-principles check to see if the topic is implicit. Scans all couplings, slow.
static bool validate_is_implicit(const cy_topic_t* const topic)
{
    if (topic->pub_count > 0) {
        return false;
    }
    const cy_topic_coupling_t* cpl = topic->couplings;
    while (cpl != NULL) {
        if (cpl->root->index_pattern == NULL) {
            return false; // This is a verbatim subscription, so the topic is not implicit.
        }
        cpl = cpl->next;
    }
    return true;
}

static bool is_implicit(const cy_topic_t* const topic)
{
    return is_listed(&topic->cy->list_implicit, &topic->list_implicit);
}

/// Move the topic to the head of the doubly-linked list of implicit topics.
/// The oldest implicit topic will be eventually pushed to the tail of the list.
static void implicit_animate(cy_topic_t* const topic, const cy_us_t now)
{
    topic->ts_animated = now;
    if (is_implicit(topic)) {
        enlist_head(&topic->cy->list_implicit, &topic->list_implicit); // move to the head of the list
    }
}

/// Retires at most one at every call.
static void retire_expired_implicit_topics(cy_t* const cy, const cy_us_t now)
{
    cy_topic_t* const topic = LIST_TAIL(cy->list_implicit, cy_topic_t, list_implicit);
    if (topic != NULL) {
        assert(is_implicit(topic) && validate_is_implicit(topic));
        if ((topic->ts_animated + cy->implicit_topic_timeout) < now) {
            CY_TRACE(cy, "⚰️ %s", topic_repr(topic).str);
            topic_destroy(topic);
        }
    }
}

/// Nothing is done if the topic is already in the urgent list because doing so would move it
/// to the head of the list, which would defeat the purpose of prioritization.
///
/// It is conceivable that large networks may encounter transient gossip storms when multiple nodes
/// trigger collisions on a topic in a short time window, forcing the local node to send multiple
/// urgent gossips on the same topic back-to-back. If this becomes a problem, we can store the last
/// gossip time per topic to throttle the gossiping rate here.
static void schedule_gossip_urgent(cy_topic_t* const topic)
{
    if (!is_listed(&topic->cy->list_gossip_urgent, &topic->list_gossip_urgent)) {
        delist(&topic->cy->list_gossip, &topic->list_gossip);
        enlist_head(&topic->cy->list_gossip_urgent, &topic->list_gossip_urgent);
        CY_TRACE(topic->cy, "⏰ %s", topic_repr(topic).str);
    }
}

/// If the topic is already scheduled, moves it back to the head of the normal gossip list.
/// If the topic is not eligible for regular gossip, it is removed from the list.
static void schedule_gossip(cy_topic_t* const topic)
{
    delist(&topic->cy->list_gossip_urgent, &topic->list_gossip_urgent);
    const bool eligible = !is_pinned(topic->hash) && !is_implicit(topic);
    if (eligible) {
        enlist_head(&topic->cy->list_gossip, &topic->list_gossip);
    } else {
        delist(&topic->cy->list_gossip, &topic->list_gossip);
    }
}

/// Parses the hexadecimal hash override suffix if present and valid. Example: "sensors/temperature#1a2b".
static bool parse_hash_override(const wkv_str_t s, uint64_t* const out)
{
    *out                  = 0;
    const char* const end = s.str + s.len;
    for (size_t i = 0; i < smaller(s.len, 17); i++) {
        const unsigned char ch = (unsigned char)*(end - (i + 1));
        if (ch == '#') {
            return i > 0;
        }
        uint64_t digit = 0;
        if ((ch >= '0') && (ch <= '9')) {
            digit = ch - '0';
        } else if ((ch >= 'a') && (ch <= 'f')) {
            digit = ch - 'a' + 10U;
        } else {
            break;
        }
        *out |= digit << (i * 4U);
    }
    return false;
}

static uint64_t topic_hash(const wkv_str_t name)
{
    uint64_t hash = 0;
    if (!parse_hash_override(name, &hash)) {
        hash = rapidhash(name.str, name.len);
    }
    return hash;
}

static uint32_t topic_subject_id(const cy_t* const cy, const uint64_t hash, const uint64_t evictions)
{
    if (is_pinned(hash)) {
        return (uint32_t)hash;
    }
#ifndef CY_CONFIG_PREFERRED_TOPIC_OVERRIDE
    return CY_PINNED_SUBJECT_ID_MAX + (uint32_t)((hash + (evictions * evictions)) % cy->subject_id_modulus);
#else
    (void)hash;
    return (uint32_t)((CY_CONFIG_PREFERRED_TOPIC_OVERRIDE + (evictions * evictions)) % cy->subject_id_modulus);
#endif
}

/// This will only search through topics that have auto-assigned subject-IDs;
/// i.e., pinned topics will not be found by this function.
static cy_topic_t* topic_find_by_subject_id(const cy_t* const cy, const uint32_t subject_id)
{
    cy_topic_t* const topic = CAVL2_TO_OWNER(
      cavl2_find(cy->topics_by_subject_id, &subject_id, &cavl_comp_topic_subject_id), cy_topic_t, index_subject_id);
    assert((topic == NULL) || (cy_topic_subject_id(topic) == subject_id));
    return topic;
}

static size_t get_subscription_extent(const cy_topic_t* const topic);

/// If a subscription is needed but is not active, this function will attempt to resubscribe.
/// Errors are handled via the platform handler, so from the caller's perspective this is infallible.
static void topic_ensure_subscribed(cy_topic_t* const topic)
{
    const cy_t* const cy = topic->cy;
    if ((topic->couplings != NULL) && (!topic->subscribed)) {
        const size_t   extent = get_subscription_extent(topic);
        const cy_err_t res    = cy->vtable->subscribe(topic, extent);
        topic->subscribed     = res == CY_OK;
        CY_TRACE(topic->cy, "🗞️ %s extent=%zu result=%d", topic_repr(topic).str, extent, res);
        if (!topic->subscribed) {
            topic->cy->vtable->on_subscription_error(topic->cy, topic, res); // not our problem anymore
        }
    }
}

/// This function will schedule all affected topics for gossip, including the one that is being moved.
/// If this is undesirable, the caller can restore the next gossip time after the call.
///
/// The complexity is O(N log(N)) where N is the number of local topics. This is because we have to search the AVL
/// index tree on every iteration, and there may be as many iterations as there are local topics in the theoretical
/// worst case. The amortized worst case is only O(log(N)) because the topics are sparsely distributed thanks to the
/// topic hash function, unless there is a large number of topics (~>1000).
/// NOLINTNEXTLINE(*-no-recursion)
static void topic_allocate(cy_topic_t* const topic, const uint64_t new_evictions, const bool virgin, const cy_us_t now)
{
    cy_t* const cy = topic->cy;
    assert(cavl_count(cy->topics_by_hash) <= (cy->subject_id_modulus / 4));
#if CY_CONFIG_TRACE
    static const int           call_depth_indent = 2;
    static CY_THREAD_LOCAL int call_depth        = 0U;
    call_depth++;
    CY_TRACE(cy,
             "🔍%*s %s evict=%llu->%llu lage=%+d subscribed=%d couplings=%p",
             (call_depth - 1) * call_depth_indent,
             "",
             topic_repr(topic).str,
             (unsigned long long)topic->evictions,
             (unsigned long long)new_evictions,
             topic_lage(topic, now),
             (int)topic->subscribed,
             (void*)topic->couplings);
#endif

    // We need to make sure no underlying resources are sitting on this topic before we move it.
    // Otherwise, changing the subject-ID field on the go may break something underneath.
    if (topic->subscribed) {
        assert(topic->couplings != NULL);
        cy->vtable->unsubscribe(topic);
        topic->subscribed = false;
    }

    // We're not allowed to alter the eviction counter as long as the topic remains in the tree! So we remove it first.
    if (!virgin) {
        cavl2_remove(&cy->topics_by_subject_id, &topic->index_subject_id);
    }

    // This mirrors the formal specification of AllocateTopic(t, topics) given in Core.tla.
    // Note that it is possible that subject_id(hash,old_evictions) == subject_id(hash,new_evictions),
    // meaning that we stay with the same subject-ID. No special case is required to handle this.
    const uint32_t    new_sid = topic_subject_id(cy, topic->hash, new_evictions);
    cy_topic_t* const that    = CAVL2_TO_OWNER(
      cavl2_find(cy->topics_by_subject_id, &new_sid, &cavl_comp_topic_subject_id), cy_topic_t, index_subject_id);
    assert((that == NULL) || (topic->hash != that->hash)); // This would mean that we inserted the same topic twice
    const bool victory = (that == NULL) || left_wins(topic, now, topic_lage(that, now), that->hash);

#if CY_CONFIG_TRACE
    if (that != NULL) {
        CY_TRACE(cy,
                 "🎲%*s T%016llx@%08x %s T%016llx@%08x",
                 (call_depth - 1) * call_depth_indent,
                 "",
                 (unsigned long long)topic->hash,
                 new_sid,
                 victory ? "wins 👑 over" : "loses 💀 to",
                 (that != NULL) ? (unsigned long long)that->hash : UINT64_MAX,
                 (that != NULL) ? cy_topic_subject_id(that) : UINT32_MAX);
    }
#endif

    if (victory) {
        if (that != NULL) {
            cavl2_remove(&cy->topics_by_subject_id, &that->index_subject_id);
        }
        topic->evictions             = new_evictions;
        const cy_topic_t* const self = CAVL2_TO_OWNER(cavl2_find_or_insert(&cy->topics_by_subject_id,
                                                                           &new_sid,
                                                                           &cavl_comp_topic_subject_id,
                                                                           &topic->index_subject_id,
                                                                           &cavl2_trivial_factory),
                                                      cy_topic_t,
                                                      index_subject_id);
        assert(self == topic);
        (void)self;
        assert(!topic->subscribed);
        // Allocation done (end of the recursion chain), schedule gossip and resubscribe if needed.
        // If a resubscription failed in the past, we will retry here as long as there is at least one live subscriber.
        schedule_gossip_urgent(topic);
        topic_ensure_subscribed(topic);
        // Re-allocate the defeated topic with incremented eviction counter.
        if (that != NULL) {
            topic_allocate(that, that->evictions + 1U, true, now);
        }
    } else {
        topic_allocate(topic, new_evictions + 1U, true, now);
    }

#if CY_CONFIG_TRACE
    CY_TRACE(cy,
             "🔎%*s %s evict=%llu lage=%+d subscribed=%d",
             (call_depth - 1) * call_depth_indent,
             "",
             topic_repr(topic).str,
             (unsigned long long)topic->evictions,
             topic_lage(topic, now),
             (int)topic->subscribed);
    assert(call_depth > 0);
    call_depth--;
#endif
}

/// UB if the topic under this name already exists.
/// out_topic may be NULL if the reference is not immediately needed (it can be found later via indexes).
/// The log-age is -1 for newly created topics, as opposed to auto-subscription on pattern match,
/// where the lage is taken from the gossip message.
static cy_err_t topic_new(cy_t* const        cy,
                          cy_topic_t** const out_topic,
                          const wkv_str_t    resolved_name,
                          const uint64_t     hash,
                          const uint64_t     evictions,
                          const int_fast8_t  lage)
{
    // TODO error handling is broken
    if ((resolved_name.len == 0) || (resolved_name.len > CY_TOPIC_NAME_MAX)) {
        return CY_ERR_NAME;
    }
    cy_topic_t* const topic = cy->vtable->new_topic(cy);
    if (topic == NULL) {
        return CY_ERR_MEMORY;
    }
    topic->index_hash         = TREE_NULL;
    topic->index_subject_id   = TREE_NULL;
    topic->index_name         = NULL;
    topic->list_implicit      = LIST_MEMBER_NULL;
    topic->list_gossip_urgent = LIST_MEMBER_NULL;
    topic->list_gossip        = LIST_MEMBER_NULL;

    topic->cy   = cy;
    topic->name = mem_alloc(cy, resolved_name.len + 1);
    if (topic->name == NULL) {
        goto oom;
    }
    memcpy(topic->name, resolved_name.str, resolved_name.len);
    topic->name[resolved_name.len] = '\0';

    topic->evictions = evictions;
    topic->hash      = hash;

    const cy_us_t now                   = cy_now(cy);
    topic->ts_origin                    = now - (pow2us(lage) * MEGA);
    topic->ts_animated                  = now;
    topic->pub_next_tag_56bit           = cy->vtable->random(cy); // bits above 56 are ignored (can be arbitrary)
    topic->couplings                    = NULL;
    topic->subscribed                   = false;
    topic->sub_index_dedup_by_remote_id = NULL;
    topic->sub_list_dedup_by_recency    = LIST_EMPTY;
    topic->pub_count                    = 0;
    topic->user_context                 = CY_USER_CONTEXT_EMPTY;

    if (cavl_count(cy->topics_by_hash) >= (cy->subject_id_modulus / 4)) {
        goto bad_name;
    }

    // Insert the new topic into the name and hash indexes. TODO ensure uniqueness.
    topic->index_name = wkv_set(&cy->topics_by_name, resolved_name);
    if (topic->index_name == NULL) {
        goto oom;
    }
    assert(topic->index_name->value == NULL); // Cannot invoke this if such topic already exists!
    topic->index_name->value = topic;
    const cy_tree_t* const res_tree =
      cavl2_find_or_insert(&cy->topics_by_hash, &topic->hash, &cavl_comp_topic_hash, topic, &cavl2_trivial_factory);
    assert(res_tree == &topic->index_hash); // Cannot invoke this if such topic already exists!
    (void)res_tree;

    // Ensure the topic is in the gossip index. This is needed for allocation.
    // This does not apply to pinned topics, which are never gossiped.
    if (!is_pinned(topic->hash)) {
        // Allocate a subject-ID for the topic and insert it into the subject index tree.
        // Pinned topics all have canonical names, and we have already ascertained that the name is unique,
        // meaning that another pinned topic is not occupying the same subject-ID.
        // Remember that topics arbitrate locally the same way they do externally, meaning that adding a new local topic
        // may displace another local one.
        topic_allocate(topic, topic->evictions, true, now);
        if (out_topic != NULL) {
            *out_topic = topic;
        }
        // Initially, all non-pinned topics are considered implicit until proven otherwise.
        enlist_head(&cy->list_implicit, &topic->list_implicit);
    } else {
        if (out_topic != NULL) {
            *out_topic = topic;
        }
    }
    CY_TRACE(cy, "✨ %s topic_count=%zu", topic_repr(topic).str, cavl_count(cy->topics_by_hash));
    return 0;

oom: // TODO correct deinitialization
    cy->vtable->topic_destroy(topic);
    return CY_ERR_NAME;

bad_name: // TODO correct deinitialization
    cy->vtable->topic_destroy(topic);
    return CY_ERR_NAME;
}

static cy_err_t topic_ensure(cy_t* const cy, cy_topic_t** const out_topic, const wkv_str_t resolved_name)
{
    cy_topic_t* const topic = cy_topic_find_by_name(cy, resolved_name);
    if (topic != NULL) {
        if (out_topic != NULL) {
            *out_topic = topic;
        }
        return 0;
    }
    return topic_new(cy, out_topic, resolved_name, topic_hash(resolved_name), 0, LAGE_MIN);
}

/// Create a new coupling between a topic and a subscriber.
/// Allocates new memory for the coupling, which may fail.
/// Don't forget topic_ensure_subscribed() afterward if necessary.
/// The substitutions must not lose validity until the topic is destroyed.
static cy_err_t topic_couple(cy_topic_t* const         topic,
                             subscriber_root_t* const  subr,
                             const size_t              substitution_count,
                             const wkv_substitution_t* substitutions)
{
#if CY_CONFIG_TRACE
    char subr_name[CY_TOPIC_NAME_MAX + 1];
    wkv_get_key(&topic->cy->subscribers_by_name, subr->index_name, subr_name);
    CY_TRACE(topic->cy, "🔗 %s <=> '%s' substitutions=%zu", topic_repr(topic).str, subr_name, substitution_count);
#endif
    // Allocate the new coupling object with the substitutions flex array.
    // Each topic keeps its own couplings because the sets of subscription names and topic names are orthogonal.
    cy_topic_coupling_t* const cpl = (cy_topic_coupling_t*)mem_alloc_zero(
      topic->cy, sizeof(cy_topic_coupling_t) + (substitution_count * sizeof(cy_substitution_t)));
    if (cpl != NULL) {
        cpl->root               = subr;
        cpl->next               = topic->couplings;
        topic->couplings        = cpl;
        cpl->substitution_count = substitution_count;
        // When we copy the substitutions, we assume that the lifetime of the substituted string segments is at least
        // the same as the lifetime of the topic, which is true because the substitutions point into the topic name
        // string, which is part of the topic object.
        const wkv_substitution_t* s = substitutions;
        for (size_t i = 0U; s != NULL; i++) {
            assert(i < cpl->substitution_count);
            cpl->substitutions[i] = (cy_substitution_t){ .str = s->str, .ordinal = s->ordinal };
            s                     = s->next;
        }
        // If this is a verbatim subscriber, the topic is no (longer) implicit.
        if ((subr->index_pattern == NULL) && is_implicit(topic)) {
            delist(&topic->cy->list_implicit, &topic->list_implicit);
            CY_TRACE(topic->cy, "🧛 %s promoted to explicit", topic_repr(topic).str);
        }
    }
    return (cpl == NULL) ? CY_ERR_MEMORY : CY_OK;
}

/// Returns non-NULL on OOM.
static void* wkv_cb_couple_new_topic(const wkv_event_t evt)
{
    cy_topic_t* const        topic = (cy_topic_t*)evt.context;
    subscriber_root_t* const subr  = (subscriber_root_t*)evt.node->value;
    const cy_err_t           res   = topic_couple(topic, subr, evt.substitution_count, evt.substitutions);
    return (0 == res) ? NULL : "";
}

/// If there is a pattern subscriber matching the name of this topic, attempt to create a new subscription.
/// If a new subscription is created, the new topic will be returned.
static cy_topic_t* topic_subscribe_if_matching(cy_t* const       cy,
                                               const wkv_str_t   resolved_name,
                                               const uint64_t    hash,
                                               const uint64_t    evictions,
                                               const int_fast8_t lage)
{
    assert((cy != NULL) && (resolved_name.str != NULL));
    if (resolved_name.len == 0) {
        return NULL; // Ensure the remote is not trying to feed us an empty name, that's bad.
    }
    if (NULL == wkv_route(&cy->subscribers_by_pattern, resolved_name, NULL, wkv_cb_first)) {
        return NULL; // No match.
    }
    CY_TRACE(cy, "✨'%s'", resolved_name.str);
    // Create the new topic.
    cy_topic_t* topic = NULL;
    {
        const cy_err_t res = topic_new(cy, &topic, resolved_name, hash, evictions, lage);
        if (res != CY_OK) {
            cy->vtable->on_subscription_error(cy, NULL, res);
            return NULL;
        }
    }
    // Attach subscriptions using topic-owned name to keep substitutions stable.
    // Using the resolved_name here would be deadly since it is stack-allocated.
    if (NULL != wkv_route(&cy->subscribers_by_pattern, cy_topic_name(topic), topic, wkv_cb_couple_new_topic)) {
        // TODO discard the topic!
        cy->vtable->on_subscription_error(cy, NULL, CY_ERR_MEMORY);
        return NULL;
    }
    // Create the transport subscription once at the end, considering the parameters from all subscribers.
    topic_ensure_subscribed(topic);
    return topic;
}

// =====================================================================================================================
//                                                      HEARTBEAT
// =====================================================================================================================

#define HEARTBEAT_OFFSET_TOPIC_NAME 24U
#define HEARTBEAT_SIZE_MAX          (HEARTBEAT_OFFSET_TOPIC_NAME + CY_TOPIC_NAME_MAX)

static cy_err_t publish_heartbeat(const cy_t* const cy,
                                  const cy_us_t     now,
                                  const uint64_t    topic_hash,
                                  const uint64_t    topic_evictions,
                                  const int8_t      topic_lage,
                                  const wkv_str_t   topic_name)
{
    assert(topic_name.len <= CY_TOPIC_NAME_MAX);
    byte_t           buf[HEARTBEAT_SIZE_MAX];
    const cy_bytes_t message_bytes = { .size = HEARTBEAT_OFFSET_TOPIC_NAME + topic_name.len, .data = buf };
    byte_t*          ptr           = buf;
    // uptime and reserved
    ptr    = serialize_u32(ptr, (uint32_t)((now - cy->ts_started) / MEGA));
    *ptr++ = 0;
    *ptr++ = 0;
    *ptr++ = 0;
    // version
    *ptr++ = 1;
    // topic fields
    ptr    = serialize_u64(ptr, topic_hash);
    ptr    = serialize_u40(ptr, topic_evictions);
    *ptr++ = (byte_t)topic_lage; // signed to unsigned sign-bit conversion is well-defined per the C standard
    *ptr++ = 0;                  // reserved
    // topic name
    *ptr++ = (byte_t)topic_name.len;
    memcpy(ptr, topic_name.str, topic_name.len);
    // send
    return cy_publish(cy->heartbeat_pub, now + cy->heartbeat_period, message_bytes);
}

static cy_err_t publish_heartbeat_gossip(cy_t* const cy, cy_topic_t* const topic, const cy_us_t now)
{
    CY_TRACE(cy, "🗣️ %s", topic_repr(topic).str);
    topic_ensure_subscribed(topic); // use this opportunity to repair the subscription if broken
    schedule_gossip(topic);         // reschedule even if failed -- some other node might pick up the gossip
    return publish_heartbeat(cy, now, topic->hash, topic->evictions, topic_lage(topic, now), cy_topic_name(topic));
}

static cy_err_t publish_heartbeat_scout(cy_t* const cy, subscriber_root_t* const subr, const cy_us_t now)
{
    assert(subr != NULL); // https://github.com/pavel-kirienko/cy/issues/12#issuecomment-2953184238
    char name[CY_TOPIC_NAME_MAX + 1];
    wkv_get_key(&cy->subscribers_by_name, subr->index_name, name);
    const cy_err_t res =
      publish_heartbeat(cy, now, 0, 0, LAGE_SCOUT, (wkv_str_t){ .len = subr->index_name->key_len, .str = name });
    CY_TRACE(cy, "📢'%s' result=%d", name, res);
    if (res == CY_OK) {
        delist(&cy->list_scout_pending, &subr->list_scout_pending);
    }
    return res;
}

/// Will schedule the first heartbeat for publication if it hasn't been published yet. Does nothing otherwise.
/// Lazy heartbeat publication commencement is an important feature for listen-only nodes,
/// allowing them to avoid transmitting anything at all until they cease to be listen-only.
/// Heartbeat publication will commence when the local node does any of the following:
/// - Publishes on a topic. See cy_publish(), cy_request(), etc.
/// - Sends a response. See cy_respond().
/// - Wins arbitration on a collision or a divergence. See on_heartbeat().
/// - Encounters a scout request match. See on_heartbeat().
static void heartbeat_begin(cy_t* const cy)
{
    if (cy->heartbeat_next == HEAT_DEATH) {
        CY_TRACE(cy, "🚀");
        cy->heartbeat_next = cy_now(cy);
    }
}

static void* wkv_cb_topic_scout_response(const wkv_event_t evt)
{
    cy_topic_t* const topic = (cy_topic_t*)evt.node->value;
    CY_TRACE(topic->cy, "📢 %s", topic_repr(topic).str);
    heartbeat_begin(topic->cy);
    schedule_gossip_urgent(topic);
    return NULL;
}

typedef struct
{
    byte_t      version;
    uint64_t    topic_hash;
    uint64_t    topic_evictions;
    int_fast8_t topic_lage;
    wkv_str_t   topic_name;
} hb_t;

/// The name buffer shall be at least CY_TOPIC_NAME_MAX+1 bytes long.
/// On failure, the version is set to zero (which corresponds to Cyphal v1.0 heartbeat with no topic information).
static hb_t heartbeat_deserialize(const cy_message_t* const msg, byte_t* const name_buf)
{
    hb_t out = { .version = 0, .topic_name = { .len = 0, .str = (const char*)name_buf } };
    // implicit zero extension rule -- assume zero if absent from the message
    (void)cy_message_read(msg, 7, 1, &out.version);
    if (out.version == 0) {
        return (hb_t){ 0 }; // Cyphal v1.0 heartbeat carries no topic information. Simply ignore.
    }
    if (out.version == 1) {
        static const size_t prefix_size = 8 + 5 + 1 + 1 + 1; // hash, evictions, lage, reserved, name_len
        assert(prefix_size <= CY_TOPIC_NAME_MAX + 1);
        if (prefix_size != cy_message_read(msg, 8, prefix_size, name_buf)) {
            return (hb_t){ 0 }; // invalid size
        }
        out.topic_hash      = deserialize_u64(name_buf + 0);
        out.topic_evictions = deserialize_u40(name_buf + 8);
        out.topic_lage      = (int_fast8_t)name_buf[13];
        out.topic_name.len  = name_buf[15];
        if ((out.topic_name.len > CY_TOPIC_NAME_MAX) ||
            (out.topic_name.len != cy_message_read(msg, 24, out.topic_name.len, name_buf))) {
            return (hb_t){ 0 }; // invalid size
        }
        name_buf[out.topic_name.len] = 0; // this is not mandatory but convenient for logging/debugging
        return out;
    }
    return (hb_t){ 0 }; // unsupported version
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void on_heartbeat(cy_subscriber_t* const sub, const cy_arrival_t arrival)
{
    (void)sub;
    assert(arrival.substitutions.count == 0); // This is a verbatim subscriber.
    const cy_us_t ts = arrival.message.timestamp;
    cy_t* const   cy = arrival.topic->cy;
    byte_t        scratchpad[CY_TOPIC_NAME_MAX + 1];
    const hb_t    hb = heartbeat_deserialize(arrival.message.content, scratchpad);
    if (hb.version == 0) {
        CY_TRACE(cy, "⚠️ Ignoring invalid or Cyphal v1.0 heartbeat");
        return; // Cyphal v1.0 heartbeat or invalid message; nothing to do.
    }
    if (hb.topic_lage >= -1) {
        // Find the topic in our local database. Create if there is a pattern match.
        cy_topic_t* mine = cy_topic_find_by_hash(cy, hb.topic_hash);
        if ((mine == NULL) && (hb.topic_name.len > 0)) { // a name is required but maybe the publisher is non-compliant
            mine = topic_subscribe_if_matching(cy, hb.topic_name, hb.topic_hash, hb.topic_evictions, hb.topic_lage);
        }
        if (mine != NULL) {        // We have this topic! Check if we have consensus on the subject-ID.
            schedule_gossip(mine); // suppress next gossip -- the network just heard about it
            implicit_animate(mine, ts);
            assert(mine->hash == hb.topic_hash);
            const int_fast8_t mine_lage = topic_lage(mine, ts);
            if (mine->evictions != hb.topic_evictions) {
                const bool win = (mine_lage > hb.topic_lage) ||
                                 ((mine_lage == hb.topic_lage) && (mine->evictions > hb.topic_evictions));
                CY_TRACE(cy,
                         "🔀 Divergence on '%s':\n"
                         "\t local  %s T%016llx@%08x evict=%llu lage=%+d\n"
                         "\t remote %s T%016llx@%08x evict=%llu lage=%+d",
                         mine->name,
                         win ? "✅" : "❌",
                         (unsigned long long)mine->hash,
                         cy_topic_subject_id(mine),
                         (unsigned long long)mine->evictions,
                         mine_lage,
                         win ? "❌" : "✅",
                         (unsigned long long)mine->hash,
                         topic_subject_id(cy, hb.topic_hash, hb.topic_evictions),
                         (unsigned long long)hb.topic_evictions,
                         hb.topic_lage);
                if (win) {
                    // Critically, if we win, we ignore possible allocation collisions. Even if the remote sits on
                    // a subject-ID that is currently used by another topic that we have, which could even lose
                    // arbitration, we ignore it because the remote will have to move to catch up with us anyway,
                    // thus resolving the collision.
                    // See https://github.com/OpenCyphal-Garage/cy/issues/28 and AcceptGossip() in Core.tla.
                    assert(!is_pinned(mine->hash));
                    heartbeat_begin(cy);
                    schedule_gossip_urgent(mine);
                } else {
                    assert((mine_lage <= hb.topic_lage) &&
                           ((mine_lage < hb.topic_lage) || (mine->evictions < hb.topic_evictions)));
                    assert(mine_lage <= hb.topic_lage);
                    topic_merge_lage(mine, ts, hb.topic_lage);
                    topic_allocate(mine, hb.topic_evictions, false, ts);
                    if (mine->evictions == hb.topic_evictions) { // perfect sync, lower the gossip priority
                        schedule_gossip(mine);
                    }
                }
            } else {
                topic_ensure_subscribed(mine); // use this opportunity to repair the subscription if broken
            }
            topic_merge_lage(mine, ts, hb.topic_lage);
        } else { // We don't know this topic; check for a subject-ID collision and do auto-subscription.
            mine = topic_find_by_subject_id(cy, topic_subject_id(cy, hb.topic_hash, hb.topic_evictions));
            if (mine == NULL) {
                return; // We are not using this subject-ID, no collision.
            }
            assert(cy_topic_subject_id(mine) == topic_subject_id(cy, hb.topic_hash, hb.topic_evictions));
            const bool win = left_wins(mine, ts, hb.topic_lage, hb.topic_hash);
            CY_TRACE(cy,
                     "💥 Collision on @%08x:\n"
                     "\t local  %s T%016llx@%08x evict=%llu lage=%+d '%s'\n"
                     "\t remote %s T%016llx@%08x evict=%llu lage=%+d '%s'",
                     cy_topic_subject_id(mine),
                     win ? "✅" : "❌",
                     (unsigned long long)mine->hash,
                     cy_topic_subject_id(mine),
                     (unsigned long long)mine->evictions,
                     topic_lage(mine, ts),
                     mine->name,
                     win ? "❌" : "✅",
                     (unsigned long long)hb.topic_hash,
                     topic_subject_id(cy, hb.topic_hash, hb.topic_evictions),
                     (unsigned long long)hb.topic_evictions,
                     hb.topic_lage,
                     hb.topic_name.str);
            // We don't need to do anything if we won, but we need to announce to the network (in particular to the
            // infringing node) that we are using this subject-ID, so that the loser knows that it has to move.
            // If we lost, we need to gossip this topic ASAP as well because every other participant on this topic
            // will also move, but the trick is that the others could have settled on different subject-IDs.
            // Everyone needs to publish their own new allocation and then we will pick max eviction counter of all.
            if (win) {
                assert(!is_pinned(mine->hash));
                heartbeat_begin(cy);
                schedule_gossip_urgent(mine);
            } else {
                topic_allocate(mine, mine->evictions + 1U, false, ts);
            }
        }
    } else if (hb.topic_lage == LAGE_SCOUT) {
        // A scout message is simply asking us to check if we have any matching topics, and gossip them ASAP if so.
        CY_TRACE(cy,
                 "📢 Scout: T%016llx evict=%llu lage=%+d '%s'",
                 (unsigned long long)hb.topic_hash,
                 (unsigned long long)hb.topic_evictions,
                 hb.topic_lage,
                 hb.topic_name.str);
        (void)wkv_match(&cy->topics_by_name, hb.topic_name, cy, wkv_cb_topic_scout_response);
    } else {
        CY_TRACE(cy, "⚠️ Invalid message: version=%d lage=%+d", (int)hb.version, hb.topic_lage);
    }
}

// =====================================================================================================================
//                                                      PUBLISHER
// =====================================================================================================================

struct cy_publisher_t
{
    cy_topic_t* topic; ///< Many-to-one relationship, never NULL; the topic is reference counted.
    cy_prio_t   priority;
    cy_list_t   publish_futures; ///< For cancellation when the publisher is destroyed.
    cy_us_t     ack_baseline_timeout;
};

cy_publisher_t* cy_advertise(cy_t* const cy, const wkv_str_t name) { return cy_advertise_client(cy, name, 0); }

cy_publisher_t* cy_advertise_client(cy_t* const cy, const wkv_str_t name, const size_t response_extent)
{
    if (cy == NULL) {
        return NULL;
    }
    char            name_buf[CY_TOPIC_NAME_MAX];
    const wkv_str_t resolved = cy_name_resolve(name, cy->ns, cy->home, sizeof(name_buf), name_buf);
    if (resolved.len > CY_TOPIC_NAME_MAX) {
        return NULL;
    }
    if (!cy_name_is_verbatim(resolved)) {
        return NULL; // Wildcard publishers are not defined.
    }
    cy_publisher_t* const pub = mem_alloc_zero(cy, sizeof(*pub));
    if (pub == NULL) {
        return NULL;
    }
    const cy_err_t res        = topic_ensure(cy, &pub->topic, resolved);
    pub->priority             = cy_prio_nominal;
    pub->publish_futures      = LIST_EMPTY;
    pub->ack_baseline_timeout = cy->ack_baseline_timeout;
    if (res == CY_OK) {
        assert(pub->topic != NULL);
        pub->topic->pub_count++;
        delist(&cy->list_implicit, &pub->topic->list_implicit);
    }
    const size_t response_extent_with_header = response_extent + HEADER_MAX_BYTES;
    if (response_extent_with_header > cy->p2p_extent) {
        // Currently, we only increase the extent and leave it at the max. Ideally we should also shrink it when
        // publishers are destroyed. One way to do it without scanning all publishers is to round up the extent
        // of each to a power of 2 and keep a count of how many publishers are at each power-of-2 level (capped 2**32):
        // size_t publisher_counts_by_extent_pow2[32];
        cy->p2p_extent = response_extent_with_header;
        cy->vtable->p2p_extent(cy, cy->p2p_extent);
    }
    CY_TRACE(cy,
             "✨ %s topic_count=%zu pub_count=%zu p2p_extent=%zu res=%d",
             (res == CY_OK) ? topic_repr(pub->topic).str : "(failed)",
             cavl_count(cy->topics_by_hash),
             pub->topic->pub_count,
             cy->p2p_extent,
             res);
    return (res == CY_OK) ? pub : NULL;
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
cy_err_t cy_publish(cy_publisher_t* const pub, const cy_us_t deadline, const cy_bytes_t message)
{
    if ((pub == NULL) || (deadline < 0)) {
        return CY_ERR_ARGUMENT;
    }
    assert(pub->topic->pub_count > 0);
    heartbeat_begin(pub->topic->cy);

    // Compose the session layer header.
    // TODO: How do we handle CAN compatibility? No header for pinned topics? The transport will strip the header?
    byte_t header[16];
    (void)serialize_u64(serialize_u64(header, (pub->topic->pub_next_tag_56bit++ << 8U) | (uint64_t)header_msg_be),
                        pub->topic->hash);
    const cy_bytes_t headed_message = { .size = sizeof(header), .data = header, .next = &message };

    return pub->topic->cy->vtable->publish(pub->topic, deadline, pub->priority, headed_message);
}

cy_prio_t cy_priority(const cy_publisher_t* const pub) { return (pub != NULL) ? pub->priority : cy_prio_nominal; }
void      cy_priority_set(cy_publisher_t* const pub, const cy_prio_t priority)
{
    if ((pub != NULL) && (((int)priority) >= 0) && (((int)priority) < CY_PRIO_COUNT)) {
        pub->priority = priority;
    }
}

cy_us_t cy_ack_timeout(const cy_publisher_t* const pub)
{
    cy_us_t out = BIG_BANG;
    if (pub != NULL) {
        out = pub->ack_baseline_timeout * (cy_us_t)(1ULL << (byte_t)pub->priority);
    }
    return out;
}

void cy_ack_timeout_set(cy_publisher_t* const pub, const cy_us_t timeout)
{
    if ((pub != NULL) && (timeout > 0)) {
        pub->ack_baseline_timeout = timeout / (cy_us_t)(1ULL << (byte_t)pub->priority);
    }
}

cy_topic_t* cy_publisher_topic(const cy_publisher_t* const pub) { return (pub != NULL) ? pub->topic : NULL; }

void cy_unadvertise(cy_publisher_t* const pub)
{
    if (pub == NULL) {
        return;
    }

    // Finalize pending publish futures.
    // TODO: IMPLEMENT

    // Dereference the topic.
    cy_topic_t* const topic = pub->topic;
    assert(!is_implicit(topic));
    assert(topic->pub_count > 0);
    topic->pub_count--;
    if (topic->pub_count == 0) {
        if (cy_topic_has_subscribers(topic)) { // Demote to implicit; will be eventually garbage collected.
            enlist_head(&topic->cy->list_implicit, &topic->list_implicit);
            assert(is_implicit(topic));
        }
    }
}

// =====================================================================================================================
//                                                      SUBSCRIBER
// =====================================================================================================================

typedef struct
{
    size_t extent;

    /// The reordering mode ensures that the application sees a monotonically increasing sequence of message tags
    /// per remote publisher.
    /// If less than zero, no frame reordering will be used -- they will be ejected in the order of arrival.
    /// Otherwise, out-of-order arrivals will be interned for up to this time waiting for the missing frames
    /// to show up to fill the gaps. If the gaps are not filled within this time window, the interned frames
    /// will be ejected in the order of arrival, and the missing frames even if arrive later will be dropped.
    cy_us_t reordering_window;

    /// The maximum number of messages that can be interned for reordering per remote publisher.
    /// This is a hard limit to prevent unbounded memory consumption in case of extreme high-rate out-of-order arrivals.
    /// If the limit is reached, the reordering window will close early and messages will be ejected even while
    /// waiting for missing frames, as if the time window had elapsed.
    /// By definition, the limit can only be exceeded if more than reordering_capacity messages arrive within the
    /// reordering_window time.
    size_t reordering_capacity;
} subscriber_params_t;

struct cy_subscriber_t
{
    subscriber_root_t* root; ///< Many-to-one relationship, never NULL.
    cy_subscriber_t*   next; ///< Lists all subscribers under the same root.

    subscriber_params_t params;

    cy_tree_t* index_reordering_by_remote_id;
    cy_list_t  list_reordering_by_recency;

    cy_user_context_t        user_context;
    cy_subscriber_callback_t callback;
};

static cy_breadcrumb_t make_breadcrumb(const cy_topic_t* const topic,
                                       const uint64_t          remote_id,
                                       const cy_p2p_context_t  p2p_context,
                                       const uint64_t          message_tag)
{
    assert(message_tag <= TAG56_MASK);
    return (cy_breadcrumb_t){ .cy          = topic->cy,
                              .remote_id   = remote_id,
                              .topic_hash  = topic->hash,
                              .message_tag = message_tag,
                              .seqno       = 0, // Starts a new sequence.
                              .p2p_context = p2p_context };
}

static cy_arrival_t make_arrival(cy_topic_t* const           topic,
                                 const uint64_t              remote_id,
                                 const cy_p2p_context_t      p2p_context,
                                 const uint64_t              message_tag,
                                 const cy_message_ts_t       message,
                                 const cy_substitution_set_t substitutions)
{
    return (cy_arrival_t){ .message       = message,
                           .breadcrumb    = make_breadcrumb(topic, remote_id, p2p_context, message_tag),
                           .topic         = topic,
                           .substitutions = substitutions };
}

static void subscriber_invoke(cy_subscriber_t* const subscriber, const cy_arrival_t arrival)
{
    assert(subscriber->callback != NULL);
    subscriber->callback(subscriber, arrival);
}

// --------------------------------------------------------------------------------------------------------------------
// RELIABLE MESSAGE DEDUPLICATION TO MITIGATE ACK LOSS

#define DEDUP_HISTORY 64U

/// An instance is kept per remote node that publishes messages on a given topic, or P2P.
/// It is used for deduplication of reliable messages received from that remote; duplications occur when the remote
/// doesn't receive (enough) acks and is trying to retransmit while we already have the message from prior attempts.
/// Stale instances are removed on timeout.
typedef struct
{
    cy_tree_t        index_remote_id; ///< For lookup when new reliable messages received.
    cy_list_member_t list_recency;    ///< For removal of old entries when a remote ceases publishing.

    uint64_t remote_id;
    cy_us_t  last_active_at;

    // bitmap[0]=tag-1, bitmap[1]=tag-2, bitmap[2]=tag-3, ..., bitmap[63]=tag-64; tag itself is implicitly true.
    uint64_t tag;
    uint64_t bitmap;
} dedup_t;
static_assert((sizeof(void*) > 4) || (sizeof(dedup_t) <= (64 - 8)), "should fit in a small o1heap block");

typedef struct
{
    cy_topic_t* owner;
    uint64_t    remote_id;
    uint64_t    tag;
    cy_us_t     now;
} dedup_factory_context_t;

/// Returns true if duplicate.
static bool dedup_update(dedup_t* const self, cy_topic_t* const owner, const uint64_t tag, const cy_us_t now)
{
    // Update the recency information.
    self->last_active_at = now;
    enlist_head(&owner->sub_list_dedup_by_recency, &self->list_recency);

    // Consult with the bitmap for duplication and update its state.
    const uint64_t fwd = tag56_forward_distance(self->tag, tag);
    const uint64_t rev = tag56_forward_distance(tag, self->tag);
    if (rev == 0) {
        assert(fwd == rev);
        return true;
    }
    if (rev <= DEDUP_HISTORY) { // Either duplicate or out-of-order; bit already in the bitmap.
        if ((self->bitmap & (1ULL << (rev - 1))) != 0) {
            return true;
        }
        self->bitmap |= (1ULL << (rev - 1));
    } else {
        if (fwd < DEDUP_HISTORY) {
            self->bitmap = (self->bitmap << fwd) | (1ULL << (fwd - 1U)); // Mark the previous current-tag as well.
        } else if (fwd == DEDUP_HISTORY) {
            self->bitmap = 1ULL << (DEDUP_HISTORY - 1U); // Mark the previous current; special case to avoid shift by 64
        } else {
            self->bitmap = 0; // A large tag jump in either direction is treated as a session restart.
        }
        self->tag = tag;
    }
    return false;
}

static void dedup_destroy(dedup_t* const self, cy_topic_t* const owner)
{
    delist(&owner->sub_list_dedup_by_recency, &self->list_recency);
    assert(cavl2_is_inserted(owner->sub_index_dedup_by_remote_id, &self->index_remote_id));
    cavl2_remove(&owner->sub_index_dedup_by_remote_id, &self->index_remote_id);
    mem_free(owner->cy, self);
}

static void dedup_drop_stale(cy_topic_t* const owner, const cy_us_t now)
{
    while (true) {
        dedup_t* const dd = LIST_TAIL(owner->sub_list_dedup_by_recency, dedup_t, list_recency);
        if ((dd == NULL) || ((dd->last_active_at + SESSION_LIFETIME) >= now)) {
            break;
        }
        CY_TRACE(owner->cy, "🧹 N%016llx tag=%016llx", (unsigned long long)dd->remote_id, (unsigned long long)dd->tag);
        dedup_destroy(dd, owner);
    }
}

static int32_t dedup_cavl_compare(const void* const user, const cy_tree_t* const node)
{
    const uint64_t outer = *(const uint64_t*)user;
    const uint64_t inner = ((const dedup_t*)node)->remote_id;
    return (outer == inner) ? 0 : ((outer > inner) ? +1 : -1); // NOLINT(*-nested-conditional-operator)
}

static cy_tree_t* dedup_factory(void* const user)
{
    const dedup_factory_context_t* const ctx = (dedup_factory_context_t*)user;
    dedup_drop_stale(ctx->owner, ctx->now); // A quick check that might free up some memory for the new entry.
    dedup_t* const state = mem_alloc_zero(ctx->owner->cy, sizeof(dedup_t));
    if (state != NULL) {
        state->remote_id = ctx->remote_id;
        // The tag itself is implicitly considered received, so we start with a distant tag value to avoid false-dup.
        state->tag    = (ctx->tag + DEDUP_HISTORY + 1U) & TAG56_MASK;
        state->bitmap = 0;
    }
    CY_TRACE(ctx->owner->cy,
             "🧹 N%016llx tag=%016llx: %s",
             (unsigned long long)ctx->remote_id,
             (unsigned long long)ctx->tag,
             (state != NULL) ? "ok" : "OUT OF MEMORY");
    return (state != NULL) ? &state->index_remote_id : NULL;
}

// --------------------------------------------------------------------------------------------------------------------
// MESSAGE ORDERING RECOVERY TO MITIGATE TRANSPORT REORDERING AND RELIABLE RETRANSMISSIONS

/// An arbitrarily chosen default.
#define REORDERING_CAPACITY_DEFAULT 16U

/// Smaller values are clamped to this. See the implementation to see why.
#define REORDERING_CAPACITY_MIN 4U

static void reordering_on_window_expiration(olga_t* const sched, olga_event_t* const event, const cy_us_t now);

typedef struct
{
    cy_tree_t       index_lin_tag;
    uint64_t        lin_tag; ///< UINT64_MAX if empty.
    cy_message_ts_t message;
} reordering_slot_t;
static_assert((sizeof(void*) > 4) || (sizeof(reordering_slot_t) <= (64 - 8)), "should fit in a small o1heap block");

static int32_t reordering_slot_cavl_compare(const void* const user, const cy_tree_t* const node)
{
    const uint64_t outer = *(const uint64_t*)user;
    const uint64_t inner = ((const reordering_slot_t*)node)->lin_tag;
    return (outer == inner) ? 0 : ((outer > inner) ? +1 : -1); // NOLINT(*-nested-conditional-operator)
}

/// Subscribers operating in the ordered mode use this instance, one per (remote node & topic) per subscription,
/// to enforce strictly-increasing order of message tags (modulo 2**56) from each remote node.
///
/// Missing messages are waited for for up to the reordering_window, after which they are considered lost and the gap
/// is closed by advancing the expected tag; if missing messages show up later, they are considered late and dropped.
/// Each subscription must have its own instance because they may use different settings (e.g., reordering window).
///
/// A slot may be ejected on timeout asynchronously with message arrival, which is why the reordering state has to
/// store the full state associated with the message. A pattern subscription may receive messages from multiple topics
/// matching the pattern; we need separate reordering state per topic per publisher, keeping in mind that the same
/// remote may publish on multiple topics matching our subscriber.
typedef struct
{
    cy_tree_t        index;        ///< For lookup when new messages received by (remote-ID, topic hash).
    cy_list_member_t list_recency; ///< For removal of old entries when a remote ceases publishing.
    olga_event_t     timeout;      ///< Expires on reordering window closure.

    uint64_t remote_id;
    cy_us_t  last_active_at;

    /// Metadata needed for asynchronous ejection.
    /// The topic will be kept alive by our subscription, so there is no lifetime issue. Same for the substitutions.
    cy_subscriber_t*      subscriber;
    cy_topic_t*           topic;
    cy_substitution_set_t substitutions; ///< Matching the subscription pattern to topic name.
    cy_p2p_context_t      p2p_context;   ///< Updated with the latest received message.

    uint64_t   tag_baseline;         ///< First seen tag in this state; subtract from incoming tags for linearization.
    uint64_t   last_ejected_lin_tag; ///< Linearized tag seen by the application; lesser tags are not allowed.
    size_t     interned_count;       ///< Number of currently allocated slots. Usually zero or one.
    cy_tree_t* interned_by_lin_tag;  ///< reordering_slot_t indexed by linearized tag.
} reordering_t;

typedef struct
{
    cy_us_t               now;
    uint64_t              remote_id;
    cy_subscriber_t*      subscriber;
    cy_topic_t*           topic;
    cy_substitution_set_t substitutions;
    uint64_t              tag;
} reordering_context_t;

/// Remove the slot and invoke the user callback.
static void reordering_eject(reordering_t* const self, reordering_slot_t* const slot)
{
    assert(self->topic->cy == self->subscriber->root->cy);
    cy_t* const cy = self->topic->cy;

    // Remove the slot from the index.
    assert(cavl2_is_inserted(self->interned_by_lin_tag, &slot->index_lin_tag));
    cavl2_remove(&self->interned_by_lin_tag, &slot->index_lin_tag);
    assert(self->interned_count > 0);
    self->interned_count--;
    assert((self->interned_by_lin_tag == NULL) == (self->interned_count == 0));

    // Update the state with the removed slot.
    assert(slot->lin_tag < (1ULL << 48U)); // ensure linearized by comparing against some unreachable value
    assert(self->tag_baseline <= TAG56_MASK);
    assert(self->subscriber->params.reordering_window >= 0); // we should only end up here if ordered mode is used
    assert(slot->lin_tag > self->last_ejected_lin_tag);      // ensure ordered sequence seen by the application
    self->last_ejected_lin_tag = slot->lin_tag;

    // Construct the arrival instance. It copies the relevant states from the slot so that it can be destroyed.
    assert(slot->message.timestamp >= 0);
    assert(slot->message.content != NULL);
    const cy_arrival_t arrival = make_arrival(self->topic,
                                              self->remote_id,
                                              self->p2p_context,
                                              tag56_add(slot->lin_tag, self->tag_baseline),
                                              slot->message,
                                              self->substitutions);
    mem_free(cy, slot); // Free the slot before the callback to give the application more memory to work with.

    // Invoke the callback with the arrival and dispose the message.
    subscriber_invoke(self->subscriber, arrival);
    cy_message_refcount_dec(arrival.message.content);
}

static void reordering_scan(reordering_t* const self, bool force_first)
{
    while (true) {
        reordering_slot_t* const slot =
          CAVL2_TO_OWNER(cavl2_min(self->interned_by_lin_tag), reordering_slot_t, index_lin_tag);
        if (slot == NULL) {
            olga_cancel(self->topic->cy->olga, &self->timeout);
            break;
        }
        if (force_first || ((self->last_ejected_lin_tag + 1U) == slot->lin_tag)) {
            force_first = false;
            reordering_eject(self, slot);
        } else { // We have pending slots but there is a gap, need to wait for missing messages to arrive first.
            const cy_us_t deadline = slot->message.timestamp + self->subscriber->params.reordering_window;
            olga_defer(self->topic->cy->olga, deadline, self, reordering_on_window_expiration, &self->timeout);
            break;
        }
    }
}

static void reordering_on_window_expiration(olga_t* const sched, olga_event_t* const event, const cy_us_t now)
{
    (void)sched;
    (void)now;
    reordering_scan(event->user, true);
}

/// Ejects all messages in the correct order and leaves the state empty & idle.
static void reordering_eject_all(reordering_t* const self)
{
    while (self->interned_count > 0) {
        reordering_slot_t* const slot =
          CAVL2_TO_OWNER(cavl2_min(self->interned_by_lin_tag), reordering_slot_t, index_lin_tag);
        assert(slot != NULL);
        reordering_eject(self, slot);
    }
    assert(self->interned_count == 0);
    assert(self->interned_by_lin_tag == NULL);
    olga_cancel(self->topic->cy->olga, &self->timeout);
}

static void reordering_resequence(reordering_t* const self, const uint64_t tag)
{
    // We do NOT accept the message immediately because we don't know if it's in order or not, as we don't have state.
    // For example, if we receive tag 3, we don't know if it's in a sequence of (3 2 1) or (3 4 5); to properly
    // handle the former case without message loss we start with the reordering delay.
    assert(self->interned_count == 0);
    assert(self->interned_by_lin_tag == NULL);
    assert(self->subscriber->params.reordering_capacity >= REORDERING_CAPACITY_MIN);
    self->tag_baseline         = tag56_forward_distance(self->subscriber->params.reordering_capacity / 2U, tag);
    self->last_ejected_lin_tag = 0;
}

/// When a new message is received, let the reordering managed decide if it can be ejected or it needs to be interned.
/// Returns true if the message is accepted (either ejected or interned) and should be acknowledged (because the
/// application will eventually see it); false if this is a late drop and should not be acknowledged.
/// This is only intended for use when the reordering window is non-negative, otherwise no reordering managed is needed.
static bool reordering_push(reordering_t* const self, const uint64_t tag, const cy_message_ts_t message)
{
    assert(self->subscriber->params.reordering_window >= 0);
    assert(self->subscriber->params.reordering_capacity >= REORDERING_CAPACITY_MIN); // caller must ensure
    assert(self->topic->cy == self->subscriber->root->cy);
    assert(tag <= TAG56_MASK);
    cy_t* const cy = self->topic->cy;

    // Update the recency information to keep the state alive.
    self->last_active_at = message.timestamp;
    enlist_head(&self->subscriber->list_reordering_by_recency, &self->list_recency);

    // Dispatch the message according to its tag ordering.
    uint64_t lin_tag = tag56_forward_distance(self->tag_baseline, tag);

    // The next expected message can be ejected immediately. No need to allocate state, happy fast path, most common.
    if (lin_tag == tag56_add(self->last_ejected_lin_tag, 1)) {
        self->last_ejected_lin_tag = lin_tag;
        subscriber_invoke(
          self->subscriber,
          make_arrival(self->topic, self->remote_id, self->p2p_context, tag, message, self->substitutions));
        reordering_scan(self, false); // The just-ejected message may have closed an earlier gap.
        return true;
    }

    // Late arrival or duplicate, the gap is already closed and the application has moved on, cannot accept.
    // Note that this check does not detect possible duplicates that are currently interned; this is checked below.
    if (lin_tag <= self->last_ejected_lin_tag) {
        CY_TRACE(cy,
                 "🔢 LATE/DUP: N%016llx tag=%016llx lin_tag=%016llx last_ejected_lin_tag=%016llx",
                 (unsigned long long)self->remote_id,
                 (unsigned long long)tag,
                 (unsigned long long)lin_tag,
                 (unsigned long long)self->last_ejected_lin_tag);
        return false;
    }

    // Too far ahead meaning that the remote has restarted. Eject all interned messages, if any, and reset the state.
    if (lin_tag > (self->last_ejected_lin_tag + self->subscriber->params.reordering_capacity)) {
        CY_TRACE(cy,
                 "🔢 RESEQUENCING: N%016llx tag=%016llx lin_tag=%016llx last_ejected_lin_tag=%016llx",
                 (unsigned long long)self->remote_id,
                 (unsigned long long)tag,
                 (unsigned long long)lin_tag,
                 (unsigned long long)self->last_ejected_lin_tag);
        reordering_eject_all(self);
        reordering_resequence(self, tag);
        lin_tag = tag56_forward_distance(self->tag_baseline, tag);
    }

    // The most difficult case -- the message is ahead of the next expected but within the reordering window,
    // we need to intern it and hope for the missing messages to arrive before the reordering window expiration.
    // It may still be a duplicate if somehow it made it past the topic-wise duplicate filter, so we check for that too.
    // For the assertion to hold, we must ensure that the reordering capacity is at least 4, otherwise the resequencing
    // logic would set the baseline too low for the assertion to hold.
    assert(lin_tag > (self->last_ejected_lin_tag + 1U));
    assert(lin_tag <= (self->last_ejected_lin_tag + self->subscriber->params.reordering_capacity));
    reordering_slot_t* const slot = mem_alloc_zero(cy, sizeof(reordering_slot_t));
    if (slot == NULL) {
        CY_TRACE(cy,
                 "🔢 OUT OF MEMORY: N%016llx tag=%016llx lin_tag=%016llx last_ejected_lin_tag=%016llx",
                 (unsigned long long)self->remote_id,
                 (unsigned long long)tag,
                 (unsigned long long)lin_tag,
                 (unsigned long long)self->last_ejected_lin_tag);
        return false;
    }
    const cy_tree_t* const slot_tree = cavl2_find_or_insert(
      &self->interned_by_lin_tag, &lin_tag, reordering_slot_cavl_compare, &slot->index_lin_tag, cavl2_trivial_factory);
    if (slot_tree != &slot->index_lin_tag) {
        // There is already an interned message with the same tag, drop the duplicate.
        CY_TRACE(cy,
                 "🔢 DUP: N%016llx tag=%016llx lin_tag=%016llx last_ejected_lin_tag=%016llx",
                 (unsigned long long)self->remote_id,
                 (unsigned long long)tag,
                 (unsigned long long)lin_tag,
                 (unsigned long long)self->last_ejected_lin_tag);
        mem_free(cy, slot);
        return true; // Duplicate accepted for reliability semantics; idempotent drop for the application.
    }
    cy_message_refcount_inc(message.content); // stayin' alive
    slot->lin_tag = lin_tag;
    slot->message = message;
    self->interned_count++;
    assert((self->interned_count == 1) || olga_is_pending(cy->olga, &self->timeout));
    if (!olga_is_pending(cy->olga, &self->timeout)) {
        const cy_us_t deadline = message.timestamp + self->subscriber->params.reordering_window;
        olga_defer(cy->olga, deadline, self, reordering_on_window_expiration, &self->timeout);
    }
    return true; // Interned messages WILL eventually be ejected and seen by the application.
}

static void reordering_destroy(reordering_t* const self)
{
    reordering_eject_all(self);
    delist(&self->subscriber->list_reordering_by_recency, &self->list_recency);
    assert(cavl2_is_inserted(self->subscriber->index_reordering_by_remote_id, &self->index));
    cavl2_remove(&self->subscriber->index_reordering_by_remote_id, &self->index);
    mem_free(self->subscriber->root->cy, self);
}

static void reordering_drop_stale(cy_subscriber_t* const owner, const cy_us_t now)
{
    while (true) {
        reordering_t* const rr = LIST_TAIL(owner->list_reordering_by_recency, reordering_t, list_recency);
        if ((rr == NULL) || ((rr->last_active_at + SESSION_LIFETIME) >= now)) {
            break;
        }
        CY_TRACE(owner->root->cy,
                 "🧹 N%016llx topic=%016llx",
                 (unsigned long long)rr->remote_id,
                 (unsigned long long)rr->topic->hash);
        reordering_destroy(rr);
    }
}

static int32_t reordering_cavl_compare(const void* const user, const cy_tree_t* const node)
{
    const reordering_context_t* const outer = (const reordering_context_t*)user;
    const reordering_t*               inner = (const reordering_t*)node;
    if (outer->remote_id == inner->remote_id) {
        // NOLINTNEXTLINE(*-nested-conditional-operator)
        return (outer->topic->hash == inner->topic->hash) ? 0 : ((outer->topic->hash > inner->topic->hash) ? +1 : -1);
    }
    return (outer->remote_id > inner->remote_id) ? +1 : -1;
}

static cy_tree_t* reordering_cavl_factory(void* const user)
{
    const reordering_context_t* const outer = (const reordering_context_t*)user;
    reordering_drop_stale(outer->subscriber, outer->now); // Might free up some memory for the new entry.
    reordering_t* const self = mem_alloc_zero(outer->subscriber->root->cy, sizeof(reordering_t));
    if (self != NULL) {
        self->timeout             = OLGA_EVENT_INIT;
        self->remote_id           = outer->remote_id;
        self->subscriber          = outer->subscriber;
        self->topic               = outer->topic;
        self->substitutions       = outer->substitutions;
        self->interned_count      = 0;
        self->interned_by_lin_tag = NULL;
        reordering_resequence(self, outer->tag);
    }
    CY_TRACE(outer->topic->cy,
             "🔢 REORDERING: N%016llx tag=%016llx: %s",
             (unsigned long long)outer->remote_id,
             (unsigned long long)outer->tag,
             (self != NULL) ? "ok" : "OUT OF MEMORY");
    return (self != NULL) ? &self->index : NULL;
}

// --------------------------------------------------------------------------------------------------------------------
// SUBSCRIPTION DATA PATH

// Returns true if the message was accepted, false if it should not be acknowledged (e.g. late drop for ordered subs).
static bool on_message(cy_t* const            cy,
                       const cy_p2p_context_t p2p_context,
                       const uint64_t         remote_id,
                       cy_topic_t* const      topic,
                       const uint64_t         tag,
                       const cy_message_ts_t  message,
                       const bool             reliable)
{
    implicit_animate(topic, message.timestamp);

    // Reliable transfers may be duplicated in case of ACK loss.
    // Non-reliable transfers are deduplicated by the transport, which makes them much more efficient.
    if (reliable) {
        dedup_factory_context_t ctx = { .owner = topic, .remote_id = remote_id, .tag = tag, .now = message.timestamp };
        dedup_t* const dedup = CAVL2_TO_OWNER(cavl2_find_or_insert(&topic->sub_index_dedup_by_remote_id, // ------
                                                                   &remote_id,
                                                                   dedup_cavl_compare,
                                                                   &ctx,
                                                                   dedup_factory),
                                              dedup_t,
                                              index_remote_id);
        if (dedup == NULL) { // Out of memory.
            return false;    // The remote will retransmit and we might be able to accept it then.
        }
        assert(dedup->remote_id == remote_id);
        if (dedup_update(dedup, topic, tag, message.timestamp)) {
            CY_TRACE(cy, "🍒 Dup N%016llx tag=%016llx", (unsigned long long)remote_id, (unsigned long long)tag);
            return true; // Already received, ack but don't process.
        }
    }

    // Go over the matching subscribers and invoke the handlers.
    // Remember that one topic may match many subscribers, and a single pattern subscriber may match many topics.
    bool                       acknowledge = false;
    const cy_topic_coupling_t* cpl         = topic->couplings;
    while (cpl != NULL) {
        const cy_topic_coupling_t* const next_cpl = cpl->next;
        cy_subscriber_t*                 sub      = cpl->root->head;
        assert(sub != NULL); // Otherwise it should have been removed from the coupling list.
        while (sub != NULL) {
            cy_subscriber_t* const      next_sub      = sub->next;
            const cy_substitution_set_t substitutions = { .count         = cpl->substitution_count,
                                                          .substitutions = cpl->substitutions };
            const bool use_reordering = (sub->params.reordering_window >= 0) && // minimums enforced at API level
                                        (sub->params.reordering_capacity >= REORDERING_CAPACITY_MIN);
            if (use_reordering) {
                reordering_context_t ctx = {
                    .now           = message.timestamp,
                    .remote_id     = remote_id,
                    .subscriber    = sub,
                    .topic         = topic, // The topic and coupling references will be kept alive by the subscriber.
                    .substitutions = substitutions,
                    .tag           = tag,
                };
                // Will either find an existing state or create a new one; NULL on OOM only.
                reordering_t* const rr = CAVL2_TO_OWNER(cavl2_find_or_insert(&sub->index_reordering_by_remote_id, //
                                                                             &ctx,
                                                                             reordering_cavl_compare,
                                                                             &ctx,
                                                                             reordering_cavl_factory),
                                                        reordering_t,
                                                        index);
                if (rr != NULL) { // Simply ignore on OOM, nothing we can do.
                    assert(rr->remote_id == remote_id);
                    assert(rr->topic == topic);
                    assert(rr->subscriber == sub);
                    rr->p2p_context = p2p_context; // keep the latest known return path discovery from the transport
                    if (reordering_push(rr, tag, message)) {
                        acknowledge = true;
                    }
                }
            } else {
                subscriber_invoke(sub, make_arrival(topic, remote_id, p2p_context, tag, message, substitutions));
                acknowledge = true;
            }
            sub = next_sub;
        }
        cpl = next_cpl;
    }

    return acknowledge;
}

/// This is linear complexity but we expect to have few subscribers per topic, so it is acceptable.
static size_t get_subscription_extent(const cy_topic_t* const topic)
{
    size_t total = 0;
    // Go over all couplings and all subscribers in each coupling.
    // A coupling corresponds to a particular name that matched the topic.
    // Each coupling has a list of subscribers under its root sharing that name.
    const cy_topic_coupling_t* cpl = topic->couplings;
    assert(cpl != NULL);
    while (cpl != NULL) {
        const bool             verbatim = cpl->root->index_pattern == NULL; // no substitution tokens in the name
        const cy_subscriber_t* sub      = cpl->root->head;
        size_t                 agg      = sub->params.extent;
        sub                             = sub->next;
        while (sub != NULL) {
            agg = larger(agg, sub->params.extent);
            sub = sub->next;
        }
        if (verbatim) {
            total = agg;
            break; // Verbatim subscription takes precedence, ignore the rest.
        }
        // If only pattern subscriptions exist, merge them all.
        total = larger(total, agg);
        cpl   = cpl->next;
    }
    CY_TRACE(topic->cy, "📬 %s extent=%zu", topic_repr(topic).str, total);
    return total;
}

/// Returns non-NULL on OOM, which aborts the traversal early.
static void* wkv_cb_couple_new_subscription(const wkv_event_t evt)
{
    const cy_subscriber_t* const sub   = (cy_subscriber_t*)evt.context;
    cy_topic_t* const            topic = (cy_topic_t*)evt.node->value;
    cy_t* const                  cy    = topic->cy;
    // Sample the old parameters before the new coupling is created to decide if we need to refresh the subscription.
    const size_t   extent_old = topic->subscribed ? get_subscription_extent(topic) : 0;
    const cy_err_t res        = topic_couple(topic, sub->root, evt.substitution_count, evt.substitutions);
    if (res == CY_OK) {
        if (topic->subscribed && (get_subscription_extent(topic) > extent_old)) {
            CY_TRACE(cy, "🚧 %s subscription refresh", topic_repr(topic).str);
            cy->vtable->unsubscribe(topic);
            topic->subscribed = false;
        }
        topic_ensure_subscribed(topic);
    }
    return (CY_OK == res) ? NULL : "";
}

/// Either finds an existing subscriber root or creates a new one. NULL if OOM.
/// A subscriber root corresponds to a unique subscription name (with possible wildcards), hosting at least one
/// live subscriber.
static cy_err_t ensure_subscriber_root(cy_t* const               cy,
                                       const wkv_str_t           resolved_name,
                                       subscriber_root_t** const out_root)
{
    assert((cy != NULL) && (resolved_name.str != NULL) && (resolved_name.len > 0U) && (out_root != NULL));

    // Find or allocate a tree node. If exists, return as-is.
    wkv_node_t* const node = wkv_set(&cy->subscribers_by_name, resolved_name);
    if (node == NULL) {
        return CY_ERR_MEMORY;
    }
    if (node->value != NULL) {
        *out_root = (subscriber_root_t*)node->value;
        return CY_OK;
    }
    CY_TRACE(cy, "✨'%s'", resolved_name.str);

    // Otherwise, allocate a new root, if possible.
    node->value = mem_alloc_zero(cy, sizeof(subscriber_root_t));
    if (node->value == NULL) {
        wkv_del(&cy->subscribers_by_name, node);
        return CY_ERR_MEMORY;
    }
    subscriber_root_t* const root = (subscriber_root_t*)node->value;
    root->cy                      = cy;

    // Insert the new root into the indexes.
    root->index_name = node;
    if (!cy_name_is_verbatim(resolved_name)) {
        root->index_pattern = wkv_set(&cy->subscribers_by_pattern, resolved_name);
        if (root->index_pattern == NULL) {
            wkv_del(&cy->subscribers_by_name, node);
            mem_free(cy, node->value);
            return CY_ERR_MEMORY;
        }
        assert(root->index_pattern->value == NULL);
        root->index_pattern->value = root;
        enlist_head(&cy->list_scout_pending, &root->list_scout_pending);
    } else {
        root->index_pattern = NULL;
        const cy_err_t res  = topic_ensure(cy, NULL, resolved_name);
        if (res != CY_OK) {
            wkv_del(&cy->subscribers_by_name, node);
            mem_free(cy, node->value);
            return res;
        }
    }

    *out_root = root;
    return CY_OK;
}

static void subscriber_callback_default(cy_subscriber_t* const sub, const cy_arrival_t arrival)
{
    (void)sub;
    (void)arrival;
}

static cy_subscriber_t* subscribe(cy_t* const cy, const wkv_str_t name, subscriber_params_t params)
{
    assert((cy != NULL) && (params.reordering_window >= -1));
    char            name_buf[CY_TOPIC_NAME_MAX + 1U];
    const wkv_str_t resolved = cy_name_resolve(name, cy->ns, cy->home, sizeof(name_buf), name_buf);
    if (resolved.len > CY_TOPIC_NAME_MAX) {
        return NULL;
    }
    name_buf[resolved.len]     = 0; // this is not needed for the logic but helps with tracing (if enabled)
    cy_subscriber_t* const sub = mem_alloc_zero(cy, sizeof(*sub));
    if (sub == NULL) {
        return NULL;
    }
    params.reordering_capacity =
      (params.reordering_capacity == 0) ? 0 : larger(params.reordering_capacity, REORDERING_CAPACITY_MIN);
    sub->params        = params;
    sub->user_context  = CY_USER_CONTEXT_EMPTY;
    sub->callback      = subscriber_callback_default;
    const cy_err_t res = ensure_subscriber_root(cy, resolved, &sub->root);
    if (res != CY_OK) {
        mem_free(cy, sub);
        return NULL;
    }
    assert(sub->root != NULL);
    sub->next       = sub->root->head;
    sub->root->head = sub;
    if (NULL != wkv_match(&cy->topics_by_name, resolved, sub, wkv_cb_couple_new_subscription)) {
        cy_unsubscribe(sub);
        return NULL;
    }
    CY_TRACE(cy, "✨'%s' extent=%zu rwin=%lld", resolved.str, params.extent, (long long)params.reordering_window);
    return sub;
}

cy_subscriber_t* cy_subscribe(cy_t* const cy, const wkv_str_t name, const size_t extent)
{
    if (cy != NULL) {
        const subscriber_params_t params = { .extent = extent, .reordering_window = -1, .reordering_capacity = 0 };
        return subscribe(cy, name, params);
    }
    return NULL;
}

cy_subscriber_t* cy_subscribe_ordered(cy_t* const     cy,
                                      const wkv_str_t name,
                                      const size_t    extent,
                                      const cy_us_t   reordering_window)
{
    if ((cy != NULL) && (reordering_window >= 0)) {
        const subscriber_params_t params = {
            .extent              = extent,
            .reordering_window   = min_i64(reordering_window, SESSION_LIFETIME / 2), // sane limit for extra paranoia
            .reordering_capacity = REORDERING_CAPACITY_DEFAULT,
        };
        return subscribe(cy, name, params);
    }
    return NULL;
}

cy_user_context_t cy_subscriber_context(const cy_subscriber_t* const self) { return self->user_context; }
void              cy_subscriber_context_set(cy_subscriber_t* const self, const cy_user_context_t context)
{
    self->user_context = context;
}

cy_subscriber_callback_t cy_subscriber_callback(const cy_subscriber_t* const self) { return self->callback; }
void cy_subscriber_callback_set(cy_subscriber_t* const self, const cy_subscriber_callback_t callback)
{
    self->callback = (callback == NULL) ? subscriber_callback_default : callback;
}

void cy_subscriber_name(const cy_subscriber_t* const self, char* const out_name)
{
    wkv_get_key(&self->root->cy->subscribers_by_name, self->root->index_name, out_name);
}

void cy_unsubscribe(cy_subscriber_t* const self)
{
    // TODO: Do not destroy the subscriber immediately; schedule an olga event instead with zero deferral timeout.
    //   This will allow unsubscribing from within a callback. We'll need a test for that.
    (void)self;
}

static cy_err_t do_respond(cy_breadcrumb_t* const breadcrumb, const cy_us_t deadline, const cy_bytes_t message)
{
    assert((breadcrumb != NULL) && (breadcrumb->cy != NULL) && (deadline >= 0));
    heartbeat_begin(breadcrumb->cy);

    // Compose the header.
    const uint64_t      seqno       = breadcrumb->seqno++;
    const header_type_t header_type = header_rsp_be;
    const uint16_t      tag         = 0U;
    assert(seqno < (1ULL << 48U)); // Sanity check -- this is unreachable.
    byte_t header[16];
    (void)serialize_u64(serialize_u64(header, (breadcrumb->message_tag << 56U) | (uint64_t)header_type),
                        seqno | ((uint64_t)tag << 48U));
    const cy_bytes_t headed_message = { .size = sizeof(header), .data = header, .next = &message };

    // Send the P2P response.
    return breadcrumb->cy->vtable->p2p(
      breadcrumb->cy, &breadcrumb->p2p_context, deadline, breadcrumb->remote_id, headed_message);
}

cy_err_t cy_respond(cy_breadcrumb_t* const breadcrumb, const cy_us_t deadline, const cy_bytes_t message)
{
    if ((breadcrumb != NULL) && (breadcrumb->cy != NULL) && (deadline >= 0)) {
        return do_respond(breadcrumb, deadline, message);
    }
    return CY_ERR_ARGUMENT;
}

// =====================================================================================================================
//                                                  NODE & TOPIC
// =====================================================================================================================

cy_us_t cy_now(const cy_t* const cy)
{
    const cy_us_t out = cy->vtable->now(cy);
    assert(out >= 0);
    return out;
}

cy_topic_t* cy_topic_find_by_name(const cy_t* const cy, const wkv_str_t name)
{
    const wkv_node_t* const node  = wkv_get(&cy->topics_by_name, name);
    cy_topic_t* const       topic = (node != NULL) ? (cy_topic_t*)node->value : NULL;
    assert(topic == cy_topic_find_by_hash(cy, topic_hash(name)));
    return topic;
}

cy_topic_t* cy_topic_find_by_hash(const cy_t* const cy, const uint64_t hash)
{
    assert(cy != NULL);
    cy_topic_t* const topic = (cy_topic_t*)cavl2_find(cy->topics_by_hash, &hash, &cavl_comp_topic_hash);
    assert((topic == NULL) || (topic->hash == hash));
    assert((topic == NULL) || cy_name_is_verbatim(cy_topic_name(topic)) ||
           (topic->pub_count == 0)); // pub only verbatim
    return topic;
}

cy_topic_t* cy_topic_iter_first(const cy_t* const cy) { return (cy_topic_t*)cavl2_min(cy->topics_by_hash); }
cy_topic_t* cy_topic_iter_next(cy_topic_t* const topic) { return (cy_topic_t*)cavl2_next_greater(&topic->index_hash); }

wkv_str_t cy_topic_name(const cy_topic_t* const topic)
{
    if (topic != NULL) {
        return (wkv_str_t){ .len = topic->index_name->key_len, .str = topic->name };
    }
    return (wkv_str_t){ .len = 0, .str = "" };
}
uint64_t cy_topic_hash(const cy_topic_t* const topic) { return (topic != NULL) ? topic->hash : UINT64_MAX; }
cy_t*    cy_topic_owner(const cy_topic_t* const topic) { return (topic != NULL) ? topic->cy : NULL; }

cy_user_context_t* cy_topic_user_context(cy_topic_t* const topic)
{
    return (topic != NULL) ? &topic->user_context : NULL;
}

// =====================================================================================================================
//                                              PLATFORM LAYER INTERFACE
// =====================================================================================================================

static bool is_prime_u32(const uint32_t n)
{
    if ((n <= 2U) || ((n & 1U) == 0U)) {
        return n == 2U;
    }
    for (uint32_t d = 3U; d <= (n / d); d += 2U) {
        if ((n % d) == 0U) {
            return false;
        }
    }
    return true;
}

static cy_us_t olga_now(olga_t* const sched) { return cy_now((cy_t*)sched->user); }

cy_err_t cy_new(cy_t* const              cy,
                const cy_vtable_t* const vtable,
                const wkv_str_t          home,
                const wkv_str_t          namespace_,
                const uint32_t           subject_id_modulus)
{
    if ((cy == NULL) || (vtable == NULL) || (subject_id_modulus < CY_SUBJECT_ID_MODULUS_17bit) ||
        !is_prime_u32(subject_id_modulus)) {
        return CY_ERR_ARGUMENT;
    }
    const bool home_valid = cy_name_is_valid(home) || (home.len == 0);
    const bool ns_valid   = cy_name_is_valid(namespace_) || (namespace_.len == 0);
    if (!home_valid || !ns_valid) {
        return CY_ERR_NAME;
    }
    memset(cy, 0, sizeof(*cy));
    cy->vtable             = vtable;
    cy->subject_id_modulus = subject_id_modulus;

    // TODO FIXME: move cy_t inside cy.c and store olga by value.
    cy->olga = mem_alloc_zero(cy, sizeof(olga_t));
    if (cy->olga == NULL) {
        return CY_ERR_MEMORY;
    }
    olga_init(cy->olga, cy, olga_now);

    // Only home needs to be freed at destruction.
    char* const home_z = mem_alloc(cy, (home.len + 1) + (larger(namespace_.len, 1) + 1));
    if (home_z == NULL) {
        return CY_ERR_MEMORY;
    }
    memcpy(home_z, home.str, home.len);
    home_z[home.len] = '\0';
    char* const ns_z = &home_z[home.len + 1];
    memcpy(ns_z, namespace_.str, namespace_.len);
    ns_z[namespace_.len] = '\0';
    cy->home             = (wkv_str_t){ .len = home.len, .str = home_z };
    cy->ns               = (wkv_str_t){ .len = namespace_.len, .str = ns_z };

    cy->topics_by_hash       = NULL;
    cy->topics_by_subject_id = NULL;

    wkv_init(&cy->topics_by_name, &wkv_realloc);
    cy->topics_by_name.context = cy;

    wkv_init(&cy->subscribers_by_name, &wkv_realloc);
    cy->subscribers_by_name.context = cy;

    wkv_init(&cy->subscribers_by_pattern, &wkv_realloc);
    cy->subscribers_by_pattern.context = cy;

    cy->list_implicit      = LIST_EMPTY;
    cy->list_gossip_urgent = LIST_EMPTY;
    cy->list_gossip        = LIST_EMPTY;
    cy->list_scout_pending = LIST_EMPTY;

    // Postpone calling the functions until after the object is set up.
    cy->ts_started = cy_now(cy);

    // Initially, the heartbeat scheduling logic is disabled, because the first heartbeat is sent together with
    // the first publication. This allows listen-only nodes to avoid transmitting anything.
    cy->heartbeat_next        = HEAT_DEATH;
    cy->heartbeat_next_urgent = HEAT_DEATH;
    cy->heartbeat_period      = 3 * MEGA; // May be made configurable at some point if necessary.

    cy->implicit_topic_timeout = IMPLICIT_TOPIC_DEFAULT_TIMEOUT_us;
    cy->ack_baseline_timeout   = ACK_BASELINE_DEFAULT_TIMEOUT_us;

    cy->publish_futures_by_tag  = NULL;
    cy->request_futures_by_tag  = NULL;
    cy->response_futures_by_tag = NULL;

    cy->p2p_extent = HEADER_MAX_BYTES + 1024U; // Arbitrary initial size; will be refined when publishers are created.
    cy->vtable->p2p_extent(cy, cy->p2p_extent);

    // Pub/sub on the heartbeat topic.
    const wkv_str_t hb_name = wkv_key(CY_HEARTBEAT_TOPIC_NAME);
    cy->heartbeat_pub       = cy_advertise(cy, hb_name);
    if (cy->heartbeat_pub == NULL) {
        return CY_ERR_MEMORY;
    }
    assert(cy->heartbeat_pub->topic->hash == CY_HEARTBEAT_TOPIC_HASH);
    cy->heartbeat_sub = cy_subscribe(cy, hb_name, HEARTBEAT_SIZE_MAX);
    if (cy->heartbeat_sub == NULL) {
        cy_unadvertise(cy->heartbeat_pub);
        return CY_ERR_MEMORY;
    }
    cy_subscriber_callback_set(cy->heartbeat_sub, &on_heartbeat);
    CY_TRACE(cy,
             "🚀 home='%s' ns='%s' ts_started=%llu subject_id_modulus=%lu",
             cy->home.str,
             cy->ns.str,
             (unsigned long long)cy->ts_started,
             (unsigned long)cy->subject_id_modulus);
    return CY_OK;
}

void cy_destroy(cy_t* const cy) { (void)cy; }

uint32_t cy_topic_subject_id(const cy_topic_t* const topic)
{
    assert(topic != NULL);
    return topic_subject_id(topic->cy, topic->hash, topic->evictions);
}

static cy_err_t heartbeat_poll(cy_t* const cy, const cy_us_t now)
{
    // Decide if it is time to publish a heartbeat. We use a very simple minimal-state scheduler that runs two
    // periods and offers an opportunity to publish a heartbeat every now and then.
    cy_err_t res = CY_OK;
    if ((now >= cy->heartbeat_next) || (now >= cy->heartbeat_next_urgent)) {
        cy_topic_t*              topic = LIST_TAIL(cy->list_gossip_urgent, cy_topic_t, list_gossip_urgent);
        subscriber_root_t* const scout = LIST_TAIL(cy->list_scout_pending, subscriber_root_t, list_scout_pending);
        if ((now >= cy->heartbeat_next) || (topic != NULL) || (scout != NULL)) {
            if ((topic != NULL) || (scout == NULL)) {
                topic = (topic != NULL) ? topic : LIST_TAIL(cy->list_gossip, cy_topic_t, list_gossip);
                topic = (topic != NULL) ? topic : cy->heartbeat_pub->topic;
                res   = publish_heartbeat_gossip(cy, topic, now);
            } else {
                res = publish_heartbeat_scout(cy, scout, now);
            }
            cy->heartbeat_next = now + dither_int(cy, cy->heartbeat_period, cy->heartbeat_period / 8);
        }
        cy->heartbeat_next_urgent = now + (cy->heartbeat_period / 32);
    }
    return res;
}

cy_err_t cy_update(cy_t* const cy)
{
    if (cy == NULL) {
        return CY_ERR_ARGUMENT;
    }
    const olga_spin_result_t spin_result = olga_spin(cy->olga);
    const cy_us_t            now         = (spin_result.now == BIG_BANG) ? cy_now(cy) : spin_result.now;
    retire_expired_implicit_topics(cy, now);

    // Topic iteration -- one at a time for managing non-time-critical stale states with minimal costs.
    if (cy->topic_iter == NULL) {
        cy->topic_iter = cy_topic_iter_first(cy);
    }
    if (cy->topic_iter != NULL) {
        dedup_drop_stale(cy->topic_iter, now);
        // Do we accept the full subscriber scan here?
        const cy_topic_coupling_t* cpl = cy->topic_iter->couplings;
        while (cpl != NULL) {
            cy_subscriber_t* sub = cpl->root->head;
            while (sub != NULL) {
                reordering_drop_stale(sub, now);
                sub = sub->next;
            }
            cpl = cpl->next;
        }
        cy->topic_iter = cy_topic_iter_next(cy->topic_iter);
    }

    return heartbeat_poll(cy, now);
}

#if 0 // NOLINT(readability-avoid-unconditional-preprocessor-if)
static void on_response(cy_t* const             cy,
                        const cy_p2p_context_t  p2p_context,
                        const uint64_t          remote_id,
                        request_future_t* const future,
                        const uint64_t          seqno,
                        const uint16_t          tag,
                        cy_message_ts_t         message)
{
    //
}
#endif

#if 0 // NOLINT(readability-avoid-unconditional-preprocessor-if)
static void on_message_ack(cy_t* const cy, publish_future_t* const future)
{
    // Currently, we use a very simple implementation that ceases delivery attempts after the first acknowledgment
    // is received, similar to the CAN bus. Such mode of reliability is useful in the following scenarios:
    //
    // - With topics with a single subscriber, or sent via P2P transport (responses to published messages).
    //   With a single recipient, a single acknowledgement is sufficient to guarantee delivery.
    //
    // - The application only cares about one acknowledgement (anycast), e.g., with modular redundant nodes.
    //
    // - The application assumes that if one copy was delivered successfully, then other copies have likely
    //   succeeded as well (depends on the required reliability guarantees), similar to the CAN bus.
    //
    // TODO In the future, there are plans to extend this mechanism to track the number of acknowledgements per topic,
    // such that we can keep pending publications until a specified number of acknowledgements have been received.
    // A remote node can be considered to have disappeared if it failed to acknowledge a transfer after the maximum
    // number of attempts have been made (i.e., the deadline expired). This is somewhat similar in principle to the
    // connection-oriented DDS/RTPS approach, where pub/sub associations are established and removed automatically,
    // transparently to the application.
    future_deadline_disarm(&future->base);
    future_index_remove(&future->base, &cy->publish_futures_by_tag);
    assert(future->result.acknowledgements == 0);
    future->result.acknowledgements++;
    future_notify(&future->base);
}
#endif

#if 0 // NOLINT(readability-avoid-unconditional-preprocessor-if)
static void on_response_ack(cy_t* const cy, response_future_t* const future, const bool positive)
{
    //
}
#endif

static void send_message_ack(cy_t* const            cy,
                             const cy_p2p_context_t p2p_context,
                             const uint64_t         remote_id,
                             const uint64_t         tag,
                             const uint64_t         topic_hash,
                             const cy_us_t          deadline)
{
    byte_t header[16];
    (void)serialize_u64(serialize_u64(header, (tag << 8U) | (uint64_t)header_msg_ack), topic_hash);
    const cy_err_t err =
      cy->vtable->p2p(cy, &p2p_context, deadline, remote_id, (cy_bytes_t){ .size = sizeof(header), .data = header });
    if (err != CY_OK) {
        CY_TRACE(cy,
                 "⚠️ Failed to send message ACK to %016llx for tag %016llx on topic %016llx: %d",
                 (unsigned long long)remote_id,
                 (unsigned long long)tag,
                 (unsigned long long)topic_hash,
                 (int)err);
    }
}

static void send_response_ack(cy_t* const            cy,
                              const cy_p2p_context_t p2p_context,
                              const uint64_t         remote_id,
                              const uint64_t         message_tag,
                              const uint64_t         seqno,
                              const uint16_t         tag,
                              const bool             positive,
                              const cy_us_t          deadline)
{
    byte_t              header[16];
    const header_type_t header_type = positive ? header_rsp_ack : header_rsp_nack;
    (void)serialize_u64(serialize_u64(header, (message_tag << 56U) | (uint64_t)header_type),
                        seqno | ((uint64_t)tag << 48U));
    const cy_err_t err =
      cy->vtable->p2p(cy, &p2p_context, deadline, remote_id, (cy_bytes_t){ .size = sizeof(header), .data = header });
    if (err != CY_OK) {
        CY_TRACE(cy,
                 "⚠️ Failed to send response %s to %016llx for seqno %016llx: %d",
                 positive ? "ACK" : "NACK",
                 (unsigned long long)remote_id,
                 (unsigned long long)seqno,
                 (int)err);
    }
}

void cy_on_message(cy_t* const            cy,
                   const cy_p2p_context_t p2p_context,
                   const uint64_t         subject_id,
                   const uint64_t         remote_id,
                   cy_message_ts_t        message)
{
    assert((cy != NULL) && (message.timestamp >= 0));
    assert(message.content->refcount == 1);
    byte_t header[HEADER_MAX_BYTES];
    if (HEADER_MAX_BYTES != cy_message_read(message.content, 0, HEADER_MAX_BYTES, header)) {
        cy_message_refcount_dec(message.content);
        return; // Malformed message; ignore.
    }
    message_skip(message.content, HEADER_MAX_BYTES);
    const header_type_t type = (header[0] & HEADER_TYPE_MASK);

    // This is the central entry point for all incoming messages. It's complex but there's an advantage to keeping the
    // central dispatch logic in one place because of the tight coupling between different parts of the stack.
    switch (type) {

        case header_msg_be:
        case header_msg_rel: {
            assert(subject_id < (CY_PINNED_SUBJECT_ID_MAX + cy->subject_id_modulus)); // transport must ensure
            const uint64_t    tag      = deserialize_u56(&header[1]);
            const uint64_t    hash     = deserialize_u64(&header[8]);
            cy_topic_t* const topic    = cy_topic_find_by_hash(cy, hash);
            const bool        reliable = type == header_msg_rel;
            if (topic != NULL) {
                if (cy_topic_subject_id(topic) != subject_id) {
                    // We happen to be subscribed to both of the divergent subject-IDs, so we can process the message
                    // despite the divergence.
                    CY_TRACE(cy,
                             "⚠️ Subject-ID divergence on message from %016llx for topic %016llx: expected %lu got %llu"
                             " Scheduling urgent gossip to repair consensus",
                             (unsigned long long)remote_id,
                             (unsigned long long)hash,
                             (unsigned long)cy_topic_subject_id(topic),
                             (unsigned long long)subject_id);
                    schedule_gossip_urgent(topic);
                }
                const bool accepted = on_message(cy, p2p_context, remote_id, topic, tag, message, reliable);
                if (reliable && accepted) {
                    send_message_ack(cy, // This is either new or retransmit, must ack either way.
                                     p2p_context,
                                     remote_id,
                                     tag,
                                     hash,
                                     message.timestamp + ACK_TX_TIMEOUT);
                }
            } else {
                cy_topic_t* const other_topic = topic_find_by_subject_id(cy, (uint32_t)subject_id);
                if (other_topic != NULL) {
                    assert(other_topic->hash != hash);
                    // Gossip to either update the remotes or solicit a newer allocation state from them.
                    CY_TRACE(cy,
                             "⚠️ Subject-ID collision on message from %016llx: topic %016llx vs %016llx"
                             " Scheduling urgent gossip to repair consensus",
                             (unsigned long long)remote_id,
                             (unsigned long long)hash,
                             (unsigned long long)other_topic->hash);
                    schedule_gossip_urgent(other_topic);
                } else {
                    CY_TRACE(cy,
                             "⚠️ Unsolicited message from %016llx on topic %016llx subject %08x: unknown topic&subject",
                             (unsigned long long)remote_id,
                             (unsigned long long)hash,
                             (unsigned)subject_id);
                }
            }
            break;
        }

#if 0 // NOLINT(readability-avoid-unconditional-preprocessor-if)
        case header_msg_ack: {
            const uint64_t tag = deserialize_u56(&header[1]);
            assert(type == header_msg_ack);
            publish_future_t* const future = (publish_future_t*)future_index_lookup(&cy->publish_futures_by_tag, tag);
            if (future != NULL) {
                on_message_ack(cy, future);
            } else {
                CY_TRACE(cy,
                         "⚠️ Orphan message ACK from %016llx for tag %016llx",
                         (unsigned long long)remote_id,
                         (unsigned long long)tag);
            }
            break;
        }
#endif
#if 0 // NOLINT(readability-avoid-unconditional-preprocessor-if)
        case header_rsp_be:
        case header_rsp_rel: {
            const uint64_t          message_tag = deserialize_u56(&header[1]);
            const uint64_t          seqno_tag   = deserialize_u64(&header[8]);
            const uint16_t          tag         = (seqno_tag >> 48U) & 0xFFFFU;
            const uint64_t          seqno       = seqno_tag & SEQNO48_MASK;
            request_future_t* const future =
              (request_future_t*)future_index_lookup(&cy->request_futures_by_tag, message_tag);
            if (type == header_rsp_rel) {
                /// A known ambiguity exists if the server sends a reliable response that is accepted, but the
                /// first positive-ack is lost; the server will retransmit the response, but the client application
                /// may no longer be listening if it only needed a single response; the second response will be a
                /// nack instead of a pack. If this becomes a problem, store a short list of recently
                /// positively-acked responses in the Cy state.
                send_response_ack(cy,
                                  p2p_context,
                                  remote_id,
                                  message_tag,
                                  seqno,
                                  tag,
                                  future != NULL,
                                  message.timestamp + ACK_TX_TIMEOUT);
            }
            if (future != NULL) {
                on_response(cy, p2p_context, remote_id, future, seqno, tag, message);
            } else {
                CY_TRACE(cy,
                         "⚠️ Orphan response from %016llx for request tag %016llx",
                         (unsigned long long)remote_id,
                         (unsigned long long)message_tag);
            }
            break;
        }

        case header_rsp_ack:
        case header_rsp_nack: {
            const uint64_t message_tag = deserialize_u56(&header[1]);
            const uint64_t seqno_tag   = deserialize_u64(&header[8]);
            const uint64_t key = rapidhash((uint64_t[3]){ remote_id, message_tag, seqno_tag }, 24); // local transform
            response_future_t* const future =
              (response_future_t*)future_index_lookup(&cy->response_futures_by_tag, key);
            if (future != NULL) {
                on_response_ack(cy, future, type == header_rsp_ack);
            } else {
                CY_TRACE(cy,
                         "⚠️ Orphan response %s from %016llx for key %016llx",
                         (type == header_rsp_ack) ? "ACK" : "NACK",
                         (unsigned long long)remote_id,
                         (unsigned long long)key);
            }
            break;
        }
#endif
        default:
            CY_TRACE(cy, "⚠️ Unsupported message from %016llx: header type %02x", (unsigned long long)remote_id, type);
            break;
    }
    cy_message_refcount_dec(message.content);
}

// =====================================================================================================================
//                                                      NAMES
// =====================================================================================================================

const char cy_name_sep  = '/';
const char cy_name_home = '~';

/// Accepts all printable ASCII characters except SPACE.
static bool is_valid_char(const char c) { return (c >= 33) && (c <= 126); }

bool cy_name_is_valid(const wkv_str_t name)
{
    if ((name.len == 0) || (name.len > CY_TOPIC_NAME_MAX) || (name.str == NULL)) {
        return false;
    }
    for (size_t i = 0; i < name.len; ++i) {
        const char c = name.str[i];
        if (!is_valid_char(c)) {
            return false;
        }
    }
    return true;
}

bool cy_name_is_verbatim(const wkv_str_t name)
{
    wkv_t kv;
    wkv_init(&kv, &wkv_realloc);
    return !wkv_has_substitution_tokens(&kv, name);
}

bool cy_name_is_homeful(const wkv_str_t name)
{
    return (name.len >= 1) && (name.str[0] == cy_name_home) && ((name.len == 1) || (name.str[1] == cy_name_sep));
}

bool cy_name_is_absolute(const wkv_str_t name) { return (name.len >= 1) && (name.str[0] == cy_name_sep); }

/// Writes the normalized and validated version of `name` into `dest`, which must be at least `dest_size` bytes long.
/// Normalization at least removes duplicate, leading, and trailing name separators.
/// The input string length must not include NUL terminator; the output string is also not NUL-terminated.
/// In case of failure, the destination buffer may be partially written.
static wkv_str_t name_normalize(const size_t in_size, const char* in, const size_t dest_size, char* const dest)
{
    if ((in == NULL) || (dest == NULL)) {
        return str_invalid;
    }
    const char* const in_end      = in + in_size;
    char*             out         = dest;
    const char* const out_end     = dest + dest_size;
    bool              pending_sep = false;
    while (in < in_end) {
        const char c = *in++;
        if (!is_valid_char(c)) {
            return str_invalid;
        }
        if (c == cy_name_sep) {
            pending_sep = out > dest; // skip duplicate and leading separators
            continue;
        }
        if (pending_sep) {
            pending_sep = false;
            if (out < out_end) {
                *out++ = cy_name_sep;
            }
        }
        if (out >= out_end) {
            return str_invalid;
        }
        *out++ = c;
    }
    assert(out <= out_end);
    return (wkv_str_t){ .len = (size_t)(out - dest), .str = dest };
}

wkv_str_t cy_name_join(const wkv_str_t left, const wkv_str_t right, const size_t dest_size, char* const dest)
{
    if (dest == NULL) {
        return str_invalid;
    }
    size_t len = name_normalize(left.len, left.str, dest_size, dest).len;
    if (len >= dest_size) {
        return str_invalid;
    }
    assert(len < dest_size);
    if (len > 0) {
        dest[len++] = cy_name_sep;
    }
    assert(len <= dest_size);
    const size_t right_len = name_normalize(right.len, right.str, dest_size - len, &dest[len]).len;
    if (right_len > (dest_size - len)) {
        return str_invalid;
    }
    if ((right_len == 0) && (len > 0)) {
        len--;
    }
    return (wkv_str_t){ .len = len + right_len, .str = dest };
}

wkv_str_t cy_name_expand_home(wkv_str_t name, const wkv_str_t home, const size_t dest_size, char* const dest)
{
    if (dest == NULL) {
        return str_invalid;
    }
    if (!cy_name_is_homeful(name)) {
        return name_normalize(name.len, name.str, dest_size, dest);
    }
    assert(name.len >= 1);
    name.len -= 1U;
    name.str += 1;
    return cy_name_join(home, name, dest_size, dest);
}

wkv_str_t cy_name_resolve(const wkv_str_t name,
                          wkv_str_t       namespace_,
                          const wkv_str_t home,
                          const size_t    dest_size,
                          char*           dest)
{
    if (dest == NULL) {
        return str_invalid;
    }
    if (cy_name_is_absolute(name)) {
        return name_normalize(name.len, name.str, dest_size, dest);
    }
    if (cy_name_is_homeful(name)) {
        return cy_name_expand_home(name, home, dest_size, dest);
    }
    if (cy_name_is_homeful(namespace_)) {
        namespace_ = cy_name_expand_home(namespace_, home, dest_size, dest);
        if (namespace_.len >= dest_size) {
            return str_invalid;
        }
    }
    return cy_name_join(namespace_, name, dest_size, dest);
}
