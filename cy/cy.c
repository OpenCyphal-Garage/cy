///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

// ReSharper disable CppDFATimeOver
// ReSharper disable CppDFAConstantParameter
// ReSharper disable CppDFANullDereference

#include "cy_platform.h"

#define CAVL2_RELATION int32_t
#define CAVL2_T        cy_tree_t
#include <cavl2.h>

#define RAPIDHASH_COMPACT // because we hash strings <96 bytes long
#include <rapidhash.h>

#include <assert.h>
#include <string.h>

#define KILO 1000L
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

typedef unsigned char byte_t;

static size_t  larger(const size_t a, const size_t b) { return (a > b) ? a : b; }
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

/// A human-friendly representation of the topic for logging and diagnostics.
typedef struct
{
    char str[CY_TOPIC_NAME_MAX + 32];
} topic_repr_t;
static topic_repr_t topic_repr(const cy_topic_t* const topic)
{
    assert(topic != NULL);
    topic_repr_t out;
    char*        ptr = out.str;
    *ptr++           = 'T';
    ptr += cy_u64_to_hex(topic->hash, ptr).len;
    *ptr++ = '@';
    ptr += cy_u32_to_hex(cy_topic_subject_id(topic), ptr).len;
    *ptr++               = '\'';
    const wkv_str_t name = cy_topic_name(topic);
    memcpy(ptr, name.str, name.len);
    ptr += name.len;
    *ptr++ = '\'';
    *ptr   = '\0';
    assert((ptr - out.str) <= (ptrdiff_t)sizeof(out.str));
    return out;
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

// =====================================================================================================================
//                                                  MESSAGE BUFFER
// =====================================================================================================================

// ReSharper disable CppParameterMayBeConstPtrOrRef

/// These are provided for safety only, to ensure valid behavior shall the user attempt to operate on an empty message.
static void   v_message_empty_destroy(cy_message_t* const self) { (void)self; }
static size_t v_message_empty_read(cy_message_t* const self, const size_t offset, const size_t size, void* const dest)
{
    (void)self;
    (void)dest;
    (void)offset;
    (void)size;
    return 0;
}
static const cy_message_vtable_t message_empty_vtable = { .destroy = v_message_empty_destroy,
                                                          .read    = v_message_empty_read };
static const cy_message_t        message_empty = { .state = { NULL }, .size = 0, .vtable = &message_empty_vtable };

cy_message_t cy_message_move(cy_message_t* const msg)
{
    const cy_message_t ret = *msg;
    *msg                   = message_empty;
    return ret;
}

size_t cy_message_read(cy_message_t* const cursor, const size_t offset, const size_t size, void* const destination)
{
    if ((cursor != NULL) && (cursor->vtable != NULL) && (destination != NULL)) {
        return cursor->vtable->read(cursor, offset, size, destination);
    }
    return 0;
}

void cy_message_destroy(cy_message_t* const msg)
{
    if ((msg != NULL) && (msg->vtable != NULL)) {
        msg->vtable->destroy(msg);
        (void)cy_message_move(msg);
    }
}

// ReSharper restore CppParameterMayBeConstPtrOrRef

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

struct cy_publisher_t
{
    cy_topic_t* topic; ///< Many-to-one relationship, never NULL; the topic is reference counted.
    cy_prio_t   priority;
    size_t      response_extent;
};

typedef struct
{
    size_t  extent;
    cy_us_t reordering_window;
} subscriber_params_t;

struct cy_subscriber_t
{
    subscriber_root_t* root; ///< Many-to-one relationship, never NULL.
    cy_subscriber_t*   next; ///< Lists all subscribers under the same root.

    subscriber_params_t      params;
    cy_user_context_t        user_context;
    cy_subscriber_callback_t callback;
};

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

/// Returns UINT32_MAX if the string is not a valid canonical pinned subject-ID form. A valid form is: "#01af".
static uint32_t parse_pinned(const wkv_str_t s)
{
    if ((s.len != 5) || (s.str[0] != '#')) {
        return UINT32_MAX;
    }
    uint32_t out = 0U;
    for (size_t i = 1; i < s.len; i++) {
        out <<= 4U;
        const unsigned char ch = (unsigned char)s.str[i];
        if ((ch >= '0') && (ch <= '9')) {
            out |= (uint32_t)(ch - '0');
        } else if ((ch >= 'a') && (ch <= 'f')) {
            out |= (uint32_t)(ch - 'a' + 10U);
        } else {
            return UINT32_MAX;
        }
    }
    return (out <= CY_PINNED_SUBJECT_ID_MAX) ? out : UINT32_MAX;
}

/// The topic hash is the key component of the protocol.
/// For pinned topics, hash<CY_TOTAL_SUBJECT_COUNT.
/// The probability of a random hash falling into the pinned range is ~4.44e-16, or about one in two quadrillion.
static uint64_t topic_hash(const wkv_str_t name)
{
    uint64_t hash = parse_pinned(name);
    if (hash > CY_PINNED_SUBJECT_ID_MAX) {
        hash = rapidhash(name.str, name.len);
    }
    return hash;
}

static uint32_t topic_subject_id(const cy_t* const cy, const uint64_t hash, const uint64_t evictions)
{
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

/// This is linear complexity but we expect to have few subscribers per topic, so it is acceptable.
/// If this becomes a problem, we can simply store the subscription parameters in the topic fields.
/// The disambiguation logic is up to review/improvement in the future based on real-world experience.
static subscriber_params_t deduce_subscription_params(const cy_topic_t* const topic)
{
    subscriber_params_t final = { .extent = 0, .reordering_window = BIG_BANG };
    // Go over all couplings and all subscribers in each coupling.
    // A coupling corresponds to a particular name that matched the topic.
    // Each coupling has a list of subscribers under its root sharing that name.
    const cy_topic_coupling_t* cpl = topic->couplings;
    assert(cpl != NULL);
    while (cpl != NULL) {
        const bool             verbatim = cpl->root->index_pattern == NULL; // no substitution tokens in the name
        const cy_subscriber_t* sub      = cpl->root->head;
        subscriber_params_t    agg      = sub->params;
        sub                             = sub->next;
        while (sub != NULL) {
            agg.extent            = larger(agg.extent, sub->params.extent);
            agg.reordering_window = max_i64(agg.reordering_window, sub->params.reordering_window);
            sub                   = sub->next;
        }
        if (verbatim) {
            final = agg;
            break; // Verbatim subscription takes precedence, ignore the rest.
        }
        // If only pattern subscriptions exist, merge them all.
        final.extent            = larger(final.extent, agg.extent);
        final.reordering_window = max_i64(final.reordering_window, agg.reordering_window);
        cpl                     = cpl->next;
    }
    CY_TRACE(topic->cy,
             "📬 %s extent=%zu rwin=%lld",
             topic_repr(topic).str,
             final.extent,
             (long long) final.reordering_window);
    return final;
}

/// If a subscription is needed but is not active, this function will attempt to resubscribe.
/// Errors are handled via the platform handler, so from the caller's perspective this is infallible.
static void topic_ensure_subscribed(cy_topic_t* const topic)
{
    if ((topic->couplings != NULL) && (!topic->subscribed)) {
        const subscriber_params_t params = deduce_subscription_params(topic);
        const cy_err_t            res    = topic->vtable->subscribe(topic, params.extent, params.reordering_window);
        topic->subscribed                = res == CY_OK;
        CY_TRACE(topic->cy,
                 "🗞️ %s extent=%zu rwin=%lld result=%d",
                 topic_repr(topic).str,
                 params.extent,
                 (long long)params.reordering_window,
                 res);
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
    static const int         call_depth_indent = 2;
    static _Thread_local int call_depth        = 0U;
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
        topic->vtable->unsubscribe(topic);
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
    topic->name = mem_alloc(cy, resolved_name.len + 1);
    if (topic->name == NULL) {
        goto oom;
    }
    memcpy(topic->name, resolved_name.str, resolved_name.len);
    topic->name[resolved_name.len] = '\0';

    const cy_us_t now = cy_now(cy);

    topic->cy        = cy;
    topic->hash      = hash;
    topic->evictions = evictions;

    topic->ts_origin   = now - (pow2us(lage) * MEGA);
    topic->ts_animated = now;

    topic->pub_count = 0;

    topic->couplings  = NULL;
    topic->subscribed = false;

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
    topic->vtable->destroy(topic);
    return CY_ERR_NAME;

bad_name: // TODO correct deinitialization
    topic->vtable->destroy(topic);
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
    // Attach subscriptions.
    if (NULL != wkv_route(&cy->subscribers_by_pattern, resolved_name, topic, wkv_cb_couple_new_topic)) {
        // TODO discard the topic!
        cy->vtable->on_subscription_error(cy, NULL, CY_ERR_MEMORY);
        return NULL;
    }
    // Create the transport subscription once at the end, considering the parameters from all subscribers.
    topic_ensure_subscribed(topic);
    return topic;
}

static void* wkv_cb_topic_scout_response(const wkv_event_t evt)
{
    cy_topic_t* const topic = (cy_topic_t*)evt.node->value;
    CY_TRACE(topic->cy, "📢 %s", topic_repr(topic).str);
    schedule_gossip_urgent(topic);
    return NULL;
}

// =====================================================================================================================
//                                                      HEARTBEAT
// =====================================================================================================================

#define HEARTBEAT_OFFSET_TOPIC_NAME 24U
#define HEARTBEAT_SIZE_MAX          (HEARTBEAT_OFFSET_TOPIC_NAME + CY_TOPIC_NAME_MAX)

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
static uint64_t deserialize_u64(const byte_t* ptr)
{
    uint64_t value = 0;
    for (size_t i = 0; i < 8; i++) {
        value |= ((uint64_t)*ptr++ << (i * 8U));
    }
    return value;
}

static cy_err_t publish_heartbeat(const cy_t* const cy,
                                  const cy_us_t     now,
                                  const uint64_t    topic_hash,
                                  const uint64_t    topic_evictions,
                                  const int8_t      topic_lage,
                                  const wkv_str_t   topic_name)
{
    assert(topic_name.len <= CY_TOPIC_NAME_MAX);
    const size_t message_size = HEARTBEAT_OFFSET_TOPIC_NAME + topic_name.len;
    byte_t       buf[HEARTBEAT_SIZE_MAX];
    byte_t*      ptr = buf;
    // uptime and user_word[3]
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
    return cy->heartbeat_pub->topic->vtable->publish(cy->heartbeat_pub->topic,
                                                     now + cy->heartbeat_period,
                                                     cy->heartbeat_pub->priority,
                                                     (cy_bytes_t){ .size = message_size, .data = buf },
                                                     NULL,
                                                     NULL,
                                                     0);
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

/// Will publish the first heartbeat if it hasn't been published yet. Does nothing otherwise.
/// Lazy heartbeat publication commencement is an important feature for listen-only nodes,
/// allowing them to avoid transmitting anything at all until they cease to be listen-only.
static cy_err_t heartbeat_begin(cy_t* const cy)
{
    cy_err_t res = CY_OK;
    if (cy->heartbeat_next == HEAT_DEATH) {
        CY_TRACE(cy, "🚀");
        const cy_us_t now  = cy_now(cy);
        cy->heartbeat_next = now;
        res                = heartbeat_poll(cy, now);
    }
    return res;
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
static hb_t heartbeat_deserialize(cy_message_t msg, byte_t* const name_buf)
{
    hb_t out = { .version = 0, .topic_name = { .len = 0, .str = (const char*)name_buf } };
    // implicit zero extension rule -- assume zero if absent from the message
    (void)cy_message_read(&msg, 7, 1, &out.version);
    if (out.version == 0) {
        return (hb_t){ 0 }; // Cyphal v1.0 heartbeat carries no topic information. Simply ignore.
    }
    if (out.version == 1) {
        static const size_t prefix_size = 8 + 5 + 1 + 1;
        assert(prefix_size <= CY_TOPIC_NAME_MAX + 1);
        if (prefix_size != cy_message_read(&msg, 8, prefix_size, name_buf)) {
            return (hb_t){ 0 }; // invalid size
        }
        out.topic_hash      = deserialize_u64(name_buf + 0);
        out.topic_evictions = deserialize_u40(name_buf + 8);
        out.topic_lage      = (int_fast8_t)name_buf[13];
        out.topic_name.len  = name_buf[15];
        if ((out.topic_name.len > CY_TOPIC_NAME_MAX) ||
            (out.topic_name.len != cy_message_read(&msg, 16, out.topic_name.len, name_buf))) {
            return (hb_t){ 0 }; // invalid size
        }
        name_buf[out.topic_name.len] = 0;
        return out;
    }
    return (hb_t){ 0 }; // unsupported version
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void on_heartbeat(const cy_user_context_t ctx, cy_arrival_t* const arrival)
{
    (void)ctx;
    assert(arrival->substitutions.count == 0); // This is a verbatim subscriber.
    const cy_us_t ts = arrival->message.timestamp;
    cy_t* const   cy = arrival->topic->cy;
    byte_t        scratchpad[CY_TOPIC_NAME_MAX + 1];
    const hb_t    hb = heartbeat_deserialize(arrival->message.content, scratchpad);
    if (hb.topic_lage >= -1) {
        // Find the topic in our local database. Create if there is a pattern match.
        cy_topic_t* mine = cy_topic_find_by_hash(cy, hb.topic_hash);
        if (mine == NULL) {
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
            // Everyone needs to publish their own new allocation and then we will pick max subject-ID out of that.
            if (!win) {
                topic_allocate(mine, mine->evictions + 1U, false, ts);
            } else {
                assert(!is_pinned(mine->hash));
                schedule_gossip_urgent(mine);
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

cy_publisher_t* cy_advertise(cy_t* const cy, const wkv_str_t name) { return cy_advertise_client(cy, name, 0); }

cy_publisher_t* cy_advertise_client(cy_t* const cy, const wkv_str_t name, const size_t response_extent)
{
    char            name_buf[CY_TOPIC_NAME_MAX];
    const wkv_str_t resolved = cy_name_resolve(name, cy->ns, cy->home, sizeof(name_buf), name_buf);
    if ((cy == NULL) || (resolved.len > sizeof(name_buf))) {
        return NULL;
    }
    if (!cy_name_is_verbatim(resolved)) {
        return NULL; // Wildcard publishers are not defined.
    }
    cy_publisher_t* const pub = mem_alloc_zero(cy, sizeof(*pub));
    if (pub == NULL) {
        return NULL;
    }
    const cy_err_t res   = topic_ensure(cy, &pub->topic, resolved);
    pub->priority        = cy_prio_nominal;
    pub->response_extent = response_extent;
    if (res == CY_OK) {
        assert(pub->topic != NULL);
        pub->topic->pub_count++;
        delist(&cy->list_implicit, &pub->topic->list_implicit);
    }
    CY_TRACE(cy,
             "✨ %s topic_count=%zu pub_count=%zu response_extent=%zu res=%d",
             topic_repr(pub->topic).str,
             cavl_count(cy->topics_by_hash),
             pub->topic->pub_count,
             response_extent,
             res);
    return (res == CY_OK) ? pub : NULL;
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
cy_err_t cy_publish(cy_publisher_t* const pub, const cy_us_t tx_deadline, const cy_bytes_t message)
{
    if ((pub == NULL) || (tx_deadline < 0)) {
        return CY_ERR_ARGUMENT;
    }
    assert(pub->topic->pub_count > 0);
    cy_err_t res = heartbeat_begin(pub->topic->cy);
    if (res == CY_OK) {
        res = pub->topic->vtable->publish(pub->topic, tx_deadline, pub->priority, message, NULL, NULL, 0);
    }
    return res;
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
cy_err_t cy_publish_reliable(cy_publisher_t* const        pub,
                             const cy_us_t                tx_deadline,
                             const cy_bytes_t             message,
                             const cy_user_context_t      ctx_delivery,
                             const cy_delivery_callback_t cb_delivery)
{
    if ((pub == NULL) || (tx_deadline < 0) || (cb_delivery == NULL)) {
        return CY_ERR_ARGUMENT;
    }
    assert(pub->topic->pub_count > 0);
    cy_err_t res = heartbeat_begin(pub->topic->cy);
    if (res == CY_OK) {
        const cy_feedback_context_t ctx = { .user = ctx_delivery, .fun = cb_delivery };
        res = pub->topic->vtable->publish(pub->topic, tx_deadline, pub->priority, message, &ctx, NULL, 0);
    }
    return res;
}

typedef struct
{
    cy_tree_t index_deadline;    ///< Global across all topics.
    cy_tree_t index_transfer_id; ///< Per-topic transfer-ID index.

    uint64_t transfer_id; ///< As returned by the platform publish() method.
    cy_us_t  deadline;

    cy_topic_t* topic;

    cy_user_context_t      user_context;
    cy_response_callback_t callback;
} pending_response_t;

/// Unlink from everywhere and deallocate the instance. The callback takes the ownership of the message.
static void pending_response_finalize(pending_response_t* const self, const cy_us_t ts, const cy_message_t msg)
{
    cy_t* const cy = self->topic->cy;
    CY_TRACE(cy,
             "📩 %s #%llu msize=%zu %s",
             topic_repr(self->topic).str,
             (unsigned long long)self->transfer_id,
             msg.size,
             (ts >= 0) ? "✅ SUCCESS" : "❌ NO RESPONSE");
    cavl2_remove(&cy->pending_responses_by_deadline, &self->index_deadline);
    cavl2_remove(&self->topic->pending_responses_by_transfer_id, &self->index_transfer_id);

    // Store the context needed to invoke the callback, then free the memory BEFORE invoking the callback.
    assert(self->callback != NULL);
    const cy_response_callback_t cb  = self->callback;
    const cy_user_context_t      ctx = self->user_context;
    mem_free(cy, self);

    // Invoke the callback to deliver the response. It may take ownership of the message.
    cy_message_ts_t mt = { .timestamp = ts, .content = msg };
    cb(ctx, (ts >= 0) ? &mt : NULL);

    // If the handler didn't take ownership of the message, destroy it here.
    if (cy_message_size(mt.content) > 0) {
        cy_message_destroy(&mt.content);
    }
}

/// Deadlines are not unique, so this comparator never returns 0.
static int32_t cavl_comp_pending_response_deadline(const void* const user, const cy_tree_t* const node)
{
    assert((user != NULL) && (node != NULL));
    const pending_response_t* const inner = CAVL2_TO_OWNER(node, pending_response_t, index_deadline);
    return ((*(cy_us_t*)user) >= inner->deadline) ? +1 : -1;
}

/// To find a pending response, one needs to locate the topic by hash first, if it exists when the response arrives.
static int32_t cavl_comp_pending_response_transfer_id(const void* const user, const cy_tree_t* const node)
{
    assert((user != NULL) && (node != NULL));
    const uint64_t                  outer = *(uint64_t*)user;
    const pending_response_t* const inner = CAVL2_TO_OWNER(node, pending_response_t, index_transfer_id);
    if (outer == inner->transfer_id) {
        return 0;
    }
    return (outer >= inner->transfer_id) ? +1 : -1;
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
cy_err_t cy_request(cy_publisher_t* const        pub,
                    const cy_us_t                tx_deadline,
                    const cy_us_t                response_deadline,
                    const cy_bytes_t             message,
                    const cy_user_context_t      ctx_delivery,
                    const cy_delivery_callback_t cb_delivery,
                    const cy_user_context_t      ctx_response,
                    const cy_response_callback_t cb_response)
{
    if ((pub == NULL) || (tx_deadline < 0) || (response_deadline < tx_deadline) || (cb_response == NULL)) {
        return CY_ERR_ARGUMENT;
    }
    cy_t* const cy = pub->topic->cy;
    assert(pub->topic->pub_count > 0);
    cy_err_t res = heartbeat_begin(cy);
    if (res == CY_OK) {
        pending_response_t* const pr = mem_alloc_zero(cy, sizeof(pending_response_t));
        if (pr == NULL) {
            res = CY_ERR_MEMORY;
        } else {
            const bool                  reliable = cb_delivery != NULL;
            const cy_feedback_context_t fb_ctx   = { .user = ctx_delivery, .fun = cb_delivery };
            res = pub->topic->vtable->publish(pub->topic, // ----------------------------
                                              tx_deadline,
                                              pub->priority,
                                              message,
                                              reliable ? &fb_ctx : NULL,
                                              &pr->transfer_id,
                                              pub->response_extent);
            if (res == CY_OK) {
                pr->deadline     = response_deadline;
                pr->topic        = pub->topic;
                pr->user_context = ctx_response;
                pr->callback     = cb_response;
                // The transfer-ID values returned by the transport layer are meant to be unique. This is trivially
                // ensured in most transports because they use 64-bit monotonically increasing sequence numbers.
                // However, Cyphal/CAN is special in that its transfer-ID space is only 5 bits wide, which will
                // cause the insertion operation to fail if there already are 31 pending requests. While this
                // is highly unlikely to actually happen in practice, we must still handle this case gracefully;
                // the solution is very simple -- finalize the old competed response early and replace it.
                while (true) {
                    pending_response_t* const pr2 =
                      CAVL2_TO_OWNER(cavl2_find_or_insert(&pub->topic->pending_responses_by_transfer_id,
                                                          &pr->transfer_id,
                                                          cavl_comp_pending_response_transfer_id,
                                                          &pr->index_transfer_id,
                                                          cavl2_trivial_factory),
                                     pending_response_t,
                                     index_transfer_id);
                    if (pr2 == pr) {
                        break; // Successfully inserted.
                    }
                    CY_TRACE(cy,
                             "⚠️ %s response transfer-ID exhaustion on #%llu",
                             topic_repr(pub->topic).str,
                             (unsigned long long)pr->transfer_id);
                    pending_response_finalize(pr2, BIG_BANG, message_empty);
                }
                (void)cavl2_find_or_insert(&cy->pending_responses_by_deadline,
                                           &pr->deadline,
                                           cavl_comp_pending_response_deadline,
                                           &pr->index_deadline,
                                           cavl2_trivial_factory);
                CY_TRACE(cy,
                         "📩 %s new pending response #%llu",
                         topic_repr(pr->topic).str,
                         (unsigned long long)pr->transfer_id);
            } else {
                mem_free(cy, pr);
            }
        }
    }
    return res;
}

static void retire_expired_pending_responses(const cy_t* cy, const cy_us_t now)
{
    pending_response_t* pr =
      CAVL2_TO_OWNER(cavl2_min(cy->pending_responses_by_deadline), pending_response_t, index_deadline);
    while ((pr != NULL) && (pr->deadline < now)) {
        pending_response_finalize(pr, BIG_BANG, message_empty);
        // We could have avoided the second min lookup by replacing this with a cavl2_next_greater(), but the problem
        // is that the user callback may modify the tree, and we don't want to put constraints on the callback behavior.
        // A more sophisticated solution is to mark the tree as modified, but it's not worth the effort.
        pr = CAVL2_TO_OWNER(cavl2_min(cy->pending_responses_by_deadline), pending_response_t, index_deadline);
    }
}

cy_prio_t cy_priority(const cy_publisher_t* const pub) { return (pub != NULL) ? pub->priority : cy_prio_nominal; }
void      cy_priority_set(cy_publisher_t* const pub, const cy_prio_t priority)
{
    if ((pub != NULL) && (((int)priority) < CY_PRIO_COUNT)) {
        pub->priority = priority;
    }
}

const cy_topic_t* cy_publisher_topic(const cy_publisher_t* const pub) { return (pub != NULL) ? pub->topic : NULL; }

void cy_unadvertise(cy_publisher_t* const pub) { (void)pub; }

// =====================================================================================================================
//                                                      SUBSCRIBER
// =====================================================================================================================

/// Returns non-NULL on OOM, which aborts the traversal early.
static void* wkv_cb_couple_new_subscription(const wkv_event_t evt)
{
    const cy_subscriber_t* const sub   = (cy_subscriber_t*)evt.context;
    cy_topic_t* const            topic = (cy_topic_t*)evt.node->value;
    assert((sub != NULL) && (topic != NULL));
    // Sample the old parameters before the new coupling is created to decide if we need to refresh the subscription.
    const subscriber_params_t param_old = topic->subscribed
                                            ? deduce_subscription_params(topic)
                                            : (subscriber_params_t){ .extent = 0, .reordering_window = BIG_BANG };
    const cy_err_t            res       = topic_couple(topic, sub->root, evt.substitution_count, evt.substitutions);
    if (res == CY_OK) {
        bool refresh_subscription = false;
        if (topic->subscribed) {
            const subscriber_params_t param_new = deduce_subscription_params(topic);
            // The resubscription decision heuristics are subject to refinement.
            refresh_subscription = (param_new.extent > param_old.extent) || //
                                   (param_new.reordering_window != param_old.reordering_window);
        }
        if (refresh_subscription) {
            CY_TRACE(topic->cy,
                     "🚧 %s subscription refresh params: extent=%zu rwin=%lld",
                     topic_repr(topic).str,
                     param_old.extent,
                     (long long)param_old.reordering_window);
            topic->vtable->unsubscribe(topic);
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

static cy_subscriber_t* subscribe(cy_t* const                    cy,
                                  const wkv_str_t                name,
                                  const subscriber_params_t      params,
                                  const cy_user_context_t        context,
                                  const cy_subscriber_callback_t callback)
{
    assert((cy != NULL) && (callback != NULL) && (params.reordering_window >= -1));
    char            name_buf[CY_TOPIC_NAME_MAX];
    const wkv_str_t resolved = cy_name_resolve(name, cy->ns, cy->home, sizeof(name_buf), name_buf);
    if (resolved.len > sizeof(name_buf)) {
        return NULL;
    }
    cy_subscriber_t* const sub = mem_alloc_zero(cy, sizeof(*sub));
    if (sub == NULL) {
        return NULL;
    }
    sub->params        = params;
    sub->user_context  = context;
    sub->callback      = callback;
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

cy_subscriber_t* cy_subscribe(cy_t* const                    cy,
                              const wkv_str_t                name,
                              const size_t                   extent,
                              const cy_user_context_t        context,
                              const cy_subscriber_callback_t callback)
{
    if ((cy != NULL) && (callback != NULL)) {
        const subscriber_params_t params = { .extent = extent, .reordering_window = -1 };
        return subscribe(cy, name, params, context, callback);
    }
    return NULL;
}

cy_subscriber_t* cy_subscribe_ordered(cy_t* const                    cy,
                                      const wkv_str_t                name,
                                      const size_t                   extent,
                                      const cy_us_t                  reordering_window,
                                      const cy_user_context_t        context,
                                      const cy_subscriber_callback_t callback)
{
    if ((cy != NULL) && (callback != NULL) && (reordering_window >= 0)) {
        const subscriber_params_t params = { .extent = extent, .reordering_window = reordering_window };
        return subscribe(cy, name, params, context, callback);
    }
    return NULL;
}

static void dummy_delivery_callback(const cy_user_context_t ctx, const uint16_t acknowledgements)
{
    (void)ctx;
    (void)acknowledgements;
}

cy_err_t cy_respond(const cy_responder_t         responder,
                    const cy_us_t                tx_deadline,
                    const cy_bytes_t             response_message,
                    const cy_user_context_t      ctx_delivery,
                    const cy_delivery_callback_t cb_delivery)
{
    if (tx_deadline < 0) {
        return CY_ERR_ARGUMENT;
    }
    const cy_err_t res = heartbeat_begin(responder.cy);
    if (res != CY_OK) {
        return res;
    }
    const cy_feedback_context_t fb_ctx = { .user = ctx_delivery,
                                           .fun  = (cb_delivery == NULL) ? dummy_delivery_callback : cb_delivery };
    return responder.vtable->respond(&responder, tx_deadline, response_message, fb_ctx);
}

void cy_subscriber_name(const cy_subscriber_t* const sub, char* const out_name)
{
    wkv_get_key(&sub->root->cy->subscribers_by_name, sub->root->index_name, out_name);
}

void cy_unsubscribe(cy_subscriber_t* const sub) { (void)sub; }

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

cy_err_t cy_new(cy_t* const              cy,
                const cy_vtable_t* const vtable,
                const wkv_str_t          home,
                const wkv_str_t          namespace_,
                const uint32_t           subject_id_modulus)
{
    if ((cy == NULL) || (vtable == NULL) || (subject_id_modulus < CY_SUBJECT_ID_MODULUS_16bit) ||
        !is_prime_u32(subject_id_modulus)) {
        return CY_ERR_ARGUMENT;
    }
    if (!cy_name_is_valid(home) || !cy_name_is_valid(namespace_) || (home.len > CY_NAMESPACE_NAME_MAX) ||
        (namespace_.len > CY_NAMESPACE_NAME_MAX)) {
        return CY_ERR_NAME;
    }
    memset(cy, 0, sizeof(*cy));
    cy->vtable             = vtable;
    cy->subject_id_modulus = subject_id_modulus;

    // Only home needs to be freed at destruction.
    char* const home_z = mem_alloc(cy, (home.len + 1) + (larger(namespace_.len, 1) + 1));
    if (home_z == NULL) {
        return CY_ERR_MEMORY;
    }
    memcpy(home_z, home.str, home.len);
    home_z[home.len] = '\0';
    cy->home         = (wkv_str_t){ .len = home.len, .str = home_z };
    char* const ns_z = &home_z[home.len + 1];
    if (namespace_.len > 0) {
        memcpy(ns_z, namespace_.str, namespace_.len);
        ns_z[namespace_.len] = '\0';
        cy->ns               = (wkv_str_t){ .len = namespace_.len, .str = ns_z };
    } else {
        ns_z[0] = '~';
        ns_z[1] = '\0';
        cy->ns  = (wkv_str_t){ .len = 1, .str = ns_z };
    }

    cy->topics_by_hash       = NULL;
    cy->topics_by_subject_id = NULL;
    cy->user                 = NULL;

    wkv_init(&cy->topics_by_name, &wkv_realloc);
    cy->topics_by_name.context = cy;

    wkv_init(&cy->subscribers_by_name, &wkv_realloc);
    cy->subscribers_by_name.context = cy;

    wkv_init(&cy->subscribers_by_pattern, &wkv_realloc);
    cy->subscribers_by_pattern.context = cy;

    // Postpone calling the functions until after the object is set up.
    cy->ts_started = cy_now(cy);

    // Initially, the heartbeat scheduling logic is disabled, because the first heartbeat is sent together with
    // the first publication. This allows listen-only nodes to avoid transmitting anything.
    cy->heartbeat_next        = HEAT_DEATH;
    cy->heartbeat_next_urgent = HEAT_DEATH;
    cy->heartbeat_period      = 3 * MEGA; // May be made configurable at some point if necessary.

    cy->implicit_topic_timeout = IMPLICIT_TOPIC_DEFAULT_TIMEOUT_us;

    // Pub/sub on the heartbeat topic.
    const wkv_str_t hb_name = wkv_key(CY_HEARTBEAT_TOPIC_NAME);
    cy->heartbeat_pub       = cy_advertise(cy, hb_name);
    if (cy->heartbeat_pub == NULL) {
        return CY_ERR_MEMORY;
    }
    assert(cy->heartbeat_pub->topic->hash == CY_HEARTBEAT_TOPIC_HASH);
    cy->heartbeat_sub = cy_subscribe(cy, hb_name, HEARTBEAT_SIZE_MAX, CY_USER_CONTEXT_EMPTY, &on_heartbeat);
    if (cy->heartbeat_sub == NULL) {
        cy_unadvertise(cy->heartbeat_pub);
        return CY_ERR_MEMORY;
    }
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

cy_err_t cy_update(cy_t* const cy)
{
    if (cy == NULL) {
        return CY_ERR_ARGUMENT;
    }
    const cy_us_t now = cy_now(cy);
    retire_expired_pending_responses(cy, now);
    retire_expired_implicit_topics(cy, now);
    return heartbeat_poll(cy, now);
}

void cy_on_topic_collision(cy_topic_t* const topic)
{
    if (topic != NULL) {
        CY_TRACE(topic->cy, "💥 %s", topic_repr(topic).str);
        schedule_gossip_urgent(topic);
    }
}

void cy_on_message(cy_topic_t* const    topic,
                   const cy_us_t        timestamp,
                   cy_message_t         message,
                   const cy_responder_t responder)
{
    assert((topic != NULL) && (timestamp >= 0) && (responder.cy != NULL) && (responder.cy == topic->cy));
    implicit_animate(topic, timestamp);
    const cy_topic_coupling_t* cpl   = topic->couplings;
    bool                       moved = false;
    // A callback may unsubscribe, so we have to store the next pointer early.
    // A topic has one or more couplings, one per subscription name: at most one verbatim and zero or more patterns.
    // Each coupling has one or more subscribers, all sharing the same subscription name and same subscriber root.
    while (cpl != NULL) {
        const cy_topic_coupling_t* const next_cpl = cpl->next;
        cy_subscriber_t*                 sub      = cpl->root->head;
        assert(sub != NULL);
        while (sub != NULL) {
            cy_subscriber_t* const next_sub = sub->next;
            assert(sub->callback != NULL);
            // Rebuild the struct before every callback because the callbacks are allowed to mutate it.
            // Most topics only have a single subscription so this is not too expensive in practice.
            cy_arrival_t arrival = {
                .message       = { .timestamp = timestamp, .content = message },
                .responder     = responder,
                .topic         = topic,
                .substitutions = { .count = cpl->substitution_count, .substitutions = cpl->substitutions },
            };
            sub->callback(sub->user_context, &arrival);
            if (cy_message_size(arrival.message.content) < cy_message_size(message)) {
                assert(!moved); // At most one handler can take ownership of the payload.
                moved = true;
            }
            sub = next_sub;
        }
        cpl = next_cpl;
    }
    if (!moved) {
        cy_message_destroy(&message);
    }
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
void cy_on_response(cy_t* const    cy,
                    const cy_us_t  timestamp,
                    const uint64_t topic_hash,
                    const uint64_t transfer_id,
                    cy_message_t   message)
{
    assert((cy != NULL) && (timestamp >= 0));
    const cy_topic_t* const topic = cy_topic_find_by_hash(cy, topic_hash);
    if (topic != NULL) {
        pending_response_t* const pr = CAVL2_TO_OWNER(
          cavl2_find(topic->pending_responses_by_transfer_id, &transfer_id, cavl_comp_pending_response_transfer_id),
          pending_response_t,
          index_transfer_id);
        if (pr != NULL) {
            pending_response_finalize(pr, timestamp, message); // Takes ownership of the message.
        } else {
            CY_TRACE(cy, "❓ %s orphan #%llu", topic_repr(topic).str, (unsigned long long)transfer_id);
            cy_message_destroy(&message); // Unexpected or duplicate response.
        }
    } else {
        CY_TRACE(cy, "❓ T%016llx no such topic", (unsigned long long)topic_hash);
        cy_message_destroy(&message); // The topic was destroyed while waiting for the response.
    }
}

void cy_on_message_feedback(cy_t* const cy, const cy_feedback_context_t context, const uint16_t acknowledgements)
{
    assert(cy != NULL);
    (void)cy; // Later we may want to add statistics.
    context.fun(context.user, acknowledgements);
}

void cy_on_response_feedback(cy_t* const cy, const cy_feedback_context_t context, const bool success)
{
    assert(cy != NULL);
    (void)cy; // Later we may want to add statistics.
    context.fun(context.user, success ? 1 : 0);
}

// =====================================================================================================================
//                                                      NAMES
// =====================================================================================================================

const char cy_name_sep  = '/';
const char cy_name_home = '~';

static const wkv_str_t str_invalid = { .len = SIZE_MAX, .str = NULL };

static bool is_valid_char(const char c) { return (c >= 32) && (c <= 126); }

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
    char* const       out_end     = dest + dest_size;
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
                          size_t          dest_size,
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
        namespace_.str = dest;
        dest_size -= namespace_.len;
        dest += namespace_.len;
    }
    return cy_name_join(namespace_, name, dest_size, dest);
}

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
wkv_str_t cy_u64_to_hex(const uint64_t value, char* const out) { return to_hex(value, 64U, out); }
wkv_str_t cy_u32_to_hex(const uint32_t value, char* const out) { return to_hex(value, 32U, out); }
wkv_str_t cy_u16_to_hex(const uint16_t value, char* const out) { return to_hex(value, 16U, out); }
wkv_str_t cy_u8_to_hex(const uint_fast8_t value, char* const out) { return to_hex(value, 8U, out); }
