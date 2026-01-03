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

#include "cy_platform.h"

#define CAVL2_RELATION int32_t
#define CAVL2_T        cy_tree_t
#include <cavl2.h>

#define RAPIDHASH_COMPACT // because we hash strings <96 bytes long
#include <rapidhash.h>

#include <assert.h>
#include <string.h>
#include <stdio.h> ///< TODO remove dependency on stdio.h! This is only for the name composition and easy to get rid of.

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

static size_t  larger(const size_t a, const size_t b) { return (a > b) ? a : b; }
static int64_t max_i64(const int64_t a, const int64_t b) { return (a > b) ? a : b; }
static int64_t min_i64(const int64_t a, const int64_t b) { return (a < b) ? a : b; }

/// Returns -1 if the argument is zero to allow linear comparison.
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

static uint64_t random_u64(cy_t* const cy) { return cy->vtable->random(cy); }

/// The limits are inclusive. Returns min unless min < max.
static int64_t random_int(cy_t* const cy, const int64_t min, const int64_t max)
{
    if (min < max) {
        return (int64_t)(random_u64(cy) % (uint64_t)(max - min)) + min;
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

static void mem_free(cy_t* const cy, void* ptr)
{
    if (ptr != NULL) {
        cy->vtable->realloc(cy, ptr, 0);
    }
}

/// Simply returns the value of the first hit. Useful for existence checks.
static void* wkv_cb_first(const wkv_event_t evt) { return evt.node->value; }

/// TODO this is ugly and dirty; use wkv_str_t
static bool resolve_name(const char* const ns, const char* const user, const char* const name, char* const destination)
{
    assert(ns != NULL);
    assert(name != NULL);
    assert(destination != NULL);
    // format a temporary representation
    char        tmp[CY_TOPIC_NAME_MAX + 10];
    const char* in = name;
    if (*in != '/') {
        const bool is_user = (*in == '~') || (*ns == '~');
        in += *in == '~';
        (void)snprintf(tmp, sizeof(tmp), "%s/%s", is_user ? user : ns, in);
    } else {
        (void)snprintf(tmp, sizeof(tmp), "%s", in);
    }
    // validate and canonicalize
    in         = tmp;
    char  prev = '/'; // remove leading slashes
    char* out  = destination;
    while (*in != '\0') {
        if ((in - tmp) > CY_TOPIC_NAME_MAX) {
            return false;
        }
        const char c = *in++;
        if (c == '/') {
            if (prev != '/') {
                *out++ = c;
            }
        } else {
            *out++ = c; // no such thing as invalid char, we accept everything at this level except multiple /.
        }
        prev = c;
    }
    if ((prev == '/') && (out != destination)) {
        out--; // remove trailing slash
    }
    *out = '\0';
    return destination != out; // empty name is not allowed
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
//                                                  AVL TREE UTILITIES
// =====================================================================================================================

static int32_t cavl_comp_topic_hash(const void* const user, const cy_tree_t* const node)
{
    assert((user != NULL) && (node != NULL));
    const uint64_t          outer = *(uint64_t*)user;
    const cy_topic_t* const inner = (const cy_topic_t*)node;
    if (outer == inner->hash) {
        return 0;
    }
    return (outer > inner->hash) ? +1 : -1;
}

static int32_t cavl_comp_topic_subject_id(const void* const user, const cy_tree_t* const node)
{
    assert((user != NULL) && (node != NULL));
    const uint32_t outer = *(const uint32_t*)user;
    const uint32_t inner = cy_topic_subject_id(CAVL2_TO_OWNER(node, cy_topic_t, index_subject_id));
    if (outer == inner) {
        return 0;
    }
    return (outer > inner) ? +1 : -1;
}

static int32_t cavl_comp_future_transfer_id(const void* const user, const cy_tree_t* const node)
{
    assert((user != NULL) && (node != NULL));
    const uint64_t           outer = *(uint64_t*)user;
    const cy_future_t* const inner = CAVL2_TO_OWNER(node, cy_future_t, index_transfer_id);
    if (outer == inner->transfer_id) {
        return 0;
    }
    return (outer >= inner->transfer_id) ? +1 : -1;
}

/// Deadlines are not unique, so this comparator never returns 0.
static int32_t cavl_comp_future_deadline(const void* const user, const cy_tree_t* const node)
{
    assert((user != NULL) && (node != NULL));
    const cy_future_t* const inner = CAVL2_TO_OWNER(node, cy_future_t, index_deadline);
    return ((*(cy_us_t*)user) >= inner->deadline) ? +1 : -1;
}

static cy_tree_t* cavl_factory_future_transfer_id(void* const user) { return &((cy_future_t*)user)->index_transfer_id; }
static cy_tree_t* cavl_factory_future_deadline(void* const user) { return &((cy_future_t*)user)->index_deadline; }
static cy_tree_t* cavl_factory_topic_subject_id(void* const user) { return &((cy_topic_t*)user)->index_subject_id; }

/// For debug invariant checking only; linear complexity.
static size_t cavl_count(cy_tree_t* const root)
{
    size_t count = 0;
    for (cy_tree_t* p = cavl2_min(root); p != NULL; p = cavl2_next_greater(p)) {
        count++;
    }
    return count;
}

// =====================================================================================================================
//                                                  MESSAGE BUFFER
// =====================================================================================================================

cy_message_t cy_message_move(cy_message_t* const msg)
{
    const cy_message_t ret = *msg;
    *msg                   = (cy_message_t){ .state = { NULL, NULL }, .size = 0, .vtable = NULL };
    return ret;
}

void cy_message_free(cy_message_t* const msg)
{
    if ((msg != NULL) && (msg->vtable != NULL) && (msg->vtable->free != NULL)) {
        msg->vtable->free(msg);
        (void)cy_message_move(msg);
    }
}

size_t cy_message_read(cy_message_t* const cursor, const size_t offset, const size_t size, void* const destination)
{
    if ((cursor != NULL) && (cursor->vtable != NULL) && (destination != NULL)) {
        return cursor->vtable->read(cursor, offset, size, destination);
    }
    return 0;
}

// =====================================================================================================================
//                                                  TOPIC UTILITIES
// =====================================================================================================================

/// For each topic we are subscribed to, there is a single subscriber root.
/// The application can create an arbitrary number of subscribers per topic, which all go under the same root.
/// If pattern subscriptions are used, a single root may match multiple topics; the matching is tracked using
/// the coupling objects.
typedef struct cy_subscriber_root_t
{
    wkv_node_t* index_name;
    wkv_node_t* index_pattern; ///< NULL if this is a verbatim subscriber.

    /// If this is a pattern subscriber, we will need to publish a scout message.
    /// The entry is delisted when it no longer requires publishing scout messages.
    cy_list_member_t list_scout_pending;

    cy_subscriber_t* head;
} cy_subscriber_root_t;

/// A single topic may match multiple subscribers if patterns are used.
/// Each instance holds a pointer to the corresponding subscriber root and a pointer to the next match for this topic.
typedef struct cy_topic_coupling_t
{
    cy_subscriber_root_t*       root;
    struct cy_topic_coupling_t* next;

    size_t            substitution_count;               ///< The size of the following substitutions flex array.
    cy_substitution_t substitutions[CY_TOPIC_NAME_MAX]; ///< Flex array.
} cy_topic_coupling_t;

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
static void implicit_retire_timed_out(cy_t* const cy, const cy_us_t now)
{
    cy_topic_t* const topic = LIST_TAIL(cy->list_implicit, cy_topic_t, list_implicit);
    if (topic != NULL) {
        assert(is_implicit(topic) && validate_is_implicit(topic));
        if ((topic->ts_animated + cy->implicit_topic_timeout) < now) {
            CY_TRACE(
              cy, "⚰️ T%016llx@%08x '%s'", (unsigned long long)topic->hash, cy_topic_subject_id(topic), topic->name);
            topic_destroy(topic);
        }
    }
}

static void schedule_gossip(cy_topic_t* const topic, const bool important)
{
    const bool eligible = important || (!is_pinned(topic->hash) && !is_implicit(topic));
    if (eligible) {
        // It is conceivable that large networks may encounter transient gossip storms when multiple nodes
        // trigger collisions on a topic in a short time window, forcing the local node to send multiple
        // urgent gossips on the same topic back-to-back. If this becomes a problem, we can store the last
        // gossip time per topic to throttle the gossiping rate here.
        if (important) {
            // TODO: don't do anything if it's already in the list!
            delist(&topic->cy->list_gossip, &topic->list_gossip);
            enlist_head(&topic->cy->list_gossip_urgent, &topic->list_gossip_urgent);
            CY_TRACE(topic->cy,
                     "⏰ T%016llx@%08x '%s'",
                     (unsigned long long)topic->hash,
                     cy_topic_subject_id(topic),
                     topic->name);
        } else {
            // TODO: don't do anything if it's already in the list!
            delist(&topic->cy->list_gossip_urgent, &topic->list_gossip_urgent);
            enlist_head(&topic->cy->list_gossip, &topic->list_gossip);
        }
    } else {
        delist(&topic->cy->list_gossip, &topic->list_gossip);
        delist(&topic->cy->list_gossip_urgent, &topic->list_gossip_urgent);
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
    assert(cy != NULL);
    cy_tree_t* const t = cavl2_find(cy->topics_by_subject_id, &subject_id, &cavl_comp_topic_subject_id);
    if (t == NULL) {
        return NULL;
    }
    cy_topic_t* topic = CAVL2_TO_OWNER(t, cy_topic_t, index_subject_id);
    assert(cy_topic_subject_id(topic) == subject_id);
    return topic;
}

/// This is linear complexity but we expect to have few subscribers per topic, so it is acceptable.
/// If this becomes a problem, we can simply store the subscription parameters in the topic fields.
static cy_subscription_params_t deduce_subscription_params(const cy_topic_t* const topic)
{
    cy_subscription_params_t out = { 0 };
    // Go over all couplings and all subscribers in each coupling.
    const cy_topic_coupling_t* cpl = topic->couplings;
    assert(cpl != NULL);
    while (cpl != NULL) {
        const cy_subscriber_t* sub = cpl->root->head;
        assert(sub != NULL);
        while (sub != NULL) {
            out.extent = larger(out.extent, sub->params.extent);
            sub        = sub->next;
        }
        cpl = cpl->next;
    }
    return out;
}

/// If a subscription is needed but is not active, this function will attempt to resubscribe.
/// Errors are handled via the platform handler, so from the caller's perspective this is infallible.
static void topic_ensure_subscribed(cy_topic_t* const topic)
{
    if ((topic->couplings != NULL) && (!topic->subscribed)) {
        const cy_subscription_params_t params = deduce_subscription_params(topic);
        const cy_err_t                 res    = topic->vtable->subscribe(topic, params);
        topic->subscribed                     = res == CY_OK;
        CY_TRACE(topic->cy,
                 "🗞️ T%016llx@%08x '%s' extent=%zu result=%d",
                 (unsigned long long)topic->hash,
                 cy_topic_subject_id(topic),
                 topic->name,
                 params.extent,
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
static void topic_allocate(cy_topic_t* const topic, const uint64_t new_evictions, const bool virgin, const cy_us_t now)
{
    cy_t* const cy = topic->cy;
    assert(cavl_count(cy->topics_by_hash) <= (cy->subject_id_modulus / 4));
#if CY_CONFIG_TRACE
    static const int         call_depth_indent = 2;
    static _Thread_local int call_depth        = 0U;
    call_depth++;
    CY_TRACE(cy,
             "🔍%*s T%016llx@%08x '%s' evict=%llu->%llu lage=%+d subscribed=%d couplings=%p",
             (call_depth - 1) * call_depth_indent,
             "",
             (unsigned long long)topic->hash,
             cy_topic_subject_id(topic),
             topic->name,
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
        topic->evictions       = new_evictions;
        cy_topic_t* const self = CAVL2_TO_OWNER(
          cavl2_find_or_insert(
            &cy->topics_by_subject_id, &new_sid, &cavl_comp_topic_subject_id, topic, &cavl_factory_topic_subject_id),
          cy_topic_t,
          index_subject_id);
        assert(self == topic);
        assert(!topic->subscribed);
        // Allocation done (end of the recursion chain), schedule gossip and resubscribe if needed.
        // If a resubscription failed in the past, we will retry here as long as there is at least one live subscriber.
        schedule_gossip(topic, true);
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
             "🔎%*s T%016llx@%08x '%s' evict=%llu lage=%+d subscribed=%d",
             (call_depth - 1) * call_depth_indent,
             "",
             (unsigned long long)topic->hash,
             cy_topic_subject_id(topic),
             topic->name,
             (unsigned long long)topic->evictions,
             topic_lage(topic, now),
             (int)topic->subscribed);
    assert(call_depth > 0);
    call_depth--;
#endif
}

/// UB if the topic under this name already exists.
/// out_topic may be new if the reference is not immediately needed (it can be found later via indexes).
/// The log-age is -1 for newly created topics, as opposed to auto-subscription on pattern match,
/// where the lage is taken from the gossip message.
static cy_err_t topic_new(cy_t* const        cy,
                          cy_topic_t** const out_topic,
                          const wkv_str_t    resolved_name,
                          const uint64_t     hash,
                          const uint64_t     evictions,
                          const int_fast8_t  lage)
{
    cy_topic_t* const topic = cy->vtable->new_topic(cy);
    if (topic == NULL) {
        return CY_ERR_MEMORY;
    }
    memset(topic, 0, sizeof(*topic));
    if ((resolved_name.len == 0) || (resolved_name.len > CY_TOPIC_NAME_MAX)) {
        goto bad_name;
    }
    memcpy(topic->name, resolved_name.str, resolved_name.len);
    topic->name[resolved_name.len] = '\0';

    const cy_us_t now = cy_now(cy);

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

    CY_TRACE(cy,
             "✨ T%016llx@%08x '%s': topic_count=%zu",
             (unsigned long long)topic->hash,
             cy_topic_subject_id(topic),
             topic->name,
             cavl_count(cy->topics_by_hash));
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
static cy_err_t topic_couple(cy_topic_t* const           topic,
                             cy_subscriber_root_t* const subr,
                             const size_t                substitution_count,
                             const wkv_substitution_t*   substitutions)
{
#if CY_CONFIG_TRACE
    char subr_name[CY_TOPIC_NAME_MAX + 1];
    wkv_get_key(&topic->cy->subscribers_by_name, subr->index_name, subr_name);
    CY_TRACE(topic->cy,
             "🔗 T%016llx@%08x '%s' <=> '%s' substitutions=%zu",
             (unsigned long long)topic->hash,
             cy_topic_subject_id(topic),
             topic->name,
             subr_name,
             substitution_count);
#endif
    // Allocate the new coupling object with the substitutions flex array.
    // Each topic keeps its own couplings because the sets of subscription names and topic names are orthogonal.
    cy_topic_coupling_t* const cpl = (cy_topic_coupling_t*)mem_alloc(
      topic->cy, offsetof(cy_topic_coupling_t, substitutions) + (substitution_count * sizeof(cy_substitution_t)));
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
            CY_TRACE(topic->cy,
                     "🧛 Promoted to explicit T%016llx@%08x '%s'",
                     (unsigned long long)topic->hash,
                     cy_topic_subject_id(topic),
                     topic->name);
        }
    }
    return (cpl == NULL) ? CY_ERR_MEMORY : CY_OK;
}

/// Returns non-NULL on OOM.
static void* wkv_cb_couple_new_topic(const wkv_event_t evt)
{
    cy_topic_t* const           topic = (cy_topic_t*)evt.context;
    cy_subscriber_root_t* const subr  = (cy_subscriber_root_t*)evt.node->value;
    const cy_err_t              res   = topic_couple(topic, subr, evt.substitution_count, evt.substitutions);
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
    CY_TRACE((cy_t*)evt.context,
             "📢 T%016llx@%08x '%s'",
             (unsigned long long)(topic->hash),
             cy_topic_subject_id(topic),
             topic->name);
    schedule_gossip(topic, true);
    return NULL;
}

// =====================================================================================================================
//                                                      HEARTBEAT
// =====================================================================================================================

/// We could have used Nunavut, but we only need a single message and it's very simple, so we do it manually.
typedef struct
{
    uint32_t uptime;
    uint8_t  user_word[3]; ///< Used to be: health, mode, vendor-specific status code. Now opaque user-defined 24 bits.
    uint8_t  version;      ///< Union tag; Cyphal v1.0 -- 0; Cyphal v1.1 -- 1.
    // The following fields are conditional on version=1.
    uint64_t topic_hash;
    uint32_t topic_evictions;
    uint8_t  topic_evictions_msb; ///< 40-bit continuation of topic_evictions.
    int8_t   topic_lage;          ///< floor(log2(topic_age)), where -1=floor(log2(0)), -2 if scout.
    uint8_t  _reserved_1_;
    uint8_t  topic_name_len;
    char     topic_name[CY_TOPIC_NAME_MAX + 1];
} heartbeat_t;

static cy_err_t publish_heartbeat(cy_t* const cy, const cy_us_t now, heartbeat_t* const message)
{
    // TODO proper serialization
    message->uptime           = (uint32_t)((now - cy->ts_started) / MEGA);
    message->version          = 1;
    const size_t message_size = offsetof(heartbeat_t, topic_name) + message->topic_name_len;
    assert(message_size <= sizeof(heartbeat_t));
    assert(message->topic_name_len <= CY_TOPIC_NAME_MAX);
    const cy_err_t res = cy->heartbeat_pub->topic->vtable->publish(
      &cy->heartbeat_pub, now + cy->heartbeat_period, (cy_bytes_t){ .size = message_size, .data = message }, false);
    cy->heartbeat_pub->topic->pub_transfer_id++;
    return res;
}

static cy_err_t publish_heartbeat_gossip(cy_t* const cy, cy_topic_t* const topic, const cy_us_t now)
{
    topic_ensure_subscribed(topic); // use this opportunity to repair the subscription if broken
    heartbeat_t msg = { .topic_hash          = topic->hash,
                        .topic_evictions     = topic->evictions & UINT32_MAX,
                        .topic_evictions_msb = (uint8_t)(topic->evictions >> 32U),
                        .topic_lage          = topic_lage(topic, now),
                        ._reserved_1_        = 0,
                        .topic_name_len      = (uint_fast8_t)topic->index_name->key_len };
    memcpy(msg.topic_name, topic->name, topic->index_name->key_len);
    CY_TRACE(cy, "🗣️ T%016llx@%08x '%s'", (unsigned long long)topic->hash, cy_topic_subject_id(topic), topic->name);
    // Update gossip even if failed so we don't get stuck publishing same gossip if error reporting is broken.
    schedule_gossip(topic, false);
    return publish_heartbeat(cy, now, &msg);
}

static cy_err_t publish_heartbeat_scout(cy_t* const cy, cy_subscriber_root_t* const subr, const cy_us_t now)
{
    assert(subr != NULL); // https://github.com/pavel-kirienko/cy/issues/12#issuecomment-2953184238
    heartbeat_t msg = { .topic_lage = LAGE_SCOUT, .topic_name_len = (uint_fast8_t)subr->index_name->key_len };
    wkv_get_key(&cy->subscribers_by_name, subr->index_name, msg.topic_name);
    const cy_err_t res = publish_heartbeat(cy, now, &msg);
    CY_TRACE(cy, "📢'%s' result=%d", msg.topic_name, res);
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
        cy_topic_t*                 topic = LIST_TAIL(cy->list_gossip_urgent, cy_topic_t, list_gossip_urgent);
        cy_subscriber_root_t* const scout = LIST_TAIL(cy->list_scout_pending, cy_subscriber_root_t, list_scout_pending);
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
static cy_err_t heartbeat_begin(cy_t* const cy)
{
    cy_err_t res = CY_OK;
    if (cy->heartbeat_next == HEAT_DEATH) {
        const cy_us_t now  = cy_now(cy);
        cy->heartbeat_next = now;
        res                = heartbeat_poll(cy, now);
    }
    return res;
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void on_heartbeat(cy_arrival_t* const evt)
{
    assert((evt->subscriber != NULL) && (evt->topic != NULL));
    cy_t* const cy = evt->topic->cy;
    // Deserialize the message. TODO: deserialize properly and check version.
    heartbeat_t  heartbeat = { 0 };
    const size_t msg_size  = cy_gather(&evt->payload, 0, sizeof(heartbeat), &heartbeat);
    if ((msg_size < offsetof(heartbeat_t, topic_name)) || (heartbeat.version != 1)) {
        return;
    }
    const cy_us_t     ts              = evt->timestamp;
    const uint64_t    other_hash      = heartbeat.topic_hash;
    const uint64_t    other_evictions = heartbeat.topic_evictions + (((uint64_t)heartbeat.topic_evictions_msb) << 32U);
    const int_fast8_t other_lage      = heartbeat.topic_lage;
    const wkv_str_t   key             = { .len = heartbeat.topic_name_len, .str = heartbeat.topic_name };
    //
    if (heartbeat.topic_lage >= -1) {
        // Find the topic in our local database. Create if there is a pattern match.
        cy_topic_t* mine = cy_topic_find_by_hash(cy, other_hash);
        if (mine == NULL) {
            mine = topic_subscribe_if_matching(cy, key, other_hash, other_evictions, other_lage);
        }
        if (mine != NULL) {               // We have this topic! Check if we have consensus on the subject-ID.
            schedule_gossip(mine, false); // suppress next gossip -- the network just heard about it
            implicit_animate(mine, ts);
            assert(mine->hash == other_hash);
            const int_fast8_t mine_lage = topic_lage(mine, ts);
            if (mine->evictions != other_evictions) {
                const bool win =
                  (mine_lage > other_lage) || ((mine_lage == other_lage) && (mine->evictions > other_evictions));
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
                         topic_subject_id(cy, other_hash, other_evictions),
                         (unsigned long long)other_evictions,
                         other_lage);
                if (win) {
                    // Critically, if we win, we ignore possible allocation collisions. Even if the remote sits on
                    // a subject-ID that is currently used by another topic that we have, which could even lose
                    // arbitration, we ignore it because the remote will have to move to catch up with us anyway,
                    // thus resolving the collision.
                    // See https://github.com/OpenCyphal-Garage/cy/issues/28 and AcceptGossip() in Core.tla.
                    assert(!is_pinned(mine->hash));
                    schedule_gossip(mine, true);
                } else {
                    assert((mine_lage <= other_lage) &&
                           ((mine_lage < other_lage) || (mine->evictions < other_evictions)));
                    assert(mine_lage <= other_lage);
                    topic_merge_lage(mine, ts, other_lage);
                    topic_allocate(mine, other_evictions, false, ts);
                    if (mine->evictions == other_evictions) { // perfect sync, lower the gossip priority
                        schedule_gossip(mine, false);
                    }
                }
            } else {
                topic_ensure_subscribed(mine); // use this opportunity to repair the subscription if broken
            }
            topic_merge_lage(mine, ts, other_lage);
        } else { // We don't know this topic; check for a subject-ID collision and do auto-subscription.
            mine = topic_find_by_subject_id(cy, topic_subject_id(cy, other_hash, other_evictions));
            if (mine == NULL) {
                return; // We are not using this subject-ID, no collision.
            }
            assert(cy_topic_subject_id(mine) == topic_subject_id(cy, other_hash, other_evictions));
            const bool win = left_wins(mine, ts, other_lage, other_hash);
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
                     (unsigned long long)other_hash,
                     topic_subject_id(cy, other_hash, other_evictions),
                     (unsigned long long)other_evictions,
                     other_lage,
                     heartbeat.topic_name);
            // We don't need to do anything if we won, but we need to announce to the network (in particular to the
            // infringing node) that we are using this subject-ID, so that the loser knows that it has to move.
            // If we lost, we need to gossip this topic ASAP as well because every other participant on this topic
            // will also move, but the trick is that the others could have settled on different subject-IDs.
            // Everyone needs to publish their own new allocation and then we will pick max subject-ID out of that.
            if (!win) {
                topic_allocate(mine, mine->evictions + 1U, false, ts);
            } else {
                assert(!is_pinned(mine->hash));
                schedule_gossip(mine, true);
            }
        }
    } else if (heartbeat.topic_lage == LAGE_SCOUT) {
        // A scout message is simply asking us to check if we have any matching topics, and gossip them ASAP if so.
        CY_TRACE(cy,
                 "📢 Scout: T%016llx evict=%llu lage=%+d '%s'",
                 (unsigned long long)other_hash,
                 (unsigned long long)other_evictions,
                 other_lage,
                 heartbeat.topic_name);
        (void)wkv_match(&cy->topics_by_name, key, cy, wkv_cb_topic_scout_response);
    } else {
        CY_TRACE(cy, "⚠️ Invalid heartbeat message version=%d: lage=%+d", (int)heartbeat.version, heartbeat.topic_lage);
    }
}

// =====================================================================================================================
//                                                      PUBLISHER
// =====================================================================================================================

static void futures_retire_timed_out(cy_t* cy, const cy_us_t now)
{
    cy_future_t* fut = (cy_future_t*)cavl2_min(cy->futures_by_deadline);
    while ((fut != NULL) && (fut->deadline < now)) {
        assert(fut->state == cy_future_pending);
        cavl2_remove(&cy->futures_by_deadline, &fut->index_deadline);
        cavl2_remove(&fut->publisher->topic->futures_by_transfer_id, &fut->index_transfer_id);
        fut->state = cy_future_timeout_response;
        if (fut->callback != NULL) {
            fut->callback(fut);
        }
        // We could have trivially avoided having to search the tree again by replacing this with a
        // cavl2_next_greater(), which is very efficient, but the problem here is that the user callback may modify
        // the tree unpredictably, and we don't want to put constraints on the callback behavior.
        // A more sophisticated solution is to mark the tree as modified, but it's not worth the effort.
        fut = (cy_future_t*)cavl2_min(cy->futures_by_deadline);
    }
}

cy_err_t cy_advertise(cy_t* const cy, cy_publisher_t* const pub, const wkv_str_t name, const size_t response_extent)
{
    assert((pub != NULL) && (cy != NULL));
    char name_buf[CY_TOPIC_NAME_MAX + 1U];
    if (!resolve_name(cy->namespace_, cy->name, name.str, name_buf)) {
        return CY_ERR_NAME;
    }
    const wkv_str_t resolved_name = wkv_key(name_buf);
    memset(pub, 0, sizeof(*pub));
    const cy_err_t res = topic_ensure(cy, &pub->topic, resolved_name);
    pub->priority      = cy_prio_nominal;
    pub->user          = NULL;
    if (res == CY_OK) {
        assert(pub->topic != NULL);
        pub->topic->pub_count++;
        delist(&cy->list_implicit, &pub->topic->list_implicit);
        pub->topic->vtable->advertise(pub->topic, response_extent + P2P_HEADER_BYTES);
        // We don't need to schedule gossip here because this is managed by topic_ensure et al.
    }
    CY_TRACE(cy,
             "✨ T%016llx@%08x '%s': topic_count=%zu pub_count=%zu res=%d",
             (unsigned long long)pub->topic->hash,
             cy_topic_subject_id(pub->topic),
             pub->topic->name,
             cavl_count(cy->topics_by_hash),
             pub->topic->pub_count,
             res);
    return res;
}

void cy_unadvertise(cy_publisher_t* const pub) { (void)pub; }

void cy_future_new(cy_future_t* const future, const cy_future_callback_t callback, void* const user)
{
    assert(future != NULL);
    memset(future, 0, sizeof(*future));
    future->state    = cy_future_fresh;
    future->callback = callback;
    future->user     = user;
}

cy_err_t cy_publish(cy_publisher_t* const pub,
                    const cy_us_t         tx_deadline,
                    const cy_bytes_t      payload,
                    const cy_us_t         response_deadline,
                    cy_future_t* const    future)
{
    assert(pub != NULL);
    cy_topic_t* const topic = pub->topic;
    assert(topic != NULL);
    assert(topic->pub_count > 0);

    cy_err_t res = heartbeat_begin(pub->topic->cy);
    if (res != CY_OK) {
        return res;
    }

    // Set up the response future first. If publication fails, we will have to undo it later.
    // The reason we can't do it afterward is that if the transport has a cyclic transfer-ID, insertion may fail if
    // we have exhausted the transfer-ID set.
    if (future != NULL) {
        future->index_deadline     = (cy_tree_t){ 0 };
        future->index_transfer_id  = (cy_tree_t){ 0 };
        future->publisher          = pub;
        future->state              = cy_future_pending;
        future->transfer_id        = topic->pub_transfer_id;
        future->deadline           = response_deadline;
        future->response_timestamp = BIG_BANG;
        future->response_payload   = (cy_scatter_t){ 0 };
        // NB: we don't touch the callback and the user pointer, as they are to be initialized by the user.
        const cy_tree_t* const tr = cavl2_find_or_insert(&topic->futures_by_transfer_id,
                                                         &future->transfer_id,
                                                         &cavl_comp_future_transfer_id,
                                                         future,
                                                         &cavl_factory_future_transfer_id);
        if (tr != &future->index_transfer_id) {
            return CY_ERR_CAPACITY;
        }
    }

    const bool ack_required = (future != NULL);
    res                     = pub->topic->vtable->publish(pub, tx_deadline, payload, ack_required);
    if (future != NULL) {
        if (res == CY_OK) {
            const cy_tree_t* const tr = cavl2_find_or_insert(&pub->topic->cy->futures_by_deadline,
                                                             &response_deadline,
                                                             &cavl_comp_future_deadline,
                                                             future,
                                                             &cavl_factory_future_deadline);
            assert(tr == &future->index_deadline);
        } else {
            cavl2_remove(&topic->futures_by_transfer_id, &future->index_transfer_id);
        }
    }

    topic->pub_transfer_id++;
    return res;
}

// =====================================================================================================================
//                                                      SUBSCRIBER
// =====================================================================================================================

/// Returns non-NULL on OOM, which aborts the traversal early.
static void* wkv_cb_couple_new_subscription(const wkv_event_t evt)
{
    const cy_subscriber_t* const sub   = (cy_subscriber_t*)evt.context;
    cy_topic_t* const            topic = (cy_topic_t*)evt.node->value;
    // If the new subscription parameters are different, we will need to resubscribe this topic.
    bool resubscribe = false;
    if (topic->subscribed) {
        const cy_subscription_params_t param_old = deduce_subscription_params(topic);
        const cy_subscription_params_t param_new = sub->params;
        resubscribe                              = (param_new.extent > param_old.extent);
    }
    // Create the coupling.
    const cy_err_t res = topic_couple(topic, sub->root, evt.substitution_count, evt.substitutions);
    // Refresh the subscription if needed. Due to the new coupling, the params are now different.
    if (res == CY_OK) {
        if (resubscribe) {
            topic->vtable->unsubscribe(topic);
            topic->subscribed = false;
        }
        topic_ensure_subscribed(topic);
    }
    return (CY_OK == res) ? NULL : "";
}

/// Either finds an existing subscriber root or creates a new one. NULL if OOM.
static cy_err_t ensure_subscriber_root(cy_t* const                  cy,
                                       const wkv_str_t              resolved_name,
                                       cy_subscriber_root_t** const out_root)
{
    assert((cy != NULL) && (resolved_name.str != NULL) && (resolved_name.len > 0U) && (out_root != NULL));

    // Find or allocate a tree node.
    wkv_node_t* const node = wkv_set(&cy->subscribers_by_name, resolved_name);
    if (node == NULL) {
        return CY_ERR_MEMORY;
    }

    // If exists, return as is.
    if (node->value != NULL) {
        *out_root = (cy_subscriber_root_t*)node->value;
        return CY_OK;
    }

    CY_TRACE(cy, "✨'%s'", resolved_name.str);

    // Otherwise, allocate a new root, if possible.
    node->value = mem_alloc(cy, sizeof(cy_subscriber_root_t));
    if (node->value == NULL) {
        wkv_del(&cy->subscribers_by_name, node);
        return CY_ERR_MEMORY;
    }
    cy_subscriber_root_t* const root = (cy_subscriber_root_t*)node->value;
    memset(root, 0, sizeof(*root));

    // Insert the new root into the indexes.
    const bool wc    = cy_has_substitution_tokens(resolved_name);
    root->index_name = node;
    if (wc) {
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

cy_err_t cy_subscribe(cy_t* const                    cy,
                      cy_subscriber_t* const         sub,
                      const wkv_str_t                name,
                      const cy_subscription_params_t params,
                      const cy_subscriber_callback_t callback)
{
    const bool rwin_ok = (params.reordering_window == CY_SUBSCRIPTION_REORDERING_WINDOW_UNORDERED) || //
                         (params.reordering_window >= 0);
    if ((sub == NULL) || (cy == NULL) || (callback == NULL) || !rwin_ok) {
        return CY_ERR_ARGUMENT;
    }
    char name_buf[CY_TOPIC_NAME_MAX + 1U];
    if (!resolve_name(cy->namespace_, cy->name, name.str, name_buf)) {
        return CY_ERR_NAME;
    }
    const wkv_str_t resolved_name = wkv_key(name_buf);
    (void)memset(sub, 0, sizeof(*sub));
    CY_TRACE(cy, "✨'%s' extent=%zu rwin=%lld", resolved_name.str, params.extent, (long long)params.reordering_window);
    const cy_err_t res = ensure_subscriber_root(cy, resolved_name, &sub->root);
    if (res != CY_OK) {
        return res;
    }
    assert(sub->root != NULL);
    sub->params     = params;
    sub->callback   = callback;
    sub->next       = sub->root->head;
    sub->root->head = sub;
    if (NULL != wkv_match(&cy->topics_by_name, resolved_name, sub, wkv_cb_couple_new_subscription)) {
        cy_unsubscribe(sub);
        return CY_ERR_MEMORY;
    }
    return CY_OK;
}

void cy_unsubscribe(cy_subscriber_t* const sub) { (void)sub; }

void cy_subscriber_name(const cy_subscriber_t* const sub, char* const out_name)
{
    wkv_get_key(&sub->cy->subscribers_by_name, sub->root->index_name, out_name);
}

cy_err_t cy_respond(cy_responder_t* const responder, const cy_us_t deadline, const cy_bytes_t payload)
{
    assert(responder != NULL);
    const cy_err_t res = heartbeat_begin(responder->cy);
    if (res != CY_OK) {
        return res;
    }
    return responder->vtable->respond(responder, deadline, payload);
}

// =====================================================================================================================
//                                                  NODE & TOPIC
// =====================================================================================================================

cy_us_t cy_now(const cy_t* const cy) { return cy->vtable->now(cy); }

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
    if (topic == NULL) {
        return NULL;
    }
    assert(topic->hash == hash);
    return topic;
}

cy_topic_t* cy_topic_iter_first(const cy_t* const cy) { return (cy_topic_t*)cavl2_min(cy->topics_by_hash); }
cy_topic_t* cy_topic_iter_next(cy_topic_t* const topic) { return (cy_topic_t*)cavl2_next_greater(&topic->index_hash); }

uint32_t cy_topic_subject_id(const cy_topic_t* const topic)
{
    return topic_subject_id(topic->cy, topic->hash, topic->evictions);
}

wkv_str_t cy_topic_name(const cy_topic_t* const topic)
{
    return (wkv_str_t){ .len = topic->index_name->key_len, .str = topic->name };
}

uint64_t cy_topic_hash(const cy_topic_t* const topic) { return topic->hash; }

bool cy_has_substitution_tokens(const wkv_str_t name)
{
    wkv_t kv;
    wkv_init(&kv, &wkv_realloc);
    return wkv_has_substitution_tokens(&kv, name);
}

bool cy_name_valid(const wkv_str_t name)
{
    if ((name.len == 0) || (name.str == NULL)) {
        return false;
    }
    return memchr(name.str, '\0', name.len) == NULL;
}

// =====================================================================================================================
//                                              PLATFORM LAYER INTERFACE
// =====================================================================================================================

cy_err_t cy_new(cy_t* const              cy,
                const cy_vtable_t* const vtable,
                const wkv_str_t          name,
                const wkv_str_t          namespace_,
                const uint32_t           subject_id_modulus)
{
    assert(cy != NULL);
    assert(subject_id_modulus > 1000);

    if ((namespace_.len > CY_NAMESPACE_NAME_MAX) || (name.len > CY_NAMESPACE_NAME_MAX) || (name.len == 0)) {
        return CY_ERR_NAME;
    }

    // Init the object.
    memset(cy, 0, sizeof(*cy));
    cy->vtable             = vtable;
    cy->subject_id_modulus = subject_id_modulus;
    // namespace
    if (namespace_.len > 0) {
        memcpy(cy->namespace_, namespace_.str, namespace_.len);
        cy->namespace_[namespace_.len] = '\0';
    } else {
        cy->namespace_[0] = '~';
        cy->namespace_[1] = '\0';
    }
    // node name
    memcpy(cy->name, name.str, name.len);
    cy->name[name.len] = '\0';

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
    const cy_us_t now = cy_now(cy);
    cy->ts_started    = now;

    cy->heartbeat_next        = HEAT_DEATH; // The first heartbeat is sent together with the first publication.
    cy->heartbeat_next_urgent = HEAT_DEATH;
    cy->heartbeat_period      = 3 * MEGA;

    cy->implicit_topic_timeout = IMPLICIT_TOPIC_DEFAULT_TIMEOUT_us;

    // Pub/sub on the heartbeat topic.
    cy_err_t res = cy_advertise_c(cy, &cy->heartbeat_pub, CY_HEARTBEAT_TOPIC_NAME, 0);
    if (res == CY_OK) {
        const cy_subscription_params_t hb_sub_params = {
            .extent            = sizeof(heartbeat_t),
            .reordering_window = CY_SUBSCRIPTION_REORDERING_WINDOW_UNORDERED,
        };
        res = cy_subscribe_c(cy, &cy->heartbeat_sub, CY_HEARTBEAT_TOPIC_NAME, hb_sub_params, &on_heartbeat);
        if (res != CY_OK) {
            cy_unadvertise(&cy->heartbeat_pub);
        }
    }
    return res;
}

void cy_ingest(cy_topic_t* const    topic,
               const cy_us_t        timestamp,
               const uint64_t       transfer_id,
               cy_scatter_t         payload,
               const cy_responder_t responder)
{
    assert(topic != NULL);
    implicit_animate(topic, timestamp);
    const cy_response_context_t response_context = { .cy          = topic->cy, //
                                                     .topic_hash  = topic->hash,
                                                     .transfer_id = transfer_id,
                                                     .responder   = responder };
    const cy_topic_coupling_t*  cpl              = topic->couplings;
    size_t                      move_count       = 0;
    // A callback may unsubscribe, so we have to store the next pointer early.
    while (cpl != NULL) {
        const cy_topic_coupling_t* const next_cpl = cpl->next;
        cy_subscriber_t*                 sub      = cpl->root->head;
        assert(sub != NULL);
        while (sub != NULL) {
            cy_subscriber_t* const next_sub = sub->next;
            cy_arrival_t           arrival  = { .timestamp          = timestamp,
                                                .payload            = payload,
                                                .response_context   = response_context,
                                                .subscriber         = sub,
                                                .topic              = topic,
                                                .substitution_count = cpl->substitution_count,
                                                .substitutions      = cpl->substitutions };
            sub->callback(&arrival);
            const bool handler_took_ownership = cy_scatter_size(arrival.payload) < cy_scatter_size(payload);
            if (handler_took_ownership) {
                assert(move_count == 0); // At most one handler can take ownership of the payload.
                move_count++;
            }
            sub = next_sub;
        }
        cpl = next_cpl;
    }
    if (move_count == 0) {
        cy_scatter_free(&payload);
    }
}

static void ingest_p2p_response(cy_t* const          cy,
                                cy_topic_t* const    topic,
                                const cy_us_t        timestamp,
                                const uint64_t       transfer_id,
                                const uint32_t       cookie,
                                cy_scatter_t         payload,
                                const cy_responder_t responder)
{
    // Find the matching pending response future -- log(N) lookup.
    cy_tree_t* const tr = cavl2_find(topic->futures_by_transfer_id, &transfer_id, &cavl_comp_future_transfer_id);
    if (tr == NULL) {
        cy_scatter_free(&payload);
        return; // Unexpected or duplicate response. TODO: Linger completed futures for multiple responses?
    }
    cy_future_t* const fut = CAVL2_TO_OWNER(tr, cy_future_t, index_transfer_id);
    assert(fut->state == cy_future_pending);

    // Finalize and retire the future.
    fut->state = cy_future_success;
    cy_scatter_free(&payload); // does nothing if already released
    fut->response_timestamp = timestamp;
    fut->response_payload   = cy_scatter_move(&payload);
    cavl2_remove(&cy->futures_by_deadline, &fut->index_deadline);
    cavl2_remove(&topic->futures_by_transfer_id, &fut->index_transfer_id);
    if (fut->callback != NULL) {
        fut->callback(fut);
    }

    (void)cookie;
    (void)responder;
}

cy_err_t cy_update(cy_t* const cy)
{
    const cy_us_t now = cy_now(cy);
    futures_retire_timed_out(cy, now);
    implicit_retire_timed_out(cy, now);
    return heartbeat_poll(cy, now);
}

void cy_notify_topic_collision(cy_topic_t* const topic)
{
    if (topic != NULL) {
        schedule_gossip(topic, true);
    }
}
