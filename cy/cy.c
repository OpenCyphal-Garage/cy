///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// This is just a PoC, a crude approximation of what it might look like when implemented properly.
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

// ReSharper disable CppDFATimeOver
#include "cy_platform.h"

#define CAVL2_RELATION int32_t
#define CAVL2_T        cy_tree_t
#include <cavl2.h>

#define RAPIDHASH_COMPACT // because we hash strings <96 bytes long
#include <rapidhash.h>

#include <assert.h>
#include <string.h>
#include <stdio.h> ///< TODO remove dependency on stdio.h! This is only for the name composition and easy to get rid of.

// =====================================================================================================================
//                                                      MISCELLANEOUS
// =====================================================================================================================

#define KILO 1000L
#define MEGA 1000000LL

/// The earliest and latest representable time in microseconds.
#define BIG_BANG   INT64_MIN
#define HEAT_DEATH INT64_MAX

/// A special log-age value that indicates that the gossip is a scout message (pattern match request).
#define LAGE_SCOUT (-2)

#define HEARTBEAT_PUB_TIMEOUT_us (1 * MEGA)

/// A topic created based on a pattern subscription will be deleted after it's been idle for this long.
/// Here, "idle" means no messages received from this topic and no gossips seen on the network.
/// Topics created explicitly by the application (without substitution tokens) are not affected by this timeout.
#define IMPLICIT_TOPIC_DEFAULT_TIMEOUT_us (3600 * MEGA)

/// P2P exchanges (acks, RPC responses) have a fixed header size before the payload.
#define P2P_HEADER_BYTES 24U

enum p2p_kind
{
    p2p_kind_ack_message  = 0,
    p2p_kind_ack_response = 1,
    p2p_kind_response     = 2,
};

// clang-format off
static   size_t smaller(const size_t a,   const size_t b)   { return (a < b) ? a : b; }
static   size_t  larger(const size_t a,   const size_t b)   { return (a > b) ? a : b; }
static  int64_t max_i64(const int64_t a,  const int64_t b)  { return (a > b) ? a : b; }
static  int64_t min_i64(const int64_t a,  const int64_t b)  { return (a < b) ? a : b; }
// clang-format on

/// Returns -1 if the argument is zero to allow linear comparison.
static int_fast8_t log2_floor(const uint64_t x)
{
    return (int_fast8_t)((x == 0) ? -1 : (63 - __builtin_clzll(x)));
}

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

static uint64_t random_u64(const cy_t* const cy)
{
    const uint64_t seed[2] = { cy->platform->prng(cy), cy->uid };
    return rapidhash(seed, sizeof(seed));
}

/// The limits are inclusive. Returns min unless min < max.
static uint64_t random_uint(const cy_t* const cy, const uint64_t min, const uint64_t max)
{
    if (min < max) {
        return (random_u64(cy) % (max - min)) + min;
    }
    return min;
}
static int64_t random_int(const cy_t* const cy, const int64_t min, const int64_t max)
{
    if (min < max) {
        return (int64_t)(random_u64(cy) % (uint64_t)(max - min)) + min;
    }
    return min;
}
static int64_t dither_int(const cy_t* const cy, const int64_t mean, const int64_t deviation)
{
    return mean + random_int(cy, -deviation, +deviation);
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void* wkv_realloc(wkv_t* const self, void* ptr, const size_t new_size)
{
    return ((cy_t*)self->context)->platform->realloc((cy_t*)self->context, ptr, new_size);
}

static void* mem_alloc(cy_t* const cy, const size_t size)
{
    return cy->platform->realloc(cy, NULL, size);
}

static void mem_free(cy_t* const cy, void* ptr)
{
    if (ptr != NULL) {
        cy->platform->realloc(cy, ptr, 0);
    }
}

/// Simply returns the value of the first hit. Useful for existence checks.
static void* wkv_cb_first(const wkv_event_t evt)
{
    return evt.node->value;
}

// =====================================================================================================================
//                                                      NAMES
// =====================================================================================================================

/// TODO this is ugly and dirty
/// TODO use wkv_str_t
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

#define LIST_MEMBER(ptr, owner_type, owner_field) ((owner_type*)unbias_ptr((ptr), offsetof(owner_type, owner_field)))
static void* unbias_ptr(const void* const ptr, const size_t offset)
{
    return (ptr == NULL) ? NULL : (void*)((char*)ptr - offset);
}

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
    return (outer >= inner->hash) ? +1 : -1;
}

static int32_t cavl_comp_topic_subject_id(const void* const user, const cy_tree_t* const node)
{
    assert((user != NULL) && (node != NULL));
    const cy_topic_t* const inner = CAVL2_TO_OWNER(node, cy_topic_t, index_subject_id);
    return (int32_t)(*(uint16_t*)user) - ((int32_t)cy_topic_subject_id(inner));
}

static int32_t cavl_comp_future_transfer_id_masked(const void* const user, const cy_tree_t* const node)
{
    assert((user != NULL) && (node != NULL));
    const uint64_t           outer = *(uint64_t*)user;
    const cy_future_t* const inner = CAVL2_TO_OWNER(node, cy_future_t, index_transfer_id);
    if (outer == inner->transfer_id_masked) {
        return 0;
    }
    return (outer >= inner->transfer_id_masked) ? +1 : -1;
}

/// Deadlines are not unique, so this comparator never returns 0.
static int32_t cavl_comp_future_deadline(const void* const user, const cy_tree_t* const node)
{
    assert((user != NULL) && (node != NULL));
    const cy_future_t* const inner = CAVL2_TO_OWNER(node, cy_future_t, index_deadline);
    return ((*(cy_us_t*)user) >= inner->deadline) ? +1 : -1;
}

static cy_tree_t* cavl_factory_future_transfer_id(void* const user)
{
    return &((cy_future_t*)user)->index_transfer_id;
}

static cy_tree_t* cavl_factory_future_deadline(void* const user)
{
    return &((cy_future_t*)user)->index_deadline;
}

static cy_tree_t* cavl_factory_topic_subject_id(void* const user)
{
    return &((cy_topic_t*)user)->index_subject_id;
}

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
//                                                  NODE ID ALLOCATION
// =====================================================================================================================

// ReSharper disable CppParameterMayBeConstPtrOrRef

/// A Bloom filter is a set-only structure so there is no way to clear a bit after it has been set.
/// It is only possible to purge the entire filter state.
static void bloom64_set(cy_bloom64_t* const bloom, const size_t value)
{
    assert(bloom != NULL);
    const size_t   index = value % bloom->n_bits;
    const uint64_t mask  = 1ULL << (index % 64U);
    if ((bloom->storage[index / 64U] & mask) == 0) {
        bloom->storage[index / 64U] |= mask;
        bloom->popcount++;
    }
    assert(bloom->popcount <= bloom->n_bits);
}

static bool bloom64_get(const cy_bloom64_t* const bloom, const size_t value)
{
    assert(bloom != NULL);
    const size_t index = value % bloom->n_bits;
    return (bloom->storage[index / 64U] & (1ULL << (index % 64U))) != 0;
}

static void bloom64_purge(cy_bloom64_t* const bloom)
{
    assert(bloom != NULL);
    for (size_t i = 0; i < (bloom->n_bits + 63U) / 64U; i++) { // dear compiler please unroll this
        bloom->storage[i] = 0U; // I suppose this is better than memset cuz we're aligned to 64 bits.
    }
    bloom->popcount = 0U;
}

/// This is guaranteed to return a valid node-ID. If the Bloom filter is not full, an unoccupied node-ID will be
/// chosen, and the corresponding entry in the filter will be set. If the filter is full, a random node-ID will be
/// chosen, which can only happen if more than filter capacity nodes are currently online.
/// The complexity is constant, independent of the filter occupancy.
///
/// In the future we could replace this with a deterministic algorithm that chooses the node-ID based on the UID
/// and a nonce. Perhaps it could be simply SplitMix64 seeded with the UID?
///
/// The Spec says that node-ID 126 and 127 are reserved for diagnostic tools. We ignore this reservation here
/// because there doesn't seem to be a good way to enforce it without degrading into a linear search,
/// or increasing the complexity of the choosing algorithm significantly. The naive approach where we simply mark
/// the corresponding Bloom filter entries as taken is too wasteful because it wipes out not only the reserved
/// IDs, but all other IDs that map to the same Bloom filter bits. In CAN networks, the transport glue library can
/// simply limit the node-ID allocation range to [0, 125], and thus ensure the reserved IDs are not used;
/// all other transports that use much wider node-ID range (which is [0, 65534]) can just disregard the reservation
/// because the likelihood of picking the reserved IDs is negligible, and the consequences of doing so are very minor.
static uint16_t pick_node_id(const cy_t* const cy, cy_bloom64_t* const bloom, const uint16_t node_id_max)
{
    // The algorithm is hierarchical: find a 64-bit word that has at least one zero bit, then find a zero bit in it.
    // This somewhat undermines the randomness of the result, but it is always fast.
    const size_t num_words  = (smaller(node_id_max, bloom->n_bits) + 63U) / 64U;
    size_t       word_index = (size_t)random_uint(cy, 0U, num_words - 1U);
    for (size_t i = 0; i < num_words; i++) {
        if (bloom->storage[word_index] != UINT64_MAX) {
            break;
        }
        word_index = (word_index + 1U) % num_words;
    }
    const uint64_t word = bloom->storage[word_index];
    if (word == UINT64_MAX) {
        return (uint16_t)random_uint(cy, 0U, node_id_max); // The filter is full, fallback to random node-ID.
    }

    // Now we have a word with at least one zero bit. Find a random zero bit in it.
    uint_fast8_t bit_index = (uint_fast8_t)random_uint(cy, 0U, 63U);
    assert(word != UINT64_MAX);
    while ((word & (1ULL << bit_index)) != 0) { // guaranteed to terminate, see above.
        bit_index = (bit_index + 1U) % 64U;
    }

    // Now we have some valid free node-ID. Recall that the Bloom filter maps multiple values to the same bit.
    // This means that we can increase randomness by incrementing the node-ID by a multiple of the Bloom filter period.
    size_t node_id = (word_index * 64U) + bit_index;
    assert(node_id < node_id_max);
    assert(bloom64_get(bloom, node_id) == false);
    node_id += (size_t)random_uint(cy, 0, node_id_max / bloom->n_bits) * bloom->n_bits;
    // TODO FIXME ensure we don't exceed node_id_max -- decrement until free?
    assert(node_id < node_id_max);
    assert(bloom64_get(bloom, node_id) == false);
    bloom64_set(bloom, node_id);
    return (uint16_t)node_id;
}

// ReSharper restore CppParameterMayBeConstPtrOrRef

/// If the local node still has no node-ID, this function will allocate one on the spot.
/// May fail if the underlying platform->node_id_set() fails.
static cy_err_t ensure_joined(cy_t* const cy)
{
    cy_err_t res = CY_OK;
    if (cy->node_id >= cy->platform->node_id_max) {
        cy_bloom64_t* const bloom = cy->platform->node_id_bloom(cy);
        assert((bloom != NULL) && (bloom->n_bits > 0) && ((bloom->n_bits % 64) == 0) &&
               (bloom->popcount <= bloom->n_bits));
        cy->node_id = pick_node_id(cy, bloom, cy->platform->node_id_max);
        assert(cy->node_id <= cy->platform->node_id_max);
        res = cy->platform->node_id_set(cy);
        if (res == CY_OK) {
            CY_TRACE(cy, "☝️ Picked own node-ID %04x; bloom popcount %zu", cy->node_id, bloom->popcount);
        } else {
            CY_TRACE(cy, "☝️ Failed to set node-ID %04x with error %d; purge bloom to retry later", cy->node_id, res);
            cy->node_id = cy->platform->node_id_max;
            bloom64_purge(bloom);
        }
    }
    return res;
}

// =====================================================================================================================
//                                                  TOPIC UTILITIES
// =====================================================================================================================

typedef struct cy_subscriber_root_t
{
    wkv_node_t* index_name;
    wkv_node_t* index_pattern; ///< NULL if this is a verbatim subscriber.

    /// If this is a pattern subscriber, we will need to publish a scout message.
    struct cy_subscriber_root_t* next_scout;

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

static void topic_destroy(cy_t* const cy, cy_topic_t* const topic)
{
    assert(cy != NULL);
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
    topic->ts_origin = min_i64(topic->ts_origin, now - pow2us(r_lage));
}

/// Pinned topic names are canonical, which ensures that one pinned topic cannot collide with another.
static bool is_pinned(const uint64_t hash)
{
    return hash < CY_TOTAL_SUBJECT_COUNT;
}

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

static bool is_implicit(const cy_t* const cy, const cy_topic_t* const topic)
{
    return is_listed(&cy->list_implicit, &topic->list_implicit);
}

/// Move the topic to the head of the doubly-linked list of implicit topics.
/// The oldest implicit topic will be eventually pushed to the tail of the list.
static void implicit_animate(cy_t* const cy, cy_topic_t* const topic, const cy_us_t now)
{
    topic->ts_animated = now;
    if (is_implicit(cy, topic)) {
        enlist_head(&cy->list_implicit, &topic->list_implicit); // move to the head of the list
    }
}

/// Retires at most one at every call.
static void implicit_retire_timed_out(cy_t* const cy, const cy_us_t now)
{
    cy_topic_t* const topic = LIST_MEMBER(cy->list_implicit.tail, cy_topic_t, list_implicit);
    if (topic != NULL) {
        assert(is_implicit(cy, topic) && validate_is_implicit(topic));
        if ((topic->ts_animated + cy->implicit_topic_timeout) < now) {
            CY_TRACE(
              cy, "⚰️'%s' #%016llx @%04x", topic->name, (unsigned long long)topic->hash, cy_topic_subject_id(topic));
            topic_destroy(cy, topic);
        }
    }
}

static void schedule_gossip(cy_t* const cy, cy_topic_t* const topic, const bool important)
{
    const bool eligible = important || (!is_pinned(topic->hash) && !is_implicit(cy, topic));
    if (eligible) {
        if (important) {
            delist(&cy->list_gossip, &topic->list_gossip);
            enlist_head(&cy->list_gossip_urgent, &topic->list_gossip_urgent);
            CY_TRACE(
              cy, "⚖️'%s' #%016llx @%04x", topic->name, (unsigned long long)topic->hash, cy_topic_subject_id(topic));
        } else {
            delist(&cy->list_gossip_urgent, &topic->list_gossip_urgent);
            enlist_head(&cy->list_gossip, &topic->list_gossip);
        }
    } else {
        delist(&cy->list_gossip, &topic->list_gossip);
        delist(&cy->list_gossip_urgent, &topic->list_gossip_urgent);
    }
}

/// Returns UINT32_MAX if the string is not a valid pinned subject-ID form. A valid form is: "@/1234".
/// Pinned topic names must have only canonical names to ensure that no two topic names map to the same subject-ID.
/// The only requirement to ensure this is that there must be no leading zeros in the number.
static uint32_t parse_pinned(const wkv_str_t s)
{
    if ((s.len < 3) || (s.len > 6) || (s.str[0] != '@') || (s.str[1] != '/') || (s.str[2] == '0')) {
        return UINT32_MAX; // Leading zeroes not accepted; only canonical form.
    }
    uint32_t out = 0U;
    for (size_t i = 2; i < s.len; i++) {
        if ((s.str[i] < '0') || (s.str[i] > '9')) {
            return UINT32_MAX;
        }
        out = (out * 10U) + (uint_fast8_t)(s.str[i] - '0');
    }
    return (out < CY_TOTAL_SUBJECT_COUNT) ? out : UINT32_MAX;
}

/// The topic hash is the key component of the protocol.
/// For pinned topics, hash<CY_TOTAL_SUBJECT_COUNT.
/// The probability of a random hash falling into the pinned range is ~4.44e-16, or about one in two quadrillion.
static uint64_t topic_hash(const wkv_str_t name)
{
    uint64_t hash = parse_pinned(name);
    if (hash >= CY_TOTAL_SUBJECT_COUNT) {
        hash = rapidhash(name.str, name.len);
    }
    return hash;
}

static uint16_t topic_subject_id(const uint64_t hash, const uint64_t evictions)
{
    if (is_pinned(hash)) {
        return (uint16_t)hash; // Pinned topics may exceed CY_TOPIC_SUBJECT_COUNT.
    }
#ifndef CY_CONFIG_PREFERRED_TOPIC_OVERRIDE
    return (uint16_t)((hash + evictions) % CY_TOPIC_SUBJECT_COUNT);
#else
    return (uint16_t)((CY_CONFIG_PREFERRED_TOPIC_OVERRIDE + evictions) % CY_TOPIC_SUBJECT_COUNT);
#endif
}

/// This will only search through topics that have auto-assigned subject-IDs;
/// i.e., pinned topics will not be found by this function.
static cy_topic_t* topic_find_by_subject_id(const cy_t* const cy, const uint16_t subject_id)
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
    cy_subscription_params_t out = { 0, 0 };
    // Go over all couplings and all subscribers in each coupling.
    const cy_topic_coupling_t* cpl = topic->couplings;
    assert(cpl != NULL);
    while (cpl != NULL) {
        const cy_subscriber_t* sub = cpl->root->head;
        assert(sub != NULL);
        while (sub != NULL) {
            out.extent              = larger(out.extent, sub->params.extent);
            out.transfer_id_timeout = max_i64(out.transfer_id_timeout, sub->params.transfer_id_timeout);
            sub                     = sub->next;
        }
        cpl = cpl->next;
    }
    return out;
}

/// If a subscription is needed but is not active, this function will attempt to resubscribe.
/// Errors are handled via the platform handler, so from the caller's perspective this is infallible.
static void topic_ensure_subscribed(cy_t* const cy, cy_topic_t* const topic)
{
    if ((topic->couplings != NULL) && (!topic->subscribed)) {
        const cy_subscription_params_t params = deduce_subscription_params(topic);
        const cy_err_t                 res    = cy->platform->topic_subscribe(cy, topic, params);
        topic->subscribed                     = res == CY_OK;
        CY_TRACE(cy,
                 "🗞️'%s' #%016llx @%04x extent=%zu tid_timeout=%lld result=%d",
                 topic->name,
                 (unsigned long long)topic->hash,
                 cy_topic_subject_id(topic),
                 params.extent,
                 (long long)params.transfer_id_timeout,
                 res);
        if (!topic->subscribed) {
            cy->platform->topic_on_subscription_error(cy, topic, res); // not our problem anymore
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
static void topic_allocate(cy_t* const       cy, // NOLINT(*-no-recursion)
                           cy_topic_t* const topic,
                           const uint64_t    new_evictions,
                           const bool        virgin,
                           const cy_us_t     now)
{
    assert(cavl_count(cy->topics_by_hash) <= CY_TOPIC_SUBJECT_COUNT); // There is certain to be a free subject-ID!

    // Consider extracting everything prior to the loop into topic_allocate_prologue() and everything after the loop
    // into topic_allocate_epilogue() to focus on the main logic.
    static const int         call_depth_indent = 2;
    static _Thread_local int call_depth        = 0U;
    call_depth++;
    CY_TRACE(cy,
             "🔜%*s'%s' #%016llx @%04x evict=%llu->%llu lage=%+d subscribed=%d couplings=%p",
             (call_depth - 1) * call_depth_indent,
             "",
             topic->name,
             (unsigned long long)topic->hash,
             cy_topic_subject_id(topic),
             (unsigned long long)topic->evictions,
             (unsigned long long)new_evictions,
             topic_lage(topic, now),
             (int)topic->subscribed,
             (void*)topic->couplings);

    // We need to make sure no underlying resources are sitting on this topic before we move it.
    // Otherwise, changing the subject-ID field on the go may break something underneath.
    if (topic->subscribed) {
        assert(topic->couplings != NULL);
        cy->platform->topic_unsubscribe(cy, topic);
        topic->subscribed = false;
    }

    // We're not allowed to alter the eviction counter as long as the topic remains in the tree! So we remove it first.
    if (!virgin) {
        cavl2_remove(&cy->topics_by_subject_id, &topic->index_subject_id);
    }

    // Find a free slot. Every time we find an occupied slot, we have to arbitrate against its current tenant.
    // Note that it is possible that (hash+old_evictions)%6144 == (hash+new_evictions)%6144, which means that we
    // stay with the same subject-ID. No special case is required for this, we handle this normally.
    topic->evictions  = new_evictions;
    size_t iter_count = 0;
    while (true) {
        iter_count++;
        const uint16_t   sid = topic_subject_id(topic->hash, topic->evictions);
        cy_tree_t* const t   = cavl2_find_or_insert(
          &cy->topics_by_subject_id, &sid, &cavl_comp_topic_subject_id, topic, &cavl_factory_topic_subject_id);
        assert(t != NULL); // we will create it if not found, meaning allocation succeeded
        if (t == &topic->index_subject_id) {
            break; // Done!
        }
        // Someone else is sitting on that subject-ID. We need to arbitrate.
        cy_topic_t* const other = CAVL2_TO_OWNER(t, cy_topic_t, index_subject_id);
        assert(topic->hash != other->hash); // This would mean that we inserted the same topic twice, impossible
        if (left_wins(topic, now, topic_lage(other, now), other->hash)) {
            // This is our slot now! The other topic has to move.
            // This can trigger a chain reaction that in the worst case can leave no topic unturned.
            // One issue is that the worst-case recursive call depth equals the number of topics in the system.
            topic_allocate(cy, other, other->evictions + 1U, false, now);
            // Remember that we're still out of tree at the moment. We pushed the other topic out of its slot,
            // but it is possible that there was a chain reaction that caused someone else to occupy this slot.
            // Since that someone else was ultimately pushed out by the topic that just lost arbitration to us,
            // we know that the new squatter will lose arbitration to us again.
            // We will handle it in the exact same way on the next iteration, so we just continue with the loop.
            // Now, moving that one could also cause a chain reaction, but we know that eventually we will run
            // out of low-rank topics to move and will succeed.
        } else {
            topic->evictions++; // We lost arbitration, keep looking.
        }
    }

    // Whenever we alter a topic, we need to make sure that everyone knows about it.
    // Recursively we can alter a lot of topics like this.
    schedule_gossip(cy, topic, true);

    // If a subscription is needed, restore it. Notice that if this call failed in the past, we will retry here
    // as long as there is at least one live subscriber.
    assert(!topic->subscribed);
    topic_ensure_subscribed(cy, topic);

    CY_TRACE(cy,
             "🔚%*s'%s' #%016llx @%04x evict=%llu lage=%+d subscribed=%d iters=%zu",
             (call_depth - 1) * call_depth_indent,
             "",
             topic->name,
             (unsigned long long)topic->hash,
             cy_topic_subject_id(topic),
             (unsigned long long)topic->evictions,
             topic_lage(topic, now),
             (int)topic->subscribed,
             iter_count);
    assert(call_depth > 0);
    call_depth--;
}

/// UB if the topic under this name already exists.
/// out_topic may be new if the reference is not immediately needed (it can be found later via indexes).
static cy_err_t topic_new(cy_t* const        cy,
                          cy_topic_t** const out_topic,
                          const wkv_str_t    resolved_name,
                          const uint64_t     hash,
                          const uint64_t     evictions)
{
    cy_topic_t* const topic = cy->platform->topic_new(cy);
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

    topic->ts_origin   = now;
    topic->ts_animated = now;

    topic->pub_transfer_id = random_u64(cy); // https://forum.opencyphal.org/t/improve-the-transfer-id-timeout/2375
    topic->pub_count       = 0;

    topic->couplings  = NULL;
    topic->subscribed = false;

    if (cavl_count(cy->topics_by_hash) >= CY_TOPIC_SUBJECT_COUNT) {
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
        topic_allocate(cy, topic, 0, true, now);
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
             "✨'%s' #%016llx @%04x: topic_count=%zu",
             topic->name,
             (unsigned long long)topic->hash,
             cy_topic_subject_id(topic),
             cavl_count(cy->topics_by_hash));
    return 0;

oom: // TODO correct deinitialization
    cy->platform->topic_destroy(cy, topic);
    return CY_ERR_NAME;

bad_name: // TODO correct deinitialization
    cy->platform->topic_destroy(cy, topic);
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
    return topic_new(cy, out_topic, resolved_name, topic_hash(resolved_name), 0);
}

/// Create a new coupling between a topic and a subscriber.
/// Allocates new memory for the coupling, which may fail.
/// Don't forget topic_ensure_subscribed() afterward if necessary.
/// The substitutions must not lose validity until the topic is destroyed.
static cy_err_t topic_couple(cy_t* const                 cy,
                             cy_topic_t* const           topic,
                             cy_subscriber_root_t* const subr,
                             const size_t                substitution_count,
                             const wkv_substitution_t*   substitutions)
{
#if CY_CONFIG_TRACE
    char subr_name[CY_TOPIC_NAME_MAX + 1];
    wkv_get_key(&cy->subscribers_by_name, subr->index_name, subr_name);
    CY_TRACE(cy,
             "🔗'%s' #%016llx @%04x <=> '%s' substitutions=%zu",
             topic->name,
             (unsigned long long)topic->hash,
             cy_topic_subject_id(topic),
             subr_name,
             substitution_count);
#endif
    // Allocate the new coupling object with the substitutions flex array.
    // Each topic keeps its own couplings because the sets of subscription names and topic names are orthogonal.
    cy_topic_coupling_t* const cpl = (cy_topic_coupling_t*)mem_alloc(
      cy, offsetof(cy_topic_coupling_t, substitutions) + (substitution_count * sizeof(cy_substitution_t)));
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
        if ((subr->index_pattern == NULL) && is_implicit(cy, topic)) {
            delist(&cy->list_implicit, &topic->list_implicit);
            CY_TRACE(cy,
                     "🧛 Promoted to explicit '%s' #%016llx @%04x",
                     topic->name,
                     (unsigned long long)topic->hash,
                     cy_topic_subject_id(topic));
        }
    }
    return (cpl == NULL) ? CY_ERR_MEMORY : CY_OK;
}

/// Returns non-NULL on OOM.
static void* wkv_cb_couple_new_topic(const wkv_event_t evt)
{
    cy_t* const                 cy    = (cy_t*)(((void**)evt.context)[0]);
    cy_topic_t* const           topic = (cy_topic_t*)(((void**)evt.context)[1]);
    cy_subscriber_root_t* const subr  = (cy_subscriber_root_t*)evt.node->value;
    const cy_err_t              res   = topic_couple(cy, topic, subr, evt.substitution_count, evt.substitutions);
    return (0 == res) ? NULL : "";
}

/// If there is a pattern subscriber matching the name of this topic, attempt to create a new subscription.
/// If a new subscription is created, the new topic will be returned.
static cy_topic_t* topic_subscribe_if_matching(cy_t* const     cy,
                                               const wkv_str_t resolved_name,
                                               const uint64_t  hash,
                                               const uint64_t  evictions)
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
        const cy_err_t res = topic_new(cy, &topic, resolved_name, hash, evictions);
        if (res != CY_OK) {
            cy->platform->topic_on_subscription_error(cy, NULL, res);
            return NULL;
        }
    }
    // Attach subscriptions.
    if (NULL != wkv_route(&cy->subscribers_by_pattern, //
                          resolved_name,
                          (void* [2]){ cy, topic }, // NOLINT(*-multi-level-implicit-pointer-conversion)
                          wkv_cb_couple_new_topic)) {
        // TODO discard the topic!
        cy->platform->topic_on_subscription_error(cy, NULL, CY_ERR_MEMORY);
        return NULL;
    }
    // Create the transport subscription once at the end, considering the parameters from all subscribers.
    topic_ensure_subscribed(cy, topic);
    return topic;
}

static void* wkv_cb_topic_scout_response(const wkv_event_t evt)
{
    cy_t* const       cy    = (cy_t*)evt.context;
    cy_topic_t* const topic = (cy_topic_t*)evt.node->value;
    CY_TRACE(cy, "📢'%s' #%016llx @%04x", topic->name, (unsigned long long)(topic->hash), cy_topic_subject_id(topic));
    schedule_gossip(cy, topic, true);
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
    uint64_t uid;
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
    cy_err_t res = ensure_joined(cy);
    if (res != CY_OK) {
        return res;
    }

    // Fill and serialize the message.
    message->uptime           = (uint32_t)((now - cy->ts_started) / MEGA);
    message->version          = 1;
    message->uid              = cy->uid;
    const size_t message_size = offsetof(heartbeat_t, topic_name) + message->topic_name_len;
    assert(message_size <= sizeof(heartbeat_t));
    assert(message->topic_name_len <= CY_TOPIC_NAME_MAX);
    const cy_buffer_borrowed_t payload = { .next = NULL, .view = { .data = message, .size = message_size } };

    // Publish the message.
    assert(cy->node_id <= cy->platform->node_id_max);
    res = cy->platform->topic_publish(cy, &cy->heartbeat_pub, now + HEARTBEAT_PUB_TIMEOUT_us, payload);
    cy->heartbeat_pub.topic->pub_transfer_id++;
    return res;
}

static cy_err_t publish_heartbeat_gossip(cy_t* const cy, cy_topic_t* const topic, const cy_us_t now)
{
    topic_ensure_subscribed(cy, topic); // use this opportunity to repair the subscription if broken
    heartbeat_t msg = { .topic_hash          = topic->hash,
                        .topic_evictions     = topic->evictions & UINT32_MAX,
                        .topic_evictions_msb = (uint8_t)(topic->evictions >> 32U),
                        .topic_lage          = topic_lage(topic, now),
                        ._reserved_1_        = 0,
                        .topic_name_len      = (uint_fast8_t)topic->index_name->key_len };
    memcpy(msg.topic_name, topic->name, topic->index_name->key_len);
    CY_TRACE(cy, "🗣️'%s' #%016llx @%04x", topic->name, (unsigned long long)topic->hash, cy_topic_subject_id(topic));
    // Update gossip even if failed so we don't get stuck publishing same gossip if error reporting is broken.
    schedule_gossip(cy, topic, false);
    return publish_heartbeat(cy, now, &msg);
}

static cy_err_t publish_heartbeat_scout(cy_t* const cy, const cy_us_t now)
{
    const cy_subscriber_root_t* subr = cy->next_scout;
    assert(subr != NULL); // https://github.com/pavel-kirienko/cy/issues/12#issuecomment-2953184238
    heartbeat_t msg = { .topic_lage = LAGE_SCOUT, .topic_name_len = (uint_fast8_t)subr->index_name->key_len };
    wkv_get_key(&cy->subscribers_by_name, subr->index_name, msg.topic_name);
    const cy_err_t res = publish_heartbeat(cy, now, &msg);
    CY_TRACE(cy, "📢'%s' result=%d", msg.topic_name, res);
    if (res == CY_OK) {
        cy->next_scout = subr->next_scout; // delist the scout if publication succeeded
    }
    return res;
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void on_heartbeat(cy_t* const cy, const cy_arrival_t* const evt)
{
    assert((evt->subscriber != NULL) && (evt->topic != NULL) && (evt->transfer != NULL));
    // Deserialize the message. TODO: deserialize properly and check version.
    heartbeat_t  heartbeat = { 0 };
    const size_t msg_size =
      cy_buffer_owned_gather(evt->transfer->payload, (cy_bytes_mut_t){ .size = sizeof(heartbeat), .data = &heartbeat });
    if ((msg_size < offsetof(heartbeat_t, topic_name)) || (heartbeat.version != 1)) {
        return;
    }
    const cy_us_t                 ts         = evt->transfer->timestamp;
    const cy_transfer_metadata_t* meta       = &evt->transfer->metadata;
    const uint64_t                other_hash = heartbeat.topic_hash;
    const uint64_t    other_evictions = heartbeat.topic_evictions + (((uint64_t)heartbeat.topic_evictions_msb) << 32U);
    const int_fast8_t other_lage      = heartbeat.topic_lage;
    const wkv_str_t   key             = { .len = heartbeat.topic_name_len, .str = heartbeat.topic_name };
    //
    if (heartbeat.topic_lage >= -1) {
        // Find the topic in our local database. Create if there is a pattern match.
        cy_topic_t* mine = cy_topic_find_by_hash(cy, other_hash);
        if (mine == NULL) {
            mine = topic_subscribe_if_matching(cy, key, other_hash, other_evictions);
        }
        if (mine != NULL) {                   // We have this topic! Check if we have consensus on the subject-ID.
            schedule_gossip(cy, mine, false); // suppress next gossip -- the network just heard about it
            implicit_animate(cy, mine, ts);
            assert(mine->hash == other_hash);
            const int_fast8_t mine_lage = topic_lage(mine, ts);
            if (mine->evictions != other_evictions) {
                CY_TRACE(cy,
                         "🔀 Divergence on '%s' #%016llx discovered via gossip from uid=%016llx nid=%04x:\n"
                         "\t local  @%04x evict=%llu lage=%+d\n"
                         "\t remote @%04x evict=%llu lage=%+d",
                         mine->name,
                         (unsigned long long)mine->hash,
                         (unsigned long long)heartbeat.uid,
                         meta->remote_node_id,
                         cy_topic_subject_id(mine),
                         (unsigned long long)mine->evictions,
                         mine_lage,
                         topic_subject_id(other_hash, other_evictions),
                         (unsigned long long)other_evictions,
                         other_lage);
                if ((mine_lage > other_lage) || ((mine_lage == other_lage) && (mine->evictions > other_evictions))) {
                    CY_TRACE(cy, "We won, existing allocation not altered; expecting remote to adjust.");
                    assert(!is_pinned(mine->hash));
                    schedule_gossip(cy, mine, true);
                } else {
                    assert((mine_lage <= other_lage) &&
                           ((mine_lage < other_lage) || (mine->evictions < other_evictions)));
                    assert(mine_lage <= other_lage);
                    CY_TRACE(cy,
                             "We lost, reallocating the topic to try and match the remote, or offer new alternative.");
                    topic_merge_lage(mine, ts, other_lage);
                    topic_allocate(cy, mine, other_evictions, false, ts);
                    if (mine->evictions == other_evictions) { // perfect sync, lower the gossip priority
                        schedule_gossip(cy, mine, false);
                    }
                }
            } else {
                topic_ensure_subscribed(cy, mine); // use this opportunity to repair the subscription if broken
            }
            topic_merge_lage(mine, ts, other_lage);
        } else { // We don't know this topic; check for a subject-ID collision and do auto-subscription.
            mine = topic_find_by_subject_id(cy, topic_subject_id(other_hash, other_evictions));
            if (mine == NULL) {
                return; // We are not using this subject-ID, no collision.
            }
            assert(cy_topic_subject_id(mine) == topic_subject_id(other_hash, other_evictions));
            const bool win = left_wins(mine, ts, other_lage, other_hash);
            CY_TRACE(cy,
                     "💥 Collision @%04x discovered via gossip from uid=%016llx nid=%04x; we %s. Contestants:\n"
                     "\t local  #%016llx evict=%llu lage=%+d '%s'\n"
                     "\t remote #%016llx evict=%llu lage=%+d '%s'",
                     cy_topic_subject_id(mine),
                     (unsigned long long)heartbeat.uid,
                     meta->remote_node_id,
                     (win ? "WIN" : "LOSE"),
                     (unsigned long long)mine->hash,
                     (unsigned long long)mine->evictions,
                     topic_lage(mine, ts),
                     mine->name,
                     (unsigned long long)other_hash,
                     (unsigned long long)other_evictions,
                     other_lage,
                     heartbeat.topic_name);
            // We don't need to do anything if we won, but we need to announce to the network (in particular to the
            // infringing node) that we are using this subject-ID, so that the loser knows that it has to move.
            // If we lost, we need to gossip this topic ASAP as well because every other participant on this topic
            // will also move, but the trick is that the others could have settled on different subject-IDs.
            // Everyone needs to publish their own new allocation and then we will pick max subject-ID out of that.
            if (!win) {
                topic_allocate(cy, mine, mine->evictions + 1U, false, ts);
            } else {
                assert(!is_pinned(mine->hash));
                schedule_gossip(cy, mine, true);
            }
        }
    } else if (heartbeat.topic_lage == LAGE_SCOUT) {
        // A scout message is simply asking us to check if we have any matching topics, and gossip them ASAP if so.
        CY_TRACE(cy,
                 "📢 Scout from uid=%016llx nid=%04x: query='%s' hash=%016llx evict=%llu lage=%+d",
                 (unsigned long long)heartbeat.uid,
                 meta->remote_node_id,
                 heartbeat.topic_name,
                 (unsigned long long)other_hash,
                 (unsigned long long)other_evictions,
                 other_lage);
        (void)wkv_match(&cy->topics_by_name, key, cy, wkv_cb_topic_scout_response);
    } else {
        CY_TRACE(cy,
                 "⚠️ Invalid heartbeat message version=%d from uid=%016llx nid=%04x: lage=%+d",
                 (int)heartbeat.version,
                 (unsigned long long)heartbeat.uid,
                 meta->remote_node_id,
                 heartbeat.topic_lage);
    }
}

// =====================================================================================================================
//                                                      PUBLISHER
// =====================================================================================================================

static void futures_retire_timed_out(cy_t* cy, const cy_us_t now)
{
    // TODO use list instead of AVL!
    cy_future_t* fut = (cy_future_t*)cavl2_min(cy->futures_by_deadline);
    while ((fut != NULL) && (fut->deadline < now)) {
        assert(fut->state == cy_future_pending);
        cavl2_remove(&cy->futures_by_deadline, &fut->index_deadline);
        cavl2_remove(&fut->publisher->topic->futures_by_transfer_id, &fut->index_transfer_id);
        fut->state = cy_future_timeout_response;
        if (fut->callback != NULL) {
            fut->callback(cy, fut);
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
        cy->platform->topic_advertise(cy, pub->topic, response_extent + P2P_HEADER_BYTES);
        if (!is_pinned(pub->topic->hash)) {
            schedule_gossip(cy, pub->topic, true); // Announce change ASAP
        }
    }
    CY_TRACE(cy,
             "✨'%s' #%016llx @%04x: topic_count=%zu pub_count=%zu res=%d",
             pub->topic->name,
             (unsigned long long)pub->topic->hash,
             cy_topic_subject_id(pub->topic),
             cavl_count(cy->topics_by_hash),
             pub->topic->pub_count,
             res);
    return res;
}

void cy_unadvertise(cy_t* const cy, cy_publisher_t* pub)
{
    (void)cy;
    (void)pub;
}

void cy_future_new(cy_future_t* const future, const cy_future_callback_t callback, void* const user)
{
    assert(future != NULL);
    memset(future, 0, sizeof(*future));
    future->state    = cy_future_fresh;
    future->callback = callback;
    future->user     = user;
}

cy_err_t cy_publish(cy_t* const                cy,
                    cy_publisher_t* const      pub,
                    const cy_us_t              tx_deadline,
                    const cy_buffer_borrowed_t payload,
                    const cy_us_t              response_deadline,
                    cy_future_t* const         future)
{
    assert(pub != NULL);
    cy_topic_t* const topic = pub->topic;
    assert(topic != NULL);
    assert(topic->pub_count > 0);

    // If we still don't have a node-ID, force allocation right now.
    // Normally, however, the application should wait for cy_join() to complete before publishing anything.
    cy_err_t res = ensure_joined(cy);
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
        future->transfer_id_masked = topic->pub_transfer_id & cy->platform->transfer_id_mask;
        future->deadline           = response_deadline;
        future->last_response      = (cy_transfer_owned_t){ 0 };
        // NB: we don't touch the callback and the user pointer, as they are to be initialized by the user.
        const cy_tree_t* const tr = cavl2_find_or_insert(&topic->futures_by_transfer_id,
                                                         &future->transfer_id_masked,
                                                         &cavl_comp_future_transfer_id_masked,
                                                         future,
                                                         &cavl_factory_future_transfer_id);
        if (tr != &future->index_transfer_id) {
            return CY_ERR_CAPACITY;
        }
    }

    res = cy->platform->topic_publish(cy, pub, tx_deadline, payload);

    if (future != NULL) {
        if (res == CY_OK) {
            const cy_tree_t* const tr = cavl2_find_or_insert(&cy->futures_by_deadline,
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
    cy_t* const                  cy    = (cy_t*)(((void**)evt.context)[0]);
    const cy_subscriber_t* const sub   = (cy_subscriber_t*)(((void**)evt.context)[1]);
    cy_topic_t* const            topic = (cy_topic_t*)evt.node->value;
    // If the new subscription parameters are different, we will need to resubscribe this topic.
    bool resubscribe = false;
    if (topic->subscribed) {
        const cy_subscription_params_t param_old = deduce_subscription_params(topic);
        const cy_subscription_params_t param_new = sub->params;
        resubscribe = (param_new.extent > param_old.extent) || //-------------------------------------
                      (param_new.transfer_id_timeout > param_old.transfer_id_timeout);
    }
    // Create the coupling.
    const cy_err_t res = topic_couple(cy, topic, sub->root, evt.substitution_count, evt.substitutions);
    // Refresh the subscription if needed. Due to the new coupling, the params are now different.
    if (res == CY_OK) {
        if (resubscribe) {
            cy->platform->topic_unsubscribe(cy, topic);
            topic->subscribed = false;
        }
        topic_ensure_subscribed(cy, topic);
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
    } else {
        root->index_pattern = NULL;
        const cy_err_t res  = topic_ensure(cy, NULL, resolved_name);
        if (res != CY_OK) {
            wkv_del(&cy->subscribers_by_name, node);
            mem_free(cy, node->value);
            return res;
        }
    }

    // Register the next pending scout. We do it strictly in the FIFO order.
    if (wc) {
        cy_subscriber_root_t* next_scout = cy->next_scout;
        while ((next_scout != NULL) && (next_scout->next_scout != NULL)) {
            next_scout = next_scout->next_scout;
        }
        if (next_scout == NULL) {
            cy->next_scout = root;
        } else {
            next_scout->next_scout = root;
        }
    }

    *out_root = root;
    return CY_OK;
}

cy_err_t cy_subscribe_with_params(cy_t* const                    cy,
                                  cy_subscriber_t* const         sub,
                                  const wkv_str_t                name,
                                  const cy_subscription_params_t params,
                                  const cy_subscriber_callback_t callback)
{
    if ((sub == NULL) || (cy == NULL) || (params.transfer_id_timeout < 0) || (callback == NULL)) {
        return CY_ERR_ARGUMENT;
    }
    char name_buf[CY_TOPIC_NAME_MAX + 1U];
    if (!resolve_name(cy->namespace_, cy->name, name.str, name_buf)) {
        return CY_ERR_NAME;
    }
    const wkv_str_t resolved_name = wkv_key(name_buf);
    (void)memset(sub, 0, sizeof(*sub));
    CY_TRACE(cy,
             "✨'%s' extent=%zu tid_timeout=%lld",
             resolved_name.str,
             params.extent,
             (long long)params.transfer_id_timeout);
    const cy_err_t res = ensure_subscriber_root(cy, resolved_name, &sub->root);
    if (res != CY_OK) {
        return res;
    }
    assert(sub->root != NULL);
    sub->params     = params;
    sub->callback   = callback;
    sub->next       = sub->root->head;
    sub->root->head = sub;
    if (NULL != wkv_match(&cy->topics_by_name, //
                          resolved_name,
                          (void*)(void* [2]){ cy, sub },
                          wkv_cb_couple_new_subscription)) {
        cy_unsubscribe(cy, sub);
        return CY_ERR_MEMORY;
    }
    return CY_OK;
}

void cy_unsubscribe(cy_t* const cy, cy_subscriber_t* const sub)
{
    (void)cy;
    (void)sub;
}

cy_err_t cy_respond(cy_t* const                cy,
                    cy_topic_t* const          topic,
                    const cy_us_t              tx_deadline,
                    cy_transfer_metadata_t     metadata,
                    const cy_buffer_borrowed_t payload)
{
    assert(topic != NULL);
    const cy_err_t res = ensure_joined(cy);
    if (res != CY_OK) {
        return res;
    }
    const uint64_t response_header[3] = { p2p_kind_response, topic->hash, metadata.transfer_id };
    return cy->platform->p2p(cy,
                             topic,
                             metadata.priority,
                             metadata.remote_node_id,
                             tx_deadline,
                             (cy_buffer_borrowed_t){
                               .next = &payload,
                               .view = { .size = sizeof(response_header), .data = &response_header },
                             });
}

void cy_subscriber_name(const cy_t* const cy, const cy_subscriber_t* const sub, char* const out_name)
{
    wkv_get_key(&cy->subscribers_by_name, sub->root->index_name, out_name);
}

// =====================================================================================================================
//                                                  NODE & TOPIC
// =====================================================================================================================

cy_us_t cy_now(const cy_t* const cy)
{
    return cy->platform->now(cy);
}

bool cy_joined(const cy_t* const cy)
{
    return cy->node_id <= cy->platform->node_id_max;
}

void cy_topic_hint(cy_t* const cy, cy_topic_t* const topic, const uint16_t subject_id)
{
    if ((topic != NULL) && (subject_id < CY_TOTAL_SUBJECT_COUNT) && (!is_pinned(topic->hash)) &&
        (topic->evictions == 0)) {
        // Existing subscriptions need to be deactivated first, if any.
        if (topic->subscribed) {
            assert(topic->couplings != NULL);
            cy->platform->topic_unsubscribe(cy, topic);
        }
        // Fit the lowest evictions counter such that we land at the specified subject-ID.
        // Avoid negative remainders, so we don't use simple evictions=(subject_id-hash)%6144.
        while (topic_subject_id(topic->hash, topic->evictions) != subject_id) {
            topic->evictions++;
        }
        assert(cy_topic_subject_id(topic) == subject_id);
        // Restore the subscriptions.
        topic_ensure_subscribed(cy, topic);
    }
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
    if (topic == NULL) {
        return NULL;
    }
    assert(topic->hash == hash);
    return topic;
}

cy_topic_t* cy_topic_iter_first(const cy_t* const cy)
{
    return (cy_topic_t*)cavl2_min(cy->topics_by_hash);
}

cy_topic_t* cy_topic_iter_next(cy_topic_t* const topic)
{
    return (cy_topic_t*)cavl2_next_greater(&topic->index_hash);
}

uint16_t cy_topic_subject_id(const cy_topic_t* const topic)
{
    return topic_subject_id(topic->hash, topic->evictions);
}

wkv_str_t cy_topic_name(const cy_topic_t* const topic)
{
    return (wkv_str_t){ .len = topic->index_name->key_len, .str = topic->name };
}

bool cy_has_substitution_tokens(const wkv_str_t name)
{
    wkv_t kv;
    wkv_init(&kv, &wkv_realloc);
    return wkv_has_substitution_tokens(&kv, name);
}

// =====================================================================================================================
//                                                      BUFFERS
// =====================================================================================================================

void cy_buffer_owned_release(cy_t* const cy, cy_buffer_owned_t* const payload)
{
    if ((cy != NULL) && (payload != NULL) && (payload->origin.data != NULL)) {
        cy->platform->buffer_release(cy, *payload);
        // nullify the pointers to prevent double free
        payload->base.next   = NULL;
        payload->origin.size = 0;
        payload->origin.data = NULL;
    }
}

size_t cy_buffer_borrowed_size(const cy_buffer_borrowed_t payload)
{
    size_t                      out = 0;
    const cy_buffer_borrowed_t* p   = &payload;
    while (p != NULL) {
        out += p->view.size;
        p = p->next;
    }
    return out;
}

size_t cy_buffer_borrowed_gather(const cy_buffer_borrowed_t payload, const cy_bytes_mut_t dest)
{
    size_t offset = 0;
    if (NULL != dest.data) {
        const cy_buffer_borrowed_t* frag = &payload;
        while ((frag != NULL) && (offset < dest.size)) {
            assert(frag->view.data != NULL);
            const size_t frag_size = smaller(frag->view.size, dest.size - offset);
            (void)memmove(((char*)dest.data) + offset, frag->view.data, frag_size);
            offset += frag_size;
            assert(offset <= dest.size);
            frag = frag->next;
        }
    }
    return offset;
}

// =====================================================================================================================
//                                              PLATFORM LAYER INTERFACE
// =====================================================================================================================

cy_err_t cy_new(cy_t* const                cy,
                const cy_platform_t* const platform,
                const uint64_t             uid,
                const uint16_t             node_id,
                const wkv_str_t            namespace_)
{
    assert(cy != NULL);
    assert(uid != 0);
    assert(platform != NULL);
    assert(platform->now != NULL);
    assert(platform->realloc != NULL);
    assert(platform->prng != NULL);
    assert(platform->buffer_release != NULL);
    assert(platform->node_id_set != NULL);
    assert(platform->node_id_clear != NULL);
    assert(platform->node_id_bloom != NULL);
    assert(platform->p2p != NULL);
    assert(platform->topic_new != NULL);
    assert(platform->topic_destroy != NULL);
    assert(platform->topic_publish != NULL);
    assert(platform->topic_subscribe != NULL);
    assert(platform->topic_unsubscribe != NULL);
    assert(platform->topic_advertise != NULL);
    assert(platform->topic_on_subscription_error != NULL);
    assert((platform->node_id_max > 0) && (platform->node_id_max < CY_NODE_ID_INVALID));

    if (namespace_.len > CY_NAMESPACE_NAME_MAX) {
        return CY_ERR_NAME;
    }

    // Init the object.
    memset(cy, 0, sizeof(*cy));
    cy->platform = platform;
    cy->uid      = uid;
    cy->node_id  = (node_id <= platform->node_id_max) ? node_id : CY_NODE_ID_INVALID;
    // namespace
    if (namespace_.len > 0) {
        memcpy(cy->namespace_, namespace_.str, namespace_.len);
        cy->namespace_[namespace_.len] = '\0';
    } else {
        cy->namespace_[0] = '~';
        cy->namespace_[1] = '\0';
    }
    // the default name is just derived from UID, can be overridden by the user later
    (void)snprintf(cy->name,
                   sizeof(cy->name),
                   "@/%04x/%04x/%08lx/",
                   (unsigned)(uid >> 48U) & UINT16_MAX,
                   (unsigned)(uid >> 32U) & UINT16_MAX,
                   (unsigned long)(uid & UINT32_MAX));
    cy->topics_by_hash       = NULL;
    cy->topics_by_subject_id = NULL;
    cy->next_scout           = NULL;
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

    cy_bloom64_t* const node_id_bloom = platform->node_id_bloom(cy);
    assert(node_id_bloom != NULL);
    assert(node_id_bloom->n_bits > 0);
    assert((node_id_bloom->n_bits % 64) == 0);
    bloom64_purge(node_id_bloom);

    // If a node-ID is given explicitly, we want to publish our heartbeat ASAP to speed up network convergence
    // and to claim the address; if it's already taken, we will want to cause a collision to move the other node,
    // because manually assigned addresses take precedence over auto-assigned ones.
    // If we are not given a node-ID, we need to first listen to the network.
    cy->heartbeat_next        = now;
    cy->heartbeat_next_urgent = HEAT_DEATH;
    cy->heartbeat_period      = 3 * MEGA;
    cy_err_t res              = CY_OK;
    if (cy->node_id > cy->platform->node_id_max) {
        cy->heartbeat_next += random_int(cy, cy->heartbeat_period, 3 * cy->heartbeat_period);
    } else {
        bloom64_set(node_id_bloom, cy->node_id);
        assert(node_id_bloom->popcount == 1);
        res = cy->platform->node_id_set(cy);
    }

    cy->implicit_topic_timeout = IMPLICIT_TOPIC_DEFAULT_TIMEOUT_us;

    // Pub/sub on the heartbeat topic.
    if (res == CY_OK) {
        res = cy_advertise_c(cy, &cy->heartbeat_pub, CY_CONFIG_HEARTBEAT_TOPIC_NAME, 0);
        if (res == CY_OK) {
            res = cy_subscribe_c(
              cy, &cy->heartbeat_sub, CY_CONFIG_HEARTBEAT_TOPIC_NAME, sizeof(heartbeat_t), &on_heartbeat);
            if (res != CY_OK) {
                cy_unadvertise(cy, &cy->heartbeat_pub);
            }
        }
    }
    return res;
}

/// We snoop on all transfers to update the node-ID occupancy Bloom filter.
/// If we don't have a node-ID and this is a new Bloom entry, follow CSMA/CD: add random wait.
/// The point is to reduce the chances of multiple nodes appearing simultaneously and claiming same node-IDs.
/// We keep tracking neighbors even if we have a node-ID in case we encounter a collision later and need to move.
static void mark_neighbor(cy_t* const cy, const uint16_t remote_node_id)
{
    cy_bloom64_t* const bloom = cy->platform->node_id_bloom(cy);
    assert((bloom != NULL) && (bloom->n_bits > 0) && ((bloom->n_bits % 64) == 0) && (bloom->popcount <= bloom->n_bits));
    // A large population count indicates that the filter contains tombstones (marks for nodes that have left the
    // network). We can't remove them individually, so we purge the filter and start over.
    const bool bloom_congested = bloom->popcount > ((bloom->n_bits * 31ULL) / 32U);
    if (bloom_congested) {
        CY_TRACE(cy, "🌻 bloom filter congested: popcount=%zu; purging to remove tombstones", bloom->popcount);
        bloom64_purge(bloom);
        assert(bloom->popcount == 0);
    }
    if ((cy->node_id > cy->platform->node_id_max) && !bloom64_get(bloom, remote_node_id)) {
        CY_TRACE(cy, "🔭 Discovered neighbor %04x; new bloom popcount %zu", remote_node_id, bloom->popcount + 1U);
    }
    bloom64_set(bloom, remote_node_id);
}

void cy_ingest(cy_t* const cy, cy_topic_t* const topic, cy_transfer_owned_t transfer)
{
    assert(topic != NULL);

    mark_neighbor(cy, transfer.metadata.remote_node_id);

    // Record activity so that the topic is not retired.
    implicit_animate(cy, topic, transfer.timestamp);

    // Simply invoke all callbacks that match this topic name.
    // The callback may unsubscribe, so we have to store the next pointer early.
    const cy_topic_coupling_t* cpl = topic->couplings;
    while (cpl != NULL) {
        const cy_topic_coupling_t* const next_cpl = cpl->next;
        cy_subscriber_t*                 sub      = cpl->root->head;
        assert(sub != NULL);
        while (sub != NULL) {
            cy_subscriber_t* const next_sub = sub->next;
            const cy_arrival_t     evt      = { .subscriber         = sub,
                                                .topic              = topic,
                                                .transfer           = &transfer,
                                                .substitution_count = cpl->substitution_count,
                                                .substitutions      = cpl->substitutions };
            sub->callback(cy, &evt);
            sub = next_sub;
        }
        cpl = next_cpl;
    }

    // Release the payload at the end, unless the subscriber(s) took ownership of it.
    if (transfer.payload.base.view.data != NULL) {
        cy->platform->buffer_release(cy, transfer.payload);
    }
}

void cy_ingest_p2p(cy_t* const cy, cy_transfer_owned_t transfer)
{
    assert(cy != NULL);
    mark_neighbor(cy, transfer.metadata.remote_node_id);

    // TODO: proper deserialization.
    if (transfer.payload.base.view.size < P2P_HEADER_BYTES) {
        cy->platform->buffer_release(cy, transfer.payload);
        return; // Malformed response -- missing header.
    }

    // Deserialize the header. The rest of the payload is for the application.
    uint64_t response_header[2];
    memcpy(&response_header, transfer.payload.base.view.data, sizeof(response_header));
    transfer.payload.base.view.size -= sizeof(response_header);
    transfer.payload.base.view.data   = ((const char*)transfer.payload.base.view.data) + sizeof(response_header);
    const uint64_t topic_hash         = response_header[0];
    const uint64_t transfer_id_masked = response_header[1] & cy->platform->transfer_id_mask;

    // Find the topic -- log(N) lookup.
    cy_topic_t* const topic = cy_topic_find_by_hash(cy, topic_hash);
    if (topic == NULL) {
        cy->platform->buffer_release(cy, transfer.payload);
        return; // We don't know this topic, ignore it.
    }

    // Find the matching pending response future -- log(N) lookup.
    cy_tree_t* const tr =
      cavl2_find(topic->futures_by_transfer_id, &transfer_id_masked, &cavl_comp_future_transfer_id_masked);
    if (tr == NULL) {
        cy->platform->buffer_release(cy, transfer.payload);
        return; // Unexpected or duplicate response. TODO: Linger completed futures for multiple responses?
    }
    cy_future_t* const fut = CAVL2_TO_OWNER(tr, cy_future_t, index_transfer_id);
    assert(fut->state == cy_future_pending);

    // Finalize and retire the future.
    fut->state = cy_future_success;
    cy_buffer_owned_release(cy, &fut->last_response.payload); // does nothing if already released
    fut->last_response = transfer;
    cavl2_remove(&cy->futures_by_deadline, &fut->index_deadline);
    cavl2_remove(&topic->futures_by_transfer_id, &fut->index_transfer_id);
    if (fut->callback != NULL) {
        fut->callback(cy, fut);
    }
}

cy_err_t cy_update(cy_t* const cy)
{
    cy_err_t      res = CY_OK;
    const cy_us_t now = cy_now(cy);

    futures_retire_timed_out(cy, now);
    implicit_retire_timed_out(cy, now);

    if (cy->node_id_collision) {
        CY_TRACE(cy, "🧠 Processing a recent node-ID collision event now.");
        assert(cy->node_id <= cy->platform->node_id_max);
        cy->node_id_collision = false;
        cy->node_id           = CY_NODE_ID_INVALID;
        cy->platform->node_id_clear(cy);
        cy->heartbeat_next = now;
    }

    // Decide if it is time to publish a heartbeat. We use a very simple minimal-state scheduler that runs two
    // periods and offers an opportunity to publish a heartbeat every now and then.
    if ((now >= cy->heartbeat_next) || (now >= cy->heartbeat_next_urgent)) {
        cy_topic_t* tg = LIST_MEMBER(cy->list_gossip_urgent.tail, cy_topic_t, list_gossip);
        if ((now >= cy->heartbeat_next) || (tg != NULL) || (cy->next_scout != NULL)) {
            if ((tg != NULL) || (cy->next_scout == NULL)) {
                tg  = (tg != NULL) ? tg : LIST_MEMBER(cy->list_gossip.tail, cy_topic_t, list_gossip);
                tg  = (tg != NULL) ? tg : cy->heartbeat_pub.topic;
                res = publish_heartbeat_gossip(cy, tg, now);
            } else {
                res = publish_heartbeat_scout(cy, now);
            }
            cy->heartbeat_next = now + dither_int(cy, cy->heartbeat_period, cy->heartbeat_period / 8);
        }
        cy->heartbeat_next_urgent = now + cy->heartbeat_period / 16U;
    }
    return res;
}

void cy_notify_topic_collision(cy_t* const cy, cy_topic_t* const topic)
{
    if (topic != NULL) { // Topics with the same time will be ordered FIFO -- the tree is stable.
        schedule_gossip(cy, topic, true);
    }
}

void cy_notify_node_id_collision(cy_t* const cy)
{
    assert(cy != NULL);
    if ((!cy->node_id_collision) && (cy->node_id <= cy->platform->node_id_max)) {
        cy->node_id_collision = true;
        CY_TRACE(cy, "💥 %04x", cy->node_id);
    }
}
