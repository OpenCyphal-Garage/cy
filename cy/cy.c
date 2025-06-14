///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// This is just a PoC, a crude approximation of what it might look like when implemented properly.
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#include "cy_platform.h"

#define CAVL2_RELATION int32_t
#define CAVL2_T        struct cy_tree_t
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

/// The earliest representable time in microseconds.
#define BIG_BANG INT64_MIN

#define HEARTBEAT_DEFAULT_PERIOD_us 333331
#define HEARTBEAT_PUB_TIMEOUT_us    (1 * MEGA)

// clang-format off
static   size_t smaller(const size_t a,   const size_t b)   { return (a < b) ? a : b; }
static   size_t  larger(const size_t a,   const size_t b)   { return (a > b) ? a : b; }
static  int64_t max_i64(const int64_t a,  const int64_t b)  { return (a > b) ? a : b; }
static uint64_t max_u64(const uint64_t a, const uint64_t b) { return (a > b) ? a : b; }
// clang-format on

/// Returns -1 if the argument is zero to allow linear comparison.
static int_fast8_t log2_floor(const uint64_t x)
{
    return (int_fast8_t)((x == 0) ? -1 : (63 - __builtin_clzll(x)));
}

static uint64_t random_u64(const struct cy_t* const cy)
{
    const uint64_t seed[2] = { cy->platform->prng(cy), cy->uid };
    return rapidhash(seed, sizeof(seed));
}

/// The limits are inclusive. Returns min unless min < max.
static uint64_t random_uint(const struct cy_t* const cy, const uint64_t min, const uint64_t max)
{
    if (min < max) {
        return (random_u64(cy) % (max - min)) + min;
    }
    return min;
}

static void* wkv_realloc(struct wkv_t* const self, void* ptr, const size_t new_size)
{
    return ((struct cy_t*)self->context)->platform->realloc((struct cy_t*)self->context, ptr, new_size);
}

static void* mem_alloc(struct cy_t* const cy, const size_t size)
{
    return cy->platform->realloc(cy, NULL, size);
}

static void mem_free(struct cy_t* const cy, void* ptr)
{
    if (ptr != NULL) {
        cy->platform->realloc(cy, ptr, 0);
    }
}

/// Simply returns the value of the first hit. Useful for existence checks.
static void* wkv_cb_first(const struct wkv_event_t evt)
{
    return evt.node->value;
}

// =====================================================================================================================
//                                                      NAMES
// =====================================================================================================================

/// TODO this is ugly and dirty
static bool compose_topic_name(const char* const ns,
                               const char* const user,
                               const char* const name,
                               char* const       destination)
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

/// Very fast single-pass check for valid substitution tokens in the name.
/// "abc/*/def" is a wildcard, but "abc/x*/def" is not.
static bool is_wildcard(const char* const name)
{
    const char* const sep = strchr(name, '/');
    const size_t      len = (sep != NULL) ? (size_t)(sep - name) : strlen(name);
    if ((len == 1) && ((name[0] == '?') || (name[0] == '*'))) {
        return true;
    }
    return (sep == NULL) ? false : is_wildcard(sep + 1); // tail call
}

// =====================================================================================================================
//                                                  AVL TREE UTILITIES
// =====================================================================================================================

static int32_t cavl_comp_topic_hash(const void* const user, const struct cy_tree_t* const node)
{
    assert((user != NULL) && (node != NULL));
    const uint64_t                 outer = *(uint64_t*)user;
    const struct cy_topic_t* const inner = (const struct cy_topic_t*)node;
    if (outer == inner->hash) {
        return 0;
    }
    return (outer >= inner->hash) ? +1 : -1;
}

static int32_t cavl_comp_topic_subject_id(const void* const user, const struct cy_tree_t* const node)
{
    assert((user != NULL) && (node != NULL));
    const struct cy_topic_t* const inner = CAVL2_TO_OWNER(node, struct cy_topic_t, index_subject_id);
    return (int32_t)(*(uint16_t*)user) - ((int32_t)cy_topic_subject_id(inner));
}

/// Gossip times are not unique, so this comparator never returns 0.
static int32_t cavl_comp_topic_gossip_time(const void* const user, const struct cy_tree_t* const node)
{
    assert((user != NULL) && (node != NULL));
    const struct cy_topic_t* const inner = CAVL2_TO_OWNER(node, struct cy_topic_t, index_gossip_time);
    return ((*(cy_us_t*)user) >= inner->last_gossip) ? +1 : -1;
}

static int32_t cavl_comp_future_transfer_id_masked(const void* const user, const struct cy_tree_t* const node)
{
    assert((user != NULL) && (node != NULL));
    const uint64_t                  outer = *(uint64_t*)user;
    const struct cy_future_t* const inner = CAVL2_TO_OWNER(node, struct cy_future_t, index_transfer_id);
    if (outer == inner->transfer_id_masked) {
        return 0;
    }
    return (outer >= inner->transfer_id_masked) ? +1 : -1;
}

/// Deadlines are not unique, so this comparator never returns 0.
static int32_t cavl_comp_future_deadline(const void* const user, const struct cy_tree_t* const node)
{
    assert((user != NULL) && (node != NULL));
    const struct cy_future_t* const inner = CAVL2_TO_OWNER(node, struct cy_future_t, index_deadline);
    return ((*(cy_us_t*)user) >= inner->deadline) ? +1 : -1;
}

static struct cy_tree_t* cavl_factory_future_transfer_id(void* const user)
{
    return &((struct cy_future_t*)user)->index_transfer_id;
}

static struct cy_tree_t* cavl_factory_future_deadline(void* const user)
{
    return &((struct cy_future_t*)user)->index_deadline;
}

static struct cy_tree_t* cavl_factory_topic_subject_id(void* const user)
{
    return &((struct cy_topic_t*)user)->index_subject_id;
}

static struct cy_tree_t* cavl_factory_topic_gossip_time(void* const user)
{
    return &((struct cy_topic_t*)user)->index_gossip_time;
}

// =====================================================================================================================
//                                                  NODE ID ALLOCATION
// =====================================================================================================================

// ReSharper disable CppParameterMayBeConstPtrOrRef

/// A Bloom filter is a set-only structure so there is no way to clear a bit after it has been set.
/// It is only possible to purge the entire filter state.
static void bloom64_set(struct cy_bloom64_t* const bloom, const size_t value)
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

static bool bloom64_get(const struct cy_bloom64_t* const bloom, const size_t value)
{
    assert(bloom != NULL);
    const size_t index = value % bloom->n_bits;
    return (bloom->storage[index / 64U] & (1ULL << (index % 64U))) != 0;
}

static void bloom64_purge(struct cy_bloom64_t* const bloom)
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
static uint16_t pick_node_id(const struct cy_t* const cy, struct cy_bloom64_t* const bloom, const uint16_t node_id_max)
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
    uint8_t bit_index = (uint8_t)random_uint(cy, 0U, 63U);
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

// =====================================================================================================================
//                                                  TOPIC UTILITIES
// =====================================================================================================================

struct cy_subscriber_root_t
{
    struct wkv_node_t* index_name;
    struct wkv_node_t* index_wildcard;

    /// If this is a wildcard subscriber, we will need to publish a scout message.
    struct cy_subscriber_root_t* next_scout;

    struct cy_subscriber_t* head;
};

/// A single topic may match multiple subscribers if wildcards are used.
/// Each instance holds a pointer to the corresponding subscriber root and a pointer to the next match for this topic.
struct cy_topic_coupling_t
{
    struct cy_subscriber_root_t* root;
    struct cy_topic_coupling_t*  next;

    size_t                   substitution_count;               ///< The size of the following substitutions flex array.
    struct cy_substitution_t substitutions[CY_TOPIC_NAME_MAX]; ///< Flex array.
};

/// Pinned topic names are canonical, which ensures that one pinned topic cannot collide with another.
static bool is_pinned(const uint64_t hash)
{
    return hash < CY_TOTAL_SUBJECT_COUNT;
}

/// This comparator is only applicable on subject-ID allocation conflicts. As such, hashes must be different.
static bool left_wins(const struct cy_topic_t* const left, const uint64_t r_age, const uint64_t r_hash)
{
    assert(left->hash != r_hash);
    if (is_pinned(left->hash) != is_pinned(r_hash)) {
        // We could replace this special case with an age advantage for pinned topics, but then we're reducing the
        // effective range of the age by a factor of 2^32, which risks overflow.
        return is_pinned(left->hash);
    }
    const int_fast8_t l_lage = log2_floor(left->age);
    const int_fast8_t r_lage = log2_floor(r_age);
    if (l_lage == r_lage) {
        return left->hash < r_hash;
    }
    return l_lage > r_lage; // older topic wins
}

/// log(N) index update requires removal and reinsertion.
static void update_last_gossip_time(struct cy_topic_t* const topic, const cy_us_t ts)
{
    assert(topic->cy->topics_by_gossip_time != NULL); // This index is never empty if we have topics
    cavl2_remove(&topic->cy->topics_by_gossip_time, &topic->index_gossip_time);
    topic->last_gossip                 = ts;
    const struct cy_tree_t* const tree = cavl2_find_or_insert(&topic->cy->topics_by_gossip_time, //
                                                              &ts,
                                                              cavl_comp_topic_gossip_time,
                                                              topic,
                                                              cavl_factory_topic_gossip_time);
    assert(tree == &topic->index_gossip_time);
}

static void schedule_gossip(struct cy_topic_t* const topic, const cy_us_t new_time)
{
    assert(topic->cy->topics_by_gossip_time != NULL); // This index is never empty if we have topics
    if (topic->last_gossip > 0) {                     // Don't do anything if it's already scheduled.
        CY_TRACE(
          topic->cy, "'%s' #%016llx @%04x", topic->name, (unsigned long long)topic->hash, cy_topic_subject_id(topic));
        // This is an optional optimization: if this is a pinned topic, it normally cannot collide with another one
        // (unless the user placed it in the dynamically allocated subject-ID range, which is not our problem);
        // we are publishing it just to announce that we have it; as such, the urgency of this action is a bit lower
        // than that of an actual colliding topic announcement, so we choose next-greater time to deprioritize it.
        const cy_us_t deranking = is_pinned(topic->hash) ? 1 : 0;
        update_last_gossip_time(topic, new_time + deranking);
    }
}

/// Returns CY_SUBJECT_ID_INVALID if the string is not a valid pinned subject-ID form.
/// Pinned topic names must have only canonical names to ensure that no two topic names map to the same subject-ID.
/// The only requirement to ensure this is that there must be no leading zeros in the number.
static uint32_t parse_pinned(const char* s)
{
    if ((s == NULL) || (*s == '\0') || (*s == '0')) { // Leading zeroes not allowed; only canonical form is accepted.
        return CY_SUBJECT_ID_INVALID;
    }
    uint32_t out = 0U;
    while (*s != '\0') {
        if ((*s < '0') || (*s > '9')) {
            return CY_SUBJECT_ID_INVALID;
        }
        out = (out * 10U) + (uint8_t)(*s++ - '0');
        if (out >= CY_TOTAL_SUBJECT_COUNT) {
            return CY_SUBJECT_ID_INVALID;
        }
    }
    return out;
}

/// The topic hash is the key component of the protocol.
/// For pinned topics, hash<CY_TOTAL_SUBJECT_COUNT.
/// The probability of a random hash falling into the pinned range is ~4.44e-16, or about one in two quadrillion.
static uint64_t topic_hash(const struct wkv_str_t name)
{
    uint64_t hash = parse_pinned(name.str);
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

/// This is linear complexity but we expect to have few subscribers per topic, so it is acceptable.
/// If this becomes a problem, we can simply store the subscription parameters in the topic fields.
static struct cy_subscription_params_t deduce_subscription_params(struct cy_topic_t* const topic)
{
    struct cy_subscription_params_t out = { 0, 0 };
    // Go over all couplings and all subscribers in each coupling.
    const struct cy_topic_coupling_t* cpl = topic->couplings;
    assert(cpl != NULL);
    while (cpl != NULL) {
        const struct cy_subscriber_t* sub = cpl->root->head;
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
static void topic_ensure_subscribed(struct cy_topic_t* const topic)
{
    if ((topic->couplings != NULL) && (!topic->subscribed)) {
        const cy_err_t res = topic->cy->platform->topic_subscribe(topic, deduce_subscription_params(topic));
        topic->subscribed  = res >= 0;
        if (!topic->subscribed) {
            topic->cy->platform->topic_handle_subscription_error(topic->cy, topic, res); // not our problem anymore
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
static void topic_allocate(struct cy_topic_t* const topic, const uint64_t new_evictions, const bool virgin)
{
    struct cy_t* const cy = topic->cy;
    assert(cy->topic_count <= CY_TOPIC_SUBJECT_COUNT); // There is certain to be a free subject-ID!

    static const int         call_depth_indent = 2;
    static _Thread_local int call_depth        = 0U;
    call_depth++;
    CY_TRACE(cy,
             "🔜%*s'%s' #%016llx @%04x evict=%llu->%llu age=%llu subscribed=%d couplings=%p",
             (call_depth - 1) * call_depth_indent,
             "",
             topic->name,
             (unsigned long long)topic->hash,
             cy_topic_subject_id(topic),
             (unsigned long long)topic->evictions,
             (unsigned long long)new_evictions,
             (unsigned long long)topic->age,
             (int)topic->subscribed,
             (void*)topic->couplings);

    // We need to make sure no underlying resources are sitting on this topic before we move it.
    // Otherwise, changing the subject-ID field on the go may break something underneath.
    if (topic->subscribed) {
        assert(topic->couplings != NULL);
        cy->platform->topic_unsubscribe(topic);
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
        assert(iter_count <= cy->topic_count);
        iter_count++;
        const uint16_t          sid = topic_subject_id(topic->hash, topic->evictions);
        struct cy_tree_t* const t   = cavl2_find_or_insert(
          &cy->topics_by_subject_id, &sid, &cavl_comp_topic_subject_id, topic, &cavl_factory_topic_subject_id);
        assert(t != NULL); // we will create it if not found, meaning allocation succeeded
        if (t == &topic->index_subject_id) {
            break; // Done!
        }
        // Someone else is sitting on that subject-ID. We need to arbitrate.
        struct cy_topic_t* const other = CAVL2_TO_OWNER(t, struct cy_topic_t, index_subject_id);
        assert(topic->hash != other->hash); // This would mean that we inserted the same topic twice, impossible
        if (left_wins(topic, other->age, other->hash)) {
            // This is our slot now! The other topic has to move.
            // This can trigger a chain reaction that in the worst case can leave no topic unturned.
            // One issue is that the worst-case recursive call depth equals the number of topics in the system.
            topic_allocate(other, other->evictions + 1U, false);
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
    schedule_gossip(topic, BIG_BANG);

    // If a subscription is needed, restore it. Notice that if this call failed in the past, we will retry here
    // as long as there is at least one live subscriber.
    assert(!topic->subscribed);
    topic_ensure_subscribed(topic);

    CY_TRACE(cy,
             "🔚%*s'%s' #%016llx @%04x evict=%llu age=%llu subscribed=%d iters=%zu",
             (call_depth - 1) * call_depth_indent,
             "",
             topic->name,
             (unsigned long long)topic->hash,
             cy_topic_subject_id(topic),
             (unsigned long long)topic->evictions,
             (unsigned long long)topic->age,
             (int)topic->subscribed,
             iter_count);
    assert(call_depth > 0);
    call_depth--;
}

static void topic_age(struct cy_topic_t* const topic, const cy_us_t now)
{
    const int32_t sec = (int32_t)((now - topic->aged_at) / MEGA);
    assert(sec >= 0);
    if (sec > 0) {
        topic->age++; // We increment it at most once because we want to avoid large leaps.
    }
    topic->aged_at += sec * MEGA;
}

/// UB if the topic under this name already exists.
/// out_topic may be new if the reference is not immediately needed (it can be found later via indexes).
static cy_err_t topic_new(struct cy_t* const cy, struct cy_topic_t** const out_topic, const char* const name)
{
    assert((cy != NULL) && (name != NULL));
    struct cy_topic_t* const topic = cy->platform->topic_new(cy);
    if (topic == NULL) {
        return CY_ERR_MEMORY;
    }
    memset(topic, 0, sizeof(*topic));
    topic->cy = cy;

    if (!compose_topic_name(cy->namespace_, cy->name, name, topic->name)) {
        goto bad_name;
    }
    topic->name[CY_TOPIC_NAME_MAX] = '\0';
    const struct wkv_str_t key     = wkv_key(topic->name);

    topic->hash      = topic_hash(key);
    topic->evictions = 0; // starting from the preferred subject-ID.
    topic->age       = 0;
    topic->aged_at   = cy_now(cy);

    topic->pub_transfer_id = random_u64(cy); // https://forum.opencyphal.org/t/improve-the-transfer-id-timeout/2375
    topic->pub_count       = 0;

    topic->couplings  = NULL;
    topic->subscribed = false;

    cy->last_event_ts = cy->last_local_event_ts = topic->last_event_ts = topic->last_local_event_ts = cy_now(cy);

    if ((key.len == 0) || (key.len > CY_TOPIC_NAME_MAX) || (cy->topic_count >= CY_TOPIC_SUBJECT_COUNT)) {
        goto bad_name;
    }

    topic->index_name = wkv_set(&cy->topics_by_name, key);
    if (topic->index_name == NULL) {
        goto oom;
    }
    assert(topic->index_name->value == NULL); // Cannot invoke this if such topic already exists!
    topic->index_name->value = topic;

    // Insert the new topic into the name index tree. If it's not unique, bail out.
    const struct cy_tree_t* const res_tree =
      cavl2_find_or_insert(&cy->topics_by_hash, &topic->hash, &cavl_comp_topic_hash, topic, &cavl2_trivial_factory);
    assert(res_tree == &topic->index_hash); // Cannot invoke this if such topic already exists!

    // Ensure the topic is in the gossip index. This is needed for allocation.
    topic->last_gossip = 0;
    (void)cavl2_find_or_insert(&cy->topics_by_gossip_time,
                               &topic->last_gossip,
                               &cavl_comp_topic_gossip_time,
                               topic,
                               &cavl_factory_topic_gossip_time);

    // Allocate a subject-ID for the topic and insert it into the subject index tree.
    // Pinned topics all have canonical names, and we have already ascertained that the name is unique,
    // meaning that another pinned topic is not occupying the same subject-ID.
    // Remember that topics arbitrate locally the same way they do externally, meaning that adding a new local topic
    // may displace another local one.
    topic_allocate(topic, 0, true);

    if (out_topic != NULL) {
        *out_topic = topic;
    }
    cy->topic_count++;
    CY_TRACE(cy,
             "🆕'%s' #%016llx @%04x: topic_count=%zu",
             topic->name,
             (unsigned long long)topic->hash,
             cy_topic_subject_id(topic),
             cy->topic_count);
    return 0;

oom: // TODO correct deinitialization
    cy->platform->topic_destroy(topic);
    return -CY_ERR_NAME;

bad_name: // TODO correct deinitialization
    cy->platform->topic_destroy(topic);
    return -CY_ERR_NAME;
}

static cy_err_t topic_ensure(struct cy_t* const cy, struct cy_topic_t** const out_topic, const char* const name)
{
    return (cy_topic_find_by_name(cy, name) == NULL) ? 0 : topic_new(cy, out_topic, name);
}

/// Create a new coupling between a topic and a subscriber.
/// Allocates new memory for the coupling, which may fail.
/// Don't forget topic_ensure_subscribed() afterward if necessary.
/// The substitutions must not lose validity until the topic is destroyed.
static cy_err_t topic_couple(struct cy_t* const                 cy,
                             struct cy_topic_t* const           topic,
                             struct cy_subscriber_root_t* const subr,
                             const size_t                       substitution_count,
                             const struct wkv_substitution_t*   substitutions)
{
    // Allocate the new coupling object with the substitutions flex array.
    // Each topic keeps its own couplings because the sets of subscription names and topic names are orthogonal.
    struct cy_topic_coupling_t* const cpl = (struct cy_topic_coupling_t*)mem_alloc(
      cy,
      offsetof(struct cy_topic_coupling_t, substitutions) + (substitution_count * sizeof(struct cy_substitution_t)));
    if (cpl != NULL) {
        cpl->root               = subr;
        cpl->next               = topic->couplings;
        topic->couplings        = cpl;
        cpl->substitution_count = substitution_count;
        // When we copy the substitutions, we assume that the lifetime of the substituted string segments is at least
        // the same as the lifetime of the topic, which is true because the substitutions point into the topic name
        // string, which is part of the topic object.
        const struct wkv_substitution_t* s = substitutions;
        for (size_t i = 0U; s != NULL; i++) {
            assert(i < cpl->substitution_count);
            cpl->substitutions[i] = (struct cy_substitution_t){ .str = s->str, .ordinal = s->ordinal };
            s                     = s->next;
        }
    }
    return (cpl == NULL) ? -CY_ERR_MEMORY : 0;
}

/// Returns non-NULL on OOM.
static void* wkv_cb_couple_new_topic(const struct wkv_event_t evt)
{
    struct cy_topic_t* const      topic = (struct cy_topic_t*)evt.context;
    struct cy_subscriber_t* const sub   = (struct cy_subscriber_t*)evt.node->value;
    const cy_err_t res = topic_couple(topic->cy, topic, sub->root, evt.substitution_count, evt.substitutions);
    return (0 == res) ? NULL : "";
}

/// If there is a wildcard subscriber matching the name of this topic, attempt to create a new subscription.
static void topic_subscribe_if_matching(struct cy_t* const cy, const struct wkv_str_t name)
{
    assert((cy != NULL) && (name.str != NULL));
    if (name.len == 0) {
        return; // Ensure the remote is not trying to feed us an empty name, that's bad.
    }
    if (NULL == wkv_route(&cy->subscribers_by_wildcard, name, NULL, wkv_cb_first)) {
        return; // No match.
    }
    // Create the new topic.
    struct cy_topic_t* topic = NULL;
    {
        const cy_err_t res = topic_new(cy, &topic, name.str);
        if (res < 0) {
            cy->platform->topic_handle_subscription_error(cy, NULL, res);
            return;
        }
    }
    // Attach subscriptions.
    if (NULL != wkv_route(&cy->subscribers_by_wildcard, name, topic, wkv_cb_couple_new_topic)) {
        // TODO discard the topic!
        cy->platform->topic_handle_subscription_error(cy, NULL, -CY_ERR_MEMORY);
        return;
    }
    // Create the transport subscription once at the end, considering the parameters from all subscribers.
    topic_ensure_subscribed(topic);
}

static void* wkv_cb_topic_mark_scout_response(const struct wkv_event_t evt)
{
    schedule_gossip((struct cy_topic_t*)evt.node->value, BIG_BANG + 10);
    return NULL;
}

// =====================================================================================================================
//                                                      HEARTBEAT
// =====================================================================================================================

#define TOPIC_FLAG_PUBLISHING 1U ///< Indicates that the source is actively publishing this topic.
#define TOPIC_FLAG_SUBSCRIBED 2U ///< Indicates that the source is subscribed to this topic.
#define TOPIC_FLAG_SCOUT      4U ///< This is a scout message requesting everyone who has matching topics to respond.

/// We could have used Nunavut, but we only need a single message and it's very simple, so we do it manually.
struct heartbeat_t
{
    uint32_t uptime;
    uint8_t  user_word[3]; ///< Used to be: health, mode, vendor-specific status code. Now opaque user-defined 24 bits.
    uint8_t  version;      ///< Union tag; Cyphal v1.0 -- 0; Cyphal v1.1 -- 1.
    // The following fields are conditional on version=1.
    uint64_t uid;
    uint64_t topic_hash;
    uint64_t topic_flags8_age56;
    uint64_t topic_name_length8_reserved16_evictions40;
    char     topic_name[CY_TOPIC_NAME_MAX];
};
static_assert(sizeof(struct heartbeat_t) == 128, "bad layout");

static cy_err_t publish_heartbeat(struct cy_t* const cy, const cy_us_t now, struct heartbeat_t* const message)
{
    message->uptime  = (uint32_t)((now - cy->started_at) / MEGA);
    message->version = 1;
    message->uid     = cy->uid;
    const size_t message_size =
      sizeof(*message) - (CY_TOPIC_NAME_MAX - (message->topic_name_length8_reserved16_evictions40 >> 56U));
    assert(message_size <= sizeof(message));
    assert((message->topic_name_length8_reserved16_evictions40 >> 56U) <= CY_TOPIC_NAME_MAX);
    const struct cy_buffer_borrowed_t payload = { .next = NULL, .view = { .data = message, .size = message_size } };
    assert(cy->node_id <= cy->platform->node_id_max);
    const cy_err_t pub_res = cy->platform->topic_publish(&cy->heartbeat_pub, now + HEARTBEAT_PUB_TIMEOUT_us, payload);
    cy->heartbeat_pub.topic->pub_transfer_id++;
    return pub_res;
}

static cy_err_t publish_heartbeat_gossip(struct cy_t* const cy, struct cy_topic_t* const topic, const cy_us_t now)
{
    topic_age(topic, now);
    topic_ensure_subscribed(topic); // use this opportunity to repair the subscription if broken
    const uint8_t flags = ((topic->pub_count > 0) ? TOPIC_FLAG_PUBLISHING : 0U) | //
                          ((topic->couplings != NULL) ? TOPIC_FLAG_SUBSCRIBED : 0U);
    // Possible optimization: we don't have to transmit the topic name if the message is urgent, i.e.,
    // if it is published in response to a divergent allocation or possibly a collision.
    struct heartbeat_t msg = {
        .topic_hash                                = topic->hash,
        .topic_flags8_age56                        = (((uint64_t)flags) << 56U) | topic->age,
        .topic_name_length8_reserved16_evictions40 = (((uint64_t)topic->index_name->key_len) << 56U) | topic->evictions,
    };
    memcpy(msg.topic_name, topic->name, topic->index_name->key_len);
    // Update gossip time even if failed so we don't get stuck publishing same gossip if error reporting is broken.
    update_last_gossip_time(topic, now);
    return publish_heartbeat(cy, now, &msg);
}

static cy_err_t publish_heartbeat_scout(struct cy_t* const cy, const cy_us_t now)
{
    struct cy_subscriber_root_t* subr = cy->next_scout;
    assert(subr != NULL);
    struct heartbeat_t msg = {
        .topic_hash         = 8185, // https://github.com/pavel-kirienko/cy/issues/12#issuecomment-2953184238
        .topic_flags8_age56 = (((uint64_t)TOPIC_FLAG_SCOUT) << 56U),
        .topic_name_length8_reserved16_evictions40 = (((uint64_t)subr->index_name->key_len) << 56U),
    };
    wkv_get_key(&cy->subscribers_by_name, subr->index_name, msg.topic_name);
    const cy_err_t res = publish_heartbeat(cy, now, &msg);
    if (res >= 0) {
        cy->next_scout = subr->next_scout; // delist the scout if publication succeeded
    }
    return res;
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void on_heartbeat(const struct cy_arrival_t* const evt)
{
    assert((evt->subscriber != NULL) && (evt->topic != NULL) && (evt->transfer != NULL));
    struct cy_t* const cy = evt->topic->cy;
    // Deserialize the message. TODO: deserialize properly.
    struct heartbeat_t heartbeat = { 0 };
    const size_t       msg_size  = cy_buffer_owned_gather(
      evt->transfer->payload, (struct cy_bytes_mut_t){ .size = sizeof(heartbeat), .data = &heartbeat });
    if ((msg_size < (sizeof(heartbeat) - CY_TOPIC_NAME_MAX)) || (heartbeat.version != 1)) {
        return;
    }
    const cy_us_t                        ts         = evt->transfer->timestamp;
    const struct cy_transfer_metadata_t* meta       = &evt->transfer->metadata;
    const uint64_t                       other_hash = heartbeat.topic_hash;
    const uint64_t         other_evictions = heartbeat.topic_name_length8_reserved16_evictions40 & ((1ULL << 40U) - 1U);
    const uint64_t         other_age       = heartbeat.topic_flags8_age56 & ((1ULL << 56U) - 1U);
    const uint8_t          flags           = (uint8_t)(heartbeat.topic_flags8_age56 >> 56U);
    const bool             is_scout        = (flags & TOPIC_FLAG_SCOUT) != 0U;
    const struct wkv_str_t key             = wkv_key(heartbeat.topic_name);
    if (!is_scout) {
        // Find the topic in our local database.
        struct cy_topic_t* mine = cy_topic_find_by_hash(cy, other_hash);
        if (mine != NULL) { // We have this topic! Check if we have consensus on the subject-ID.
            assert(mine->hash == other_hash);
            const int_fast8_t mine_lage  = log2_floor(mine->age);
            const int_fast8_t other_lage = log2_floor(other_age);
            if (mine->evictions != other_evictions) {
                CY_TRACE(cy,
                         "Topic '%s' #%016llx divergent allocation discovered via gossip from uid=%016llx nid=%04x:\n"
                         "\t local  @%04x evict=%llu log2(age=%llu)=%+d\n"
                         "\t remote @%04x evict=%llu log2(age=%llu)=%+d",
                         mine->name,
                         (unsigned long long)mine->hash,
                         (unsigned long long)heartbeat.uid,
                         meta->remote_node_id,
                         cy_topic_subject_id(mine),
                         (unsigned long long)mine->evictions,
                         (unsigned long long)mine->age,
                         mine_lage,
                         topic_subject_id(other_hash, other_evictions),
                         (unsigned long long)other_evictions,
                         (unsigned long long)other_age,
                         other_lage);
                assert(mine->evictions != other_evictions);
                if ((mine_lage > other_lage) || ((mine_lage == other_lage) && (mine->evictions > other_evictions))) {
                    CY_TRACE(cy, "We won, existing allocation not altered; expecting remote to adjust.");
                    schedule_gossip(mine, BIG_BANG);
                } else {
                    assert((mine_lage <= other_lage) &&
                           ((mine_lage < other_lage) || (mine->evictions < other_evictions)));
                    assert(mine_lage <= other_lage);
                    CY_TRACE(cy,
                             "We lost, reallocating the topic to try and match the remote, or offer new alternative.");
                    const cy_us_t old_last_gossip = mine->last_gossip;
                    mine->age                     = max_u64(mine->age, other_age);
                    topic_allocate(mine, other_evictions, false);
                    if (mine->evictions == other_evictions) { // perfect sync, no need to gossip
                        update_last_gossip_time(mine, old_last_gossip);
                    }
                    cy->last_local_event_ts = mine->last_local_event_ts = ts;
                }
                cy->last_event_ts = mine->last_event_ts = ts;
            } else {
                topic_ensure_subscribed(mine); // use this opportunity to repair the subscription if broken
            }
            mine->age = max_u64(mine->age, other_age);
        } else { // We don't know this topic; check for a subject-ID collision and do auto-subscription.
            topic_subscribe_if_matching(cy, key);
            mine = cy_topic_find_by_subject_id(cy, topic_subject_id(other_hash, other_evictions));
            if (mine == NULL) {
                return; // We are not using this subject-ID, no collision.
            }
            assert(cy_topic_subject_id(mine) == topic_subject_id(other_hash, other_evictions));
            const bool win = left_wins(mine, other_age, other_hash);
            CY_TRACE(cy,
                     "Topic collision 💥 @%04x discovered via gossip from uid=%016llx nid=%04x; we %s. Contestants:\n"
                     "\t local  #%016llx evict=%llu log2(age=%llx)=%+d '%s'\n"
                     "\t remote #%016llx evict=%llu log2(age=%llx)=%+d '%s'",
                     cy_topic_subject_id(mine),
                     (unsigned long long)heartbeat.uid,
                     meta->remote_node_id,
                     (win ? "WIN" : "LOSE"),
                     (unsigned long long)mine->hash,
                     (unsigned long long)mine->evictions,
                     (unsigned long long)mine->age,
                     log2_floor(mine->age),
                     mine->name,
                     (unsigned long long)other_hash,
                     (unsigned long long)other_evictions,
                     (unsigned long long)other_age,
                     log2_floor(other_age),
                     heartbeat.topic_name);
            // We don't need to do anything if we won, but we need to announce to the network (in particular to the
            // infringing node) that we are using this subject-ID, so that the loser knows that it has to move.
            // If we lost, we need to gossip this topic ASAP as well because every other participant on this topic
            // will also move, but the trick is that the others could have settled on different subject-IDs.
            // Everyone needs to publish their own new allocation and then we will pick max subject-ID out of that.
            if (!win) {
                topic_allocate(mine, mine->evictions + 1U, false);
                cy->last_local_event_ts = mine->last_local_event_ts = ts;
            } else {
                schedule_gossip(mine, BIG_BANG);
            }
            cy->last_event_ts = mine->last_event_ts = ts;
        }
    } else {
        // A scout message is simply asking us to check if we have any matching topics, and gossip them ASAP if so.
        (void)wkv_match(&cy->topics_by_name, key, NULL, wkv_cb_topic_mark_scout_response);
    }
}

// =====================================================================================================================
//                                                      PUBLISHER
// =====================================================================================================================

static void retire_timed_out_futures(struct cy_t* cy, const cy_us_t now)
{
    struct cy_future_t* fut = (struct cy_future_t*)cavl2_min(cy->futures_by_deadline);
    while ((fut != NULL) && (fut->deadline < now)) {
        assert(fut->state == cy_future_pending);
        cavl2_remove(&cy->futures_by_deadline, &fut->index_deadline);
        cavl2_remove(&fut->publisher->topic->futures_by_transfer_id, &fut->index_transfer_id);
        fut->state = cy_future_failure;
        if (fut->callback != NULL) {
            fut->callback(fut);
        }
        // We could have trivially avoided having to search the tree again by replacing this with a
        // cavl2_next_greater(), which is very efficient, but the problem here is that the user callback may modify
        // the tree unpredictably, and we don't want to put constraints on the callback behavior.
        // A more sophisticated solution is to mark the tree as modified, but it's not worth the effort.
        fut = (struct cy_future_t*)cavl2_min(cy->futures_by_deadline);
    }
}

cy_err_t cy_advertise(struct cy_publisher_t* const pub, struct cy_t* const cy, const char* const name)
{
    assert((pub != NULL) && (cy != NULL) && (name != NULL));
    memset(pub, 0, sizeof(*pub));
    cy_err_t res  = 0;
    pub->topic    = cy_topic_find_by_name(cy, name);
    pub->priority = cy_prio_nominal;
    pub->user     = NULL;
    if (pub->topic == NULL) {
        res = topic_new(cy, &pub->topic, name);
    }
    if (res >= 0) {
        assert(pub->topic != NULL);
        pub->topic->pub_count++;
    }
    return res;
}

void cy_future_new(struct cy_future_t* const future, const cy_response_callback_t callback, void* const user)
{
    assert(future != NULL);
    memset(future, 0, sizeof(*future));
    future->state    = cy_future_pending;
    future->callback = callback;
    future->user     = user;
}

cy_err_t cy_publish(struct cy_publisher_t* const      pub,
                    const cy_us_t                     tx_deadline,
                    const struct cy_buffer_borrowed_t payload,
                    const cy_us_t                     response_deadline,
                    struct cy_future_t* const         future)
{
    assert(pub != NULL);
    struct cy_topic_t* const topic = pub->topic;
    assert(topic != NULL);
    assert(topic->pub_count > 0);
    struct cy_t* const cy = topic->cy;
    assert(cy != NULL);

    // Set up the response future first. If publication fails, we will have to undo it later.
    // The reason we can't do it afterward is that if the transport has a cyclic transfer-ID, insertion may fail if
    // we have exhausted the transfer-ID set.
    if (future != NULL) {
        future->index_deadline     = (struct cy_tree_t){ 0 };
        future->index_transfer_id  = (struct cy_tree_t){ 0 };
        future->publisher          = pub;
        future->state              = cy_future_pending;
        future->transfer_id_masked = topic->pub_transfer_id & cy->platform->transfer_id_mask;
        future->deadline           = response_deadline;
        future->last_response      = (struct cy_transfer_owned_t){ 0 };
        // NB: we don't touch the callback and the user pointer, as they are to be initialized by the user.
        const struct cy_tree_t* const tr = cavl2_find_or_insert(&topic->futures_by_transfer_id,
                                                                &future->transfer_id_masked,
                                                                &cavl_comp_future_transfer_id_masked,
                                                                future,
                                                                &cavl_factory_future_transfer_id);
        if (tr != &future->index_transfer_id) {
            return -CY_ERR_CAPACITY;
        }
    }

    const cy_err_t res = cy->platform->topic_publish(pub, tx_deadline, payload);

    if (future != NULL) {
        if (res >= 0) {
            const struct cy_tree_t* const tr = cavl2_find_or_insert(&cy->futures_by_deadline,
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
void* wkv_cb_couple_new_subscription(const struct wkv_event_t evt)
{
    struct cy_subscriber_t* const sub   = (struct cy_subscriber_t*)evt.context;
    struct cy_topic_t* const      topic = (struct cy_topic_t*)evt.node->value;

    // If the new subscription parameters are different, we will need to resubscribe this topic.
    bool resubscribe = false;
    if (topic->subscribed) {
        const struct cy_subscription_params_t param_old = deduce_subscription_params(topic);
        const struct cy_subscription_params_t param_new = sub->params;
        resubscribe = (param_new.extent > param_old.extent) || //-------------------------------------
                      (param_new.transfer_id_timeout > param_old.transfer_id_timeout);
    }

    // Create the coupling.
    const cy_err_t res = topic_couple(topic->cy, topic, sub->root, evt.substitution_count, evt.substitutions);

    // Refresh the subscription if needed. Due to the new coupling, the params are now different.
    if (res >= 0) {
        if (resubscribe) {
            topic->cy->platform->topic_unsubscribe(topic);
            topic->subscribed = false;
        }
        topic_ensure_subscribed(topic);
    }

    return (0 == res) ? NULL : "";
}

/// Either finds an existing subscriber root or creates a new one. NULL if OOM.
static cy_err_t ensure_subscriber_root(struct cy_t* const                  cy,
                                       const struct wkv_str_t              key,
                                       struct cy_subscriber_root_t** const out_root)
{
    assert((cy != NULL) && (key.str != NULL) && (key.len > 0U) && (out_root != NULL));

    // Find or allocate a tree node.
    struct wkv_node_t* const node = wkv_set(&cy->subscribers_by_name, key);
    if (node == NULL) {
        return -CY_ERR_MEMORY;
    }

    // If exists, return as is.
    if (node->value != NULL) {
        *out_root = (struct cy_subscriber_root_t*)node->value;
        return 0;
    }

    // Otherwise, allocate a new root, if possible.
    node->value = mem_alloc(cy, sizeof(struct cy_subscriber_root_t));
    if (node->value == NULL) {
        wkv_del(&cy->subscribers_by_name, node);
        return -CY_ERR_MEMORY;
    }
    struct cy_subscriber_root_t* const root = (struct cy_subscriber_root_t*)node->value;
    memset(root, 0, sizeof(*root));

    // Insert the new root into the indexes.
    const bool wc    = is_wildcard(key.str);
    root->index_name = node;
    if (wc) {
        root->index_wildcard = wkv_set(&cy->subscribers_by_wildcard, key);
        if (root->index_wildcard == NULL) {
            wkv_del(&cy->subscribers_by_name, node);
            mem_free(cy, node->value);
            return -CY_ERR_MEMORY;
        }
        assert(root->index_wildcard->value == NULL);
        root->index_wildcard->value = root;
    } else {
        root->index_wildcard = NULL;
        const cy_err_t res   = topic_ensure(cy, NULL, key.str);
        if (res < 0) {
            wkv_del(&cy->subscribers_by_name, node);
            mem_free(cy, node->value);
            return res;
        }
    }

    // Register the next pending scout. We do it strictly in the FIFO order.
    if (wc) {
        struct cy_subscriber_root_t* next_scout = cy->next_scout;
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
    return 0;
}

cy_err_t cy_subscribe_with_params(struct cy_subscriber_t* const         sub,
                                  struct cy_t* const                    cy,
                                  const char* const                     name,
                                  const struct cy_subscription_params_t params,
                                  const cy_subscriber_callback_t        callback)
{
    if ((sub == NULL) || (cy == NULL) || (name == NULL) || (params.transfer_id_timeout < 0) || (callback == NULL)) {
        return -CY_ERR_ARGUMENT;
    }
    char name_buf[CY_TOPIC_NAME_MAX + 1U];
    if (!compose_topic_name(cy->namespace_, cy->name, name, name_buf)) {
        return -CY_ERR_NAME;
    }
    const struct wkv_str_t key = wkv_key(name_buf);
    (void)memset(sub, 0, sizeof(*sub));
    const cy_err_t res = ensure_subscriber_root(cy, key, &sub->root);
    if (res < 0) {
        return res;
    }
    assert(sub->root != NULL);
    sub->params     = params;
    sub->callback   = callback;
    sub->next       = sub->root->head;
    sub->root->head = sub;
    if (NULL != wkv_match(&cy->topics_by_name, key, sub, wkv_cb_couple_new_subscription)) {
        cy_unsubscribe(cy, sub);
        return -CY_ERR_MEMORY;
    }
    return 0;
}

cy_err_t cy_respond(struct cy_topic_t* const            topic,
                    const cy_us_t                       tx_deadline,
                    const struct cy_transfer_metadata_t metadata,
                    const struct cy_buffer_borrowed_t   payload)
{
    assert(topic != NULL);
    /// Yes, we send the response using a request transfer. In the future we may leverage this for reliable delivery.
    /// All responses are sent to the same RPC service-ID; they are discriminated by the topic hash.
    return topic->cy->platform->request(topic->cy,
                                        CY_RPC_SERVICE_ID_TOPIC_RESPONSE,
                                        metadata,
                                        tx_deadline,
                                        (struct cy_buffer_borrowed_t){
                                          .next = &payload,
                                          .view = { .size = 8U, .data = &topic->hash },
                                        });
}

void cy_subscriber_name(struct cy_t* const cy, const struct cy_subscriber_t* const sub, char* const out_name)
{
    wkv_get_key(&cy->subscribers_by_name, sub->root->index_name, out_name);
}

// =====================================================================================================================
//                                                      TOPIC
// =====================================================================================================================

void cy_topic_hint(struct cy_topic_t* const topic, const uint16_t subject_id)
{
    if ((topic != NULL) && (subject_id < CY_TOTAL_SUBJECT_COUNT) && (!is_pinned(topic->hash)) && (topic->age == 0)) {
        // Fit the lowest evictions counter such that we land at the specified subject-ID.
        // Avoid negative remainders, so we don't use simple evictions=(subject_id-hash)%6144.
        while (topic_subject_id(topic->hash, topic->evictions) != subject_id) {
            topic->evictions++;
        }
    }
}

struct cy_topic_t* cy_topic_find_by_name(const struct cy_t* const cy, const char* const name)
{
    assert((cy != NULL) && (name != NULL));
    struct wkv_node_t* const node  = wkv_get(&cy->topics_by_name, wkv_key(name));
    struct cy_topic_t* const topic = (node != NULL) ? (struct cy_topic_t*)node->value : NULL;
    assert(topic == cy_topic_find_by_hash(cy, topic_hash(wkv_key(name))));
    return topic;
}

struct cy_topic_t* cy_topic_find_by_hash(const struct cy_t* const cy, const uint64_t hash)
{
    assert(cy != NULL);
    struct cy_topic_t* const topic = (struct cy_topic_t*)cavl2_find(cy->topics_by_hash, &hash, &cavl_comp_topic_hash);
    if (topic == NULL) {
        return NULL;
    }
    assert(topic->hash == hash);
    assert(topic->cy == cy);
    return topic;
}

struct cy_topic_t* cy_topic_find_by_subject_id(const struct cy_t* const cy, const uint16_t subject_id)
{
    assert(cy != NULL);
    struct cy_tree_t* const t = cavl2_find(cy->topics_by_subject_id, &subject_id, &cavl_comp_topic_subject_id);
    if (t == NULL) {
        return NULL;
    }
    struct cy_topic_t* topic = CAVL2_TO_OWNER(t, struct cy_topic_t, index_subject_id);
    assert(cy_topic_subject_id(topic) == subject_id);
    assert(topic->cy == cy);
    return topic;
}

struct cy_topic_t* cy_topic_iter_first(const struct cy_t* const cy)
{
    return (struct cy_topic_t*)cavl2_min(cy->topics_by_hash);
}

struct cy_topic_t* cy_topic_iter_next(struct cy_topic_t* const topic)
{
    return (struct cy_topic_t*)cavl2_next_greater(&topic->index_hash);
}

uint16_t cy_topic_subject_id(const struct cy_topic_t* const topic)
{
    return topic_subject_id(topic->hash, topic->evictions);
}

struct wkv_str_t cy_topic_name(const struct cy_topic_t* const topic)
{
    return (struct wkv_str_t){ .len = topic->index_name->key_len, .str = topic->name };
}

// =====================================================================================================================
//                                                      NODE
// =====================================================================================================================

cy_err_t cy_new(struct cy_t* const                cy,
                const struct cy_platform_t* const platform,
                const uint64_t                    uid,
                const uint16_t                    node_id,
                const char* const                 namespace_)
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
    assert(platform->request != NULL);
    assert(platform->topic_new != NULL);
    assert(platform->topic_destroy != NULL);
    assert(platform->topic_publish != NULL);
    assert(platform->topic_subscribe != NULL);
    assert(platform->topic_unsubscribe != NULL);
    assert(platform->topic_handle_subscription_error != NULL);
    assert((platform->node_id_max > 0) && (platform->node_id_max < CY_NODE_ID_INVALID));

    // Init the object.
    memset(cy, 0, sizeof(*cy));
    cy->platform = platform;
    cy->uid      = uid;
    cy->node_id  = (node_id <= platform->node_id_max) ? node_id : CY_NODE_ID_INVALID;
    // namespace
    if ((namespace_ != NULL) && (namespace_[0] != '\0')) {
        const size_t len = smaller(CY_NAMESPACE_NAME_MAX, strlen(namespace_));
        memcpy(cy->namespace_, namespace_, len);
        cy->namespace_[len] = '\0';
    } else {
        cy->namespace_[0] = '/'; // default namespace
        cy->namespace_[1] = '\0';
    }
    // the default name is just derived from UID, can be overridden by the user later
    (void)snprintf(cy->name,
                   sizeof(cy->name),
                   "%04x/%04x/%08lx/",
                   (unsigned)(uid >> 48U) & UINT16_MAX,
                   (unsigned)(uid >> 32U) & UINT16_MAX,
                   (unsigned long)(uid & UINT32_MAX));
    cy->topics_by_hash        = NULL;
    cy->topics_by_subject_id  = NULL;
    cy->topics_by_gossip_time = NULL;
    cy->next_scout            = NULL;
    cy->topic_count           = 0;
    cy->user                  = NULL;

    wkv_init(&cy->topics_by_name, &wkv_realloc);
    cy->topics_by_name.context = cy;

    wkv_init(&cy->subscribers_by_name, &wkv_realloc);
    cy->subscribers_by_name.context = cy;

    // Postpone calling the functions until after the object is set up.
    cy->started_at = cy_now(cy);

    struct cy_bloom64_t* const node_id_bloom = platform->node_id_bloom(cy);
    assert(node_id_bloom != NULL);
    assert(node_id_bloom->n_bits > 0);
    assert((node_id_bloom->n_bits % 64) == 0);
    bloom64_purge(node_id_bloom);

    // If a node-ID is given explicitly, we want to publish our heartbeat ASAP to speed up network convergence
    // and to claim the address; if it's already taken, we will want to cause a collision to move the other node,
    // because manually assigned addresses take precedence over auto-assigned ones.
    // If we are not given a node-ID, we need to first listen to the network.
    cy->heartbeat_period = HEARTBEAT_DEFAULT_PERIOD_us;
    cy->heartbeat_next   = cy->started_at;
    cy_err_t res         = 0;
    if (cy->node_id > cy->platform->node_id_max) {
        cy->heartbeat_next += (cy_us_t)random_uint(cy, CY_START_DELAY_MIN_us, CY_START_DELAY_MAX_us);
        cy->last_event_ts = cy->last_local_event_ts = cy->started_at;
    } else {
        bloom64_set(node_id_bloom, cy->node_id);
        assert(node_id_bloom->popcount == 1);
        res               = cy->platform->node_id_set(cy);
        cy->last_event_ts = cy->last_local_event_ts = 0;
    }

    // Pub/sub on the heartbeat topic.
    if (res >= 0) {
        res = cy_advertise(&cy->heartbeat_pub, cy, CY_CONFIG_HEARTBEAT_TOPIC_NAME);
        if (res >= 0) {
            res = cy_subscribe(
              &cy->heartbeat_sub, cy, CY_CONFIG_HEARTBEAT_TOPIC_NAME, sizeof(struct heartbeat_t), &on_heartbeat);
            if (res < 0) {
                cy_unadvertise(&cy->heartbeat_pub);
            }
        }
    }
    return res;
}

bool cy_joined(const struct cy_t* const cy)
{
    return cy->node_id <= cy->platform->node_id_max;
}

bool cy_ready(const struct cy_t* const cy)
{
    return cy_joined(cy) && ((cy_now(cy) - cy->last_event_ts) > (1 * MEGA));
}

cy_us_t cy_now(const struct cy_t* const cy)
{
    return cy->platform->now(cy);
}

// =====================================================================================================================
//                                                      BUFFERS
// =====================================================================================================================

void cy_buffer_owned_release(struct cy_t* const cy, struct cy_buffer_owned_t* const payload)
{
    if ((cy != NULL) && (payload != NULL) && (payload->origin.data != NULL)) {
        cy->platform->buffer_release(cy, *payload);
        // nullify the pointers to prevent double free
        payload->base.next   = NULL;
        payload->origin.size = 0;
        payload->origin.data = NULL;
    }
}

size_t cy_buffer_borrowed_size(const struct cy_buffer_borrowed_t payload)
{
    size_t                             out = 0;
    const struct cy_buffer_borrowed_t* p   = &payload;
    while (p != NULL) {
        out += p->view.size;
        p = p->next;
    }
    return out;
}

size_t cy_buffer_borrowed_gather(const struct cy_buffer_borrowed_t payload, const struct cy_bytes_mut_t dest)
{
    size_t offset = 0;
    if (NULL != dest.data) {
        const struct cy_buffer_borrowed_t* frag = &payload;
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

// ====================================================================================================================
// =================================================  END OF THE API  =================================================
// ====================================================================================================================

/// We snoop on all transfers to update the node-ID occupancy Bloom filter.
/// If we don't have a node-ID and this is a new Bloom entry, follow CSMA/CD: add random wait.
/// The point is to reduce the chances of multiple nodes appearing simultaneously and claiming same node-IDs.
/// We keep tracking neighbors even if we have a node-ID in case we encounter a collision later and need to move.
static void mark_neighbor(struct cy_t* const cy, const uint16_t remote_node_id)
{
    struct cy_bloom64_t* const bloom = cy->platform->node_id_bloom(cy);
    assert((bloom != NULL) && (bloom->n_bits > 0) && ((bloom->n_bits % 64) == 0) && (bloom->popcount <= bloom->n_bits));
    // A large population count indicates that the filter contains tombstones (marks for nodes that have left the
    // network). We can't remove them individually, so we purge the filter and start over.
    const bool bloom_congested = bloom->popcount > ((bloom->n_bits * 31ULL) / 32U);
    if (bloom_congested) {
        CY_TRACE(cy, "Bloom filter congested: popcount=%zu; purging to remove tombstones", bloom->popcount);
        bloom64_purge(bloom);
        assert(bloom->popcount == 0);
    }
    if ((cy->node_id > cy->platform->node_id_max) && !bloom64_get(bloom, remote_node_id)) {
        cy->heartbeat_next += (cy_us_t)random_uint(cy, 0, 2 * MEGA);
        CY_TRACE(cy, "🔭 Discovered neighbor %04x; new Bloom popcount %zu", remote_node_id, bloom->popcount + 1U);
    }
    bloom64_set(bloom, remote_node_id);
}

void cy_ingest_topic_transfer(struct cy_topic_t* const topic, struct cy_transfer_owned_t transfer)
{
    assert(topic != NULL);
    struct cy_t* const cy = topic->cy;

    mark_neighbor(cy, transfer.metadata.remote_node_id);

    // Experimental: age the topic with received transfers. Not with the published ones because we don't want
    // unconnected publishers to inflate the age.
    topic->age++;

    // Simply invoke all callbacks that match this topic name.
    // The callback may unsubscribe, so we have to store the next pointer early.
    const struct cy_topic_coupling_t* cpl = topic->couplings;
    while (cpl != NULL) {
        struct cy_subscriber_t* sub = cpl->root->head;
        assert(sub != NULL);
        const struct cy_topic_coupling_t* const next_cpl = cpl->next;
        struct cy_subscriber_t* const           next_sub = sub->next;
        while (sub != NULL) {
            const struct cy_arrival_t evt = { .subscriber         = sub,
                                              .topic              = topic,
                                              .transfer           = &transfer,
                                              .substitution_count = cpl->substitution_count,
                                              .substitutions      = cpl->substitutions };
            sub->callback(&evt);
            sub = next_sub;
        }
        cpl = next_cpl;
    }

    // Release the payload at the end, unless the subscriber(s) took ownership of it.
    if (transfer.payload.base.view.data != NULL) {
        cy->platform->buffer_release(cy, transfer.payload);
    }
}

void cy_ingest_topic_response_transfer(struct cy_t* const cy, struct cy_transfer_owned_t transfer)
{
    assert(cy != NULL);
    mark_neighbor(cy, transfer.metadata.remote_node_id);

    // TODO: proper deserialization. This fails if the first <8 bytes are fragmented.
    if (transfer.payload.base.view.size < 8U) {
        cy->platform->buffer_release(cy, transfer.payload);
        return; // Malformed response. The first 8 bytes shall contain the full topic hash.
    }

    // Deserialize the topic hash. The rest of the payload is for the application.
    uint64_t topic_hash = 0;
    memcpy(&topic_hash, transfer.payload.base.view.data, sizeof(topic_hash));
    transfer.payload.base.view.size -= sizeof(topic_hash);
    transfer.payload.base.view.data = ((const char*)transfer.payload.base.view.data) + sizeof(topic_hash);

    // Find the topic -- log(N) lookup.
    struct cy_topic_t* const topic = cy_topic_find_by_hash(cy, topic_hash);
    if (topic == NULL) {
        cy->platform->buffer_release(cy, transfer.payload);
        return; // We don't know this topic, ignore it.
    }

    // Find the matching pending response future -- log(N) lookup.
    const uint64_t          transfer_id_masked = transfer.metadata.transfer_id & cy->platform->transfer_id_mask;
    struct cy_tree_t* const tr =
      cavl2_find(topic->futures_by_transfer_id, &transfer_id_masked, &cavl_comp_future_transfer_id_masked);
    if (tr == NULL) {
        cy->platform->buffer_release(cy, transfer.payload);
        return; // Unexpected or duplicate response. TODO: Linger completed futures for multiple responses?
    }
    struct cy_future_t* const fut = CAVL2_TO_OWNER(tr, struct cy_future_t, index_transfer_id);
    assert(fut->state == cy_future_pending); // TODO Linger completed futures for multiple responses?

    // Finalize and retire the future.
    fut->state = cy_future_success;
    cy_buffer_owned_release(cy, &fut->last_response.payload); // does nothing if already released
    fut->last_response = transfer;
    cavl2_remove(&cy->futures_by_deadline, &fut->index_deadline);
    cavl2_remove(&topic->futures_by_transfer_id, &fut->index_transfer_id);
    if (fut->callback != NULL) {
        fut->callback(fut);
    }
}

cy_err_t cy_update(struct cy_t* const cy)
{
    cy_err_t      res = 0;
    const cy_us_t now = cy_now(cy);

    retire_timed_out_futures(cy, now);

    if (cy->node_id_collision) {
        CY_TRACE(cy, "Processing the delayed node-ID collision event now.");
        cy->node_id_collision = false;
        if (cy->node_id <= cy->platform->node_id_max) {
            cy->node_id = CY_NODE_ID_INVALID;
            cy->platform->node_id_clear(cy);
            cy->heartbeat_next = now;
        }
    }

    if (now >= cy->heartbeat_next) {
        // If it is time to publish a heartbeat but we still don't have a node-ID, it means that it is time to allocate!
        if (cy->node_id >= cy->platform->node_id_max) {
            struct cy_bloom64_t* const bloom = cy->platform->node_id_bloom(cy);
            assert((bloom != NULL) && (bloom->n_bits > 0) && ((bloom->n_bits % 64) == 0) &&
                   (bloom->popcount <= bloom->n_bits));
            // Pick the node-ID using the most recent state of the Bloom filter.
            cy->node_id = pick_node_id(cy, bloom, cy->platform->node_id_max);
            assert(cy->node_id <= cy->platform->node_id_max);
            res = cy->platform->node_id_set(cy);
            CY_TRACE(
              cy, "Picked own node-ID %04x; Bloom popcount %zu; node_id_set()->%d", cy->node_id, bloom->popcount, res);
        }
        assert(cy->node_id <= cy->platform->node_id_max);
        if (res < 0) {
            return res; // Failed to set node-ID, bail out. Will try again next time.
        }

        // Find the next topic to gossip.
        const struct cy_tree_t* const t = cavl2_min(cy->topics_by_gossip_time);
        assert(t != NULL); // We always have at least the heartbeat topic.
        struct cy_topic_t* tp = CAVL2_TO_OWNER(t, struct cy_topic_t, index_gossip_time);
        // If this is not an urgent gossip and we have pending scouts, prefer the scouts.
        if ((tp->last_gossip > 0) && (cy->next_scout != NULL)) {
            tp = NULL;
        }

        // Publish the heartbeat.
        if (tp != NULL) {
            res = publish_heartbeat_gossip(cy, tp, now);
        } else {
            res = publish_heartbeat_scout(cy, now);
        }

        // Schedule the next one.
        // If this heartbeat failed to publish, we simply give up and move on to try again in the next period.
        assert(cy->topic_count > 0);                // we always have at least the heartbeat topic
        cy->heartbeat_next += cy->heartbeat_period; // Do not accumulate heartbeat phase slip!
    }
    return res;
}

void cy_notify_topic_hash_collision(struct cy_topic_t* const topic)
{
    // Schedule the topic for gossiping ASAP, unless it is already scheduled.
    if ((topic != NULL) && (topic->last_gossip > 0)) {
        CY_TRACE(topic->cy, "💥 '%s'@%04x", topic->name, cy_topic_subject_id(topic));
        // Topics with the same time will be ordered FIFO -- the tree is stable.
        schedule_gossip(topic, BIG_BANG);
        // We could subtract the heartbeat period from the next heartbeat time to make it come out sooner,
        // but this way we would generate unpredictable network loading. We probably don't want that.
    }
}

void cy_notify_node_id_collision(struct cy_t* const cy)
{
    assert(cy != NULL);
    if (!cy->node_id_collision) {
        cy->node_id_collision = true;
        CY_TRACE(cy, "💥 node-ID %04x", cy->node_id);
    }
}
