///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// Platform-side API of the Cy library.
///
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#pragma once

#include "cy.h"

// =====================================================================================================================
//                                              BUILD TIME CONFIG OPTIONS
// =====================================================================================================================

/// Only for testing and debugging purposes; never redefine in production builds.
/// All nodes obviously must use the same heartbeat topic, which is why it is pinned.
#define CY_HEARTBEAT_TOPIC_NAME "/#1d55"

/// Only for testing and debugging purposes.
/// Makes all non-pinned topics prefer the same subject-ID that equals the value of this macro,
/// which maximizes topic allocation collisions. Pinned topics are unaffected.
/// This can be used to stress-test the consensus algorithm.
/// This value shall be identical for all nodes in the network; otherwise, divergent allocations will occur.
#ifndef CY_CONFIG_PREFERRED_TOPIC_OVERRIDE
// Not defined by default; the normal subject expression is used instead: subject_id=(hash+evictions)%6144
#endif

/// If CY_CONFIG_TRACE is defined and is non-zero, cy_trace() shall be defined externally.
#ifndef CY_CONFIG_TRACE
#define CY_CONFIG_TRACE 0
#endif
#if CY_CONFIG_TRACE
#define CY_TRACE(cy, ...) cy_trace(cy, __FILE__, __LINE__, __func__, __VA_ARGS__)
#else
#define CY_TRACE(cy, ...) (void)cy
#endif

#ifdef __cplusplus
extern "C"
{
#endif

typedef struct cy_list_member_t cy_list_member_t;
struct cy_list_member_t
{
    cy_list_member_t* next;
    cy_list_member_t* prev;
};
typedef struct cy_list_t
{
    cy_list_member_t* head; ///< NULL if list empty
    cy_list_member_t* tail; ///< NULL if list empty
} cy_list_t;

/// This is the base type that is extended by the platform layer with transport- and platform-specific entities,
/// such as socket handles, etc. Instantiation is therefore done inside the platform layer in the heap or some
/// other dynamic storage. The user code is not expected to interact with the topic type, and the only reason it is
/// defined in the header file is to allow the platform layer to use it.
///
/// A topic name is suffixed to the namespace name of the node that owns it, unless it begins with a `/`.
/// The leading `~` in the name is replaced with the local node name, which is set during node initialization.
/// Repeated and trailing slashes are removed.
///
/// A topic that is only used by pattern subscriptions (like `ins/?/data/*`, without publishers or explicit
/// subscriptions) is called implicit. Such topics are automatically retired when they see no traffic and
/// no gossips from publishers or receiving subscribers for implicit_topic_timeout.
/// This is needed to prevent implicit pattern subscriptions from lingering forever when all publishers are gone.
/// See https://github.com/pavel-kirienko/cy/issues/15.
///
/// CRDT merge rules, first rule takes precedence:
/// - on collision (same subject-ID, different hash):
///     1. winner is pinned;
///     2. winner is older;
///     3. winner has smaller hash.
/// - on divergence (same hash, different subject-ID):
///     1. winner is older;
///     2. winner has seen more evictions (i.e., larger subject-ID mod max_topics).
/// When a topic is reallocated, it retains its current age.
/// Conflict resolution may result in a temporary jitter if it happens to occur near log2(age) integer boundary.
typedef struct cy_topic_t
{
    /// All indexes that this topic is a member of. Indexes are very fast log(N) lookup structures.
    cy_tree_t   index_hash; ///< Hash index handle MUST be the first field.
    cy_tree_t   index_subject_id;
    wkv_node_t* index_name;

    /// All lists that this topic is a member of. Lists are used for ordering with fast constant-time insertion/removal.
    cy_list_member_t list_implicit;      ///< Last animated topic is at the end of the list.
    cy_list_member_t list_gossip_urgent; ///< High-priority gossips. Fetch from the tail.
    cy_list_member_t list_gossip;        ///< Normal-priority gossips. Fetch from the tail.

    /// The name length is stored in index_name.
    /// We need to store the full name to allow valid references from name substitutions during pattern matching.
    char name[CY_TOPIC_NAME_MAX + 1];

    /// Whenever a topic conflicts with another one locally, arbitration is performed, and the loser has its
    /// eviction counter incremented. The eviction counter is used as a Lamport clock counting the loss events.
    /// Higher clock wins because it implies that any lower value is non-viable since it has been known to cause
    /// at least one collision anywhere on the network. The counter MUST NOT BE CHANGED without removing the topic
    /// from the subject-ID index tree!
    uint64_t evictions;

    /// hash=rapidhash(topic_name). For a pinned topic, the hash equals its subject-ID.
    uint64_t hash;

    /// Event timestamps used for state management.
    cy_us_t ts_origin;   ///< An approximation of when the topic was first seen on the network.
    cy_us_t ts_animated; ///< Last time the topic saw activity that prevents it from being retired.

    /// Used for matching futures against received responses.
    /// The platform layer can access this too if needed.
    cy_tree_t* futures_by_transfer_id;

    /// Only used if the application publishes data on this topic.
    /// pub_count tracks the number of existing advertisements on this topic; when this number reaches zero
    /// and there are no live subscriptions, the topic will be garbage collected by Cy.
    uint64_t pub_transfer_id;
    size_t   pub_count;

    /// Only used if the application subscribes on this topic.
    struct cy_topic_coupling_t* couplings;
    bool subscribed; ///< May be (tentatively) false even with couplings!=NULL on resubscription error.
} cy_topic_t;

/// Returns the current monotonic time in microseconds. The initial time shall be non-negative.
typedef cy_us_t (*cy_platform_now_t)(const cy_t*);

/// The semantics are per the standard realloc from stdlib, except:
/// - If the fragment is not increased in size, reallocation MUST succeed.
/// - If the size is zero, it must behave like free() (which is often the case in realloc() but technically an UB).
typedef void* (*cy_platform_realloc_t)(cy_t*, void*, size_t);

/// Returns a random 64-bit unsigned integer.
/// A TRNG is preferred; if not available, a PRNG will suffice, but its initial state should be distinct across reboots,
/// and it should be hashed with the node's unique identifier.
///
/// A simple compliant solution that can be implemented in an embedded system without TRNG is:
///
///     static uint64_t g_prng_state __attribute__ ((section (".noinit")));
///     g_prng_state += 0xA0761D6478BD642FULL;                // add Wyhash seed (64-bit prime)
///     const uint64_t seed[2] = { g_prng_state, local_uid }; // if possible, add more entropy here, like ADC noise
///     return rapidhash(seed, sizeof(seed));
///
/// It is desirable to save the PRNG state in a battery-backed memory, if available; otherwise, in small MCUs one could
/// hash the entire RAM contents at startup to scavenge as much entropy as possible, or use ADC or clock noise.
/// If an RTC is available, then the following is sufficient:
///
///     static uint_fast16_t g_counter = 0;
///     const uint64_t seed[2] = {
///         ((uint64_t)rtc_get_time() << 16U) + ++g_counter,
///         local_uid,
///     }; // if possible, add more entropy here, like ADC noise
///     return rapidhash(seed, sizeof(seed));
typedef uint64_t (*cy_platform_random_t)(const cy_t*);

/// Return payload memory obtained with received transfers via cy_ingest*().
/// The head is passed by value so not freed, but its data and all other fragments are.
typedef void (*cy_platform_buffer_release_t)(cy_t*, cy_buffer_owned_t);

/// Instructs the underlying transport layer to send a peer-to-peer response transfer. The identity of the remote
/// endpoint is encoded inside the cy_response_context_t object in a platform-specific manner.
/// The transfer-ID is managed by the glue library internally; it is expected that the glue layer may need
/// access to the specific topic that this P2P transfer pertains to, so the reference to the topic is also provided.
///
/// Each acknowledgement transfer can be sent twice to reduce the risk of loss, since the loss of an acknowledgment
/// is costly in terms of bandwidth and latency.
///
/// The ack/response transfer payload is prefixed with a fixed-size header shown below in DSDL notation:
///
///     uint8  kind         # 0 -- message ack; 1 -- response ack; 2 -- response data.
///     void24              # Reserved
///     uint32 cookie       # A response ack shall contain the same cookie as in the response data header.
///     uint64 topic_hash   # The hash of the topic that the ack/response is for.
///     uint64 transfer_id  # The transfer-ID of the original message that this ack/response is for.
///     # If this is a response, the payload follows immediately after this header.
///     # Acks have no payload beyond the header.
///
/// Transfers with invalid kind shall be dropped.
typedef cy_err_t (*cy_platform_p2p_t)(cy_t*,
                                      cy_topic_t*,
                                      cy_response_context_t context,
                                      cy_prio_t             priority,
                                      cy_us_t               tx_deadline,
                                      cy_buffer_borrowed_t  payload,
                                      bool                  ack_required);

/// Allocates a new topic. NULL if out of memory.
typedef cy_topic_t* (*cy_platform_topic_new_t)(cy_t*);

typedef void (*cy_platform_topic_destroy_t)(cy_t*, cy_topic_t*);

/// Instructs the underlying transport layer to publish a new message on the topic.
/// The function shall not increment the transfer-ID counter; Cy will do it.
typedef cy_err_t (*cy_platform_topic_publish_t)(cy_t*, //
                                                cy_publisher_t*,
                                                cy_us_t,
                                                cy_buffer_borrowed_t,
                                                bool ack_required);

/// Instructs the underlying transport layer to create a new subscription on the topic.
typedef cy_err_t (*cy_platform_topic_subscribe_t)(cy_t*, cy_topic_t*, cy_subscription_params_t);

/// Instructs the underlying transport to destroy an existing subscription.
typedef void (*cy_platform_topic_unsubscribe_t)(cy_t*, cy_topic_t*);

/// Invoked when a new publisher is created on the topic.
/// The main purpose here is to communicate the response extent requested by this publisher to the platform layer,
/// allowing it to configure the RPC session accordingly.
/// The requested extent is adjusted for any protocol overheads, so that the platform layer does not have to handle it.
typedef void (*cy_platform_topic_advertise_t)(cy_t*, cy_topic_t*, size_t response_extent_with_overhead);

/// If a subject-ID collision or divergence are discovered, Cy may reassign the topic to a different subject-ID.
/// To do that, it will first unsubscribe the topic using the corresponding function,
/// and then invoke the subscription function to recreate the subscription with the new subject-ID.
/// The unsubscription function is infallible, but the subscription function may fail.
/// If it does, this callback will be invoked to inform the user about the failure,
/// along with the error code returned by the subscription function.
///
/// The callback is also used to report errors that occur when attempting to create a new topic that matches a
/// pattern subscriber; in this case, the topic pointer will be NULL.
///
/// Normally, the error handler does not need to do anything specific aside from perhaps logging/reporting the error.
/// Cy will keep attempting to repair the topic periodically when relevant heartbeats are received.
typedef void (*cy_platform_topic_on_subscription_error_t)(cy_t*, cy_topic_t*, const cy_err_t);

/// The platform- and transport-specific entities. These can be underpinned by libcanard, libudpard, libserard,
/// or any other transport library, plus the platform-specific logic.
/// None of the entities are mutable; instances of this struct are mostly intended to be static const singletons.
///
/// The platform layer implementations for cyclic-transfer-ID transports (specifically, Cyphal/CAN) must unroll
/// the transfer-ID counters into monotonic 64-bit counters that do not overflow. This is trivial to do for topics
/// but P2P ack/response transfers will contain transfer-ID values unrolled by the remote node, which may disagree
/// with the values we unrolled locally; this must be addressed by the platform layer by fusing the least significant
/// bits of the remote transfer-ID with the most significant bits of the local counter. To do that, the platform layer
/// will search the local topics and futures for the closest transfer-ID to the received one.
typedef struct cy_platform_t
{
    cy_platform_now_t            now;
    cy_platform_realloc_t        realloc;
    cy_platform_random_t         random;
    cy_platform_buffer_release_t buffer_release;

    cy_platform_p2p_t p2p;

    cy_platform_topic_new_t                   topic_new;
    cy_platform_topic_destroy_t               topic_destroy;
    cy_platform_topic_publish_t               topic_publish;
    cy_platform_topic_subscribe_t             topic_subscribe;
    cy_platform_topic_unsubscribe_t           topic_unsubscribe;
    cy_platform_topic_advertise_t             topic_advertise;
    cy_platform_topic_on_subscription_error_t topic_on_subscription_error;
} cy_platform_t;

/// There are only three functions (plus convenience wrappers) whose invocations may result in network traffic:
/// - cy_update()  -- heartbeat only, at most one per call.
/// - cy_publish() -- user transfers only.
/// - cy_respond() -- user transfers only.
/// Creation of a new topic may cause resubscription of any existing topics (all in the worst case).
typedef struct cy_t
{
    const cy_platform_t* platform; ///< Never NULL.

    /// Namespace is a prefix added to all topics created on this instance, unless the topic name starts with "/".
    /// Local node name is prefixed to the topic name if it starts with `~`.
    /// Note that the leading / and ~ are only used as directives when creating a topic; they are never actually present
    /// in the final topic name.
    char namespace_[CY_NAMESPACE_NAME_MAX + 1];
    char name[CY_NAMESPACE_NAME_MAX + 1];

    cy_us_t ts_started;

    /// Cannot be changed after startup. Must be the same for all nodes in the network.
    /// https://github.com/OpenCyphal-Garage/cy/issues/12#issuecomment-3577831960
    uint32_t subject_id_modulus;

    /// Heartbeat topic and related items.
    cy_publisher_t  heartbeat_pub;
    cy_subscriber_t heartbeat_sub;
    cy_us_t         heartbeat_period;
    cy_us_t         heartbeat_next;
    cy_us_t         heartbeat_next_urgent;

    cy_us_t implicit_topic_timeout;

    /// Topics are indexed in multiple ways for various lookups.
    /// Remember that pinned topics have small hash ≤8184, hence they are always on the left of the hash tree,
    /// and can be traversed quickly if needed.
    wkv_t      topics_by_name;       // Contains ALL topics, never empty since we always have at least the heartbeat.
    cy_tree_t* topics_by_hash;       // ditto
    cy_tree_t* topics_by_subject_id; // All except pinned, since they do not collide. May be empty.

    /// Topic lists for ordering.
    cy_list_t list_implicit;      ///< Most recently animated topic is at the head.
    cy_list_t list_gossip_urgent; ///< High-priority gossips. Newest at the head.
    cy_list_t list_gossip;        ///< Normal-priority gossips. Newest at the head.
    cy_list_t list_scout_pending; ///< Lists cy_subscriber_root_t that are due for gossiping.

    /// When a heartbeat is received, its topic name will be compared against the patterns,
    /// and if a match is found, a new subscription will be constructed automatically; if a new topic instance
    /// has to be created for that, such instance is called implicit. Implicit instances are retired automatically
    /// when there are no explicit counterparts left and there is no traffic on the topic for a while.
    /// The values of these tree nodes point to instances of cy_subscriber_root_t.
    wkv_t subscribers_by_name;    ///< Both explicit and patterns.
    wkv_t subscribers_by_pattern; ///< Only patterns for implicit subscriptions on heartbeat.

    uint32_t p2p_next_cookie;

    /// For detecting timed out futures. This index spans all topics.
    cy_tree_t* futures_by_deadline;
    /// The user can use this field for arbitrary purposes.
    void* user;
} cy_t;

/// The namespace may be NULL or empty, in which case it defaults to `~`.
/// It may begin with `~`, which expands into the node name.
/// The node name should be unique in the network; one way to ensure this is to default it to the node UID as hex.
cy_err_t cy_new(cy_t* const                cy,
                const cy_platform_t* const platform,
                const wkv_str_t            name,
                const wkv_str_t            namespace_,
                const uint32_t             subject_id_modulus);
void     cy_destroy(cy_t* const cy);

/// This function must be invoked periodically to let the library publish heartbeats and handle response timeouts.
/// The most efficient invocation schedule is guided by cy->heartbeat_next_urgent, but not less often than every 10 ms;
/// if fixed-rate updates are desired, then the recommended period is 1 millisecond.
///
/// This is the only function that generates heartbeat -- the only kind of auxiliary traffic needed by the protocol.
/// The returned value indicates the success of the heartbeat publication, if any took place, or zero.
///
/// Excluding the transport_publish dependency, the time complexity is logarithmic in the number of topics.
cy_err_t cy_update(cy_t* const cy);

/// When the transport library detects a topic hash mismatch, it will notify Cy about it to let it rectify the problem.
/// Transport frames with mismatched topic hash must be dropped; no processing at the transport layer is needed.
/// This function is not essential for the protocol to function, but it speeds up collision repair.
///
/// The function will not perform any IO and will return immediately after quickly updating an internal state.
/// It is thus safe to invoke it from a deep callback or from deep inside the transport library; the side effects
/// are confined to the Cy state only. The time complexity is logarithmic in the number of topics.
///
/// If the transport library is unable to efficiently find the topic when a collision is found, use
/// cy_topic_find_by_subject_id(). The function has no effect if the topic is NULL; it is not an error to call it
/// with NULL to simplify chaining like:
///     cy_notify_topic_collision(cy, cy_topic_find_by_subject_id(cy, collision_subject_id));
void cy_notify_topic_collision(cy_t* const cy, cy_topic_t* const topic);

/// This is invoked whenever a new transfer on the topic is received.
/// The library will dispatch it to the appropriate subscriber callbacks.
/// Excluding the callbacks, the time complexity is constant.
/// The transfer payload ownership is taken by this function.
void cy_ingest(cy_t* const cy, cy_topic_t* const topic, cy_transfer_owned_t transfer);

/// Report arrival of a P2P transfer from another node.
void cy_ingest_p2p(cy_t* const cy, cy_transfer_owned_t transfer);

/// For diagnostics and logging only. Do not use in embedded and real-time applications.
/// This function is only required if CY_CONFIG_TRACE is defined and is nonzero; otherwise it should be left undefined.
/// Other modules that build on Cy can also use it; e.g., transport-specific glue modules.
extern void cy_trace(cy_t* const         cy,
                     const char* const   file,
                     const uint_fast16_t line,
                     const char* const   func,
                     const char* const   format,
                     ...)
#if defined(__GNUC__) || defined(__clang__)
  __attribute__((__format__(__printf__, 5, 6)))
#endif
  ;

#ifdef __cplusplus
}
#endif
