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

/// Only for testing and debugging purposes.
/// All nodes obviously must use the same heartbeat topic, which is why it is pinned.
#ifndef CY_CONFIG_HEARTBEAT_TOPIC_NAME
#define CY_CONFIG_HEARTBEAT_TOPIC_NAME "/7509"
#endif

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

/// When a response to a received message is sent, it is delivered as an RPC request (sic) transfer to this service-ID.
/// The response user data is prefixed with 8 bytes of the full topic hash to which we are responding.
/// The receiver of the response will be able to match the response with a specific request using the transfer-ID.
///
/// We are using RPC request transfers to deliver responses because in the future we may want to use the unused
/// response transfer as a confirmation for reliable transport.
///
/// TODO: use RPC response transfers instead.
#define CY_RPC_SERVICE_ID_TOPIC_RESPONSE 510

/// This is the base type that is extended by the platform layer with transport- and platform-specific entities,
/// such as socket handles, etc. Instantiation is therefore done inside the platform layer in the heap or some
/// other dynamic storage. The user code is not expected to interact with the topic type, and the only reason it is
/// defined in the header file is to allow the platform layer to use it.
///
/// A topic name is suffixed to the namespace name of the node that owns it, unless it begins with a `/`.
/// The leading `~` in the name is replaced with `/vvvv/pppp/iiiiiiii`, where the letters represent hexadecimal
/// digits of the vendor ID, product ID, and instance ID of the node.
/// Repeated and trailing slashes are removed.
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
struct cy_topic_t
{
    struct cy_tree_t index_hash; ///< Hash index handle MUST be the first field.
    struct cy_tree_t index_subject_id;
    struct cy_tree_t index_gossip_time;

    struct wkv_node_t* index_name;

    /// The name length is stored in index_name.
    /// We need to store the full name to allow valid references from name substitutions during pattern matching.
    char name[CY_TOPIC_NAME_MAX + 1];

    /// Assuming we have 1000 topics, the probability of a topic name hash collision is:
    /// >>> from decimal import Decimal
    /// >>> n = 1000
    /// >>> d = Decimal(2**64)
    /// >>> 1 - ((d-1)/d) ** ((n*(n-1))//2)
    /// About 2.7e-14, or one in 37 trillion.
    /// For pinned topics, the name hash equals the subject-ID.
    uint64_t hash;

    /// Whenever a topic conflicts with another one locally, arbitration is performed, and the loser has its
    /// eviction counter incremented. The eviction counter is used as a Lamport clock counting the loss events.
    /// Higher clock wins because it implies that any lower value is non-viable since it has been known to cause
    /// at least one collision anywhere on the network. The counter MUST NOT BE CHANGED without removing the topic
    /// from the subject-ID index tree!
    /// Remember that the subject-ID is (for non-pinned topics): (hash+evictions)%topic_count.
    uint64_t evictions;

    /// Currently, the age is increased locally as follows:
    ///
    /// 1. When the topic is gossiped, but not more often than once per second.
    ///
    /// 2. Experimental and optional: When a transfer is received on the topic.
    ///    Not transmitted, though, to prevent unconnected publishers from inflating their own age.
    ///    Subscription-driven ageing is a robust choice because it implies that the topic is actually used.
    ///    All nodes except the publishers will locally adjust the age; the publisher will eventually learn
    ///    that during CRDT merge. If the publisher loses allocation in the meantime, its subscribers will prevent
    ///    it from losing their allocation and force it to move back in eventually.
    ///
    /// The age is NOT reset when a topic loses arbitration; otherwise, it would not be able to convince other nodes
    /// on the same topic to follow suit.
    ///
    /// We use max(x,y) for CRDT merge, which is commutative [max(x,y)==max(y,x)], associative
    /// [max(x,max(y,z))==max(max(x,y),z)], and idempotent [max(x,x)==x], making it a valid merge operation.
    uint64_t age;

    /// This is used to implement the once-per-second age increment rule.
    cy_us_t aged_at;

    /// Updated whenever the topic is gossiped.
    ///
    /// Notably, this is NOT updated when we receive a gossip from another node. While this approach can reduce
    /// redundant gossip traffic (no need to publish a gossip when the network just saw it), it can also lead to
    /// issues if the network is semi-partitioned such that the local node straddles multiple partitions.
    /// This could occur in packet switched networks or if redundant interfaces are used. Such coordinated publishing
    /// can naturally settle on a stable state where some nodes become responsible for publishing specific topics,
    /// and nodes that happen to be in a different partition will never see those topics.
    cy_us_t last_gossip;

    /// Time when this topic last saw a conflict (another topic occupying its subject-ID) or a divergence
    /// (same topic elsewhere using a different subject-ID), even if the local entry was not affected
    /// (meaning that this timestamp is updated regardless of whether the local topic won arbitration).
    ///
    /// The purpose of this timestamp is to provide the local application with a topic stability metric:
    /// if this value is sufficiently far in the past, the network could be said to have reached a stable state;
    /// if it changed (it can only increase), it means that there was either a disturbance somewhere, or a new
    /// node using this topic has joined and had to catch up.
    cy_us_t last_event_ts;

    /// Time when this topic last had to be locally moved to another subject-ID due to a conflict
    /// (another topic occupying its subject-ID) or a divergence (same topic elsewhere using a different subject-ID).
    /// Events affecting other nodes are not considered here, meaning that this is updated only if the local topic
    /// loses arbitration.
    ///
    /// The purpose of this timestamp is to provide the local application with a topic stability metric:
    /// if this value is sufficiently far in the past, the network could be said to have reached a stable state.
    cy_us_t last_local_event_ts;

    /// Used for matching futures against received responses.
    struct cy_tree_t* futures_by_transfer_id;

    /// Only used if the application publishes data on this topic.
    /// pub_count tracks the number of existing advertisements on this topic; when this number reaches zero
    /// and there are no live subscriptions, the topic will be garbage collected by Cy.
    uint64_t pub_transfer_id;
    size_t   pub_count;

    /// Only used if the application subscribes on this topic.
    struct cy_topic_coupling_t* couplings;
    bool subscribed; ///< May be (tentatively) false even with subscribers!=NULL on resubscription error.
};

/// Returns the current monotonic time in microseconds. The initial time shall be non-negative.
typedef cy_us_t (*cy_platform_now_t)(const struct cy_t*);

/// The semantics are per the standard realloc from stdlib, except:
/// - If the fragment is not increased in size, reallocation MUST succeed.
/// - If the size is zero, it must behave like free() (which is often the case in realloc() but technically an UB).
typedef void* (*cy_platform_realloc_t)(struct cy_t*, void*, size_t);

/// Returns a PRNG hashing seed or a full pseudo-random 64-bit unsigned integer.
/// A TRNG is preferred; if not available, a PRNG will suffice, but its initial state SHOULD be likely to be
/// distinct across reboots happening in a quick succession. This condition does not apply if subsequent reboots are
/// spaced apart by a long time.
///
/// The simplest compliant solution that can be implemented in an embedded system without TRNG is:
///
///     static uint64_t g_prng_state __attribute__ ((section (".noinit")));
///     g_prng_state += 0xA0761D6478BD642FULL;  // add wyhash seed (64-bit prime)
///     return g_prng_state;
///
/// It is desirable to save the PRNG state in a battery-backed memory, if available; otherwise, in small MCUs one could
/// hash the entire RAM contents at startup to scavenge as much entropy as possible, or use ADC or clock noise.
/// If RTC is available, then the following is sufficient:
///
///     static uint_fast16_t g_counter = 0;
///     return ((uint64_t)rtc_get_time() << 16U) + ++g_counter;
///
/// Internally, Cy will hash the returned value with the local node's UID for whitening and to ensure that each node
/// obtains different sequences even if they all share the same PRNG source.
typedef uint64_t (*cy_platform_prng_t)(const struct cy_t*);

/// Return payload memory obtained with received transfers via cy_ingest*().
/// The head is passed by value so not freed, but its data and all other fragments are.
typedef void (*cy_platform_buffer_release_t)(struct cy_t*, struct cy_buffer_owned_t);

/// Instructs the underlying transport to adopt the new node-ID.
/// This is invoked either immediately from cy_new() if an explicit node-ID is given,
/// or after some time from cy_update() when one is allocated automatically.
/// When this function is invoked, cy_t contains a valid node-ID.
/// Cy guarantees that this function will not be invoked unless the node-ID is currently unset.
typedef cy_err_t (*cy_platform_node_id_set_t)(struct cy_t*);

/// Instructs the underlying transport to abandon the current node-ID. Notice that this function is infallible.
/// This is invoked only if a node-ID conflict is detected; in a well-managed network this should never happen.
/// If the transport does not support reconfiguration or it is deemed too complicated to support,
/// one solution is to simply restart the node.
/// It is recommended to purge the tx queue to avoid further collisions.
/// Cy guarantees that this function will not be invoked unless the node-ID is currently set.
typedef void (*cy_platform_node_id_clear_t)(struct cy_t*);

/// The node-ID occupancy Bloom filter is used to track the occupancy of the node-ID space. The filter must be at least
/// a single 64-bit word long. The number of bits in the filter (64 times the word count) defines the maximum number
/// of nodes present in the network while the local node is still guaranteed to be able to auto-configure its own ID
/// without collisions. The recommended parameters are two 64-bit words for CAN networks (takes 16 bytes) and
/// 64~128 words (512~1024 bytes) for all other transports.
///
/// The filter is entirely managed by Cy, but its size depends on the transport layer (and how it's configured),
/// so the filter is not allocated by Cy. Instead, it is accessed indirectly via this function.
/// Every invocation returns a mutable borrowed reference to the filter, which outlives the Cy instance.
typedef struct cy_bloom64_t* (*cy_platform_node_id_bloom_t)(struct cy_t*);

/// Instructs the underlying transport layer to send an RPC request transfer.
typedef cy_err_t (*cy_platform_request_t)(struct cy_t*,
                                          uint16_t                            service_id,
                                          const struct cy_transfer_metadata_t metadata,
                                          cy_us_t                             tx_deadline,
                                          struct cy_buffer_borrowed_t         payload);

/// Allocates a new topic. NULL if out of memory.
typedef struct cy_topic_t* (*cy_platform_topic_new_t)(struct cy_t*);

typedef void (*cy_platform_topic_destroy_t)(struct cy_t*, struct cy_topic_t*);

/// Instructs the underlying transport layer to publish a new message on the topic.
/// The function shall not increment the transfer-ID counter; Cy will do it.
typedef cy_err_t (*cy_platform_topic_publish_t)(struct cy_t*,
                                                struct cy_publisher_t*,
                                                cy_us_t,
                                                struct cy_buffer_borrowed_t);

/// Instructs the underlying transport layer to create a new subscription on the topic.
typedef cy_err_t (*cy_platform_topic_subscribe_t)(struct cy_t*, struct cy_topic_t*, struct cy_subscription_params_t);

/// Instructs the underlying transport to destroy an existing subscription.
typedef void (*cy_platform_topic_unsubscribe_t)(struct cy_t*, struct cy_topic_t*);

/// Invoked when a new publisher is created on the topic.
/// The main purpose here is to communicate the response extent requested by this publisher to the platform layer,
/// allowing it to configure the P2P session accordingly.
/// The requested extent is adjusted for any protocol overheads, so that the platform layer does not have to handle it.
typedef void (*cy_platform_topic_advertise_t)(struct cy_t*, struct cy_topic_t*, size_t response_extent_with_overhead);

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
typedef void (*cy_platform_topic_on_subscription_error_t)(struct cy_t*, struct cy_topic_t*, const cy_err_t);

/// The platform- and transport-specific entities. These can be underpinned by libcanard, libudpard, libserard,
/// or any other transport library, plus the platform-specific logic.
/// None of the entities are mutable; instances of this struct are mostly intended to be static const singletons.
struct cy_platform_t
{
    cy_platform_now_t            now;
    cy_platform_realloc_t        realloc;
    cy_platform_prng_t           prng;
    cy_platform_buffer_release_t buffer_release;

    cy_platform_node_id_set_t   node_id_set;
    cy_platform_node_id_clear_t node_id_clear;
    cy_platform_node_id_bloom_t node_id_bloom;

    cy_platform_request_t request;

    cy_platform_topic_new_t                   topic_new;
    cy_platform_topic_destroy_t               topic_destroy;
    cy_platform_topic_publish_t               topic_publish;
    cy_platform_topic_subscribe_t             topic_subscribe;
    cy_platform_topic_unsubscribe_t           topic_unsubscribe;
    cy_platform_topic_advertise_t             topic_advertise;
    cy_platform_topic_on_subscription_error_t topic_on_subscription_error;

    /// 127 for Cyphal/CAN, 65534 for Cyphal/UDP and Cyphal/Serial, etc.
    /// This is used for the automatic node-ID allocation.
    uint16_t node_id_max;

    /// The mask is used only for matching received responses with pending futures.
    /// In Cyphal/CAN, the mask is 31, as we only have 5 bits for the cyclic transfer-ID counter.
    /// In other transports, the mask is 2**64-1.
    /// This shall always be one less than an integer power of two.
    uint64_t transfer_id_mask;
};

/// There are only three functions (plus convenience wrappers) whose invocations may result in network traffic:
/// - cy_update()  -- heartbeat only, at most one per call.
/// - cy_publish() -- user transfers only.
/// - cy_respond() -- user transfers only.
/// Creation of a new topic may cause resubscription of any existing topics (all in the worst case).
///
/// TODO: Use a form of leaky bucket to allow unscheduled heartbeats on collision/divergence,
/// and at the same time limit the worst case bursts. Say, we could be limited to 10 heartbeats per second
/// and by default publish 1 heartbeat per second.
struct cy_t
{
    const struct cy_platform_t* platform; ///< Never NULL.

    /// Namespace is a prefix added to all topics created on this instance, unless the topic name starts with "/".
    /// Local node name is prefixed to the topic name if it starts with `~`.
    /// Note that the leading / and ~ are only used as directives when creating a topic; they are never actually present
    /// in the final topic name.
    char namespace_[CY_NAMESPACE_NAME_MAX + 1];
    char name[CY_NAMESPACE_NAME_MAX + 1];

    /// The UID is actually composed of 16-bit vendor-ID, 16-bit product-ID, and 32-bit instance-ID (aka serial
    /// number), arranged from the most significant to the least significant bits. However, Cy doesn't care about
    /// the inner structure of the UID; all it needs is a number to order the nodes on the network and to seed PRNG.
    /// Zero is not a valid UID.
    uint64_t uid;
    uint16_t node_id;
    cy_us_t  started_at;

    /// Time when this node last saw a conflict (another topic occupying its subject-ID) or a divergence
    /// (same topic elsewhere using a different subject-ID) involving any of its topics,
    /// even if the local topic was not affected (meaning that this timestamp is updated regardless of whether
    /// the local topic won arbitration).
    ///
    /// The purpose of this timestamp is to provide the local application with a network stability metric:
    /// if this value is sufficiently far in the past, the network could be said to have reached a stable state;
    /// if it changed (it can only increase), it means that there was either a disturbance somewhere, or a new
    /// node using any of our topics has joined and had to catch up.
    cy_us_t last_event_ts;

    /// Time when any of the local topics last had to be locally moved to another subject-ID due to a conflict
    /// (another topic occupying its subject-ID) or a divergence (same topic elsewhere using a different subject-ID).
    /// Events affecting other nodes are not considered here, meaning that this is updated only if the local topic
    /// loses arbitration.
    ///
    /// The purpose of this timestamp is to provide the local application with a network stability metric:
    /// if this value is sufficiently far in the past, the network could be said to have reached a stable state.
    cy_us_t last_local_event_ts;

    /// Set from cy_notify_node_id_collision(). The actual handling is delayed.
    bool node_id_collision;

    /// Heartbeat topic and related items.
    /// The heartbeat period can be changed at any time, but it must not exceed 1 second.
    struct cy_publisher_t  heartbeat_pub;
    struct cy_subscriber_t heartbeat_sub;
    cy_us_t                heartbeat_next;
    cy_us_t                heartbeat_period;

    /// Topics have multiple indexes.
    struct cy_tree_t* topics_by_hash;
    struct cy_tree_t* topics_by_subject_id;
    struct cy_tree_t* topics_by_gossip_time;
    struct wkv_t      topics_by_name;

    /// When a heartbeat is received, its topic name will be compared against the patterns,
    /// and if a match is found, a new subscription will be constructed automatically.
    /// The values of these tree nodes point to instances of cy_subscriber_root_t.
    struct wkv_t subscribers_by_name;    ///< Both verbatim and patterns.
    struct wkv_t subscribers_by_pattern; ///< Only patterns for automatic subscriptions on heartbeat.

    /// Only for pattern subscriptions.
    struct cy_subscriber_root_t* next_scout;

    /// For detecting timed out futures. This index spans all topics.
    struct cy_tree_t* futures_by_deadline;

    /// This is to ensure we don't exhaust the subject-ID space.
    size_t topic_count;

    /// The user can use this field for arbitrary purposes.
    void* user;
};

/// If node_id > node_id_max, it is assumed to be unknown, so a stateless PnP node-ID allocation will be performed.
/// If a node-ID is given explicitly, a heartbeat will be published immediately to claim it. If the ID
/// is already taken by another node, it will have to move. This behavior differs from the normal node-ID
/// autoconfiguration process, where a node will make sure to avoid conflicts at the beginning to avoid disturbing
/// the network; the rationale is that a manually assigned node-ID takes precedence over the auto-assigned one,
/// thus forcing any squatters out of the way.
///
/// The namespace may be NULL or empty, in which case it defaults to `~`.
/// It may begin with `~`, which expands into the node name.
cy_err_t cy_new(struct cy_t* const                cy,
                const struct cy_platform_t* const platform,
                const uint64_t                    uid,
                const uint16_t                    node_id,
                const struct wkv_str_t            namespace_);
void     cy_destroy(struct cy_t* const cy);

/// This function must be invoked periodically to let the library publish heartbeats and handle response timeouts.
/// The most efficient invocation schedule is guided by cy->heartbeat_next, but not less often than every 10 ms;
/// if a fixed-rate updates are desired, then the recommended period is 1 millisecond.
///
/// This is the only function that generates heartbeat -- the only kind of auxiliary traffic needed by the protocol.
/// The returned value indicates the success of the heartbeat publication, if any took place, or zero.
///
/// If this is invoked together with cy_ingest(), then cy_update() must be invoked AFTER cy_ingest() to ensure
/// that the latest state updates are reflected in the heartbeat message.
///
/// This function is also responsible for handling the local node-ID allocation.
///
/// Excluding the transport_publish dependency, the time complexity is logarithmic in the number of topics.
cy_err_t cy_update(struct cy_t* const cy);

/// When the transport library detects a topic hash error, it will notify Cy about it to let it rectify the
/// problem. Transport frames with mismatched topic hash must be dropped; no processing at the transport layer
/// is needed. This function is not essential for the protocol to function, but it speeds up collision repair.
///
/// The function will not perform any IO and will return immediately after quickly updating an internal state.
/// It is thus safe to invoke it from a deep callback or from deep inside the transport library; the side effects
/// are confined to the Cy state only. The time complexity is logarithmic in the number of topics.
///
/// If the transport library is unable to efficiently find the topic when a collision is found, use
/// cy_topic_find_by_subject_id(). The function has no effect if the topic is NULL; it is not an error to call it
/// with NULL to simplify chaining like:
///     cy_notify_topic_hash_collision(cy_topic_find_by_subject_id(cy, collision_subject_id));
void cy_notify_topic_hash_collision(struct cy_t* const cy, struct cy_topic_t* const topic);

/// When the transport library detects an incoming transport frame with the same source node-ID as the local node-ID,
/// it must notify Cy about it to let it rectify the problem.
///
/// This function will simply set a flag and return immediately.
/// It is thus safe to invoke it from a deep callback or from deep inside the transport library; the side effects
/// are confined to the Cy state only. The time complexity is constant.
///
/// Note that the node-ID collision checks must be done on raw transport frames, not on reassembled transfers, for
/// two reasons: 1. this is faster, allowing quick reaction; 2. in the presence of a node-ID conflict, transfers
/// arriving from that ID cannot be robustly reassembled.
void cy_notify_node_id_collision(struct cy_t* const cy);

/// This is invoked whenever a new transfer on the topic is received.
/// The library will dispatch it to the appropriate subscriber callbacks.
/// Excluding the callbacks, the time complexity is constant.
/// The transfer payload ownership is taken by this function.
///
/// If this is invoked together with cy_update(), then cy_ingest() must be invoked BEFORE cy_update()
/// to ensure that the latest state updates are reflected in the next heartbeat message.
void cy_ingest_topic_transfer(struct cy_t* const         cy,
                              struct cy_topic_t* const   topic,
                              struct cy_transfer_owned_t transfer);

/// Cy does not manage RPC endpoints explicitly; it is the responsibility of the transport-specific glue logic.
/// Currently, the following RPC endpoints must be implemented in the glue logic:
///
///     - CY_RPC_SERVICE_ID_TOPIC_RESPONSE request (sic!) handler.
///       Delivers the optional response to a message published on a topic.
///       The first 8 bytes of the transfer payload are the topic hash to which the response is sent.
///       Note that we send a topic response as an RPC request transfer; the reasoning is that a higher-level
///       response is carried by a lower-level request transfer.
void cy_ingest_topic_response_transfer(struct cy_t* const cy, struct cy_transfer_owned_t transfer);

/// For diagnostics and logging only. Do not use in embedded and real-time applications.
/// This function is only required if CY_CONFIG_TRACE is defined and is nonzero; otherwise it should be left undefined.
/// Other modules that build on Cy can also use it; e.g., transport-specific glue modules.
extern void cy_trace(struct cy_t* const  cy,
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
