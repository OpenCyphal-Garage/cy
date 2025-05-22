///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// This is just a PoC, a crude approximation of what it might look like when implemented properly.
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

// ========================================  BUILD TIME CONFIG OPTIONS  ========================================

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

// =============================================  PRIMITIVES & CONSTANTS  =============================================

/// A sensible middle ground between worst-case gossip traffic and memory utilization vs. longest name support.
/// In CAN FD networks, topic names should be short to avoid multi-frame heartbeats.
///
/// Max name length is chosen such that together with the 1-byte length prefix the result is a multiple of 8 bytes,
/// because it helps with memory-aliased C structures for quick serialization.
#define CY_TOPIC_NAME_MAX 96

/// The max namespace length should also provide space for at least one separator and the one-character topic name.
#define CY_NAMESPACE_NAME_MAX (CY_TOPIC_NAME_MAX - 2)

/// If not sure, use this value for the transfer-ID timeout.
#define CY_TRANSFER_ID_TIMEOUT_DEFAULT_us 2000000L

/// If a node-ID is provided by the user, it will be used as-is and the node will become operational immediately.
///
/// If no node-ID is given, the node will take some time after it is started before it starts sending transfers.
/// While waiting, it will listen for heartbeats from other nodes to learn which addresses are available.
/// If a collision is found, the local node will immediately cease publishing and restart the node-ID allocation.
///
/// Once a node-ID is allocated, it can be optionally saved in non-volatile memory so that the next startup is
/// immediate, bypassing the allocation stage.
///
/// If a conflict is found, the current node-ID is reallocated regardless of whether it's been given explicitly or
/// allocated automatically.
#define CY_START_DELAY_MIN_us 1000000L
#define CY_START_DELAY_MAX_us 3000000L

/// The range of unregulated identifiers to use for CRDT topic allocation. The range must be the same for all
/// applications.
/// Pinned topics (such as the ordinary topics with manually assigned IDs) can be pinned anywhere in [0, 8192);
/// however, if they are used to communicate with old nodes that are not capable of the named topic protocol,
/// they should be placed in [6144, 8192), because if for whatever reason only the old nodes are left using those
/// topics, no irreparable collisions occur.
#define CY_TOPIC_SUBJECT_COUNT 6144
#define CY_SUBJECT_BITS        13U
#define CY_TOTAL_SUBJECT_COUNT (1UL << CY_SUBJECT_BITS)

#define CY_SUBJECT_ID_INVALID 0xFFFFU
#define CY_NODE_ID_INVALID    0xFFFFU

/// When a response to a received message is sent, it is delivered as an RPC request (sic) transfer to this service-ID.
/// The response user data is prefixed with 8 bytes of the full topic hash to which we are responding.
/// The receiver of the response will be able to match the response with a specific request using the transfer-ID.
///
/// We are using RPC request transfers to deliver responses because in the future we may want to use the unused
/// response transfer as a confirmation for reliable transport.
#define CY_RPC_SERVICE_ID_TOPIC_RESPONSE 510

#define CY_PASTE_(a, b) a##b
#define CY_PASTE(a, b)  CY_PASTE_(a, b)

/// I am not sure if this should be part of the library because this is a rather complicated macro.
/// It simply eliminates the boilerplate code for gathering a borrowed buffer into a contiguous storage on the stack.
/// If the source buffer is only a single fragment, then no copying is done as the resulting cy_bytes_t is simply
/// set to point to the only fragment.
///
/// Ideally, this should not be necessary at all, as all efficient APIs need to support scattered buffers;
/// but the reality is that many APIs still expect contiguous buffers, which requires an extra copy.
#define CY_BUFFER_GATHER_ON_STACK(to_bytes, from_buffer_borrowed_head)                                        \
    struct cy_bytes_t to_bytes = { .data = from_buffer_borrowed_head.view.data,                               \
                                   .size = from_buffer_borrowed_head.view.size };                             \
    uint8_t           CY_PASTE(to_bytes, _storage)[cy_buffer_borrowed_get_size(from_buffer_borrowed_head)];   \
    if (from_buffer_borrowed_head.next != NULL) {                                                             \
        to_bytes.size =                                                                                       \
          cy_buffer_borrowed_gather(from_buffer_borrowed_head,                                                \
                                    (struct cy_bytes_mut_t){ .data = CY_PASTE(to_bytes, _storage),            \
                                                             .size = sizeof(CY_PASTE(to_bytes, _storage)) }); \
        to_bytes.data = CY_PASTE(to_bytes, _storage);                                                         \
    }

/// TODO: unified error codes: argument, memory, capacity, anonymous, name.
typedef int32_t cy_err_t;
typedef int64_t cy_us_t; ///< Monotonic microsecond timestamp. Signed to permit arithmetics in the past.

struct cy_t;
struct cy_topic_t;
struct cy_future_t;

enum cy_prio_t
{
    cy_prio_exceptional = 0,
    cy_prio_immediate   = 1,
    cy_prio_fast        = 2,
    cy_prio_high        = 3,
    cy_prio_nominal     = 4,
    cy_prio_low         = 5,
    cy_prio_slow        = 6,
    cy_prio_optional    = 7,
};

struct cy_bytes_t
{
    size_t      size;
    const void* data;
};
struct cy_bytes_mut_t
{
    size_t size;
    void*  data;
};

/// The transport libraries support very efficient zero-copy data pipelines which operate on scattered buffers.
/// Received data may be represented as a chain of scattered buffers; likewise, it is possible to transmit a chain
/// of buffers instead of a single monolithic buffer. The last entry in the chain has next=NULL.
///
/// The view points to the useful payload; DO NOT attempt to deallocate the view.
/// The origin can only be used to deallocate the payload; that address shall not be accessed in any way.
/// Normally, view and origin are identical, but this is not always the case depending on the transport library.
/// The view is usually inside the origin, but even that is not guaranteed; e.g., if memory mapping is used.
///
/// The head of the payload chain is always passed by value and thus does not require freeing; the following chain
/// elements are also allocated from some memory resource and thus shall be freed with the payload.
///
/// Warning: It is required that the first 8 bytes of the payload are NOT fragmented. Otherwise, Cy may refuse to
/// accept the transfer. This requirement is trivial to meet because the MTU of all transports that supply fragmented
/// payloads is much larger than 8 bytes.
///
/// The size of a payload fragment may be zero.
struct cy_buffer_borrowed_t
{
    const struct cy_buffer_borrowed_t* next; ///< NULL in the last entry.
    struct cy_bytes_t                  view;
};
struct cy_buffer_owned_t
{
    struct cy_buffer_borrowed_t base;
    struct cy_bytes_mut_t       origin; ///< Do not access! Address may not be mapped. Only for freeing the payload.
};

struct cy_tree_t
{
    struct cy_tree_t* up;
    struct cy_tree_t* lr[2];
    int8_t            bf;
};

/// An ordinary Bloom filter with 64-bit words.
struct cy_bloom64_t
{
    size_t    n_bits;   ///< The total number of bits in the filter, a multiple of 64.
    size_t    popcount; ///< (popcount <= n_bits)
    uint64_t* storage;
};

struct cy_transfer_metadata_t
{
    enum cy_prio_t priority;
    uint16_t       remote_node_id;
    uint64_t       transfer_id;
};

/// A transfer object owns its payload.
/// When passing it to Cy, the ownership is transferred.
/// Likewise, when receiving a transfer, the payload shall be freed by the application.
struct cy_transfer_owned_t
{
    cy_us_t                       timestamp;
    struct cy_transfer_metadata_t metadata;
    struct cy_buffer_owned_t      payload;
};

// ===============================================  PLATFORM INTERFACE  ===============================================

/// Returns the current monotonic time in microseconds. The initial time shall be non-negative.
typedef cy_us_t (*cy_platform_now_t)(const struct cy_t*);

/// Returns a PRNG hashing seed or a full pseudo-random 64-bit unsigned integer.
/// A TRNG is preferred; if not available, a PRNG will suffice, but its initial state SHOULD be likely to be
/// distinct across reboots happening in a quick succession. This condition does not apply if subsequent reboots are
/// spaced apart by a long time (ca. 10 seconds or more). If this condition is not satisfied,
/// the transfer-ID counters will be initialized with the same value every time,
/// which may incur an initial synchronization delay (up to the transfer-ID timeout value).
///
/// The simplest compliant solution that can be implemented in a deeply embedded system is:
///
///     static uint64_t g_prng_state __attribute__ ((section (".noinit")));
///     g_prng_state += 0xA0761D6478BD642FULL;  // add wyhash seed (64-bit prime)
///     return g_prng_state;
///
/// If RTC is available, then the following is sufficient (the counter can be 8-bit if RTC is microsecond resolution):
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

typedef void (*cy_platform_topic_destroy_t)(struct cy_topic_t*);

/// Instructs the underlying transport layer to publish a new message on the topic.
/// The function shall not increment the transfer-ID counter; Cy will do it.
typedef cy_err_t (*cy_platform_topic_publish_t)(struct cy_topic_t*, cy_us_t, struct cy_buffer_borrowed_t);

/// Instructs the underlying transport layer to create a new subscription on the topic.
typedef cy_err_t (*cy_platform_topic_subscribe_t)(struct cy_topic_t*);

/// Instructs the underlying transport to destroy an existing subscription.
typedef void (*cy_platform_topic_unsubscribe_t)(struct cy_topic_t*);

/// If a subject-ID collision or divergence are discovered, Cy may reassign the topic to a different subject-ID.
/// To do that, it will first unsubscribe the topic using the corresponding function,
/// and then invoke the subscription function to recreate the subscription with the new subject-ID.
///
/// The unsubscription function is infallible, but the subscription function may fail.
/// If it does, this callback will be invoked to inform the user about the failure,
/// along with the error code returned by the subscription function. It is up to the user to repair the problem.
/// If the user does nothing, the topic will be simply left in the unsubscribed state, as if
/// cy_topic_subscribe() was never invoked. However, if the topic needs to be moved again in the future,
/// Cy will use that opportunity to attempt another subscription, which may or may not succeed.
///
/// A possible failure handling strategy is to record which topic has failed and to keep trying to re-subscribe
/// in the background until it succeeds. Once the subscription is successful, no additional actions are needed.
/// It is probably not useful to try and invoke cy_subscribe() immediately from the error handler.
typedef void (*cy_platform_topic_handle_resubscription_error_t)(struct cy_topic_t*, const cy_err_t);

/// The platform- and transport-specific entities. These can be underpinned by libcanard, libudpard, libserard,
/// or any other transport library, plus the platform-specific logic.
/// None of the entities are mutable; instances of this struct are mostly intended to be static const singletons.
struct cy_platform_t
{
    cy_platform_now_t            now;
    cy_platform_prng_t           prng;
    cy_platform_buffer_release_t buffer_release;

    cy_platform_node_id_set_t   node_id_set;
    cy_platform_node_id_clear_t node_id_clear;
    cy_platform_node_id_bloom_t node_id_bloom;

    cy_platform_request_t request;

    cy_platform_topic_new_t                         topic_new;
    cy_platform_topic_destroy_t                     topic_destroy;
    cy_platform_topic_publish_t                     topic_publish;
    cy_platform_topic_subscribe_t                   topic_subscribe;
    cy_platform_topic_unsubscribe_t                 topic_unsubscribe;
    cy_platform_topic_handle_resubscription_error_t topic_handle_resubscription_error;

    /// 127 for Cyphal/CAN, 65534 for Cyphal/UDP and Cyphal/Serial, etc.
    /// This is used for the automatic node-ID allocation.
    uint16_t node_id_max;

    /// The mask is used only for matching received responses with pending futures.
    /// In Cyphal/CAN, the mask is 31, as we only have 5 bits for the cyclic transfer-ID counter.
    /// In other transports, the mask is 2**64-1.
    /// This shall always be one less than an integer power of two.
    uint64_t transfer_id_mask;
};

// ===============================================  CY API  ===============================================

/// This is the base type that is extended by the platform layer with transport- and platform-specific entities,
/// such as socket handles, etc. Instantiation is therefore done inside the platform layer in the heap or some
/// other dynamic storage.
///
/// A topic name is suffixed to the namespace name of the node that owns it, unless it begins with a `/`.
/// The leading `~` in the name is replaced with `/vvvv/pppp/iiiiiiii`, where the letters represent hexadecimal
/// digits of the vendor ID, product ID, and instance ID of the node.
/// Repeated and trailing slashes are removed.
///
/// TODO: Missing feature: wildcard topic subscriptions. This requires dynamic memory, unlike the basic feature set.
/// The consensus protocol is not affected by this feature, only the library implementation.
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

    struct cy_t* cy;

    /// The name is always null-terminated. We keep the size for convenience as well.
    size_t name_length;
    char   name[CY_TOPIC_NAME_MAX + 1];

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
    /// The priority can be adjusted as needed by the user.
    ///
    /// The publishing flag will be set automatically on first publish(). The application can also set it manually.
    /// The purpose of this flag is to inform other network participants whether we intend to publish on this topic.
    /// If the application is no longer planning to continue publishing, the flag should be zeroed (or topic destroyed).
    uint64_t       pub_transfer_id;
    enum cy_prio_t pub_priority;
    bool           publishing;

    /// Only used if the application subscribes on this topic.
    /// The payload ownership is transferred to sub_last_transfer when a new transfer is received.
    /// If a payload is already available when a new transfer is received, Cy will free the old payload first.
    /// The user can detect when a new message is received by checking sub_last_transfer.timestamp.
    /// Optionally, a reception callback can be set in cy_subscription_t.
    struct cy_transfer_owned_t sub_last_transfer;
    struct cy_subscription_t*  sub_list;
    cy_us_t                    sub_transfer_id_timeout;
    size_t                     sub_extent;
    bool                       subscribed; ///< May be false even if sub_list is nonempty on resubscription error.

    void* user; ///< The application can use this field for arbitrary purposes.
};

typedef void (*cy_subscription_callback_t)(struct cy_subscription_t*);
typedef void (*cy_response_callback_t)(struct cy_future_t*);

struct cy_subscription_t
{
    struct cy_subscription_t* next;
    struct cy_topic_t*        topic;

    /// These fields may be altered by the user at any time; e.g., to implement a state machine.
    /// The callback may be NULL if the application prefers to check last_message by polling.
    cy_subscription_callback_t callback;
    void*                      user;
};

enum cy_future_state_t
{
    cy_future_pending = 0,
    cy_future_success = 1,
    cy_future_failure = 2,
};

/// Register an expectation for a response to a message sent to the topic.
/// The future shall not be moved or altered in anyway except for the user and callback fields until its state is
/// no longer pending. Once it is not pending, it can be reused for another request.
/// The future will enter the failure state to indicate that the response was not received before the deadline.
struct cy_future_t
{
    struct cy_tree_t index_deadline;
    struct cy_tree_t index_transfer_id;

    struct cy_topic_t*     topic;
    enum cy_future_state_t state;
    uint64_t               transfer_id_masked; ///< Masked as (platform->transfer_id_mask & transfer_id)
    cy_us_t                deadline;           ///< We're indexing on this so it shall not be changed after insertion.

    /// These fields are populated once the response is received.
    /// The payload ownership is transferred to this structure.
    /// If a payload is already available when a response is received, Cy will free the old payload first.
    /// The user can detect when a new response is received by checking its timestamp.
    struct cy_transfer_owned_t last_response;

    /// Only these fields can be altered by the user while the future is pending.
    /// The callback may be NULL if the application prefers to check last_response by polling.
    cy_response_callback_t callback;
    void*                  user;
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
    struct cy_topic_t*       heartbeat_topic;
    struct cy_subscription_t heartbeat_sub;
    cy_us_t                  heartbeat_next;
    cy_us_t                  heartbeat_period_max;
    cy_us_t                  heartbeat_full_gossip_cycle_period_max; ///< Max time to gossip all local topics.

    /// Topics have multiple indexes.
    struct cy_tree_t* topics_by_hash;
    struct cy_tree_t* topics_by_subject_id;
    struct cy_tree_t* topics_by_gossip_time;

    /// For detecting timed out futures. This index spans all topics.
    struct cy_tree_t* futures_by_deadline;

    /// This is to ensure we don't exhaust the subject-ID space.
    size_t topic_count;

    /// The user can use this field for arbitrary purposes.
    void* user;
};

/// A convenience wrapper that returns the current time in microseconds.
static inline cy_us_t cy_now(const struct cy_t* const cy)
{
    return cy->platform->now(cy);
}

/// This shall be invoked once the application is done processing a payload.
/// The struct will be modified by zeroing pointers and sizes in it.
/// When Cy assigns a new payload to a subscription/response/etc object, it will check first if the previous payload
/// is released; if not, it will do it automatically. The nullification of the pointers is thus required to make it
/// explicit that the payload is no longer valid and to prevent double-free errors.
/// Invoking this function on an already released payload has no effect and is safe.
void cy_buffer_owned_release(struct cy_t* const cy, struct cy_buffer_owned_t* const payload);

/// Returns the total size of all payload fragments in the chain.
/// The complexity is linear, but the number of elements is very small (total size divided by MTU).
size_t               cy_buffer_borrowed_get_size(const struct cy_buffer_borrowed_t payload);
static inline size_t cy_buffer_owned_get_size(const struct cy_buffer_owned_t payload)
{
    return cy_buffer_borrowed_get_size(payload.base);
}

/// Takes the head of a fragmented buffer list and copies the data into the contiguous buffer provided by the user.
/// If the total size of all fragments combined exceeds the size of the user-provided buffer,
/// copying will stop early after the buffer is filled, thus truncating the fragmented data short.
/// The function has no effect and returns zero if the destination buffer is NULL.
/// Returns the number of bytes copied into the contiguous destination buffer.
size_t cy_buffer_borrowed_gather(const struct cy_buffer_borrowed_t payload, const struct cy_bytes_mut_t dest);
static inline size_t cy_buffer_owned_gather(const struct cy_buffer_owned_t payload, const struct cy_bytes_mut_t dest)
{
    return cy_buffer_borrowed_gather(payload.base, dest);
}

/// If a node-ID is given explicitly at startup, it will be used as-is and the node will become operational immediately.
/// Otherwise, some initial node-ID autoconfiguration time will be needed before the local ID is available.
/// Also, if a node-ID conflict is found at any later time (e.g., if a badly configured node joins the network),
/// the current ID will be abandoned and after some time a new one will be allocated. This cannot happen in a
/// well-managed network. A node with an auto-configured ID will not encroach on the IDs of other nodes by design.
///
/// An attempt to emit a transfer while the local node-ID is missing may fail, depending on the transport library.
static inline bool cy_has_node_id(const struct cy_t* const cy)
{
    return cy->node_id <= cy->platform->node_id_max;
}

/// A heuristical prediction of whether the local node is ready to fully participate in the network.
/// The joining process will be bypassed if the node-ID and all topic allocations are recovered from non-volatile
/// storage. This flag can briefly flip back to false if a topic allocation conflict or a divergence are detected;
/// it will return back to true automatically once the network is repaired.
///
/// Since the network fundamentally relies on an eventual consistency model, it is not possible to guarantee that
/// any given state is final. It is always possible, for example, that while our network segment looks stable,
/// it could actually be a partition of a larger network; when the partitions are rejoined, the younger and/or smaller
/// partition will be forced to adapt to the main network, thus enduring a brief period of instability.
static inline bool cy_ready(const struct cy_t* const cy)
{
    return cy_has_node_id(cy) && ((cy->platform->now(cy) - cy->last_local_event_ts) > 1000000);
}

/// Register a new topic that may be used by the local application for publishing, subscribing, or both.
/// Returns NULL if the topic name is not unique or not valid, or if the platform could not allocate the topic.
///
/// If the hint is provided, it will be used as the initial allocation state, unless either a conflict or divergence
/// are discovered, which will be treated normally, without any preference to the hint. This option allows the user
/// to optionally save the network configuration in a non-volatile storage, such that the next time the network becomes
/// operational immediately, without waiting for the CRDT consensus. Remember that the hint is discarded on conflict.
struct cy_topic_t* cy_topic_new_hint(struct cy_t* const cy, const char* const name, const uint16_t subject_id_hint);
static inline struct cy_topic_t* cy_topic_new(struct cy_t* const cy, const char* const name)
{
    return cy_topic_new_hint(cy, name, CY_SUBJECT_ID_INVALID);
}
void cy_topic_destroy(struct cy_topic_t* const topic);

/// Complexity is logarithmic in the number of topics. NULL if not found.
/// In practical terms, these queries are very fast and efficient.
struct cy_topic_t* cy_topic_find_by_name(struct cy_t* const cy, const char* const name);
struct cy_topic_t* cy_topic_find_by_hash(struct cy_t* const cy, const uint64_t hash);
struct cy_topic_t* cy_topic_find_by_subject_id(struct cy_t* const cy, const uint16_t subject_id);

/// Iterate over all topics in an unspecified order.
/// This is useful when handling IO multiplexing (building the list of descriptors to read) and for introspection.
/// The iteration stops when the returned topic is NULL.
/// The set of topics SHALL NOT be mutated while iterating over it (a restart will be needed otherwise).
/// Usage:
///     for (struct cy_topic_t* topic = cy_topic_iter_first(cy); topic != NULL; topic = cy_topic_iter_next(topic)) {
///         ...
///     }
struct cy_topic_t* cy_topic_iter_first(struct cy_t* const cy);
struct cy_topic_t* cy_topic_iter_next(struct cy_topic_t* const topic);

uint16_t cy_topic_get_subject_id(const struct cy_topic_t* const topic);

static inline bool cy_topic_has_local_publishers(const struct cy_topic_t* const topic)
{
    return topic->publishing;
}

static inline bool cy_topic_has_local_subscribers(const struct cy_topic_t* const topic)
{
    return topic->sub_list != NULL;
}

/// Topic discriminator is fused into every transport frame and possibly transfer for subject-ID collision detection.
/// It is defined as the 51 most significant bits of the topic name hash, while the least significant bits are
/// used for deterministic subject-ID allocation. The two numbers must be uncorrelated to minimize collisions.
/// For pinned topics, the discriminator is zero because we don't want to check it for compatibility with old
/// nodes; this is ensured by our special topic hash function. Transports are expected to use either the full 51-bit
/// discriminator or any part thereof (excepting the most significant zero bits ofc), depending on their design.
///
/// Given the size of the subject-ID space of 6144 identifiers and 2^51 possible discriminators, the probability of
/// a collision on a network with 1000 topics is birthday(6144*(2**51), 1000) ~ 3.6e-14, or one in ~28 trillion.
/// This is assuming that all bits of the discriminator are used. If only 32 bits are used, the probability is
/// birthday(6144*(2**32), 1000) ~ 1.9e-8, or one in 53 million.
static inline uint64_t cy_topic_get_discriminator(const struct cy_topic_t* const topic)
{
    return topic->hash >> CY_SUBJECT_BITS;
}

/// Technically, the callback can be NULL, and the subscriber will work anyway.
/// One can still use the transfers by polling the last received transfer in the topic object.
///
/// Invoking this function on the same cy_subscription_t instance multiple times is allowed.
/// This is supported specifically to allow repairing broken resubscriptions when Cy attempts
/// to move the topic to another subject-ID but fails to subscribe it.
///
/// Future expansion: add wildcard subscribers that match topic names by pattern. Requires unbounded dynamic memory.
///
/// It is allowed to remove the subscription from its own callback, but not from the callback of another subscription.
///
/// The extent and transfer-ID timeout of all subscriptions should be the same, or these values of subscriptions
/// added later should be less than the values of subscriptions added earlier. Otherwise, the library will be forced
/// to resubscribe, which may cause momentary data loss if there were transfers in the middle of reassembly.
cy_err_t               cy_subscribe_with_transfer_id_timeout(struct cy_topic_t* const         topic,
                                                             struct cy_subscription_t* const  sub,
                                                             const size_t                     extent,
                                                             const cy_us_t                    transfer_id_timeout,
                                                             const cy_subscription_callback_t callback);
static inline cy_err_t cy_subscribe(struct cy_topic_t* const         topic,
                                    struct cy_subscription_t* const  sub,
                                    const size_t                     extent,
                                    const cy_subscription_callback_t callback)
{
    return cy_subscribe_with_transfer_id_timeout(topic, sub, extent, CY_TRANSFER_ID_TIMEOUT_DEFAULT_us, callback);
}
void cy_unsubscribe(struct cy_topic_t* const topic, struct cy_subscription_t* const sub);

/// Just a convenience function, nothing special.
struct cy_future_t cy_future_new(const cy_response_callback_t callback, void* const user);

/// The transfer-ID is always incremented, even on failure, to signal lost messages.
/// This function always publishes only one transfer as requested; no auxiliary traffic is generated.
/// If the local node-ID is not allocated, the function may fail depending on the capabilities of the transport library;
/// to avoid this, it is possible to check cy_has_node_id() before calling this function.
///
/// If no response is needed/expected, the future must be NULL and the response_deadline is ignored.
/// Otherwise, future must point to an uninitialized cy_future_t instance.
///
/// The response future will not be registered unless the result is non-negative.
///
/// If the response deadline is in the past, the message will be sent anyway but it will time out immediately.
cy_err_t cy_publish(struct cy_topic_t* const          topic,
                    const cy_us_t                     tx_deadline,
                    const struct cy_buffer_borrowed_t payload,
                    const cy_us_t                     response_deadline,
                    struct cy_future_t* const         future);

/// A simpler wrapper over cy_publish() when no response is needed/expected. 1 means one way.
static inline cy_err_t cy_publish1(struct cy_topic_t* const          topic,
                                   const cy_us_t                     tx_deadline,
                                   const struct cy_buffer_borrowed_t payload)
{
    return cy_publish(topic, tx_deadline, payload, 0, NULL);
}

/// This needs not be done after a future completes normally. It is only needed if the future needs to be
/// destroyed before it completes. Calling this on a non-pending future has no effect.
void cy_future_cancel(struct cy_future_t* const future);

/// Send a response to a message received from a topic subscription. The response will be sent directly to the
/// publisher using peer-to-peer transport, not affecting other nodes on this topic. The payload may be arbitrary
/// and the metadata shall be taken from the original message. The transfer-ID will not be incremented since it's
/// not a publication.
///
/// This can be invoked either from a subscription callback or at any later point. The topic may even get reallocated
/// in the process but it doesn't matter.
///
/// The response is be sent using an RPC request (sic) transfer to the publisher with the specified priority and
/// the original transfer-ID.
cy_err_t cy_respond(struct cy_topic_t* const            topic,
                    const cy_us_t                       tx_deadline,
                    const struct cy_transfer_metadata_t metadata,
                    const struct cy_buffer_borrowed_t   payload);

// ====================================================================================================================
// =================================================  END OF THE API  =================================================
// ====================================================================================================================
// The definitions that follow are used by the platform layer, not by the application.

/// If node_id > node_id_max, it is assumed to be unknown, so a stateless PnP node-ID allocation will be performed.
/// If a node-ID is given explicitly, a heartbeat will be published immediately to claim it. If the ID
/// is already taken by another node, it will have to move. This behavior differs from the normal node-ID
/// autoconfiguration process, where a node will make sure to avoid conflicts at the beginning to avoid disturbing
/// the network; the rationale is that a manually assigned node-ID takes precedence over the auto-assigned one,
/// thus forcing any squatters out of the way.
///
/// The namespace may be NULL or empty, in which case it defaults to `/`.
/// It may begin with `~`, which expands into the node name.
cy_err_t cy_new(struct cy_t* const                cy,
                const struct cy_platform_t* const platform,
                const uint64_t                    uid,
                const uint16_t                    node_id,
                const char* const                 namespace_);
void     cy_destroy(struct cy_t* const cy);

/// This function must be invoked periodically to let the library publish heartbeats and handle response timeouts.
/// The invocation period MUST NOT EXCEED the heartbeat period configured in cy_t; there is no lower limit.
/// The recommended invocation period is less than 10 milliseconds.
///
/// This is the only function that generates heartbeat --- the only kind of auxiliary traffic needed to support
/// named topics. The returned value indicates the success of the heartbeat publication, if any took place, or zero.
///
/// If this is invoked together with cy_ingest(), then cy_update() must be invoked AFTER cy_ingest() to ensure
/// that the latest state updates are reflected in the heartbeat message.
///
/// This function is also responsible for handling the local node-ID allocation.
///
/// Excluding the transport_publish dependency, the time complexity is logarithmic in the number of topics.
cy_err_t cy_update(struct cy_t* const cy);

/// When the transport library detects a discriminator error, it will notify Cy about it to let it rectify the
/// problem. Transport frames with mismatched discriminators must be dropped; no processing at the transport layer
/// is needed. This function is not essential for the protocol to function, but it speeds up collision repair.
///
/// The function will not perform any IO and will return immediately after quickly updating an internal state.
/// It is thus safe to invoke it from a deep callback or from deep inside the transport library; the side effects
/// are confined to the Cy state only. The time complexity is logarithmic in the number of topics.
///
/// If the transport library is unable to efficiently find the topic when a collision is found, use
/// cy_topic_find_by_subject_id(). The function has no effect if the topic is NULL; it is not an error to call it
/// with NULL to simplify chaining like:
///     cy_notify_discriminator_collision(cy_topic_find_by_subject_id(cy, collision_subject_id));
void cy_notify_discriminator_collision(struct cy_topic_t* const topic);

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
///
/// If this is invoked together with cy_update(), then cy_ingest() must be invoked BEFORE cy_update()
/// to ensure that the latest state updates are reflected in the next heartbeat message.
void cy_ingest_topic_transfer(struct cy_topic_t* const topic, const struct cy_transfer_owned_t transfer);

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
