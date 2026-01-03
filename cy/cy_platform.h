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

/// For compatibility with Cyphal v1.0, the heartbeat topic is pinned at subject-ID 7509.
#define CY_HEARTBEAT_TOPIC_NAME "/#1d55"

/// Only for testing and debugging purposes.
/// Makes all non-pinned topics prefer the same subject-ID that equals the value of this macro,
/// which maximizes topic allocation collisions. Pinned topics are unaffected.
/// This can be used to stress-test the consensus algorithm.
/// This value shall be identical for all nodes in the network; otherwise, divergent allocations will occur.
#ifndef CY_CONFIG_PREFERRED_TOPIC_OVERRIDE
// Never define in production use.
#endif

/// The subject-ID modulus depends on the width of the subject-ID field in the transport protocol.
/// All nodes in the network shall share the same value.
/// If heterogeneously redundant transports are used, then the smallest modulus shall be used.
/// The range of used subject-ID values is [0, CY_PINNED_SUBJECT_ID_MAX+modulus),
/// where the values below or equal to CY_PINNED_SUBJECT_ID_MAX are used for pinned topics only.
/// The modulus shall be a prime number; see https://github.com/OpenCyphal-Garage/cy/issues/12#issuecomment-3577831960
#define CY_SUBJECT_ID_MODULUS_16bit 57349
#define CY_SUBJECT_ID_MODULUS_23bit 8380417
#define CY_SUBJECT_ID_MODULUS_32bit 4294959083U

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

typedef struct cy_tree_t cy_tree_t;
struct cy_tree_t
{
    cy_tree_t*  up;
    cy_tree_t*  lr[2];
    int_fast8_t bf;
};

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

/// Platform-specific implementation of cy_message_t.
typedef struct cy_message_vtable_t
{
    void (*free)(cy_message_t*);
    size_t (*read)(cy_message_t*, size_t, size_t, void*);
} cy_message_vtable_t;

/// The data that is forwarded back to Cy per message delivery callback by value.
typedef struct cy_feedback_context_t cy_feedback_context_t;
struct cy_feedback_context_t
{
    cy_user_context_t user;
    void (*fun)(void); ///< May exceed sizeof(void*) depending on the platform; treat as opaque.
};

/// This is the base type that is extended by the platform layer with transport- and platform-specific entities,
/// such as socket handles, etc. Instantiation is therefore done inside the platform layer in the heap or some
/// other dynamic storage. The user code is not expected to interact with the topic type, and the only reason it is
/// defined in the header file is to allow the platform layer to use it.
///
/// Topic instances are allocated in some kind of dynamic storage (heap or block pool) and are pinned (never copied).
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

    cy_t* cy;

    /// The name length is stored in index_name.
    /// We need to store the full name to allow valid references from name substitutions during pattern matching.
    char name[CY_TOPIC_NAME_MAX + 1];

    /// Whenever a topic conflicts with another one locally, arbitration is performed, and the loser has its
    /// eviction counter incremented. The eviction counter is used as a Lamport clock counting the loss events.
    /// Higher clock wins because it implies that any lower value is non-viable since it has been known to cause
    /// at least one collision anywhere on the network. The counter MUST NOT BE CHANGED without removing the topic
    /// from the subject-ID index tree!
    uint64_t evictions;

    /// hash=rapidhash(topic_name); except for a pinned topic, hash=subject_id<=CY_PINNED_SUBJECT_ID_MAX.
    uint64_t hash;

    /// Event timestamps used for state management.
    cy_us_t ts_origin;   ///< An approximation of when the topic was first seen on the network.
    cy_us_t ts_animated; ///< Last time the topic saw activity that prevents it from being retired.

    /// Used for matching pending response states against received responses by transfer-ID.
    cy_tree_t* response_by_transfer_id;

    /// States related to tracking publishers and subscribers on this topic. The topic is removed when none left.
    struct cy_topic_coupling_t* couplings;
    bool   subscribed; ///< May be (tentatively) false even with couplings!=NULL on resubscription error.
    size_t pub_count;  ///< Number of active advertisements; counted for garbage collection.

    /// The vtable pointer must be initialized by the new_topic() factory.
    const struct cy_topic_vtable_t* vtable;
} cy_topic_t;

/// Platform-specific implementation of the topic operations.
typedef struct cy_topic_vtable_t
{
    void (*destroy)(cy_topic_t* self);

    /// Instructs the underlying transport layer to non-blockingly publish a new message on the topic.
    /// The transport will choose a new transfer-ID value for the message and return it, which may be used later to
    /// match responses if any are needed/expected.
    ///
    /// The feedback context is NULL iff best-effort mode is chosen, otherwise the reliable mode is used.
    /// If reliable mode is chosen, the outcome will ALWAYS be reported EXACTLY ONCE per successful publish() call
    /// via cy_on_message_feedback() with the provided context.
    ///
    /// The response extent hints the maximum size of response messages arriving in response to the published message
    /// that is of interest for the application, allowing the transport to truncate the rest. The transport may
    /// disreagrd the hint and receive an arbitrarily larger response message.
    cy_err_t (*publish)(cy_topic_t*                  self,
                        cy_us_t                      tx_deadline,
                        cy_prio_t                    priority,
                        cy_bytes_t                   message,
                        const cy_feedback_context_t* reliable_context,
                        uint64_t*                    out_transfer_id,
                        size_t                       response_extent);

    /// Instructs the underlying transport layer to create a new subscription on the topic.
    /// The topic is guaranteed to not be subscribed to when this function is invoked.
    /// TODO: Should we implement an optimization to allow quick extent change without full resubscription?
    /// The reordering window is negative if the unordered mode is desired.
    cy_err_t (*subscribe)(cy_topic_t* self, size_t extent, cy_us_t reordering_window);

    /// Instructs the underlying transport to destroy an existing subscription. Infallible by design.
    void (*unsubscribe)(cy_topic_t* self);
} cy_topic_vtable_t;

/// Platform-specific implementation of cy_responder_t.
typedef struct cy_responder_vtable_t
{
    /// Instructs the underlying transport layer to send a peer-to-peer response transfer. The identity of the remote
    /// endpoint is encoded and the transfer metadata are stored inside the cy_responder_t object in a
    /// platform-specific manner.
    /// Implementations may optionally invalidate the responder object after use -- only a single use is guaranteed.
    /// Currently, all P2P response transfers are sent using the reliable delivery mode, and the result of the transfer
    /// is reported via cy_on_message_feedback().
    cy_err_t (*respond)(cy_responder_t*, cy_us_t tx_deadline, cy_bytes_t message, cy_feedback_context_t context);
} cy_responder_vtable_t;

/// Instances of cy are not copyable; they are always accessed via pointer provided during initialization.
/// Creation of a new topic may cause resubscription of any existing topics (all topics in the unlikely worst case).
struct cy_t
{
    const struct cy_vtable_t* vtable;

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
    cy_publisher_t*  heartbeat_pub;
    cy_subscriber_t* heartbeat_sub;
    cy_us_t          heartbeat_period;
    cy_us_t          heartbeat_next;
    cy_us_t          heartbeat_next_urgent;

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

    /// For detecting timed out responses. This index spans all topics.
    cy_tree_t* responses_by_deadline;

    /// The user can use this field for arbitrary purposes. The platform layer shall not touch it.
    void* user;
};

/// Platform-specific implementation of cy_t.
typedef struct cy_vtable_t
{
    /// Returns the current monotonic time in microseconds. The initial time shall be non-negative.
    cy_us_t (*now)(const cy_t*);

    /// The semantics are per the standard realloc from stdlib, except:
    /// - If the fragment is not increased in size, reallocation MUST succeed.
    /// - If the size is zero, it must behave like free() (which is often the case in realloc() but technically an UB).
    /// - Constant-complexity is preferred -- the API complexity specs are given assuming O(1) alloc/free operations,
    ///   unless memory needs to be moved, in which case the complexity is linear in the old size of the block.
    void* (*realloc)(cy_t*, void*, size_t);

    /// Returns a random 64-bit unsigned integer.
    /// A TRNG is preferred; if not available, a PRNG will suffice, but its initial state should be distinct across
    /// reboots, and it should be hashed with the node's unique identifier.
    ///
    /// A simple compliant solution that can be implemented in an embedded system without TRNG is:
    ///
    ///     static uint64_t g_prng_state __attribute__ ((section (".noinit")));
    ///     g_prng_state += 0xA0761D6478BD642FULL;                // add Wyhash seed (64-bit prime)
    ///     const uint64_t seed[2] = { g_prng_state, local_uid }; // if possible, add more entropy here, like ADC noise
    ///     return rapidhash(seed, sizeof(seed));
    ///
    /// It is desirable to save the PRNG state in a battery-backed memory, if available; otherwise, in small MCUs one
    /// could hash the entire RAM contents at startup to scavenge as much entropy as possible, or use ADC or clock
    /// noise. If an RTC is available, then the following is sufficient:
    ///
    ///     static uint_fast16_t g_counter = 0;
    ///     const uint64_t seed[2] = {
    ///         ((uint64_t)rtc_get_time() << 16U) + ++g_counter,
    ///         local_uid,
    ///     }; // if possible, add more entropy here, like ADC noise
    ///     return rapidhash(seed, sizeof(seed));
    uint64_t (*random)(cy_t*);

    /// Allocates a new topic that is initially neither subscribed nor advertised. NULL if out of memory.
    cy_topic_t* (*new_topic)(cy_t*);

    /// If an allocation collision or divergence are discovered, Cy may reassign the topic to a different subject-ID.
    /// To do that, it will first unsubscribe the topic using the corresponding function,
    /// and then invoke the subscription function to recreate the subscription with the new subject-ID.
    /// The unsubscription function is infallible, but the subscription function may fail.
    /// If it does, this callback will be invoked to inform the user about the failure,
    /// along with the error code returned by the subscription function.
    ///
    /// The callback is also used to report errors that occur when attempting to create a new topic that matches a
    /// pattern subscriber; in this case, the topic pointer will be NULL.
    ///
    /// Normally, the error handler does not need to do anything specific aside from perhaps logging/reporting the
    /// error. Cy will keep attempting to repair the topic periodically as long as it exists.
    void (*on_subscription_error)(cy_t*, cy_topic_t*, cy_err_t);
} cy_vtable_t;

/// The namespace may be NULL or empty, in which case it defaults to `~`.
/// It may begin with `~`, which expands into the node name.
/// The node name should be unique in the network; one way to ensure this is to default it to the node UID as hex.
cy_err_t cy_new(cy_t* const              cy,
                const cy_vtable_t* const vtable,
                const wkv_str_t          name,
                const wkv_str_t          namespace_,
                const uint32_t           subject_id_modulus);
void     cy_destroy(cy_t* const cy);

/// This function must be invoked periodically to ensure liveness.
/// The most efficient invocation schedule is guided by min(cy->heartbeat_next, cy->heartbeat_next_urgent),
/// but not less often than every 10 ms; if fixed-rate updates are desired, then the recommended period is 1 ms.
/// The returned value indicates the success of the heartbeat publication, if any took place, or zero.
cy_err_t cy_update(cy_t* const cy);

/// Hidden from the application because the application is not expected to need this.
uint32_t cy_topic_subject_id(const cy_topic_t* const topic);

static inline bool cy_topic_has_subscribers(const cy_topic_t* const topic) { return topic->couplings != NULL; }

/// When the transport library detects a topic hash mismatch, it will notify Cy about it to let it rectify the problem.
/// Transport frames with mismatched topic hash must be dropped; no processing at the transport layer is needed.
/// This function is not essential for the protocol to function, but it speeds up collision repair.
///
/// The function will not perform any IO and will return immediately after quickly updating an internal state.
/// It is thus safe to invoke it from a deep callback or from deep inside the transport library; the side effects
/// are confined to the Cy state only. The time complexity is logarithmic in the number of topics.
/// No effect if the topic is NULL.
void cy_on_topic_collision(cy_topic_t* const topic);

/// New message received on a topic.
/// The message ownership is taken by this function.
/// No effect if the topic is NULL.
void cy_on_message(cy_topic_t* const    topic,
                   const cy_us_t        timestamp,
                   const uint64_t       transfer_id,
                   const cy_message_t   message,
                   const cy_responder_t responder);

/// New P2P response to a message published earlier is received. The topic hash and the transfer-ID of the original
/// message are provided.
/// This function accepts a topic hash instead of a topic pointer, which is to decouple it from the topic lifetime
/// -- by the time the response is received, the topic may have been destroyed already.
/// The message ownership is taken by this function.
///
/// Observe that we do not pass a responder instance here because we assume that if any follow-up communication is
/// needed, it will take place using the normal topic publication with P2P responses.
/// At this time I am not certain if this assumption will hold. We may revise this based on empirical evidence.
void cy_on_response(cy_t* const        cy,
                    const cy_us_t      timestamp,
                    const uint64_t     topic_hash,
                    const uint64_t     transfer_id,
                    const cy_message_t message);

/// Communicates the delivery status of a reliable message published on a topic (with the topic hash and the
/// transfer-ID of the message), and a P2P response sent to a previously received message (with the topic hash and
/// the transfer-ID of the original request message).
///
/// This is GUARANTEED to be invoked EXACTLY ONCE per published message where the reliable option is set,
/// unless the publish function did not return CY_OK.
/// This function accepts a topic hash instead of a topic pointer, which is to decouple it from the topic lifetime
/// -- by the time the delivery outcome is known, the topic may have been destroyed already.
void cy_on_message_feedback(cy_t* const                 cy,
                            const uint64_t              topic_hash,
                            const uint64_t              transfer_id,
                            const bool                  success,
                            const cy_feedback_context_t context);
void cy_on_response_feedback(cy_t* const                 cy,
                             const uint64_t              topic_hash,
                             const uint64_t              transfer_id,
                             const bool                  success,
                             const cy_feedback_context_t context);

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
