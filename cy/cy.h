///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// A robust lightweight real-time decentralized pub/sub for embedded systems and robotics.
/// See the README.md for details.
///
/// Source: https://github.com/OpenCyphal-Garage/cy
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#pragma once

#include <wild_key_value.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

/// The limit could be set arbitrarily, but chosen this way for compatibility with Cyphal v1.0,
/// which only has 13-bit subject-IDs. Cyphal v1.1 will never allocate non-pinned topics in this subject-ID range.
/// For pinned topics, hash<=CY_SUBJECT_ID_PINNED_MAX. The probability of a random hash falling into the pinned
/// range is ~4.44e-16, or about one in two quadrillion, which is not practically possible.
#define CY_SUBJECT_ID_PINNED_MAX 0x1FFFU

/// This notably excludes the broadcast subject, which is always at the top, above this maximum.
/// See cy_broadcast_subject_id().
#define CY_SUBJECT_ID_MAX(modulus) (CY_SUBJECT_ID_PINNED_MAX + (modulus))

#define CY_OK 0
// error code 1 is omitted intentionally
#define CY_ERR_ARGUMENT 2
#define CY_ERR_MEMORY   3
#define CY_ERR_CAPACITY 4
#define CY_ERR_NAME     5
#define CY_ERR_MEDIA    6

typedef uint_fast8_t cy_err_t;
typedef int64_t      cy_us_t; ///< Monotonic microsecond timestamp. Signed to permit arithmetics in the past.

typedef struct cy_t          cy_t;
typedef struct cy_topic_t    cy_topic_t;
typedef struct cy_platform_t cy_platform_t;

typedef wkv_str_t      cy_str_t;
static inline cy_str_t cy_str(const char* const s) { return wkv_key(s); }

typedef enum cy_prio_t
{
    cy_prio_exceptional = 0,
    cy_prio_immediate   = 1,
    cy_prio_fast        = 2,
    cy_prio_high        = 3,
    cy_prio_nominal     = 4,
    cy_prio_low         = 5,
    cy_prio_slow        = 6,
    cy_prio_optional    = 7,
} cy_prio_t;
#define CY_PRIO_COUNT 8

/// An immutable borrowed buffer, optionally fragmented if next is not NULL. The last entry has next==NULL.
/// The optional fragmentation allows efficient handling of scatter/gather I/O without copying the data.
typedef struct cy_bytes_t
{
    size_t                   size; ///< Size of the current fragment in bytes.
    const void*              data; ///< May be NULL if size==0.
    const struct cy_bytes_t* next;
} cy_bytes_t;

/// The size is chosen to match most small closures, which is helpful when interfacing with Rust/C++ lambdas.
/// The size can be changed arbitrarily, it's a trivial trade-off between flexibility and memory usage.
/// This size must be the same for all translation units to avoid ABI incompatibilities.
#ifndef CY_USER_CONTEXT_PTR_COUNT
#define CY_USER_CONTEXT_PTR_COUNT 2
#endif

/// An opaque user context enabling the application to share data with callbacks. It is intended to be passed by value.
typedef union cy_user_context_t
{
    void*         ptr[CY_USER_CONTEXT_PTR_COUNT];
    unsigned char bytes[sizeof(void*) * CY_USER_CONTEXT_PTR_COUNT];
} cy_user_context_t;

#ifdef __cplusplus
#define CY_USER_CONTEXT_EMPTY (cy_user_context_t{})
#else
#define CY_USER_CONTEXT_EMPTY ((cy_user_context_t){ .ptr = { NULL } })
#endif

// =====================================================================================================================
//                                                  MESSAGE BUFFER
// =====================================================================================================================

/// An abstract buffer handle with a platform-specific implementation.
/// It allows the platform layer to eliminate data copying until/unless explicitly requested by the application.
/// Some transport libraries (e.g., libudpard) store the data in a set of segments obtained directly from the NIC.
/// Use cy_message_read to access the data. To retain/release instances, use refcount functions.
typedef struct cy_message_t cy_message_t;

/// It is not necessary to check the size before reading the data; the read function checks the bounds so it is
/// safe to request an out-of-bounds read; only the available data will be copied.
size_t cy_message_size(const cy_message_t* const msg);

/// This is the only way to access the received message data.
/// It gathers `size` bytes of data located at `offset` bytes from payload origin into the provided contiguous buffer.
/// The function returns the number of bytes copied.
/// If the requested range exceeds the available message size, only the available bytes are copied.
size_t cy_message_read(const cy_message_t* const msg, const size_t offset, const size_t size, void* const destination);

/// Use reference counting to manage the lifetime of message instances.
void cy_message_refcount_inc(cy_message_t* const msg);
void cy_message_refcount_dec(cy_message_t* const msg);

/// A message with an associated non-negative arrival timestamp.
/// The timestamp is carried over from the low-level NIC driver, which defines the accuracy, which is typically high
/// -- hardware timestamping in the driver can achieve microsecond accuracy.
/// The timestamp of a multi-frame transfer equals the arrival time of the first frame of that transfer.
typedef struct cy_message_ts_t
{
    cy_us_t       timestamp;
    cy_message_t* content;
} cy_message_ts_t;

// =====================================================================================================================
//                                                      FUTURE
// =====================================================================================================================

/// Futures are constructed by the library when an async operation is initiated that will complete later.
/// The future object is passed to the user-provided callback when the operation completes (successfully or not).
/// Future instances are owned by the application; the application is responsible for destroying them
/// using cy_future_destroy(). Destroying a pending future will cancel the associated operation.
typedef struct cy_future_t cy_future_t;

/// If set, invoked on future completion always; also may be invoked multiple times for progress updates while pending.
typedef void (*cy_future_callback_t)(cy_future_t*);

/// A future can transition from pending to either success or failure exactly once.
typedef enum cy_future_status_t
{
    cy_future_pending = 0,
    cy_future_success = 1,
    cy_future_failure = 2,
} cy_future_status_t;
cy_future_status_t cy_future_status(const cy_future_t* const self);

/// The result depends on the type of the future; some intermediate results may be available while still pending.
/// The lifetime of the returned pointer is bound to the lifetime of the future instance (valid until destroyed).
void* cy_future_result(cy_future_t* const self);

/// The application can store arbitrary data in the context to share information with the future callback, if used.
cy_user_context_t cy_future_context(const cy_future_t* const self);
void              cy_future_context_set(cy_future_t* const self, const cy_user_context_t context);

/// The callback is guaranteed to be invoked when the future completes (successfully or not);
/// also, it may be invoked when the future is still pending to provide intermediate progress updates.
/// Therefore, it is necessary to always check the future status inside the callback.
///
/// If the future is already completed, the callback will be invoked immediately before this function returns,
/// unless it was already set.
/// It is safe to destroy the future from within its own callback (but it is not safe to destroy another future).
cy_future_callback_t cy_future_callback(const cy_future_t* const self);
void                 cy_future_callback_set(cy_future_t* const self, const cy_future_callback_t callback);

/// Every future must be destroyed. If the future is still pending, the associated action will be cancelled.
/// A future may be destroyed from within its own callback.
/// If a future is not of interest, use this function as the future callback to ensure automatic destruction.
void cy_future_destroy(cy_future_t* const self);

// =====================================================================================================================
//                                                      PUBLISHER
// =====================================================================================================================

typedef struct cy_publisher_t cy_publisher_t;

/// Create a new publisher on the topic. The default priority value is cy_prio_nominal, it can be changed later.
/// The response_extent is the extent (maximum size) of the response data if the publisher expects responses.
/// TODO: currently, responses may arrive out-of-order; this can be easily changed in the future if/when needed
///       by adding a reordering window parameter here and implementing a simple reordering buffer in Cy.
cy_publisher_t* cy_advertise(cy_t* const cy, const cy_str_t name);
cy_publisher_t* cy_advertise_client(cy_t* const cy, const cy_str_t name, const size_t response_extent);

/// Create a new publisher that ensures that there is at most one, the most recent, message pending for transmission.
/// If a new message is published while another one is still pending, the previous one is cancelled.
/// TODO not implemented; very simple idea -- store last cancellation token in the topic and cancel it on new publish.
cy_publisher_t* cy_advertise_sample(cy_t* const cy, const cy_str_t name);

/// Publish a best-effort (non-reliable) one-way message without expecting a response.
cy_err_t cy_publish(cy_publisher_t* const pub, const cy_us_t deadline, const cy_bytes_t message);

/// Publish a reliable one-way message.
cy_future_t* cy_publish_reliable(cy_publisher_t* const pub, const cy_us_t deadline, const cy_bytes_t message);

/// Future result of a request message that expects a response.
typedef struct cy_request_result_t
{
    /// Delivery result of the request message itself.
    /// It is updated while the future is still pending, as a means to provide intermediate progress feedback.
    // cy_publish_result_t request;

    /// The response is valid only if the future status is cy_future_success.
    /// It is updated with every received response; the arrival of new responses can be monitored using either
    /// a future callback or by checking the seqno counter.
    /// The message contents can be moved out using cy_message_move(); if not moved out, it will be destroyed
    /// when the future is destroyed.
    struct cy_request_result_response_t
    {
        cy_message_ts_t message;
        uint64_t        remote_id; ///< Uniquely identifies the remote node that sent the response within the network.
        uint64_t        seqno;     ///< Incremented by the remote (sic) with each response sent; starts at zero.
    } response;
} cy_request_result_t;

/// The first received P2P response transfer will be awaited from any remote node that received the published message.
/// The future result is of type cy_request_result_t.
/// The future will be updated when the request delivery feedback is available (intermediate update) and when
/// the response is received. The future will enter the completed state after the first response, and it will
/// continue to receive further responses if the remote chooses to send more; the future will remain completed.
/// The application can monitor the seqno field in the response to detect new responses.
/// To stop receiving further responses, the application must destroy the future.
cy_future_t* cy_request(cy_publisher_t* const pub,
                        const cy_us_t         delivery_deadline,
                        const cy_us_t         first_response_deadline,
                        const cy_bytes_t      message);

/// Defaults to cy_prio_nominal for all newly created publishers.
cy_prio_t cy_priority(const cy_publisher_t* const pub);
void      cy_priority_set(cy_publisher_t* const pub, const cy_prio_t priority);

/// A message will be retransmitted if there is no acknowledgment within this timeout period.
/// This timeout is only a hint that can be altered by the library according to heuristics;
/// in particular, each subsequent retransmission uses a larger timeout.
/// A sensible default is automatically chosen when the publisher is created; it rarely needs to be changed.
cy_us_t cy_ack_timeout(const cy_publisher_t* const pub);
void    cy_ack_timeout_set(cy_publisher_t* const pub, const cy_us_t timeout);

/// Each publisher is always linked to a specific single topic.
/// This pointer remains valid for the entire lifetime of the publisher.
/// It can be used to obtain the topic name, hash, etc. of this publisher.
cy_topic_t* cy_publisher_topic(const cy_publisher_t* const pub);

/// All pending futures created by this publisher, if any, will be cancelled.
void cy_unadvertise(cy_publisher_t* const pub);

// =====================================================================================================================
//                                                      SUBSCRIBER
// =====================================================================================================================

typedef struct cy_subscriber_t cy_subscriber_t;

/// This ought to be enough for any reasonable transport-specific state.
/// For example, IPv4 with 3 redundant transfers would need (4 bytes IP + 2 bytes port) * 3 = 18 bytes plus padding.
/// IPv6 would likely need north of 64 bytes, but at the moment we don't have any transport that would require that.
/// It can be changed easily as the library makes no assumptions about the size of this state.
#ifndef CY_RESPONSE_CONTEXT_BYTES
#define CY_RESPONSE_CONTEXT_BYTES 24U
#endif

/// Received transfers are given this copyable instance to allow sending P2P response transfers back to the sender.
/// It can be copied / passed by value. It can be trivially discarded if no response is needed.
///
/// This object avoids linking the topic instance that delivered the original message to avoid lifetime
/// issues that would occur if the topic is destroyed between the message arrival and the response time.
/// Instead of referencing the topic, the relevant parameters of the topic are stored here by value.
typedef struct cy_p2p_context_t
{
    unsigned char state[CY_RESPONSE_CONTEXT_BYTES];
} cy_p2p_context_t;

/// Stores the origin information of a received message to allow sending a P2P response back to the sender.
/// None of the fields may be altered by the application.
///
/// The triplet of (remote-ID, topic hash, request tag) uniquely identifies the original message within the network.
/// Consequently, if response streaming is used, it uniquely identifies the response stream.
/// One can obtain a convenient 64-bit stream identifier by hashing these three values together; given a good hash,
/// the collision probability is astronomically low and is negligible for all practical purposes:
///
///     const uint64_t key[3] = { b->remote_id, b->topic_hash, b->message_tag };
///     return rapidhash(key, sizeof(key));
///
typedef struct cy_breadcrumb_t
{
    cy_t*     cy;       ///< The owning Cy instance.
    cy_prio_t priority; ///< The response priority matches the priority of the original message.

    /// Stream identifier triplet. Can be hashed down to a single 64-bit value if needed.
    uint64_t remote_id;   ///< Uniquely identifies the source node within the network.
    uint64_t topic_hash;  ///< Identifies the topic the original request message was received from.
    uint64_t message_tag; ///< The tag of the original request message this breadcrumb can respond to.

    uint64_t         seqno; ///< Incremented with each response sent (incl. failed); starts at zero.
    cy_p2p_context_t p2p_context;
} cy_breadcrumb_t;

typedef struct cy_substitution_t
{
    cy_str_t str;     ///< The substring that matched the substitution token in the pattern. Not NUL-terminated.
    size_t   ordinal; ///< Zero-based index of the substitution token as occurred in the pattern.
} cy_substitution_t;

/// When a name pattern match occurs, Cy will store the string substitutions that had to be made to
/// achieve the match. The substitutions are listed in the order of their occurrence in the pattern.
/// For example, if the pattern is "ins/*/data/#" and the key is "ins/0/data/foo/456",
/// then the substitutions will be (together with their ordinals):
///  1. #0 "0"
///  2. #1 "foo"
///  3. #1 "456"
typedef struct cy_substitution_set_t
{
    size_t                   count;         ///< The size of the following substitutions array.
    const cy_substitution_t* substitutions; ///< A contiguous array of substitutions of size `count`.
} cy_substitution_set_t;

/// Event information for a received message from a topic subscription.
typedef struct cy_arrival_t
{
    /// The message will be given with refcount=1. If the application needs to keep it after return from the callback,
    /// it must increment the refcount using cy_message_refcount_inc() to avoid premature destruction.
    cy_message_ts_t message;

    /// Use cy_respond() to send a P2P response directly to the publisher of this message if needed.
    /// Multiple responses can be sent if necessary; each will carry a unique sequence number starting from zero.
    /// If responses are needed, this instance should be copied by value only once, as it keeps internal state.
    /// If multiple subscribers will be sending responses, they must coordinate to use a shared breadcrumb instance
    /// to avoid seqno counter discontinuity. If no responses are needed, this instance can be discarded.
    cy_breadcrumb_t breadcrumb;

    /// The topic that the message was received from; always non-NULL.
    ///
    /// For verbatim subscribers, the topic pointer is always the same, and the substitution set is always empty.
    /// For pattern subscribers, the topic pointer refers to the matched topic instance, which may change,
    /// and the substitution set contains at least one entry.
    ///
    /// The lifetime of the substitutions is bound to the lifetime of the topic, which is guaranteed to remain alive
    /// as long as there is at least one verbatim subscriber or at least one publisher on it. Topics that only have
    /// pattern subscribers are eventually destroyed after a long time of inactivity, which is reset after every
    /// received message (among some other events not necessarily visible to the application).
    cy_topic_t*           topic;
    cy_substitution_set_t substitutions;
} cy_arrival_t;

/// The arrival pointer is mutable to allow moving the message out of it if needed.
/// The lifetime of the arrival struct ends upon return from the current callback.
typedef void (*cy_subscriber_callback_t)(cy_subscriber_t*, cy_arrival_t);

// Future note: eventually, we may want to support sampling subscription pattern:
// keep the last arrival inside the subscriber instance, and add a function to query it outside of the callback.

/// We intentionally use the exact same API for both verbatim and pattern subscriptions; this is a key design feature.
///
/// There may be more than one subscriber with the same name (pattern). The library will only keep one
/// reference-counted topic; upon message arrival, all matching subscribers will be invoked in an unspecified order.
/// Each subscriber may use distinct parameters (extent, reordering, etc).
cy_subscriber_t* cy_subscribe(cy_t* const cy, const cy_str_t name, const size_t extent);

/// The reordering window must be non-negative.
cy_subscriber_t* cy_subscribe_ordered(cy_t* const    cy,
                                      const cy_str_t name,
                                      const size_t   extent,
                                      const cy_us_t  reordering_window);

cy_user_context_t cy_subscriber_context(const cy_subscriber_t* const self);
void              cy_subscriber_context_set(cy_subscriber_t* const self, const cy_user_context_t context);

cy_subscriber_callback_t cy_subscriber_callback(const cy_subscriber_t* const self);
void cy_subscriber_callback_set(cy_subscriber_t* const self, const cy_subscriber_callback_t callback);

/// Copies the subscriber name into the user-supplied buffer. Max size is CY_TOPIC_NAME_MAX plus NUL-terminator.
/// The output string is NUL-terminated.
void cy_subscriber_name(const cy_subscriber_t* const self, char* const out_name);

/// No effect if the subscriber pointer is NULL.
void cy_unsubscribe(cy_subscriber_t* const self);

/// If streaming responses are used, streaming should continue only as long as the response futures materialize to
/// cy_response_acknowledged; otherwise, the stream should be ceased.
///
/// A known ambiguity exists if the server sends a reliable response that is accepted, but the pack is lost;
/// the server will retransmit the response, but the client application may no longer be listening if it only needed
/// a single response; the second response will be a nack instead of a pack.
/// TODO If this becomes a problem, store a short list of recently positively-acked responses in the Cy state.
typedef enum cy_response_status_t
{
    cy_response_timeout      = 0, ///< Remote did not respond before the deadline.
    cy_response_acknowledged = 1, ///< Remote responded and acknowledged the response.
    cy_response_rejected     = 2, ///< Remote received the response but the application is no longer interested in it.
} cy_response_status_t;

/// Future result of sending a reliable response message.
/// The future will succeed iff the response is cy_response_acknowledged.
typedef struct cy_response_result_t
{
    cy_response_status_t status;
    uint64_t seqno; ///< The unique sequence number used for this response message. Constant, always available.
} cy_response_result_t;

/// Send a best-effort response to a message previously received from a topic subscription.
/// The response will be sent directly to the publisher using peer-to-peer transport, not affecting other nodes.
/// This can be invoked from a subscription callback or at any later point as long as the breadcrumb is available.
/// There may be an arbitrary number of responses sent per received message; we call these streamed RPC responses.
/// Each response will carry a unique sequence number starting from zero, generated automatically by Cy.
/// For reliable responses use cy_respond_reliable().
cy_err_t cy_respond(cy_breadcrumb_t* const breadcrumb, const cy_us_t deadline, const cy_bytes_t message);

/// Reliable counterpart of cy_respond() that provides the delivery success feedback via a future.
/// This is useful for streamed RPC responses where the server (the sender) needs to know whether the client
/// is still listening or has gone away (in which case streaming should be ceased).
///
/// The future result is of type cy_response_result_t. The seqno field is always available immediately upon future
/// creation; the acknowledged field becomes true when/if the remote node acknowledges reception of the response.
/// Destruction of the future will cancel the response if it is still pending transmission.
cy_future_t* cy_respond_reliable(cy_breadcrumb_t* const breadcrumb, const cy_us_t deadline, const cy_bytes_t message);

// =====================================================================================================================
//                                                  NODE & TOPIC
// =====================================================================================================================

/// The new instance will be heap-allocated via the platform layer API.
cy_t* cy_new(cy_platform_t* const platform);

/// Cy will clean up all resources obtained from the platform, such as memory and readers/writers, but will not
/// destroy the platform instance itself; the application is responsible for that.
void cy_destroy(cy_t* const cy);

/// The async error handler is used to report errors occurring in Cy asynchronously with API invocations.
/// In particular, it is used for topic resubscription errors occurring in response to consensus updates,
/// and also in cases where Cy is unable to create an implicit subscription on pattern match due to lack of memory.
///
/// Normally, the error handler does not need to do anything specific aside from perhaps logging the error or updating
/// relevant performance counters. Cy will keep attempting to repeat the failing operation continuously until it
/// succeeds or the condition requiring the operation is lifted.
///
/// Since Cy is a single-file library, the line number uniquely identifies the error site.
/// The topic pointer may be NULL depending on the nature of the error.
///
/// The default handler will simply CY_TRACE() the error, which is a no-op unless tracing is enabled.
typedef void (*cy_async_error_handler_t)(cy_t*, cy_topic_t*, cy_err_t, uint16_t line_number);
void cy_async_error_handler_set(cy_t* const cy, const cy_async_error_handler_t handler);

/// See cy_name_... for name resolution details. The provided names will be validated and normalized.
/// The home should be unique in the network; one way to ensure this is to default it to the node's unique ID.
/// The returned strings are NUL-terminated. The lifetime is bound to the Cy instance.
/// Mutators fail if the supplied string is invalid.
/// The default home and namespace are empty. They should not be changed after the first topic is created.
cy_str_t cy_home(const cy_t* const cy);
cy_str_t cy_namespace(const cy_t* const cy);
cy_err_t cy_home_set(cy_t* const cy, const cy_str_t home);
cy_err_t cy_namespace_set(cy_t* const cy, const cy_str_t name_space);

/// This function must be invoked periodically to ensure liveness.
/// The returned value indicates the success of the gossip publication, if any took place, or zero.
/// Transient failures normally should be logged & ignored.
/// The function will return not later than the specified deadline. It may return early.
cy_err_t               cy_spin_until(cy_t* const cy, const cy_us_t deadline);
static inline cy_err_t cy_spin_once(cy_t* const cy) { return cy_spin_until(cy, 0); }

/// The current time in microseconds sourced from the platform layer as-is. Always non-negative.
cy_us_t cy_now(const cy_t* const cy);

/// The time since cy_new() in microseconds.
cy_us_t cy_uptime(const cy_t* const cy);

/// The strings will be copied into an internal storage, so they don't have to survive after this call.
/// The effect is incremental. If a remapping for the same "from" already exists, it will be replaced with the new "to".
/// On error, the node remap configuration is left unchanged.
/// TODO not implemented
cy_err_t cy_remap(cy_t* const cy, const cy_str_t from, const cy_str_t to);

/// Like cy_remap(), but the remappings are read from a string of the form "from1=to1 from2=to2 "...
/// and applied sequentially via cy_remap(). The effect of multiple invocations is incremental.
/// The from/to are separated with `=` (equals), and the pairs are separated with ASCII whitespaces " \t\n\r\x0b\x0c".
/// This is designed to support single-string configuration parameters storing all remappings in one place.
/// Invalid pairs are ignored. The string does not have to survive after this call.
/// On error, the node remap configuration may be left in an inconsistent state.
/// TODO not implemented
cy_err_t cy_remap_parse(cy_t* const cy, const cy_str_t spec_string);

/// Invokes cy_name_resolve() using the home and the namespace of the node, then applies remapping, if any.
/// The result is a fully resolved topic name.
/// On failure, the output string has length SIZE_MAX and NULL data pointer.
cy_str_t cy_resolve(const cy_t* const cy, const cy_str_t name, const size_t dest_size, char* dest);

// TODO: add a way to dump/restore topic configuration for instant initialization. This may be platform-specific.

/// Complexity is logarithmic in the number of topics. NULL if not found.
/// In practical terms, these queries are very fast and efficient.
cy_topic_t* cy_topic_find_by_hash(const cy_t* const cy, const uint64_t hash);
cy_topic_t* cy_topic_find_by_name(const cy_t* const cy, const cy_str_t name);

/// Iterate over all topics in an unspecified order.
/// This is useful when handling IO multiplexing (building the list of descriptors to read) and for introspection.
/// The iteration stops when the returned topic is NULL.
/// The set of topics SHALL NOT be mutated while iterating over it (a restart will be needed otherwise).
/// Usage:
///     for (cy_topic_t* topic = cy_topic_iter_first(cy); topic != NULL; topic = cy_topic_iter_next(topic)) {
///         ...
///     }
cy_topic_t* cy_topic_iter_first(const cy_t* const cy);
cy_topic_t* cy_topic_iter_next(cy_topic_t* const topic);

/// The name pointer lifetime is bound to the topic. The name is NUL-terminated.
cy_str_t cy_topic_name(const cy_topic_t* const topic);
uint64_t cy_topic_hash(const cy_topic_t* const topic);
cy_t*    cy_topic_owner(const cy_topic_t* const topic);

/// Reliable delivery is guaranteed to at most this many subscribers on a topic; excess are best-effort.
/// The limit is intended to bound memory use on high-fanout topics.
/// A sensible default is provided that is large enough for most scenarios, so usually this does not need changing.
/// Changes will take effect eventually.
size_t cy_topic_association_limit(const cy_topic_t* const topic);
void   cy_topic_association_limit_set(cy_topic_t* const topic, const size_t limit);

/// Provides access to the application-specific context associated per topic.
/// By default it is set to CY_USER_CONTEXT_EMPTY when the topic is created.
/// It can be used to associate arbitrary application-specific data with the topic.
/// Returns NULL iff the topic pointer is NULL.
cy_user_context_t* cy_topic_user_context(cy_topic_t* const topic);

// =====================================================================================================================
//                                                      NAMES
// =====================================================================================================================

/// Shorter topic names reduce the gossip traffic overhead.
/// In CAN FD networks, normalized topic names should not exceed 48 characters to avoid multi-frame gossips.
/// This limit is chosen rather arbitrarily, keeping in mind RTPS where the maximum is 255,
/// and ROS2 where the maximum is 248. In practice, topics very rarely exceed ~100 characters.
#define CY_TOPIC_NAME_MAX 200

/// A valid name consists of printable ASCII characters except SPACE.
/// A normalized name does not begin with a separator, does not end with a separator, and does not contain
/// consecutive separators.
extern const char cy_name_sep;  ///< `/`
extern const char cy_name_home; ///< `~` -- replaced with the home of the current node. Homes should be unique.
extern const char cy_name_one;  ///< `*` -- matches any single name component: "abc/*/def" => "abc/123/def".
extern const char cy_name_any;  ///< `>` -- matches zero or more components: "abc/>" => "abc", "abc/def", "abc/def/ghi".

/// True iff the given name is valid according to the Cy naming rules. An empty name is not a valid name.
bool cy_name_is_valid(const cy_str_t name);

/// Returns true iff the name can only match a single topic, which is called a verbatim name;
/// conversely, returns false for patterns that can match more than one topic.
/// This is useful for some applications that want to ensure that certain names can match only one topic.
///
/// There may be at most one zero-or-more substitution token used, and if used, it must be the last token of the name.
/// Otherwise, the behavior is currently unstable; it is well-defined internally but may change between minor versions
/// and result in wire compatibility issues.
bool cy_name_is_verbatim(const cy_str_t name);

/// Whether the name is relative to the home namespace ~ or is absolute.
bool cy_name_is_homeful(const cy_str_t name);
bool cy_name_is_absolute(const cy_str_t name);

/// Joins two (potentially empty) names with cy_name_sep, normalizing both parts, such that the result is
/// a normalized name. Either part may be empty, in which case it behaves like normalization of the other part.
/// On failure, the output string has length SIZE_MAX and NULL data pointer.
/// The destination is not NUL-terminated.
cy_str_t cy_name_join(const cy_str_t left, const cy_str_t right, const size_t dest_size, char* const dest);

/// If cy_name_is_homeful(name), expands the home prefix using the provided home string;
/// otherwise, returns the normalized name.
/// The result is normalized and written into dest, which must be at least dest_size bytes long.
/// On failure, the output string has length SIZE_MAX and NULL data pointer.
/// The destination is not NUL-terminated.
cy_str_t cy_name_expand_home(cy_str_t name, const cy_str_t home, const size_t dest_size, char* const dest);

/// Constructs the full normalized name as exchanged over the wire prior to remapping: homeful names are expanded,
/// relative names are prefixed with the namespace, and absolute names are left as-is.
/// The namespace may be homeful and will be expanded accordingly. Examples:
///
///     name="foo/bar"      namespace="ns1"     home="me"   => "ns1/foo/bar"
///     name="~//foo/bar"   namespace="ns1"     home="me"   => "me/foo/bar"
///     name="/foo//bar/"   namespace="ns1"     home="me"   => "foo/bar"
///     name="foo/bar/"     namespace="~//ns1"  home="me"   => "me/ns1/foo/bar"
///
/// The dest points to a buffer at least dest_size bytes long.
/// On failure, the output string has length SIZE_MAX and NULL data pointer.
/// The destination is not NUL-terminated.
///
/// TODO: add remapping set.
cy_str_t cy_name_resolve(const cy_str_t name,
                         cy_str_t       name_space,
                         const cy_str_t home,
                         const size_t   dest_size,
                         char*          dest);

// =====================================================================================================================
//                                                  MONITORING & DIAGNOSTICS
// =====================================================================================================================

// TODO: topic hooks: extern functions similar to cy_trace invoked when a topic is created/destroyed/(un)subscribed/etc.

/// If CY_CONFIG_TRACE is defined and is non-zero, cy_trace() shall be defined externally.
#ifndef CY_CONFIG_TRACE
#define CY_CONFIG_TRACE 0
#endif
#if CY_CONFIG_TRACE
#define CY_TRACE(cy, ...) cy_trace(cy, __FILE__, __LINE__, __func__, __VA_ARGS__)
#else
#define CY_TRACE(cy, ...) (void)cy
#endif

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
