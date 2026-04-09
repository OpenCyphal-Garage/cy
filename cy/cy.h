//                            ____                   ______            __          __
//                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
//                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
//                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
//                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
//                             /_/                     /____/_/
//
// A robust lightweight real-time decentralized pub/sub for embedded systems and robotics.
// See the README.md for details.
//
// Source: https://github.com/OpenCyphal-Garage/cy
// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#pragma once

#include <wild_key_value.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

#define CY_OK 0
// error code 1 is omitted intentionally
#define CY_ERR_ARGUMENT 2
#define CY_ERR_MEMORY   3
#define CY_ERR_CAPACITY 4 // May be used by the platform layer if any resource is depleted (e.g., queue size).
#define CY_ERR_NAME     5
#define CY_ERR_MEDIA    6  // Generic low-level network error from the underlying platform layer.
#define CY_ERR_LAG      7  // Strong scheduler lag detected. Non-real-time systems may ignore.
#define CY_ERR_DELIVERY 8  // Reliable message (publication or response) was not acknowledged by the remote(s).
#define CY_ERR_LIVENESS 9  // Message (publication or response) did not arrive on time.
#define CY_ERR_NACK     10 // Explicitly rejected by the remote.

/// The limit could be set arbitrarily, but chosen this way for compatibility with Cyphal v1.0,
/// which only has 13-bit subject-IDs. Cyphal v1.1 will never allocate non-pinned topics in this subject-ID range.
/// Pinned topics are identified by evictions >= (UINT32_MAX - CY_SUBJECT_ID_PINNED_MAX).
/// The pinned subject-ID is UINT32_MAX - evictions.
#define CY_SUBJECT_ID_PINNED_MAX 0x1FFFU

/// This notably excludes the broadcast subject and gossip shards, which are always at the top, above this maximum.
#define CY_SUBJECT_ID_MAX(modulus) (CY_SUBJECT_ID_PINNED_MAX + (modulus))

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
/// No effect if the message pointer is NULL.
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
///
/// There are functions that operate only on specific polymorphic type of future; they always include runtime type
/// checking, such that invocation with a wrong polymorphic future type will be detected and handled gracefully.
/// E.g., invoking cy_response_move() on a future from cy_publish_reliable() is incorrect but well-defined and safe.
typedef struct cy_future_t cy_future_t;

/// If set, invoked on future completion always; also may be invoked multiple times for progress updates while pending.
typedef void (*cy_future_callback_t)(cy_future_t*);

/// State queries. Transient errors may occur while not done, they may also trigger callbacks. CY_OK indicates success.
bool     cy_future_done(const cy_future_t* const self);
cy_err_t cy_future_error(const cy_future_t* const self);

/// The application can store arbitrary data in the context to share information with the future callback, if used.
cy_user_context_t cy_future_context(const cy_future_t* const self);
void              cy_future_context_set(cy_future_t* const self, const cy_user_context_t context);

/// The callback is guaranteed to be invoked when the future completes (successfully or not);
/// also, it may be invoked when the future is still pending to provide intermediate progress updates.
/// Therefore, it is necessary to always check the future done()/error() inside the callback.
///
/// If the future is already completed, the callback will be invoked immediately before this function returns,
/// unless it was already set. This is why the context must be set BEFORE setting the callback!
/// It is safe to destroy the future from within its own callback (but it is not safe to destroy another future).
cy_future_callback_t cy_future_callback(const cy_future_t* const self);
void                 cy_future_callback_set(cy_future_t* const self, const cy_future_callback_t callback);

/// Every future must be destroyed. If the future is still pending, the associated action will be cancelled.
/// A future may be destroyed from within its own callback.
/// If the future outcome is not of interest, use this function as the future callback to ensure automatic destruction.
/// Note: the actual memory deallocation may happen at a later time depending on the future implementation.
void cy_future_destroy(cy_future_t* const self);

// =====================================================================================================================
//                                                      PUBLISHER
// =====================================================================================================================

typedef struct cy_publisher_t cy_publisher_t;

/// Create a new publisher on the topic. The default priority value is cy_prio_nominal, it can be changed later.
/// The response_extent is the extent (maximum size) of the response data if the publisher expects responses;
/// see cy_request() for details.
cy_publisher_t* cy_advertise(cy_t* const cy, const cy_str_t name);
cy_publisher_t* cy_advertise_client(cy_t* const cy, const cy_str_t name, const size_t response_extent);

/// Publish a best-effort (non-reliable) one-way message without expecting a response.
cy_err_t cy_publish(cy_publisher_t* const pub, const cy_us_t deadline, const cy_bytes_t message);

/// Publish a reliable one-way message.
///
/// Reliable messages consume more memory for associated states and are a greater burden on the network and nodes
/// compared to best-effort messages. A best-effort message is simply sent out to the network expecting the transport
/// to deliver it to all interested parties (do its best, no guarantees). A reliable message requires every recipient
/// to unicast an acknowledgement back to the publisher, which may create nontrivial traffic on high-fanout topics.
///
/// The session layer tracks remote subscribers (called associations) using a simple stateless protocol and
/// ensures that all live subscribers confirm message reception, retransmitting as necessary, switching between
/// multicast and unicast strategies as necessary to manage network utilization. The association set management,
/// retransmission, ack deduplication, and related bookkeeping are hidden from the application.
/// The application will observe future failure if no subscriber confirms reception before the deadline.
///
/// The first publication on a topic will assume success upon arrival of the first acknowledgement; the association set
/// will be built in the background following the first publication; all subsequent publications will use & update it.
///
/// Errors are non-fatal: attempts to deliver will continue regardless until canceled or timed out, but the
/// future callback (if set) is triggered on every error, and the future remains non-done until acked or timed out
/// (or destroyed by the application).
/// Newer errors override older ones; to handle every error, callback is needed.
/// Platform errors encountered on send are forwarded as-is. Other possible errors include:
/// CY_OK: Message delivered successfully.
/// CY_ERR_DELIVERY: Message not delivered.
/// CY_ERR_LAG: Strong scheduler lag prevented full ack timeout utilization; reachability information incomplete.
///
/// TODO API for querying the tracked associations and per-remote delivery success may be added in the future since it
///   is expected that some applications would benefit from the knowledge of which specific remotes accept their data.
cy_future_t* cy_publish_reliable(cy_publisher_t* const pub, const cy_us_t deadline, const cy_bytes_t message);

/// Models a single response to a request sent with cy_request(). There may be several of those received from different
/// remote nodes and also multiple response messages from the same remote node if response streaming is used.
/// This is obtained from the request future using cy_response_borrow()/_move().
///
/// The tuple of sender ID and seqno uniquely identifies each response per message.
/// For a globally unique identifier, add the tag of the original message as well.
///
/// Information on reliability, priority, etc. is intentionally not exposed; may change in the future if needed.
typedef struct cy_response_t
{
    uint64_t remote_id; ///< Uniquely identifies the source node within the network.
    uint64_t seqno;     ///< If the remote streams multiple responses, each response increments seqno starting from 0.

    cy_message_ts_t message;
} cy_response_t;

/// This is similar to cy_publish_reliable() except that we also wait for the remote(s) to send unicast response(s).
/// The response timeout is added to the delivery deadline to obtain the total time to wait for the first response;
/// for subsequent responses it is used as the maximum inter-response interval for liveness monitoring to alert the
/// application when responses cease to arrive. The application may destroy the future at any moment (e.g., if it
/// needs no further responses).
///
/// The future will continue to receive responses as long as it is alive, even after the liveness monitoring timeout.
/// Each received response resets the liveness timeout, which implies that the future may flip between done/pending
/// multiple times until destroyed. The CY_ERR_LIVENESS is cleared if the response arrives after the timeout.
/// Liveness state is independent from response queue state: if CY_ERR_LIVENESS is reported, a queued unread response
/// may still be present.
///
/// Received deduplicated responses are stored in the future; the application should retrieve them using
/// cy_response_borrow()/_move().
/// The queue length is 1; on overflow, the old entry is replaced. To process all responses, the application needs to
/// either set the future callback, which will be invoked per every received response, or to poll the future
/// sufficiently frequently to avoid overrun.
///
/// If the remote node that sends the responses uses reliable delivery, it will be able to monitor whether the
/// requester is still listening for responses (i.e., whether the future is still alive):
/// once the future is destroyed, the local node will respond to further responses from the remote node with negative
/// acknowledgments, which the remote application can use to decide when to cease responding if streaming is used.
///
/// Responses may arrive out of order depending on the behavior of the underlying network; the library does not attempt
/// to reconstruct the original seqno ordering. It is guaranteed that each response arrives at most once. If multiple
/// ordering-sensitive responses are expected, the application should monitor the seqno field, which starts at zero
/// per remote and is incremented with each response from that remote.
///
/// We may also provide a function for querying the delivery status, such that the client is aware if the remote(s)
/// have acknowledged the request.
cy_future_t* cy_request(cy_publisher_t* const pub,
                        const cy_us_t         delivery_deadline, // Attempt to reliably deliver the request until this
                        const cy_us_t         response_timeout,  // NB: this is relative time, not a deadline!
                        const cy_bytes_t      message);

/// Polymorphic type check: true if the future is not NULL and is a request future.
bool cy_is_request(const cy_future_t* const future);

/// If the request future holds a received response, cy_response_move() fetches that response and demotes the future
/// state back to pending unless it is in the liveness timeout state CY_ERR_LIVENESS, in which case it will remain done.
/// cy_response_borrow() returns the message but also keeps the original unchanged.
///
/// If no response is available, the message pointer will be NULL.
/// Responses will be lost if the application neglects to fetch one prior to the next response arrival; i.e.,
/// the queue is limited to only one, most recent sample.
///
/// This is not idempotent -- the response is moved to the application.
/// The application MUST use cy_message_refcount_dec() when done with the message.
cy_response_t cy_response_borrow(const cy_future_t* const future);
cy_response_t cy_response_move(cy_future_t* const future);

/// Number of responses received so far.
uint64_t cy_response_count(const cy_future_t* const future);

/// Defaults to cy_prio_nominal for all newly created publishers.
/// Changing the priority may affect the reliable delivery timeout, so if a specific timeout value is needed,
/// it should be set after setting the priority.
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

/// The application MUST destroy all futures created by this publisher instance beforehand.
void cy_unadvertise(cy_publisher_t* const pub);

// =====================================================================================================================
//                                                      SUBSCRIBER
// =====================================================================================================================

/// This ought to be enough for any reasonable transport-specific state.
/// For example, IPv4 with 3 redundant transfers would need (4 bytes IP + 2 bytes port) * 3 = 18 bytes plus padding.
/// IPv6 would likely need north of 64 bytes, but at the moment we don't have any transport that would require that.
/// It can be changed easily as the library makes no assumptions about the size of this state.
#ifndef CY_RESPONSE_CONTEXT_BYTES
#define CY_RESPONSE_CONTEXT_BYTES 24U
#endif

/// Received transfers are given this copyable instance to allow sending unicast response transfers back to the sender.
/// It can be copied / passed by value. It can be trivially discarded if no response is needed.
///
/// This object avoids linking the topic instance that delivered the original message to avoid lifetime
/// issues that would occur if the topic is destroyed between the message arrival and the response time.
/// Instead of referencing the topic, the relevant parameters of the topic are stored here by value.
typedef struct cy_unicast_context_t
{
    unsigned char state[CY_RESPONSE_CONTEXT_BYTES];
} cy_unicast_context_t;

/// Stores the origin information of a received message to allow sending a unicast response back to the sender.
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

    uint64_t             seqno; ///< Incremented with each response sent; starts at zero.
    cy_unicast_context_t unicast_ctx;
} cy_breadcrumb_t;

/// Event information for a received message from a topic subscription.
typedef struct cy_arrival_t
{
    /// Messages are shared and reference counted. See cy_message_refcount_inc()/_dec().
    cy_message_ts_t message;

    /// Use cy_respond() to send a unicast response directly to the publisher of this message if needed.
    /// Multiple responses can be sent if necessary; each will carry a unique sequence number starting from zero.
    /// If responses are needed, this instance should be copied by value only once, as it keeps internal state.
    /// If multiple subscribers will be sending responses, they must coordinate to use a shared breadcrumb instance
    /// to avoid seqno counter discontinuity. If no responses are needed, this instance can be discarded.
    ///
    /// The breadcrumb also contains the hash of the topic that this message was received from.
    /// For verbatim subscribers, the topic is always the same.
    /// For pattern subscribers, the topic hash refers to the matched topic, which may change for distinct messages.
    /// The topic hash can be used to retrieve the topic later using cy_topic_find_by_hash(), and
    /// -- most importantly! -- it can be used to obtain the topic name substitutions that had to be made to match
    /// the subscription name pattern if this is a pattern subscriber. Verbatim subscribers have no pattern
    /// substitutions. See cy_subscriber_substitutions().
    cy_breadcrumb_t breadcrumb;
} cy_arrival_t;

/// We intentionally use the exact same API for both verbatim and pattern subscriptions; this is a key design feature.
///
/// There may be more than one subscriber with the same name (pattern). The library will only keep one
/// reference-counted topic; upon message arrival, all matching subscribers will be invoked in an unspecified order.
/// Each subscriber may use distinct parameters (extent, reordering, etc).
///
/// All received messages are stored into a one-message-deep queue in the future instance. The future becomes done
/// when there is at least one pending message, or when the liveness timeout is enabled and has expired (no messages
/// seen for the specified time). The application can either poll the future using cy_future_done() or
/// cy_arrival_count(), or it can set up a callback to be invoked when new messages arrive via cy_future_callback_set().
/// Received messages can be retrieved using cy_arrival_borrow()/_move().
///
/// By default, liveness monitoring is disabled -- a subscriber future will only be marked as done when a new message
/// is available. If liveness monitoring is enabled, when arrivals cease, the future will materialize after the
/// liveness timeout with CY_ERR_LIVENESS and the callback will be invoked if set.
///
/// The regular subscriber does not guarantee that messages arrive in the same order as they are published.
/// It does, however, guarantee that each arrives at most once.
///
/// Possible errors include:
/// CY_OK: No errors. If done, message received successfully.
/// CY_ERR_MEMORY: Could not allocate auxiliary state, message dropped. Note that memory exhaustion may cause loss
/// at the lower layers of the stack, which will not be detected via this API.
/// CY_ERR_LIVENESS: No messages received for the specified timeout (disabled by default).
cy_future_t* cy_subscribe(cy_t* const cy, const cy_str_t name, const size_t extent);

/// A variant of subscriber that ensures that messages are delivered in the same order they are sent by the remotes,
/// with ordering guaranteed on a per-remote basis. This is to say that ordering is not ensured for messages that
/// originate from distinct remotes, as that would require global synchronization which is outside of the scope of
/// the session layer.
///
/// The reordering window specifies the maximum amount of time to delay messages received out of order before they
/// are forcibly ejected to the application; it must be non-negative. Force ejection implies that if late missing
/// messages apply later, they will be dropped since ejecting them would violate the ordering constraint.
cy_future_t* cy_subscribe_ordered(cy_t* const    cy,
                                  const cy_str_t name,
                                  const size_t   extent,
                                  const cy_us_t  reordering_window);

/// Polymorphic type check: true if the specified future is not NULL and is a subscriber.
bool cy_is_subscriber(const cy_future_t* const future);

/// When a new message is received, the subscribe future becomes done. The message can be accessed via borrow/move.
/// If no message is available (future not done), returns a default-inited arrival struct with NULL message.
///
/// The borrow version provides access to the received message without erasing it from the subscriber instance.
/// This is useful when a subscriber is used as a sampling port, always keeping the most recent message.
/// The application may opt to keep the message alive if needed using cy_message_refcount_inc().
///
/// The moving version transfers message ownership to the application; the future will transition from done to pending
/// unless it has encountered a liveness timeout.
/// The application MUST use cy_message_refcount_dec() when done with the message to release memory.
///
/// If the message is not moved by the time the next one arrives, the old message is replaced with the new one
/// (the application may still retain the old one if needed by adjusting the refcount accordingly).
cy_arrival_t cy_arrival_borrow(const cy_future_t* const future);
cy_arrival_t cy_arrival_move(cy_future_t* const future);

/// Number of unique messages successfully received by the subscriber so far.
uint64_t cy_arrival_count(const cy_future_t* const future);

/// A non-positive value disables the liveness timeout; it is disabled by default.
/// When enabled, lack of messages for this long resolves the future with CY_ERR_LIVENESS.
///
/// When used with ordered subscribers, out of order messages may be interned for up to the reordering_window prior
/// to ejection, which may cause liveness timeout to be reported even though there are pending interned messages.
/// A related edge case to be aware of is when an interned message is ejected, given large enough ejection delay,
/// the liveness timeout may fire immediately afterward since it is measured relative to the original arrival timestamp.
///
/// Takes effect immediately, implying that if the last message was received more than timeout ago (or subscriber
/// constructed more than timeout ago and no messages seen), the liveness error will fire on next spin.
/// cy_subscriber_timeout_set() will reset CY_ERR_LIVENESS if set regardless of the argument.
cy_us_t cy_subscriber_timeout(const cy_future_t* const future);
void    cy_subscriber_timeout_set(cy_future_t* const future, const cy_us_t timeout);

/// Copies the subscriber name into the user-supplied buffer. Max size is CY_TOPIC_NAME_MAX plus NUL-terminator.
/// The output string is NUL-terminated.
void cy_subscriber_name(const cy_future_t* const future, char* const out_name);

typedef struct cy_substitution_t
{
    cy_str_t str;     ///< The substring that matched the substitution token in the pattern. Not NUL-terminated.
    size_t   ordinal; ///< Zero-based index of the substitution token as occurred in the pattern.
} cy_substitution_t;

/// When a name pattern match occurs, Cy will store the string substitutions that had to be made to achieve the match.
/// The substitutions are listed in the order of their occurrence in the pattern.
/// For example, if the pattern is "ins/*/data/>" and the key is "ins/0/data/foo/456",
/// then the substitutions will be (together with their ordinals):
///  1. #0 "0"
///  2. #1 "foo"
///  3. #1 "456"
typedef struct cy_substitution_set_t
{
    size_t                   count;         ///< The size of the following substitutions array.
    const cy_substitution_t* substitutions; ///< A contiguous array of substitutions of size `count`.
} cy_substitution_set_t;

/// Given a subscriber and a topic, returns the set of pattern name substitutions that have to be made to make
/// the subscriber name match the topic name. For verbatim subscribers the substitution set is always empty.
/// See cy_substitution_set_t and cy_arrival_t.
///
/// This is a very fast query intended to be used in high-frequency loops; it DOES NOT manipulate strings
/// but rather returns a pre-computed substitution set. The lifetime of the set is tied to the lifetime of the
/// topic, which is managed automatically by the library; if data needs to survive the next spin, it must be copied.
///
/// This is safe to invoke if any of the pointers are NULL. This guarantee enables the following usage:
///
///     cy_substitution_set_t set = cy_subscriber_substitutions(subscriber, cy_topic_find_by_hash(cy, topic_hash));
///     cy_substitution_set_t set = cy_subscriber_substitutions(subscriber, cy_topic_find_by_name(cy, topic_name));
///
/// On invalid usage returns empty/NULL substitutions; for verbatim subscribers the count is zero but pointer is
/// never NULL.
///
/// Complexity is linear in the number of subscribers on a topic unless this is a verbatim subscriber,
/// in which case the complexity is constant (a single flag check).
cy_substitution_set_t cy_subscriber_substitutions(const cy_future_t* const future, const cy_topic_t* const topic);

/// Send a best-effort response to a message previously received from a topic subscription.
/// The response will be sent directly to the publisher using unicast transport, not affecting other nodes.
/// This can be invoked from a subscription callback or at any later point as long as the breadcrumb is available.
/// There may be an arbitrary number of responses sent per received message; we call these streamed RPC responses.
/// Each response will carry a unique sequence number starting from zero, generated automatically by Cy.
/// For reliable responses use cy_respond_reliable().
cy_err_t cy_respond(cy_breadcrumb_t* const breadcrumb, const cy_us_t deadline, const cy_bytes_t message);

/// Reliable counterpart of cy_respond() that provides the delivery success feedback via a future.
/// This is especially useful for streamed RPC responses where the server (the sender) needs to know whether the
/// client (original message publisher) is still listening or has gone away (in which case streaming should be ceased).
///
/// The client session layer will respond with a positive ACK as long as the application is still receiving the
/// responses (in the specific implementation of Cy it means that the corresponding future is still alive).
/// If the application is no longer listening (in Cy, future is destroyed), the session layer will respond with a NACK,
/// indicating that response could not be delivered to the application, and further responses will not be useful.
///
/// The future materializes (becomes done) either on timeout, or upon (N)ACK arrival. The user can check the outcome
/// using cy_future_error():
/// CY_OK: ACK received, remote application accepted the response.
/// CY_ERR_NACK: Remote replied with NACK; application did not accept the response.
/// CY_ERR_DELIVERY: Remote did not respond before the timeout: network connectivity issue or remote is down.
cy_future_t* cy_respond_reliable(cy_breadcrumb_t* const breadcrumb, const cy_us_t deadline, const cy_bytes_t message);

// =====================================================================================================================
//                                                  NODE & TOPIC
// =====================================================================================================================

/// The new instance will be heap-allocated via the platform layer API.
///
/// The home must be nonempty and should be unique in the network (a random suffix is one way to ensure this).
/// The home and namespace will be normalized and copied; the original references don't need to persist.
/// See cy_name_... for details on name normalization and resolution.
cy_t* cy_new(cy_platform_t* const platform, const cy_str_t home, const cy_str_t name_space);

/// Cy will clean up all resources obtained from the platform, such as memory and readers/writers, but will not
/// destroy the platform instance itself; the application is responsible for that.
///
/// The caller MUST ensure that all user-owned objects referencing this Cy instance are destroyed beforehand
/// (such as publishers, subscribers, futures, etc).
void cy_destroy(cy_t* const cy);

/// See cy_name_... for name resolution details.
/// The returned strings are NUL-terminated. The lifetime is bound to the Cy instance.
cy_str_t cy_home(const cy_t* const cy);
cy_str_t cy_namespace(const cy_t* const cy);

/// This function must be invoked periodically to ensure liveness.
/// The returned value indicates the success of the platform spin().
/// Gossips are published from this function; their failures, if any, are reported via diagnostics listeners.
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

/// Models a fully resolved and normalized topic name. See cy_resolve() et al.
typedef struct cy_resolved_t
{
    cy_str_t name;     ///< Resolved, normalized canonical name (pin-free). On error, ptr is NULL and len=SIZE_MAX.
    uint16_t pin;      ///< Pinned subject-ID, or UINT16_MAX if not pinned.
    bool     verbatim; ///< False if this is a pattern that can match multiple topic names.
} cy_resolved_t;

/// A convenience wrapper for cy_name_resolve(). On failure, the name field has length SIZE_MAX and NULL data pointer.
cy_resolved_t cy_resolve(const cy_t* const cy, const cy_str_t name, const size_t dest_size, char* const dest);

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

// TODO: provide API for querying the associations of reliable topics (discovered subscribers).

/// Provides access to the application-specific context associated per topic.
/// By default it is set to CY_USER_CONTEXT_EMPTY when the topic is created.
/// It can be used to associate arbitrary application-specific data with the topic.
/// Returns NULL iff the topic pointer is NULL.
cy_user_context_t* cy_topic_user_context(cy_topic_t* const topic);

// =====================================================================================================================
//                                                      NAMES
// =====================================================================================================================

/// Maximum length of a resolved normalized name that appears on the wire.
/// Names prior to resolution and normalization may be longer (e.g., due to pinning, redundant `/` separators, etc).
/// In CAN FD networks, normalized topic names should not exceed 48 characters to avoid multi-frame gossips.
/// This limit is chosen rather arbitrarily, keeping in mind RTPS where the maximum is 255,
/// and ROS2 where the maximum is 248. In practice, topics very rarely exceed ~100 characters.
#define CY_TOPIC_NAME_MAX 200

/// A valid name consists of printable ASCII characters except SPACE; i.e., all ASCII codes in [33, 126] are accepted.
/// A normalized name does not begin with a separator, does not end with a separator, and does not contain
/// consecutive separators.
/// Certain combinations of characters have special meaning and may affect final name resolution.
extern const char cy_name_sep;        ///< `/`
extern const char cy_name_home;       ///< `~` -- replaced with the home of the current node. Homes should be unique.
extern const char cy_name_one;        ///< `*` -- matches any single name component: "abc/*/def" => "abc/123/def".
extern const char cy_name_any;        ///< `>` -- matches 0+ components: "abc/>" => "abc", "abc/def", "abc/def/ghi".
extern const char cy_name_pin_prefix; ///< `#` -- followed by decimal digits specifying the subject-ID.

/// Joins two (potentially empty) names with cy_name_sep, normalizing both parts, such that the result is
/// a normalized name. Either part may be empty, in which case it behaves like normalization of the other part.
/// The output string length may exceed CY_TOPIC_NAME_MAX if allowed by dest_size (allows for the pinning suffix).
/// On failure, the output string has length SIZE_MAX and NULL data pointer.
/// The destination is not NUL-terminated.
/// Exact in-place use is supported: dest may equal left.str or right.str. Other overlap modes not supported.
cy_str_t cy_name_join(const cy_str_t left, const cy_str_t right, const size_t dest_size, char* const dest);

/// Constructs the full normalized name as exchanged over the wire prior to remapping: homeful names are expanded,
/// relative names are prefixed with the namespace, and absolute names are left as-is.
/// The pin expression, if present, is removed from the name. Only verbatim names may have pin expressions.
/// The namespace may be homeful and will be expanded accordingly.
///
/// Examples:
///
///     NAME        NAMESPACE   HOME    RESOLVED        PINNING     VERBATIM
///     foo/bar     ns1         me      ns1/foo/bar     -           yes
///     ~//foo/bar  ns1         me      me/foo/bar      -           yes
///     /foo//bar/  ns1         me      foo/bar         -           yes
///     foo/bar/    ~//ns1      me      me/ns1/foo/bar  -           yes
///     foo#123     ns1#456     me      ns1#456/foo     123         yes
///     foo/#123    ns1#456     me      ns1#456/foo     123         yes
///     */foo       ns1         me      ns1/*/foo       -           no
///     ~/*/foo/    ns1         me      me/*/foo        -           no
///     /~/*/foo/   ns1         me      ~/*/foo         -           no
///
/// Examples of invalid names leading to resolution failure:
///
///     `foo bar\nbaz`  -- spaces and non-printable characters are not allowed.
///     `foo/*/bar#123` -- patterns cannot be pinned.
///     ``              -- empty name is not allowed.
///     `#1234`         -- name is empty after the pin expression is stripped, not allowed.
///     (long string)   -- final name cannot exceed CY_TOPIC_NAME_MAX regardless of dest_size.
///
/// The dest points to a buffer at least dest_size bytes long. On failure, the output string has length SIZE_MAX
/// and NULL data pointer. The destination is not NUL-terminated.
/// Destination must not overlap with any of the input strings.
///
/// TODO: add remapping set.
cy_resolved_t cy_name_resolve(const cy_str_t name,
                              const cy_str_t name_space,
                              const cy_str_t home,
                              const size_t   dest_size,
                              char* const    dest);

// =====================================================================================================================
//                                                  MONITORING & DIAGNOSTICS
// =====================================================================================================================

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

/// The application can install an arbitrary number of such diagnostic listeners.
/// Any of the vtable function pointers can be NULL.
/// If multiple listeners are installed, they will be invoked in an unspecified order.
/// Adding/removing listeners from within a callback is not supported.
/// The application must not modify any fields in cy_diag_t except the user context.
typedef struct cy_diag_t        cy_diag_t;
typedef struct cy_diag_vtable_t cy_diag_vtable_t;
struct cy_diag_t
{
    cy_diag_t*              next;
    cy_user_context_t       user_context; ///< Arbitrary state shared with the diagnostics callbacks.
    const cy_diag_vtable_t* vtable;
};

struct cy_diag_vtable_t
{
    /// Async errors are used to report errors occurring in Cy asynchronously with API invocations,
    /// and in a few minor cases may also be invoked synchronously with some API calls.
    /// In particular, they are used for topic resubscription errors occurring in response to consensus updates,
    /// and also in cases where Cy is unable to create an implicit subscription on pattern match due to lack of memory.
    ///
    /// Normally, the listener does not need to do anything specific aside from perhaps logging the error or updating
    /// relevant performance counters. Cy will keep attempting to repeat the failing operation continuously until it
    /// succeeds or the condition requiring the operation is lifted, unless the operation is not mandatory for
    /// correctness.
    ///
    /// Since Cy is a single-file library, the line number uniquely identifies the error site.
    /// The topic pointer may be NULL depending on the nature of the error.
    void (*async_error)(cy_diag_t*, cy_topic_t*, cy_err_t, uint16_t line_number);

    /// Creation is reported immediately after creation, and destruction is reported immediately before destruction.
    void (*topic_created)(cy_diag_t*, cy_topic_t*);
    void (*topic_destroyed)(cy_diag_t*, cy_topic_t*);

    /// Reallocation is reported immediately after the new allocation state is committed.
    /// This includes the initial allocation performed during topic creation.
    void (*topic_reallocated)(cy_diag_t*, cy_topic_t*, uint32_t subject_id, uint32_t evictions);

    /// Inline gossips may not be reported here. The name lifetime ends upon return from the handler.
    /// The function is invoked immediately after the gossip message is processed.
    /// The topic object is NULL if the gossip is not associated with any locally known topic.
    void (*gossip_processed)(cy_diag_t*, cy_topic_t*, cy_str_t name, uint64_t hash);
};

/// Addition/removal are O(n), but n is expected to be very small.
/// The user context is not altered. Once installed, the instance must not be moved.
/// Duplicate addition and nonexistent removal are no-ops.
void cy_diag_add(cy_t* const cy, cy_diag_t* const diag);
void cy_diag_remove(cy_t* const cy, cy_diag_t* const diag);

#ifdef __cplusplus
}
#endif
