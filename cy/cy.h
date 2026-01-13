///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#pragma once

#include <wkv.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

#if defined(__STDC_VERSION__) && (__STDC_VERSION__ < 201112L)
#define CY_ALIGN
#elif defined(__STDC_VERSION__) && (__STDC_VERSION__ < 202311L)
#define CY_ALIGN _Alignas(max_align_t)
#else
#define CY_ALIGN alignas(max_align_t)
#endif

/// The limit could be set arbitrarily, but chosen this way for compatibility with Cyphal v1.0,
/// which only has 13-bit subject-IDs. Cyphal v1.1 will never allocate non-pinned topics in this subject-ID range.
/// For pinned topics, hash<=CY_PINNED_SUBJECT_ID_MAX. The probability of a random hash falling into the pinned
/// range is ~4.44e-16, or about one in two quadrillion, which is not practically possible.
#define CY_PINNED_SUBJECT_ID_MAX 0x1FFFU

#define CY_OK 0
// error code 1 is omitted intentionally
#define CY_ERR_ARGUMENT 2
#define CY_ERR_MEMORY   3
#define CY_ERR_CAPACITY 4
#define CY_ERR_NAME     5
#define CY_ERR_MEDIA    6

typedef uint_fast8_t cy_err_t;
typedef int64_t      cy_us_t; ///< Monotonic microsecond timestamp. Signed to permit arithmetics in the past.

typedef struct cy_t       cy_t;
typedef struct cy_topic_t cy_topic_t;

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
/// The size can be increased as long as it doesn't break the compile-time size checks/limits in the platform layer.
#define CY_USER_CONTEXT_PTR_COUNT 2

/// An opaque user context enabling the application to share data with callbacks. It is intended to be passed by value.
typedef union cy_user_context_t
{
    CY_ALIGN void*         ptr[CY_USER_CONTEXT_PTR_COUNT];
    CY_ALIGN unsigned char bytes[sizeof(void*) * CY_USER_CONTEXT_PTR_COUNT];
} cy_user_context_t;

#ifdef __cplusplus
#define CY_USER_CONTEXT_EMPTY \
    cy_user_context_t {}
#else
#define CY_USER_CONTEXT_EMPTY ((cy_user_context_t){ .ptr = { NULL } })
#endif

// =====================================================================================================================
//                                                  MESSAGE BUFFER
// =====================================================================================================================

/// A type-erased movable received transfer buffer handle with a platform-specific implementation.
/// It allows the platform layer to eliminate data copying until/unless explicitly requested by the application.
/// Some transport libraries (e.g., libudpard) store the data in a set of segments obtained directly from the NIC.
/// Use cy_message_read to access the data.
/// Avoid copying instances, consider using cy_message_move() instead.
/// Do not access any of the fields directly; use the provided functions instead.
typedef struct cy_message_t
{
    void*                             state[2]; ///< Opaque implementation-specific soft state.
    size_t                            size;     ///< Must contain the total size of the scattered buffer data in bytes.
    const struct cy_message_vtable_t* vtable;
} cy_message_t;

/// Returns the total size of the scattered buffer in bytes. The size of a moved-from instance is zero.
static inline size_t cy_message_size(const cy_message_t msg) { return msg.size; }

/// A convenience helper that returns a copy of the message object and invalidates the original.
/// Use this to transfer the ownership of the message to another message object.
cy_message_t cy_message_move(cy_message_t* const msg);

/// This is the only way to access the received message data.
/// It gathers `size` bytes of data located at `offset` bytes from the beginning of the transfer data
/// into the provided contiguous buffer. The function returns the number of bytes copied.
/// If the requested range exceeds the available message size, only the available bytes are copied.
/// The implementation may be optimized for highly efficient sequential access by caching soft states in the cursor
/// instance. This is particularly useful for message deserialization by reading the fields out one by one.
size_t cy_message_read(cy_message_t* const cursor, const size_t offset, const size_t size, void* const destination);

/// Must be invoked at least once on a message object obtained from a received transfer.
/// No effect if the instance is already moved-from or if the pointer is NULL.
/// Subsequent calls have no effect; the passed instance will be moved-from.
void cy_message_destroy(cy_message_t* const msg);

/// A message with an associated non-negative arrival timestamp.
/// The timestamp is carried over from the low-level NIC driver, which defines the accuracy, which is typically high
/// -- hardware timestamping in the driver can achieve microsecond accuracy.
/// The timestamp of a multi-frame transfer equals the arrival time of the first frame of that transfer.
typedef struct cy_message_ts_t
{
    cy_us_t      timestamp;
    cy_message_t content;
} cy_message_ts_t;

// =====================================================================================================================
//                                                      PUBLISHER
// =====================================================================================================================

typedef struct cy_publisher_t cy_publisher_t;

/// Create a new publisher on the topic. The default priority value is cy_prio_nominal, it can be changed later.
/// The response_extent is the extent (maximum size) of the response data if the publisher expects responses.
cy_publisher_t* cy_advertise(cy_t* const cy, const wkv_str_t name);
cy_publisher_t* cy_advertise_client(cy_t* const cy, const wkv_str_t name, const size_t response_extent);

/// Create a new publisher that ensures that there is at most one, the most recent, message pending for transmission.
/// If a new message is published while another one is still pending, the previous one is cancelled.
/// TODO not implemented; this is a simple idea -- store the last transfer-ID in the topic and cancel it on new publish.
cy_publisher_t* cy_advertise_sample(cy_t* const cy, const wkv_str_t name);

/// Notifies the application about the outcome of a reliable delivery attempt.
/// It is ALWAYS invoked EXACTLY ONCE per published message or a sent response if reliable delivery was requested.
/// For published messages, the value indicates the number of remote subscribers that acknowledged the message.
/// For responses, the value is either zero (failure) or one (success).
typedef void (*cy_delivery_callback_t)(cy_user_context_t, uint16_t acknowledgements);

/// Optionally, the user callback can take ownership of the message using cy_message_move().
/// If the message is not moved out, it will be destroyed automatically after return from the callback.
/// If no response was received before the deadline, the message pointer will be NULL.
typedef void (*cy_response_callback_t)(cy_user_context_t, cy_message_ts_t*);

/// Publish a best-effort (non-reliable) one-way message without expecting a response.
cy_err_t cy_publish(cy_publisher_t* const pub, const cy_us_t tx_deadline, const cy_bytes_t message);

/// Publish a reliable one-way message without expecting a response.
/// The delivery callback, unless NULL, is GUARANTEED to be invoked EXACTLY ONCE per published message
/// to report the outcome (success/failure), unless this function returns anything other than CY_OK.
cy_err_t cy_publish_reliable(cy_publisher_t* const        pub,
                             const cy_us_t                tx_deadline,
                             const cy_bytes_t             message,
                             const cy_user_context_t      ctx_delivery,
                             const cy_delivery_callback_t cb_delivery);

/// If the delivery callback is provided, reliable delivery will be used, attempting to deliver the message
/// until the specified deadline is reached. The outcome will be reported via the delivery callback,
/// which is GUARANTEED to be invoked EXACTLY ONCE per published message unless the function did not return CY_OK.
/// If the delivery callback is NULL, best-effort delivery will be used.
///
/// The response callback is mandatory (otherwise use the simple publish functions instead of this one).
/// A P2P response transfer will be awaited from any remote node that received the published message.
/// The response or lack thereof will be reported via the response callback.
/// The response callback is GUARANTEED to be invoked EXACTLY ONCE per published message unless the function
/// did not return CY_OK. If no response is received before the deadline, the response callback will be invoked
/// with a negative timestamp and empty data.
///
/// The reliability of the response transfer is up to the remote node.
///
/// If reliable delivery fails, the response callback will still be invoked. The guaranteed callback invocation
/// regardless of the outcome is taken very seriously because it simplifies resource management for the application.
cy_err_t cy_request(cy_publisher_t* const        pub,
                    const cy_us_t                tx_deadline,
                    const cy_us_t                response_deadline,
                    const cy_bytes_t             message,
                    const cy_user_context_t      ctx_delivery,
                    const cy_delivery_callback_t cb_delivery,
                    const cy_user_context_t      ctx_response,
                    const cy_response_callback_t cb_response);

cy_prio_t cy_priority(const cy_publisher_t* const pub);
void      cy_priority_set(cy_publisher_t* const pub, const cy_prio_t priority);

/// Each publisher is always linked to a specific single topic.
/// This pointer remains valid for the entire lifetime of the publisher.
/// It can be used to obtain the topic name, hash, etc. of this publisher.
cy_topic_t* cy_publisher_topic(const cy_publisher_t* const pub);

/// Pending delivery callbacks, if any, will not be invoked after unadvertisement.
void cy_unadvertise(cy_publisher_t* const pub);

// =====================================================================================================================
//                                                      SUBSCRIBER
// =====================================================================================================================

typedef struct cy_subscriber_t cy_subscriber_t;

/// This ought to be enough for any reasonable transport-specific state.
#define CY_RESPONDER_STATE_BYTES 64U

/// Received transfers are given this copyable instance to allow sending P2P response transfers if necessary.
/// It is only valid for a single response. It can be copied / passed by value.
/// It can be trivially discarded if no response is needed.
///
/// This object avoids linking the topic instance that delivered the original message to avoid lifetime
/// issues that would occur if the topic is destroyed between the message arrival and the response time.
/// Instead of referencing the topic, the relevant parameters of the topic are stored here by value.
typedef struct cy_responder_t
{
    cy_t*                               cy; ///< Must be valid; the platform layer is responsible for ensuring this.
    const struct cy_responder_vtable_t* vtable;
    CY_ALIGN unsigned char              state[CY_RESPONDER_STATE_BYTES];
} cy_responder_t;

typedef struct cy_substitution_t
{
    wkv_str_t str;     ///< The substring that matched the substitution token in the pattern. Not NUL-terminated.
    size_t    ordinal; ///< Zero-based index of the substitution token as occurred in the pattern.
} cy_substitution_t;

/// When a name pattern match occurs, Cy will store the string substitutions that had to be made to
/// achieve the match. The substitutions are listed in the order of their occurrence in the pattern.
/// For example, if the pattern is "ins/?/data/*" and the key is "ins/0/data/foo/456",
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
///
/// Note that we do not report the transfer-ID here because this value is considered too low-level to be useful.
/// In the future we may consider adding an API for signaling lost messages to the application, which may be based
/// on the transfer-ID discontinuities, but it will likely be a separate callback.
typedef struct cy_arrival_t
{
    /// Optionally, the user callback can take ownership of the message using cy_message_move();
    /// however, to avoid use-after-free, the following rules must be followed:
    /// 1. At most one callback can move the message out of the arrival instance.
    /// 2. If the message is moved out, it shall not be destroyed (see cy_message_destroy()) until after the last
    ///    callback returns, unless it is the last callback to process it.
    /// If the message is not moved out, it will be destroyed automatically after return from the callback.
    /// If these restrictions become too limiting, we may introduce simple reference counting for messages.
    cy_message_ts_t message;

    /// Use cy_respond() to send a P2P response directly to the publisher of this message if needed.
    cy_responder_t responder;

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
typedef void (*cy_subscriber_callback_t)(cy_user_context_t, cy_arrival_t*);

/// We intentionally use the exact same API for both verbatim and pattern subscriptions; this is a key design feature.
///
/// It is allowed to remove the subscription from its own callback, but not from the callback of another subscription.
///
/// There may be more than one subscriber with the same name (pattern). The library will only keep one
/// reference-counted topic; upon message arrival, all matching subscribers will be invoked in an unspecified order.
/// If there is more than one subscriber utilizing different parameters (extent, ordering, etc.) on the same topic,
/// the library will disambiguate the parameters using simple heuristics.
cy_subscriber_t* cy_subscribe(cy_t* const                    cy,
                              const wkv_str_t                name,
                              const size_t                   extent,
                              const cy_user_context_t        context,
                              const cy_subscriber_callback_t callback);

/// The reordering window must be non-negative.
cy_subscriber_t* cy_subscribe_ordered(cy_t* const                    cy,
                                      const wkv_str_t                name,
                                      const size_t                   extent,
                                      const cy_us_t                  reordering_window,
                                      const cy_user_context_t        context,
                                      const cy_subscriber_callback_t callback);

/// Send a response to a message previously received from a topic subscription.
/// The response will be sent directly to the publisher using peer-to-peer transport, not affecting other nodes.
/// This can be invoked from a subscription callback or at any later point as long as the responder object is available,
/// but there may be at most one such invocation per responder instance.
///
/// The feedback may be NULL if no delivery status notification is needed; the absence of the callback does not imply
/// that the transfer will not be sent in the reliable mode.
/// If a feedback callback is provided, it will be invoked EXACTLY ONCE to report the outcome of the delivery attempt,
/// unless this function returns anything other than CY_OK. In particular, it will be invoked also when the topic is
/// destroyed with pending responses.
cy_err_t cy_respond(const cy_responder_t         responder,
                    const cy_us_t                tx_deadline,
                    const cy_bytes_t             response_message,
                    const cy_user_context_t      ctx_delivery,
                    const cy_delivery_callback_t cb_delivery);

/// Copies the subscriber name into the user-supplied buffer. Max size is CY_TOPIC_NAME_MAX plus NUL-terminator.
/// The output string is NUL-terminated.
void cy_subscriber_name(const cy_subscriber_t* const sub, char* const out_name);

/// No effect if the subscriber pointer is NULL.
void cy_unsubscribe(cy_subscriber_t* const sub);

// =====================================================================================================================
//                                                  NODE & TOPIC
// =====================================================================================================================

/// Returns the current time in microseconds. Always non-negative.
cy_us_t cy_now(const cy_t* const cy);

// TODO: cy_err_t cy_remap(cy_t*, wkv_str_t from, wkv_str_t to);

// TODO: add a way to dump/restore topic configuration for instant initialization. This may be platform-specific.

/// Complexity is logarithmic in the number of topics. NULL if not found.
/// In practical terms, these queries are very fast and efficient.
cy_topic_t* cy_topic_find_by_hash(const cy_t* const cy, const uint64_t hash);
cy_topic_t* cy_topic_find_by_name(const cy_t* const cy, const wkv_str_t name);

/// Iterate over all topics in an unspecified order except that pinned topic are listed first.
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
wkv_str_t cy_topic_name(const cy_topic_t* const topic);
uint64_t  cy_topic_hash(const cy_topic_t* const topic);

/// Provides access to the application-specific context associated per topic.
/// By default it is set to CY_USER_CONTEXT_EMPTY when the topic is created.
/// It can be used to associate arbitrary application-specific data with the topic.
/// Returns NULL iff the topic pointer is NULL.
cy_user_context_t* cy_topic_user_context(cy_topic_t* const topic);

// TODO: topic hooks: extern functions similar to cy_trace invoked when a topic is created/destroyed/(un)subscribed/etc.

// =====================================================================================================================
//                                                      NAMES
// =====================================================================================================================

/// Shorter topic names reduce the gossip traffic overhead.
/// In CAN FD networks, topic names should not exceed 39 characters to avoid multi-frame heartbeats.
/// This limit is chosen rather arbitrarily, keeping in mind RTPS where the maximum is 255,
/// and ROS2 where the maximum is 248. In practice, topics very rarely exceed ~100 characters.
#define CY_TOPIC_NAME_MAX 200

/// The max namespace length should also provide space for at least one separator and a one-character topic name.
#define CY_NAMESPACE_NAME_MAX (CY_TOPIC_NAME_MAX - 2)

/// A valid name consists of printable ASCII characters except SPACE.
/// A normalized name does not begin with a separator, does not end with a separator, and does not contain
/// consecutive separators.
extern const char cy_name_sep;  ///< '/'
extern const char cy_name_home; ///< '~'

/// True iff the given name is valid according to the Cy naming rules. An empty name is not a valid name.
bool cy_name_is_valid(const wkv_str_t name);

/// Returns true iff the name can only match a single topic, which is called a verbatim name;
/// conversely, returns false for patterns that can match more than one topic.
/// This is useful for some applications that want to ensure that certain names can match only one topic.
bool cy_name_is_verbatim(const wkv_str_t name);

/// Whether the name is relative to the home namespace ~ or is absolute.
bool cy_name_is_homeful(const wkv_str_t name);
bool cy_name_is_absolute(const wkv_str_t name);

/// Joins two (potentially empty) names with cy_name_sep, normalizing both parts, such that the result is
/// a normalized name. Either part may be empty, in which case it behaves like normalization of the other part.
/// On failure, the output string has length SIZE_MAX and NULL data pointer.
/// The destination is not NUL-terminated.
wkv_str_t cy_name_join(const wkv_str_t left, const wkv_str_t right, const size_t dest_size, char* const dest);

/// If cy_name_is_homeful(name), expands the home prefix using the provided home string;
/// otherwise, returns the normalized name.
/// The result is normalized and written into dest, which must be at least dest_size bytes long.
/// On failure, the output string has length SIZE_MAX and NULL data pointer.
/// The destination is not NUL-terminated.
wkv_str_t cy_name_expand_home(wkv_str_t name, const wkv_str_t home, const size_t dest_size, char* const dest);

/// Constructs the full normalized name as exchanged over the wire: homeful names are expanded,
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
wkv_str_t cy_name_resolve(const wkv_str_t name,
                          wkv_str_t       namespace_,
                          const wkv_str_t home,
                          size_t          dest_size,
                          char*           dest);

#ifdef __cplusplus
}
#endif
