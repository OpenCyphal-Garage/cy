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

#include <wkv.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

// =====================================================================================================================
//                                              PRIMITIVES & CONSTANTS
// =====================================================================================================================

/// A sensible middle ground between worst-case gossip traffic and memory utilization vs. longest name support.
/// In CAN FD networks, topic names should be short to avoid multi-frame heartbeats.
///
/// Max name length is chosen such that together with the 1-byte length prefix the result is a multiple of 8 bytes,
/// because it helps with memory-aliased C structures for quick serialization.
#define CY_TOPIC_NAME_MAX 88

/// The max namespace length should also provide space for at least one separator and the one-character topic name.
#define CY_NAMESPACE_NAME_MAX (CY_TOPIC_NAME_MAX - 2)

/// The range of unregulated identifiers to use for CRDT topic allocation.
/// Pinned topics (such as the ordinary topics with manually assigned IDs) can be pinned anywhere in [0, 8184].
/// Subject-IDs in [8187, 65535] are managed by the named topic allocation protocol.
/// Subject-IDs 8185 and 8186 are reserved.
#define CY_TOPIC_SUBJECT_COUNT 6144
#define CY_SUBJECT_BITS        13U
#define CY_TOTAL_SUBJECT_COUNT (1UL << CY_SUBJECT_BITS)

#define CY_PASTE_(a, b) a##b
#define CY_PASTE(a, b)  CY_PASTE_(a, b)

/// I am not sure if this should be part of the library because this is a rather complicated macro.
/// It simply eliminates the boilerplate code for gathering a borrowed buffer into a contiguous storage on the stack.
/// If the source buffer is only a single fragment, then no copying is done as the resulting cy_bytes_t is simply
/// set to point to the only fragment.
///
/// Ideally, this should not be necessary at all, as all efficient APIs need to support scattered buffers;
/// but the reality is that many APIs still expect contiguous buffers, which requires an extra copy.
#define CY_BUFFER_GATHER_ON_STACK(to_bytes, from_buffer_borrowed_head)                                             \
    cy_bytes_t    to_bytes = { .data = from_buffer_borrowed_head.view.data,                                        \
                               .size = from_buffer_borrowed_head.view.size };                                      \
    unsigned char CY_PASTE(to_bytes, _storage)[cy_buffer_borrowed_size(from_buffer_borrowed_head)];                \
    if (from_buffer_borrowed_head.next != NULL) {                                                                  \
        to_bytes.size = cy_buffer_borrowed_gather(                                                                 \
          from_buffer_borrowed_head,                                                                               \
          (cy_bytes_mut_t){ .data = CY_PASTE(to_bytes, _storage), .size = sizeof(CY_PASTE(to_bytes, _storage)) }); \
        to_bytes.data = CY_PASTE(to_bytes, _storage);                                                              \
    }

#define CY_OK 0
// error code 1 is omitted intentionally
#define CY_ERR_ARGUMENT 2
#define CY_ERR_MEMORY   3
#define CY_ERR_CAPACITY 4
#define CY_ERR_NAME     5
#define CY_ERR_MEDIA    6

typedef uint_fast8_t cy_err_t;
typedef int64_t      cy_us_t; ///< Monotonic microsecond timestamp. Signed to permit arithmetics in the past.

#ifndef __cplusplus
typedef struct cy_t                     cy_t;
typedef struct cy_topic_t               cy_topic_t;
typedef struct cy_bytes_t               cy_bytes_t;
typedef struct cy_bytes_mut_t           cy_bytes_mut_t;
typedef struct cy_buffer_borrowed_t     cy_buffer_borrowed_t;
typedef struct cy_buffer_owned_t        cy_buffer_owned_t;
typedef struct cy_tree_t                cy_tree_t;
typedef union cy_response_context_t     cy_response_context_t;
typedef struct cy_transfer_metadata_t   cy_transfer_metadata_t;
typedef struct cy_transfer_owned_t      cy_transfer_owned_t;
typedef struct cy_publisher_t           cy_publisher_t;
typedef struct cy_future_t              cy_future_t;
typedef struct cy_substitution_t        cy_substitution_t;
typedef struct cy_arrival_t             cy_arrival_t;
typedef struct cy_subscription_params_t cy_subscription_params_t;
typedef struct cy_subscriber_t          cy_subscriber_t;
#endif

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
/// Normally, the view and origin are identical, but this is not always the case depending on the transport library.
/// The view is usually inside the origin, but even that is not guaranteed; e.g., if memory mapping is used.
///
/// The head of the payload chain is always passed by value and thus does not require freeing; the following chain
/// elements are also allocated from some memory resource and thus shall be freed with the payload.
///
/// Warning: It is required that the first 24 bytes of the payload are NOT fragmented. Otherwise, Cy may refuse to
/// accept the transfer. This requirement is trivial to meet because the MTU of all transports that supply fragmented
/// payloads is much larger than this.
///
/// The size of a payload fragment may be zero.
struct cy_buffer_borrowed_t
{
    const cy_buffer_borrowed_t* next; ///< NULL in the last entry.
    cy_bytes_t                  view;
};
struct cy_buffer_owned_t
{
    cy_buffer_borrowed_t base;
    cy_bytes_mut_t       origin; ///< Do not access! Address may not be mapped. Only for freeing the payload.
};

struct cy_tree_t
{
    cy_tree_t*  up;
    cy_tree_t*  lr[2];
    int_fast8_t bf;
};

#define CY_RESPONSE_CONTEXT_SIZE_BYTES 24U

/// Received messages are given an instance of the response context to allow the application to respond to them,
/// if necessary. The context is only valid for a single response. The context can be copied and passed by value.
/// The platform layer uses the context to store arbitrary transport-specific information needed to send the
/// response back to the publisher. For example, it may contain the source addresses and port numbers,
/// or pointers into private structures.
union cy_response_context_t
{
    uint64_t u64[CY_RESPONSE_CONTEXT_SIZE_BYTES / 8U]; // Enough for x3 IPv4 address+port pairs.
    uint32_t u32[CY_RESPONSE_CONTEXT_SIZE_BYTES / 4U];
    uint16_t u16[CY_RESPONSE_CONTEXT_SIZE_BYTES / 2U];
    void*    ptr[CY_RESPONSE_CONTEXT_SIZE_BYTES / sizeof(void*)];
};

struct cy_transfer_metadata_t
{
    cy_prio_t             priority;
    uint64_t              transfer_id;
    cy_response_context_t context;
};

/// A transfer object owns its payload.
/// The application may claim ownership of the payload by invalidating the payload pointers in the object;
/// otherwise, Cy will clean it up afterward.
struct cy_transfer_owned_t
{
    cy_us_t                timestamp;
    cy_transfer_metadata_t metadata;
    cy_buffer_owned_t      payload;
};

// =====================================================================================================================
//                                                      PUBLISHER
// =====================================================================================================================

struct cy_publisher_t
{
    cy_topic_t* topic;    ///< Many-to-one relationship, never NULL; the topic is reference counted.
    cy_prio_t   priority; ///< Defaults to cy_prio_nominal; can be overridden by the user at any time.
    // TODO: add `bool fec`
    void* user;
};

/// Future lifecycle:
///     fresh --> pending --+--> success
///                         +--> timeout_ack
///                         +--> timeout_response
typedef enum cy_future_state_t
{
    cy_future_fresh,
    cy_future_pending,
    cy_future_success,
    cy_future_timeout_ack,      ///< Remote end did not confirm reception of the message.
    cy_future_timeout_response, ///< Response was not received before the deadline.
} cy_future_state_t;

typedef void (*cy_future_callback_t)(cy_t*, cy_future_t*);

/// Register an expectation for a response to a message sent to the topic.
/// The future shall not be moved or altered in any way except for the user and callback fields until its state is
/// no longer pending. Once it is not pending, it can be reused for another request.
/// The future will enter the failure state to indicate that the response was not received before the deadline.
struct cy_future_t
{
    cy_tree_t index_deadline;
    cy_tree_t index_transfer_id;

    cy_publisher_t*   publisher;
    cy_future_state_t state;
    uint64_t          transfer_id; ///< Remember that transports with narrow transfer-ID should recover the full ID.
    cy_us_t           deadline;    ///< We're indexing on this so it shall not be changed after insertion.

    /// These fields are populated once the response is received.
    /// The payload ownership is transferred to this structure.
    /// If a payload is already available when a response is received, Cy will free the old payload first.
    /// The user can detect when a new response is received by checking its timestamp.
    cy_transfer_owned_t last_response;

    /// Only these fields can be altered by the user while the future is pending.
    /// The callback may be NULL if the application prefers to check last_response by polling.
    cy_future_callback_t callback;
    void*                user;
};

/// Create a new publisher on the topic.
/// Every advertisement needs to be unadvertised later to clean up resources.
///
/// The response_extent is the extent (maximum size) of the response payload if the publisher expects responses;
/// if no response is expected/needed, the response_extent should be zero. If responses are needed but their maximum
/// size is unknown, pick any sensible large value.
cy_err_t cy_advertise(cy_t* const cy, cy_publisher_t* const pub, const wkv_str_t name, const size_t response_extent);
static inline cy_err_t cy_advertise_c(cy_t* const           cy,
                                      cy_publisher_t* const pub,
                                      const char* const     name,
                                      const size_t          response_extent)
{
    return cy_advertise(cy, pub, wkv_key(name), response_extent);
}
void cy_unadvertise(cy_t* const cy, cy_publisher_t* pub);

/// Just a convenience function, nothing special.
/// The initial future state is cy_future_fresh.
void cy_future_new(cy_future_t* const future, const cy_future_callback_t callback, void* const user);

/// This needs not be done after a future completes normally. It is only needed if the future needs to be
/// destroyed before it completes. Calling this on a non-pending future has no effect.
void cy_future_cancel(cy_future_t* const future);

/// The transfer-ID is always incremented, even on failure, to signal lost messages.
///
/// If no response is needed/expected, the future must be NULL and the response_deadline is ignored.
/// Otherwise, future must point to an uninitialized cy_future_t instance.
///
/// The response future will not be registered unless the result is non-negative.
///
/// If the response deadline is in the past, the message will be sent anyway but it will time out immediately.
cy_err_t cy_publish(cy_t* const                cy,
                    cy_publisher_t* const      pub,
                    const cy_us_t              tx_deadline,
                    const cy_buffer_borrowed_t payload,
                    const cy_us_t              response_deadline,
                    cy_future_t* const         future);

/// A simpler wrapper over cy_publish() when no response is needed/expected. 1 means one way.
static inline cy_err_t cy_publish1(cy_t* const                cy,
                                   cy_publisher_t* const      pub,
                                   const cy_us_t              tx_deadline,
                                   const cy_buffer_borrowed_t payload)
{
    return cy_publish(cy, pub, tx_deadline, payload, 0, NULL);
}

// =====================================================================================================================
//                                                      SUBSCRIBER
// =====================================================================================================================

struct cy_substitution_t
{
    wkv_str_t str;     ///< The substring that matched the substitution token in the pattern. Not NUL-terminated.
    size_t    ordinal; ///< Zero-based index of the substitution token as occurred in the pattern.
};

/// Optionally, the user handler can take ownership of the transfer payload by zeroing the origin pointer
/// by setting transfer->payload.origin.data = NULL. However, this may cause undesirable interference with other
/// subscribers that also match the same topic and are to receive the data after the current callback returns.
struct cy_arrival_t
{
    cy_subscriber_t*     subscriber; ///< Which subscriber matched on this topic by verbatim name or pattern.
    cy_topic_t*          topic;      ///< The specific topic that received the transfer.
    cy_transfer_owned_t* transfer;   ///< The actual received message and its metadata.

    /// When a pattern match occurs, the matcher will store the string substitutions that had to be made to
    /// achieve the match. For example, if the pattern is "ins/?/data/*" and the key is "ins/0/data/foo/456",
    /// then the substitutions will be (together with their ordinals):
    ///  1. #0 "0"
    ///  2. #1 "foo"
    ///  3. #1 "456"
    /// The lifetime of the substitutions is at least as long as that of the subscriber.
    size_t                   substitution_count; ///< The size of the following substitutions array.
    const cy_substitution_t* substitutions;      ///< A contiguous array of substitutions.
};

typedef void (*cy_subscriber_callback_t)(cy_t*, const cy_arrival_t*);

/// These parameters are used to configure the underlying transport layer implementation.
/// These values shall not be changed by the user; the only way to set them is when a new subscription is created.
/// They need to be stored per subscriber to support pattern subscriptions, where the first subscription may
/// be created asynchronously wrt the user calling cy_subscribe().
struct cy_subscription_params_t
{
    size_t extent;
};

/// Subscribers SHALL NOT be copied/moved after initialization until destroyed.
/// There may be more than one subscriber with the same name (pattern).
/// The user must not alter any fields except for the callback and the user pointer.
struct cy_subscriber_t
{
    struct cy_subscriber_root_t* root;
    cy_subscriber_t*             next;

    cy_subscription_params_t params;

    /// The callback may be changed by the user at any time; e.g., to implement a state machine.
    /// The user field can be changed arbitrarily at any moment.
    cy_subscriber_callback_t callback;
    void*                    user;
};

/// It is allowed to remove the subscription from its own callback, but not from the callback of another subscription.
///
/// The extent of all subscriptions should be the same, or the values of subscriptions added later should be less
/// than those of subscriptions added earlier. Otherwise, the library will be forced to resubscribe,
/// which may cause momentary data loss if there were transfers in the middle of reassembly, plus it is usually slow.
cy_err_t               cy_subscribe(cy_t* const                    cy,
                                    cy_subscriber_t* const         sub,
                                    const wkv_str_t                name,
                                    const size_t                   extent,
                                    const cy_subscriber_callback_t callback);
static inline cy_err_t cy_subscribe_c(cy_t* const                    cy,
                                      cy_subscriber_t* const         sub,
                                      const char* const              name,
                                      const size_t                   extent,
                                      const cy_subscriber_callback_t callback)
{
    return cy_subscribe(cy, sub, wkv_key(name), extent, callback);
}
void cy_unsubscribe(cy_t* const cy, cy_subscriber_t* const sub);

/// Send a response to a message received from a topic subscription. The response will be sent directly to the
/// publisher using peer-to-peer transport, not affecting other nodes on this topic. The payload may be arbitrary
/// and the metadata shall be taken from the original message. The transfer-ID will not be incremented since it's
/// not a publication.
///
/// This can be invoked either from a subscription callback or at any later point. The topic may even get reallocated
/// in the process but it doesn't matter.
///
/// The response is sent using a P2P transfer to the publisher with the specified priority and the original transfer-ID.
cy_err_t cy_respond(cy_t* const                cy,
                    cy_topic_t* const          topic,
                    const cy_us_t              tx_deadline,
                    cy_transfer_metadata_t     metadata,
                    const cy_buffer_borrowed_t payload);

/// Copies the subscriber name into the user-supplied buffer.
void cy_subscriber_name(const cy_t* const cy, const cy_subscriber_t* const sub, char* const out_name);

// =====================================================================================================================
//                                                  NODE & TOPIC
// =====================================================================================================================

/// A convenience wrapper that returns the current time in microseconds.
cy_us_t cy_now(const cy_t* const cy);

/// If the topic configuration is restored from non-volatile memory or elsewhere, it can be supplied to the library
/// via this function immediately after the topic is first created. This function should not be invoked at any other
/// moment except immediately after initialization.
///
/// If the hint is provided, it will be used as the initial allocation state, unless either a conflict or divergence
/// are discovered, which will be treated normally, without any preference to the hint. This option allows the user
/// to optionally save the network configuration in a non-volatile storage, such that the next time the network becomes
/// operational immediately, without waiting for the CRDT consensus. Remember that the hint is discarded on conflict.
///
/// The hint will be silently ignored if it is invalid, inapplicable, or if the topic is not freshly created.
void cy_topic_hint(cy_t* const cy, cy_topic_t* const topic, const uint16_t subject_id);

/// Complexity is logarithmic in the number of topics. NULL if not found.
/// In practical terms, these queries are very fast and efficient.
cy_topic_t*               cy_topic_find_by_name(const cy_t* const cy, const wkv_str_t name);
static inline cy_topic_t* cy_topic_find_by_name_c(const cy_t* const cy, const char* const name)
{
    return cy_topic_find_by_name(cy, wkv_key(name));
}
cy_topic_t* cy_topic_find_by_hash(const cy_t* const cy, const uint64_t hash);

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

/// Optionally, the application can use this to save the allocated subject-ID before shutting down/rebooting
/// for instant recovery. Not needed for pinned topics since their IDs cannot change.
uint16_t cy_topic_subject_id(const cy_topic_t* const topic);

/// The name is NUL-terminated; pointer lifetime bound to the topic.
wkv_str_t cy_topic_name(const cy_topic_t* const topic);

/// Returns true iff the name can match more than one topic.
/// This is useful for some applications that want to ensure that certain names can match only one topic.
bool               cy_has_substitution_tokens(const wkv_str_t name);
static inline bool cy_has_substitution_tokens_c(const char* const name)
{
    return cy_has_substitution_tokens(wkv_key(name));
}

// =====================================================================================================================
//                                                      BUFFERS
// =====================================================================================================================

/// This should be invoked once the application is done processing a payload.
/// The struct will be modified by zeroing pointers and sizes in it.
/// When Cy assigns a new payload to a subscription/response/etc object, it will check first if the previous payload
/// is released; if not, it will do it automatically. The nullification of the pointers is thus required to make it
/// explicit that the payload is no longer valid and to prevent double-free errors.
/// Invoking this function on an already released payload has no effect and is safe.
void cy_buffer_owned_release(cy_t* const cy, cy_buffer_owned_t* const payload);

/// Returns the total size of all payload fragments in the chain.
/// The complexity is linear, but the number of elements is very small (total size divided by MTU).
size_t               cy_buffer_borrowed_size(const cy_buffer_borrowed_t payload);
static inline size_t cy_buffer_owned_size(const cy_buffer_owned_t payload)
{
    return cy_buffer_borrowed_size(payload.base);
}

/// Takes the head of a fragmented buffer list and copies the data into the contiguous buffer provided by the user.
/// If the total size of all fragments combined exceeds the size of the user-provided buffer,
/// copying will stop early after the buffer is filled, thus truncating the fragmented data short.
/// The function has no effect and returns zero if the destination buffer is NULL.
/// Returns the number of bytes copied into the contiguous destination buffer.
size_t               cy_buffer_borrowed_gather(const cy_buffer_borrowed_t payload, const cy_bytes_mut_t dest);
static inline size_t cy_buffer_owned_gather(const cy_buffer_owned_t payload, const cy_bytes_mut_t dest)
{
    return cy_buffer_borrowed_gather(payload.base, dest);
}

#ifdef __cplusplus
}
#endif
