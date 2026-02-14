///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// Platform-side API of the Cy library.
/// The application is not intended to have access to this header; this is only for the platform layer implementation.
/// Applications should only include cy.h.
///
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#pragma once

#include "cy.h"

/// For compatibility with Cyphal v1.0, the heartbeat topic is pinned at subject-ID 7509.
/// Historical trivia: number 0x1D55==7509==0b1110101010101 was chosen because it has a long alternating bit pattern,
/// which enables a more robust automatic bit rate detection in CAN bus networks.
#define CY_HEARTBEAT_TOPIC_NAME "/#1d55"
#define CY_HEARTBEAT_TOPIC_HASH 0x1D55U

/// See the subject_id_modulus for details.
#define CY_SUBJECT_ID_MODULUS_17bit 122867ULL
#define CY_SUBJECT_ID_MODULUS_23bit 8380403ULL
#define CY_SUBJECT_ID_MODULUS_32bit 4294959083ULL

#ifdef __cplusplus
extern "C"
{
#endif

struct cy_message_t
{
    size_t                            refcount;
    const struct cy_message_vtable_t* vtable;
};
#define CY_MESSAGE_INIT(vtable_ptr) ((cy_message_t){ .refcount = 1, .vtable = (vtable_ptr) })

/// Platform-specific implementation of cy_message_t.
typedef struct cy_message_vtable_t
{
    /// This is used to skip the session-layer header after receiving the message.
    /// All subsequent reads must add this offset to the requested offset.
    /// The effect is incremental if invoked more than once.
    void (*skip)(cy_message_t*, size_t offset);

    /// The implementation must add add the skip offset to the requested offset and adjust the size accordingly.
    /// The implementation must limit the size if the requested range exceeds the available message size.
    /// The return value is the number of bytes copied to the output buffer after adjusting the offset and size for
    /// the skip and bounds.
    size_t (*read)(const cy_message_t*, size_t offset, size_t size, void*);

    /// The size sans the skip offset.
    size_t (*size)(const cy_message_t*);

    /// Invalidates the message instance. Cy invokes this when the refcount drops to zero.
    void (*destroy)(cy_message_t*);
} cy_message_vtable_t;

/// A subject writer is used to send messages on the subject specified at the time of its construction.
/// Cy guarantees that there will be at most one subject writer per subject-ID.
typedef struct cy_subject_writer_t
{
    uint32_t subject_id;
} cy_subject_writer_t;

/// A subject reader is created when the higher layer requires data from the specified subject-ID.
/// The transport layer must report all received messages via cy_on_message().
/// Cy guarantees that there will be at most one subject reader per subject-ID.
typedef struct cy_subject_reader_t
{
    uint32_t subject_id;
} cy_subject_reader_t;

/// Abstracts away the specifics of the transport (UDP, serial, CAN, etc) and the platform where Cy is running
/// (POSIX, baremetal MCU, RTOS, etc).
struct cy_platform_t
{
    /// The instance of Cy currently tied to this platform instance.
    /// It is assigned automatically in cy_new() and should not be altered by any other code.
    cy_t* cy;

    /// The subject-ID modulus depends on the width of the subject-ID field in the transport protocol.
    /// All nodes in the network shall share the same value.
    /// If heterogeneously redundant transports are used, then the smallest modulus shall be used.
    ///
    /// The full range of used subject-ID values is [0, CY_PINNED_SUBJECT_ID_MAX + 1 + modulus),
    /// where the values below or equal to CY_PINNED_SUBJECT_ID_MAX are used for pinned topics only.
    ///
    /// The modulus shall be a prime number because the subject-ID function uses a quadratic probing strategy:
    ///     subject_id = CY_PINNED_SUBJECT_ID_MAX + 1 + ((hash + evictions^2) mod modulus)
    /// Further, to enable fast reconstruction of the eviction count from the subject-ID, we impose an additional
    /// constraint that subject_id_modulus mod 4 == 3. The suitability of the modulus is checked at initialization.
    ///
    /// See https://en.wikipedia.org/wiki/Quadratic_probing
    /// See https://github.com/OpenCyphal-Garage/cy/issues/12#issuecomment-3577831960
    uint32_t subject_id_modulus;

    const struct cy_platform_vtable_t* vtable;
};

/// Most of the platform API is defined by this large vtable.
/// All functions are non-blocking except for spin(), which may or may not be blocking.
typedef struct cy_platform_vtable_t
{
    // === SUBJECT WRITER ===

    /// The factory returns NULL on OOM.
    /// The write method non-blockingly publishes a new message on the subject; the message lifetime ends upon return
    /// from this function.
    cy_subject_writer_t* (*subject_writer_new)(cy_platform_t*, uint32_t subject_id);
    void (*subject_writer_destroy)(cy_platform_t*, cy_subject_writer_t*);
    cy_err_t (*subject_writer_send)(cy_platform_t*, //
                                    cy_subject_writer_t*,
                                    cy_us_t    deadline,
                                    cy_prio_t  priority,
                                    cy_bytes_t message);

    // === SUBJECT READER ===

    /// The factory returns NULL on OOM.
    cy_subject_reader_t* (*subject_reader_new)(cy_platform_t*, uint32_t subject_id, size_t extent);
    void (*subject_reader_destroy)(cy_platform_t*, cy_subject_reader_t*);

    // === P2P ===

    /// Instructs the underlying transport layer to send a peer-to-peer transfer to the specified remote node.
    /// The message lifetime ends upon return from this function.
    /// If the transport layer needs any additional metadata to send a P2P message (e.g., destination address/port),
    /// it must be stored inside the responder context prior to cy_on_message() invocation.
    cy_err_t (*p2p_send)(cy_platform_t*,
                         const cy_p2p_context_t*, // Never NULL
                         cy_us_t    deadline,
                         uint64_t   remote_id,
                         cy_bytes_t message);

    /// Sets/updates the maximum extent of incoming P2P transfers. Messages larger than this may be truncated.
    /// The initial value prior to the first invocation is transport-defined.
    void (*p2p_extent_set)(cy_platform_t*, size_t);

    // === EVENT LOOP ===

    /// Runs the event loop until the specified deadline, or until the first error. Early exit is allowed.
    /// If the deadline is in the past, update the event loop once without blocking and return.
    /// The cy_on_message() callback will be invoked from this function.
    /// This is the only platform function that is allowed to block.
    cy_err_t (*spin)(cy_platform_t*, cy_us_t deadline);

    // === MISC ===

    /// Returns the current monotonic time in microseconds. The initial time shall be non-negative.
    cy_us_t (*now)(cy_platform_t*);

    /// The semantics are per the standard realloc from stdlib, except:
    /// - If the size is zero, it must behave like free() (which is often the case in realloc() but technically an UB).
    /// - Constant-complexity is preferred -- the API complexity specs are given assuming O(1) alloc/free operations,
    ///   unless an expansion is needed, in which case the complexity is linear in the old size of the block.
    void* (*realloc)(cy_platform_t*, void*, size_t);

    /// Returns a random 64-bit unsigned integer.
    /// A TRNG is preferred; if not available, a PRNG will suffice, but its initial state MUST be distinct across
    /// reboots in quick succession, and it should be hashed with the node's unique identifier.
    ///
    /// A simple compliant solution that can be implemented in an embedded system without TRNG is:
    ///
    ///     static uint64_t g_prng_state __attribute__ ((section (".noinit")));  // adapt .noinit to your toolchain
    ///     g_prng_state += 0xA0761D6478BD642FULL;     // add Wyhash seed (64-bit prime)
    ///     const uint64_t seed[] = { g_prng_state };  // if possible, add more entropy here, like ADC noise
    ///     return rapidhash_withSeed(seed, sizeof(seed), local_uid);
    ///
    /// It is desirable to save the PRNG state in a battery-backed memory, if available; otherwise, in small MCUs one
    /// could also hash the entire RAM contents at startup to scavenge as much entropy as possible, or use ADC or clock
    /// noise. If an RTC is available, then the following is sufficient (extra entropy can be added via the seed array):
    ///
    ///     static uint_fast16_t g_counter = 0;
    ///     const uint64_t seed[] = { ((uint64_t)rtc_get_time() << 16U) + ++g_counter };  // Add ADC noise etc.
    ///     return rapidhash_withSeed(seed, sizeof(seed), local_uid);
    uint64_t (*random)(cy_platform_t*);
} cy_platform_vtable_t;

/// New message received on a topic or P2P. The data ownership is taken by this function.
/// The subject reader is NULL for P2P messages.
void cy_on_message(cy_platform_t* const             platform,
                   const cy_p2p_context_t           p2p_context,
                   const uint64_t                   remote_id,
                   const cy_subject_reader_t* const subject_reader,
                   const cy_message_ts_t            message);

#ifdef __cplusplus
}
#endif
