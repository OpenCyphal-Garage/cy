# Cyphal session layer design notes

These notes are useful for understanding how the protocol is built but are generally not useful for end-users -- they should
 instead refer to the top-level `README.md` and also to the API documentation in [`cy.h`](./cy.h).

The Cyphal session layer is a new addition in Cyphal v1.1. It provides higher-level protocol abstractions including named topics, new RPC semantics, optional reliable and ordered message delivery, and service discovery. The objective is to provide intentionally compact and highly robust publish-subscribe and request-response communication patterns that can be used in a variety of applications, including those with stringent real-time and reliability requirements. The solution is fully decentralized and is based on a simple CRDT consensus algorithm internally.

The Cyphal transport layer is borrowed from Cyphal v1.0 with only minimal changes; crucially, the transport layer has seen no increase in complexity compared to the previous version, and Cyphal/CAN v1.0 remains compatible and interoperable with the new Cyphal v1.1.

## Transport layer requirements

The transport layer provides _unreliable_ _deduplicated_ (at most one) _unordered_ delivery of messages either to:

- A _group of subscribers_ on a given _subject_ identified with a numerical subject-ID (IGMP group, CAN ID, etc).
- A specified _remote note_ direct peer-to-peer (_P2P_).

An exception is applied to the single _broadcast subject_ that takes the highest subject-ID: deduplication is not required on it to improve scalability; the session layer accepts occasional message duplication on this subject. This exception is due to the fact that all nodes participate in the broadcast subject, which may put strain on the smaller nodes.

The transport layer supports messages of arbitrary size, providing _segmentation_/_reassembly_ transparently to the higher layers. In high-reliability applications, redundant transport interfaces with transparent failover may be used.

The transport layer guarantees message integrity; messages are either delivered intact or not delivered.

The transport layer _does not_ provide message ordering recovery or reliable delivery (messages may arrive out of order or may not arrive at all).

The transport layer provides network participant discovery as a side effect of joining the broadcast subject.

These are very basic functions that result in a very compact transport interface contract that is easy to implement. The Cyphal specification predefines some transport layers, such as Cyphal/UDP or Cyphal/CAN; additional transport layers can be easily constructed ad-hoc as well.

## Session layer

For the description of the CRDT consensus algorithm and the topic allocation protocol, please refer to the formal verification model in `/formal_verification`.

The transport delivers deduplicated messages, but duplication due to retransmission in case of lost acks may still  occur (for the transport such messages are seen as distinct). To mitigate, additional deduplication is performed at the session layer only for reliable messages based on their 64-bit unique tags.

The session layer is designed to be mostly invariant to the delivery method used: multicast, unicast, or broadcast. This allows senders to choose the preferred delivery method ad-hoc.

### Subject-ID ranges

The set of subject-ID values ranges from zero (inclusive) up to some transport-specific boundary. For Cyphal/CAN, the maximum is $2^{17}-1$, while for Cyphal/UDP (and all IPv4-based transports in general) the maximum is $2^{23}-1$ due to L2 multicast limitations.

Subject-ID values from 0 to 8191 inclusive are reserved for pinned topics, which are guaranteed to be collision-free.

The maximum subject-ID value is reserved for broadcast subject that is used for low-rate broadcast gossip propagation and scouts. For Cyphal/CAN, this is subject 131071=0x1ffff, for Cyphal/UDP this is 8388607=0x7fffff.

Values from 8192 (inclusive) up to (8191+modulus) (inclusive) are used for automatic subject-ID allocation for topics. THe modulus is the largest prime number not greater than the maximum subject-ID minus 8191 such that $\text{modulus} mod 4 = 3$ holds. The latter condition enables very efficient constant-time reconstruction of the eviction counter from the subject-ID; while this capability is currently not used in the protocol design (an attempt to use it to optimize gossip propagation was made but rejected due to ambiguities that arise once the eviction counter exceeds half the modulus), it might come useful in the future, especially for diagnostics. For posterity, a simple solver that reconstructs the eviction counter from the subject-ID is provided below.

The subject-ID is derived from the topic hash and eviction counter using quadratic probing. This probing strategy guarantees unique placement until the eviction counter exceeds half the modulus, at which point the sequence will restart. Such restrarting behavior is expected and may occur during normal operation of the network. The eviction counter itself is not expected to overflow, as it is wide enough; for reference, it will take 136 years of continuous churn at 1 Hz to overflow a 32-bit eviction counter (eviction counters are not incremented continuously but only when the network configuration is changed in a way that triggers collisions, so the limit is unreachable in any practical scenario).

```c++
// a**e mod m
static uint32_t pow_mod_u32(uint32_t a, uint32_t e, const uint32_t m)
{
    uint32_t r = 1 % m;
    a %= m;
    while (e) {
        if (e & 1U) {
            r = (uint32_t)(((uint64_t)r * (uint64_t)a) % m);
        }
        a = (uint32_t)(((uint64_t)a * (uint64_t)a) % m);
        e >>= 1U;
    }
    return r;
}

// Legendre symbol: a^((p-1)/2) mod p is 1 for residues, p-1 for non-residues, 0 for a==0.
static bool is_quadratic_residue_prime(const uint32_t a, const uint32_t p)
{
    return (a == 0) || (pow_mod_u32(a, (p - 1U) / 2U, p) == 1U);
}

// Derives evictions from a non-pinned subject-ID. For pinned subject-ID returns zero unconditionally.
// Assumes subject_id_modulus is a prime with (subject_id_modulus % 4) == 3.
// Returns UINT32_MAX if the subject-ID was obtained using distinct parameters/expression (no solutions).
// If evictions>floor(modulus/2), the subject-ID sequence repeats, leading to non-unique solutions.
// Complexity is O(1).
// This implementation has been exhaustively brute-force verified at least for modulus values 131071 and 8388607.
static uint32_t topic_evictions_from_subject_id(const uint64_t hash,
                                                const uint32_t subject_id,
                                                const uint32_t subject_id_modulus)
{
    const uint32_t p = subject_id_modulus;
    assert((p > 3) && ((p & 3U) == 3U)); // Method below requires p&3=3, i.e. p%4=3
    if ((subject_id <= CY_SUBJECT_ID_PINNED_MAX) || is_pinned(hash)) {
        return 0; // Pinned subjects are collision-free, assume zero evictions.
    }

    const uint32_t base = subject_id - (CY_SUBJECT_ID_PINNED_MAX + 1U);
    if (base >= p) {
        return UINT32_MAX; // The subject-ID was calculated using distinct parameters.
    }

    const uint32_t delta = (uint32_t)(((uint64_t)base + (uint64_t)p - (hash % p)) % p); // delta = (base - h) mod p
    if (!is_quadratic_residue_prime(delta, p)) {
        return UINT32_MAX; // The subject-ID was calculated using distinct parameters.
    }

    // sqrt(delta) mod p (since p % 4 == 3): r = delta^((p+1)/4) mod p
    const uint32_t r1 = (delta == 0U) ? 0U : pow_mod_u32(delta, (p + 1U) / 4U, p);
    const uint32_t r2 = (r1 == 0U) ? 0U : (p - r1);

    uint32_t       best     = UINT32_MAX;
    const uint32_t roots[2] = { r1, r2 };
    for (unsigned i = 0; i < 2; i++) {
        const uint64_t s = roots[i];
        // We assume the eviction counter doesn't exceed half-modulus as that leads to ambiguity.
        if ((s <= (p / 2U)) && (s < best)) {
            assert(base == ((hash % p) + ((uint64_t)(s % p) * (uint64_t)(s % p)) % p) % p);
            best = (uint32_t)s;
        }
    }
    return best;
}
```

### Headers

>TODO: Pinned topics on CAN must have no header to ensure backward compatibility, sort this out later.

The transport layer just ferries **opaque blobs between nodes**. The job of the session layer is to build and interpret them. To enable that, the session layer adds small fixed-size headers to messages. All headers carry the header type in the 6 least significant bits of the first byte; the rest is header-specific. All headers have a fixed size of 24 bytes and favor natural alignment where possible to simplify parsing. The following header types are defined:

```c++
#define HEADER_BYTES     24U
#define HEADER_TYPE_MASK 63U
typedef enum
{
    header_msg_be   = 0,    ///< Best-effort published message with user payload.
    header_msg_rel  = 1,    ///< Reliable published message with user payload. Requires acknowledgement.
    header_msg_ack  = 2,    ///< Acknowledgement of a reliable published message. No payload.
    header_rsp_be   = 3,    ///< Best-effort response with user payload. Requires no acknowledgement.
    header_rsp_rel  = 4,    ///< Reliable response with user payload. Requires acknowledgement.
    header_rsp_ack  = 5,    ///< Acknowledgement of a reliable response. No payload.
    header_rsp_nack = 6,    ///< Negative acknowledgement of a reliable message or response. No payload.
    header_gossip   = 7,    ///< Topic allocation CRDT gossip. No payload.
    header_scout    = 8,    ///< Topic discovery scout. No payload.
    // Rest reserved for future use.
} header_type_t;
```

DSDL notation is used to define the headers. Void fields are sent zero and ignored on reception. Incompatibility fields are sent zero; on reception, messages must be discarded if nonzero.

#### Types 0 (best-effort message publication), 1 (reliable message publication)

Each message carries its own _inline_ CRDT gossip state, which allows instant consensus update without waiting for the next normal gossip (broadcast/epidemic). Handling such inline gossips is not essential for protocol correctness (CRDT convergence), but it does improve its performance, so it is recommended that all nodes do that.

The message tags must be unique across reboots to avoid misattribution; for that, they are randomly initialized and incremented with every published message to enable ordering reconstruction and loss detection. Message tags can be initialized using PRNG with a good seed; the API docs provide examples how this could be achieved (easily) on an embedded system without a hardware TRNG. It follows that tags can (and do) wrap around.

```bash
uint6 type
void2
void8
uint8  incompatibility
int8   topic_log_age    # floor(log2(topic_age)) if topic_age>0 else -1, like in the gossip message.
uint32 evictions        # Offset 4 bytes
uint64 topic_hash       # For subject allocation collision detection and immediate consensus updates.
uint64 tag              # For ordering recovery and acknowledgement & response correlation. Random-init, wraparound.
# Payload follows.
```

#### Type 2 (publication acknowledgement)

Sent in response to a reliable message publication. Message publications have no negative acknowledgements because they are inherently multicast: even if we can't accept a message, someone else might be able to.

The ack priority level must match that of the original message.

```bash
uint6 type
void2
void24
uint32 incompatibility
uint64 topic_hash       # From the acknowledged message.
uint64 tag              # From the acknowledged message.
```

#### Types 3 (best-effort response), 4 (reliable response), 5 (response ack), 6 (response nack)

Response tags are not used for ordering recovery since there is a seqno available, and there is no risk of reboot misattribution -- they are only needed for acknowledgement correlation and as such they are much narrower and there is no monotonicity requirement, the sender can choose values arbitrarily.

For P2P NACKs are well-defined since these interactions are inherently unicast.

The (n)ack priority level must match that of the original response.

```bash
uint6 type
void2
void24
uint32 incompatibility
uint48 seqno            # Incremented starting from zero for each response to this message; used for streaming.
uint16 tag              # Chosen by the responder arbitrarily for ack correlation, if needed.
uint64 message_tag      # The tag of the published message this response pertains to.
# Payload follows, unless ACK.
```

#### Type 7 (topic allocation CRDT gossip)

This is broadcast at a constant rate and may also be epidemic unicast ad-hoc when consensus needs repair to speed up the repair process. Broadcast is the ultimate last-resort baseline for eventual convergence where all nodes MUST participate, while epidemic unicasting is an option.

The TTL field is decremented every time the gossip is forwarded to gossip peers to prevent cycles. Broadcast gossips MUST have zero TTL.

The TTL is only the last line of defence against cycles; each forwarding node must keep a short list of recently seen gossips to prevent redundant transmissions early.

```bash
uint6 type
void2
void8
uint8  ttl              # Must be zero for broadcast gossips.
int8   topic_log_age    # floor(log2(topic_age)) if topic_age>0 else -1
uint32 incompatibility
uint64 topic_hash
uint32 topic_evictions
void24                  # May be used to extend the evictions counter and/or some other purpose.
utf8[<=CY_TOPIC_NAME_MAX] topic_name  # Has 1 byte length prefix. The name is normalized.
# Total size is 24 bytes + topic name length.
```

#### Type 8 (topic discovery scout)

This is typically broadcast to let every node check if it has any matching topics. On match, responses are sent as the ordinary CRDT gossip message with zero TTL. Responses are usually unicast, but this is not required; the only requirement is that the requester should be likely to receive them.

```bash
uint6 type
void2
void24
uint32 incompatibility
uint64 incompatibility1
void56
utf8[<=CY_TOPIC_NAME_MAX] pattern  # Has 1 byte length prefix. The pattern is applied to normalized names.
# Total size is 24 bytes + pattern length.
```

### CRDT gossips

The topic to subject-ID mapping is done via a CRDT described in the formal specification/verification model. For the CRDT to function, nodes must periodically exchange their states with each other. A simple and robust approach is to regularly broadcast all CRDT state of each node or a part of it, the limit case of the latter being a single topic per message with a scheduler choosing which topic to gossip next. The next topic to gossip is that which has recently seen conflicts/divergences, then the one whose gossips haven't been observed the longest.

The broadcast gossip rate is constant on a large time interval, but short-term it is variable due to intentional dithering, which is introduced to enable duplicate gossip suppression, similar to GAAP/ZMAAP. Removal of duplicates speeds up topic discovery and consensus repair.

While broadcast gossips are robust, they are inherently slow. To improve CRDT repair time, Cyphal v1.1 includes epidemic unicast gossips, roughly derived from Cyclon/HyParView etc. Each node holds a randomly chosen set of remotes that are likely to be currently online, called "gossip peers"; the gossip peer set is refreshed stochastically. When consensus needs repair, the affected topics are scheduled to be broadcast-gossiped at the next opportunity (the broadcast rate is fixed so all we can do is to alter the schedule not the rate), and epidemic unicast gossips of the affected topics are emitted immediately to a randomly chosen small subset of the gossip peers (typ. 2 peers only) with some positive TTL (typ. ~16). Every peer upon reception of epidemic gossips will update its own CRDT state and forward the gossips (updated from the local CRDT state as necessary) unless they lost arbitration to local state, in which case new gossips with the newer CRDT state will be emitted instead.

#### Prior art

- [HyParView](https://asc.di.fct.unl.pt/~jleitao/pdf/dsn07-leitao.pdf)
- [Epidemic broadcast trees](https://asc.di.fct.unl.pt/~jleitao/pdf/srds07-leitao.pdf)
- [Gossip-based peer sampling](https://www.inf.u-szeged.hu/~jelasity/cikkek/tocs05.pdf)
- [Cyclon](https://www.cs.unibo.it/babaoglu/courses/csns/resources/tutorials/cyclon.pdf)
- [Chord](https://en.wikipedia.org/wiki/Chord_%28peer-to-peer%29)

## Security/threat model

All nodes are trusted and there are no malicious actors. The protocol is designed to be robust against network faults and adverse conditions, but not against intentional attacks.

Security features are likely to be introduced as optional extensions of the protocol at a later stage, once the core has stabilized. Feedback, suggestions, and feature requests are welcome on the [OpenCyphal Forum](https://forum.opencyphal.org).
