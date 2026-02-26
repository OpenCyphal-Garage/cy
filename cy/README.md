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

The session layer is designed to be mostly invariant to the delivery method used: multicast, unicast, or broadcast. This allows senders to choose the preferred delivery method ad-hoc. An exception applies to message publications which serve as their own gossips only when multicast (because the subject-ID encodes the eviction counter, see below).

### Headers

>TODO: Pinned topics on CAN must have no header to ensure backward compatibility, sort this out later.

The transport layer just ferries **opaque blobs between nodes**. The job of the session layer is to build and interpret them. To enable that, the session layer adds small variable-size headers to the messages. All headers carry the header type in the 6 least significant bits of the first byte; the rest is header-specific. The following header types are defined:

```c++
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

DSDL notation is used to define the headers. Void fields are sent zero and ignored on reception.

#### Types 0 (best-effort message publication), 1 (reliable message publication)

One thing to note is that each message on a subject carries its own CRDT gossip state, which allows instant consensus synchronization without waiting for the next gossip broadcast. The topic hash and the age-logarithm-floor are included directly in the header while the evictions counter is derived from the subject-ID. The consensus data is only relevant if the message is published on a subject; if sent P2P, then the eviction count cannot be reconstructed as there is no subject-ID known, so the consensus data is ignored by the receiver.

The message tags must be unique across reboots to avoid misattribution; for that, they are randomly initialized and incremented with every published message to enable ordering reconstruction and loss detection. Message tags can be initialized using PRNG with a good seed; the API docs provide examples how this could be achieved (easily) on an embedded system without a hardware TRNG. It follows that tags can (and do) wrap around.

```bash
uint6 type
void2
int8   topic_log_age    # floor(log2(topic_age)) if topic_age>0 else -1, like in the gossip message.
uint64 tag              # For ordering recovery and for acknowledgement & response correlation.
uint64 topic_hash       # For subject allocation collision detection and immediate consensus updates.
# Header size 18 bytes. Payload follows.
```

#### Type 2 (publication acknowledgement)

Sent in response to a reliable message publication. Message publications have no negative acknowledgements because they are inherently multicast: even if we can't accept a message, someone else might be able to.

The ack priority level must match that of the original message.

```bash
uint6 type
void2
void8
uint64 tag              # From the acknowledged message.
uint64 topic_hash       # From the acknowledged message.
# Total size 18 bytes.
```

#### Types 3 (best-effort response), 4 (reliable response), 5 (response ack), 6 (response nack)

Response tags are not used for ordering recovery since there is a seqno available, and there is no risk of reboot misattribution -- they are only needed for acknowledgement correlation and as such they are much narrower and there is no monotonicity requirement, the sender can choose values arbitrarily.

For P2P NACKs are well-defined since these interactions are inherently unicast.

The (n)ack priority level must match that of the original response.

```bash
uint6 type
void2
void8
uint64 message_tag      # The tag of the published message this response pertains to.
uint48 seqno            # Incremented starting from zero for each response to this message; used for streaming.
uint16 tag              # Chosen by the responder arbitrarily for ack correlation, if needed.
# Header size 18 bytes. Payload follows, unless ACK.
```

#### Type 7 (topic allocation CRDT gossip)

This is broadcast at a constant rate and may also be epidemic unicast ad-hoc when consensus needs repair to speed up the repair process. Broadcast is the ultimate last-resort baseline for eventual convergence where all nodes MUST participate, while epidemic unicasting is an option.

The TTL field is decremented every time the gossip is forwarded to gossip peers to prevent cycles. Broadcast gossips MUST have zero TTL.

The TTL is only the last line of defence against cycles; each forwarding node must keep a short list of recently seen gossips to prevent redundant transmissions early.

```bash
uint6 type
void2
uint8 ttl               # Must be zero for broadcast gossips.
uint8 incompatibility   # Transmit zero; ignore message if this is not zero.
# offset 3
int8   topic_log_age    # floor(log2(topic_age)) if topic_age>0 else -1
uint64 topic_hash
uint32 topic_evictions
void8                   # May be used to extend the evictions counter and/or some other purpose.
utf8[<=CY_TOPIC_NAME_MAX] topic_name  # Has 1 byte length prefix. The name is normalized.
# Total size is 18 bytes + topic name length.
```

#### Type 8 (topic discovery scout)

This is typically broadcast to let every node check if it has any matching topics. On match, responses are sent as the ordinary CRDT gossip message with zero TTL. Responses are usually unicast, but this is not required; the only requirement is that the requester should be likely to receive them.

```bash
uint6 type
void2
void64
uint64 incompatibility  # Transmit zero; ignore message if this is not zero.
utf8[<=CY_TOPIC_NAME_MAX] pattern  # Has 1 byte length prefix. The pattern is applied to normalized names.
# Total size is 18 bytes + pattern length.
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
