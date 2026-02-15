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

The thing to note is that each message on a subject carries its own CRDT gossip state, which allows instant consensus synchronization without waiting for the next gossip broadcast. This ensures fast consensus convergence. The consensus data is only relevant if the message is published on a subject; if sent P2P, then the eviction count cannot be reconstructed as there is no subject-ID known, so the consensus data is ignored by the receiver.

The message tags must be unique across reboots to avoid misattribution; for that, they are randomly initialized and incremented with every published message to enable ordering reconstruction and loss detection. Message tags can be initialized using PRNG with a good seed; the API docs provide examples how this could be achieved (easily) on an embedded system without a hardware TRNG.

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
uint64 tag              # From the acknowledged message.
uint64 topic_hash       # From the acknowledged message.
# Total size 17 bytes.
```

#### Types 3 (best-effort response), 4 (reliable response), 5 (response ack), 6 (response nack)

Response tags are not used for ordering recovery since there is a seqno available, and there is no risk of reboot misattribution -- they are only needed for acknowledgement correlation and as such they are much narrower and there is no monotonicity requirement, the sender can choose values arbitrarily.

For P2P NACKs are well-defined since these interactions are inherently unicast.

The (n)ack priority level must match that of the original response.

```bash
uint6 type
void2
uint64 message_tag      # The tag of the published message this response pertains to.
uint48 seqno            # Incremented starting from zero for each response to this message; used for streaming.
uint16 tag              # Chosen by the responder arbitrarily for ack correlation, if needed.
# Header size 17 bytes. Payload follows, unless ACK.
```

#### Type 7 (topic allocation CRDT gossip)

This is usually broadcast, but when consensus divergence is discovered it can also be immediately unicast to the infringing parties at the discretion of the sender. The important difference here is that the broadcast rate has to be tightly managed to avoid overwhelming the smaller nodes, while P2P can be sent directly without strict bandwidth control.

```bash
uint6 type
void2
int8   topic_log_age    # floor(log2(topic_age)) if topic_age>0 else -1
uint64 topic_hash
uint32 topic_evictions
utf8[<=CY_TOPIC_NAME_MAX] topic_name  # Has 1 byte length prefix. The name is normalized and nonempty.
# Total size is 15 bytes + topic name length.
```

#### Type 8 (topic discovery scout)

This is typically broadcast to let every node check if it has any matching topics. On match, responses are sent using the CRDT gossip message either unicast to the origin of the scout or broadcast.

```bash
uint6 type
void2
utf8[<=CY_TOPIC_NAME_MAX] pattern  # Has 1 byte length prefix. The pattern is applied to normalized names.
# Total size is 2 bytes + pattern length.
```
