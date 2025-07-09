------------------------------ MODULE TopicOps ------------------------------
\* Key operators defined on Cyphal named topics.
\* This is pure TLA+ without PlusCal.
\* Pavel Kirienko <pavel@opencyphal.org>, MIT license

EXTENDS Utils
LOCAL INSTANCE Integers
LOCAL INSTANCE TLC
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets

\* Computes floor(log2(x)), with the special case floor(log2(0)) == -1
RECURSIVE Log2Floor(_)
Log2Floor(x) == IF x > 1 THEN 1 + Log2Floor(x \div 2) ELSE x - 1
LOCAL Check_Log2Floor ==
    /\ Log2Floor(0)   = -1 /\ Log2Floor(1)   = 0 /\ Log2Floor(2)   = 1 /\ Log2Floor(3) = 1 /\ Log2Floor(4) = 2
    /\ Log2Floor(255) =  7 /\ Log2Floor(256) = 8 /\ Log2Floor(257) = 8

\* Special case: Pow2(-1) = 0
Pow2(x) == IF x > 1 THEN 2^x ELSE x + 1
LOCAL Check_Pow2 ==
    /\ Pow2(-1) = 0
    /\ Pow2(0) =  1
    /\ Pow2(1) =  2
    /\ Pow2(2) =  4
    /\ Pow2(3) =  8

FloorToPow2(x) == Pow2(Log2Floor(x))
LOCAL Check_FloorToPow2 ==
    /\ FloorToPow2(0) = 0
    /\ FloorToPow2(1) = 1
    /\ FloorToPow2(2) = 2
    /\ FloorToPow2(3) = 2
    /\ FloorToPow2(4) = 4
    /\ FloorToPow2(7) = 4
    /\ FloorToPow2(8) = 8
    /\ FloorToPow2(9) = 8

\***********************************************************************************************************************
\* Subject-ID mapping function. The ring size is the total number of distinct subject-IDs.
\* TODO: Switch to quadratic probing: https://github.com/OpenCyphal-Garage/cy/issues/12
SubjectIDRing == 10
SubjectID(hash, evictions) == (hash + evictions) % SubjectIDRing

\***********************************************************************************************************************
\* COLLISION is when topics with different hashes land on the same subject-ID (see the subject_id mapping).
LeftWinsCollision(a, b) == IF   Log2Floor(a.age) # Log2Floor(b.age)
                           THEN Log2Floor(a.age) > Log2Floor(b.age)
                           ELSE a.hash < b.hash

LOCAL Check_LeftWinsCollision == LeftWinsCollision([hash |-> 100, age |-> 2008], [hash |-> 101, age |-> 1008])
                              /\ LeftWinsCollision([hash |-> 100, age |-> 1008], [hash |-> 101, age |-> 1008])

\* DIVERGENCE is when topics with the same hash are found to have different eviction counters:
\* the eviction counters have to match, so we need to decide which one is the correct one.
LeftWinsDivergence(a, b) == \/  Log2Floor(a.age) > Log2Floor(b.age)
                            \/ (Log2Floor(a.age) = Log2Floor(b.age) /\ a.evictions > b.evictions)

LOCAL Check_LeftWinsDivergence == LeftWinsDivergence([age |-> 124, evictions |-> 5], [age |-> 123, evictions |-> 4])
                               /\ LeftWinsDivergence([age |-> 124, evictions |-> 5], [age |-> 124, evictions |-> 4])

\***********************************************************************************************************************
\* The result is Nothing if no such topic exists.
\* Topics are stored in sets because all operations on them are ordering-invariant,
\* which is a basic prerequisite for CRDT operations.
GetByHash(hash, topics)            == Get(topics, LAMBDA x: x.hash = hash)
GetBySubjectID(subject_id, topics) == Get(topics, LAMBDA x: SubjectID(x.hash, x.evictions) = subject_id)

LOCAL Check_GetByHash == GetByHash(123, {[hash |-> 100], [hash |-> 123]}).hash = 123
                      /\ GetByHash(100, {[hash |-> 100], [hash |-> 123]}).hash = 100
                      /\ GetByHash(200, {[hash |-> 100], [hash |-> 123]}) = Nothing

LOCAL Check_GetBySubjectID == GetBySubjectID(6, {[hash |-> 3, evictions |-> 0], [hash |-> 4, evictions |-> 2]}).hash = 4
                           /\ GetBySubjectID(4, {[hash |-> 3, evictions |-> 1], [hash |-> 4, evictions |-> 2]}).hash = 3

\***********************************************************************************************************************
\* A set of topics without the specified one. Same set if the specified topic is not a member.
RemoveTopic(hash, topics) == { t \in topics : t.hash # hash }

\* Add or replace a topic into a set of topics.
\* Use this to mutate a topic state in a set.
ReplaceTopic(new, topics) == {new} \cup RemoveTopic(new.hash, topics)

\* A set of topics extended with the specified one, and the existing topics possibly altered.
\* Uniqueness is guaranteed; if the topic is in the set already, it will be modified.
\* This can also be used to model state update of the local topic table.
RECURSIVE AllocateTopic(_, _)
AllocateTopic(t, topics) ==
    LET ts == RemoveTopic(t.hash, topics)
        x == GetBySubjectID(SubjectID(t.hash, t.evictions), ts)
        Evicted(z) == [hash |-> z.hash, evictions |-> 1 + z.evictions, age |-> z.age]
    IN   IF x = Nothing             THEN {t} \cup ts
    ELSE IF LeftWinsCollision(t, x) THEN AllocateTopic(Evicted(x), {t} \cup ts)
    ELSE                                 AllocateTopic(Evicted(t), ts)          \* Retry with evictions+1

LOCAL Check_AllocateTopic ==
    LET tp(h, e, a) == [hash |-> h, evictions |-> e, age |-> a] IN
    \* Add topic to an empty set; succeeds immediately.
    /\ AllocateTopic(tp(1000, 0, 3), {}) = {tp(1000, 0, 3)}
    \* The topic is already in the set, no-op.
    /\ AllocateTopic(tp(1000, 0, 3), {tp(1000, 0, 3)}) = {tp(1000, 0, 3)}
    \* The topic is already in the set with different parameters; replaced.
    /\ AllocateTopic(tp(1000, 1, 3), {tp(1000, 0, 3)}) = {tp(1000, 1, 3)}
    /\ AllocateTopic(tp(1000, 0, 4), {tp(1000, 0, 3)}) = {tp(1000, 0, 4)}
    \* Loses arbitration to the only other topic with hash=3.
    /\ AllocateTopic(tp(2, 1, 2), {             tp(3, 0, 4)}) = {tp(2, 2, 2), tp(3, 0, 4)}
    /\ AllocateTopic(tp(2, 1, 2), {tp(2, 0, 2), tp(3, 0, 4)}) = {tp(2, 2, 2), tp(3, 0, 4)}
    \* Loses arbitration to hash=3, displaces hash=4.
    /\ AllocateTopic(tp(2, 1, 2), {             tp(3, 0, 4), tp(4, 0, 1)}) = {tp(4, 1, 1), tp(2, 2, 2), tp(3, 0, 4)}
    /\ AllocateTopic(tp(2, 1, 2), {tp(2, 0, 2), tp(3, 0, 4), tp(4, 0, 1)}) = {tp(4, 1, 1), tp(2, 2, 2), tp(3, 0, 4)}
    \* Cyclic displacement: hash=0 displaces hash=1, etc.
    /\ AllocateTopic(tp(0, 1, 1024),
        { tp(1, 0, 512),
          tp(2, 0, 256),
          tp(3, 0, 128),
          tp(4, 0, 64),
          tp(5, 0, 32),
          tp(6, 0, 16),
          tp(7, 0, 8),
          tp(8, 0, 4),
          tp(9, 0, 2) }) =
        { tp(9, 1, 2),
          tp(8, 1, 4),
          tp(7, 1, 8),
          tp(6, 1, 16),
          tp(5, 1, 32),
          tp(4, 1, 64),
          tp(3, 1, 128),
          tp(2, 1, 256),
          tp(1, 1, 512),
          tp(0, 1, 1024) }
    \* Cyclic displacement: hash=0 displaces hash=1, etc, skips a gap.
    /\ AllocateTopic(tp(0, 1, 1024),
        { tp(1, 0, 512),
          tp(2, 0, 256),
          tp(3, 0, 128),
          tp(4, 0, 64),
          tp(5, 0, 32),    \* lowest age => will see the most evictions.
          tp(6, 0, 2048),
          tp(7, 0, 2048),
          tp(8, 0, 2048),
          tp(9, 0, 2048) }) =
        { tp(5, 5, 32),
          tp(4, 1, 64),
          tp(3, 1, 128),
          tp(2, 1, 256),
          tp(1, 1, 512),
          tp(0, 1, 1024),  \* breaking point, the rest unmodified.
          tp(6, 0, 2048),
          tp(7, 0, 2048),
          tp(8, 0, 2048),
          tp(9, 0, 2048) }
    \* Allocation catchup: age goes up while the eviction counter goes down, forcing reordering. Subject-ID goes 5 => 3.
    /\ AllocateTopic(tp(2, 1, 16), {tp(2, 3, 2), tp(3, 0, 8), tp(4, 0, 4)}) = {tp(4, 1, 4), tp(3, 1, 8), tp(2, 1, 16)}

\***********************************************************************************************************************
\* Constructs a conflict-free topic set. This is meant for constructing the initial node state.
\* Each hash can occur at most once.
RECURSIVE AllocateTopics(_, _)
AllocateTopics(new, topics) ==
    IF Cardinality(new) = 0 THEN topics
    ELSE LET t == CHOOSE x \in new : TRUE
         IN AllocateTopics(new \ {t}, AllocateTopic(t, topics))

LOCAL Check_AllocateTopics ==
    LET tp(h, e, a) == [hash |-> h, evictions |-> e, age |-> a] IN
    AllocateTopics({tp(13, 0, 2), tp(3, 0, 8), tp(4, 0, 4)}, {}) = {tp(13, 2, 2), tp(4, 0, 4), tp(3, 0, 8)}

\***********************************************************************************************************************
\* Implementation of the divergence resolution rule with CRDT age merge.
LOCAL AcceptGossip_Divergence(remote, topics) ==
    LET hash == remote.hash
        local == GetByHash(hash, topics)
        \* The serialization protocol floors the remote age to pow2 before transmission.
        new_age == Max({IF local # Nothing THEN local.age ELSE 0, FloorToPow2(remote.age)})
    IN
    IF local # Nothing THEN
        IF local.evictions # remote.evictions /\ LeftWinsDivergence(remote, local)
        THEN AllocateTopic([hash|->hash, evictions|->remote.evictions, age|->new_age], topics)
        ELSE              {[hash|->hash, evictions|-> local.evictions, age|->new_age]} \cup RemoveTopic(hash, topics)
    ELSE topics

LOCAL Check_AcceptGossip_Divergence ==
    LET tp(h, e, a) == [hash |-> h, evictions |-> e, age |-> a] IN
    \* Not our topic.
    /\ AcceptGossip_Divergence(tp(3, 1, 4), {}) = {}
    /\ AcceptGossip_Divergence(tp(3, 1, 4), {tp(4, 1, 4)}) = {tp(4, 1, 4)}
    \* Update age only, no divergence.
    /\ AcceptGossip_Divergence(tp(4, 1, 2), {tp(4, 1, 4)}) = {tp(4, 1, 4)}
    /\ AcceptGossip_Divergence(tp(4, 1, 70), {tp(4, 1, 4)}) = {tp(4, 1, 64)}
    \* Resolve divergence -- remote wins.
    /\ AcceptGossip_Divergence(tp(4, 3, 70), {tp(4, 1, 4)}) = {tp(4, 3, 64)}
    \* Resolve divergence -- local wins.
    /\ AcceptGossip_Divergence(tp(4, 3, 2), {tp(4, 1, 5)}) = {tp(4, 1, 5)}

\* Implementation of the collision resolution rule.
LOCAL AcceptGossip_Collision(remote, topics) ==
    LET local == GetBySubjectID(SubjectID(remote.hash, remote.evictions), topics)
    IN IF local # Nothing /\ LeftWinsCollision(remote, local)
    THEN AllocateTopic([hash |-> local.hash, evictions |-> local.evictions + 1, age |-> local.age], topics)
    ELSE topics

LOCAL Check_AcceptGossip_Collision ==
    LET tp(h, e, a) == [hash |-> h, evictions |-> e, age |-> a] IN
    \* No collision.
    /\ AcceptGossip_Collision(tp(3, 1, 4), {}) = {}
    /\ AcceptGossip_Collision(tp(3, 1, 4), {tp(4, 1, 4)}) = {tp(4, 1, 4)}
    \* Remote wins.
    /\ AcceptGossip_Collision(tp(3, 2, 8), {tp(4, 1, 4)}) = {tp(4, 2, 4)}
    \* Local wins.
    /\ AcceptGossip_Collision(tp(3, 2, 4), {tp(4, 1, 8)}) = {tp(4, 1, 8)}

\* An updated sequence of topics based on a received gossip message.
AcceptGossip(remote, topics) == AcceptGossip_Collision(remote, AcceptGossip_Divergence(remote, topics))
LOCAL Check_AcceptGossip ==
    /\ Check_AcceptGossip_Divergence
    /\ Check_AcceptGossip_Collision
    \* Empirical issue.
    /\ AcceptGossip(
           [ hash |-> 11, evictions |-> 0, age |-> 6],
           {[hash |-> 1,  evictions |-> 0, age |-> 6]}
       ) = {[hash |-> 1,  evictions |-> 0, age |-> 6]}
    /\ AcceptGossip(
           [ hash |-> 11, evictions |-> 0, age |-> 6],
           {[hash |-> 1,  evictions |-> 0, age |-> 3]}
       ) = {[hash |-> 1,  evictions |-> 1, age |-> 3]}
    /\ AcceptGossip(
           [ hash |-> 1,  evictions |-> 0, age |-> 6],
           {[hash |-> 11, evictions |-> 0, age |-> 6]}
       ) = {[hash |-> 11, evictions |-> 1, age |-> 6]}
    /\ AcceptGossip(
           [ hash |-> 1,  evictions |-> 0, age |-> 6],
           {[hash |-> 11, evictions |-> 0, age |-> 9]}
       ) = {[hash |-> 11, evictions |-> 0, age |-> 9]}
    \* Empirical issue.
    /\ AcceptGossip(
           [hash |-> 1, evictions |-> 0, age |-> 2],
           {[hash |-> 2, evictions |-> 0, age |-> 1], [hash |-> 11, evictions |-> 0, age |-> 2]}
       ) = {[hash |-> 2, evictions |-> 1, age |-> 1], [hash |-> 11, evictions |-> 1, age |-> 2]}
    \* The gossip age is lower, but its (floor o log2) is the same, so it wins due to smaller hash.
    /\ AcceptGossip(
           [hash |-> 1, evictions |-> 2, age |-> 4],
           {[hash |-> 2, evictions |-> 1, age |-> 5], [hash |-> 11, evictions |-> 3, age |-> 5]}
       ) = {[hash |-> 2, evictions |-> 2, age |-> 5], [hash |-> 11, evictions |-> 4, age |-> 5]}

\***********************************************************************************************************************
\* Divergent allocation detector operating on a function node_id -> {topic_0, topic_1, ..., topic_n}
\* A divergent allocation occurs when topic records with the same hash have distinct eviction counters.
\* If no divergences are found, the result is an empty set.
FindDivergent(node_topics) ==
    LET hashes == { t.hash : t \in UNION Range(node_topics) }
        flat == { [hash |-> t.hash, evictions |-> t.evictions] : t \in UNION Range(node_topics) }
    IN { h \in hashes : Cardinality({ s \in flat : s.hash = h }) > 1 }

LOCAL Check_FindDivergent ==
    LET tp(h, e) == [hash |-> h, evictions |-> e, age |-> 0] IN
    /\ FindDivergent(1 :> {tp(4, 0), tp(2, 0)} @@ 2 :> {tp(3, 0), tp(6, 1)}) = {}
    /\ FindDivergent(1 :> {tp(4, 0), tp(2, 0)} @@ 2 :> {tp(3, 0), tp(2, 1)}) = {2}

\***********************************************************************************************************************
\* Allocation collision detector operating on a function node_id -> {topic_0, topic_1, ..., topic_n}
\* A collision occurs when topic records with distinct hashes have identical subject-ID.
\* If no collisions are found, the result is an empty set.
FindCollisions(node_topics) ==
    LET flat == { [hash |-> t.hash, subject_id |-> SubjectID(t.hash, t.evictions)] : t \in UNION Range(node_topics) }
        subject_ids == { t.subject_id : t \in flat }
    IN { s \in subject_ids : Cardinality({ t \in flat : t.subject_id = s }) > 1 }

LOCAL Check_FindCollisions ==
    LET tp(h, e) == [hash |-> h, evictions |-> e, age |-> 0] IN
    /\ FindCollisions(1 :> {tp(2, 0), tp(3, 0)} @@ 2 :> {tp(3, 0), tp(4, 0)}) = {}
    /\ FindCollisions(1 :> {tp(2, 0), tp(3, 1)} @@ 2 :> {tp(3, 0), tp(4, 0)}) = {4}
    /\ FindCollisions(1 :> {tp(2, 2), tp(3, 1)} @@ 2 :> {tp(3, 0), tp(4, 0)}) = {4}
    /\ FindCollisions(1 :> {tp(2, 1), tp(3, 3)} @@ 2 :> {tp(3, 0), tp(4, 2)}) = {3, 6}

\***********************************************************************************************************************
Check_TopicOps ==
    /\ Check_Log2Floor
    /\ Check_Pow2
    /\ Check_FloorToPow2
    /\ Check_LeftWinsCollision
    /\ Check_LeftWinsDivergence
    /\ Check_GetByHash
    /\ Check_GetBySubjectID
    /\ Check_AllocateTopic
    /\ Check_AllocateTopics
    /\ Check_AcceptGossip
    /\ Check_FindDivergent
    /\ Check_FindCollisions

========================================================================================================================
