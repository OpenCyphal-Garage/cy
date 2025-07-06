------------------------------ MODULE cyphal_topics ------------------------------

EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANT Nothing, Debug, NodeCount, Duration, TopicsPerNodeMax, DistinctTopicCount, InitialEvictionMax, InitialAgeMax

ASSUME Debug \in BOOLEAN
ASSUME NodeCount \in Nat /\ NodeCount > 1
ASSUME Duration \in Nat /\ Duration > 1

ASSUME TopicsPerNodeMax \in Nat /\ TopicsPerNodeMax > 0 /\ TopicsPerNodeMax <= DistinctTopicCount
ASSUME DistinctTopicCount \in Nat /\ DistinctTopicCount > 0
ASSUME InitialEvictionMax \in Nat /\ InitialEvictionMax > 0
ASSUME InitialAgeMax \in Nat /\ InitialAgeMax > 0

\**********************************************************************************************************************
\* General utilities and helpers.

PrintVal(id, exp) == Print(<<id, exp>>, TRUE)

Remove(s, e) == SelectSeq(s, LAMBDA t: t # e)

Max(a, b) == IF a > b THEN a ELSE b

IsUnique(s) ==
  \A i, j \in 1..Len(s):
    i # j => s[i] # s[j]

HasDuplicates(seq) ==
  \E i, j \in 1..Len(seq):
    i # j /\ seq[i] = seq[j]

FirstMatch(haystack, test(_)) ==
    LET i == CHOOSE i \in 1..(Len(haystack)+1): (i > Len(haystack)) \/ test(haystack[i])
    IN IF i > Len(haystack) THEN Nothing ELSE haystack[i]

Check_FirstMatch == FirstMatch(<<1,2,3>>, LAMBDA x: x = 2) = 2
                 /\ FirstMatch(<<1,2,3>>, LAMBDA x: x = 4) = Nothing
                 /\ FirstMatch(<<>>, LAMBDA x: x = 0) = Nothing

Get(haystack, test(_)) ==
  LET matches == { x \in haystack : test(x) }
  IN IF matches = {} THEN Nothing ELSE CHOOSE x \in matches : TRUE

Check_Get == Get({1,2,3}, LAMBDA x: x = 2) = 2
          /\ Get({1,2,3}, LAMBDA x: x = 4) = Nothing
          /\ Get({}, LAMBDA x: x = 0) = Nothing

SeqToSet(s) == {s[i] : i \in DOMAIN s}

IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

\**********************************************************************************************************************
\* The core assumptions include that the hash function is perfect (no hash collisions) and the counters never overflow.
Topic == [hash : Nat, evictions : Nat, age : Nat]

\**********************************************************************************************************************
\* Computes floor(log2(x)), with the special case floor(log2(0)) == -1
RECURSIVE Log2Floor(_)
Log2Floor(x) == IF x > 1 THEN 1 + Log2Floor(x \div 2) ELSE x - 1
Check_Log2Floor ==
    /\ Log2Floor(0)   = -1 /\ Log2Floor(1)   = 0 /\ Log2Floor(2)   = 1 /\ Log2Floor(3) = 1 /\ Log2Floor(4) = 2
    /\ Log2Floor(255) =  7 /\ Log2Floor(256) = 8 /\ Log2Floor(257) = 8

\* Special case: Pow2(-1) = 0
Pow2(x) == IF x > 1 THEN 2^x ELSE x + 1
Check_Pow2 ==
    /\ Pow2(-1) = 0
    /\ Pow2(0) =  1
    /\ Pow2(1) =  2
    /\ Pow2(2) =  4
    /\ Pow2(3) =  8

FloorToPow2(x) == Pow2(Log2Floor(x))
Check_FloorToPow2 ==
    /\ FloorToPow2(0) = 0
    /\ FloorToPow2(1) = 1
    /\ FloorToPow2(2) = 2
    /\ FloorToPow2(3) = 2
    /\ FloorToPow2(4) = 4
    /\ FloorToPow2(7) = 4
    /\ FloorToPow2(8) = 8
    /\ FloorToPow2(9) = 8

\**********************************************************************************************************************
\* Subject-ID mapping function.
\* TODO: Switch to quadratic probing: https://github.com/OpenCyphal-Garage/cy/issues/12
SubjectIDRing == 10
SubjectID(hash, evictions) == (hash + evictions) % SubjectIDRing

\**********************************************************************************************************************
\* COLLISION is when topics with different hashes land on the same subject-ID (see the subject_id mapping).
LeftWinsCollision(a, b) == IF   Log2Floor(a.age) # Log2Floor(b.age)
                           THEN Log2Floor(a.age) > Log2Floor(b.age)
                           ELSE a.hash < b.hash

Check_LeftWinsCollision == LeftWinsCollision([hash |-> 100, age |-> 2008], [hash |-> 101, age |-> 1008])
                        /\ LeftWinsCollision([hash |-> 100, age |-> 1008], [hash |-> 101, age |-> 1008])

\**********************************************************************************************************************
\* DIVERGENCE is when topics with the same hash are found to have different eviction counters:
\* the eviction counters have to match, so we need to decide which one is the correct one.
LeftWinsDivergence(a, b) == \/  Log2Floor(a.age) > Log2Floor(b.age)
                            \/ (Log2Floor(a.age) = Log2Floor(b.age) /\ a.evictions > b.evictions)

Check_LeftWinsDivergence == LeftWinsDivergence([age |-> 124, evictions |-> 5], [age |-> 123, evictions |-> 4])
                         /\ LeftWinsDivergence([age |-> 124, evictions |-> 5], [age |-> 124, evictions |-> 4])

\**********************************************************************************************************************
\* The result is Nothing if no such topic exists.
\* Topics are stored in sets because all operations on them are ordering-invariant,
\* which is a basic prerequisite for CRDT operations.
GetByHash(hash, topics)            == Get(topics, LAMBDA x: x.hash = hash)
GetBySubjectID(subject_id, topics) == Get(topics, LAMBDA x: SubjectID(x.hash, x.evictions) = subject_id)

Check_GetByHash == GetByHash(123, {[hash |-> 100], [hash |-> 123]}).hash = 123
                /\ GetByHash(100, {[hash |-> 100], [hash |-> 123]}).hash = 100
                /\ GetByHash(200, {[hash |-> 100], [hash |-> 123]}) = Nothing

Check_GetBySubjectID == GetBySubjectID(6, {[hash |-> 3, evictions |-> 0], [hash |-> 4, evictions |-> 2]}).hash = 4
                     /\ GetBySubjectID(4, {[hash |-> 3, evictions |-> 1], [hash |-> 4, evictions |-> 2]}).hash = 3

\**********************************************************************************************************************
\* A set of topics without the specified one. Same set if the specified topic is not a member.
RemoveTopic(hash, topics) == { t \in topics : t.hash # hash }

\* A sequence of topics extended with the specified one, and the existing topics possibly altered.
\* Uniqueness is guaranteed; if the topic is in the sequence already, it will be modified.
\* This can also be used to model state update of the local topic table.
RECURSIVE AllocateTopic(_, _)
AllocateTopic(t, topics) ==
    LET ts == RemoveTopic(t.hash, topics)
        x == GetBySubjectID(SubjectID(t.hash, t.evictions), ts)
        Evicted(z) == [hash |-> z.hash, evictions |-> 1 + z.evictions, age |-> z.age]
    IN   IF x = Nothing             THEN {t} \cup ts
    ELSE IF LeftWinsCollision(t, x) THEN AllocateTopic(Evicted(x), {t} \cup ts)
    ELSE                                 AllocateTopic(Evicted(t), ts)          \* Retry with evictions+1

Check_AllocateTopic ==
    LET tp(h, e, a) == [hash |-> h, evictions |-> e, age |-> a] IN
    \* Add topic to an empty sequence; succeeds immediately.
    /\ AllocateTopic(tp(1000, 0, 3), {}) = {tp(1000, 0, 3)}
    \* The topic is already in the sequence, no-op.
    /\ AllocateTopic(tp(1000, 0, 3), {tp(1000, 0, 3)}) = {tp(1000, 0, 3)}
    \* The topic is already in the sequence with different parameters; replaced.
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
    \* Allocation catchup: age goes up while the eviction counter goes down, forcing reordering. Subject-ID goes from 5 to 3.
    /\ AllocateTopic(tp(2, 1, 16), {tp(2, 3, 2), tp(3, 0, 8), tp(4, 0, 4)}) = {tp(4, 1, 4), tp(3, 1, 8), tp(2, 1, 16)}

\**********************************************************************************************************************
\* Constructs a conflict-free topic sequence. This is meant for constructing the initial node state.
\* Per the definition of AllocateTopic, the ordering of the elements does not affect the final allocation.
\* Each hash can occur at most once.
RECURSIVE AllocateTopics(_, _)
AllocateTopics(new, topics) ==
    IF Cardinality(new) = 0 THEN topics
    ELSE LET t == CHOOSE x \in new : TRUE
         IN AllocateTopics(new \ {t}, AllocateTopic(t, topics))

Check_AllocateTopics ==
    LET tp(h, e, a) == [hash |-> h, evictions |-> e, age |-> a] IN
    AllocateTopics({tp(13, 0, 2), tp(3, 0, 8), tp(4, 0, 4)}, {}) = {tp(13, 2, 2), tp(4, 0, 4), tp(3, 0, 8)}

\**********************************************************************************************************************
\* Implementation of the divergence resolution rule with CRDT age merge.
AcceptGossip_Divergence(remote, topics) ==
    LET hash == remote.hash
        local == GetByHash(hash, topics)
        \* The serialization protocol floors the remote age to pow2 before transmission.
        new_age == Max(IF local # Nothing THEN local.age ELSE 0, FloorToPow2(remote.age))
    IN
    IF local # Nothing THEN
        IF local.evictions # remote.evictions /\ LeftWinsDivergence(remote, local)
        THEN AllocateTopic([hash |-> hash, evictions |-> remote.evictions, age |-> new_age], topics)
        ELSE              {[hash |-> hash, evictions |->  local.evictions, age |-> new_age]} \cup RemoveTopic(hash, topics)
    ELSE topics

Check_AcceptGossip_Divergence ==
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
AcceptGossip_Collision(remote, topics) ==
    LET local == GetBySubjectID(SubjectID(remote.hash, remote.evictions), topics)
    IN IF local # Nothing /\ LeftWinsCollision(remote, local)
    THEN AllocateTopic([hash |-> local.hash, evictions |-> local.evictions + 1, age |-> local.age], topics)
    ELSE topics

Check_AcceptGossip_Collision == 
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
Check_AcceptGossip == Check_AcceptGossip_Divergence /\ Check_AcceptGossip_Collision

\**********************************************************************************************************************
\* Model self-check.
Check == /\ Check_FirstMatch
         /\ Check_Get
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

\**********************************************************************************************************************
Nodes == 1..NodeCount

\* All possible initial topic states prior to local allocation and gossip.
InitialTopicSpace == {
    [hash |-> h, evictions |-> e, age |-> a]:
        h \in 0..(DistinctTopicCount-1),
        e \in 0..InitialEvictionMax,
        a \in 0..InitialAgeMax
}
\* All possible initial local topic sets per node.
\* We don't consider the case of zero local topics because this case is trivially correct.
InitialTopicSets == { S \in SUBSET InitialTopicSpace : Cardinality(S) \in 1..TopicsPerNodeMax }

(* --algorithm node
variables
  \* Prior to start, each node will allocate the following topics locally. Divergences may result.
  initial_topics \in [Nodes -> InitialTopicSets];
  \* Local topics per node; mutable state. Initial local allocation is performed prior to launch.
  topics = [n \in Nodes |-> AllocateTopics(initial_topics[n], {})];
  \* TODO FLATTEN AND SIMPLIFY!
  heartbeat_queue = [destination \in Nodes |-> [source \in Nodes |-> <<>>]];

define
  Invariant == TRUE
  AllProcDone == \A p \in Nodes: pc[p] = "Done"
  TerminationInvariant == AllProcDone => Check /\ Invariant
end define;

process pub \in Nodes
variable
    pub_dst = 1;
    pub_time = 0;
begin
  PubInit:
    pub_dst := 1;
  PubHeartbeat:
    while pub_dst <= NodeCount do
        if pub_dst # self /\ heartbeat_queue[pub_dst][self] = <<>> then
            with tp \in topics[self] do
                either heartbeat_queue[pub_dst][self] := Append(heartbeat_queue[pub_dst][self], tp);
                or skip;  \* MESSAGE LOSS
                end either;
            end with;
        end if;
        pub_dst := pub_dst + 1;
    end while;
    if pub_time < Duration then
        pub_time := pub_time + 1;
        goto PubHeartbeat;
    end if;
  PubFinal:
    if Debug then
        print heartbeat_queue;
    end if;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "cf21b14c" /\ chksum(tla) = "7fb4d324")
VARIABLES initial_topics, topics, heartbeat_queue, pc

(* define statement *)
Invariant == TRUE
AllProcDone == \A p \in Nodes: pc[p] = "Done"
TerminationInvariant == AllProcDone => Check /\ Invariant

VARIABLES pub_dst, pub_time

vars == << initial_topics, topics, heartbeat_queue, pc, pub_dst, pub_time >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ initial_topics \in [Nodes -> InitialTopicSets]
        /\ topics = [n \in Nodes |-> AllocateTopics(initial_topics[n], {})]
        /\ heartbeat_queue = [destination \in Nodes |-> [source \in Nodes |-> <<>>]]
        (* Process pub *)
        /\ pub_dst = [self \in Nodes |-> 1]
        /\ pub_time = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> "PubInit"]

PubInit(self) == /\ pc[self] = "PubInit"
                 /\ pub_dst' = [pub_dst EXCEPT ![self] = 1]
                 /\ pc' = [pc EXCEPT ![self] = "PubHeartbeat"]
                 /\ UNCHANGED << initial_topics, topics, heartbeat_queue, 
                                 pub_time >>

PubHeartbeat(self) == /\ pc[self] = "PubHeartbeat"
                      /\ IF pub_dst[self] <= NodeCount
                            THEN /\ IF pub_dst[self] # self /\ heartbeat_queue[pub_dst[self]][self] = <<>>
                                       THEN /\ \E tp \in topics[self]:
                                                 \/ /\ heartbeat_queue' = [heartbeat_queue EXCEPT ![pub_dst[self]][self] = Append(heartbeat_queue[pub_dst[self]][self], tp)]
                                                 \/ /\ TRUE
                                                    /\ UNCHANGED heartbeat_queue
                                       ELSE /\ TRUE
                                            /\ UNCHANGED heartbeat_queue
                                 /\ pub_dst' = [pub_dst EXCEPT ![self] = pub_dst[self] + 1]
                                 /\ pc' = [pc EXCEPT ![self] = "PubHeartbeat"]
                                 /\ UNCHANGED pub_time
                            ELSE /\ IF pub_time[self] < Duration
                                       THEN /\ pub_time' = [pub_time EXCEPT ![self] = pub_time[self] + 1]
                                            /\ pc' = [pc EXCEPT ![self] = "PubHeartbeat"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "PubFinal"]
                                            /\ UNCHANGED pub_time
                                 /\ UNCHANGED << heartbeat_queue, pub_dst >>
                      /\ UNCHANGED << initial_topics, topics >>

PubFinal(self) == /\ pc[self] = "PubFinal"
                  /\ IF Debug
                        THEN /\ PrintT(heartbeat_queue)
                        ELSE /\ TRUE
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << initial_topics, topics, heartbeat_queue, 
                                  pub_dst, pub_time >>

pub(self) == PubInit(self) \/ PubHeartbeat(self) \/ PubFinal(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: pub(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Jul 06 22:07:09 EEST 2025 by pavel
\* Created Sun Jun 22 15:55:20 EEST 2025 by pavel
