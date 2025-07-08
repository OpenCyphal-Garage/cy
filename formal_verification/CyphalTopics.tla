------------------------------ MODULE CyphalTopics ------------------------------

EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANT Nothing, Debug
ASSUME Debug \in BOOLEAN

CONSTANT NodeCount, TopicsPerNodeMax, DistinctTopicCount, InitialEvictionMax, InitialAgeMax
ASSUME NodeCount \in Nat /\ NodeCount > 0
ASSUME TopicsPerNodeMax \in Nat /\ TopicsPerNodeMax > 0 /\ TopicsPerNodeMax <= DistinctTopicCount
ASSUME DistinctTopicCount \in Nat /\ DistinctTopicCount > 0
ASSUME InitialEvictionMax \in Nat
ASSUME InitialAgeMax \in Nat

CONSTANT Duration, MaxTimeSkew
ASSUME Duration \in Nat /\ Duration > 1
ASSUME MaxTimeSkew \in Nat

\**********************************************************************************************************************
\* General utilities and helpers.

PrintVal(id, exp) == Print(<<id, exp>>, TRUE)

Range(f) == { f[x] : x \in DOMAIN f }

Min(S) == CHOOSE s \in S : \A t \in S : s <= t

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

SetToSeqs(S) == LET D == 1..Cardinality(S) IN { f \in [D -> S] : \A i,j \in D : i # j => f[i] # f[j] }

\* A new sequence that contains zero needles.
SeqWithout(haystack, needle) == SelectSeq(haystack, LAMBDA x: x # needle)

Check_SeqWithout == SeqWithout(<<>>, 1) = <<>>
                 /\ SeqWithout(<<1, 2, 3>>, 2) = <<1, 3>>
                 /\ SeqWithout(<<1, 2, 3>>, 4) = <<1, 2, 3>>

\* <<1, 2, 3>> ==> <<2, 3, 1>>
SeqRotLeft(seq) == IF Len(seq) > 0 THEN Tail(seq) \o <<Head(seq)>> ELSE seq

\* Converts {<<k1, v1>>, <<k2, v2>>, ...} into a function [k |-> v]. Keys must be unique.
FunFromTupleSet(S) == [
    k \in {p[1] : p \in S} |-> CHOOSE v \in {r[2] : r \in S} : <<k, v>> \in S
]
Check_FunFromTupleSet == FunFromTupleSet({<<1, 11>>, <<2, 12>>, <<3, 13>>})[1] = 11
                      /\ FunFromTupleSet({<<1, 11>>, <<2, 12>>, <<3, 13>>})[2] = 12
                      /\ FunFromTupleSet({<<1, 11>>, <<2, 12>>, <<3, 13>>})[3] = 13

\**********************************************************************************************************************
\* The core assumptions include that the hash function is perfect (no hash collisions) and the counters never overflow.
Topic == [hash : Nat, evictions : Nat, age : Nat]

\* Given a set of topics, evaluates to a set of their hashes.
HashesOf(topics) == { t.hash : t \in topics }

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

Check_AllocateTopic ==
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

\**********************************************************************************************************************
\* Constructs a conflict-free topic set. This is meant for constructing the initial node state.
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
        THEN AllocateTopic([hash|->hash, evictions|->remote.evictions, age|->new_age], topics)
        ELSE              {[hash|->hash, evictions|-> local.evictions, age|->new_age]} \cup RemoveTopic(hash, topics)
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
\* Divergent allocation detector operating on a function node_id -> {topic_0, topic_1, ..., topic_n}
\* A divergent allocation occurs when topic records with the same hash have distinct eviction counters.
\* If no divergences are found, the result is an empty set.
FindDivergent(node_topics) ==
    LET hashes == { t.hash : t \in UNION Range(node_topics) }
        flat == { [hash |-> t.hash, evictions |-> t.evictions] : t \in UNION Range(node_topics) }
    IN { h \in hashes : Cardinality({ s \in flat : s.hash = h }) > 1 }

Check_FindDivergent ==
    LET tp(h, e) == [hash |-> h, evictions |-> e, age |-> 0] IN
    /\ FindDivergent(1 :> {tp(4, 0), tp(2, 0)} @@ 2 :> {tp(3, 0), tp(6, 1)}) = {}
    /\ FindDivergent(1 :> {tp(4, 0), tp(2, 0)} @@ 2 :> {tp(3, 0), tp(2, 1)}) = {2}

\**********************************************************************************************************************
\* Allocation collision detector operating on a function node_id -> {topic_0, topic_1, ..., topic_n}
\* A collision occurs when topic records with distinct hashes have identical subject-ID.
\* If no collisions are found, the result is an empty set.
FindCollisions(node_topics) ==
    LET flat == { [hash |-> t.hash, subject_id |-> SubjectID(t.hash, t.evictions)] : t \in UNION Range(node_topics) }
        subject_ids == { t.subject_id : t \in flat }
    IN { s \in subject_ids : Cardinality({ t \in flat : t.subject_id = s }) > 1 }

Check_FindCollisions ==
    LET tp(h, e) == [hash |-> h, evictions |-> e, age |-> 0] IN
    /\ FindCollisions(1 :> {tp(2, 0), tp(3, 0)} @@ 2 :> {tp(3, 0), tp(4, 0)}) = {}
    /\ FindCollisions(1 :> {tp(2, 0), tp(3, 1)} @@ 2 :> {tp(3, 0), tp(4, 0)}) = {4}
    /\ FindCollisions(1 :> {tp(2, 2), tp(3, 1)} @@ 2 :> {tp(3, 0), tp(4, 0)}) = {4}
    /\ FindCollisions(1 :> {tp(2, 1), tp(3, 3)} @@ 2 :> {tp(3, 0), tp(4, 2)}) = {3, 6}

\**********************************************************************************************************************
\* Model self-check.
Check == /\ Check_FirstMatch
         /\ Check_Get
         /\ Check_SeqWithout
         /\ Check_FunFromTupleSet
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
    
    \* Each node has its own time model that doesn't have to be in sync with the others.
    time = [n \in Nodes |-> 0];

    \* Each node has an independent queue of incoming gossips.
    heartbeat_queue = [destination \in Nodes |-> <<>>];

    \* Topic gossip ordering per node. Each ordering contains a set of permutations of topic hashes.
    \* The function type is:
    \*      node -> {sequence_1, sequence_2, ..., sequence_n}
    gossip_order_sets = [ n \in Nodes |-> SetToSeqs(HashesOf(topics[n])) ];
    \* We cannot use the above form directly; first, we need to transform it into a form that can be
    \* used with the nondeterministic selection form \in:
    \*      { node->sequence_0, node->sequence_1, ..., node->sequence_n }
    gossip_order \in {
        FunFromTupleSet(m) : m \in {
            S \in SUBSET (
                UNION {{ <<n, g>> : g \in gossip_order_sets[n] } : n \in Nodes}
            ) : /\ Cardinality({Head(s) : s \in S}) = Cardinality(Nodes)
                /\ Cardinality(S) = Cardinality(Nodes)
        }
    }

define
    NoDivergences == {} = FindDivergent(topics)
    NoCollisions == {} = FindCollisions(topics)
    AllProcDone == \A p \in DOMAIN pc: pc[p] = "Done"
    FinalInvariant == AllProcDone => Check /\ NoDivergences /\ NoCollisions
end define;

\* PERIODIC GOSSIP PUBLISHER PROCESS.
process pub \in {n + 1000 : n \in Nodes}
variable
    node_id = self - 1000;
    pub_dst;
    pub_gossip;
begin
  PubMain:
    pub_dst := 1;
    pub_gossip := GetByHash(Head(gossip_order[node_id]), topics[node_id]);
    gossip_order[node_id] := SeqRotLeft(gossip_order[node_id]);

  PubAge:
    pub_gossip.age := pub_gossip.age + 1;
    topics[node_id] := ReplaceTopic(pub_gossip, topics[node_id]);

  PubLoop:
    while pub_dst <= NodeCount do
        if pub_dst # node_id then
            await heartbeat_queue[pub_dst] = <<>>;
            heartbeat_queue[pub_dst] := Append(heartbeat_queue[pub_dst], pub_gossip);
        end if;
        pub_dst := pub_dst + 1;
    end while;

  PubTime:
    await time[node_id] - Min(Range(time)) < MaxTimeSkew;
    if time[node_id] < Duration then
        time[node_id] := time[node_id] + 1;
        goto PubMain;
    end if;
  
  PubFinal:
    if Min(Range(time)) >= Duration /\ Debug then
        skip; \* print <<"FINAL TOPICS", topics>>;
    end if;
end process;

\* HEARTBEAT SUBSCRIBER PROCESS.
process sub \in {n + 2000 : n \in Nodes}
variable
    node_id = self - 2000;
begin
  SubMain:
    while TRUE do
        if heartbeat_queue[node_id] # <<>> then
            with gossip = Head(heartbeat_queue[node_id]) do
                heartbeat_queue[node_id] := Tail(heartbeat_queue[node_id]);
                topics[node_id] := AcceptGossip(gossip, topics[node_id])
                \* Here, we could update the schedule if the local replica won to speedup collision/divergence repair:
                \* gossip_order[node_id] := SeqWithout(gossip_order[node_id], gossip.hash) \o <<gossip.hash>>
            end with;
        end if;
    end while;
end process;

end algorithm; *) \****************************************************************************************************
\* BEGIN TRANSLATION (chksum(pcal) = "6fb1cc7d" /\ chksum(tla) = "91764bdf")
\* Process variable node_id of process pub at line 397 col 5 changed to node_id_
CONSTANT defaultInitValue
VARIABLES initial_topics, topics, time, heartbeat_queue, gossip_order_sets, 
          gossip_order, pc

(* define statement *)
NoDivergences == {} = FindDivergent(topics)
NoCollisions == {} = FindCollisions(topics)
AllProcDone == \A p \in DOMAIN pc: pc[p] = "Done"
FinalInvariant == AllProcDone => Check /\ NoDivergences /\ NoCollisions

VARIABLES node_id_, pub_dst, pub_gossip, node_id

vars == << initial_topics, topics, time, heartbeat_queue, gossip_order_sets, 
           gossip_order, pc, node_id_, pub_dst, pub_gossip, node_id >>

ProcSet == ({n + 1000 : n \in Nodes}) \cup ({n + 2000 : n \in Nodes})

Init == (* Global variables *)
        /\ initial_topics \in [Nodes -> InitialTopicSets]
        /\ topics = [n \in Nodes |-> AllocateTopics(initial_topics[n], {})]
        /\ time = [n \in Nodes |-> 0]
        /\ heartbeat_queue = [destination \in Nodes |-> <<>>]
        /\ gossip_order_sets = [ n \in Nodes |-> SetToSeqs(HashesOf(topics[n])) ]
        /\ gossip_order \in                  {
                                FunFromTupleSet(m) : m \in {
                                    S \in SUBSET (
                                        UNION {{ <<n, g>> : g \in gossip_order_sets[n] } : n \in Nodes}
                                    ) : /\ Cardinality({Head(s) : s \in S}) = Cardinality(Nodes)
                                        /\ Cardinality(S) = Cardinality(Nodes)
                                }
                            }
        (* Process pub *)
        /\ node_id_ = [self \in {n + 1000 : n \in Nodes} |-> self - 1000]
        /\ pub_dst = [self \in {n + 1000 : n \in Nodes} |-> defaultInitValue]
        /\ pub_gossip = [self \in {n + 1000 : n \in Nodes} |-> defaultInitValue]
        (* Process sub *)
        /\ node_id = [self \in {n + 2000 : n \in Nodes} |-> self - 2000]
        /\ pc = [self \in ProcSet |-> CASE self \in {n + 1000 : n \in Nodes} -> "PubMain"
                                        [] self \in {n + 2000 : n \in Nodes} -> "SubMain"]

PubMain(self) == /\ pc[self] = "PubMain"
                 /\ pub_dst' = [pub_dst EXCEPT ![self] = 1]
                 /\ pub_gossip' = [pub_gossip EXCEPT ![self] = GetByHash(Head(gossip_order[node_id_[self]]), topics[node_id_[self]])]
                 /\ gossip_order' = [gossip_order EXCEPT ![node_id_[self]] = SeqRotLeft(gossip_order[node_id_[self]])]
                 /\ pc' = [pc EXCEPT ![self] = "PubAge"]
                 /\ UNCHANGED << initial_topics, topics, time, heartbeat_queue, 
                                 gossip_order_sets, node_id_, node_id >>

PubAge(self) == /\ pc[self] = "PubAge"
                /\ pub_gossip' = [pub_gossip EXCEPT ![self].age = pub_gossip[self].age + 1]
                /\ topics' = [topics EXCEPT ![node_id_[self]] = ReplaceTopic(pub_gossip'[self], topics[node_id_[self]])]
                /\ pc' = [pc EXCEPT ![self] = "PubLoop"]
                /\ UNCHANGED << initial_topics, time, heartbeat_queue, 
                                gossip_order_sets, gossip_order, node_id_, 
                                pub_dst, node_id >>

PubLoop(self) == /\ pc[self] = "PubLoop"
                 /\ IF pub_dst[self] <= NodeCount
                       THEN /\ IF pub_dst[self] # node_id_[self]
                                  THEN /\ heartbeat_queue[pub_dst[self]] = <<>>
                                       /\ heartbeat_queue' = [heartbeat_queue EXCEPT ![pub_dst[self]] = Append(heartbeat_queue[pub_dst[self]], pub_gossip[self])]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED heartbeat_queue
                            /\ pub_dst' = [pub_dst EXCEPT ![self] = pub_dst[self] + 1]
                            /\ pc' = [pc EXCEPT ![self] = "PubLoop"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "PubTime"]
                            /\ UNCHANGED << heartbeat_queue, pub_dst >>
                 /\ UNCHANGED << initial_topics, topics, time, 
                                 gossip_order_sets, gossip_order, node_id_, 
                                 pub_gossip, node_id >>

PubTime(self) == /\ pc[self] = "PubTime"
                 /\ time[node_id_[self]] - Min(Range(time)) < MaxTimeSkew
                 /\ IF time[node_id_[self]] < Duration
                       THEN /\ time' = [time EXCEPT ![node_id_[self]] = time[node_id_[self]] + 1]
                            /\ pc' = [pc EXCEPT ![self] = "PubMain"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "PubFinal"]
                            /\ time' = time
                 /\ UNCHANGED << initial_topics, topics, heartbeat_queue, 
                                 gossip_order_sets, gossip_order, node_id_, 
                                 pub_dst, pub_gossip, node_id >>

PubFinal(self) == /\ pc[self] = "PubFinal"
                  /\ IF Min(Range(time)) >= Duration /\ Debug
                        THEN /\ TRUE
                        ELSE /\ TRUE
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << initial_topics, topics, time, 
                                  heartbeat_queue, gossip_order_sets, 
                                  gossip_order, node_id_, pub_dst, pub_gossip, 
                                  node_id >>

pub(self) == PubMain(self) \/ PubAge(self) \/ PubLoop(self)
                \/ PubTime(self) \/ PubFinal(self)

SubMain(self) == /\ pc[self] = "SubMain"
                 /\ IF heartbeat_queue[node_id[self]] # <<>>
                       THEN /\ LET gossip == Head(heartbeat_queue[node_id[self]]) IN
                                 /\ heartbeat_queue' = [heartbeat_queue EXCEPT ![node_id[self]] = Tail(heartbeat_queue[node_id[self]])]
                                 /\ topics' = [topics EXCEPT ![node_id[self]] = AcceptGossip(gossip, topics[node_id[self]])]
                       ELSE /\ TRUE
                            /\ UNCHANGED << topics, heartbeat_queue >>
                 /\ pc' = [pc EXCEPT ![self] = "SubMain"]
                 /\ UNCHANGED << initial_topics, time, gossip_order_sets, 
                                 gossip_order, node_id_, pub_dst, pub_gossip, 
                                 node_id >>

sub(self) == SubMain(self)

Next == (\E self \in {n + 1000 : n \in Nodes}: pub(self))
           \/ (\E self \in {n + 2000 : n \in Nodes}: sub(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
