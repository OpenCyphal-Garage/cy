------------------------------ MODULE CyphalTopics ------------------------------
\* Pavel Kirienko <pavel@opencyphal.org>, MIT license

EXTENDS Integers, TLC, Sequences, FiniteSets, Utils, TopicOps

CONSTANT Debug
ASSUME Debug \in BOOLEAN

CONSTANT NodeCount, TopicHashes, TopicsPerNodeMax, InitialEvictionMax, InitialAgeMax
ASSUME NodeCount \in Nat /\ NodeCount > 0
ASSUME TopicsPerNodeMax \in Nat /\ TopicsPerNodeMax > 0
ASSUME \A h \in TopicHashes: h \in Nat
ASSUME InitialEvictionMax \in Nat
ASSUME InitialAgeMax \in Nat

CONSTANT Duration, MaxTimeSkew
ASSUME Duration \in Nat /\ Duration > 1
ASSUME MaxTimeSkew \in Nat

Check == Check_Utils /\ Check_TopicOps

Nodes == 1..NodeCount

\* All possible initial topic states prior to local allocation and gossip.
InitialTopicSpace == {
    [hash |-> h, evictions |-> e, age |-> a]:
        h \in TopicHashes,
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
    fabric = [destination \in Nodes |-> <<>>];

    \* Topic gossip ordering per node. Each ordering contains a set of permutations of topic hashes.
    \* The function type is:
    \*      node -> {sequence_1, sequence_2, ..., sequence_n}
    gossip_order_sets = [ n \in Nodes |-> SetToSeqs({ t.hash : t \in topics[n] }) ];
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
    PubProcs == { n + 1000 : n \in Nodes }
    AllPubDone == \A p \in PubProcs : pc[p] = "Done"
    Silent == fabric = [n \in DOMAIN fabric |-> <<>>]

    AllProcDone == \A p \in DOMAIN pc: pc[p] = "Done"

    NoDivergences  == AllProcDone => {} = FindDivergent(topics)
    NoCollisions   == AllProcDone => {} = FindCollisions(topics)
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
                await fabric[pub_dst] = <<>>;
                fabric[pub_dst] := Append(fabric[pub_dst], pub_gossip);
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
            skip;\*print <<"FINAL TOPICS", node_id, topics[node_id]>>;
        end if;
end process;

\* GOSSIP SUBSCRIBER PROCESS.
process sub \in {n + 2000 : n \in Nodes}
variable
    node_id = self - 2000;
begin
    SubMain:
        while ~AllPubDone \/ ~Silent do
            if fabric[node_id] # <<>> then
                with gossip = Head(fabric[node_id]) do
                    fabric[node_id] := Tail(fabric[node_id]);
                    topics[node_id] := AcceptGossip(gossip, topics[node_id]);
                    \* Update the schedule if the local replica won to speedup collision/divergence repair:
                    \* gossip_order[node_id] := SeqWithout(gossip_order[node_id], gossip.hash) \o <<gossip.hash>>
                end with;
            end if;
        end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "9c6666b5" /\ chksum(tla) = "1e949ccd")
\* Process variable node_id of process pub at line 79 col 5 changed to node_id_
CONSTANT defaultInitValue
VARIABLES initial_topics, topics, time, fabric, gossip_order_sets,
          gossip_order, pc

(* define statement *)
PubProcs == { n + 1000 : n \in Nodes }
AllPubDone == \A p \in PubProcs : pc[p] = "Done"
Silent == fabric = [n \in DOMAIN fabric |-> <<>>]

AllProcDone == \A p \in DOMAIN pc: pc[p] = "Done"

NoDivergences  == AllProcDone => {} = FindDivergent(topics)
NoCollisions   == AllProcDone => {} = FindCollisions(topics)

VARIABLES node_id_, pub_dst, pub_gossip, node_id

vars == << initial_topics, topics, time, fabric, gossip_order_sets,
           gossip_order, pc, node_id_, pub_dst, pub_gossip, node_id >>

ProcSet == ({n + 1000 : n \in Nodes}) \cup ({n + 2000 : n \in Nodes})

Init == (* Global variables *)
        /\ initial_topics \in [Nodes -> InitialTopicSets]
        /\ topics = [n \in Nodes |-> AllocateTopics(initial_topics[n], {})]
        /\ time = [n \in Nodes |-> 0]
        /\ fabric = [destination \in Nodes |-> <<>>]
        /\ gossip_order_sets = [ n \in Nodes |-> SetToSeqs({ t.hash : t \in topics[n] }) ]
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
                 /\ UNCHANGED << initial_topics, topics, time, fabric,
                                 gossip_order_sets, node_id_, node_id >>

PubAge(self) == /\ pc[self] = "PubAge"
                /\ pub_gossip' = [pub_gossip EXCEPT ![self].age = pub_gossip[self].age + 1]
                /\ topics' = [topics EXCEPT ![node_id_[self]] = ReplaceTopic(pub_gossip'[self], topics[node_id_[self]])]
                /\ pc' = [pc EXCEPT ![self] = "PubLoop"]
                /\ UNCHANGED << initial_topics, time, fabric,
                                gossip_order_sets, gossip_order, node_id_,
                                pub_dst, node_id >>

PubLoop(self) == /\ pc[self] = "PubLoop"
                 /\ IF pub_dst[self] <= NodeCount
                       THEN /\ IF pub_dst[self] # node_id_[self]
                                  THEN /\ fabric[pub_dst[self]] = <<>>
                                       /\ fabric' = [fabric EXCEPT ![pub_dst[self]] = Append(fabric[pub_dst[self]], pub_gossip[self])]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED fabric
                            /\ pub_dst' = [pub_dst EXCEPT ![self] = pub_dst[self] + 1]
                            /\ pc' = [pc EXCEPT ![self] = "PubLoop"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "PubTime"]
                            /\ UNCHANGED << fabric, pub_dst >>
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
                 /\ UNCHANGED << initial_topics, topics, fabric,
                                 gossip_order_sets, gossip_order, node_id_,
                                 pub_dst, pub_gossip, node_id >>

PubFinal(self) == /\ pc[self] = "PubFinal"
                  /\ IF Min(Range(time)) >= Duration /\ Debug
                        THEN /\ TRUE
                        ELSE /\ TRUE
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << initial_topics, topics, time, fabric,
                                  gossip_order_sets, gossip_order, node_id_,
                                  pub_dst, pub_gossip, node_id >>

pub(self) == PubMain(self) \/ PubAge(self) \/ PubLoop(self)
                \/ PubTime(self) \/ PubFinal(self)

SubMain(self) == /\ pc[self] = "SubMain"
                 /\ IF ~AllPubDone \/ ~Silent
                       THEN /\ IF fabric[node_id[self]] # <<>>
                                  THEN /\ LET gossip == Head(fabric[node_id[self]]) IN
                                            /\ fabric' = [fabric EXCEPT ![node_id[self]] = Tail(fabric[node_id[self]])]
                                            /\ topics' = [topics EXCEPT ![node_id[self]] = AcceptGossip(gossip, topics[node_id[self]])]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << topics, fabric >>
                            /\ pc' = [pc EXCEPT ![self] = "SubMain"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << topics, fabric >>
                 /\ UNCHANGED << initial_topics, time, gossip_order_sets,
                                 gossip_order, node_id_, pub_dst, pub_gossip,
                                 node_id >>

sub(self) == SubMain(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {n + 1000 : n \in Nodes}: pub(self))
           \/ (\E self \in {n + 2000 : n \in Nodes}: sub(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

========================================================================================================================
