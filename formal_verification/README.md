# Model-based formal verification

All operations defined on topics are extracted into `Core.tla`, where the operations are implemented as
pure functions (called "operators" in TLA+ terminology).
This module includes both basic things like the subject-ID mapping function and CRDT arbitration
up to the high-level functions `AllocateTopic` and `AcceptGossip`.
To understand the protocol, start with this module; consider it to be also its formal specification,
which can be relied on when working on new implementations.

Complete verification models are defined in `CyphalTopics_*.tla`.
All of them model the same algorithm using different approaches.

## Usage

Download `tla2tools.jar` from <https://github.com/tlaplus/tlaplus/releases> and store it somewhere under `/opt`.

Use the `run.sh` helper script to run the PlusCal translator and the TLC model checker at once in CLI:

```sh
./run.sh CyphalTopics_1.tla
```

Other modules can be evaluated using the same script as well.

To edit the model, use VS Code with the recommended extensions. The TLA<sup>+</sup> extension also allows interactive model checking and limited REPLing. Be sure to enable font ligatures. The TLA<sup>+</sup> Toolbox IDE does not offer the best user experience so its use is not recommended.

To run a local REPL in CLI, say `java -cp tla2tools.jar tlc2.REPL`.

## TODO

Add a temporal property that each topic of each node has a non-decreasing age.

Improve performance:
- Use [symmetry sets](https://learntla.com/topics/optimization.html#use-symmetry-sets).
- Reduce the number of labels in the processes.

Prove that the topic with the highest log-age will never change its subject-ID.
We need to handle the case of one topic overtaking another in age.

## Issues discovered in the original protocol design

### Nonuniform ageing rate increases the worst-case convergence time

The variable aging rate proposed in the original RFC, where the topic age increases faster with higher traffic, was found to be a potential cause of ping-pong eviction, slowing down convergence. While it does not *prevent* convergence, it is still undesirable. Slow progress issues can be resurfaced by artificially limiting the maximum number of steps the network is allowed to take before requiring convergence. In this case, TLA+ will find counterexamples when the network takes longer to converge than the allotted time, and the corresponding state traces will reveal the specific conditions.

Given a simple subject-ID function `SubjectID(hash, evictions) == (hash + evictions) % 10` and two nodes with the following initial topic states (hash, evictions, age):

1. (1, 0, 0), (11, 1, 0). The second topic has evictions = 1 to avoid conflict with local topic 1, which wins arbitration due to the lower hash value.
2. (2, 0, 0), (11, 0, 0). Notice the initial divergence (topic 11 maps to subject-ID 1 while in the other node it maps to 2) and the two collisions on subject-IDs 1 and 2.

After some time, the age counters are increased non-uniformly as follows:

1. (1, 0, 1), (11, 1, 2). Notice topic 1 lagging behind.
2. (2, 0, 2), (11, 0, 2).

Node 2 gossips topic 11. Node 1 receives the gossip, topic 1 loses arbitration due to lower $\lfloor{} \log_2 \text{age} \rfloor{}$. The divergence (topic 11 has distinct eviction counters) is ignored because the local replica of 11 wins arbitration.

1. (1, 2, 1), (11, 1, 2). Topic 1 was evicted twice, now occupying subject-ID 3.
2. (2, 0, 2), (11, 0, 2).

Some time passed. The topics have aged nonuniformly, but their log-ages are the same, so they compare equal.

1. (1, 2, 2), (11, 1, 2).
2. (2, 0, 2), (11, 0, 3).

Node 1 gossips topic 11. Node 2 loses the divergence arbitration and attempts to synchronize its eviction counter, which causes another collision.

1. (1, 2, 2), (11, 1, 2).
2. (2, 0, 2), (11, 2, 3). Topic 11 was evicted again due to losing arbitration to topic 2. It is now colliding with topic 1, but neither node is aware.

Some time passed.

1. (1, 2, 2), (11, 1, 3). Topic 11 aged.
2. (2, 0, 2), (11, 2, 3).

Node 1 gossips topic 1. Node 2 discovers the collision and moves topic 11 again, which loses due to the greater hash.

1. (1, 2, 2), (11, 1, 3).
2. (2, 0, 2), (11, 3, 3).

It will take a few more exchanges for the nodes to finally agree on the following mapping:

1. (1, 2, ?), (11, 4, ?).
2. (2, 2, ?), (11, 4, ?).

The protocol may temporarily fail to converge until the aging rate differential across nodes sharing the affected topics falls below the rate of $\lfloor{} \log_2 \text{age} \rfloor{}$ increment. To improve its performance, all involved nodes should attempt to increment the ages of their local topic replicas at approximately the same rate. Even low-cost microcontrollers clocked from an RC oscillator can easily achieve the optimal accuracy without any additional measures.

A few extra evictions may not seem like a big deal, but given the finite subject-ID space they may cause a chain reaction, as a single evicted topic may step on a subject-ID allocation belonging to a remote node, potentially disrupting a large number of participants. This is why evictions must be minimized; in particular, upon detection of a collision, a node must not attempt to repair it if it observes that the remote node causing the collision will have to increase its eviction count to catch up with the local replica.

### Collisions caused by divergent topics should be ignored unless the local node loses arbitration

Consider the following initial state:

1. (1, 2, 4), (11, 1, 4).
2. (2, 0, 3), (11, 3, 4).

Node 1 gossips topic 11, currently occupying subject-ID 2. Node 2 wins the divergence arbitration because its eviction counter on topic 11 is greater, so its local replica of 11 is not altered. The correct action here is to ignore the gossip completely. The original protocol design, however, called for the collision resolution on the received gossip as well, which alters topic 2, as it is currently occupying the same subject-ID of 2, and its log-age is lower:

1. (1, 2, 4), (11, 1, 4).
2. (2, 1, 3), (11, 3, 4). Topic 2 was evicted unjustly and is now colliding with topic 1, but neither node is aware yet!

Eventually, node 2 will gossip its replica of topic 11, causing node 1 to catch up:

1. (1, 2, 4), (11, 3, 4).
2. (2, 1, 3), (11, 3, 4).

This state is suboptimal because now the lower subject-IDs remain unused purely due to poor convergence properties of the algorithm. The correct course of action would have been to ignore the collision on subject 2, which would have resulted in the following final configuration that is both conflict-free and has a higher subject-ID allocation density:

1. (1, 2, 4), (11, 3, 4).
2. (2, 0, 3), (11, 3, 4).

## TLA<sup>+</sup> resources

- [Learn TLA<sup>+</sup>](https://learntla.com)
- [Cheatsheet](https://mbt.informal.systems/docs/tla_basics_tutorials/tla+cheatsheet.html)
- [Browser REPL](https://will62794.github.io/spectacle)

Articles by Hillel Wayne:

- [Modeling Message Queues in TLA+](https://www.hillelwayne.com/post/tla-messages/)
- [Weak and Strong Fairness](https://www.hillelwayne.com/post/fairness/)
- [Modeling Adversaries with TLA+](https://www.hillelwayne.com/post/adversaries/#fnref:module)
- [TLA+ Action Properties](https://www.hillelwayne.com/post/action-properties/)
