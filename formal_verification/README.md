# Model-based formal verification

All operations defined on topics are extracted into `Core.tla`, where the operations are implemented as
pure functions (called "operators" in TLA+ terminology).
This module includes both basic things like the subject-ID mapping function and CRDT arbitration
up to the high-level functions `AllocateTopic` and `AcceptGossip`.
To understand the protocol, start with this module; consider it to be also its formal specification,
which can be relied on when working on new implementations.

Complete verification models are defined in `CyphalTopics_*.tla`.
All of them model the same algorithm using different approaches.

## TODO

Add a temporal property that each topic of each node has a non-decreasing age.

Improve performance:
- Use [symmetry sets](https://learntla.com/topics/optimization.html#use-symmetry-sets).
- Reduce the number of labels in the processes.

Introduce liveness and temporal properties. Requires fairness.
Need a new operator for checking that the topic set is collision-free, divergence-free, and log-age-identical.
We can call it `Converged`. Then, `<>[]Converged`.

Prove that the topic with the higest log-age will never change its subject-ID.
We need to handle the case of one topic overtaking another in age.

## Usage

Download `tla2tools.jar` from <https://github.com/tlaplus/tlaplus/releases> and store it somewhere under `/opt`.

Use the `run.sh` script to run the PlusCal translator and the TLC model checker at once in CLI:

```sh
./run.sh CyphalTopics_1.tla
```

The utility modules can be evaluated using the same script as well.

To edit the model, use VS Code with the recommended extensions. The TLA<sup>+</sup> extension also allows interactive model checking and limited REPLing. Be sure to enable font ligatures. The TLA<sup>+</sup> Toolbox IDE does not offer the best user experience so its use is not recommended.

To run a local REPL in CLI, say `java -cp tla2tools.jar tlc2.REPL`.

## TLA<sup>+</sup> resources

- [Learn TLA<sup>+</sup>](https://learntla.com)
- [Cheatsheet](https://mbt.informal.systems/docs/tla_basics_tutorials/tla+cheatsheet.html)
- [Browser REPL](https://will62794.github.io/spectacle)

Articles by Hillel Wayne:

- [Modeling Message Queues in TLA+](https://www.hillelwayne.com/post/tla-messages/)
- [Weak and Strong Fairness](https://www.hillelwayne.com/post/fairness/)
- [Modeling Adversaries with TLA+](https://www.hillelwayne.com/post/adversaries/#fnref:module)
- [TLA+ Action Properties](https://www.hillelwayne.com/post/action-properties/)
