# Model-based verification

## Usage

Download `tla2tools.jar` from <https://github.com/tlaplus/tlaplus/releases> and store it somewhere under `/opt`.

Use the `run.sh` script to run the PlusCal translator and the TLC model checker at once in CLI:

```sh
./run.sh CyphalTopics.tla
```

Utility modules can be evaluated using the same approach.

To edit the model, use VS Code with the recommended extensions. The TLA<sup>+</sup> extension also allows interactive model checking and limited REPLing. Be sure to enable font ligatures. The TLA<sup>+</sup> Toolbox IDE does not offer the best user experience so its use is not recommended.

To run a local REPL in CLI, say `java -cp tla2tools.jar tlc2.REPL`.

## TODO

- Add an option to run a reduced state space model quickly.
- Cleanup the duration/skew mechanics.
- Introduce liveness and temporal properties. Requires fairness.
  - Need a new operator for checking that the topic set is collision-free, divergence-free, and log-age-identical.
    We can call it `Converged`. Then, `<>[]Converged`.
- Dynamic gossip schedule.
- Prove that the topic with the higest log-age will never change its subject-ID.

## TLA<sup>+</sup> resources

- [Learn TLA<sup>+</sup>](https://learntla.com)
- [Cheatsheet](https://mbt.informal.systems/docs/tla_basics_tutorials/tla+cheatsheet.html)
- [Browser REPL](https://will62794.github.io/spectacle)

Articles by Hillel Wayne:

- [Modeling Message Queues in TLA+](https://www.hillelwayne.com/post/tla-messages/)
- [Weak and Strong Fairness](https://www.hillelwayne.com/post/fairness/)
- [Modeling Adversaries with TLA+](https://www.hillelwayne.com/post/adversaries/#fnref:module)
- [TLA+ Action Properties](https://www.hillelwayne.com/post/action-properties/)
