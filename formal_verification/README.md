# Formal verification

Download `tla2tools.jar` from <https://github.com/tlaplus/tlaplus/releases> and store it somewhere under `/opt`.

Use the `run.sh` script to run the PlusCal translator and the TLC model checker at once in CLI:

```sh
./run.sh CyphalTopics.tla
```

To edit the model, use VS Code with the recommended extensions. The TLA+ extension also allows interactive model checking and limited REPLing.

To run a local REPL in CLI, say `java -cp tla2tools.jar tlc2.REPL`. You can also use <https://will62794.github.io/spectacle> to the same end.
