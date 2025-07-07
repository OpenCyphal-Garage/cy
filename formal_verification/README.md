# Formal verification

Download `tla2tools.jar` from <https://github.com/tlaplus/tlaplus/releases> and store it somewhere under `/opt`.

Use the `run.sh` script to run the PlusCal translator and the TLC model checker at once:

```sh
./run.sh CyphalTopics.tla
```

To run a local REPL, say `java -cp tla2tools.jar tlc2.REPL`. You can also use <https://will62794.github.io/spectacle> to the same end.
