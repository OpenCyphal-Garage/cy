#!/bin/sh
# A trivial helper for running PlusCal translator and TLC in a single command.
# Invoke it as:
#   ./run.sh MySpec.tla

src=$1

die() {
    echo "$@" 1>&2
    exit 1
}

if [ -z "$tla2tools" ]; then
    tla2tools=$(find /opt -type f -name 'tla2tools.jar' -print -quit)
fi
[ -n "$tla2tools" ] || die "tla2tools.jar not found"
echo "Using $tla2tools"

[ -n "$src" ] || die "Source file not specified"

if grep -q -- '--algorithm' "$src"; then
    java -cp "$tla2tools" pcal.trans "$src" || die "PlusCal translation failed"
else
    echo "No “--algorithm” directive found -- skipping PlusCal translation"
fi

# https://learntla.com/topics/cli.html
java -XX:+UseParallelGC -jar "$tla2tools" -workers auto -fpmem 0.8 $src || die "TLA+ failed"
