#!/bin/bash

set -euo pipefail

ROOT="$(dirname "$0")"
cd "$ROOT/build"
./cobble build

OUTPUT=$(mktemp)
trap '{ rm -f -- "$OUTPUT"; }' EXIT

FAILURES=
for t in $(find latest -name "*-bin"); do
    echo "--- running $t"
    if $t > $OUTPUT && grep -q PASS $OUTPUT ; then
        echo "(pass)"
    else
        echo "FAIL: status $?"
        echo "output:"
        cat $OUTPUT
        FAILURES="$t $FAILURES"
    fi
done

if [ "$FAILURES" = "" ]; then
    echo "--- all tests passed ---"
else
    echo "SOME TESTS FAILED: $FAILURES"
fi
