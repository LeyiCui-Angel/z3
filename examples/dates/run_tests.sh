#!/bin/bash
# Run the date theory tests under both solver pipelines.
#   ./run_tests.sh [path-to-z3]
Z3=${1:-../../build/z3}
DIR=$(dirname "$0")
fail=0
for f in "$DIR"/t*.smt2; do
    echo "=== $(basename "$f") ==="
    echo "--- legacy smt core:"
    timeout 60 "$Z3" "$f" || { echo "FAILED/TIMEOUT (legacy)"; fail=1; }
    echo "--- sat/euf core:"
    timeout 60 "$Z3" sat.euf=true tactic.default_tactic=sat "$f" || { echo "FAILED/TIMEOUT (euf)"; fail=1; }
done
exit $fail
