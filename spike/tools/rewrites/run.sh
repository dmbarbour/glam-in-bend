#!/bin/sh
# Builds spike/bench_rules.bend four ways and times each at k = 16, 17, 18
# (docs/plans/EvalSpike_2026-10-26.md, spike-node-layout):
#   A  the rule table, interpreted (the spike as it is)
#   B  dispatch on the kind pair, each rule passed as a constant
#   C  the workload's rules written by hand, in the table's order
#   D  C without the level assertions and fusion checks
#
#   spike/tools/rewrites/run.sh OUT    (OUT: a directory to build in)
set -eu
[ $# -eq 1 ] || { echo "usage: $0 OUT" >&2; exit 2; }
OUT=$1
T=$(cd "$(dirname "$0")" && pwd)
SPIKE=$(cd "$T/../.." && pwd)
for v in A B C D; do
  mkdir -p "$OUT/$v"
  cp "$SPIKE"/*.bend "$OUT/$v/"
  case $v in
    B) python3 -I "$T/apply.py" "$OUT/$v/net.bend" "$T/B.bend.txt" ;;
    C) python3 -I "$T/apply.py" "$OUT/$v/net.bend" "$T/C.bend.txt" ;;
    D) python3 -I "$T/apply.py" "$OUT/$v/net.bend" "$T/C.bend.txt"
       python3 -I "$T/D.py" "$OUT/$v/net.bend" ;;
  esac
  (cd "$OUT/$v" && bend bench_rules.bend -o bench >/dev/null)
done
for k in 16 17 18; do
  for v in A B C D; do
    for rep in 1 2 3; do
      echo "$v $("$SPIKE/../scripts/capped.sh" 3000 600 "$OUT/$v/bench" "$k")"
    done
  done
done
