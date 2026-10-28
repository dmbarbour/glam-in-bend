#!/bin/sh
# The kernel's differential test on random terms (terms.py --kernel): each
# ending, `succ 0`, `(plus 1) 0` and `(fma 1 1) 0`, lowered with levels and
# with static labels, three seeds of COUNT terms. Every term runs through
# the spike, the kernel's interpreted table, its generated rewrites and on
# demand, against the Python evaluator's value; each set is built and run
# under scripts/capped.sh, and every term's values and counts recorded in
# the analysis store (scripts/results.py) under one run, whose summary is
# printed at the end.
#
#   spike/tools/differential.sh OUT [COUNT [NOTE]]
#
# OUT holds the generated programs and their outputs. TERMS names another
# terms.py (a variant's copy of the spike); its spike is what is tested.
set -u
[ $# -ge 1 ] || { echo "usage: $0 OUT [COUNT [NOTE]]" >&2; exit 2; }
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
mkdir -p "$1"
OUT=$(cd "$1" && pwd)
COUNT=${2:-200}
NOTE=${3:-}
T=${TERMS:-$ROOT/spike/tools/terms.py}
R="python3 -I $ROOT/scripts/results.py"
RUN=$($R run differential "{\"count\": $COUNT, \"seeds\": [7, 11, 23], \"terms\": \"$T\", \"fuel\": {\"spike\": 5000, \"kernel\": 320000, \"demand\": 1280000}}" "$NOTE") || exit 1
echo "run $RUN"
for tail in succ plus fma; do
  for mode in levels labels; do
    flags=""
    [ "$mode" = labels ] && flags="$flags --labels"
    [ "$tail" = plus ] && flags="$flags --plus"
    [ "$tail" = fma ] && flags="$flags --fma"
    for seed in 7 11 23; do
      D=$OUT/$tail/$mode/s$seed
      mkdir -p "$D"
      python3 -I "$T" --kernel $flags gen "$D" "$COUNT" "$seed" >/dev/null
      (cd "$D" && bend terms.bend -o terms >/dev/null) || { echo "$tail $mode $seed: build failed"; continue; }
      "$ROOT/scripts/capped.sh" 4000 1200 "$D/terms" > "$D/out.txt"
      $R terms "$RUN" "$tail" "$mode" "$seed" "$D/out.txt" >/dev/null
    done
  done
done
$R summary "$RUN"
