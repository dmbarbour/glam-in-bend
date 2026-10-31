#!/bin/sh
# The kernel's differential test on random terms (terms.py --kernel): each
# ending, `succ 0`, `(plus 1) 0` and `(fma 1 1) 0`, lowered with levels and
# with static labels, three seeds of COUNT terms. Every term runs through
# the spike, the kernel's interpreted table, its generated rewrites and on
# demand, against the Python evaluator's value; each set is run under
# scripts/capped.sh, and every term's values and counts recorded in the
# analysis store (scripts/results.py) under one run, whose summary is
# printed at the end.
#
#   [JOBS=n] [OPS=1] spike/tools/differential.sh OUT [COUNT [NOTE]]
#
# OUT holds the nets written and the outputs. TERMS names another
# terms.py (a variant's copy of the spike); its spike is what is tested.
# OPS=1 lowers the builtins as an operator's data (terms.py --ops).
#
# The test program, spike/runterms.bend, is built once and reads each
# set's nets from a file (heap-strategies.measure.loader), where a
# program with its nets compiled in took a minute to build per set. The
# sets are then written and run side by side, JOBS at once (all the
# cores by default), and recorded in order once all are done.
set -u
ROOT=$(cd "$(dirname "$0")/../.." && pwd)

# one set, as the pool runs it: its nets written, then run; its state in
# D/status, which recording reads
if [ "${1:-}" = --one ]; then
  T=$2; OUT=$3; COUNT=$4; tail=$5; mode=$6; seed=$7
  flags=""
  [ "$mode" = labels ] && flags="$flags --labels"
  [ "$tail" = plus ] && flags="$flags --plus"
  [ "$tail" = fma ] && flags="$flags --fma"
  [ -n "${OPS:-}" ] && flags="$flags --ops"
  D=$OUT/$tail/$mode/s$seed
  mkdir -p "$D"
  echo started > "$D/status"
  python3 -I "$T" --kernel $flags gen "$D" "$COUNT" "$seed" >/dev/null
  if "$ROOT/scripts/capped.sh" 4000 1200 "$OUT/runterms" "$D/nets.txt" > "$D/out.txt"; then
    echo ran > "$D/status"
  else
    echo "run failed" > "$D/status"
  fi
  exit 0
fi

[ $# -ge 1 ] || { echo "usage: $0 OUT [COUNT [NOTE]]" >&2; exit 2; }
mkdir -p "$1"
OUT=$(cd "$1" && pwd)
COUNT=${2:-200}
NOTE=${3:-}
T=${TERMS:-$ROOT/spike/tools/terms.py}
SPIKE=$(cd "$(dirname "$T")/.." && pwd)
R="python3 -I $ROOT/scripts/results.py"
OPSJ=false
[ -n "${OPS:-}" ] && OPSJ=true
(cd "$SPIKE" && "$ROOT/scripts/capped.sh" 8000 1800 bend runterms.bend -o "$OUT/runterms" >/dev/null) ||
  { echo "differential.sh: runterms.bend failed to build" >&2; exit 1; }
RUN=$($R run differential "{\"count\": $COUNT, \"seeds\": [7, 11, 23], \"terms\": \"$T\", \"ops\": $OPSJ, \"fuel\": {\"spike\": 5000, \"kernel\": 320000, \"demand\": 1280000}}" "$NOTE") || exit 1
echo "run $RUN"
sets() {
  for tail in succ plus fma; do
    for mode in levels labels; do
      for seed in 7 11 23; do
        echo "$tail $mode $seed"
      done
    done
  done
}
sets | xargs -P "${JOBS:-$(nproc)}" -L 1 sh "$0" --one "$T" "$OUT" "$COUNT"
sets | while read -r tail mode seed; do
  D=$OUT/$tail/$mode/s$seed
  if [ "$(cat "$D/status" 2>/dev/null)" = ran ]; then
    $R terms "$RUN" "$tail" "$mode" "$seed" "$D/out.txt" >/dev/null
  else
    echo "$tail $mode $seed: run failed"
  fi
done
$R summary "$RUN"
