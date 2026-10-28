#!/bin/sh
# Every term of the differential test's families profiled (terms.py
# --profile; kstrat.bend's Profiling): each ending, `succ 0`, `(plus 1) 0`
# and `(fma 1 1) 0`, lowered with levels, with static labels, and with
# levels as unit brackets (--unfused), three seeds of COUNT terms, each
# reduced fully by the profiling strategy. Each set is built and run under
# scripts/capped.sh, and every term's counts, weighted count, peels and
# interactions by pair of kinds recorded in the analysis store
# (scripts/results.py profiles) under one run.
#
#   [FUSE=off] spike/tools/profile.sh OUT [COUNT [NOTE]]
#
# OUT holds the generated programs and their outputs. FUSE=off profiles a
# copy of the spike, made in OUT, whose kernel never fuses controls
# (kprim.bend's fuse a no-op).
set -u
[ $# -ge 1 ] || { echo "usage: $0 OUT [COUNT [NOTE]]" >&2; exit 2; }
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
mkdir -p "$1"
OUT=$(cd "$1" && pwd)
COUNT=${2:-200}
NOTE=${3:-}
FUSE=${FUSE:-on}
SPIKE=$ROOT/spike
if [ "$FUSE" = off ]; then
  [ ! -e "$OUT/nofuse" ] || { echo "$OUT/nofuse exists: give a fresh OUT" >&2; exit 2; }
  mkdir -p "$OUT/nofuse"
  cp -r "$ROOT/spike" "$OUT/nofuse/spike"
  SPIKE=$OUT/nofuse/spike
  python3 -I - "$SPIKE/kprim.bend" <<'EOF' || exit 1
import sys
p = sys.argv[1]
s = open(p).read()
old = "def fuse(h: H, +x: U32) -> H:\n  fa.go0(U32.is_eq(x, nil()), h, x)\n"
if s.count(old) != 1:
    sys.exit("kprim.bend's fuse is not as profile.sh expects")
open(p, "w").write(s.replace(old, "def fuse(h: H, +x: U32) -> H:\n  h\n"))
EOF
fi
T=$SPIKE/tools/terms.py
R="python3 -I $ROOT/scripts/results.py"
RUN=$($R run profile "{\"count\": $COUNT, \"seeds\": [7, 11, 23], \"fuse\": \"$FUSE\", \"spike\": \"$SPIKE\", \"fuel\": 1280000}" "$NOTE") || exit 1
echo "run $RUN"
for tail in succ plus fma; do
  for mode in levels labels unfused; do
    flags="--profile"
    [ "$mode" = labels ] && flags="$flags --labels"
    [ "$mode" = unfused ] && flags="$flags --unfused"
    [ "$tail" = plus ] && flags="$flags --plus"
    [ "$tail" = fma ] && flags="$flags --fma"
    for seed in 7 11 23; do
      D=$OUT/$tail/$mode/s$seed
      mkdir -p "$D"
      python3 -I "$T" $flags gen "$D" "$COUNT" "$seed" >/dev/null
      (cd "$D" && bend terms.bend -o terms >/dev/null) || { echo "$tail $mode $seed: build failed"; continue; }
      "$ROOT/scripts/capped.sh" 4000 1200 "$D/terms" > "$D/out.txt"
      $R profiles "$RUN" "$tail" "$mode" "$seed" "$D/out.txt"
    done
  done
done
