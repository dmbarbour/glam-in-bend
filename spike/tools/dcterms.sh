#!/bin/sh
# Collecting demand against plain demand on random terms
# (heap-strategies.erasure.load.cycle.walk.directed.dataflow.walk): the
# differential test's sets (terms.py --kernel gen: each ending, `succ 0`,
# `(plus 1) 0` and `(fma 1 1) 0`, lowered with levels and with static
# labels, three seeds of COUNT terms), each run by a build of
# spike/runmode.bend on plain demand (lazy), demand collecting where its
# net would grow (dclazy) and its stress test, collecting a net of 1024
# nodes or fewer every 16 steps (dcs). Every term's state and value must
# agree across the three: a collection never changes what demand finds.
# Prints, per set, its terms, how many collected, the states plain demand
# ended in, and the terms that differ; exits 1 if any does.
#
#   spike/tools/dcterms.sh RUNMODE OUT [COUNT]
#
# OUT holds the nets written and each mode's output. A random corpus finds
# faults; shrink one into the library (spike/library.txt) before fixing it.
# The three modes run at once, each under scripts/capped.sh: DCTERMS_CAP,
# "MEGABYTES SECONDS" (1500 300), so that together they stay within the
# machine's free memory.
set -u
[ $# -ge 2 ] || { echo "usage: $0 RUNMODE OUT [COUNT]" >&2; exit 2; }
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
RM=$1
OUT=$2
COUNT=${3:-100}
CAP=${DCTERMS_CAP:-1500 300}
status=0
for tail in succ plus fma; do
  for mode in levels labels; do
    for seed in 7 11 23; do
      flags=""
      [ "$mode" = labels ] && flags="$flags --labels"
      [ "$tail" = plus ] && flags="$flags --plus"
      [ "$tail" = fma ] && flags="$flags --fma"
      D=$OUT/$tail/$mode/s$seed
      mkdir -p "$D"
      python3 -I "$ROOT/spike/tools/terms.py" --kernel $flags gen "$D" "$COUNT" "$seed" >/dev/null
      for m in lazy dclazy dcs; do
        # shellcheck disable=SC2086
        "$ROOT/scripts/capped.sh" $CAP "$RM" "$D/nets.txt" $m > "$D/$m.txt" 2>&1 &
      done
      wait
      python3 -I - "$D" "$tail $mode $seed" <<'PY' || status=1
import re
import sys

d, label = sys.argv[1], sys.argv[2]


def rows(m):
    out = {}
    for ln in open(f"{d}/{m}.txt"):
        k = re.match(r"^([^:]+): ([^:]+): ([^,]*),", ln)
        if k:
            out[k.group(1)] = (k.group(2), k.group(3))
    return out


def collecting(m):
    return sum(1 for ln in open(f"{d}/{m}.txt") if re.search(r"; [1-9]\d* collections", ln))


a, b, c = rows("lazy"), rows("dclazy"), rows("dcs")
bad = sorted(k for k in set(a) | set(b) | set(c) if not (a.get(k) == b.get(k) == c.get(k)))
states = {}
for v in a.values():
    states[v[0]] = states.get(v[0], 0) + 1
print(f"{label}: {len(a)} terms, collecting in {collecting('dclazy')}, under stress in {collecting('dcs')};"
      f" plain demand {states}; {len(bad)} differ")
for k in bad[:3]:
    print(f"  {k}: plain {a.get(k)}, collecting {b.get(k)}, under stress {c.get(k)}")
sys.exit(1 if bad or not a else 0)
PY
    done
  done
done
exit "$status"
