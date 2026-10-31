#!/bin/sh
# The kernel's instructions on its standard workloads (succ, fma and lvl,
# lvl and succ on demand too) at k, in the four builds of
# spike/tools/inline_build.sh: as bend builds it, every function forced
# inline, and both profile-guided, trained at k 14. Each run is counted
# by scripts/count.sh under scripts/capped.sh and recorded in the analysis
# store (scripts/results.py) under one run; with BASE, an earlier run of
# this tool, each count is printed beside that run's. With EV=1, the
# erasure modes too (spike/kernel.bend's ev and evlazy: succ, fma and lvl
# eagerly, succ and lvl on demand), recorded as workloads `succ.ev` and
# so on, demand's lazy; the profile-guided builds are trained without
# them. BUILDS names the builds to count, all four by default; without a
# profile-guided one, nothing is trained (spike/tools/spot.sh, the default
# and forced-inline builds alone, for development).
#
#   [BASE=RUN] [EV=1] [BUILDS="default ai"] spike/tools/count_builds.sh OUT [K [NOTE]]
#
# OUT holds the builds.
set -eu
[ $# -ge 1 ] || { echo "usage: $0 OUT [K [NOTE]]" >&2; exit 2; }
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
mkdir -p "$1"
OUT=$(cd "$1" && pwd)
K=${2:-18}
NOTE=${3:-}
R="python3 -I $ROOT/scripts/results.py"
BUILDS=${BUILDS:-default ai pgo ai_pgo}
case " $BUILDS " in
  *pgo*)
    "$ROOT/spike/tools/inline_build.sh" "$ROOT/spike/kernel.bend" "$OUT/kernel" \
      "14 succ" "14 succ lazy" "14 fma" "14 lvl" "14 lvl lazy" >/dev/null
    TRAIN='["14 succ", "14 succ lazy", "14 fma", "14 lvl", "14 lvl lazy"]' ;;
  *)
    "$ROOT/spike/tools/inline_build.sh" "$ROOT/spike/kernel.bend" "$OUT/kernel" >/dev/null
    TRAIN='[]' ;;
esac
BLIST=$(echo "$BUILDS" | sed 's/\([a-z_]*\)/"\1"/g; s/ /, /g')
RUN=$($R run count_builds "{\"k\": $K, \"builds\": [$BLIST], \"train\": $TRAIN, \"ev\": ${EV:-0}, \"tool\": \"spike/tools/count_builds.sh\"}" "$NOTE")
echo "run $RUN"
for b in $BUILDS; do
  bin=$OUT/kernel
  [ "$b" = default ] || bin=$OUT/kernel_$b
  set -- "succ" "succ lazy" "fma" "lvl" "lvl lazy"
  [ "${EV:-0}" = 1 ] && set -- "$@" "succ ev" "succ evlazy" "fma ev" "lvl ev" "lvl evlazy"
  for w in "$@"; do
    # shellcheck disable=SC2086
    out=$("$ROOT/scripts/capped.sh" 4000 600 "$ROOT/scripts/count.sh" "$bin" "$K" $w 2>&1)
    itrs=$(echo "$out" | sed -n 's/.* \([0-9]*\) interactions.*/\1/p' | head -n 1)
    ins=$(echo "$out" | sed -n 's/^count.sh: \([0-9?]*\) instructions.*/\1/p')
    cyc=$(echo "$out" | sed -n 's/^count.sh: .* instructions, \([0-9?]*\) cycles.*/\1/p')
    lazy=0
    case "$w" in *lazy) lazy=1 ;; esac
    $R count "$RUN" "$b" "$(echo "${w% lazy}" | tr ' ' '.')" "$K" "$lazy" "$itrs" "$ins" "$cyc"
  done
done
if [ -n "${BASE:-}" ]; then
  $R sql "select b.build, b.workload, b.lazy, b.interactions - a.interactions as d_itrs, a.instructions, b.instructions, round(100.0 * (b.instructions - a.instructions) / a.instructions, 2) as pct from counts a join counts b on a.build = b.build and a.workload = b.workload and a.lazy = b.lazy and a.k = b.k where a.run_id = $BASE and b.run_id = $RUN order by b.workload, b.lazy, b.build"
else
  $R sql "select build, workload, lazy, interactions, instructions from counts where run_id = $RUN order by workload, lazy, build"
fi
