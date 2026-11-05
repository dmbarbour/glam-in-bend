#!/bin/sh
# Blend's cost on one family of modules at N, 2N and 4N
# (blend/bench/README.md): each module printed by families.bend, built
# natively once for each version of it, then emitted by Blend's built
# executable (blend/build.sh) under perf (count.sh), each run capped
# (capped.sh); its instructions and seconds printed, and recorded in the
# analysis store (results.py; these three the tools blend/tools.sh
# finds): a run of tool
# `blend/bench/measure.sh`, its shape and N its parameters, each size a
# row of `counts` (build `blend`, the shape its workload, the size its
# k, no interactions) and its seconds a metric (`<shape> <size> s`). The
# modules and what Blend writes go to blend/results/bench (out of git).
#
#   blend/bench/measure.sh chain|fan|dense N [MB SECONDS]
set -u
[ $# -ge 2 ] || { echo "usage: $0 chain|fan|dense N [MB SECONDS]" >&2; exit 2; }
cd "$(dirname "$0")/.." || exit 1
BLEND_ROOT=$PWD
. ./tools.sh
shape=$1 n=$2 mb=${3:-4000} secs=${4:-600}
BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
out=results/bench
mkdir -p "$out/emitted" || exit 1
gen=$out/families
if [ ! -x "$gen" ] || [ bench/families.bend -nt "$gen" ]; then
  "$TOOLS/capped.sh" 1500 300 "$BEND" bench/families.bend -o "$gen" >&2 || exit 1
fi
blend=$(./build.sh) || exit 1
run=$(python3 -I "$TOOLS/results.py" run blend/bench/measure.sh "{\"shape\": \"$shape\", \"n\": $n}") || exit 1
for k in "$n" $((2 * n)) $((4 * n)); do
  mod=$out/$shape$k.blend
  "$gen" "$shape" "$k" > "$mod" || exit 1
  start=$(date +%s.%N)
  "$TOOLS/capped.sh" "$mb" "$secs" "$TOOLS/count.sh" "$blend" emit "$mod" "$out/emitted" > /dev/null 2> "$out/run.err"
  ok=$?
  t=$(awk -v a="$start" -v b="$(date +%s.%N)" 'BEGIN { printf "%.2f", b - a }')
  ins=$(sed -n 's/^count.sh: \([0-9]*\) instructions.*/\1/p' "$out/run.err")
  cyc=$(sed -n 's/^count.sh: .* \([0-9]*\) cycles.*/\1/p' "$out/run.err")
  [ "$ok" -eq 0 ] && [ -n "$ins" ] || {
    echo "$shape $k: the run failed or ran past its cap ($t s)"; cat "$out/run.err" >&2; exit 1; }
  python3 -I "$TOOLS/results.py" count "$run" blend "$shape" "$k" 0 "" "$ins" "$cyc" || exit 1
  python3 -I "$TOOLS/results.py" metric "$run" "$shape $k s" "$t" || exit 1
  echo "$shape $k: $ins instructions, $t s"
done
echo "run $run in the analysis store ($TOOLS/results.py)"
