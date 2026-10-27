#!/bin/sh
# Builds spike/kernel.bend over each storage module (kmem_flat, kmem_grow,
# kmem_paged) and times it at k = 4 (start-up alone) and 18, 19, 20,
# three runs each, with peak memory
# (docs/plans/EvalSpike_2026-10-26.md, spike-node-layout).
#
#   spike/tools/kmem_run.sh OUT    (OUT: a directory to build in)
set -eu
[ $# -eq 1 ] || { echo "usage: $0 OUT" >&2; exit 2; }
OUT=$1
T=$(cd "$(dirname "$0")" && pwd)
SPIKE=$(cd "$T/.." && pwd)
for v in flat grow paged; do
  mkdir -p "$OUT/$v"
  cp "$SPIKE"/*.bend "$OUT/$v/"
  sed -i "s|^import ./kmem_flat.bend as KM$|import ./kmem_$v.bend as KM|" "$OUT/$v/kernel.bend"
  grep -q "^import ./kmem_$v.bend as KM$" "$OUT/$v/kernel.bend"
  (cd "$OUT/$v" && bend kernel.bend -o kernel >/dev/null)
done
for k in 4 18 19 20; do
  for v in flat grow paged; do
    for rep in 1 2 3; do
      echo "$v $(CAPPED_REPORT=1 "$SPIKE/../scripts/capped.sh" 3000 600 "$OUT/$v/kernel" "$k" 2>&1 | tr '\n' ' ')"
    done
  done
done
