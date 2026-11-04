#!/bin/sh
# Blend's samples (blend/README.md): each valid sample's .bend is what
# Blend emits from its .blend, byte for byte, and runs under Bend to print
# what its .out says; each invalid sample fails, its errors exactly its
# .err.
#
#   blend/check.sh
set -u
cd "$(dirname "$0")/samples" || exit 1
BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
CAPPED=../../scripts/capped.sh
# Blend's executable, built once for each version of its sources
BLEND=$(BEND=$BEND ../build.sh) || { echo "blend: no executable to check with"; exit 1; }
status=0
n=0
for src in *.blend; do
  base=${src%.blend}
  n=$((n + 1))
  if [ ! -f "$base.bend" ] || [ ! -f "$base.out" ]; then
    echo "blend: $src has no $base.bend or $base.out"
    status=1
    continue
  fi
  "$CAPPED" 500 30 "$BLEND" emit "$src" 2>&1 | cmp -s - "$base.bend" || {
    echo "blend: $src does not emit $base.bend:"
    "$CAPPED" 500 30 "$BLEND" emit "$src" 2>&1 | diff - "$base.bend" | head -20
    status=1; }
  got=$("$CAPPED" 1000 60 "$BEND" "$base.bend" 2>&1)
  if [ "$got" != "$(cat "$base.out")" ]; then
    echo "blend: $base.bend prints '$got', not '$(cat "$base.out")'"
    status=1
  fi
done
m=0
for src in invalid/*.blend; do
  m=$((m + 1))
  err=${src%.blend}.err
  [ -f "$err" ] || { echo "blend: $src has no .err"; status=1; continue; }
  if got=$("$CAPPED" 500 30 "$BLEND" emit "$src" 2>&1); then
    echo "blend: $src emits, where it must fail with $(cat "$err")"
    status=1
  elif [ "$got" != "$(cat "$err")" ]; then
    echo "blend: $src gives '$got', not '$(cat "$err")'"
    status=1
  fi
done
[ "$status" -eq 0 ] && echo "blend samples: $n valid, $m invalid: ok"
exit "$status"
