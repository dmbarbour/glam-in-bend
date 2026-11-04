#!/bin/sh
# Blend's samples (blend/README.md): each valid sample's emitted form,
# written by hand until Blend exists, must run under Bend and print what
# its .out says; each invalid sample states the error it must raise in
# its .err. Once Blend exists, it is run on every sample too, its output
# compared with the .bend or the .err.
#
#   blend/check.sh
set -u
cd "$(dirname "$0")/samples" || exit 1
BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
CAPPED=../../scripts/capped.sh
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
  got=$("$CAPPED" 1000 60 "$BEND" "$base.bend" 2>&1)
  if [ "$got" != "$(cat "$base.out")" ]; then
    echo "blend: $base.bend prints '$got', not '$(cat "$base.out")'"
    status=1
  fi
done
m=0
for src in invalid/*.blend; do
  m=$((m + 1))
  [ -f "${src%.blend}.err" ] || { echo "blend: $src has no .err"; status=1; }
done
[ "$status" -eq 0 ] && echo "blend samples: $n valid, $m invalid: ok"
exit "$status"
