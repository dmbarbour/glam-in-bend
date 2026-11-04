#!/bin/sh
# Blend's samples (blend/README.md): each valid sample's emitted form,
# written by hand until Blend emits it, must run under Bend and print what
# its .out says; each invalid sample states the error it must raise in
# its .err. Blend checks every sample as far as its steps go (its
# objects, `blend-objects`; their references, `blend-resolve`): the
# invalid samples whose errors those steps find must print their .err
# exactly, and every other sample no error; once it emits, its output is
# compared with the .bend too.
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
# the invalid samples whose errors Blend finds so far, by the step that
# finds them
found="upd-undefined def-defined undeclared no-c3 shadow host-at-module"
for src in *.blend invalid/*.blend; do
  got=$("$CAPPED" 1000 60 "$BEND" ../blend.bend resolve "$src" 2>&1) || {
    echo "blend: checking $src failed: $got"; status=1; continue; }
  base=$(basename "$src" .blend)
  case " $found " in
    *" $base "*)
      [ "$got" = "$(cat "${src%.blend}.err")" ] || {
        echo "blend: $src gives '$got', not '$(cat "${src%.blend}.err")'"; status=1; } ;;
    *)
      bad=$(printf '%s\n' "$got" | grep -E '^[^ :]+:[0-9]+: ') && {
        echo "blend: $src gives errors:"; echo "$bad"; status=1; } ;;
  esac
done
[ "$status" -eq 0 ] && echo "blend samples: $n valid, $m invalid, resolved: ok"
exit "$status"
