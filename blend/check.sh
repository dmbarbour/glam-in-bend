#!/bin/sh
# Blend's samples (blend/README.md): each valid sample's .bend, what
# Blend emits from its .blend (a generated file, checked current by
# scripts/check_generated.sh), runs under Bend to print what its .out
# says; each invalid sample fails, its errors exactly its .err; each
# refused sample emits, and Bend refuses its proofs' file, its output
# exactly its .err.
#
#   blend/check.sh
set -u
cd "$(dirname "$0")/samples" || exit 1
BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
CAPPED=$PWD/../../scripts/capped.sh
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
  got=$("$CAPPED" 1000 60 "$BEND" "$base.bend" 2>&1)
  if [ "$got" != "$(cat "$base.out")" ]; then
    echo "blend: $base.bend prints '$got', not '$(cat "$base.out")'"
    status=1
  fi
done
m=0
# an invalid sample that emits writes into results/ (out of git), never
# beside the sample
out=../../results/blend/invalid
mkdir -p "$out" || exit 1
for src in invalid/*.blend; do
  m=$((m + 1))
  err=${src%.blend}.err
  [ -f "$err" ] || { echo "blend: $src has no .err"; status=1; continue; }
  if got=$("$CAPPED" 500 30 "$BLEND" emit "$src" "$out" 2>&1); then
    echo "blend: $src emits, where it must fail with $(cat "$err")"
    status=1
  elif [ "$got" != "$(cat "$err")" ]; then
    echo "blend: $src gives '$got', not '$(cat "$err")'"
    status=1
  fi
done
k=0
r=../../results/blend/refused
mkdir -p "$r" || exit 1
for src in refused/*.blend; do
  k=$((k + 1))
  base=${src#refused/}
  base=${base%.blend}
  [ -f "refused/$base.err" ] || { echo "blend: $src has no .err"; status=1; continue; }
  if ! "$CAPPED" 500 30 "$BLEND" emit --alone "$src" "$r" >/dev/null; then
    echo "blend: $src does not emit, where Bend must refuse its proofs"
    status=1
  elif got=$(cd "$r" && "$CAPPED" 1000 60 "$BEND" "${base}_PROOF.bend" 2>&1); then
    echo "blend: Bend accepts ${base}_PROOF.bend, where it must refuse it"
    status=1
  elif [ "$got" != "$(cat "refused/$base.err")" ]; then
    echo "blend: Bend gives '$got' on ${base}_PROOF.bend, not '$(cat "refused/$base.err")'"
    status=1
  fi
done
# an import no argument names is verified, its files compared with its
# emission: a stale one fails the command, which writes nothing, and
# `--alone` leaves it unverified; a module named by its absolute path
# finds its imports (results/, fixed paths, overwritten each run)
v=../../results/blend/verify
mkdir -p "$v/lib" || exit 1
cp imports.blend "$v/" && cp lib/shapes.blend "$v/lib/" && echo "# stale" > "$v/lib/shapes.bend" || exit 1
want="blend: lib/shapes.bend is stale: it is not what lib/shapes.blend emits
blend: name each such import too, or emit --alone to leave the imports unverified"
if got=$(cd "$v" && "$CAPPED" 500 30 "$BLEND" emit imports.blend 2>&1); then
  echo "blend: a stale import passes unverified"
  status=1
elif [ "$got" != "$want" ]; then
  echo "blend: a stale import gives '$got', not '$want'"
  status=1
fi
(cd "$v" && "$CAPPED" 500 30 "$BLEND" emit --alone imports.blend >/dev/null) || { echo "blend: emit --alone fails"; status=1; }
mkdir -p ../../results/blend/absolute || exit 1
"$CAPPED" 500 30 "$BLEND" emit "$PWD/imports.blend" ../../results/blend/absolute >/dev/null ||
  { echo "blend: a module named by its absolute path fails"; status=1; }
[ "$status" -eq 0 ] && echo "blend samples: $n valid, $m invalid, $k refused: ok"
exit "$status"
