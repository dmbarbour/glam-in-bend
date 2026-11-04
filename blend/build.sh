#!/bin/sh
# Builds Blend natively, once for each version of its sources and of Bend,
# into results/blend/ (out of git), and prints the executable's path. A
# run of the executable takes milliseconds, where `bend blend.bend ...`
# checks and compiles the tool again each time (1.3 s a run, 2026-11-04);
# the build takes 13 s and 0.4 GB.
#
#   blend/build.sh          the executable's path, built first if stale
#   blend/run.sh ARGS...    the executable run (blend/run.sh resolve F.blend)
set -u
cd "$(dirname "$0")/.." || exit 1
BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
out=results/blend
# the key: Bend itself (its version; its executable's size, time and
# inode, cheaper than hashing 80 MB on every run; its Base and effects
# beside it) and every Bend source of Blend's, so that an update of Bend,
# in place or not, rebuilds the tool
exe=$(command -v "$BEND" 2>/dev/null) || { echo "blend: no bend at $BEND" >&2; exit 1; }
real=$(readlink -f "$exe")
lib=$(dirname "$real")/../bend2
key=$({ "$BEND" version; stat -c '%s %Y %i' "$real"; cat "$lib"/base.bend "$lib"/effs/* 2>/dev/null; cat blend/*.bend; } |
  sha256sum | cut -d' ' -f1)
if [ ! -x "$out/blend" ] || [ "$(cat "$out/key" 2>/dev/null)" != "$key" ]; then
  mkdir -p "$out" || exit 1
  scripts/capped.sh 1500 300 "$BEND" blend/blend.bend -o "$out/blend.new" >&2 || {
    echo "blend: the build failed" >&2; exit 1; }
  mv "$out/blend.new" "$out/blend" && echo "$key" > "$out/key" || exit 1
fi
echo "$PWD/$out/blend"
