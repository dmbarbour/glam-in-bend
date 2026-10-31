#!/bin/sh
# Builds a Bend program natively as `bend` builds it (OUT), and from its
# emitted C with every compiled Bend function forced inline (OUT_ai).
# Given training runs, each one argument string, also profile-guided
# builds of both (OUT_pgo, OUT_ai_pgo), clang choosing what to inline
# from the profile. With GCC_BUILDS=1, where GCC 16 is installed
# (scripts/gcc-setup.sh, or $GCC), also both C files by GCC (OUT_gcc,
# OUT_ai_gcc), a second compiler for reference; Bend's C is written for
# clang, so GCC's code is slower. Bend leaves inlining to clang's
# heuristics, which a small change elsewhere can flip
# (docs/BendIssues.md, "Inlining left to the C compiler"); the other
# builds measure the work itself.
#
# The C is emitted once and compiled as `bend` compiles it, its flags
# captured from the installed Bend (scripts/bend-cc.sh; for 2.0.39,
# clang -std=c11 -O3 ... -lpthread -lm, which `bend -o` runs on its C in a
# temporary directory whose name the binary keeps, so that two of its
# builds of one program differ by a few hundred instructions); the builds
# that do not depend on each other compile side by side
# (heap-strategies.measure.builds).
#
#   [GCC_BUILDS=1] spike/tools/inline_build.sh PROGRAM.bend OUT ["TRAIN ARGS" ...]
#   e.g. spike/tools/inline_build.sh spike/kernel.bend /tmp/k/kernel "14" "14 fma" "14 lvl"
set -eu
[ $# -ge 2 ] || { echo "usage: $0 PROGRAM.bend OUT [\"TRAIN ARGS\" ...]" >&2; exit 2; }
SRC=$1
mkdir -p "$(dirname "$2")"
OUT=$(cd "$(dirname "$2")" && pwd)/$(basename "$2")
shift 2
DIR=$(cd "$(dirname "$SRC")" && pwd); NAME=$(basename "$SRC")
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
FLAGS=$("$ROOT/scripts/bend-cc.sh" "$OUT.cc")
PRE=$(echo "$FLAGS" | sed -n 1p)
POST=$(echo "$FLAGS" | sed -n 2p)
(cd "$DIR" && bend "$NAME" -o "$OUT.c" >/dev/null)
python3 -I -c '
import re, sys
s = open(sys.argv[1]).read()
open(sys.argv[2], "w").write(re.sub(r"^INLINE Term (spin_\d+)\(", r"static inline __attribute__((always_inline)) Term \1(", s, flags=re.M))
' "$OUT.c" "${OUT}_ai.c"
CC="clang $PRE"
# compile the jobs given as "SOURCE TARGET [FLAGS]" side by side, failing
# if any fails
together() {
  pids=""
  for job in "$@"; do
    # shellcheck disable=SC2086
    set -- $job
    src=$1; dst=$2; shift 2
    # shellcheck disable=SC2086
    $CC "$@" "$src" -o "$dst" $POST 2>/dev/null &
    pids="$pids $!"
  done
  ok=0
  for p in $pids; do wait "$p" || ok=1; done
  return $ok
}
GEN=""
[ $# -gt 0 ] && GEN="$OUT.c ${OUT}_gen -fprofile-instr-generate"
# shellcheck disable=SC2086
together "$OUT.c $OUT" "${OUT}_ai.c ${OUT}_ai" ${GEN:+"$GEN"}
GCC=${GCC:-/opt/gcc-16.2.0/bin/gcc}
if [ "${GCC_BUILDS:-0}" = 1 ] && [ -x "$GCC" ]; then
  "$GCC" -std=c11 -O3 "$OUT.c" -o "${OUT}_gcc" -lpthread -lm 2>/dev/null &
  g1=$!
  "$GCC" -std=c11 -O3 "${OUT}_ai.c" -o "${OUT}_ai_gcc" -lpthread -lm 2>/dev/null &
  g2=$!
  wait "$g1"; wait "$g2"
fi
[ $# -gt 0 ] || exit 0
V=$(clang --version | sed -n 's/.*clang version \([0-9]*\).*/\1/p' | head -n 1)
for train in "$@"; do
  # shellcheck disable=SC2086
  LLVM_PROFILE_FILE="${OUT}_%p.profraw" "${OUT}_gen" $train >/dev/null
done
"llvm-profdata-$V" merge -o "$OUT.profdata" "${OUT}"_*.profraw
together "$OUT.c ${OUT}_pgo -fprofile-instr-use=$OUT.profdata" "${OUT}_ai.c ${OUT}_ai_pgo -fprofile-instr-use=$OUT.profdata"
