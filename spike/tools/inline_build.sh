#!/bin/sh
# Builds a Bend program natively as `bend` builds it (OUT), and from its
# emitted C with every compiled Bend function forced inline (OUT_ai).
# Given training runs, each one argument string, also profile-guided
# builds of both (OUT_pgo, OUT_ai_pgo), clang choosing what to inline
# from the profile. Bend leaves inlining to clang's heuristics, which a
# small change elsewhere can flip (docs/BendIssues.md, "Inlining left to
# the C compiler"); the other builds measure the work itself.
#
#   spike/tools/inline_build.sh PROGRAM.bend OUT ["TRAIN ARGS" ...]
#   e.g. spike/tools/inline_build.sh spike/kernel.bend /tmp/k/kernel "14" "14 fma" "14 lvl"
set -eu
[ $# -ge 2 ] || { echo "usage: $0 PROGRAM.bend OUT [\"TRAIN ARGS\" ...]" >&2; exit 2; }
SRC=$1
mkdir -p "$(dirname "$2")"
OUT=$(cd "$(dirname "$2")" && pwd)/$(basename "$2")
shift 2
DIR=$(cd "$(dirname "$SRC")" && pwd); NAME=$(basename "$SRC")
(cd "$DIR" && bend "$NAME" -o "$OUT" >/dev/null && bend "$NAME" -o "$OUT.c" >/dev/null)
python3 -I -c '
import re, sys
s = open(sys.argv[1]).read()
open(sys.argv[2], "w").write(re.sub(r"^INLINE Term (spin_\d+)\(", r"static inline __attribute__((always_inline)) Term \1(", s, flags=re.M))
' "$OUT.c" "${OUT}_ai.c"
CC="clang -std=c11 -O3"
$CC "${OUT}_ai.c" -o "${OUT}_ai" -lpthread -lm 2>/dev/null
[ $# -gt 0 ] || exit 0
V=$(clang --version | sed -n 's/.*clang version \([0-9]*\).*/\1/p' | head -n 1)
$CC -fprofile-instr-generate "$OUT.c" -o "${OUT}_gen" -lpthread -lm 2>/dev/null
for train in "$@"; do
  # shellcheck disable=SC2086
  LLVM_PROFILE_FILE="${OUT}_%p.profraw" "${OUT}_gen" $train >/dev/null
done
"llvm-profdata-$V" merge -o "$OUT.profdata" "${OUT}"_*.profraw
$CC -fprofile-instr-use="$OUT.profdata" "$OUT.c" -o "${OUT}_pgo" -lpthread -lm 2>/dev/null
$CC -fprofile-instr-use="$OUT.profdata" "${OUT}_ai.c" -o "${OUT}_ai_pgo" -lpthread -lm 2>/dev/null
