#!/bin/sh
# Builds a Bend program natively twice: as `bend` builds it (OUT), and
# from its emitted C with every compiled Bend function forced inline
# (OUT_ai). Bend leaves inlining to clang's heuristics, which a small
# change elsewhere can flip (docs/BendIssues.md, "Inlining left to the C
# compiler"); the second build measures the work itself.
#
#   spike/tools/inline_build.sh PROGRAM.bend OUT
set -eu
[ $# -eq 2 ] || { echo "usage: $0 PROGRAM.bend OUT" >&2; exit 2; }
SRC=$1
mkdir -p "$(dirname "$2")"
OUT=$(cd "$(dirname "$2")" && pwd)/$(basename "$2")
DIR=$(cd "$(dirname "$SRC")" && pwd); NAME=$(basename "$SRC")
(cd "$DIR" && bend "$NAME" -o "$OUT" >/dev/null && bend "$NAME" -o "$OUT.c" >/dev/null)
python3 -I -c '
import re, sys
s = open(sys.argv[1]).read()
open(sys.argv[2], "w").write(re.sub(r"^INLINE Term (spin_\d+)\(", r"static inline __attribute__((always_inline)) Term \1(", s, flags=re.M))
' "$OUT.c" "${OUT}_ai.c"
clang -std=c11 -O3 "${OUT}_ai.c" -o "${OUT}_ai" -lpthread -lm 2>/dev/null
