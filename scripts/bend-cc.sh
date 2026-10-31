#!/bin/sh
# How `bend -o` compiles the C it emits, for builds that compile Bend's C
# themselves (spike/tools/inline_build.sh): a one-line program built in DIR
# with a logging `clang` first on PATH, its call split at the C file into
# the flags before it and those after, `-o` and its target left out. Prints
# the two, a line each. A Bend that calls no `clang` from PATH, or calls it
# otherwise than once on one C file, fails here rather than letting a
# measurement compile with something else. Under a second, so it runs for
# every build, whatever version of Bend is installed.
#
#   scripts/bend-cc.sh DIR
set -eu
[ $# -eq 1 ] || { echo "usage: $0 DIR" >&2; exit 2; }
mkdir -p "$1"
D=$(cd "$1" && pwd)
REAL=$(command -v clang) || { echo "bend-cc.sh: no clang on PATH" >&2; exit 1; }
printf '#!/bin/sh\necho "$@" >> "%s/args.txt"\nexec "%s" "$@"\n' "$D" "$REAL" > "$D/clang"
chmod +x "$D/clang"
printf 'import Base\n\ndef main() -> IO(Unit):\n  IO.print("probe")\n' > "$D/probe.bend"
: > "$D/args.txt"
(cd "$D" && PATH="$D:$PATH" bend probe.bend -o probe >/dev/null)
python3 -I -c '
import sys
calls = [l.split() for l in open(sys.argv[1]) if any(w.endswith(".c") for w in l.split())]
if len(calls) != 1:
    sys.exit(f"bend-cc.sh: bend called clang on {len(calls)} C files, not 1")
w = calls[0]
i = next(j for j, x in enumerate(w) if x.endswith(".c"))
after, k = [], i + 1
while k < len(w):
    if w[k] == "-o":
        k += 2
        continue
    after.append(w[k])
    k += 1
print(" ".join(w[:i]))
print(" ".join(after))
' "$D/args.txt"
