#!/bin/sh
# The gate: run before every commit, from anywhere in the repository.
# Checks the docs, the law history, the proofs (each `PROOF.bend`, by bend
# and by BendTT's proven kernel), that
# generated code matches its generator, the library of nets
# (spike/library.txt), then that every other Bend file still typechecks.
# Exits nonzero on any
# failure, and names the tree it checked so a stale pass can't pass for new.
set -u
cd "$(dirname "$0")/.." || exit 1

BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
status=0

echo "== docs"
python3 -I scripts/check_docs.py || status=1

echo "== laws"
python3 -I scripts/check_laws.py || status=1

echo "== proofs"
# each PROOF.bend checked by bend, then rechecked by BendTT's kernel, which
# has a proof in Lean (`bend --verdict`); Lean as scripts/dev-setup.sh
# installs it, last on the path: its toolchain carries a clang of its own,
# without the system's headers, which native builds must not find first
PATH="$PATH:$HOME/.lean/bin"
command -v lean >/dev/null 2>&1 || { echo "no lean for --verdict: run scripts/dev-setup.sh"; status=1; }
# every PROOF.bend outside bench/, and one beside every LAWS.bend
proofs=$(git ls-files --cached --others --exclude-standard -- '*PROOF.bend' ':!bench/')
for laws in $(git ls-files --cached --others --exclude-standard -- '*LAWS.bend' ':!bench/'); do
  [ -f "$(dirname "$laws")/PROOF.bend" ] || { echo "$laws has no PROOF.bend beside it"; status=1; }
done
if [ -n "$proofs" ]; then
  for f in $proofs; do
    echo "-- $f"
    "$BEND" "$f" --verdict || status=1
  done
elif git ls-files --cached --others --exclude-standard -- '*.bend' ':!bench/' | grep -q .; then
  echo "Bend sources exist but no PROOF.bend does"
  status=1
else
  echo "no Bend sources yet"
fi

echo "== generated code"
# every generated file matches its generator (generated-sources)
BEND=$BEND scripts/check_generated.sh || status=1

echo "== library"
# every net of spike/library.txt through every strategy, its checks
# (pairing-library); the program and its output go to results/library
if [ -f spike/library.txt ]; then
  BEND=$BEND python3 -I spike/tools/library.py results/library > results/library.log 2>&1 || {
    grep -v '^ok ' results/library.log; status=1; }
  tail -n 1 results/library.log
fi

echo "== bend files"
failed=0
for f in $(git ls-files --cached --others --exclude-standard -- '*.bend' ':!*LAWS.bend' ':!*PROOF.bend'); do
  out=$("$BEND" "$f" --check-only 2>&1) || { echo "$f:"; echo "$out"; failed=$((failed + 1)); }
done
if [ "$failed" -eq 0 ]; then echo "bend files: ok"; else echo "bend files: $failed failed"; status=1; fi

changes=$(git status --porcelain | wc -l)
tree="$(git rev-parse --short HEAD) with $changes changed path(s)"
if [ "$status" -eq 0 ]; then echo "PASS: $tree"; else echo "FAIL: $tree"; fi
exit "$status"
