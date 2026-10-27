#!/bin/sh
# The gate: run before every commit, from anywhere in the repository.
# Checks the docs, the law history, the proofs (`bend PROOF.bend`), then
# that the benchmarks in bench/ still typecheck. Exits nonzero on any
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
# every PROOF.bend outside bench/, and one beside every LAWS.bend
proofs=$(git ls-files --cached --others --exclude-standard -- '*PROOF.bend' ':!bench/')
for laws in $(git ls-files --cached --others --exclude-standard -- '*LAWS.bend' ':!bench/'); do
  [ -f "$(dirname "$laws")/PROOF.bend" ] || { echo "$laws has no PROOF.bend beside it"; status=1; }
done
if [ -n "$proofs" ]; then
  for f in $proofs; do
    echo "-- $f"
    "$BEND" "$f" || status=1
  done
elif git ls-files --cached --others --exclude-standard -- '*.bend' ':!bench/' | grep -q .; then
  echo "Bend sources exist but no PROOF.bend does"
  status=1
else
  echo "no Bend sources yet"
fi

echo "== bench"
failed=0
for f in $(git ls-files --cached --others --exclude-standard -- 'bench/*.bend'); do
  out=$("$BEND" "$f" --check-only 2>&1) || { echo "$f:"; echo "$out"; failed=$((failed + 1)); }
done
if [ "$failed" -eq 0 ]; then echo "bench: ok"; else echo "bench: $failed failed"; status=1; fi

changes=$(git status --porcelain | wc -l)
tree="$(git rev-parse --short HEAD) with $changes changed path(s)"
if [ "$status" -eq 0 ]; then echo "PASS: $tree"; else echo "FAIL: $tree"; fi
exit "$status"
