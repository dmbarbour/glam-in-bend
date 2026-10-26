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
if [ -f PROOF.bend ]; then
  "$BEND" PROOF.bend || status=1
elif git ls-files --cached --others --exclude-standard -- '*.bend' ':!bench/' | grep -q .; then
  echo "Bend sources exist but PROOF.bend does not"
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
