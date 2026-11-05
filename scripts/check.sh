#!/bin/sh
# The gate: run before every commit, from anywhere in the repository.
# Checks the docs, the law history, the proofs (each `PROOF.bend`, by bend
# and by BendTT's proven kernel), the mutations each law must fail, that
# generated code matches its generator, Blend (its own gate, blend/check.sh:
# Blend is arranged as a repository of its own, `blend-own-repository`, so
# the sections here leave blend/ to it), the library of nets
# (spike/library.txt), then that every other Bend file still typechecks.
# Exits nonzero on any
# failure, and names the tree it checked so a stale pass can't pass for new.
# Each section's time follows it, each proof file's too, and a summary of
# them ends the run: a gate slow to run is a cost on every commit.
set -u
cd "$(dirname "$0")/.." || exit 1

BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
status=0

# the seconds since a mark, to a tenth
since() { awk -v a="$1" -v b="$(date +%s.%N)" 'BEGIN { printf "%.1f", b - a }'; }
start=$(date +%s.%N)
times=""
section=""
mark=$start
# a section begun, the one before it timed
section() {
  if [ -n "$section" ]; then
    t=$(since "$mark")
    echo "   ($section: $t s)"
    times="$times $section $t s,"
  fi
  section=$1
  mark=$(date +%s.%N)
  [ -z "$1" ] || echo "== $1"
}

section docs
python3 -I scripts/check_docs.py || status=1

section laws
python3 -I scripts/check_laws.py || status=1

section proofs
# each PROOF.bend checked by bend, then rechecked by BendTT's kernel, which
# has a proof in Lean (`bend --verdict`), a pass kept for inputs unchanged
# (scripts/kept.py: the file, its imports, Bend and Lean); Lean as scripts/dev-setup.sh
# installs it, last on the path: its toolchain carries a clang of its own,
# without the system's headers, which native builds must not find first
PATH="$PATH:$HOME/.lean/bin"
command -v lean >/dev/null 2>&1 || { echo "no lean for --verdict: run scripts/dev-setup.sh"; status=1; }
# every PROOF.bend outside bench/, and one beside every LAWS.bend: X_LAWS.bend
# beside X_PROOF.bend, as Blend writes a module's (blend/README.md)
proofs=$(git ls-files --cached --others --exclude-standard -- '*PROOF.bend' ':!bench/' ':!blend/')
for laws in $(git ls-files --cached --others --exclude-standard -- '*LAWS.bend' ':!bench/' ':!blend/'); do
  [ -f "${laws%LAWS.bend}PROOF.bend" ] || { echo "$laws has no ${laws%LAWS.bend}PROOF.bend beside it"; status=1; }
done
if [ -n "$proofs" ]; then
  for f in $proofs; do
    echo "-- $f"
    at=$(date +%s.%N)
    BEND=$BEND python3 -I scripts/kept.py verdict "$f" || status=1
    echo "   ($f: $(since "$at") s)"
  done
elif git ls-files --cached --others --exclude-standard -- '*.bend' ':!bench/' | grep -q .; then
  echo "Bend sources exist but no PROOF.bend does"
  status=1
else
  echo "no Bend sources yet"
fi

section mutants
# each MUTANTS.txt beside a proof file (X_MUTANTS.txt beside X_PROOF.bend),
# its mutations tried against the laws they name, each expected to fail
# them (scripts/one_law.py), a pass kept for inputs unchanged
# (scripts/kept.py)
for m in $(git ls-files --cached --others --exclude-standard -- '*MUTANTS.txt' ':!bench/' ':!blend/'); do
  BEND=$BEND python3 -I scripts/kept.py mutants "$m" || status=1
done

section "generated code"
# every generated file matches its generator (generated-sources)
BEND=$BEND scripts/check_generated.sh || status=1

section blend
# Blend's own gate: its docs, laws, proofs, mutants, generated samples,
# samples and Bend files (blend/check.sh)
if BEND=$BEND blend/check.sh > results/blend.log 2>&1; then
  grep -E '^blend( times|: )' results/blend.log
else
  grep -v ': matches blend$' results/blend.log
  status=1
fi

section library
# every net of spike/library.txt through every strategy, its checks
# (pairing-library); the program and its output go to results/library, a
# whole run's pass kept for its inputs unchanged (library.py says which)
if [ -f spike/library.txt ]; then
  BEND=$BEND python3 -I spike/tools/library.py results/library > results/library.log 2>&1 || {
    grep -v '^ok ' results/library.log; status=1; }
  tail -n 1 results/library.log
fi

section "bend files"
# every other Bend file typechecks, a pass kept for inputs unchanged
# (scripts/kept.py)
# shellcheck disable=SC2046 # one argument a file
BEND=$BEND python3 -I scripts/kept.py check $(git ls-files --cached --others --exclude-standard -- '*.bend' ':!*LAWS.bend' ':!*PROOF.bend' ':!blend/') ||
  status=1

section ""
echo "times:${times%,}; total $(since "$start") s"

changes=$(git status --porcelain | wc -l)
tree="$(git rev-parse --short HEAD) with $changes changed path(s)"
if [ "$status" -eq 0 ]; then echo "PASS: $tree"; else echo "FAIL: $tree"; fi
exit "$status"
