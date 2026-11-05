#!/bin/sh
# Blend's gate: run before every commit to Blend, from anywhere. Checks
# Blend's docs (links, records and their index, plans and their step
# names), its law history and the records its laws cite, its proofs (each
# PROOF.bend checked by Bend and rechecked by BendTT's proven kernel,
# `--verdict`), the mutations each law must fail (each MUTANTS.txt), that
# its generated samples match what it emits, its samples, and that every
# other Bend file of its typechecks. A check whose inputs are unchanged
# keeps its pass (kept.py: a verdict, a mutants file's, a typecheck),
# never a failure, under results/kept. Times each section, and exits
# nonzero on any failure. The tools it shares with glam-in-bend are found
# by tools.sh; glam-in-bend's gate runs this one.
#
#   check.sh
set -u
cd "$(dirname "$0")" || exit 1
BLEND_ROOT=$PWD
. ./tools.sh
BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
export BEND
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
  [ -z "$1" ] || echo "== blend: $1"
}
# Blend's files, as git knows them, by a pattern
files() { git ls-files --cached --others --exclude-standard -- "$@"; }

section docs
python3 -I "$TOOLS/check_docs.py" --root . || status=1

section laws
python3 -I "$TOOLS/check_laws.py" || status=1

section proofs
# Lean as glam-in-bend's scripts/dev-setup.sh installs it, last on the
# path: its toolchain carries a clang of its own, which native builds
# must not find first
PATH="$PATH:$HOME/.lean/bin"
command -v lean >/dev/null 2>&1 || { echo "no lean for --verdict"; status=1; }
for laws in $(files '*LAWS.bend'); do
  [ -f "${laws%LAWS.bend}PROOF.bend" ] || { echo "$laws has no ${laws%LAWS.bend}PROOF.bend beside it"; status=1; }
done
for f in $(files '*PROOF.bend'); do
  python3 -I "$TOOLS/kept.py" verdict "$f" || status=1
done

section mutants
for m in $(files '*MUTANTS.txt'); do
  python3 -I "$TOOLS/kept.py" mutants "$m" || status=1
done

section generated
./check_generated.sh > results/generated.log 2>&1 || { grep -v ': matches blend$' results/generated.log; status=1; }

section samples
samples/check.sh || status=1

section "bend files"
# shellcheck disable=SC2046 # one argument a file
python3 -I "$TOOLS/kept.py" check $(files '*.bend' ':!*LAWS.bend' ':!*PROOF.bend') || status=1

section ""
echo "blend times:${times%,}; total $(since "$start") s"
if [ "$status" -eq 0 ]; then echo "blend: PASS"; else echo "blend: FAIL"; fi
exit "$status"
