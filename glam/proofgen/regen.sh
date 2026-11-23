#!/bin/sh
# glam/proofgen (generated-outputs-checked-in): the program that writes
# glam/PROOF.bend, glam/SERVE_PROOF.bend and glam/JOIN_PROOF.bend,
# generated files kept in git beside it so that building and checking
# want Bend alone; this matters only to whoever changes those proofs.
# Python authoring aids, stage by stage, from the hand-kept inputs here: PROOF.bend.in and
# SERVE_PROOF.bend.in (the files' parts kept by hand, edited here, not in
# glam/), align/ALIGN.bend (the alignment lemmas, a Bend file checked as
# itself), sv/ctxp.txt and wsel.txt. See README.md.
#
# Every stage runs in a scratch copy of glam/ under
# results/proofgen_run/ (out of git), so that no stage writes a hand-kept
# file; the three generated files alone are copied back, or compared.
#
#   glam/proofgen/regen.sh          write the three generated files
#   glam/proofgen/regen.sh --check  compare them, writing nothing in glam/
set -eu
cd "$(dirname "$0")/../.."
root=$PWD
rm -rf results/proofgen_run
mkdir -p results/proofgen_run/glam results/proofgen_run/scripts
cp glam/*.bend results/proofgen_run/glam/
rm results/proofgen_run/glam/PROOF.bend results/proofgen_run/glam/SERVE_PROOF.bend results/proofgen_run/glam/JOIN_PROOF.bend
cp -R glam/proofgen results/proofgen_run/glam/proofgen
mkdir -p results/proofgen_run/glam/proofgen/kp
cp scripts/one_law.py scripts/kept.py results/proofgen_run/scripts/

cd results/proofgen_run
P=glam/proofgen
run() { python3 -I "$P/$1" >/dev/null; }
# glam/JOIN_PROOF.bend: link_live's proof, then link_leave's
run gen_link.py
run gen_link2.py
run gen_lvlink.py
run join.py
# glam/PROOF.bend: the hand-kept part, then the index's sections
cp $P/PROOF.bend.in glam/PROOF.bend
run gen_cpend.py
cp glam/PROOF.bend $P/PROOF.before_j1.bend
run gen_j1.py
run gen_j1b.py
run gen_j1c.py
cp glam/PROOF.bend $P/PROOF.before_cx.bend
run gen_cx.py
run gen_fold.py
run gen_keeps.py
run gen_align.py
run gen_lv.py
run gen_jn.py
run gen_cfi.py
run gen_lvk.py
run gen_ch.py
run gen_jnk.py
run gen_cxl.py
run gen_lera.py
run gen_compose.py
# glam/SERVE_PROOF.bend: the hand-kept part, then the copy's sections
CPI_PART=5 run sv/gen_cpi.py
CPI_PART=6 run sv/gen_cpi.py
CPI_PART=7 run sv/gen_cpi.py
run serve.py
# both cut to what their laws reach
run cut.py

cd "$root"
status=0
# a stage that would change a hand-kept file fails the run: what it would
# write is for its author to make by hand
for f in results/proofgen_run/glam/*.bend; do
  b=$(basename "$f")
  case $b in
    PROOF.bend|SERVE_PROOF.bend|JOIN_PROOF.bend) ;;
    *) cmp -s "$f" "glam/$b" || { echo "glam/proofgen would change glam/$b, which is kept by hand"; status=1; } ;;
  esac
done
for b in PROOF.bend SERVE_PROOF.bend JOIN_PROOF.bend; do
  if [ "${1:-}" = --check ]; then
    if cmp -s "results/proofgen_run/glam/$b" "glam/$b"; then
      echo "glam/$b: matches glam/proofgen/regen.sh"
    else
      echo "glam/$b differs from what glam/proofgen/regen.sh writes: regenerate it"
      status=1
    fi
  else
    cp "results/proofgen_run/glam/$b" "glam/$b"
    echo "glam/$b: written"
  fi
done
exit "$status"
