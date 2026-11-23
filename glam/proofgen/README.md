# glam/proofgen

The program that writes `glam/PROOF.bend`, `glam/SERVE_PROOF.bend` and
`glam/JOIN_PROOF.bend`, kept in git beside the files it writes
(`generated-outputs-checked-in`).
Building and checking glam want Bend alone, since the generated files
are committed. This directory matters to whoever changes those proofs.

    glam/proofgen/regen.sh          write the three files
    glam/proofgen/regen.sh --check  compare them, writing nothing in glam/

`scripts/check_generated.sh` runs the check, so the gate and the
pre-commit hook fail a generated file that its program no longer writes.
A run takes about two seconds.

## How it runs

Every stage runs in a scratch copy of `glam/` under
`results/proofgen_run/` (out of git), from that copy's root, with paths
relative to it. Only the three generated files are copied back. A stage
that would change any other file of `glam/` fails the run: some stages
insert a law into `glam/LAWS.bend` or a definition into
`glam/ring_model.bend` when it is missing, as they did when written, and
those files are kept by hand.

The stages are Python authoring aids that write Bend text, mostly through
f-strings. Several `exec` another stage's text up to a marker, the line
where it writes, to share its definitions (`gen_j1b.py` splits
`gen_j1.py`'s at its `open('glam/proofgen/j1_part1.txt','w')`). A change
to a marker's line must keep the marker matching, or the whole file runs.

## Inputs kept by hand

- `PROOF.bend.in`: `glam/PROOF.bend`'s hand-kept part, its header among
  it, which the stages append to. Edit it here, never the generated file.
- `SERVE_PROOF.bend.in`: likewise `glam/SERVE_PROOF.bend`'s, first
  written by an aid not kept.
- `align/ALIGN.bend`: the alignment lemmas, a Bend file the gate checks
  as itself, which `gen_align.py` copies. `align/bisect.py` checks a
  Bend file's growing prefixes, naming the first definition whose prefix
  fails: Bend reports a stack overflow with no place.
- `sv/ctxp.txt`, `wsel.txt`: text the stages read.

## Stages, in order

`glam/JOIN_PROOF.bend`, whole:

- `gen_link.py`, `gen_link2.py`: `link_live`'s proof, its case trees
  first.
- `gen_lvlink.py`, `join.py`: `link_leave`'s, appended.

`glam/PROOF.bend`, from `PROOF.bend.in`:

1. `gen_cpend.py`: `cursor_pend` over the index.
2. `gen_j1.py`, `gen_j1b.py`, `gen_j1c.py`: `join1_pend`, in three
   parts.
3. `gen_cx.py`: `cross_pend`.
4. `gen_fold.py`: `crossings_pend`.
5. `gen_keeps.py`, with `gen_keeps_b.py` to `_e.py`:
   `crossings_keeps`.
6. `gen_align.py`: the alignment section, from `align/ALIGN.bend`.
7. `gen_lv.py`: `leave_pend`.
8. `gen_jn.py`: `join_pend`.
9. `gen_cfi.py`: the ports faced after a copy's crossings.
10. `gen_lvk.py`: `leave_keeps`.
11. `gen_ch.py`: `cursor_head`.
12. `gen_jnk.py`: `join_keeps`.
13. `gen_cxl.py`: the served cursor's lookup through the crossings.
14. `gen_lera.py`: `leave_era_pend`.
15. `gen_compose.py`: each step law's conclusion widened
    (`step-laws-conclude-next-premises`).

`glam/SERVE_PROOF.bend`, from `SERVE_PROOF.bend.in`:

16. `sv/gen_cpi.py`, run for its parts 5, 6 and 7: the copy's sections
    over the index (`copy_pend`, `serve_pend`, `serve_keeps`,
    `serve_ring_exact`, `serve_root_keeps`).
17. `serve.py`: the file assembled.

Then both files:

18. `cut.py`: each cut to the definitions its laws reach.

## Changing a proof

1. Edit the stage that writes it, or the hand-kept input.
2. Run `glam/proofgen/regen.sh`.
3. Check the laws touched alone, with their mutants
   (`scripts/one_law.py PROOF LAW --mutants FILE`).
4. Run the gate.

A law's statement lives in its laws file, kept by hand. The stages that
once inserted a missing law are no help there.

The stages were written under `results/index_bits/` while the serve's
laws were restated over the index (the Cells plan's
`cells-freeze.sharing.cursors.index` steps) and moved here by
`cursor-laws.sources.commit`.
