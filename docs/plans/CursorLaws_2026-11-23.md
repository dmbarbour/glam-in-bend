# The cursors' laws after the index's merge

`cursor-laws` steps: what the holistic review of the index's merge found,
ordered as the maintainer's answers direct
(`docs/reviews/IndexHolistic_2026-11-23.md`, its second reviewer's
`IndexHolisticFable_2026-11-23.md`). Drafted at the maintainer's request,
a rough plan (2026-11-23: "Ordering is up to you. Prepare a rough plan.
Partition, merge, reorder tasks where it makes sense."). Work proceeds in
this order unless the maintainer reorders it.

The rulings it follows:
- `generated-outputs-checked-in`: proofs a program writes are committed
  with the program, marked generated, checked reproduced.
- `laws-over-tests`: what matters, or is easy to state, is a law.
- `implementation-errors-stop`: glam's own errors stop the run.

And the maintainer's answer on duplicates: "Let's investigate making it a
law first. We can back off if it's impractical."

## Order, and why

1. `cursor-laws.sources` first. Every later step changes laws through
   the proofs' generators, which live in one container today; once they
   are in git, each later change is reproducible and checked.
2. `cursor-laws.stop` next: small, a ruling to carry out, and
   independent of the laws. The merged code's measurement is folded in,
   since it measures what it changes.
3. `cursor-laws.dup`: the decision's own law, of the index alone.
4. `cursor-laws.materializer`: the materializer under laws, with the
   root's laws composed of laws (`crossings_look`, carried here from the
   premises review) and the template freeze builds when nothing has
   finished.
5. `cursor-laws.loop`: the invariant established, reshaped once, and
   the wires stated. It restates every law, so it comes after the steps
   that add laws, which it then simplifies. It is split in three so that
   the base case comes first.
6. `cursor-laws.index`: the index's laws by disposition, last, as
   nothing waits on it.
7. `cursor-laws.watch`, throughout.

Merged: `crossings_look` into `.materializer`; F3 into `.materializer`;
the measurement (H4) into `.stop`. The premises review's P5 to P11
(`cells-freeze.sharing.cursors.index.ring.premises.later`) are spread
over `.dup` (P8, P9) and `.loop` (P5, P6, P7, P10, P11).

## Steps

- `cursor-laws` — planned — the steps below.
  - `cursor-laws.sources` — planned — the proofs' generators in git
    (F1, H1). M.
    - `cursor-laws.sources.commit` — planned — the live generators
      move under `results/index_bits/` and `results/proofgen/` into a
      tracked directory with `regen.sh` and the snapshot it starts from.
      These are the stages `regen.sh` runs, `sv/gen_cpi.py`, `gen_serve.py`,
      the alignment prototype and the index's appending aid. Their paths
      become the repository's own, not this container's. Backups and
      one-off aids stay out, listed.
    - `cursor-laws.sources.reproduce` — planned — each proof file
      regenerated whole from its generators: `glam/SERVE_PROOF.bend`,
      spliced from parts today, and `glam/INDEX_PROOF.bend`, kept by
      hand since half of it was written. Either generated whole or
      declared hand-written, with the sections a program still writes
      named. Each file's header says it is generated and by what.
    - `cursor-laws.sources.check` — planned —
      `scripts/check_generated.sh` regenerates each into scratch and
      compares, the gate running it. Its cost is measured, to be
      kept within the generated-code section's few seconds or kept as
      a pass while the inputs are unchanged.
  - `cursor-laws.stop` — planned — implementation errors stop the run
    (`implementation-errors-stop`; H7). S.
    - The serve's end reads the kernel's error count (`P.stats`, as the
      climb reads the capacity). A count risen stops the run with its
      diagnostic, before the core reads a cursor's words.
    - `cursor` orders its writes so that a refused insert leaves the
      placeholder a placeholder. The order is weighed against
      `insert_tree`'s premise, which would move to the caller.
    - Measured with the change (H4): the six- and eight-head families
      at n, 2n, 4n beside run 340; `spike/tools/sharing.py compare`
      over the merge (`ds.run` has two callers); run 340 cited in
      `cursors-indexed` and the Cells plan's `.index` step.
  - `cursor-laws.dup` — planned — one cursor a position as a law (F2,
    H3; P9, P8), investigated first, backed off if impractical. M.
    - `insert_dup`: an insert meeting its own key counts one error and
      writes nothing else. With `.stop`, the run then stops.
    - `cxs_ab`: the crossings' positions distinct and absent from the
      index at the serve's start give `RG.cxs.ok`'s stepwise absence.
      `cxs_room` beside it, the free list's nodes enough.
    - Whether freeze's crossings are distinct by a law of freeze: the
      claim that makes the error unreachable. Investigated, and
      reported as a question if large.
  - `cursor-laws.materializer` — planned — the materializer's
    composition under laws (`laws-over-tests`; F6, H2, F3). M to L.
    - `mz.sp`, `mz.sp.r`, `mz.root` and `mz.root.e` move into a module
      of their own beside `glam/ring.bend`. The serve's laws are stated
      over its functions, not over a copy of their sequence, and its
      mutants are added (the root port one past, `at_root` ignored, the
      leave before the crossings).
    - `crossings_look`: the served cursor found through the crossings,
      a law. The root's laws are then `serve_pend`, it and
      `leave_pend`, composed of laws alone.
    - The frontier: a law that its join never meets the served cursor
      (`cells-freeze.nested.host.join.self`), replacing the check if
      practical; the call sites of `join` and the eraser's `leave`.
    - The template freeze builds when nothing has finished (F3): find
      how the materializer serves it, and bring it under the laws where
      it is served by the copy.
  - `cursor-laws.loop` — planned — the invariant established and kept
    across serves (F7, H5).
    - `cursor-laws.loop.base` — planned — the first use made through
      `R.cursor` on an empty index (H8). `situate_pend` (P6): a fresh
      situating node is an empty index, and `cursor_pend` the base case.
      S to M, measured on the sharing families.
    - `cursor-laws.loop.shape` — planned — one change of the
      invariant, every law restated once. L.
      - The live nodes distinct (P5).
      - Layout, bases and past folded in (P10): four premises off
        every law.
      - `px_sub` and `px_grow` (P11): one serve's conclusion the next
        one's premise, across the heap's growth.
    - `cursor-laws.loop.wires` — planned — `join_links`,
      `leave_links` (P7): the wire a join or a leave makes. M.
  - `cursor-laws.index` — planned — the index's 41 laws by
    disposition, as `.retire`'s were (H6, H9, H12). M.
    - Each law gets the downstream proof that uses it, or the reason it
      stands alone.
    - `at_first` and `RG.first` retired with approval.
    - A mutant, or a stated reason, for each law no mutant names.
    - The redundant error arm of the insert commented.
    - Branches, which no port reaches, stated in `cursors-indexed`'s
      consequences for future sweeps.
  - `cursor-laws.watch` — planned — throughout: the gate's sections and
    the proofs' check times recorded at each step's commit. A step that
    slows iteration much is followed by one that speeds it (the
    maintainer, 2026-11-23: "watch the growth and occasionally take
    action to improve iteration speed").

## Open

- Where the generators live in the tree, and whether `regen.sh`'s
  snapshot stays one file or becomes the hand-kept part of
  `glam/PROOF.bend` (`.sources.commit`).
- How much `.loop.shape` shrinks the proofs, and whether
  `.materializer`'s module should wait for it.
