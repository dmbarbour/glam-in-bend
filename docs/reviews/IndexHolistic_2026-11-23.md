# The index's merge, reviewed whole

The work merged as 2e4aeea (`cursor-index-spike` into main, 846f452
before it), judged as a whole against its intent, after the merge, as the
maintainer asked (2026-11-23: "We'll do a holistic review after merge").
That intent was a copy's cursors in a crit-bit tree of the net's nodes in
place of the ring and its walks (`cursors-indexed`), the serve's laws
restated over it, the ring's retired. Two reviewers: the agent, here, and
the second reviewer, Fable, in `IndexHolisticFable_2026-11-23.md`,
written apart and kept as written. Drafted by the agent.

## Findings

### F1. The proofs' source lives outside git

- **Evidence.** The proof files are committed, and their source is not
  [checked]:

      glam/PROOF.bend        3,819 lines, 2.8 MB, longest line 39,778
      glam/SERVE_PROOF.bend  2,055 lines, 1.5 MB, longest line 62,811
      glam/INDEX_PROOF.bend  5,563 lines, 1.0 MB, longest line 21,325

  `glam/PROOF.bend` is rebuilt by `results/index_bits/regen.sh` from a
  snapshot (`results/index_bits/PROOF.before_cpend.bend`) through about
  twenty generator stages; `glam/SERVE_PROOF.bend` is spliced from
  `results/index_bits/sv/gen_cpi.py`'s parts (`sv/NOTES.md`). Those are
  69 Python files and about 16,000 lines, under `results/`, which
  `.gitignore:3` ignores: no file under it is tracked.
- **Against the rules.** `generated-sources`: "a generator writes the
  variants into files of their own, committed beside it and never edited
  by hand ... Python serves as a development tool, never as the primary
  expression of source"; `scripts/check_generated.sh` lists every
  generated file and regenerates it. The proof files are neither hand
  written nor listed, and their generators are neither committed nor
  Bend.
- **Why it matters.** A fresh clone checks the proofs but cannot change
  one by the means it was made. A line of 60,000 characters will not be
  edited by hand, so the next change to a serve law needs these
  generators, which live only in this container's working tree.
- **Addressed** after the ruling (`generated-outputs-checked-in`):
  `cursor-laws.sources` moved the generators into `glam/proofgen/` and
  the check into the gate.
- **Proposal.** A ruling, as a design question (below). One way is to
  commit the generators beside the proofs, e.g. `tools/proofs/`, with
  `regen.sh` and its snapshot, and list the proof files in
  `scripts/check_generated.sh` so that the gate checks they are
  reproduced. This accepts Python as the authoring aid it has been and
  records it. Another is to express the proof families in Blend, the
  repository's own route for generated Bend.

### F2. One cursor a position is not yet a law

- **Evidence.** `cursors-indexed` decides "One cursor a position in a
  copy: an insert meeting its own key is a kernel error, the tree
  unchanged, and a law." The code says so and defers the law
  (`glam/index.bend:21-22`: "Keys are distinct: an insert meeting its own
  key is an error, the tree unchanged (one cursor a position in a copy,
  a law to come)") [checked]. No law of `glam/INDEX_LAWS.bend` states
  the duplicate's error [checked]. The serve's laws take the absence as
  a premise instead, `cursor_pend`'s `ha: look(I, src) == None` and
  `RG.cxs.ok` (`IndexPremises` P9, `insert_dup`, deferred past the
  merge).
- **Proposal.** `insert_dup` next: the insert at a key present counts
  one error and keeps every word. It is the decision's own law, small,
  and of the index alone.

### F3. One template freeze builds is outside every serve law

- **Evidence.** Freeze emits, where nothing finished, one cursor and one
  crossing and no link (`glam/freeze.bend:490`):

      (h, Fz{T.Tpl{[T.TN{R.KCur{}, V.PNone{}}], Nil{}, T.TE{0, 0}, 1},
             [RN.FzC{0, P.iface(), True{}, P.iface()}], 0})

  This is the plan's `(\y -> y) c`, "nothing finished, the root a cursor
  at the interface" (`docs/plans/Cells_2026-11-09.md:1309`) [checked].
  `SV.copy.ok` asks of each crossing's hole a link naming it
  (`glam/serve_model.bend:87`, `names(ls, dm, at)`); this template has
  none. `SV.root.ok` asks a root that is no hole, and this template's
  root is the hole [checked]. So neither `copy_pend` nor the root's laws
  apply to serving it. The second reviewer saw the first half in the
  premises review (`IndexPremisesFable_2026-11-23.md:272`); no review or
  plan step dispositioned it [checked].
- **Unchecked.** Whether the materializer serves this template through
  the copy at all. Its header's frontier case may take it first: "a
  cursor of the ring at the port reached is joined to the served one
  directly, nothing copied (the identity's case)"
  (`glam/materialize.bend:32-33`). If so, the gap is in the laws' text,
  not their reach.
- **Proposal.** Find which path serves it, with a sample if the ladder
  has none. If it is the copy's, either widen the model so that a root
  hole is named by the root (and the root law's port taken from it), or
  write it into the laws' "Not claimed".

### F4. The code's comments still describe the ring

- **Evidence.** The premises review fixed `glam/ring.bend`'s wording
  (P4) and left the others [checked]:
  - `glam/materialize.bend:17`: "A copy's cursors form a ring in the
    host's heap through word 3"; also `:29`, "looked up in the ring";
    `:31`, "put in the ring"; `:32`, "a cursor of the ring". Eleven
    mentions in the file.
  - `glam/core.bend:768`, `:821`, `:909` ("a ring served from the
    source").
  - three in `glam/freeze.bend`.
  - `glam/test_materialize.bend:139`, a test's message, "a climb met no
    position of the ring".
- **Fixed** in the review's commit: the comments of
  `glam/materialize.bend`, `glam/core.bend` and `glam/freeze.bend` and
  the test's wording speak of the index; the test's `ring` helper is
  `index_one`, a tree of one leaf. `glam/index.bend`'s own mentions say
  what the tree replaced and stay.
- **Proposal.**
  Whether `glam/ring.bend` (`R.`) is renamed for what it now holds is a
  larger edit: it is named in some thirty files, generators included.
  Consider it with F1.

### F5. The frontier's new check has no test

- **Evidence.** The rulings added a report where the frontier would join
  a cursor to itself: `sv.front.c` and `sv1.front.c`, `SvBad` and
  `S1Bad` (`glam/materialize.bend`; `corruption-reported-when-cheap`).
  `glam/test_materialize.bend` exercises `SvBad` for the climb alone
  (`:240-252`, "A climb that found no position of the ring") [checked].
  No sample reaches the new case, and none can without corrupting a
  heap.
- **Fixed** in the review's commit: `front_self` and `front1_self` in
  `glam/test_materialize.bend` give each path's frontier the served
  cursor as the one its index finds, and expect the report, beside the
  climb's test.

### F6. The materializer itself is neither a law's subject nor mutated

- **Evidence.** The mutants' files [checked]:

      glam/INDEX_MUTANTS.txt   index.bend 22, index_model.bend 17, kprim.bend 2, ring_model.bend 1
      glam/MUTANTS.txt         ring.bend 28
      glam/SERVE_MUTANTS.txt   splice_copy.bend 5
      glam/JOIN_MUTANTS.txt    kprim.bend 2

  None touches `glam/materialize.bend`. The root's laws restate its
  sequence by hand, as an expression over `R.crossings` and `R.leave`
  with the root's port read through the map, "as the materializer reads
  it, mz.root" (`glam/SERVE_LAWS.bend`, `serve_ring_exact`'s comment). A
  change to the order of the materializer's steps, which port it links
  at the root, or which cursor leaves, would pass every proof. Only the
  ladder would catch it.
- **Proposal.** Where Bend allows, state the root's laws over the
  materializer's own functions rather than a copy of their composition.
  Failing that, add mutants of `glam/materialize.bend` to the library or
  the ladder.

### F7. The laws keep the invariant; nothing establishes it

- **Evidence.** Every step law takes `RG.px.ok` and gives it back. No law
  shows that the state the core builds before a copy's first serve
  satisfies it (`situate_pend`, `.premises.later`), nor that the
  materializer's loop calls the steps in an order the laws chain. The
  caller's obligations are also open:
  - `RG.cxs.ok`, `RG.far.off`, the live nodes distinct;
  - freeze's `SM.tpl.ok`, `SV.copy.ok` and `SV.root.ok`, "not claimed"
    by the laws' own text, "an obligation for its review"
    (`glam/SERVE_LAWS.bend`).
- **Note.** Known and listed (`.premises.later`; the second reviewer's
  premises review). Recorded here so that the merge is not read as
  proving the serve correct end to end: it proves each step correct
  where its premises hold.

### F8. The costs the decision gave hold on the merged code

- **Evidence.** `scripts/cursors.py` on main at 2e4aeea, the ladder's
  build, sizes 100 to 1,600 [checked; `results/index_bits/review/
  cursors_merge.log`]. Instructions an element:

      seq   201,566 at 100   190,129 at 1,600   (spike: 202K, 191K)
      deep  204,157 at 100   193,411 at 1,600   (spike: 204K, 192K; the ring 209K, 323K)

  Each doubling costs ×1.94 to ×2.00, so the cost is linear. The laws'
  work changed no cost the decision cited; the six- and eight-head
  families were not run again.
- **Note.** Recorded for the decision's numbers, which came from the
  spike before the laws.

### F9. Smaller things

- The proofs' checks: `glam/PROOF.bend` 52 s, `glam/SERVE_PROOF.bend` 60
  s, in parallel, the gate about 160 s when a proof changes
  (`results/index_bits/review/gate_p3.log`). Acceptable, and they fell
  with P3.
- The frontier check is written twice, `sv.front.c` for the serve and
  `sv1.front.c` for the one-net path, as the two paths already are. No
  new duplication, but the two paths' twinning predates this work and
  stays a candidate for a template.
- The alignment section's general lemmas are listed for the hub
  (`.premises.later`), awaiting Blend's next commit.

## With the second reviewer

The second reviewer's review (`IndexHolisticFable_2026-11-23.md`, H1 to
H12) was written apart; each of its claims relayed here was checked
against the source.

- **Agreed, found by both:**
  - F1 and H1, the proofs' generators out of git;
  - F2 and H3, one cursor a position a premise, not a law;
  - F6 and H2, the materializer outside every law and mutant;
  - F7 and H5, the invariant kept and never established;
  - F4 and H10, the ring's wording;
  - F8 and H4, the costs, which H4 found unrecorded.
- **H1 adds** that the proof files' headers disagree about what they are
  (`glam/SERVE_PROOF.bend:1-4` named only `results/proofgen/gen_serve.py`;
  `glam/PROOF.bend`'s said nothing). Fixed here: both headers say which
  aids wrote them. Its one open point is answered: `regen.sh`
  reproduces the committed `glam/PROOF.bend` byte for byte. That was
  checked by `cmp` after P1, after P3 and here.
- **H4 adds** that the record's figures and the plan's differ by a few
  thousand instructions and cite no run. Run 340 of the store
  (`scripts/cursors.py` at 2e4aeea, recorded here) gives `deep` 193K at
  1,600: the record's figure, where the plan's 192K is the first spike's.
  Proposed: cite run 340 in the record and the plan. Still to do: the
  six- and eight-head families again, and `spike/tools/sharing.py
  compare` over the merge (`ds.run` has two callers now, which splits a
  segment).
- **H6, checked:** six index laws no downstream proof names
  (`at_first`, `put_leaves`, `put_flsep`, `del_flsep`, `del_drop`,
  `look_member`: zero uses in `glam/PROOF.bend` and
  `glam/SERVE_PROOF.bend`). `at_first` bridges to `find_exact`, retired
  in this merge. Eight laws no mutant names. Proposed: a disposition
  pass over the index's laws, as `.retire`'s was.
- **H7, checked:** `cursor` writes a placeholder's header and word 2,
  then inserts (`glam/ring.bend:48-49`). An insert refused at its own
  key therefore leaves a cursor in no index. The error is counted, and
  read only when a cell's value is forced or the run ends.
- **H8:** the core lays out the first index by hand (`use.cursor`,
  `use.situ`), the base case no law covers. Its comment was fixed here
  (F4); the proposal stands, to make the first use `R.cursor` on an
  empty index.
- **H10, the rest fixed here:**
  - `glam/SERVE_LAWS.bend`'s and `glam/SPLICE_LAWS.bend`'s headers;
  - `glam/SERVE_MUTANTS.txt`'s file name;
  - `remove_tree`'s stale "Not claimed", which `remove_free` claims.

  `glam/PROOF.bend`'s lessons are still the ring's alone. The index
  sections' lessons are in `docs/Proving.md`.
- **H11:** `cells-freeze.sharing.cursors.ring` dropped here, superseded
  by `cursors-indexed`. AGENTS.md's gate figures are dated 2026-11-05;
  updating them is the maintainer's file to change, so proposed only.
- **H9 and H12** stand as notes:
  - one of the insert's two error arms is redundant;
  - `rg.unlink` is not idempotent;
  - branches are nodes of kind 18 and form 3 that no port reaches, to
    be stated where a future sweep or mark will meet them.
- **F3** is this review's alone. The second reviewer did not raise the
  nothing-finished template.

## Proposals, ranked

Both reviews together:

1. F1 and H1: a ruling on where the proofs' source lives; then commit
   the aids and their snapshot, or act on the ruling, before the next
   law changes. This is the one finding where waiting can lose
   something not rebuilt.
2. F2 and H3: `insert_dup`; then `cxs_ab`. Then the record's sentence
   made to match what holds.
3. H4: cite run 340, measure the heads families, run `sharing.py
   compare` over the merge.
4. F3: how the nothing-finished template is served.
5. F6 and H2: the materializer's composition into a module of its own,
   the root's laws stated over it, with mutants.
6. F7 and H5: the docket ordered to close the loop: P6, then P8 and P9,
   then P5, P10 and P11 as one change of the invariant, then P7.
7. H8 and H7, each measured before it is adopted; H6 and H12 when the
   index is next touched.

Done in the review's commit: F4, F5, H10, H11's plan step, the proof
headers (H1), and run 340 recorded (H4).

## Questions for the maintainer

1. Proofs as sources (F1, H1). The main and serve proofs are written by
   Python that is not in git. Should proof files written by programs
   fall under `generated-sources`, with their generators in git (in Bend
   where they can be) and checked by the gate? Or should they be a
   recorded exception, with the aids kept in git as development tools?
   Or are they sources edited in place from now on?
2. One cursor a position (F2, H3). The decision calls it "a law". As
   merged it is a premise every serve law takes, with a kernel error as
   the run-time report. Which claim do you want:
   - a law of the index, that a duplicate insert is reported and the
     tree kept (`insert_dup`);
   - a law that freeze never asks for a duplicate, so the error cannot
     be reached from any program;
   - or the record's wording made to match what holds?
3. The materializer (F6, H2). Should its composition come under the
   laws, moved beside `cursor` and `leave`? Or do the laws stop at
   `glam/ring.bend` and the splice, with the materializer's wiring left
   to tests and the ladder?
4. A source with nothing finished (F3). Should the serve's laws cover a
   copy that is a single cursor at its root? Or is saying they do not
   enough?
5. Corruption, once reported (H7). Should a serve stop at the first
   error it reports? Or is the error count read when a value is forced
   enough?
6. Order (H5, and the second reviewer's question 6). Should the laws'
   loop be closed first (P6, then P5, P10 and P11)? Or should the next
   work on materialization or dead cursors come first, though it will
   change the invariant again?
7. Size (the second reviewer's question 2). Is there a size or check
   time past which a law is to be restated, so that its invariant holds
   by computation, rather than proved as it stands?

## The maintainer's answers

The maintainer, 2026-11-23, to the questions above:

1. Proofs as sources: "Yes. Users should be able to build with just
   Bend. Thus, generated sources via Python or even Blend should be
   checked in. Ideally, such sources include a comment that they're
   generated." Recorded: `generated-outputs-checked-in`
   (`cursor-laws.sources`).
2. One cursor a position: "Let's investigate making it a law first. We
   can back off if it's impractical." (`cursor-laws.dup`).
3. and 4. The materializer and the nothing-finished template: "we
   should favor laws over tests for any property important (for
   correctness or performance) or easy to express and enforce
   lawfully." The general decision the maintainer recalled is
   `docs/Proving.md`'s "Prove what is important, and what is easy",
   which no record held. Recorded: `laws-over-tests`
   (`cursor-laws.materializer`).
5. Corruption, once reported: "Yes. We won't push through glam
   implementation errors. This is different from user errors such as
   syntax issues." Recorded: `implementation-errors-stop`
   (`cursor-laws.stop`).
6. Order: "Ordering is up to you. Prepare a rough plan. Partition,
   merge, reorder tasks where it makes sense."
   (`docs/plans/CursorLaws_2026-11-23.md`).
7. Size: "I don't have any specific thresholds in mind ... Best we can
   do is watch the growth and occasionally take action to improve
   iteration speed." (`cursor-laws.watch`).
