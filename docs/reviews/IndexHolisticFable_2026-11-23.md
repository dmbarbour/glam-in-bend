# The cursors' index, merged: a holistic review (second reviewer)

Scope. The merge 2e4aeea of `cursor-index-spike` into main (main before
it 846f452; 90 commits, 38 files, +16,891 −5,962): a copy's cursors in a
crit-bit tree of the net's nodes (`cursors-indexed`), the tree's laws
(`glam/INDEX_LAWS.bend`), the serve's steps restated over `RG.px.ok`
(`glam/LAWS.bend`, `glam/SERVE_LAWS.bend`), the ring's laws and walks
retired. Read in full: AGENTS.md, the eight decision records the work cites,
the plan's `cells-freeze.sharing.cursors.index` and its steps, the code
(`glam/index.bend`, `ring.bend`, `materialize.bend`, `ring_model.bend`),
`glam/LAWS.bend` and `glam/SERVE_LAWS.bend`. Sampled: `docs/Proving.md`
(its diff and lines 340 to 441), `docs/Decisions.md` (its diff),
`docs/DistilledDesign.md` (searched: it does not speak of the ring or
the index), `glam/INDEX_LAWS.bend` (law names and three comments), the
mutants files (names, targets, headers), `glam/core.bend` (the serve's
ends, the first use, the error count), the proof files (headers, sizes,
names by grep; never read through), the two premises reviews (findings
and proposals) and the generators under `results/index_bits/` (out of
git; listed and grepped). Nothing was built or run; the gate was not
run. Findings say whether the merge introduced, worsened or inherited
what they describe. Each claim is marked [checked] (read in the
source cited) or [inferred] (reasoned, not verified). Written
independently of the first reviewer's review, which was not read.

Severities: blocking, should fix, consider, note.

## 1. Intent and outcome

What `cursors-indexed` set out to do, and what the merge shows:

- **The walks are gone.** [checked] `glam/ring.bend` is 135 lines of
  calls into `glam/index.bend`: `rg.find` is `X.ix.find`, `rg.unlink`
  reads the cursor's home and calls `X.ix.remove`, `rg.situ` is one read
  (`glam/ring.bend:21-34`, `:52-53`). No `pred`, no walk, no fuel taken
  from the heap's size. The record's "a lookup descends at most 33
  steps" is `ix.fuel` (`glam/index.bend:31-32`).
- **The tree is words of the net.** [checked] Nothing in
  `glam/index.bend` allocates a Bend value but the descent's small
  records; a branch is `P.node` at an insert and `P.free` at a removal
  (`:238`, `:297`).
- **The tree has laws of its own, tested first.** [checked] 41 laws in
  `glam/INDEX_LAWS.bend`, 42 mutations in `glam/INDEX_MUTANTS.txt` (22
  of `index.bend`, 17 of the model), and the model run beside the code
  (`glam/test_index_model.bend`), wired into the gate's ladder
  (`scripts/ladder.py:82`).
- **The serve's steps are restated and compose once as laws.**
  [checked] `serve_pend` is stated as `copy_pend` then `crossings_pend`
  (`glam/SERVE_LAWS.bend:76-118`); each step law concludes the invariant
  and the words full (`step-laws-conclude-next-premises`).
- **The ring's laws and code are retired by disposition**, each mutant
  classified first (the plan's `.retire`). This is the most careful part
  of the work and worth keeping as the method (`docs/Proving.md`,
  "Retire laws by disposition, mutants first").

The work delivers the performance intent and a real body of proof. What
it does not deliver, against its own records, is in the findings: one
promised law (H3), a measurement of the merged code (H4), laws that
reach the materializer's own code (H2), and a way for anyone but this
container to change the proofs (H1). None is a correctness fault found
in the code; I found no crash path in `glam/index.bend` reachable from
user input (section 4).

## 2. Findings: how the proofs are kept

### H1. The main and serve proofs are generated sources in fact, kept by generators out of git — should fix, wants a ruling (inherited practice, much worsened)

Evidence [checked]:

- `glam/PROOF.bend` grew from 848,650 bytes (4,607 lines, at 846f452) to
  2,823,804 (3,819 lines); `glam/SERVE_PROOF.bend` from 410,658 to
  1,547,848; `glam/INDEX_PROOF.bend` is new at 1,000,437. In
  `PROOF.bend` 403 lines exceed 2,000 characters and the longest is
  62,811; its 268 definitions average 10 KB. Text of that shape is not
  edited by hand.
- `results/index_bits/regen.sh` (gitignored: `.gitignore:3:results/`)
  says of itself "authoring aid: glam/PROOF.bend's index sections
  regenerated from the snapshot before them, stage by stage", and its
  first act is `cp $B/PROOF.before_cpend.bend
  /workspaces/glam-in-bend/glam/PROOF.bend`, then 18 Python stages in
  order, the last a reachability cut (`CUT_ONLY=1 python3 -I
  $B/retire/retire.py`). Those stages and `sv/gen_cpi.py`, the serve
  proof's, are 4,551 lines of Python with 31 `.replace(` or `re.sub(`
  calls on text already emitted; the directory as a whole holds 16,172
  lines, backups and the index proof's one-off aids among them, with
  nothing marking which are live. `sv/gen_cpi.py:526` builds its
  namespace by `exec` of a slice of `gen_j1.py`'s text.
- The files disagree about what they are. `glam/INDEX_PROOF.bend:52-54`:
  "About half of this file was written by authoring aids ... text
  written once, kept by hand since; not generated sources."
  `glam/SERVE_PROOF.bend:3-4`: "written by a generator kept out of git
  (results/proofgen/gen_serve.py)", while the plan names
  `results/index_bits/sv/gen_cpi.py` for its `cpi` section.
  `glam/PROOF.bend`'s header says nothing of generation, though
  `regen.sh` rewrites it wholesale.
- `scripts/check_generated.sh` lists neither file; no decision record
  exempts proofs (`grep -rn "authoring aid" docs/decisions AGENTS.md`
  finds nothing).
- The snapshot a regeneration starts from,
  `results/index_bits/PROOF.before_cpend.bend` (848,811 bytes), is
  itself out of git: it equals no version of `glam/PROOF.bend` committed
  from 846f452 to the merge (`cmp` against each). Whether `regen.sh`
  reproduces the committed `glam/PROOF.bend` today is not known
  [inferred: I did not run it, since it overwrites the file].
- Inherited: the serve proof's header read the same at 846f452, so the
  practice predates the branch; no plan, review, record or
  `docs/Proving.md` names `results/proofgen/` (grep), so it was never
  put to the maintainer as a practice. Worsened: the main proof file,
  whose text at 846f452 names no generator, joined it and tripled.

Why it matters. AGENTS.md: code "is generated, by a Bend program where
possible, into files of its own that nobody edits; list each in
`scripts/check_generated.sh`"; "Python is a development tool, never the
source"; and the user's own note that `/tmp` and containers are not
durable. The committed proof is checked by the gate, so soundness does
not rest on the generators. Maintainability does: a fresh clone holds
2.8 MB of proof text whose only practical editor is 16 K lines of
Python and a snapshot that exist in one container. The plan's own
account of changing three premises (`.premises.implied`) names five
generators rerun.

What changing one law costs today [inferred from the above and the
coupling below]: restate the law; find its stage among the generators;
edit Python that emits Bend by string templates; run `regen.sh`, which
replays every stage from the snapshot; run `one_law` and its mutants;
and hope no later stage's `.replace(` anchored on text the change moved.
The coupling: `glam/PROOF.bend` calls 41 lemmas of `INDEX_PROOF.bend`
by name 769 times (`XP.`), and `SERVE_PROOF.bend` 36 of `PROOF.bend`'s
(`GP.`); only `serve_pend` is proved "through the steps' laws" as
`step-laws-conclude-next-premises` describes.

Proposal, in order:

1. Ask the maintainer for a ruling (question 1 below): are proof files
   exempt from `generated-sources` as checked artifacts whose authoring
   aids are disposable, or are they generated sources?
2. Whatever the ruling, commit the aids and the snapshot they start
   from (under `tools/` or `glam/proofgen/`, named as development
   tools), so that a clone can do what this container can. This is a
   copy, not a rewrite.
3. Make the three headers say the same true thing, and say which
   sections an aid wrote.
4. If the ruling is "generated": one generator per proof section that
   prints its section, no replay from a snapshot, no patching of
   earlier output, listed in `scripts/check_generated.sh`. That is a
   plan step of its own, and the place to shrink the text: the 62 K
   lines are goals restated in full at each rewrite, which lemmas over
   named sub-terms would cut.

### H2. No law and no mutant reaches `glam/materialize.bend` — should fix (inherited boundary; the merge added code beyond it)

Evidence [checked]: `glam/LAWS.bend` imports `ring.bend`,
`ring_model.bend`, `index_model.bend`; `glam/SERVE_LAWS.bend` adds
`splice_copy.bend` and the models; neither imports
`materialize.bend`. Every mutation in `glam/MUTANTS.txt` is of
`ring.bend` (28 of 28), every one in `glam/SERVE_MUTANTS.txt` of
`splice_copy.bend` (5 of 5). The serve the laws speak of is a term
written out in each law's statement, for example `serve_ring_exact`'s
`R.leave(Pair.snd(..., R.crossings(cs, (SM.map(S.sp.links(ls,
S.sp.nodes(ts, 0, ...)))...), s)), (Array.get(..., rn) + rp), nc)`
(`glam/SERVE_LAWS.bend:230`), which mirrors by hand what `mz.sp`,
`mz.sp.r`, `mz.root` and `mz.root.e` compute
(`glam/materialize.bend:47-67`). The law's comment says "read through
the map as the materializer reads it, mz.root" (`:172-173`); nothing
checks that it is.

So these are outside every law and every mutant:

- `mz.root.e`'s port `(n + p : U32)` and the `at_root` test
  (`glam/materialize.bend:47-58`);
- the order "crossings, then the root's leave" (`:60-67`);
- `sv.front.c`'s compare, added on this branch to stop a double free
  (`:202-207`, `:357-362`): swapping its arms fails no law, though a
  test does catch it (`front_self`, `glam/test_materialize.bend:260-265`,
  which calls `M.sv.front.m` with the served cursor found);
- the frontier's `R.join(h, nc, c)` and the static's
  `R.leave(h, P.era(), nc)` as call sites (`:207`, `:234`): the laws
  `join_pend` and `leave_era_pend` cover the callee, not that the
  arguments are these;
- the one-net path's own wiring (`materialize1`, `serve1`,
  `:289-423`). It calls the same `mz.sp` (`:295`), and the laws are
  host-side only, so they apply to its splice and crossings as to any
  [inferred]; its mutants are of the core ("the one-net serve refused",
  the plan's `cells-freeze.nested.self`), not of this file.

The boundary is inherited: at 846f452 the laws imported the same
modules and the mutants were of `ring.bend` (40) and `splice_copy.bend`
(5). The merge added `sv.front.c` beyond it and restated every serve
law without moving it. The ladder's samples exercise all of this, so a
gross fault would show; the laws would not.

Proposal: move `mz.sp`, `mz.sp.r`, `mz.root`, `mz.root.e` into a small
module of their own importing `ring.bend`, `splice_copy.bend` and the
template (not into `ring.bend`, whose laws "import the heap's
primitives alone", `glam/ring.bend:45-47`; `SERVE_LAWS.bend` imports
all three already), and state `serve_pend`,
`serve_ring_exact` and the two frames over that function, their
statements shrinking with it. Add mutants there (root port one past,
`at_root` ignored, leave before crossings). `sv.front.c` keeps its
test until its law comes (`cells-freeze.nested.host.join.self`,
tentative).

## 3. Findings: the laws

### H3. "One cursor a position ... and a law" is a premise, not a law — should fix (introduced: the record is this work's)

Evidence [checked]. `docs/decisions/cursors-indexed.md:41-42`: "One
cursor a position in a copy: an insert meeting its own key is a kernel
error, the tree unchanged, and a law." What the merge holds:

- The plan restates it in passing as something weaker: "one cursor a
  position a law (an insert's premise that its key is absent)" (the
  plan's `.index.ring`). `insert_tree` and `cursor_pend` take the
  absence as a premise (`glam/LAWS.bend:115`, `ha`); no law says what an
  insert meeting its key does. `insert_dup` is on the docket, tentative
  (`docs/plans/Cells_2026-11-09.md:952`).
- `glam/index.bend:24-25` still says "(one cursor a position in a copy,
  a law to come)".
- The serve takes the absence stepwise over the model
  (`RG.cxs.ok`, `glam/ring_model.bend:483-492`), which a caller can
  discharge only by running the model's fold. The bridge from "the
  crossings' positions distinct and absent at the start" is "still
  owed" (`docs/plans/Cells_2026-11-09.md:969`; `cxs_ab`, tentative).
  And nothing says the crossings are such:
  `serve-premises-over-index` item 1 gives the obligation to "the
  serve's caller"; the crossings are built by `glam/freeze.bend`
  (`glam/ring.bend:100-104`) and handed on by `glam/materialize.bend`,
  neither under a law that speaks of positions.

So the property the record names as the reason dead cursors are kept
has three layers, none closed: the index's behaviour on a duplicate
(no law), the fold's premise from a start condition (no law), the
start condition from freeze (no law, and no plan step I found that
names it).

Proposal: amend the record's wording to what holds (a premise, with the
kernel error as the run-time report), or build `insert_dup` now: it is
the cheapest of the three (the review's S/M), its code path is five
lines (`ix.put.n`, `glam/index.bend:250-255`), and it is the only one that says a
fault here is *reported* instead of silently mis-wiring. Then `cxs_ab`
before any further law is stacked on `RG.cxs.ok`.

### H5. The invariant has no beginning and no life between serves; this is on the docket, but it is the frame every claim sits in — consider (ordering)

Evidence [checked]. `docs/reviews/IndexPremises_2026-11-23.md`'s P5 to
P11, tentative under `.premises.later`
(`docs/plans/Cells_2026-11-09.md:947-957`): the live nodes distinct in
the invariant (P5), `situate_pend`, the first index's writes giving the
invariant (P6), `join_links` and `leave_links`, that the wire is made
(P7), `cxs_ab` and `cxs_room` (P8), `insert_dup` (P9), layout, bases
and past in the invariant (P10), `px_sub` and `px_grow` (P11).

Read together, what the merged laws say is: *if* `RG.px.ok` holds of
some lists `I, L, F, N` with the fresh nodes the free list's first, the
nodes laid out, past the header, the live nodes distinct, the template
and crossings well formed and the crossings' stepwise premise, *then*
one serve's host-side writes keep `RG.px.ok` of other lists and write
only a stated region. Not yet said, each acknowledged somewhere in the
plan or the reviews:

- that the invariant ever holds (P6): the core lays the first index out
  by hand (H8);
- that one serve's conclusion is the next serve's premise: the
  conclusion's lists are `M ++ pls` and the crossings' `F`, the next
  premise's `M' ++ ns` and `ns ++ F'` with `ns` as many as the next
  template makes (`glam/SERVE_LAWS.bend:65-68`); `px_grow` and
  `distinct(L)` are owed;
- that the host's own reduction between serves keeps it: interactions
  link the ports cursors face, take and give free nodes; no law of the
  kernel is stated against `RG.px.ok` [inferred: I found no such law
  named in the plan];
- that a join or a leave makes the wire (P7): `_pend` says the
  invariant survives, `_keeps` what is not written; a join that linked
  nothing at all would be caught only through `px.tw`'s clauses, by
  accident of the witness [inferred];
- growth: every law fixes the depth `d`; `P.node` at an empty free list
  doubles the store (`spike/kprim.bend:486-518`), after which no law
  applies ("Not claimed: growth", `glam/SERVE_LAWS.bend:38`).

This is honest in the plan. It is less visible in the records:
`cursors-indexed`'s consequences say "the serve's laws are restated
over it", and a reader takes "the serve is proved". Proposal: one
paragraph in the plan's `.index` step (or `docs/Proving.md`, "What to
claim") stating the frame above in these words, and the docket ordered
by what closes the loop a caller needs: P6, then P8 and P9 (H3), then
P5/P10/P11 together as one invariant change, then P7. P10 is worth
doing early for a second reason: `layout`, `bases` and the words full
are four premises repeated on all 16 laws.

### H6. Index laws nothing uses, and laws no mutation names — consider

Evidence [checked, by grep of `XL.<law>` in `glam/PROOF.bend` and
`glam/SERVE_PROOF.bend`, and of each law's name on the `===` lines of
the mutants files]:

- Never named in a downstream proof file, as a law (`XL.`) or through
  a lemma of its proof (none of the 41 `XP.` names `PROOF.bend` uses is
  theirs; the bare names occur in neither file): `at_first`,
  `put_leaves`, `put_flsep`, `del_flsep`, `del_drop`, `look_member`;
  and `ne_found`, `look_at`, which the index's own proofs mention 8
  and 12 times [inferred: used there]. `at_first`
  (`glam/INDEX_LAWS.bend:238-252`) equates the index's lookup with
  `RG.first`, "so that a find on the index gives what the ring's
  find_exact gave": a bridge to a law retired in this merge.
  `RG.first` and `RG.pos.is` (`glam/ring_model.bend:104-129`) are
  named in `INDEX_LAWS.bend` and `INDEX_PROOF.bend` alone.
- Named by no mutation: `layout_ok`, `del_flsep`, `del_sub`,
  `chain_kept`, `free_full`, `insert_full`, `remove_full`, `del_bsub`.
  The `_full` three are structural (a write keeps an array full) and a
  mutant would be artificial; `chain_kept` and `del_sub` are not, and
  AGENTS.md asks that the code a new law follows be mutated.

Proposal: a disposition pass like `.retire`'s over the index's 41 laws:
for each, the downstream proof that calls it or the reason it stands
alone (a specification, like `look_at`); retire `at_first` and its
model with the maintainer's approval, or say what future law wants it;
a mutant or a stated reason for each of the eight.

## 4. Findings: the code

Read for crash paths first. `glam/index.bend`'s three loops are fueled
by `ix.fuel()`, 33 (`:31-32`), each ending in `P.err_if` when the fuel
is spent (`ds.out` `:133-136`, `pl.out` `:209-212`, `rm.out`
`:321-324`); a removal reaching a node that is no branch raises the
error (`rm.br`, `:314-315`); an insert meeting its key raises it
(`:253`, `:246`). `P.node` at an empty free list grows the store and
does not stop (`spike/kprim.bend:486-518`). The corruption the
materializer reports ends the run with a diagnostic, not a fail-stop:
`err(msg)` is `RDone{OErrs{[G.Diag{0, msg}]}}` (`glam/core.bend:371-372`,
`:1074`, `:1138`). I found no Bend fail-stop reachable from user input
through this code [checked for the paths above; inferred for the
whole]. Two remarks on corrupt trees only: `ix.bitof` turns a header's
24-bit field into a `Nat` (`glam/index.bend:39-40`,
`spike/kprim.bend:766-767`), so a
corrupt branch may name a bit far past 31, which `ix.side` then shifts
by; the fuel still bounds the descent [inferred: I did not check what
`>>` by a large `Nat` costs].

### H7. A reported index error does not stop the serve that met it, and a refused insert leaves a cursor with no home — consider (the error's late reading inherited; the refusal introduced)

Evidence [checked]. `cursor` writes the placeholder's header and word 2
and then inserts (`glam/ring.bend:48-49`). On its own key the insert
returns `P.err_if(True{}, h)` with nothing else written
(`glam/index.bend:250-255`): the node now has a cursor's header and
position and whatever its word 3 held, in no index. The crossings go
on (`glam/ring.bend:120-125`), the serve returns `SvOk`, and the error
count is read where a cell's value is forced
(`cell.done`, `glam/core.bend:1254-1259`: "the kernel reported errors
forcing a value") or at the run's end (`:209-217`). Between the two,
the host may stop at that cursor and the core read its word 3 as a
situating node (`frame.at.p`, `:815-817`), then that node's word 2 as
a source's number (`frame.at.s`, `:811-813`).

The same holds of a descent out of fuel: `ix.found` reads word 2 of
whatever node the descent stopped at (`glam/index.bend:166-169`) and
may hand back a branch as a cursor.

The count was read there before the branch too (the same message at
846f452, `glam/core.bend:1253`); what is new is an operation that
refuses half way. This is `corruption-reported-when-cheap` as ruled ("detect and return
the memory corruption error"), and the run does end in an error. The
question is only how far a net known to be corrupt is driven first; I
could not show a crash from it [inferred: `srcs.take` on a wild number
ends at `SrcOut`, `glam/core.bend:404-413`].

Proposal: the frame that receives a serve's end already holds the host;
one read of the error count there (`P.stats`, as `sv.climb.f` already
does for the capacity) turns "reported at the end" into "reported at
the serve", at a read a serve. Measure before adopting, as `sv.front.c`
was (71 instructions in 106 million). Short of that, order `cursor`'s
writes so that a refused insert leaves the placeholder a placeholder:
the header after the insert, word 2 before it (the insert reads only
word 2, `glam/index.bend:282-283`; `insert_tree`'s premise on the header would move to
the caller, so this costs a law's restatement and wants weighing).

### H8. The core lays out the first index by hand — consider

Evidence [checked]. `glam/core.bend:774-779`: `use.cursor` writes the
leaf's header, its position `P.iface()` and its word 3 `situ`;
`use.situ` writes the situating node's word 3 `leaf`. The comment above
(`:767-771`) still says "in a ring of its own ... laid out as
glam/test_materialize.bend's ring". The record allows it: "A tree of
one cursor is the words of a ring of one"
(`cursors-indexed`), and the plan notes "the core's first use builds it
as it did". But the tree's layout is now written in two modules, and
the one outside `glam/index.bend` is the base case no law covers (P6,
`situate_pend`).

Proposal: either `use.situ` calls `R.cursor` on an empty index (the
situating node's word 3 first set to itself; `ix.put.k`'s empty arm
makes the same two writes, `glam/index.bend:268-269`), so that
`cursor_pend` is the base case and P6 shrinks to "a fresh situating
node is an empty index"; or keep the hand layout and say so in
`glam/index.bend`'s header, with a test that the two agree. The first
costs three reads at each first use; measure on the sharing families.

### H9. Small things in the code — note

- [checked] `ix.put.n` refuses equal keys (`glam/index.bend:250-253`),
  and `ix.put.c` refuses a scan that found no differing bit
  (`:244-246`), which `ne_found` says happens only for equal keys. One
  of the two error arms is unreachable. The first saves a 32-step scan
  on a path that is an error anyway; the second is what the law's shape
  needs. Worth a comment saying which is the boundary and which the
  redundancy (AGENTS.md: "When removing a check, tell redundant work
  from a deliberate boundary").
- [checked] `ix.rm.k`'s only-leaf arm resets the situating node's word 3
  and leaves the removed cursor's word 3 pointing home
  (`:344-347`); harmless, since every caller frees the cursor next
  (`glam/ring.bend:60`, `:73`, `:129`), but `rg.unlink` alone is not
  safe to call twice. No caller does.
- [checked] The names: `ring.bend`, `ring_model.bend`, `RG`, `rg.*`,
  `serve_ring_exact`, `RG.cxs` beside `IM.ix`. Both files say so in
  their headers ("The names (rg.*) are the ring's the index replaced").
  A rename is mechanical for the code and costly for the proofs while
  H1 stands; it belongs after H1, not before.

## 5. Findings: measurements and documents

### H4. The record's figures and the plan's differ, neither names its commit or run, and the merged code's flatness has no guard — should fix (small; introduced)

Evidence [checked]. The same workloads, instructions an element at 100
elements and at the largest size:

| | `cursors-indexed.md:49-52`, `:58` | the plan's `.index.spike`, `:698-702` |
|---|---|---|
| `deep` | 204K, 193K at 1,600 | 204K, 192K at 1,600 |
| six heads | 476K, 467K at 400 | 475K, 464K at 400 |
| eight heads | 586K, 575K | 583K, 572K |
| `seq` | "unchanged, about 190K" | 202K, 191K (main 201K, 189K) |
| the ladder | −0.02% to +0.26% | −0.02% to +0.34% |

The likely cause [inferred from commit times]: the plan's figures are
the first spike's (0c23393, 2026-11-22 19:16); the code was then
reshaped for the laws (597b2d4 "bits from the lowest", 21:59; 8b3106f,
22:47) and the record written after (ebf66f0, 23:47). Neither text
says so, neither cites a store run or a commit, and AGENTS.md asks for
both ("record other bulk runs there too, and cite run ids where a plan
reports what they found"; counts "recorded with the Bend version, the
commit and the CPU"). After the record, the code changed twice more:
the dead walk out (measured, "within 5 of 106 million", the plan's
`:1161`) and
`sv.front.c` (measured, within 71). Those two are on the sharing
samples at one size each, not on the families at n, 2n, 4n that the
record's claim is about. `seq` "unchanged" sits beside a plan figure
that is 0.5% to 1% above main.

And nothing in the gate would notice the flatness lost:
`cells-freeze.sharing.cursors.growth.gate` is tentative
(`docs/plans/Cells_2026-11-09.md:637-644`), and the growth family
bounds interactions, which the index's steps are not.

Proposal: one run of `deep`, the heads families and `seq` at n, 2n, 4n
on 2e4aeea, recorded in the store with `scripts/results.py`, its run id
and commit cited in the record's performance paragraph and in the
plan's `.index` step, the spike's figures marked as the first spike's.
An AGENTS.md check besides, which the plan's index steps (lines 645
to 1165) do not mention: `sharing.py compare` over the merge, since `ds.run` now has two callers
(`ix.find.k` and `ix.put.k`, `glam/index.bend:176`, `:271`) and "a
second caller splits a function into a segment of its own".

### H10. Comments and headers that still describe the ring — should fix (small)

The premises review's P4 fixed `ring.bend` and `ring_model.bend`; its
"Not done" lists "The materializer's and the core's comments still say
ring" (`docs/reviews/IndexPremises_2026-11-23.md:146`). They still do
after the merge [checked]:

- `glam/materialize.bend:17`: "A copy's cursors form a ring in the
  host's heap through word 3"; `:29-31`: "looked up in the ring ... put
  in the ring"; `:32-35`; `:46`: "which leaves its ring"; `:106`: "its
  wires joined in situ's ring"; `:135`: "a position the ring holds";
  `:174-175`: "a well-formed source and ring". The file's header is
  the first thing a reader of the serve meets, and word 3 no longer
  links anything round.
- `glam/core.bend:768-770` (H8), `:821`: "a ring served from the
  source", `:909`.
- `glam/freeze.bend:334`: "a crossing of the ring the copy joins".
- `glam/index.bend:24-25`: "a law to come" (H3).
- `glam/INDEX_LAWS.bend:67-69`, on `remove_tree`: "Not claimed: that
  the parent is freed ..., which the realization does not read; the
  serve's laws over the free list will." `remove_free` (`:286`) claims
  it now.
- `glam/SERVE_LAWS.bend:1-5`: "joined to the ring's crossings ... so
  that the ring's laws keep their imports"; `glam/SPLICE_LAWS.bend:3`.
- `glam/SERVE_MUTANTS.txt:1`: "the code the serve's laws follow
  (glam/splice.bend)", every mutation there being of
  `splice_copy.bend`.
- `glam/PROOF.bend:1-55`: fifty lines of lessons "learned on the
  ring's proofs, retired with it", naming lemmas only "git before
  ebc5887 keeps". `docs/Proving.md:242-244` already keeps this
  convention for the standing doc; in the proof file a maintainer needs the
  lessons of the index's own sections, which the header does not hold:
  it has this one paragraph and no other.

Proposal: one commit of comments; no law changes, so no trailer.

### H11. Leftovers in the plan and the rules — note

- [checked] `cells-freeze.sharing.cursors.ring` is still listed
  "tentative — the ring's walks cut, its simple shape kept"
  (`docs/plans/Cells_2026-11-09.md:1166` on), two pointers and a sorted
  ring. The index made it moot; it should be closed as superseded by
  `cursors-indexed`, or reduced to the one idea that survives (the
  crossings sorted by far end, if any workload wants it).
- [checked] AGENTS.md's gate figures are dated 2026-11-05 ("near 200 s
  when the spike does, its verdict 57 s and the library 96 s"); the
  plan reports the full gate at 195 s with the main and serve proofs'
  verdicts at 70 s and 76 s (`docs/plans/Cells_2026-11-09.md:1157`). The glam verdicts are now the
  gate's longest sections whenever `glam/index.bend` or a model
  changes, and three proof files chain (`INDEX_PROOF` into `PROOF`
  into `SERVE_PROOF`), so a change to the index rechecks all three. A
  line in AGENTS.md's Gate section would say so.
- [checked] `hub-laws-reused` asks that the plan say which hub laws a
  proof relies on; the plan's `.premises.implied` does, by name, for
  lawful-words. Good. `docs/BendIssues.md` gained the two stack
  overflows met on the way. Consistent with what was built.
- [checked] `corruption-reported-when-cheap` and
  `ring-ports-faced-off-positions` are restated for the index and read
  true against `glam/index.bend` and `RG.port.ok`, `RG.po.n`.
- This review is not listed in `docs/reviews/README.md` (I was asked to
  write one file only); the gate's docs check will want it there.

## 6. Other things to know before building on this

### H12. Branches are reached through no port — consider (a question to settle before collection or marks touch a host)

[checked] `glam/index.bend:19-20`: "Nothing links to a branch through a
port, so no walk of the kernel's meets one." A branch is held only by
its parent's word 2 or 3 or the situating node's word 3; the situating
node itself only by its cursors' words 3 and its branches. [inferred]
Any future pass that decides liveness by reachability through ports,
or that sweeps the store by header kind (the marks of
`cells-freeze.sharing.cursors.growth.marks`, a collector of hosts, a
whole-net freeze of a host that is itself a source), will meet nodes
of kind 18 and form 3 that its rules have never seen, in the one-net
case inside the very net being frozen. With the ring every member but
the situating node was a cursor and faced something. Proposal: state
in `cursors-indexed`'s consequences that forms 2 and 3 of kind 18 are
store the kernel's walks neither enter nor may free, and give
`spike/net.bend`'s and `krules`' `case 18` a line saying what form 3
is, so that the next author of a sweep finds it.

### What is solid

So that the findings above are read in proportion [checked unless
marked]:

- The index's code is small, fueled, and shaped for its laws; its model
  was run beside it before any proof; its mutations are of the code
  that matters (descents, sides, the place of a branch, the root, the
  home, the free list on both operations).
- Every mutation in `glam/MUTANTS.txt` is of `glam/ring.bend`, 28 over
  135 lines, most with a witness built by the kernel's own writes, so
  that the step laws' premises are shown satisfiable together.
- The retirement was done by disposition and left no orphan mutant.
- The laws' "Not claimed" lines are specific (`leave_era_pend`'s frame,
  `serve_ring_exact`'s two-way links after the leave and its obligation
  on freeze), and the docket in `.premises.later` matches what the two
  premises reviews found.
- The law check now reads every laws file (`laws-files-all-checked`),
  found by a trial merge: the process caught its own gap.

## 7. What I would do first

1. **H1, steps 2 and 3**: commit the authoring aids and their snapshot
   as development tools, and make the three proof headers true. Hours,
   no law touched, and it is the one finding where waiting loses
   something that cannot be rebuilt (a container).
2. **H4**: measure the merged commit at n, 2n, 4n, record the run, fix
   the record's and the plan's figures. An hour; it is the evidence the
   decision record rests on.
3. **H10 and H11**: the comments and the stale plan step, one commit.
4. **H3**: `insert_dup`, and the record's sentence made to match what
   holds; then `cxs_ab`.
5. **H2**: the materializer's composition moved beside `leave` and the
   serve laws stated over it, with mutants. This shortens the serve
   laws' statements too, which helps H1.
6. **H5**: order the docket P6, P8/P9, then P5/P10/P11 as one invariant
   change, then P7; write the frame of the claims in one place.
7. **H8**, then **H7**, each measured before adopted.
8. **H6** and **H12** when the index is next touched.

H1's step 4, proofs as generated sources proper, waits on the
maintainer's ruling.

## 8. Questions for the maintainer

1. **Are proofs sources?** `generated-sources` speaks of code needed in
   variants. A proof the kernel checks is safe whoever wrote it, so one
   answer is that proof text is an artifact and its authoring aids
   disposable. But then the only way to change a law is to write its
   proof again from nothing, or to keep the aids after all. Should
   proof files written by programs fall under `generated-sources`
   (generators in git, in Bend where they can be, checked by the gate),
   or be a recorded exception with the aids kept in git as development
   tools?
2. **How large may the proof of a step be?** The serve's five laws and
   the ring's eleven now rest on 4.4 MB of proof beside the index's
   1 MB. Is there a size, or a check time, past which a law is to be
   restated (the invariant reshaped so that it "holds by computation",
   as AGENTS.md prefers) instead of proved as it stands? P10 of the
   premises review is one such reshaping.
3. **What should "one cursor a position" mean as a claim?** A premise
   every serve law takes, with the kernel error as the run's report (as
   merged); a law of the index that a duplicate is reported and the
   tree kept (`insert_dup`); or a law that freeze never asks for one,
   so that the error is unreachable from any program? The third is the
   one that says dead cursors do their job.
4. **Should a serve stop at the first corruption it reports?** Today
   the error is counted and the cell's value refused when forced. A
   read of the count where a serve ends would stop sooner, at a cost a
   serve; `corruption-reported-when-cheap` reads either way.
5. **Is the materializer's own code to come under the laws**, by moving
   its composition beside the cursors' as `cursor` and `leave` were, or
   are the laws meant to stop at `glam/ring.bend` and the splice, the
   materializer's wiring left to tests and the ladder?
6. **Is the laws' frame, one serve from a state nothing yet
   establishes, the intended stopping point for now?** If the next
   work is coarser materialization or forgetting dead cursors (the
   record's option C, the removal criterion), each will change the
   invariant again; closing the loop first (P6, P5/P10/P11) may be
   wasted, or may be what makes those changes safe. Which comes first?
