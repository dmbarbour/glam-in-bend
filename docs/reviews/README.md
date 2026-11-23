# Reviews

A review checks work against intent: a design, a plan's steps, a subsystem.
It lists findings, each with a stable ID (`F1`, `F2`, …; write
`<Review> F3` where ambiguous) and a verdict.

- **Quote what you find.** A finding cites the text or code it is about,
  with its location. A claim relayed from another reviewer or agent is
  checked against the source before it is reported.
- **Small fixes go in the review.** A finding may be fixed in the commit
  that records it, or by follow-ups citing its ID. Work that needs steps of
  its own becomes a plan.
- **Files and retirement follow [plans](../plans/README.md):**
  `docs/reviews/<Topic>_<YYYY-MM-DD>.md`, listed below while active, and
  retired by extracting decisions and removing references, then deleted
  with its last commit listed.

## Active Reviews

- [`Direction_2026-11-09.md`](Direction_2026-11-09.md): the direction
  glam-in-bend has taken, the spike against the path to the product, and
  what to do or stop doing to get there; drafted for the maintainer at
  their request.
- [`Heap_2026-11-09.md`](Heap_2026-11-09.md): the heap's options and
  intentions toward high parallelism, where the current plans hinder
  it, and alternatives free of the Rust bootstrap and the sketch: heaps
  per net, nets as heaps; two reviewers, the agent and Fable; drafted
  for the maintainer at their request.
- [`HeapFable_2026-11-09.md`](HeapFable_2026-11-09.md): the second
  reviewer's review of the same question, by a Fable sub-agent, kept as
  written beside `Heap_2026-11-09.md`, which summarizes it.
- [`InsideData_2026-11-10.md`](InsideData_2026-11-10.md): the design
  round of `cells-lazy-data`, on how data holds a function's net, frozen
  or live. Revised after three rounds of the maintainer's answers.
  - The first draft's closures are withdrawn because they lost the work
    of partial applications.
  - The build already loses that work in two places (measured).
  - A function in data is a live template, the maintainer's batch
    materialization: finished parts frozen, unprocessed ones behind
    cursors in the source.
  - Whole copies first are dropped. Within a net, the agent reads the
    third round as cursors with linear moves, which awaits the
    maintainer's confirmation, as does the cursor design.

  Drafted for the maintainer.
- [`Cursors_2026-11-10.md`](Cursors_2026-11-10.md): how a live
  template's copy joins its cursors, which the maintainer raised with the
  identity function's aux-to-aux wire. A brainstorm by the agent,
  compared with the second reviewer's. Recommended: finished as a
  fixpoint, a copy made nodes then links, and placeholders by polarity
  threaded per copy, after laws for monotone finishedness; five
  questions. Drafted for the maintainer.
- [`CursorsFable_2026-11-10.md`](CursorsFable_2026-11-10.md): the second
  reviewer's brainstorm on the same question, by a Fable sub-agent, kept
  as written beside `Cursors_2026-11-10.md`, which compares the two.
- [`Demand_2026-11-11.md`](Demand_2026-11-11.md): demand for copying and
  fusion, at the maintainer's request: what demand does by polarity and
  scoping, what demand through a value's negative auxiliaries would
  mean, fans, positioned demand for live templates. Compared with the
  second reviewer's opinion. Recommended:
  - demand to weak head normal form at the root, unchanged;
  - positioned demand at cursors;
  - bounded head demand as early evaluation, before a source's first
    copy.

  Six questions. Drafted for the maintainer.
- [`DemandFable_2026-11-11.md`](DemandFable_2026-11-11.md): the second
  reviewer's opinion on the same question, by a Fable sub-agent, kept as
  written beside `Demand_2026-11-11.md`.
- [`HeadDemandFable_2026-11-11.md`](HeadDemandFable_2026-11-11.md): the
  second reviewer's analysis of head demand without fuel, by a Fable
  sub-agent, kept as written; compared in `Demand_2026-11-11.md`'s
  second round.
- [`Positions_2026-11-11.md`](Positions_2026-11-11.md): busy state and
  tracking for the positions a live template's copies demand, at the
  maintainer's request. Two investigations compared. Proposed:
  - busy as a task at the position, nothing stored in the source;
  - a suspended walk keeping no path and walking again from its
    position;
  - cursors as handles served like needs, each copy pulling its own
    result.

  Drafted for the maintainer.
- [`PositionsFable_2026-11-11.md`](PositionsFable_2026-11-11.md): the
  second reviewer's investigation, by a Fable sub-agent, kept as
  written.
- [`Joins_2026-11-11.md`](Joins_2026-11-11.md): how a live template's
  copy joins its cursors.
  - A ring of cursor nodes for each copy in the host's heap, with two
    rules: copy fans wait at negative cursors, and positive cursors
    never interact.
  - Joins at any outstanding cursor of the copy, cursor to cursor
    included.
  - Reviewed in depth by the second reviewer, who confirms the copy's
    side but finds that events and the sweep break the stability of
    positions in a source.

  Six questions. Drafted for the maintainer.
- [`JoinsFable_2026-11-11.md`](JoinsFable_2026-11-11.md): the second
  reviewer's review of that design, by a Fable sub-agent, kept as
  written.
- [`Levels_2026-11-12.md`](Levels_2026-11-12.md): what to prove to be
  confident in GAL levels across cursors, and how it fits a
  formalization of GAL over polarized nets, at the maintainer's request.
  - Shift equivariance of the rule table comes first, in Bend: the
    unproved premise of templates spliced at level too.
  - Probes found a source reduced at its own levels and copied whole
    agreeing with its recipe on every program tried. They also found
    the samples blind to controls.
  - The second reviewer adds the splice premise, fans pairing by level
    alone with no check of their identities, and an unguarded drop.

  A combined order of tests and proofs. Drafted for the maintainer.
- [`LevelsFable_2026-11-12.md`](LevelsFable_2026-11-12.md): the second
  reviewer's review of the same question, by a Fable sub-agent, kept as
  written.
- [`Hierarchy_2026-11-13.md`](Hierarchy_2026-11-13.md): live sources
  holding copies of sources, set beside the maintainer's hierarchical
  heaps, at the maintainer's request: a glossary both ways, re-entry and
  cycles, the kept walk under an inner frame's writes (docketed for a
  proof), and copies counted as cursor interactions. Compared with the
  second reviewer's: the finished mark and the stack as segments before
  the self copy, the proof as a path law and a write-set law, copies
  folded into the families' check. Drafted for the maintainer.
- [`HierarchyFable_2026-11-13.md`](HierarchyFable_2026-11-13.md): the
  second reviewer's review of the same question, by a Fable sub-agent,
  kept as written.
- [`ArrayLaws_2026-11-13.md`](ArrayLaws_2026-11-13.md): what other
  users have proven about Bend's arrays and words, for the proof ladder
  of `cells-freeze.nested.host`, at the maintainer's request:
  `lawful-arrays` proves its first rung and `lawful-words` the word
  arithmetic, both checked under glam's Bend with `--verdict`; what no
  package proves; deficiencies to present, by package. Drafted for the
  maintainer.

- [`JoinLaws_2026-11-14.md`](JoinLaws_2026-11-14.md): the join laws
  `join_keeps` and `join1_keeps`, explained word by word on a worked
  ring, at the maintainer's request. Their write set is coarser than a
  serve's next steps bear (a sharper law proved, a mutation and its
  witness to show it); cursors left listed after a join break the model
  at the next serve; the premises taken and how to derive them; set
  beside the second reviewer's, which adds the materializer's own joins
  and the positive laws missing. Four questions, answered; exact write
  sets then sketched and proved in a worktree for their tradeoffs.
  Drafted for the maintainer.
- [`JoinLawsFable_2026-11-14.md`](JoinLawsFable_2026-11-14.md): the
  second reviewer's review of the same laws, by a Fable sub-agent, kept
  as written.

- [`JoinExact_2026-11-14.md`](JoinExact_2026-11-14.md): `join_exact`'s
  fourteen premises, at the maintainer's request: sorted by cause,
  membership in place of splits, the walk's fuel taken from the heap,
  the model taught its nodes and their ports; set beside the second
  reviewer's, which adds the interference of rings, the materializer's
  other walks and joins, and the model route for nodes the agent then
  takes. Four questions. Drafted for the maintainer.
- [`JoinExactFable_2026-11-14.md`](JoinExactFable_2026-11-14.md): the
  second reviewer's review of the same law, by a Fable sub-agent, kept
  as written.
- [`Refs_2026-11-18.md`](Refs_2026-11-18.md): how references are
  encoded (statics at port bits `00`, a node's ports at `01` to `11`,
  the maintainer's question) and how far the laws state the encoding.
  The second review checked against the source, five findings added.
  Recommended: laws over a link word that is a `Maybe`, none for a
  static, first; the encoding decided with `netdata-refs`'s integer
  tag, before immediates land. Five questions. Drafted for the
  maintainer.
- [`RefsFable_2026-11-18.md`](RefsFable_2026-11-18.md): the second
  reviewer's review of the same question, by a Fable sub-agent, kept as
  written beside `Refs_2026-11-18.md`, which checks and extends it.
- [`Splice_2026-11-19.md`](Splice_2026-11-19.md): the splice's frame
  law, three questions with pros and cons (the fresh nodes, the
  template's premises, the header's words), the second reviewer's advice
  checked against the source. Recommended: the fresh nodes a premise
  now, the allocator's prefix law to discharge it; a template predicate
  discharged by a law on freeze; the header's words as an exact list. A
  fault to confirm first: an eraser node at a source's root. Drafted for
  the maintainer.
- [`SpliceFable_2026-11-19.md`](SpliceFable_2026-11-19.md): the second
  reviewer's advice on the same questions, by a Fable sub-agent, kept as
  written beside `Splice_2026-11-19.md`.
- [`Freeze_2026-11-21.md`](Freeze_2026-11-21.md): what freeze does, where
  it sits, what a fully evaluated net becomes, caching and compression;
  a discussion with the maintainer before the full review of freeze and
  templates. Their direction: finished trees cached per position, a
  wholly finished source frozen into its cell's value, early evaluation
  and net-layer GC finding nets to freeze; a bytecode with stacks the
  likely frozen form. Six findings; then the full review, the agent's
  recommendations and the second reviewer's checked against the source
  (three latent faults, a stale far end a cache must not keep),
  compared, with an order proposed.
- [`Erasers_2026-11-21.md`](Erasers_2026-11-21.md): every place an
  eraser node is treated otherwise than its static, the review
  `representations-interchangeable` asks for. Plain demand runs eraser
  events, so copied nodes are not kept from them (X1, correcting the
  freeze review); a whole freeze of a static root, positioned demand off
  the interface and freeze's count to fix; the collector's count to
  measure.
- [`RingIndex_2026-11-22.md`](RingIndex_2026-11-22.md): a copy's cursors
  indexed, the designs for the maintainer's discussion: what a serve
  walks (three walks, not one), the designs compared, where the agent and
  the second reviewer agree (replace the ring, word 3 naming the
  situating node, measure first) and differ (the index in the heap's
  nodes or a value in the data table); option B not low-hanging.
- [`RingIndexFable_2026-11-22.md`](RingIndexFable_2026-11-22.md): the
  second reviewer's brainstorm of index designs, kept as written.
- [`DeadCursorsFable_2026-11-22.md`](DeadCursorsFable_2026-11-22.md): the
  second reviewer's scouting of forgetting dead cursors (option B), kept
  as written: not low-hanging.
- [`Cost_2026-11-22.md`](Cost_2026-11-22.md): instructions against what
  they buy (`ladder-measure.roi`), first findings on the cursor
  workload: the machinery around the kernel is the cost, half of it
  Bend's reference counting on shared values; the core's book a list
  walked for each lookup, a splice's template a list, values dropped on
  branches that leave them; the front end a fifth. For the
  maintainer's direction before anything is trimmed.
- [`ClimbFable_2026-11-22.md`](ClimbFable_2026-11-22.md): the second
  reviewer's review of positioned demand's climb
  (`cells-freeze.sharing.cursors.growth.climb`): sound, but because
  finished is closed along the climb, not because walks stop at marks
  (they run to the root); the bound of eight fitted to one term and
  failing on wider cells, as measured; the climb to a known-finished
  node or the interface, fuelled by the source's nodes, then marks on
  every copied kind; laws on finishedness, not on the walk. Kept as
  written; its prediction checked.
- [`StacksFable_2026-11-22.md`](StacksFable_2026-11-22.md): the second
  reviewer's brainstorm on `pairing-overhead.stacks`, a walk of a list
  built by exponentiation carrying a stack of raises down the list's
  tail: no simple sound remedy; fusing, reordering and raise-drop
  cancelling refuted in the model; a control holding its word sound and
  modelled, days of kernel work; a safety criterion unsettled. Kept as
  written; its deciding facts checked against the traces.
- [`RecursionFable_2026-11-21.md`](RecursionFable_2026-11-21.md): the
  second reviewer's account of why a recursion through a lambda costs
  interactions quadratic in its depth (`cells-recursion.depth`): one
  unit drop more a call on the tail's wire, drops never fusing; drop
  runs in the kernel (`pairing-fusion.drops.kernel`) to cut it six fold,
  a whole-run crossing to end it. Kept as written; checked against a
  trace.
- [`FreezeFable_2026-11-21.md`](FreezeFable_2026-11-21.md): the second
  reviewer's review of freeze and templates, by a Fable sub-agent, kept
  as written beside `Freeze_2026-11-21.md`, which checks it.
- [`IndexPremises_2026-11-23.md`](IndexPremises_2026-11-23.md): the
  premises of the laws over a copy's index, against the ring-era laws
  they replaced, for the review before the branch's merge: two lookups
  stated over the index after a step (F1, F2), the live nodes' distinctness
  (F3), the frames' regions widened to the tracked nodes (F6); and what
  the branch did without approval. Drafted by the agent.

## Retired

- `LawsInBend_2026-11-06.md`: where Blend writes laws and proofs, against
  how Bend checks them; its decisions in Blend's `blend-laws-in-module`,
  built as Blend's `blend-module-laws`; last commit 03cb4ac.
