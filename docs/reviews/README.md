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

## Retired

- `LawsInBend_2026-11-06.md`: where Blend writes laws and proofs, against
  how Bend checks them; its decisions in Blend's `blend-laws-in-module`,
  built as Blend's `blend-module-laws`; last commit 03cb4ac.
