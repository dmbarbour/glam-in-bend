# A copy's cursors are indexed, not ringed; dead cursors kept

`cursors-indexed` · maintainer · rev e073d6c

**Context.** A copy's cursors live in a ring linked through word 3, and
every serve walks it three ways: lookups by position, the predecessor
before each unlink, the situating node twice. Dead cursors stay in the
ring by design (`cells-freeze.cursors`, "Erasure, under review"), so a
host that drops parts of what it is given makes every serve dearer as
the copy goes on (`cells-freeze.sharing.cursors.erased`). The agent and
the second reviewer brainstormed indexes
(`docs/reviews/RingIndex_2026-11-22.md`, `RingIndexFable_2026-11-22.md`);
forgetting dead cursors was scouted and found not low-hanging
(`DeadCursorsFable_2026-11-22.md`).

**Decision.** The maintainer (2026-11-22), on the review's questions:
"Q1. Nobody cares about the ring if it's replaced. Q2. I lean towards
index in net nodes. But as you mentioned, we can measure first. Q3.
Sounds like a useful law. My general guidance on laws remains: prove
what's important (whether for correctness or performance) and prove
what's easy. Q4. Yes. Keep until we know what we're doing."

- The ring is replaced by an index of the copy's cursors by position;
  its order is not kept, nothing needing it.
- Every dead cursor is kept, its memory accepted, until a removal
  criterion or coarser copies are understood.
- Where the index lives is open: the maintainer leans to the net's own
  nodes; a measurement of the walks and of ring lengths decides
  between that and a value in the net's data table.
- One cursor a position in a copy becomes a law.

**Consequences.**
- The ring's chain laws retire and its invariant is restated with the
  index, approved at the merge that brings them; the serve's laws are
  restated as far as the index's home requires.
- `ring-walks-fueled-by-heap` retires with the walks it fuels.
- Option C (fewer cursors made, e.g. opportunistic crossing) waits until
  it can be exercised usefully (the maintainer, 2026-11-22).

**Rule lives in:** `glam/ring.bend`, `glam/ring_model.bend`,
`glam/LAWS.bend` (the ring's laws); `cells-freeze.sharing.cursors.ring`
and `.erased` in `docs/plans/Cells_2026-11-09.md`.
