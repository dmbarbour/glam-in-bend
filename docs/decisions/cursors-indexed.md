# A copy's cursors live in a crit-bit tree of the net's own nodes; dead cursors kept

`cursors-indexed` · maintainer · rev f76f98e

**Context.** A copy's cursors lived in a ring linked through word 3, and
every serve walked it three ways: lookups by position, the predecessor
before each unlink, the situating node twice. Dead cursors stay by
design (`cells-freeze.cursors`, "Erasure, under review"), so a host that
drops parts of what it is given made every serve dearer as the copy went
on (`cells-freeze.sharing.cursors.erased`). The agent and the second
reviewer brainstormed indexes (`docs/reviews/RingIndex_2026-11-22.md`,
`RingIndexFable_2026-11-22.md`); forgetting dead cursors was scouted and
found not low-hanging (`DeadCursorsFable_2026-11-22.md`). The maintainer
first ruled the ring replaced, its order dropped, dead cursors kept and
one cursor a position a law, the index's home to be measured (2026-11-22:
"Q1. Nobody cares about the ring if it's replaced. Q2. I lean towards
index in net nodes. But as you mentioned, we can measure first. Q3.
Sounds like a useful law. ... Q4. Yes. Keep until we know what we're
doing."). The measurement (`cells-freeze.sharing.cursors.index.measure`)
found most rings short, 1 to 9 members on average across the ladder and
the sharing families, and the long ones the live frontier (`deep`, 52 at
100 elements to 202 at 400) and the dead (cells of six heads, 254 to
1,004, nearly all dead cursors at inputs). The index was then built in
the net's nodes on a side branch (`.index.spike`) and its find, removal
and insert proved against a model (`.index.laws`).

**Decision.** The maintainer (2026-11-22), the index built and its laws
proved: "Yes, let's take it as an architecture decision now, replacing
the ring decision (if one was recorded), with performance reasons
given."

- A copy's cursors live in a crit-bit tree keyed by their source
  positions, made of the net's own nodes: a cursor is a leaf, its word 2
  the key and its word 3 its situating node; a branch is a node of kind
  18 and form 3 testing one bit, its children in words 2 and 3; the
  situating node's word 3 holds the root, or itself when the copy has no
  cursor. A tree of one cursor is the words of a ring of one.
- The ring and its order go; nothing needed the order.
- Every dead cursor is kept, its memory accepted, until a removal
  criterion or coarser copies are understood.
- One cursor a position in a copy: an insert meeting its own key is a
  kernel error, the tree unchanged, and a law.

Why the net's nodes, for performance:
- Nothing walks the cursors any more: a lookup descends at most 33
  steps, the situating node is one read (a cursor's word 3), an unlink
  needs no predecessor. With the ring, the walks grew with the copy;
  with the tree, every workload that grew is flat in instructions an
  element (the spike, against main): `deep` 204K at 100 elements and
  193K at 1,600 (the ring 209K and 323K), cells of six heads 476K and
  467K at 100 and 400 (538K and 734K), of eight 586K and 575K (685K and
  1,009K); `seq` unchanged, about 190K.
- The tree is read and written as words, nothing allocated or counted
  by Bend. A persistent value in the data table, the other home weighed,
  would allocate and count references on every change, and reference
  counting is half of all instructions (the cost review,
  `cost-as-low-as-feasible`). Short rings, the common case, pay for the
  tree no more than for the ring: the ladder's samples −0.02% to +0.26%.
- A branch is one node of the free list, taken at an insert and given
  back at a removal, with the store the net already has.

**Consequences.**
- The ring's chain laws retire and its invariant is restated over the
  tree, approved at the merge that brings them; the serve's laws are
  restated over it, the free list's first nodes threaded through a
  serve's crossings, since an insert now takes a node and a removal
  frees one.
- `ring-walks-fueled-by-heap` retires with the walks it fuels, when the
  laws citing it are restated; `ring-ports-faced-off-positions` is
  restated for the tree's members with them.
- Option C (fewer cursors made, e.g. opportunistic crossing) waits until
  it can be exercised usefully (the maintainer, 2026-11-22).

**Rule lives in:** `docs/plans/Cells_2026-11-09.md`,
`cells-freeze.sharing.cursors.index`; with its merge, `glam/index.bend`,
`glam/index_model.bend` and `glam/INDEX_LAWS.bend`.
