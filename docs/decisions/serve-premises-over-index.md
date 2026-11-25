# The serve's laws over the index take four premises

`serve-premises-over-index` · maintainer · rev 1317ae6

**Context.** The serve's laws are restated with a copy's cursors in a
tree of the net's nodes (`cursors-indexed`). The first, `cursor_pend`,
needed premises the ring's laws did not state, beyond
`copy-links-two-way`:

1. A crossing's position is absent from the index, and the crossings'
   positions are distinct. A crossing finds at its far end but inserts
   at its own position, so its find does not discharge it. The serve's
   caller owes it: it is the fault that dead cursors are kept to prevent.
2. A port a live node faces has its link word off every word of the
   tracked nodes that are not live, off the word 0 of those that are, and
   off the free list's head, which the list's chain reads.
3. No live node faces itself.
4. The free list holds the crossings' nodes as well as the copy's. The
   materializer reserves none, so growth stays unclaimed, as it already
   is for the splice (`splice-frame-premises`).

**Decision.** The maintainer (2026-11-23): "The added premises seem
reasonable. We might want to review premises and see what can become
laws later."

**Consequences.**
- The serve's restated laws take these premises, stated in the pending
  invariant over the index.

**Rule lives in:** `docs/plans/Cells_2026-11-09.md`,
`cells-freeze.sharing.cursors.index`; the pending invariant in
`glam/ring_model.bend`.
