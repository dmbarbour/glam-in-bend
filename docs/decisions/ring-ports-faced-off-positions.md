# The live nodes face ports whose link words are no live node's key nor home

`ring-ports-faced-off-positions` · maintainer · rev b6c82c8

**Context.** A copy's cursors formed a ring linked through word 3,
and the ring exact with its nodes (`RG.ring.ok`) said of each member
that the port it faces has its link word off every member's word 3, so
that linking that port, as a join does, left the ring's links. It said
nothing of a member's word 2, its position, which a find reads: a join
could write a member's position, if a member faced that word as a port,
and no law excluded it. In a net it cannot happen: a cursor has one
port, its principal, and the situating node none (the maintainer,
2026-11-14). The serve's composition, a find after a join, needs the
positions kept. Three ways were set out: strengthen `faces`; a separate
predicate in the serve's invariant alone; or read positions from the
heap as it changes, the model sharing the find's decisions. In the
index of the net's nodes (`cursors-indexed`), a cursor's word 2 is its
key, which a find descends by, its word 3 its home, the situating node,
whose word 3 is the index's root; a join and a leave still link the
ports the live nodes face.

**Decision.** The maintainer (2026-11-17): "Strengthen faces." A port a
member faces has its link word in no member's word 2 nor word 3. A
member's word 1 may still be faced: two cursors may face each other.
Restated for the index (the maintainer, 2026-11-23, asked whether to
restate it for the index's live nodes as `cursors-indexed` said:
"Yes"): the members are the live nodes, the situating node, the cursors
and the pending placeholders.

**Consequences.**
- `RG.faces.m` asks `RG.port.ok`: the port's link word off every live
  node's words 2 and 3, the invariant over the index's `faces`
  conjunct. Its `px.off` adds the tracked nodes that are not live (the
  index's branches, the free list's first nodes), all four words
  (`serve-premises-over-index`, item 2).
- A join or a leave keeps the cursors' keys and homes and the index's
  root, so the serve's composition finds by the keys the cursors had,
  not by reading the heap as it changes.
- The port a leave links in its cursor's place (the copy's root port,
  or the eraser) is stated faceable too (`leave_pend`'s `port.ok`
  premise), which its `po.all` premise may imply
  (`docs/reviews/IndexPremises_2026-11-23.md`, P3).
- The situating node's word 1, its static eraser, is not protected: no
  law reads it, and naming it in `port.ok` would single out the
  situating node in every list the faces are stated against. Whether it
  should be is the Cells plan's `cells-freeze.nested.host.situ`.

**Rule lives in:** `glam/ring_model.bend`, `port.ok`, `faces.m` and
`px.ok`.
