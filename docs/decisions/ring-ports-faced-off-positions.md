# A ring's members face ports whose link words are no member's position or link

`ring-ports-faced-off-positions` · maintainer · rev 439d3a7

**Context.** The ring exact with its nodes (`RG.ring.ok`) said of each
member that the port it faces has its link word off every member's word
3, so that linking that port, as a join does, leaves the ring's links.
It said nothing of a member's word 2, its position, which a find reads:
a join could write a member's position, if a member faced that word as
a port, and no law excluded it. In a net it cannot happen: a cursor has
one port, its principal, and the situating node none (the maintainer,
2026-11-14). The serve's composition, a find after a join, needs the
positions kept. Three ways were set out: strengthen `faces`; a separate
predicate in the serve's invariant alone; or read positions from the
heap as it changes, the model sharing the find's decisions.

**Decision.** The maintainer (2026-11-17): "Strengthen faces." A port a
member faces has its link word in no member's word 2 nor word 3. A
member's word 1 may still be faced: two cursors may face each other.

**Consequences.**
- `RG.faces.m` asks `RG.port.ok`: the port's link word off every listed
  node's words 2 and 3. Every law over `ring.ok`, `node.ok` or
  `enter.ok`, and `leave_exact`'s premise on the port linked, changes
  meaning, and is approved again at the merge that carries it.
- A join keeps the members' positions, so the serve's composition finds
  by the positions the members had, not by reading the heap as it
  changes.
- The situating node's word 1, its static eraser, is not protected: no
  law reads it, and naming it would single out the situating node in
  every list the faces are stated against.

**Rule lives in:** `glam/ring_model.bend`, `port.ok` and `faces.m`.
