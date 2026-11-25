# A copy's tracked nodes that face one another face one another both ways; a premise

`copy-links-two-way` · maintainer · rev ebf66f0

**Context.** With a copy's cursors in a tree of the net's own nodes
(`cursors-indexed`), a serve's crossing that joins frees three nodes: the
placeholder, the cursor found and that cursor's parent branch. An insert
later in the same serve takes its branch from the free list. A freed
node's word 1 holds the free list's link. A port's link word is that
word (`laws-name-link-words`), so a later join linking a port that faces
the freed node would overwrite the list's link, and the node the next
insert takes would be unknown. For the serve's laws to keep the free list
sound, nothing the serve tracks may face a node once it is freed.

In a net, links are two-way. A cursor has one port, so a cursor facing
another is faced back by it. The join that frees a node relinks the one
facing it, and after the free nothing faces the node. The laws did not
assume this. A member's word 1 may be faced (`ring-ports-faced-off-positions`),
and no law says the facing is mutual.

Two ways were set out:
- Assume it as a premise of the serve's laws.
- Change the code: defer a serve's frees until its crossings are done,
  every join holding its freed nodes until the pass ends.

**Decision.** The maintainer (2026-11-23) chose the first, as the
option read: "A new premise on the serve's laws: a copy's cursors that
face one another face one another both ways, kept by every join and
leave as the code already does. Like the allocator's facts, it is
stated, not proved from the kernel's wiring laws."

**Consequences.**
- The serve's invariant says that the nodes it tracks and that are live
  (the copy's cursors, and the holes not yet crossed) face one another
  both ways, when they face one another at all. The serve's laws take
  it of the cursors before the serve. Their proofs show that the copy's
  fresh holes, each join, each cursor made and the leave keep it.
- Frees stay where the code has them; no deferral is paid for.
- It is not derived from the kernel's wiring laws, which are stated over
  the free-list model in Nat. Whatever calls a serve owes it, as it owes
  `faces`.

**Rule lives in:** `docs/plans/Cells_2026-11-09.md`,
`cells-freeze.sharing.cursors.index` (its step restating the ring's
laws); the serve's invariant in `glam/ring_model.bend`.
