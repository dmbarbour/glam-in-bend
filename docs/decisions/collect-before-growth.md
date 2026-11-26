# A net tries a collection before its store grows

`collect-before-growth` · maintainer · rev e8516c1

**Context.** A net's store doubles when its free list runs dry
(`alloc.grow`, `spike/kprim.bend`). The kernel's collecting demand
already collects first: it keeps a reserve off the free list, takes it
where the list runs dry, raises a flag, collects at the end of a chunk
of steps, and grows only if less than half is free
(`heap-strategies.erasure.load.cycle.reserve`). Glam's core runs plain
demand, which doubles without collecting. The materializer, making room
before a serve (`cursor-laws.alloc`), would double too. Garbage that
erasure does not reclaim, a subnet cut off from the interface, would
then grow the store without bound.

**Decision.** The maintainer (2026-11-26): "Yes, always try GC before
growth, otherwise we'll have very awkward corner cases where we cannot
compute in bounded space."
- Wherever a net glam runs would grow, a collection is tried first. The
  store grows only when the collection leaves too little free.
- Room is one policy with one home: the materializer asking for room
  before a serve goes through it, and does not double on its own.

**Consequences.**
- Glam's hosts collect, as the collecting demand does, and the
  materializer's guard asks for a collection before `P.grow_more`.
- A host's collector keeps what the materializer holds: the situating
  node, its index, the cursors and the placeholders. A source's
  collector keeps the nodes a copy took (`copied-nodes-untouched`).
- The laws' premise that the reserve's word is 0, which holds while no
  glam net collects, goes when hosts collect. The reserve's law
  discharges it.
- The kernel's plain modes remain as measurement baselines, not as
  glam's way of running a net.

**Rule lives in:** `docs/plans/CursorLaws_2026-11-23.md`,
`cursor-laws.alloc.collect`.
