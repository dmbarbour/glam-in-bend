# What marks a free node is the kernel's representation, behind one name

`free-mark-internal` · agent · rev e8516c1

**Context.** The materializer's laws need a node on the free list to be
none in use (`free-list-sound`), and the faced-port premise needs it
too, since the wiring's model reads a live node by its header. Today a
free node's header word is 0: `free` zeroes it and growth's fresh words
are zero. The audit (`KN.free_ok`) and the wiring's model already read
it so. The alternatives cost more: ghost sets of free and used nodes
carried through every write, or an abstraction of the whole heap
([`Alloc_2026-11-26`](../reviews/Alloc_2026-11-26.md), second round;
the second reviewer's C5).

**Decision.** The maintainer (2026-11-26): "TBH, I'm not fond of
assuming the 0 header/kind indicates a free node as a law. It feels
like an implementation detail elevated to a design law. But if it's the
best approach, we can do as needed. I won't say 'should' in these
cases." So the encoding stays an implementation detail.
- What the laws rely on is only that a node's being free or in use can
  be read at the node. The audit, the wiring's model and a collector
  (`collect-before-growth`) need that anyway.
- One predicate pair in the kernel's model (`KMd.free_at`,
  `KMd.used_at`) is the only place that says how it is read. Laws, the
  wiring's model and the audit cite the names.
- No design doc or law statement spells the encoding.

**Consequences.**
- A change of encoding, such as frees zeroed lazily, a mark in the
  kind field, or marks per page or per worker, changes the predicates
  and the laws of the primitives that write them, not the laws above.
- A template's nodes are of kinds in use, a fact of templates stated
  without the encoding. This closes the case of a free-kind template
  node, whose header would read free.
- The frame laws still promise nothing of a free or taken node's stale
  words (the maintainer, 2026-11-13).

**Rule lives in:** `spike/kmodel.bend`, `KMd.free_at` and
`KMd.used_at`.
