# The materializer's laws ask the free list to be sound, not complete

`free-list-sound` · maintainer · rev 1a07a55

**Context.** The serve's growth premises (`LM.ext.ok`) and the splice's
fresh-node premises ask that the nodes a serve takes from the free list
be free. The free list's model in `Nat` (`FL.ok`, `spike/freelist.bend`)
is exact. It is sound, each listed slot free, and complete, every free
slot listed. A serve can be hurt only by the first failing: a listed
node in use. Completeness is what the kernel's reserve breaks
(`heap-laws-align.statics`: the reserve cut from the free list fails
`FL.ok`'s one list), and what a leak would break. Two reviewers
([`Alloc_2026-11-26`](../reviews/Alloc_2026-11-26.md), the second
reviewer's A0.2).

**Decision.** The maintainer (2026-11-26): "We can separate no leaks.
Make sure it's planned, though."
- The materializer's laws claim and ask only soundness: a node on the
  free list, or on the reserve, is not in use.
- No leaks, every node not in use on the free list or the reserve, is a
  property of its own: the audit's (`KN.free_ok`) and its own law's.

**Consequences.**
- The prefix law the splice and the loop wait on
  (`splice-frame-premises`) is stated over a sound list. Its premises
  do not include completeness.
- A sound list over the heap's words refines `FL.ok`'s soundness half.
  `FL.ok`'s exactness stays the model's.
- No leaks has a step of its own, so that separating it does not drop
  it.

**Rule lives in:** `docs/plans/KernelRefine_2026-11-24.md`,
`kernel-refine.leaks`; `docs/plans/CursorLaws_2026-11-23.md`,
`cursor-laws.alloc`.
