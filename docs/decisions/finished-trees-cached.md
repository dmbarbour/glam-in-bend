# Finished trees frozen at a source's position are cached, their space accounted

`finished-trees-cached` · maintainer · rev 2884596

**Context.** Each serve at a source's position walks the finished tree
there and reads it back anew (`freeze_tree`), though a finished tree
never changes: no rewrite reaches it, and `copied-nodes-untouched`
keeps eraser events, fusion and the collector off copied nodes. The
second reviewer proposed fragments "cached in the source, so the second
copy to demand it splices the fragment instead of walking"
(`docs/reviews/CursorsFable_2026-11-10.md`, idea 3); the agent raised it
again as option B (`docs/reviews/Freeze_2026-11-21.md`, F3).

**Decision.** The maintainer (2026-11-21): "I like the idea of tree
caching per position, but I'm a bit concerned about space overheads. I
think we should go ahead, with attention to space-time tradeoffs
inherent to caching."

- A tree frozen at a source's position is kept for later serves at that
  position, which splice it without positioned demand or a freeze walk.
- Its space is accounted and bounded; what the cache keeps, and when it
  drops an entry, is chosen by measured space against time.

**Consequences.**
- The cache is sound by `copied-nodes-untouched`: a finished tree is
  fixed once a copy has taken it. The cache needs the marks on copied
  nodes: its key and its holes' source ports must name nodes no step
  changes or reuses.
- A hole's far end is no part of an entry: where it faced unfinished
  structure, that structure's reduction has rewritten the wire, so a
  serve reads it from the source when it runs.
- A compact frozen form saves more with every serve a cache answers, so
  the form and the cache are designed together (`cells-freeze.format`;
  the maintainer: "Efficient representations become more valuable with
  caching because we save per serve").
- Step: `cells-freeze.fragments` (the Cells plan).
