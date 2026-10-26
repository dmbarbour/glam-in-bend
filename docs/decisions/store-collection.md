# The store has its own collector: stop-the-world, then SATB

`store-collection` · maintainer · rev dd5c912

**Context.** Bend frees its own data when the last owner drops it, but
cannot see into our store (`split-heap`, `store-pages`). Lazy fixpoints make
cycles there, so the store needs a tracing collector.

**Decision.** Build a stop-the-world collector first, then a concurrent one
whose marking runs under fuel with a snapshot-at-the-beginning barrier:
cells allocated during a cycle are born marked, and a write overwriting a
handle logs the old one first. Both shortcut: a handle to a cell holding a
fully evaluated value without handles is replaced by that value, so forced
structure leaves the traced heap.

**Consequences.**
- Collection runs in rounds by pages, as evaluation does; marks crossing
  pages travel between rounds.
- Generations, pacing and shortcutting are heuristics, tuned from
  profiles.
- Laws state what must not break: no marked cell freed, marking closed
  over handles, shortcutting preserving every value read, the snapshot
  invariant across a concurrent cycle.

**Rule lives in:** the architecture sketch, "Collection", until a standing
doc takes it.
