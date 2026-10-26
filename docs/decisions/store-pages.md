# The store is equal pages of cells that never move

`store-pages` · maintainer · rev b2ec86c

**Context.** The split heap keeps lazy state in our own store, split so
separate workers can own separate parts of it (`split-heap`). A handle sits
inside `Val` variants such as `Lazy{h}`, copied wherever a value goes.

**Decision.** The store is pages, all the same size. A handle names a cell
as one `U32`: the page number in its high bits, the slot within the page in
its low bits. Cells never move, so handles stay valid; a cell no longer in
use may be recycled.

**Consequences.**
- A constructor holding one `U32` packs into Bend's term word, tagged
  variant or not: a handle costs no allocation and is copied without
  counting. A `Nat` would reach 2^48, but any constructor holding one is a
  heap node counted when shared (measured: 24.5 against 16.5 bytes per list
  element, whatever the `Nat`'s value).
- 2^32 cells in all. A small handle module keeps the width replaceable if
  an assembly ever needs more.
- No collection rewrites a handle, and pages pass between workers as whole
  values.
- Recycling needs free lists per page, and fragmentation is managed by
  allocation heuristics, not compaction.
