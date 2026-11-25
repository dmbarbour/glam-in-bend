# The splice's frame law: its premises and who discharges them

`splice-frame-premises` · maintainer · rev 8574fe5

**Context.** The splice's frame law (`serve-write-sets-hybrid`: an exact
list of the words its three passes write) rests on facts the splice
does not make: that the fresh nodes it pops are free, apart and past the
net's header; that the template's links name nodes and ports in range
and link every eraser; and which header words a value or an error
writes. Three questions on where each fact comes from, with options,
pros and cons, and a fault found on the way
([`Splice_2026-11-19`](../reviews/Splice_2026-11-19.md), with the second
reviewer's advice beside it).

**Decision.** The maintainer (2026-11-19): "We'll go with the
recommended options, including reproduction of the fault. We should
record Fable's target for allocation."
- The fresh nodes are a premise of the splice law: the free list's first
  k nodes as the heap's words spell them (`KMd.chain`), laid out apart,
  past the header.
- The allocator's target (the second reviewer's): one prefix law, "the
  free list's first k nodes are distinct, laid out apart, past the
  header, below the capacity, and none live", which discharges the
  splice's premise, the serve's that the ring's nodes lie past the
  header, and `.host.path`'s that fresh nodes miss the walk's path,
  together; `FL`, the free list's model in Nat, is the model it refines.
- The template's premises are one model predicate (`SM.tpl.ok`): each
  end names a slot the node pass writes, at port 0 for an eraser and
  below 3 for a node (`splice-erasers-static`). Port uniqueness is no
  frame premise. Discharged by a law on what freeze builds; for the
  compiler's templates, a check where they enter (`book.tk`).
- The header's words are an exact named list (the error count and the
  value table's four words, the head beside them), not a class; "the
  ring's nodes lie past the header" is a premise of the serve's
  composition, not a widening of `layout`.

**Consequences.**
- The splice law lists its premises as missing pieces, discharged by
  the allocator's prefix law and freeze's law; each law's witness shows
  its premises hold together at an instance.
- A stray header write in the splice is refuted, the list being exact;
  growth, when it enters, widens the list, a law change.
- A runtime check stands at the compiler's boundary, marked to go when a
  law replaces it (the maintainer's direction: laws over audits).

**Rule lives in:** `docs/plans/Cells_2026-11-09.md`,
`cells-freeze.nested.host.splice` and `cells-freeze.nested.host.alloc`.
