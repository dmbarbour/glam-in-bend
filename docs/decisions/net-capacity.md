# A net holds at most 2^28 nodes

`net-capacity` · maintainer · rev cc33928

**Context.** The kernel stopped a net at 2^21 nodes (2^23 words) and a
strategy's stack of pairs at 2^22 words. These were the sizes of the
first flat kernel's preallocated arrays, a measuring harness
(`spike-node-layout`), kept as the doubling array's ceiling
(`net-nodes-double`) without a decision, and our own workloads pass them
(`succ` at k 21). Bend 2 bounds an array at depth 31, 2^31 words, which
at four words a node is 2^29 nodes. The collection's walk keeps
references in words of its own, tagged in their top two bits (an event's
in bit 31, a boundary's in bit 30, `spike/kstrat.bend`), which needs
every reference below 2^30. The maintainer (2026-11-02): 2^28 is an
acceptable bound for a single net.

**Decision.** A net holds at most 2^28 nodes, 2^30 words, 4 GiB. A
reference, a node's word and its port, stays below 2^30, leaving its top
two bits free wherever references are kept apart from the net's links. A
strategy's stack of pairs holds up to 2^28 words, a word a node, twice
the pairs a net can hold at once. The data table needs no bound of its
own: it reuses freed entries, and each entry has a node as its one
owner. A net or stack that would grow past its bound is out of memory
(`machine-limits-not-errors`). A computation larger than one net spans
nets and cells.

**Consequences.**
- The kernel's ceilings are `P.w_maxd` 30 and `P.rs_maxd` 28; a law
  keeps the first within the walk's tags and the net's growth
  arithmetic within a `U32` (eight times a net's nodes).
- A net at the bound is 4 GiB of nodes, more than a machine or a run's
  budget may give; running out sooner is out of memory too.
- Packed references (`netdata-refs` in
  [`NetData_2026-11-02.md`](../plans/NetData_2026-11-02.md)) can name any
  node in 28 bits.
- Levels keep their own bound, the header's 24-bit field
  (`header-kind-byte`).

**Rule lives in:** `spike/LAWS.bend`, `capacity_leaves_tags`.
