# A net holds its own nodes, in an array that doubles

`net-nodes-double` · maintainer · rev faaf32c

**Context.** A net is a value within the larger heap, usually lazy, and at
most one worker reduces it at a time; parallelism inside a net comes from
accelerated operations, not from spreading the net across workers.
EvalSpike's kernel (`spike-node-layout`) measured three ways to hold a
net's four-word nodes as it grows: preallocated, doubled when full, and
paged with a focus page. Paging used the least memory but cost about four
times as much an interaction, the page check on every access; doubling had
no start-up cost and kept the flat array's speed at median sizes.

**Decision.** A net's nodes live in one flat array of its own, four `U32`
words a node, doubled when full, from 128 nodes (2 KB) at first: most
functions are expected to take 64 nodes or fewer. Below that size, a fully
evaluated function is compacted, or compiled to a short string, rather
than kept as a net. A value a node cannot hold in a word goes
in the net's own data table, indexed from a spare word. An entry may
reference lazies, through heap handles, but is never the cell that owns
one, so an index into the table is not a heap handle. A net does not spread
across the heap's pages: the heap holds nets as values, each taken whole by
the worker that reduces it.

**Consequences.**
- A small net, the likely median under 1 MB, starts small and pays no
  paging cost; a large one pays amortized copying as it grows (measured,
  2^20 live nodes: 208 against 143 ms preallocated, 64 MB at the peak of a
  copy).
- Node references are indices local to their net; heap handles are
  `store-pages`'.
- Parallelism within a net is up to accelerated operations, using what
  arrays allow (`Array.fork`, a split array).
