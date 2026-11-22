# A copy's cursors, indexed: the designs for discussion

For the maintainer's discussion (2026-11-22), who asked for "a
brainstorm on index designs. In theory, an index could replace the ring
structure (e.g. the 'next' becomes an index ref) and be hosted in the
heap or a side table or a number of other options. Depending on
decisions here, a lot of laws and proofs may need to be rewritten. So,
let's also bring in a Fable instance together with your own best ideas
and we'll discuss." Beside it: the second reviewer's brainstorm
(`RingIndexFable_2026-11-22.md`) and its scouting of option B
(`DeadCursorsFable_2026-11-22.md`); the agent's own ideas, written before
reading them, are summarized here. Plan steps:
`cells-freeze.sharing.cursors.erased` and `.ring` in
`docs/plans/Cells_2026-11-09.md`.

## Where things stand

The maintainer likes options A (lookups that do not walk the dead,
every dead cursor kept) and C (fewer cursors made), C waiting until it
can be exercised usefully (opportunistic crossing, say).

**B, scouted: not low-hanging.** Dead cursors that matter clean
themselves up already: a later serve that reaches one joins it, and the
join frees it. The clutter is the ones never reached, tombstones for
"this wire's copy end is erased", and whether anyone will read a
tombstone depends on the source's future, which the host cannot see. Of
the criteria tested only one is sound and cheap (the source's port
already holds an eraser), and it misses the workload. A relaxation,
forgetting dead cursors at inputs and keeping those at outputs (which
are void values the copy owes), would flatten the workload but makes
the reached ones worse in aliasing programs and rests on an unproved
lemma. Not recommended; a count would put numbers on it.

**What a serve walks.** Three walks round the whole ring, not one: the
lookups by position (a crossing, the frontier, each climb step), the
search for a cursor's predecessor before every unlink (always the whole
ring), and the search for the ring's situating node (twice a serve,
past every older member). So an index for lookups alone still leaves
the cost growing; option A needs all three gone.

## The designs

| design | what changes | walks left | where the index lives | laws |
|---|---|---|---|---|
| two pointers (both) | a find hands back the predecessor; the core hands the situating node to the serve | most | none | one law beside `find_exact`; small |
| index beside the ring (both) | a position map kept in step; the ring stays the truth | the predecessor's and the situating node's, unless more maps are kept | needs a home: the situating node has no free word | the 27 ring laws stand; a refinement law each operation |
| ring fully indexed (Fable's D5) | three maps beside the ring: position, predecessor, situating node | none | one map a heap, held by the core | the 27 laws stand; refinement laws up through the serve; two structures in step for ever |
| crit-bit tree in the heap (the agent's) | the ring replaced by a binary trie on the position's bits, its nodes ordinary heap nodes, the cursors its leaves; word 3 names the situating node | none | in the net's own nodes; no contiguous words needed | a new model; every frame law gains a region; the collector must know the tree's nodes |
| the star (Fable's D6d) | word 3 names the situating node; membership and lookup a persistent trie a copy, threaded through a serve and resting in the net's data table | none | a value in the data table, under a constructor that is no glam value | the list model kept; five chain laws retire, the ring's invariant restated, frames lose a region; the trie's laws pure data |

Rejected by both: a second list for dead cursors (finds must still
search it), sorting (every serve still walks past every dead cursor),
an array a copy over the source's positions (its size paid by every
copy, however small its use).

## Where the agent and the second reviewer agree

- Replace the ring rather than index beside it: once nothing walks the
  ring, its order serves nothing on a serve's path, and keeping it
  means keeping two structures in step.
- A cursor's word 3 should name its situating node: finding it becomes
  one read, and unlinking needs no predecessor.
- Measure first: walk steps by kind and ring lengths over the ladder,
  the heads families and `deep`. Most rings may be short, and below
  some length a walk beats any index; the measurement sets the
  constant.
- Build the index first as pure data with its own laws (a lookup equals
  the ring model's first match, a put and a removal commute with the
  model's list), before touching the heap.

## Where they differ: where the index lives

- **In the heap's nodes** (the agent's crit-bit tree). The index is part
  of the net: it grows with the node store, travels wherever the net
  goes, and is read as words, with no Bend structure to allocate or
  count. Costs: a node a cursor; the collector and the audits must know
  the tree's nodes; the ring's model and every frame law are restated
  for a tree.
- **As a value in the data table** (the second reviewer's star). The
  index is a Bend value beside the net's words: the ring's list model
  and most law statements stand, and the trie's proofs are about pure
  data, the cheapest kind here. Costs: a new constructor among the
  table's values that is never a glam value (about 49 matches meet
  it); freeing the entry with its ring is to be built; a persistent
  structure in Bend allocates and counts references. The cost review
  found reference counting half of all instructions, so the trie must
  be taken out and threaded unshared through a serve, as proposed,
  for that cost to stay small.

The agent now leans to the second reviewer's star on the laws, and
would let the measurement decide between the two homes: if rings are
mostly short and the trie's constant shows, the heap's tree wins on
cost.

## Small things found on the way

- A serve's climb that finds no ring position runs its whole fuel, a
  ring walk a step, before reporting; a climb reaching the interface
  could stop there.
- A dead cursor at an input whose far end is a cursor at an output of
  the same ring could give that one the eraser on sight: a small leak
  the design tolerates today.
- The root placeholder a serve makes (B6 of the freeze review) costs a
  lookup, a join and a free a serve under any design.

## For the maintainer

1. Should the ring's order go? Fable and the agent see no use for it
   once nothing walks it: an audit or a collector can go through the
   index instead.
2. Where should the index live: in the net's nodes, part of the net as
   its cursors are, or as a value in the net's data table, keeping the
   laws' list model?
3. Should one cursor a position in a copy be a law? Today nothing says
   so; a second cursor at one position is the fault dead cursors are
   kept to prevent.
4. Is keeping every dead cursor's memory acceptable (four words and an
   index entry each) until a removal criterion or coarser copies come?

The agent proposes, whatever the answers: the measurement first
(walk steps by kind, ring lengths, dead cursors by polarity, a single
build answering both reviews' first steps).
