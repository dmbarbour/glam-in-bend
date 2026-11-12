# In a source, nodes copied into a host are left alone: no events, no fusion, no collection

`copied-nodes-untouched` · maintainer · rev 1710211

**Context.** A live template's copies take a source's finished nodes and
key their cursors by the source's positions: a node a copy took and one
of its ports (`copy-reduced-function-nets`;
`docs/reviews/Joins_2026-11-11.md`). A rewrite never touches a finished
node, since it is in no active pair. Three other things in the kernel
do:
- **fusion** folds a new control into a finished one, which
  `copied-controls-unfused` refuses for copied controls;
- **eraser events** turn a fan reached by an eraser on one side into a
  linear fan, moving its kept side from port 2 to port 1 (`ev.copy`,
  `ev.merge` in `spike/rules.bend`), or turn an operator whose result is
  erased into an eraser;
- **the collector** follows inputs from the interface. It frees a
  finished consumer of the function's variable once the source discards
  where its output led, though no event touched it (the Joins review,
  `\x -> k (x v) 5`), and the freed slot is then reused.

Each changes or frees a node a copy took, so the copy's cursors name
ports that are gone, renumbered or reused (the second reviewer,
`JoinsFable_2026-11-11.md`).

**Decision.** The maintainer (2026-11-11): "We can forbid eraser nodes
from modifying finished nodes", and "we'll need to include eraser events
with control fusion among things that must not touch finished nodes".
On the collector (2026-11-12): "a source's collector must keep any nodes
marked 'finished'. Especially assuming that mark is only applied once
the node is copied into a host."

The mark is set when a copy first takes a node, as on controls, and in
a source:
- no eraser event modifies a marked node, the eraser staying a static
  in the link word, as strategies that run no events already leave it
  (`erasure-at-write`);
- no fusion modifies a marked node (`copied-controls-unfused`);
- the collector keeps every marked node.

**Consequences.**
- A copied node keeps its slot, its kind and its ports while its
  source lives, so a position is a valid key for every copy's cursors,
  stale ones included.
- Nodes finished but not yet copied are not protected and need not be:
  no cursor names their ports. Events, fusion and collection keep their
  gains there.
- The marks are a bitmap per source, a word for every 32 nodes. They
  are written when a copy takes a node, and read by events, fusion and
  the collector.
- The garbage the collector keeps is bounded by what copies took, and
  goes with the source.
