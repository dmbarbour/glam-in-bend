# In a source, eraser events and fusion leave finished nodes alone

`finished-nodes-untouched` · maintainer · rev 37e045d

**Context.** A live template's copies take a source's finished nodes and
key their cursors by the source's positions: a finished node and one of
its ports (`copy-reduced-function-nets`; `docs/reviews/Joins_2026-11-11.md`).
A rewrite never touches a finished node, since a finished node is in no
active pair. Two other things in the kernel do:
- **fusion** folds a new control into a finished one, which
  `copied-controls-unfused` already refuses for copied controls;
- **eraser events** turn a fan reached by an eraser on one side into a
  linear fan, moving its kept side from port 2 to port 1 (`ev.copy`,
  `ev.merge` in `spike/rules.bend`), or turn an operator whose result is
  erased into a dead operator.

Either changes the node a copy took, or renumbers the ports its cursors
are keyed by (the second reviewer, `JoinsFable_2026-11-11.md`).

**Decision.** The maintainer (2026-11-11): "We can forbid eraser nodes
from modifying finished nodes." And: "I agree we'll need to include
eraser events with control fusion among things that must not touch
finished nodes." In a source, neither an eraser event nor fusion
modifies a finished node. An eraser reaching a finished node's port
stays there as a static in the link word, as strategies that run no
events already leave it (`erasure-at-write`).

**Consequences.**
- A finished node keeps its kind and its ports while its source lives,
  so a position stays a valid key for every copy's cursors.
- The optimizations those events gave are lost on the source's
  finished part. Demand on the source before it is first copied
  mitigates that, and a copy that takes the node may run the event in
  its own net.
- Whether the source's collector may still free a finished node is a
  separate question, open in the Joins review. Its walk follows inputs
  only, so a finished node whose outputs feed nothing it reaches is
  unmarked, though no event touched it.
