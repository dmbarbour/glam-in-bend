# Equivalent representations are interchangeable in context, an eraser node and its static among them

`representations-interchangeable` · maintainer · rev 5f2e64f

**Context.** An eraser is held two ways: an allocated eraser node, or a
static in the link word of the port it faces (`static-links-count-as-nodes`,
`erasure-at-write`). The freeze review found code that tells them apart:
positioned demand serves an eraser node as the static only at the
interface, so elsewhere the eraser's tree is frozen as a value and falls
outside the serve's laws (`docs/reviews/Freeze_2026-11-21.md`, C1), and
a whole freeze of a net whose root is a static gives a cursor instead of
the eraser (B1). The agent put the first to the maintainer as a question
about one function.

**Decision.** The maintainer (2026-11-21): "it should always be valid to
transform equivalent representations (modulo reflection) in context,
including an eraser node and its static. If this isn't the case, a
review for discrepancies is warranted." On statics: "I do generally view
statics as links to principal ports of abstract, remote, copyable
nodes."

- Replacing a representation by an equivalent one, wherever it stands,
  changes no outcome; only reflection may see the difference. An eraser
  node and its static are one value.
- Code that behaves differently for the two, in a result, a branch
  taken, what is copied or frozen, or an error, is a fault: found by a
  review for discrepancies and fixed, not answered as a question.
- A static is a link to the principal port of an abstract, remote,
  copyable node: a template may name it as a link's end, no node of its
  own (`cells-freeze.format`).

**Consequences.**
- Counts may differ between representations only as
  `static-links-count-as-nodes` allows: they count what allocated nodes
  would.
