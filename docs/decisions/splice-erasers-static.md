# The splice makes a template's erasers static as it links

`splice-erasers-static` · maintainer · rev b99fc3e

**Context.** A template has no static ends: freeze writes each static
at a port it reads back as an eraser node linked there (`fz.era`), and
the splice, like the loader (`KN.load`'s `ld.statics`), took a node from
the free list for each eraser, linked it, then in a third pass read each
node's header back, made each eraser static in the port it faced and
freed it: a pop and a free for each eraser, two reads for each node,
nothing kept. The statics pass's frame needed an invariant carried
through it, and three premises more, since it writes through words it
reads (`cells-freeze.nested.host.splice.statics`). Asked why the pass
was its own, the maintainer (2026-11-20): "for now I favor a single
pass"; and of two erasers linked to each other, kept as two nodes:
"we could just immediately count the interaction for eager, or
immediately ignore for lazy (disconnected subgraphs can't be reached by
demand)."

**Decision.** In the splice and the materializer's copy, an eraser of
the template makes no node: the node pass maps its index to the static,
and the links pass links static-aware (`P.link_xx`), so that the link
writes the static in its peer's link word and nothing of its own. Two
erasers linked to each other write nothing: the splice runs under
demand, which never reaches such a pair, and a pair off demand's path is
counted by no one (`static-links-count-as-nodes`). The loader keeps its
statics pass; an eager loader would count such a pair as one
interaction at once, of its kinds.

**Consequences.**
- No outcome changes for any template the system makes: lowering emits
  no erasers, and freeze links each eraser to a port of a node it read
  back, which is no eraser facing a static (an eraser's one port facing
  a static leaves nothing to reach it by), so it makes no eraser pair.
  Nodes take other slots, and the free list another order.
- The statics pass and its law go; the node pass's law counts the
  fresh nodes by the nodes a template makes (`SM.made`), and the links
  pass's admits ends that name the static.
- An eraser at a source's root no longer reads a stale word: its map
  entry is the static, which the materializer's root leaves with, as it
  does a static eraser.

**Rule lives in:** `glam/splice_copy.bend` (`sp.node_k`, `sp.link2`),
`glam/SPLICE_LAWS.bend`, and `docs/plans/Cells_2026-11-09.md`,
`cells-freeze.nested.host.splice.single`.
