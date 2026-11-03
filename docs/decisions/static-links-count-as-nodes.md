# A static link counts as the node it stands for

`static-links-count-as-nodes` · maintainer · rev 9b9ea11

**Context.** A static link (HeapModel's
`heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links`) is a
leaf with no node: a reference whose port bits are 3, held in the link
word of the port it faces. Its first form made two statics meeting vanish
with no interaction, so a collection counted 908 fewer interactions over
the library than with allocated erasers, and it chose the erasers' values
so that a link written back to one landed on a scratch word of the net's
header. The maintainer (2026-11-03): for profiling, static nodes should
still count as logical nodes for interactions, as though there were as
many copies of the node as we want; numbering chosen for a scratch word
won't generalize to immediates and packed pointers, and gives statics a
location they do not have.

**Decision.** A static stands for a node, a copy of it at each link to
it, and every count treats it as that node: an interaction with one is
an interaction, profiled by its kind, and two statics meeting are a pair,
counted and reduced where a strategy would count and reduce a pair of
allocated nodes. Where allocated nodes would form a pair off demand's
path, which demand never reduces and a collection sweeps unreduced, two
statics meeting are counted by no one either: the counts match what
allocated nodes do (the maintainer, 2026-11-03). A static's value means
only what NetData's layout gives it (`netdata-refs`): no code relies on
where statics lie among references, and a reference compared with a
node's is tested for being static first; a link written back to a static
is skipped, by a test, not sent to a scratch word.

**Consequences.**
- A strategy that keeps pairs notes two statics meeting as a pair, one of
  the statics standing for it on the stack.
- A link from a rewrite to an external peer tests whether the peer is
  static before writing back to it: the price of static links for every
  rewrite, paid whether or not a net holds any.
- Counts and profiles compare across representations: a collection makes
  as many interactions with static erasers as with allocated ones.
