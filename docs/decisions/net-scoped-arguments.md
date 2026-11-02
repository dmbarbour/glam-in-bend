# A function's argument is used only within its body

`net-scoped-arguments` · maintainer · rev 8e3f26d

**Context.** Links run both ways, but data does not: it flows from a
positive port to a negative one, and demand flows back. A collection that
keeps only what feeds the interface, following each node's inputs and the
outputs wired to them, frees more than one that keeps what demand might
meet from either side (in the spike's benchmark, 9.0% of what was kept
against 2.6%), and what it frees stays dead: no rewrite wires a dead output
into a live input. It is safe only if demand never steps forward, from an
output to its consumer. Demand steps forward in one case alone: it enters
a function by its argument, a variable demanded apart from its function's
application, since only a function has a positive principal port and
another output. glam's lowering of lambda terms never builds that;
`interaction_net` could, and the spike's library held three such nets,
written by hand.

**Decision.** A function bind's argument may be used only within the
function's body. On the graph of ports, where an output needs its node's
inputs and an input needs the output wired to it, every path from the
exposed port to the argument passes through the function's result: the
result dominates the argument, as a definition dominates its uses in SSA.
`interaction_net` refuses a net where it does not, as it refuses the
obvious errors (`net-obvious-errors`), checked with a dominator tree in
near-linear time. For users: a function's argument is local to its body;
to send it elsewhere, return it. Scoping is checked as a net is built.
Once a function is copied, the copies share one body, and each copy's
argument is scoped only per sharing context, not by structure, so demand
reports a forward step, should one occur, as it reports a cycle: a
variable demanded outside its function's body.

**Consequences.**
- The collection may follow inputs only
  (`heap-strategies.erasure.load.cycle.walk.directed.dataflow`).
- Every static wiring stays: graphs of any shape, copies and operators,
  results wired to any consumer, a body reading any producer in the net,
  cycles of data such as `r = f r`. Backpropagation without fixpoint
  rests on the wiring.
- The scopeless binder goes: a function value used as a write-once
  channel, its application by other code sending the argument to wherever
  the variable is read, as a callback reporting to its creator or an
  early return would. If wanted, it returns as a kind of its own, with an
  edge of its own for the collection.
- Until glam's construction exists, the spike's tools check nets for
  scoping beside polarity (`spike/tools/polarity.py`), and the library
  keeps the hand-built unscoped nets only to show them refused and
  demand's report.

**Rule lives in:** `docs/Design.md`, Interaction Nets.
