# A function's net is reduced locally, then copied whole

`copy-reduced-function-nets` · maintainer · rev faaf32c

**Context.** A function is a net and its remaining arity, and copies share
the reductions of its source (`functions-are-nets-with-arity`). Copying
lazily, frontier by frontier, as the Rust bootstrap's cursors do
(EvalSpike's `spike-cursors`), shares the most work at the most
complexity.

**Decision.** First, a function's net reduces locally, as far as it goes
without an argument; then each application copies the whole net. Cursors
wait until measurements call for them.

**Consequences.**
- Work in the source is shared as far as local reduction reaches; work
  that needs the argument is done again in each copy.
- An application costs a copy of the net, so small nets (128 nodes to
  start, `net-nodes-double`) and compacting fully evaluated functions
  matter.
