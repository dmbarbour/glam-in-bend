# Shared lazy state lives in a split heap

`split-heap` · maintainer · rev a5d3082

**Context.** Lazy values and function nets are shared, change once for all
their sharers, and must be reclaimed. Bend 2 offers no laziness and no
shared mutable state outside `@unsafe` forked arrays, and its runtime rules
out a native memo cell. One global store would serialize evaluation, and
marking from Bend data would walk shared structure once per path to it.

**Decision.** Split the heap. Ground data, with no lazy or function handle
beneath it, is plain Bend data, shared and freed by Bend. Everything else
has identity in our own store, so marking visits it once, and a collection
grounds what has been fully forced. Aim for parallelism by splitting
independent work across the store, so separate workers own separate parts
of it.

**Consequences.**
- The core stays pure and free of `@unsafe`, so laws can cover the store.
- Structures holding handles have two representations, inline and in the
  store; rope and dict code handles both.
- Parallel evaluation depends on partitioning: the architecture sketch's
  "Pages and rounds" proposes pages owned linearly by workers, granted
  between parallel rounds. EvalSpike measures before anything depends on
  it.
