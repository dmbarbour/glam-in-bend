# A forced net reduces to weak head normal form

`net-demand-whnf` · maintainer · rev c528e1c

**Context.** A lazy value is a net reduced on demand. EvalSpike's kernel
reduced every active pair to the end (`spike-node-layout`), which a lazy
value must not: demand needs a rule for how far to go. Demand was first
built erasing eagerly, reducing every pair an eraser made as found, so
dropped values freed what they held at once; the maintainer judged that
not what was wanted (2026-10-28): unneeded work is better found by
analysing nets ahead of time.

**Decision.** By default a forced net reduces until its root holds a value
in weak head normal form, and reduces only the pairs that lie on the way.
Other normal forms and strategies are admissible where they are
guaranteed to terminate.

**Consequences.**
- The kernel reduces toward the root and leaves other pairs in the net;
  a computation only an eraser takes is never started (`K 0 Ω` is 0), and
  a value dropped off the path stays in the net, garbage until the net
  goes.
- Eliminating unneeded work is an analysis of nets before evaluation, not
  a reduction strategy.
- Reducing further is asked for explicitly, as an annotation might
  (EvalSpike's `spike-materialize`), and only with a strategy known to
  terminate.
