# A forced net reduces to weak head normal form, erasing eagerly

`net-demand-whnf` · maintainer · rev faaf32c

**Context.** A lazy value is a net reduced on demand. EvalSpike's kernel
reduced every active pair to the end (`spike-node-layout`), which a lazy
value must not: demand needs a rule for how far to go.

**Decision.** By default a forced net reduces until its root holds a value
in weak head normal form, and reduces erasures eagerly, so dropped work
frees what it holds at once. Other normal forms and strategies are
admissible where they are guaranteed to terminate.

**Consequences.**
- The kernel reduces toward the root first and leaves other pairs pending;
  pairs that only feed erasers reduce as found.
- Reducing further is asked for explicitly, as an annotation might
  (EvalSpike's `spike-materialize`), and only with a strategy known to
  terminate.
