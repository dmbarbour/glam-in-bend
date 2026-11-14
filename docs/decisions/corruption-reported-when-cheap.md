# Corruption is detected and reported where the check costs nothing

`corruption-reported-when-cheap` · maintainer · rev f3bca8f

**Context.** A walk round a ring that runs out of fuel returned whatever
node it had reached, and an unlink wrote that node's word 3: a corrupt
ring was corrupted further, silently. The review of `join_exact`'s
premises asked whether such a walk should report an error, as the
splice reports its own (`P.err_if`), at the cost of changing the walks'
code and letting the frame laws allow the error count's word.

**Decision.** The maintainer (2026-11-14): "We're trying to avoid dynamic
checks. But where the cost is negligible, detect and return the memory
corruption error." Correctness is shown by proof, not guarded at run
time; but where a state that only corruption reaches is detected for
free, as a walk's fuel running out, the kernel's error is raised.

**Consequences.**
- A walk round a ring raises the kernel's error (`P.err_if`, the error
  count in the heap's header) when it runs out of fuel, and the run
  reports it as any kernel error.
- Laws over steps that walk allow the error count's word among the
  words they may write, where the ring is not shown exact; where it is,
  the walk never runs out and nothing is allowed.
- A check that costs on the normal path is not added for corruption:
  what the laws prove is not checked again (a join of a cursor with
  itself is excluded by proof, `cells-freeze.nested.host.join.self`).

**Rule lives in:** `glam/ring.bend`, the walks' ends.
