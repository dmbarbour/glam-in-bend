# Corruption is detected and reported where the check costs nothing

`corruption-reported-when-cheap` · maintainer · rev b6c82c8

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
- A descent of a copy's index (`glam/index.bend`) raises the kernel's
  error (`P.err_if`, the error count in the heap's header) when it does
  not end at a leaf within its bound, and the run reports it as any
  kernel error.
- Laws over steps that descend the index take it real (the pending
  invariant over the index), so that no descent runs out and their frames
  allow no error.
- A check that costs on the normal path is not added for corruption:
  what the laws prove is not checked again.
- Once reported, the error stops the run (`implementation-errors-stop`).

**Rule lives in:** `glam/index.bend`, the descents' ends.
