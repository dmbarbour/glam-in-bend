# A machine's limit is not a program's failure

`machine-limits-not-errors` · maintainer · rev 49ee041

**Context.** Demand stopped as stuck where its path's array, or a
collecting demand's net, could not grow (`spike/kstrat.bend`). Stuck is
an outcome of the program: a rule leaves a pair as it is, as a type
error would. Running out of memory says nothing about the program, only
about the machine and the run. The maintainer (2026-11-01): runtime
errors such as out of memory should not be expressed as glam semantics
errors like stuck; they should be distinguished.

**Decision.** A reduction that cannot go on for want of a resource
reports that apart from every outcome of the program: demand's state
"out of memory" where its path or its net cannot grow. Such a state is
the run's, not the value's: it may differ from run to run and machine to
machine, and is never cached as a lazy value's result (as a crash is
not).

**Consequences.**
- Demand has a state of its own for it (6), which the library and the
  kernel's reports name.
- The net still counts a failed growth among its errors (`P.h_err`), with
  the program's; counting it apart, and the eager strategies, which
  count only that error where a rewrite cannot grow the net, is
  `heap-strategies.erasure.load.cycle.oom`.

**Rule lives in:** `spike/kstrat.bend` (Demand: the states of `D`).
