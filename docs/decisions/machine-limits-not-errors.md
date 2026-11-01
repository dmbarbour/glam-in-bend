# A machine's limit is not a program's failure

`machine-limits-not-errors` · maintainer · rev 413aa83

**Context.** Demand stopped as stuck where its path's array, or a
collecting demand's net, could not grow (`spike/kstrat.bend`). Stuck is
an outcome of the program: a rule leaves a pair as it is, as a type
error would. Running out of memory says nothing about the program, only
about the machine and the run. The maintainer (2026-11-01): runtime
errors such as out of memory should not be expressed as glam semantics
errors like stuck; they should be distinguished.

**Decision.** A reduction that cannot go on for want of a resource
returns an error of the runtime, out of memory, apart from every outcome
of the program. It is no state of the net: it says nothing of the net or
the value, only of the run (the maintainer, 2026-11-01), which may differ
from run to run and machine to machine, and it is never cached as a lazy
value's result (as a crash is not). Running out of fuel is of the same
kind.

**Consequences.**
- Demand's walk returns it where its path or its net cannot grow (code
  6, besides out of fuel, 4), which the library and the kernel's reports
  name; the program's outcomes are the others (done, needing a lazy
  value, stuck, a cycle).
- The net still counts a failed growth among its errors (`P.h_err`), with
  the program's; counting it apart, and the eager strategies, which
  count only that error where a rewrite cannot grow the net, is
  `heap-strategies.erasure.load.cycle.oom`.

**Rule lives in:** `spike/kstrat.bend` (Demand: the states of `D`).
