# Scheduling decides the order diagnostics are observed in

`diagnostic-order-follows-schedule` · maintainer · rev dd5c912

**Context.** With tasks evaluated in parallel rounds, several may fail or
log before any one result is demanded. Results stay independent of
scheduling, but which diagnostic surfaces first need not.

**Decision.** The coordinator's scheduling, heuristic but deterministic
given the shell's input log, decides the order in which diagnostics are
observed. Results never depend on it.

**Consequences.** Replaying a run's input log reproduces its diagnostics in
order. Two live runs, or two builds with different heuristics, may report
the same failures in different orders.
