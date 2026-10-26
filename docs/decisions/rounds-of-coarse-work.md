# Workers do coarse work in rounds; fairness comes across rounds

`rounds-of-coarse-work` · maintainer · rev dd5c912

**Context.** Bend parallelizes balanced fork-join calls, and each fork tree
costs barriers (about 8–19 µs a round here). Pages of the store are owned
linearly, so parallel workers must each hold the pages they touch.

**Decision.** A coordinator in the pure core runs evaluation as rounds:
it splits work into tasks, learns from each task which pages and thunks it
needs next, assigns tasks and pages to workers heuristically, and runs
several rounds under fuel. Each worker does coarse work per round. Not
every task runs every round: one whose pages are split between workers, or
which waits on a result better computed as a task of its own, sits out.
Fairness, where needed, comes from scheduling across rounds.

**Consequences.**
- Programs must expose concurrent tasks (sparks, reflection tasks,
  independent work) for rounds to pay off.
- A worker that finds a task needs a thunk it cannot proceed past records
  the requirement and goes on with its other work. The coordinator then
  attaches the task as one of the thunk's waiters, restored to the run
  queue only once the thunk is ready; a thunk no task is computing becomes
  a task of its own. A task waiting on pages becomes runnable once a worker
  can hold them all.
- The coordinator owes no task to any worker: assignments may change every
  round.
- Fuel starts as one unit per logical step, however large the step.
  Weights wait for performance profiles across several machines.
