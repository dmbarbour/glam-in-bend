# Workers do coarse work in rounds; fairness comes across rounds

`rounds-of-coarse-work` · maintainer · rev b2ec86c

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
- A task waiting on a page becomes runnable once it holds its pages; a task
  waiting on a thunk is tracked as that thunk's waiter and restored only
  once the thunk is ready.
- Fuel per task is heuristic, designed so a round's workers finish near
  together.
