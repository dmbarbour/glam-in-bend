# Small local lazy computations may run twice; reflection and expensive work may not

`bounded-duplication` · maintainer · rev 8067136

**Context.** HeapModel asks of evaluation that "a thunk forced twice
computes once". Under parallel evaluation, holding to that makes a task
needing a lazy value that another task is computing stop and wait: an
interrupt that breaks Bend's balanced fork-join (the heap review,
`docs/reviews/Heap_2026-11-09.md`). Evaluation is pure, and
"Assembly-time performance never affects results, only speed"
(DistilledDesign), so a second evaluation gives an equal value. GHC's
parallel runtime lets cheap thunks be evaluated twice and locks only
expensive ones (Harris, Marlow and Peyton Jones, "Haskell on a
Shared-Memory Multiprocessor", Haskell Workshop 2005).

**Decision.** The maintainer (2026-11-09), reading "computes once" as a
cost bound: a small, local lazy computation may be duplicated. Two
things may not be:
- an emission to reflection, such as the task `anno refl:(...)` emits,
  which happens at most once, however cheap the task;
- expensive work, kept shared for work sharing: in `(expensive + 42)`,
  `expensive` is never duplicated.

**Consequences.**
- "Computes once" is a cost bound, kept wherever work is not small and
  local.
- What counts as small is a heuristic: a bound read from the template,
  a fuel bound at run time, or both, tuned from profiles.
- A computation that emits to reflection is either never duplicated or
  publishes its emissions once, whichever copy is kept; which is a
  design question.
- The heap review's second reviewer raised a question this leaves open:
  a step that mints an identity, `anno 'scope_unique`'s metadata or
  cells made at run time, must mint the same identity in every copy, or
  never be duplicated.
