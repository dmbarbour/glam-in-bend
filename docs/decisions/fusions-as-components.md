# A fused op behaves as its components, and is proven to

`fusions-as-components` · maintainer · rev 25710ad

**Context.** The kernel fuses ops for speed: adjacent controls into runs
(`fuse-control-runs`), an eraser into a fan (the linear fans), and, by
events, a node with the eraser at one of its ports into a single node.
Lowering may recognize patterns too. Two events, plausible at sight,
were not exact: a dead application's, which a variable used outside its
function's body could tell, and a call's, which erased a function its
rule leaves stuck (`heap-strategies.erasure.kernel.exact` in
`docs/plans/HeapModel_2026-10-27.md`).

**Decision.** Every fusion or pattern optimization, in the kernel or at
lowering, behaves as the ops it stands for: against anything it can
meet, it reduces where they reduce, is stuck where they are stuck, and
leaves what they leave. A law proves each (the maintainer, 2026-10-30).
A fusion observes no data value, beyond whether a value is immediate; it
moves, copies or drops a payload as its components would. A level update
applied to a fusion gives what it gives the expanded form.

**Consequences.**
- No event for a dead application or a dead call; the dead application's
  rule is kept for where it is exact, as at lowering where a function's
  scope is known, and a dead call is a fused node of its own, stuck where
  a call is (`heap-strategies.erasure.deadcall`).
- An optimization without such a law is an experiment, not a feature.
- The laws compare kinds, wiring and data payloads' provenance; level
  updates are to be compared too, and control runs stated as their unit
  controls at the level of rules, not only of levels.

**Rule lives in:** `spike/LAWS.bend`, laws `linear_as_components` and
`events_as_components` (controls: `units_are_run`, `run_splits`,
`peel_pairs_units`).
