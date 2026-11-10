# Evaluation ahead of demand is an optimization; divergence and reflection block it

`early-evaluation-optimization` · maintainer · rev 1bf6dc1

**Context.** The design round on laziness inside data asked whether a
captured local not yet evaluated may be forced where a function enters
data, or must stay lazy (`docs/reviews/InsideData_2026-11-10.md`). Other
records already reduce ahead of demand: `copy-reduced-function-nets`
reduces a function's net before copying it, and the maintainer's answer
on freezing (2026-11-09) reads "the obvious option is eager evaluation
of the function's net, reducing all active pairs". `net-demand-whnf`
admits strategies past weak head normal form only "where they are
guaranteed to terminate". DistilledDesign: "Assembly-time performance
never affects results, only speed"; a reflection task is "lazily
demanded"; and divergence is unobservable in evaluation.

**Decision.** The maintainer (2026-11-10): "We can evaluate early as an
optimization. Divergence or reflection tasks would be blockers."
Evaluation ahead of demand, whether forcing a capture, reducing a
function's net before it is frozen, or reducing any pair before demand
reaches it, is an optimization and never changes an outcome. It stops
where it might not end, under fuel, and before a reflection task, which
it does not emit. Whatever it leaves stays lazy.

**Consequences.**
- Laziness is the semantics. Captures, members and a function's body
  stay lazy; early evaluation only makes them cheaper.
- Fuel is the guarantee of termination that `net-demand-whnf` asks of
  a strategy past weak head normal form. A reflection task is the
  other stop.
- Freezing a function's net is early evaluation. It reduces until the
  net is done, the fuel runs out, or it is blocked, so a frozen net may
  hold what reduction left: a residue. How a template holds that
  residue, shared by its copies rather than duplicated
  (`bounded-duplication`), is open in the review above.
- Sparks also run work ahead of demand. How this record meets the
  bridge's note on sparks and reflection tasks, where annotations
  guide the policy (`bridge-parallel`), is open.
