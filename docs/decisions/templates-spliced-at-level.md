# A top-level function is a template, spliced at the level where it is applied

`templates-spliced-at-level` · maintainer · rev 93243b7

**Context.** The static linker bound a module's top-level definitions
around `asm.result` as one binding group, which cannot hold recursion.
The cells review asked how a function value meets an application; the
maintainer agreed to try a splice at the applying level ("We'll try your
recommended approach", on the level offset) and to treat the protocol
"as an experiment" (2026-11-09), then approved the bridge plan, whose
first milestone, `bridge-recursion`, makes a recursive function a
template ("Alright, let's begin developing this bridge").

**Decision.** The maintainer (2026-11-09): a top-level function is a
template, its net lowered alone and closed, each name of a top-level
function in it a leaf, a data node holding that function's handle.
Demand meeting a leaf at an application splices a copy of the template
there: the leaf is freed, the copy's root linked to the application in
its place, and every level in the copy is raised by the application's
level. It stands as an experiment, its
evidence the differential run against the linker, proofs if confidence
needs them.

**Consequences.**
- Recursion, direct and mutual, runs through templates: each use copies
  the template whole, as lowered. `copy-reduced-function-nets` would
  either reduce it first or leave its unfinished work in the source
  behind cursors, and neither is built. So closed work in a function's
  body is done again at every splice, where the linker shared it: 147
  interactions and 8 splices a use
  (`docs/reviews/InsideData_2026-11-10.md`, F2, run 312 of the analysis
  store).
- The values a template names are root cells, forced once each on a
  task of their own. A value whose outcome is a function is spliced from
  its recipe at each use, as a template is, until frozen nets exist
  (`cells-data.root`, `cells-freeze`). Until then, each use redoes the
  work of the partial application it holds (the same review, F2): such
  a value is copied as `copy-reduced-function-nets` describes only
  once `cells-freeze` is built.
- A splice is no interaction: counts of interactions miss its cost, a
  copy of the template.

**Rule lives in:** `glam/splice.bend`, its header.
