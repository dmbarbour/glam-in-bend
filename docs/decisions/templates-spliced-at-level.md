# A top-level function is a template, spliced at the level where it is applied

`templates-spliced-at-level` · maintainer · rev 12b2ac1

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
  the template, as `copy-reduced-function-nets` copies a function's net.
- The values a template names are root cells, forced once each on a
  task of their own; a value whose outcome is a function is spliced from
  its recipe at each use, as a template is, until frozen nets exist
  (`cells-data.root`, `cells-freeze`).
- A splice is no interaction: counts of interactions miss its cost, a
  copy of the template.

**Rule lives in:** `glam/splice.bend`, its header.
