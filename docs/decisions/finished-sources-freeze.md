# A wholly finished source's cell reduces to a frozen template

`finished-sources-freeze` · maintainer · rev b6d806f

**Context.** A function-valued cell keeps its net live as a source, each
use copying from it (`copy-reduced-function-nets`). A source stays live
for the run: nothing frees it or freezes it again, even once nothing is
left to reduce (`docs/reviews/Freeze_2026-11-21.md`, F2). A net with no
active pair and no vicious circle is finished wherever its interface
reaches, so freezing its finished part leaves no cursor (the same
review, F4): "a net freezes only insofar as nothing is left to reduce"
(`copy-reduced-function-nets`).

**Decision.** The maintainer (2026-11-21): "When a source is wholly
finished, its cell should reduce to an evaluated value, a frozen net
template. As for whether the original is released, that depends on our
tactic for cursors. We could rely on cell-layer GC like we roughly
intend for other partial values, or something more specializes. This
will need more design."

- A source found wholly finished is frozen whole, and its cell's value
  becomes the template; its later uses are splices, with no ring, no
  positioned demand and no crossings.

**Consequences.**
- Finding a source wholly finished is a check after its reductions;
  early evaluation and the net's collection look for chances to make it
  so (`early-evaluation-optimization`).
- The template value is what persistent caching may key, once its form
  is chosen (`cells-freeze.format`).
- Steps: `cells-freeze.whole`, `cells-freeze.release` (the Cells plan).
