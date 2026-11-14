# A walk round a ring takes as fuel the size of the heap that holds it

`ring-walks-fueled-by-heap` · maintainer · rev f3bca8f

**Context.** Bend asks every loop to end, so the walks round a copy's
ring of cursors (`rg.pred`, `rg.find`, `rg.situ` in
`glam/ring.bend`) took a fixed fuel of a million steps, and the laws
that follow a walk to its end (`pred_exact`, `unlink_exact`,
`join_exact`) had to require a ring shorter than a million. The
maintainer: "A fuel limit in law is terribly awkward. We could have an
abstract static-variable fuel limit, if necessary, but setting a number
like a million steps as a law doesn't feel right to me." The review of
`join_exact`'s premises (`docs/reviews/JoinExact_2026-11-14.md`, beside
the second reviewer's) found that the heap bounds a ring: an exact
ring's members keep their word 3 in distinct slots of the heap's words,
so it has no more members than the heap has words.

**Decision.** The maintainer (2026-11-14): straight to the heap's size,
from the words' array ("Array size seems more convenient"). A walk round
a ring takes as fuel the number of words in the heap's array.

**Consequences.**
- No law names a fuel. Until a pigeonhole lemma shows an exact ring no
  longer than the heap's words, the laws carry that bound in the heap's
  own terms (fewer cursors than `2^d` words); with it, the premise goes.
- The array's size needs no new premise: lawful-arrays gives it for a
  perfect tree (`size_pair`), unlike the header's capacity word, which
  would need a law that it matches the array.
- A walk reads the array's size once.
- A walk that runs out of fuel nonetheless is on a corrupt ring, and is
  reported (`corruption-reported-when-cheap`).

**Rule lives in:** `glam/ring.bend`, `rg.fuel`.
