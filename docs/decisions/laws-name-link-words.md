# Laws name a port's link word through a model; a static has none

`laws-name-link-words` · maintainer · rev 1d0e08e

**Context.** The frame laws (`link_keeps`, `join_keeps`, `join1_keeps`,
`leave_keeps`) left out of their guarantees the word after every port
they link, `r + 1`, static ports included. A static has no node and no
link word, and `P.link_xx` writes none for it; for a static other than
the eraser, `r + 1` is an arbitrary node's header, which nothing writes
and which the laws then said nothing of (found with `crossings_keeps`,
2026-11-18). The maintainer asked that laws abstract the
representation, its details in definitions and proof lemmas
([`Refs_2026-11-18`](../reviews/Refs_2026-11-18.md), B1).

**Decision.** The maintainer (2026-11-18), on B1: "Sure." Laws name a
port's link word through a heap model shared by `spike/` and `glam/`:
`KMd.lw(r)`, a `Maybe`, none for a static, and `KMd.off.port(d, r, j)`,
word `j` not `r`'s link word. The frame laws state their link-word
premises through it, and the crossings' region (`RG.off.ports`) too.

**Consequences.**
- The four frame laws are strengthened: a static's `r + 1` is inside
  their guarantees. Each has a mutation that links a static as a node's
  port, refuted at that word, which their earlier premises could not
  refute.
- `RG.port.ok` is unchanged: it holds of every static by alignment, a
  member being a node's base and the heap's depth at least 2 (the
  review's Corrections); no law over `ring.ok` changes meaning.
- An encoding change touches `KMd.lw.k` and the proof lemmas that
  unfold it (`lx_keeps`, `link2`), not the laws' text.

**Rule lives in:** `spike/kmodel.bend`.
