# A step law concludes what the next step's premises ask

`step-laws-conclude-next-premises` · maintainer · rev 2dd4b88

**Context.** The serve's laws state each step (a cursor made, a join, a
crossing, the crossings' fold, a leave, the copy) over the pending
placeholders' invariant. Each concluded the invariant alone, though the
next step's premises also ask the words full and, after the copy, the
map full and the tracked nodes after laid out apart, each its own base.
The proofs had these facts, so that the laws composed only inside the
proof files (`docs/reviews/IndexPremises_2026-11-23.md`, P1; the second
reviewer's A1). The review proposed laws beside each step for them
(`_full`, `copy_lay`).

**Decision.** The maintainer (2026-11-23), asked to approve the merge
with each step law's conclusion widened instead: "Approved." One law a
step, its conclusion carrying what the next step's premises ask, its
premises stated once and its mutants unchanged.

**Consequences.**
- `cursor_pend`, `join1_pend`, `cross_pend`, `crossings_pend`,
  `leave_pend`, `leave_era_pend`, `join_pend` and `serve_ring_exact`
  conclude the invariant and the words full; `copy_pend` the words and
  the map full and the tracked nodes after laid out apart, each its own
  base.
- A law of several steps is proved through the steps' laws
  (`serve_pend`: `copy_pend`, then `crossings_pend`), nothing of the
  proof files but the heap's eta and the arrays' mirrors.
- A new step law states its conclusion so. A fact the next step asks
  that no law gives is a gap to list beside the law: the served
  cursor's lookup through the crossings, which the root's laws still
  take from a proof (`crossings_look`, tentative).

**Rule lives in:** `glam/LAWS.bend`, `glam/SERVE_LAWS.bend`;
`docs/Proving.md`, "Laws compose as functions".
