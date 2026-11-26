# Laws reach multi-step evaluation iteratively, on scaffolding premises

`laws-across-steps-iterative` · maintainer · rev 1a07a55

**Context.** The loop's laws compose serves, but the host reduces
between them: `host.go` sets the host's demand going again, and the
kernel's rewrites pop the free list, push what they free and may relink
what a cursor faces. Carrying the cursors' invariant from one serve to
the next therefore needs a law that the kernel's steps keep it. That is
the kernel refinement's work (`kernel-refine`), and it is large. Asking
for it before the loop's laws are stated would hold them back.
([`Alloc_2026-11-26`](../reviews/Alloc_2026-11-26.md), the second
reviewer's F9.)

**Decision.** The maintainer (2026-11-26): "I want to eventually reach
a point where laws carry invariants across multi-step evaluations. But
I think asking for it up front is a bit much. So, we approach it
iteratively and use temporary scaffolding as needed."
- The goal is laws that carry invariants across multi-step
  evaluation.
- They are reached in steps. Each law is stated for what it composes,
  and what it cannot yet show stands as a premise: scaffolding that a
  later law removes.

**Consequences.**
- A scaffolding premise names, in its law's comment, what discharges
  it, and a plan step owns the discharge. A premise with no discharger
  named is a claim left out, not scaffolding.
- `serve_next` composes two serves with no kernel step between. Across
  the host's reduction, the cursors' invariant is a premise of the
  loop's laws, the per-serve contract, until `kernel-refine` carries
  it.
- The wiring premise (`net-obvious-errors`) is scaffolding of the same
  kind.

**Rule lives in:** `docs/Proving.md`, What to claim.
