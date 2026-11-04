# Blend translates objects and adds no Bend logic of its own

`blend-adds-no-bend-logic` · maintainer · rev b8e32bc

**Context.** Blend reads `.blend` files and writes `.bend` files, its
objects vanishing in the translation (`blend/README.md`). Writing its
reader in Bend, the agent turned each pair of functions that would call
each other into one loop over a state record, as Bend has no mutual
recursion, and suggested that Blend might one day do that for its users.
Its samples leave types, laws and proofs to Bend.

**Decision.** The maintainer (2026-11-04): Blend does not implicitly
provide Bend-layer logic. What a definition says in Bend means what Bend
makes of it: two definitions that call each other are an error in Blend
as they are in Bend, by the principle of least surprise. Blend's own
work is its objects (names, inheritance, priors, copies by the sharing a
definition states) and what it offers explicitly in its source, such as
macros, should it support them. Types, laws and proofs were left to the
Bend layer at first; each has use cases as an override or specialization
per family, and the maintainer brought them into objects sooner
(2026-11-04): types as members (`blend-types`), laws and proofs as
members (`blend-object-laws`), each emitted as Bend.

**Consequences.**
- The sample `cycle` stays an error, and no step rewrites recursion.
- Any expansion beyond objects is a construct of Blend's own, named where
  it is used (macros; `static` definitions, `blend-partial`).
- Until those steps, a type, law or proof in a `.blend` file passes
  through as Bend, unprefixed and shared by every object.

**Rule lives in:** `blend/README.md`, The model.
