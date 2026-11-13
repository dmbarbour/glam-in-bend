# glam's laws may rest on laws proven in third-party hub packages

`hub-laws-reused` · maintainer · rev 245f27c

**Context.** The proof ladder of `cells-freeze.nested.host` reads the
kernel's heap after writes, and the heap's words are a Bend array indexed
by shifts and masks. Other users have proven what that needs: the
ArrayLaws review (`docs/reviews/ArrayLaws_2026-11-13.md`) found
`lawful-arrays` proving a read after a write and `lawful-words` the
shifts and masks, both checked under the Bend glam pins with `--verdict`,
MIT, their statements reviewed by AI models but not yet by their
author's human reviewer. `vendored-sources` already imports hub code by
hash; whether glam's own laws may depend on another's proofs was open.

**Decision.** The maintainer (2026-11-13): "Yes, we can bring in some
third-party packages." glam's proofs may use laws proven in third-party
hub packages.

**Consequences.**
- A package is imported by its hash, as `vendored-sources` has it, and
  the agent reads the statements of the laws a proof uses before using
  them, saying in the plan beside the law which it relies on.
- The gate's verdict rechecks an imported package's proofs with glam's
  own, as imports of `PROOF.bend`; a package that stops checking under a
  new Bend fails the gate like glam's own proofs.
- `lawful-arrays@0.1.0.1` and `lawful-words@0.1.0.1` are the first, for
  `cells-freeze.nested.host.array` and `.words`.
- What the packages lack is listed by package in the ArrayLaws review,
  to offer upstream when the maintainer chooses.
