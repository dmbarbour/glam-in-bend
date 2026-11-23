# A property that matters, or is easy to state, is a law rather than a test

`laws-over-tests` · maintainer · rev 4713121

**Context.** The index's merge left the materializer's own code outside
every law and mutant: the serve's laws restate its sequence by hand,
and only the ladder's samples would catch a change to it. One template
freeze builds also lies outside the serve's laws' premises
(`docs/reviews/IndexHolistic_2026-11-23.md`, F3 and F6; the second
reviewer's H2). The review asked whether the materializer's sequence
should come under the laws, or be left to tests and the ladder.

**Decision.** The maintainer (2026-11-23): "we should favor laws over
tests for any property important (for correctness or performance) or
easy to express and enforce lawfully." The general decision recalled is
`docs/Proving.md`'s "Prove what is important, and what is easy" (the
maintainer, 2026-11-22), stated there but never recorded; this records
it, with laws favoured over tests.

**Consequences.**
- The materializer's composition of the serve's steps comes under the
  laws, its mutants with it. Laws over its own functions replace
  statements that copy its sequence by hand (`cursor-laws.materializer`).
- What the serve's laws leave out, such as a template freeze builds, is
  brought under them where it can be stated, rather than noted as not
  claimed.
- A test stays where a law cannot yet say it, and for what it measures
  (costs, the ladder's bytes). A check added in the meantime, like the
  frontier's, names the law meant to replace it.

**Rule lives in:** `docs/Proving.md`, What to claim.
