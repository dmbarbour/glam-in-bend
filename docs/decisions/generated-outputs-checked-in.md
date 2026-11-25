# Generated sources are checked in, with their generators, marked generated

`generated-outputs-checked-in` · maintainer · rev 4713121

**Context.** `generated-sources` has variants written by generators,
committed beside them and checked current, Python a development tool only.
The proofs of the serve and the index's merge grew past it. Their text,
4.3 MB in `glam/PROOF.bend` and `glam/SERVE_PROOF.bend`, lines to 62,811
characters, is written by Python generators kept under the gitignored
`results/`, none in git. So a fresh clone can check the proofs but cannot
change them as they were made (`docs/reviews/IndexHolistic_2026-11-23.md`,
F1; the second reviewer's H1).

**Decision.** The maintainer (2026-11-23), asked whether proof files
written by programs fall under `generated-sources`, their generators
committed and checked by the gate: "Yes. Users should be able to build
with just Bend. Thus, generated sources via Python or even Blend should
be checked in. Ideally, such sources include a comment that they're
generated."

**Consequences.**
- A file a program writes is committed with the program that writes it,
  whether in Python, Blend or Bend. A user needs nothing but Bend to build
  and check: the generated output is in git, and its generator matters only
  to whoever changes it.
- Each such file says at its top that it is generated, and by what.
- `scripts/check_generated.sh` lists each, and the gate checks that its
  generator reproduces it.
- A proof file kept by hand since a program first wrote it says so, and
  which of its sections a program still writes.

**Rule lives in:** `scripts/check_generated.sh`; the generated files'
headers.
