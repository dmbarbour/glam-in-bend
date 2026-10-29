# Code that must be written many times is generated, by Bend

`generated-sources` · maintainer · rev 828f025

**Context.** Bend does not specialize code at compile time
(`docs/BendIssues.md`, "Compile-time specialization"), so a hot path wanted
in several variants, such as the kernel's rewrites with and without a
strategy's stack, must exist once per variant: a shared helper on a hot path
costs its callers 4% to 12% (HeapModel's `heap-strategies.stack` and
`heap-strategies.twostack.cheaper`). The spike already generates its
rewrites from the rule table with a Bend program. A macro processor such as
M4, or scripts that rewrite sources in place, were the alternatives raised
(the maintainer, 2026-10-29).

**Decision.** Where code must exist in several variants, a generator writes
it into files of their own, committed beside it and never edited by hand.
Generators are Bend programs where they can be, Bend being the more
reproducible over time; Python serves as a development tool, never as the
primary expression of source. No macro processor, and no script that
mutates hand-written sources. The spike may carry an awkward generator for
several families; the main code is not to be written this way.

**Consequences.**
- `scripts/check_generated.sh` regenerates every generated file it lists
  and compares, never writing; the gate and the pre-commit hook in
  `.githooks/` run it, so what was developed and tested is what the
  generators produce.
- A string builder such as the hub's `bend-kit-fmt` suits a generator; its
  `{}` holes clash with Bend's own braces (`True{}`), so templates there
  would escape every pair.

**Rule lives in:** `AGENTS.md`, "Working Rules"; the list of generated
files in `scripts/check_generated.sh`.
