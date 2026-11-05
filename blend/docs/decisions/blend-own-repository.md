# Blend is arranged as a repository of its own

`blend-own-repository` · maintainer · rev e443d92

**Context.** Blend grew inside glam-in-bend, as the vehicle for glam's
kernel (glam-in-bend's `codegen-vehicle`); it is meant to be shared
beyond it (`blend-home`), and the maintainer expects to split it off
soon (2026-11-05: arrange Blend as a repository, its records, checks and
benchmarks with it, for an easy separation later).

**Decision.** Blend is arranged within its directory as its own
repository would hold it: its code, samples, laws, proofs and mutants;
its benchmarks (`bench/`); its docs (`docs/`, this index and its
records, its plans); its gate (`check.sh`) and its agents' notes
(`AGENTS.md`). Its scripts work from its directory, writing under its
own `results/`, and its docs name its files from its root. The tools it
shares with glam-in-bend (`capped.sh`, `count.sh`, `results.py`,
`kept.py`, `one_law.py`, `check_docs.py`, `check_laws.py`) stay in
glam-in-bend's `scripts/`, found through `tools.sh`, until the split
copies them into Blend's own `scripts/`.

**Consequences.**
- While the two share a history, a step name is unique across both
  projects' plans, a commit may name a step of either, and glam-in-bend's
  gate runs Blend's.
- glam-in-bend's docs name Blend's files by their paths under `blend/`
  and its records by slug.
- A split copies the tools and filters the history; record revs then
  name glam-in-bend's commits, and want a map or a note.

**Rule lives in:** `AGENTS.md`, Layout.
