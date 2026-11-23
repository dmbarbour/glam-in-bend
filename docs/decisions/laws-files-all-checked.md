# Every laws file's changes are named in their commits

`laws-files-all-checked` · maintainer · rev b6c82c8

**Context.** A commit on main that adds, changes or removes a law names
it in a `Law:` trailer (`AGENTS.md`, Laws), and `scripts/check_laws.py`
checks so, in the commit-msg hook and over main's history. It read laws
only from files named `LAWS.bend`, while glam's laws had spread to files
beside their proofs (`glam/INDEX_LAWS.bend`, `JOIN_LAWS.bend`,
`SERVE_LAWS.bend`, `SPLICE_LAWS.bend`; `spike/HEAP_LAWS.bend`): a trial
merge of the index's branch asked trailers for 25 of the 71 laws it
changes (`docs/reviews/IndexPremises_2026-11-23.md`, F8).

**Decision.** The maintainer (2026-11-23), asked whether the check
should read every `*LAWS.bend`, main's history then rechecked against
them too: "Yes". A laws file is `LAWS.bend` or `X_LAWS.bend`.

**Consequences.**
- The hook and the history check read every laws file. Main's history so
  rechecked passes as it stands (2026-11-23): its commits changing those
  files named their laws.
- The rule against weakening a law on main without approval is enforced
  for every laws file, not `LAWS.bend` alone.

**Rule lives in:** `scripts/check_laws.py`, `laws_file`.
