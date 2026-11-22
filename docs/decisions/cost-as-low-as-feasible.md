# Cost is kept as low as feasible: no targets, trimmed in cycles, regressions resisted

`cost-as-low-as-feasible` · maintainer · rev 7501436

**Context.** The cost review (`docs/reviews/Cost_2026-11-22.md`,
`ladder-measure.roi`) found the cursor workload at about 7,600
instructions an interaction against the kernel's 590 to 940, and the
agent proposed setting a target per interaction once the first trims
were measured.

**Decision.** The maintainer (2026-11-22): "As for costs, the answer is
always: as little as feasible. It's almost always a tradeoff, but lower
costs are always a good thing and I wouldn't want to set a target just
squeeze down during performance cycles then resist regressions."

- No cost target, per interaction or per workload.
- Performance cycles squeeze cost down; what they win is kept by
  resisting regressions between them.
- A tradeoff against cost is still weighed as one: lower cost is
  always good, not always worth its price elsewhere.

**Consequences.**
- A change that raises cost is looked at, as AGENTS.md's 10% rule asks,
  and a measured regression is a finding, not a budget spent.
- Gate checks that catch growth (the ladder's growth families,
  `cells-freeze.sharing.cursors.growth.gate`) serve the second half of
  the rule.

**Rule lives in:** `AGENTS.md` (Measuring); `ladder-measure` in
`docs/plans/HelloLadder_2026-11-09.md`.
