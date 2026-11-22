# Drops at one index fuse into a run, peeled at any index or crossed whole

`drop-runs-fuse` · maintainer · rev 5fe60b4

**Context.** Only raises fused (`fuse-control-runs`). A drop by more than
one was defined by `drops-stop-at-index`, b unit drops at n, and the
one-wire model had checked drop runs (NetPairing's
`pairing-fusion.drops`, 2026-11-13), but random terms rarely made two
drops meet (analysis store run 320), so the kernel's part waited for "a
workload that shows drops piling up". glam's walk of a Scott list was
one: each recursive call is spliced a level deeper and leaves a unit
drop on the tail's wire, unfused, and each later step's controls cross
every one, so a walk of n costs 6n² + 15n + 9 interactions
(`docs/reviews/RecursionFable_2026-11-21.md`, the Cells plan's
`cells-recursion.depth`). The agent asked whether drop runs should be
allowed to fuse, the model checked first and the laws brought at merge.

**Decision.** Two drops at one index fuse into one dropping by their
sum, b unit drops at n: the maintainer (2026-11-21), asked whether drop
runs should be allowed to fuse now that a workload shows them piling up,
"Yes, let's work on this." How a run then meets a facing control is the
agent's, within that ruling, each choice one the model checks:

- A drop run facing a control it does not equal gives up one unit to
  meet it, the rest staying at its index, as the model found: a control
  crossing a run's units one at a time can reach the run's index
  partway, and the units left are then its partners.
- Unless the control crosses it whole: at another index, no drop run,
  and not above the run's index by less than its length. Such a control
  never sits at the run's index before the last unit, so it crosses each
  unit where it crossed the first, and each unit leaves alike.
- Two drop runs facing each other each give up a unit, both sides peeled
  against each other as they were. A drop run is never crossed whole by
  another, though in the one library net that tries it at a distance
  (`drop-runs-far`) crossing whole kept the logical interactions: a
  conservative choice, peeling never wrong.

**Consequences.**
- The one-wire model with the rule (`spike/tools/ctlwire.py --peel
  --drops --cross --shapes 0,6`): fused and unit reductions reach the
  same outcomes and logical interactions on every start of up to four
  controls at the checker's default bounds, indices to 2 and levels to
  5 (12,463,200), of up to three at indices to 4 and levels to 3
  (1,050,240), and on samples of 6, 8 and 10 (2026-11-22).
- Laws: `drop_units_are_run` and `drop_run_splits` (a run is its units;
  fusing and peeling a unit change nothing), `drop_run_passed_below` and
  `drop_run_passed_above` (where a control cannot reach a run's index
  partway), all over `spike/ctl.bend`'s model; `raise_compose` covers
  drop fusion. Not proved: the kernel's test (`P.cross_whole`, U32)
  against the model's window, and a raise run's own units against a
  drop run's; the model's enumeration and the library's drop-run nets
  check them, and mutations of the test fail those nets.
- glam's Scott walk costs 19n + 9. Over the library, the full
  reduction's interactions fall in 19 cases, demand's in 50, by up to
  19%, and none rise; the logical interactions are unchanged wherever the
  reduction finishes (store runs 334 and 335). Over 5,400 random terms
  (store runs 330 and 329) no value changes. Instructions rise 0.26% in
  the default build on the leveled workload, peeling entered only at one
  index or for a drop run.
- A walk of a Scott numeral by a fixpoint (`scott-walk-*` in the
  library) keeps a quadratic, demand about 0.8n² where it was 5.8n²: not
  drops but raises, the numeral built by exponentiation leaving a stack
  of n/4 at mixed indices that every step's beta carries
  (`pairing-fusion.drops.fixpoint`, `pairing-overhead.stacks`).

**Rule lives in:** `spike/val.bend` (`V.compose`), `spike/kprim.bend`
("Fusing controls", `compose`; "Peeling", `peel.amt`, `cross_whole`),
`spike/net.bend` ("Peeling"), `spike/kstrat.bend` (the profile's logical
interactions), `spike/ctl.bend` and `spike/LAWS.bend`;
`pairing-fusion.drops.kernel` in `docs/plans/NetPairing_2026-10-26.md`.
