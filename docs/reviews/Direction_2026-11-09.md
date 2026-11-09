# Direction — 2026-11-09

Drafted for the maintainer, at their request: the direction glam-in-bend
has taken, the spike measured against the path to the product, and what
to do, or stop doing, to get there faster while keeping performance and
correctness. Facts are as of main 56586bc (454 commits, 2026-10-26 to
2026-11-09). This review proposes; the maintainer decides. It creates no
plan, no step and no record.

## Where the work stands

The product's surface is known: the Rust bootstrap (github.com/dmbarbour/glam,
its raw docs read 2026-11-09) had a `.g` parser ("`--parse` runs only the
built-in `.g` parser.", its docs/CLI.md), an evaluator, a CLI with
configuration in glam source, reflection arguments, "one crate of about
2,100 unit tests" (its docs/plans/README.md) and an ELF sample
(`samples/README.md:22`, carried over here: "`hello_x86_64_linux/`
compiles a direct-assembly effect program into ELF"). It failed on its
collector, its concurrency and its performance (`host-bend2`). The 96
`.g` samples here are that surface's executable specification.

What exists here, against the Architecture sketch's layers
(`Architecture_2026-10-26.md:13-27`):

| Layer | State |
|---|---|
| IO shell: CLI, files, outputs | nothing |
| core: scheduler, tasks, rounds | nothing (`spike-page-rounds` unbuilt) |
| front end: bytes, tokens, syntax, lowering | nothing (`spike-lowering` unbuilt) |
| evaluator: live nets | the kernel: rules, pairing by levels, demand, erasure, operators, collection within a net |
| evaluator: memo cells, laziness, functions applied | nothing (`heap-cells`, `heap-freeze`, `heap-apply`, `spike-fixpoints`, `spike-lazy-data` unbuilt) |
| values: numbers, ropes, dicts | a `U32` placeholder (`netdata-numbers`, `arch-structures-spike` unbuilt) |
| store: pages, collection across cells | a page allocator (`spike-net-store`); no collector |

Code: `spike/` is about 20,000 lines of Bend (3,300 generated) and 29,030
lines of proof; Blend is 10,119 lines and 17,326 of proof. Commits by
`Plan-Step` prefix: heap 285, blend 93, spike 62, pairing 27, docs 13,
netdata 9, codegen 4, arch 0. In the last nine days: heap 164, blend 93,
every other prefix 27 together.

## Findings

**F1. Nothing runs end to end, and the project's largest risk is now
integration, which nothing measures.** One layer of seven exists, the
evaluator's inner loop, and it is fed hand-built nets. Whether lambda
lowering, nets, lazy cells, objects as open fixpoints over `self`, the
freer monad's effects and the scheduler compose, and what a real glam
program costs through them, is unknown. The Rust bootstrap's costs sat in
those upper layers as much as in its nets: its plans record "376 K
instructions a `.r ()` step" (its docs/plans/README.md) beside the need
for its net performance to improve, so the inner loop's speed is not what
alone decides the product's. Verdict: act; the first milestone should be
one sample from bytes to `asm.result` (Recommendations, 1).

**F2. The hard questions the spike named are the unbuilt ones.**
EvalSpike's own words: "**Fixpoints**, the maintainer's chief worry"
(`EvalSpike_2026-10-26.md:61`), and `spike-fixpoints` is unbuilt, its
`.await` tried on a branch and deleted; the Architecture sketch on the
store: "**This is the crux, and could sink the project if mishandled.**"
(`Architecture_2026-10-26.md:137`), and `heap-cells`, `heap-freeze`,
`heap-apply`, `spike-lazy-data` are unbuilt. EvalSpike's steps 4 to 13
are all unbuilt, `spike-verdict` among them; HeapModel's 4 to 7 likewise;
NetData waits on `netdata-review` entire. What was answered, pairing,
erasure, demand's walk, fusion, the kernel's layout, was answered to a
depth well past need. Verdict: act; reorder toward the unanswered.

**F3. Levels were perfected before learning whether glam's code needs
them.** EvalSpike, at the moment pairing was found hard: "glam's own
lowering may avoid the question: a function is data, copies share it,
and each call instantiates a fresh net with a fresh fan namespace, so
`spike-lowering` tests that." (`EvalSpike_2026-10-26.md:124-127`). Since
then NetPairing built `pairing-gal`, `pairing-fusion`,
`pairing-overhead`, `pairing-library` and worked `pairing-nets`, and plans
a Lean study; `spike-lowering` is unbuilt and `pairing-verdict` unreached.
Levels may well be needed inside one function's body, but the work that
says so, for glam's lowering rather than for optimal reduction of random
lambda terms, was deferred behind perfecting them. Verdict: act; build
`spike-lowering` next, then decide `pairing-verdict` on what it shows.

**F4. Effort went to depth, and the plans show it.** `heap-strategies` is
one step spanning `HeapModel_2026-10-27.md:299-3908`, with sub-steps to
depth 10
(`heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.propagate.writers.moves`),
87 built, 31 tentative, 15 dropped, 7 active, 5 contingent: a laboratory
notebook, not a plan. Four plans open with "the maintainer reviews this
sketch" (HeapModel's, "this model") and that step is unbuilt in each
(`arch-review` since 2026-10-26, the Architecture plan at 0 of 4 steps;
`heap-model-review`; `netdata-review`; `codegen-review`), though the
records show the decisions were made. One plan has been retired in two weeks. Status is
therefore hard to read off the plans, which is what they are for.
Verdict: act; trim and close (Recommendations, 3).

**F5. The kernel is tuned to eight digits on workloads nobody chose as
representative.** EvalSpike's open question stands since 2026-10-26:
"Which stand-in workloads represent real assemblies well enough, before a
parser exists?" (`EvalSpike_2026-10-26.md:874`). The workloads are Church
numerals (`succ`, `fma`, `lvl`) and 3,600 random lambda terms. Against
them the kernel's instruction counts are compared to a few parts in a
hundred million across four builds, inlining forced and profile-guided;
today's `blend-kernel-chain.calls` spent hours on a 1.5% difference, and
found one Bend quirk worth recording (`docs/BendIssues.md`, "A matched
number kept as its bits past a call"). Structural wins were real (fusion
−25% interactions; static links; the layout at hvm5's speed); the
remaining percent-level work transfers to the product only if these
workloads resemble it, which is unknown. Verdict: act; freeze
percent-level tuning until the slice yields workloads (Recommendations,
4); keep counting, since counts are cheap and the store keeps them.

**F6. "Throwaway" code carries 29,030 lines of proof.** EvalSpike: "The
code is throwaway; what it learns becomes decision records"
(`EvalSpike_2026-10-26.md:11-12`). The spike's proofs are 1.5 times its
code, its verdict takes 57 s, and `heap-laws-align` flags 17 of its 79
laws as misaligned with their intent. Laws over the rule table
(`rules_polarized`, `rules_linear`, `fusions-as-components`) are
load-bearing and cheap; much of the rest proves strategy variants that
the next step changes. Either this is the kernel, and `spike-verdict`
should say so and retire the spike framing, or it is a spike, and proving
it past the rule table is spent effort. Verdict: decide
(Recommendations, 2 and 6).

**F7. Blend grew from a vehicle into a project.** Codegen's sketch of the
vehicle, 2026-11-04: "A first directive, a copy per caller"
(`Codegen_2026-11-04.md:105`). Five days later Blend is 10,119 lines of
Bend with 17,326 of proof, C3 linearization, templates, imports, nested
objects bound late, laws and lemmas inside modules, `do` and operator
sugar over `self`, build stamps, a CLI, its own repository, a package
name and a 2,980-line plan with 132 built steps and 25 tentative. The
transition it serves has moved one family (`blend-kernel-chain.slice`),
measured 1.0% to 1.1% cheaper on demand (store run 285) after a first cut
2% dearer; the rest of `blend-kernel-chain`, `blend-kernel-loops` and
`blend-kernel-measure` are planned, and today's `blend-kernel-chain.calls`
found that `shared` cannot be dropped from `go` whatever the callers do.
Blend's proofs are the investment to question: its output is checked by
Bend and kept current by the gate, and the one Blend bug the kernel met,
copies dropped past the root file's count of definitions
(`blend-scale.copies-fuel`), was found by the transition, not by a law;
whether its laws earn their check time (3.6 s on every load, BendIssues
"Checking every proof at each load") is open. The maintainer chose glam
over Blend today; that choice should become policy. Verdict: scope
(Recommendations, 5).

**F8. The host is fragile, and the kernel is shaped by its compiler.**
Bend is pinned at 2.0.39 because 2.0.40 passes 6 GB emitting the kernel
and 8 GB on the library's program (`docs/BendIssues.md`, "Memory of
native builds", #2076); under 2.0.39 the library's program builds at 3 to
4.5 GB in about 55 s; clang's inlining flips a
build by 15% on a small change; a second caller splits a segment and
costs every rewrite; a matched `U32` carried past a call costs 40%. Much
of HeapModel and Codegen is engineering around these. They are facts of
the host, not of glam's design, and each Bend release may move them
either way (`host-bend2`). Verdict: watch, with a budget: keep the kernel
buildable under 2 GB, build the two or three families a runtime needs
routinely (`codegen-families`), build the rest only in the gate's library
run, check each release on the day, keep the JS target as the
portability check.

**F9. The standing docs and the implementation disagree on what nets are
for.** Design.md: "Toplevel semantics is a lazy, untyped lambda calculus.
For performance, users may implement computations and functions behind
explicit lambda-style interfaces using interaction nets"
(`Design.md:35-37`) and "Initially, we'll mostly use interaction nets as a
performance tool for difficult dataflows behind explicit lambda-style
interfaces" (`Design.md:499-501`); DistilledDesign likewise
(`DistilledDesign.md:11`). EvalSpike evaluates glam "through monadically
constructed interaction nets" (`EvalSpike_2026-10-26.md:3-4`) and
Design.md's own nets section ends "Lambda calculus becomes a design pattern
within interaction nets" (`Design.md:486`). The Rust bootstrap also
evaluated through nets, so this is the maintainer's choice, not drift;
but the standing doc should state the choice, because the critical path
differs. Nets everywhere: F2 and F3 are the path, and pairing must be
right for every lowered term. A lazy lambda calculus at the top, with
thunks and closures over the cells store and nets only behind
`interaction_net`: a conventional call-by-need machine, with NetPairing's
hard cases confined to user nets, where the spike found static labels
already right for nets without self-application. Verdict: decide; the
doc follows the ruling.

**F10. The working rules pull toward depth and nothing pulls toward the
product.** AGENTS.md: "Prefer narrow, testable slices" (`AGENTS.md:85`),
"Run the full gate every time" (`AGENTS.md:108`), "Mutate the code a new
law follows" (`AGENTS.md:223`), measure at n, 2n and 4n. Each is right,
and each rewards going deeper where one stands. No rule names the
milestone or asks what a session moved toward it, so sessions, agents
above all, optimize locally: a proven, measured, mutated slice of
whatever is nearest. Verdict: act (Recommendations, 8).

## What is going well

Keep all of this; point it at the product.

- Decision records with revisions, `Plan-Step` trailers, the results
  store with each run's commit and parameters, run ids cited where
  findings are reported.
- Measurement discipline: exact counters over timings, families at n, 2n,
  4n, four builds before crediting a change, segments audited.
- Laws over the rule table, which catch mutants and once caught the Rust
  bootstrap's pairing bug: duplication histories pair wrongly
  (`pairing-histories`).
- Fusion, erasure at write, static links and the node layout: structural
  gains, not tuning.
- The pure core behind an IO shell, and pages owned in rounds: coherent,
  derisked by measurement, and they remove the whole class of the Rust
  bootstrap's twelve concurrency defects by construction.
- Bend's shortfalls tracked with reproductions and upstream issues, the
  pin moved only to releases.

## Recommendations, in order

1. **A vertical slice, as a plan of its own.** One sample,
   `samples/hello/hello_lambda.g` or the smallest of them, from bytes to
   `asm.result` on stdout through real layers, with `U32` numbers and
   texts as lists if need be: a fuel-driven lexer and parser for the
   subset the sample uses, lowering to nets (`spike-lowering`, which also
   answers F3), cells enough for top-level definitions and one `self`
   knot (`heap-cells` minimal, `spike-fixpoints` minimal), `.r` and
   `.seq` through the freer monad, a shell that reads one file and writes
   one. Acceptance: the sample's output; then the other `hello/` samples
   one by one. Its by-products are what everything else waits on: the
   representative workloads (F5), the fixpoint and laziness costs (F2),
   and the first integration facts (F1). Two to three weeks, at the pace
   of the last two.
2. **Decide `spike-verdict` now**, on what is known: the kernel's layout,
   demand, erasure and operators are the representation. Retire EvalSpike,
   its durable findings to records, its unbuilt steps moved to the slice
   plan or HeapModel where each is needed. Stop calling the kernel
   throwaway, or stop proving it (F6).
3. **Trim the plans.** `heap-strategies`: extract what is decided (most
   is), keep the measurements in the store, park the 31 tentatives in a
   Later list, close the actives that the slice does not need
   (`erasure.kernel`, `walk.directed`, `kinds`, `fusions`, `twostack`,
   `cascade`) or finish them in a day each. Mark or decide the four
   review steps. A rule for the plans README: a step whose sub-steps pass
   depth three becomes a plan or closes.
4. **Freeze percent-level kernel tuning** until the slice gives a
   workload: no change for less than, say, 5% on demand, or unless it
   removes code. Counts are still taken (`spot.sh` is a minute) and kept.
5. **Scope Blend to what the kernel needs**: finish `blend-kernel-chain`
   if the next family moves in a day, else stop there; defer
   `blend-kernel-loops`, `blend-macros.alias`, `blend-perf2`, the
   pseudo-parser and the CLI's remaining steps; no new Blend laws. Give
   the rest a budget the maintainer sets, as a side project with its own
   repository already.
6. **A proof policy**, written in `docs/Proving.md`: laws for load-bearing
   invariants on stable code, the rule table, the store's conservation,
   later the collector's snapshot invariant and the scheduler's no task
   lost or duplicated; lemmas, not laws, for construction restated;
   nothing for a preprocessor's internals beyond what exists; a ceiling
   on the gate's proof time, and a law past it gets a model or a lemma.
7. **Host risk as a budget** (F8): the kernel buildable under 2 GB; the
   runtime's families built routinely, the rest in the library run;
   each Bend release tried on the day under `capped.sh`.
8. **A milestone in AGENTS.md**: a "Current milestone" section naming the
   slice and its acceptance, and the rule that a session's summary says
   what it moved toward it, with perf and proof work justified against
   it. Agents read AGENTS.md first; today it tells them how to dig, not
   where.

## Questions for the maintainer, and their answers (2026-11-09)

- F9: nets as the evaluator of every lowered term, or a lazy lambda
  calculus at the top with nets behind `interaction_net`? **Lambdas are
  a `.g` compiler concept, lowered through `interaction_net` at compile
  time; the core has no lambda** (the Rust bootstrap put them in its
  core for a convenient start and took a week to undo it;
  `lambdas-lower-to-nets`). F9 is resolved: the critical path is F2 and
  F3, and the kernel's data types are built to be adopted by the final
  evaluator, not as placeholders.
- F6: is the spike's kernel the kernel? **Most likely, in a couple of
  forms: a lazy one for ordinary evaluation, an eager one for a JIT.** A
  leaning, so `spike-verdict` still records it; but the kernel is not
  throwaway, and proving it is not spent effort. Recommendation 2
  stands as the writing-down; recommendation 6's policy applies to new
  laws.
- F7: Blend's budget, and whether its proofs continue. **Blend has wider
  interest, a separate repository and its own identity; completing it
  has independent utility and is not a waste.** Recommendation 5 is
  withdrawn as scope: Blend is a project of its own, and the question
  left is only how glam's and Blend's work alternate, which the
  maintainer decides session by session, as today.
- Recommendation 1: which sample, and which subset of the syntax, the
  slice targets first. **A part of `.g` is hard to make usable; the Rust
  bootstrap's hello samples built the syntax up incrementally.** So the
  slice follows that ladder rather than one chosen sample: the hello
  samples in the order of the syntax each introduces, the parser and
  the lowering growing a rung at a time, each rung's output the test.
  Drafted as [`HelloLadder_2026-11-09.md`](../plans/HelloLadder_2026-11-09.md).
- Recommendation 4: the threshold below which kernel tuning waits.
  **Push several features, then review performance; a +40% needs
  immediate attention; no confident policy beyond that.** A starting
  point, not a ruling: the spot check still runs at each kernel change
  and its counts go to the store; a movement past 10% on demand or the
  eager run is looked into before the commit, as the 40% was; smaller
  movements are noted in the plan and left for a performance review
  step that closes each feature plan.
