# Agent Notes

This repository implements glam, a high-level language for assembly-level
software description, in Bend 2. The Rust bootstrap at
github.com/dmbarbour/glam is reference, not specification (`host-bend2`).

When using Bend:
- run `bend guide` to learn it
- use `LAWS.bend` to keep important rules
- before proving anything, read `docs/Proving.md`, `docs/BendIssues.md`
  and the lessons recorded in the headers of the proof files already
  written: Bend's shortfalls have workarounds that cost hours to find
  again
- run `bend PROOF.bend` before committing
- parallelize the code whenever possible

## Reading

Required reading:

- `docs/DistilledDesign.md` - a compressed view of the target design
- `docs/Decisions.md` - why things are as they are, indexing `docs/decisions/`
- `docs/plans/README.md` - how work proceeds, and the active plans

Contingent:

- When writing glam ".g" code: `docs/SyntaxCheatSheet.md`, then
  `docs/Syntax.md` for details and motivations
- When contemplating overall design: `docs/Overview.md`,
  `docs/DesignPrinciples.md`, `docs/Design.md`
- Macros, direct-style assembly, the command line: `docs/Macros.md`,
  `docs/DirectStyleAssembly.md`, `docs/CLI.md`
- When proving: `docs/Proving.md`, what the proofs so far have taught
- When Bend falls short: `docs/BendIssues.md` tracks shortfalls with their
  upstream issues; `bench/` holds programs that measure and reproduce them.
  Comment upstream only when the maintainer asks.

## Setup

`scripts/dev-setup.sh` installs the pinned Bend release, checked by hash,
links `clang`, installs `perf`, the LLVM profile tools, Node and Lean
(for `--verdict`), builds
GCC 16 from source (the first time, a quarter of an hour or more), and
enables the commit hooks; run it once per container.
`scripts/cgroup-delegate.sh` lets `scripts/capped.sh` cap memory in the
kernel instead of polling; run it at each container start.

## Dev Cycle

- Work proceeds through plans in `docs/plans/` and reviews in
  `docs/reviews/`; their READMEs give the lifecycle and step names.
- Commits that advance a plan step end with `Plan-Step: <name>` trailers,
  before attribution lines.
- Record decisions in `docs/decisions/` when they are made, not only when a
  plan retires.
- Keep slices narrow and testable. Check a claim relayed from another agent
  against its source before acting on it.

## Working Rules

Lessons carried over from the Rust bootstrap:

- Prefer narrow, testable slices. Add a focused regression before a broad
  fix.
- Valid and invalid samples are executable syntax specifications.
- Fenced `g` blocks in the standing docs are examples that must parse, once
  a parser exists; put pseudocode and grammar notation in indented blocks.
- A crash on user input is a bug, never semantics: a Bend fail-stop (a `Nat`
  past 2^48, a saturated count, an array too deep) reached from user input
  is one too. Report a failure instead, and never cache a crash as a lazy
  result.
- Evaluation is pure demand. Reflection may inspect evaluation; evaluation
  never observably depends on reflection.
- Retryable waits and unresolved promises are scheduler states, not errors.
- A front end receives raw bytes and a narrow context, never filesystem
  authority.
- Keep implementation claims out of design docs: DistilledDesign is intent,
  not implemented behavior. Give each invariant one authoritative owner and
  link to it from elsewhere.
- When removing a check, tell redundant work from a deliberate boundary.
- An ordering question in the IO shell or Bend's runtime needs a forced
  ordering; repeated passing runs prove nothing. Prefer laws as evidence.
- Before declaring a transition done, audit it against every named
  invariant and acceptance criterion: tests are evidence only for what they
  exercise.
- Run the full gate every time. A check once run only periodically let a
  regression go unnoticed for weeks.
- Code needed in several variants is written once as a template (`~`
  parameters) where Bend's templates serve; otherwise it is generated, by
  a Bend program where possible, into files of its own that nobody edits;
  list each in `scripts/check_generated.sh`, which the gate and the
  pre-commit hook run. Python is a development tool, never the source; no
  external macro processors (a preprocessor of our own, in Bend, may
  come), no scripts that rewrite sources (`generated-sources`).

## Measuring

- Measure workloads as families at n, 2n and 4n and fit cost to a + b·n^k:
  one size hides superlinear growth.
- Take sizes from the command line; Bend folds constant inputs away.
- Run anything that may run away, such as reducing a net that may not
  normalize, under `scripts/capped.sh MB SECONDS command`: an uncapped run
  once exhausted the machine's memory and crashed the session. Prefer
  native builds (`bend x.bend -o x`) for spike runs.
- Cap a run near its normal cost, so that one going astray shows in
  minutes, and stop it there: a hang is a fault to trace, not to wait
  out. A build of the kernel with every strategy peaks at 3 to 4.5 GB
  (the library's, 2026-11-04; the compiler's heap varies): build one at
  a time, and keep the caps of runs that overlap below the machine's
  free memory. Run
  `scripts/cgroup-delegate.sh` first, or the caps only poll.
- Bend folds a chain of functions into one compiled segment only while
  each has one caller; a second caller splits a function into a segment
  of its own, which costs every call through it. Before trusting a
  change to a hot path, `python3 -I spike/tools/sharing.py compare HEAD
  OUT` lists the functions whose segments moved, with their call sites
  (half a minute); `sharing.py audit OUT` lists the calls clang leaves
  out of line from the kernel's segments, Bend's unnamed leaves named by
  their parameters where they can be (a minute;
  `docs/plans/Codegen_2026-11-04.md`).
- Exact counters (interactions, cells) are signal; timings are trend data,
  recorded with the Bend version, the commit and the CPU. Count
  instructions too (`scripts/count.sh`, under `perf`): stable to a few
  parts in a hundred million where times wander by tens of percent.
  Bend leaves inlining to clang, which a small change can flip by 15%:
  before crediting or blaming a change, compare builds with every Bend
  function forced inline and profile-guided
  (`spike/tools/inline_build.sh`). For development, a spot check of the
  default and forced-inline builds takes about a minute
  (`spike/tools/spot.sh`); a merge takes the four builds
  (`spike/tools/count_builds.sh`, under two minutes).
- Judge a change case by case over a broad sample, not by totals alone:
  how many cases it improves, worsens and leaves alike, and why each
  exception moved (`spike/tools/gcbench.py compare` does so for the
  collecting demand over the whole library).
- Profile with `perf record -e instructions:u -c 100000` or a longer
  period, on runs of a tenth of a second or more: the kernel throttles
  sampling past `perf_event_max_sample_rate` (50,000 a second here), so a
  shorter period loses most samples. `perf annotate` (6.12) crashes on
  the large segments Bend inlines everything into; `--asm-raw` works.
- Baselines live in the plan or review that uses them; reusable workloads
  live in `bench/`.
- Bulk results go in the analysis store with the parameters that produced
  them: `scripts/results.py` (SQLite, `results/analysis.sqlite`, out of
  git) records a run's tool, parameters, commit and changed paths, Bend's
  version and the CPU, with its rows. `spike/tools/differential.sh`
  records every term; record other bulk runs there too, and cite run ids
  where a plan reports what they found.

## Gate

Run `scripts/check.sh` before every commit. It checks the docs (links,
decision records and their index, plan and review lists, step names), the
law history, then runs `bend PROOF.bend --verdict` (the proofs rechecked
by BendTT's kernel, itself proved in Lean; a pass kept while the file, its
imports, Bend and Lean are unchanged, `scripts/kept.py`, as each Bend
file's typecheck is), each `MUTANTS.txt`'s mutations against the laws
they name (`scripts/one_law.py`, kept the same way) and the library of nets
(`spike/library.txt`), and names the tree it checked. It times each
section and ends with their summary: watch it, a slow gate costing every
commit. A check whose inputs are unchanged keeps its pass (a verdict, a
Bend file's typecheck, the library's whole run; `scripts/kept.py`,
`spike/tools/library.py`), never a failure: 16 s when only Blend or the
docs change, near 200 s when the spike does, its verdict 57 s and the
library 96 s (2026-11-05). Report its result as
it is: a check skipped or too slow to finish is not a pass.

The library holds small nets kept for what they exercise, each with what
must hold. Add an entry for each fault or costly case found, shrunk first;
random corpora are for finding them, not the main test.

The commit-msg hook in `.githooks/` checks `Plan-Step:` and `Law:` trailers
before a commit is recorded, and the pre-commit hook runs the gate's quick
checks, a dozen seconds at most (the docs, the law history, the generated
files, the staged Bend files and the proofs they touch); the full gate
still runs before every commit. Enable it once per clone with
`git config core.hooksPath .githooks`.

## Laws

`LAWS.bend` states what must always hold; `PROOF.bend` proves it. Agents
write both.

- Comment each law with what it claims and the records it serves, as
  `# Record: <slug>`; a cited record must exist.
- On main, a commit that adds, changes or removes a law names it in a
  `Law: <name>` trailer. Comments and spacing are not law changes.
- Develop law changes freely on side branches off main, to show a proposal
  is viable; land them with a `--no-ff` merge or a squash commit that names
  the laws.
- Never weaken, change or delete an existing law on main without the
  maintainer's explicit approval: a law edited to fit the code proves
  nothing.
- Before proving, review `docs/Proving.md`, `docs/BendIssues.md` and the
  lessons in the existing proof files' headers; add what a new proof
  teaches to them. A law weakened to be cheap lists its missing pieces
  in the plan beside it (`docs/Proving.md`, What to claim).
- Mutate the code a new law follows, and keep the mutations in a
  `MUTANTS.txt` beside the proof file; `scripts/one_law.py` checks one
  law alone, and tries them against it, as the gate does for every
  mutants file.
- Prefer state shapes in which an invariant holds by computation; then its
  law costs a case split.

## Summaries

Always summarize:

- what you did
- semantic decisions made, emphasizing any you are not confident of
- ideas for improvements
- next steps
