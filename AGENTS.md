# Agent Notes

This repository implements glam, a high-level language for assembly-level
software description, in Bend 2. The Rust bootstrap at
github.com/dmbarbour/glam is reference, not specification (`host-bend2`).

When using Bend:
- run `bend guide` to learn it
- use `LAWS.bend` to keep important rules
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
- When Bend falls short: `docs/BendIssues.md` tracks shortfalls with their
  upstream issues; `bench/` holds programs that measure and reproduce them.
  Comment upstream only when the maintainer asks.


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

## Measuring

- Measure workloads as families at n, 2n and 4n and fit cost to a + b·n^k:
  one size hides superlinear growth.
- Take sizes from the command line; Bend folds constant inputs away.
- Exact counters (interactions, cells) are signal; timings are trend data,
  recorded with the Bend version, the commit and the CPU.
- Baselines live in the plan or review that uses them; reusable workloads
  live in `bench/`.

## Gate

Run `scripts/check.sh` before every commit. It checks the docs (links,
decision records and their index, plan and review lists, step names), the
law history, then runs `bend PROOF.bend`, and names the tree it checked.
Report its result as it is: a check skipped or too slow to finish is not a
pass.

The commit-msg hook in `.githooks/` checks `Plan-Step:` and `Law:` trailers
before a commit is recorded. Enable it once per clone with
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
- Prefer state shapes in which an invariant holds by computation; then its
  law costs a case split.

## Summaries

Always summarize:

- what you did
- semantic decisions made, emphasizing any you are not confident of
- ideas for improvements
- next steps
