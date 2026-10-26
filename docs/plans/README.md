# Plans

A plan says how a piece of work proceeds: what it builds, in which steps,
and what is still open. Plans are working documents, edited as the work
moves. Reviews, in [`../reviews/`](../reviews/), check work and may carry
small fixes of their own. Standing docs win where they disagree with a plan,
and the reasons behind decisions live in [`../Decisions.md`](../Decisions.md).

## Lifecycle

1. **Draft** `docs/plans/<Topic>_<YYYY-MM-DD>.md` and list it under Active
   Plans. A plan the maintainer should see before building says so at its
   top.
2. **Edit as work proceeds.** Mark each step built, with its date and what
   it found; record decisions in `docs/decisions/` as they are made, and
   keep open questions current.
3. **Retire when done:** make sure its durable decisions are records and
   its standing rules live in standing docs; remove every reference to the
   plan from code and current docs; delete it; list its last commit under
   Retired. Recover a retired plan with `git show <commit>:<path>`.

## Step names

Every step has a name: kebab-case, in backticks, prefixed by its plan's
topic, and unique across all docs, e.g. `spike-net-store`.
- Refer to steps by name, never by number: numbers only order a list.
- A commit that advances a step ends with a `Plan-Step: <name>` trailer, one
  per step, before any attribution lines. Find a step's history with
  `git log --grep 'Plan-Step: spike-net-store'`.

## Active Plans

- [`DocsPort_2026-10-26.md`](DocsPort_2026-10-26.md): `docs-port-` steps
  adapting the imported design docs and samples: the maintainer's rulings,
  known errors, and removing what describes the Rust runtime.
- [`EvalSpike_2026-10-26.md`](EvalSpike_2026-10-26.md): `spike-` steps
  measuring how Bend 2 hosts glam's interaction-net evaluation, ending in a
  representation decision. Drafted for the maintainer's review.

## Retired

None yet.
