# Plans

A plan says how a piece of Blend's work proceeds: what it builds, in which
steps, and what is still open. Plans are working documents, edited as the
work moves. Standing docs (the README, `LAWS.bend`) win where they
disagree with a plan, and the reasons behind decisions live in
[`../Decisions.md`](../Decisions.md). These are glam-in-bend's rules for
plans, which Blend keeps (`blend-own-repository`).

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
topic, and unique across all docs (while Blend shares glam-in-bend's
history, across both projects'), e.g. `blend-laws`.
- Refer to steps by name, never by number: numbers only order a list.
- A commit that advances a step ends with a `Plan-Step: <name>` trailer,
  one per step, before any attribution lines. Find a step's history with
  `git log --grep 'Plan-Step: blend-laws'`.
- When a step breaks into smaller steps, write them down as it does: a
  sub-step is named after its parent with a dot (`blend-laws.order`, and
  `blend-laws.order.once` below that), and listed under the parent in the
  same plan as

      - `parent.sub` — disposition — what it does, and what it found

  where the disposition is `tentative`, `planned`, `contingent on` one or
  more steps in backticks, `active`, `built <date>` or `dropped <date>`,
  the reason after it. `tentative` is an idea, brainstorming that likely
  wants discussion before work; `planned` is accepted work, the
  maintainer's or agreed with them, waiting its turn. A trailer names the
  deepest step advanced; `git log -F --grep 'Plan-Step: blend-laws'`
  finds a step and its sub-steps.

## Active Plans

- [`Blend_2026-11-04.md`](Blend_2026-11-04.md): `blend-` steps for the
  tool, in Bend, its samples its tests; Blend maturing (types, imports,
  nested objects, laws and proofs in objects); Blend's own laws; and what
  lies beyond, its own repository among it. Reviewed by the maintainer,
  2026-11-04.

## Retired Plans

None yet.
