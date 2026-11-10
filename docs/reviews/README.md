# Reviews

A review checks work against intent: a design, a plan's steps, a subsystem.
It lists findings, each with a stable ID (`F1`, `F2`, …; write
`<Review> F3` where ambiguous) and a verdict.

- **Quote what you find.** A finding cites the text or code it is about,
  with its location. A claim relayed from another reviewer or agent is
  checked against the source before it is reported.
- **Small fixes go in the review.** A finding may be fixed in the commit
  that records it, or by follow-ups citing its ID. Work that needs steps of
  its own becomes a plan.
- **Files and retirement follow [plans](../plans/README.md):**
  `docs/reviews/<Topic>_<YYYY-MM-DD>.md`, listed below while active, and
  retired by extracting decisions and removing references, then deleted
  with its last commit listed.

## Active Reviews

- [`Direction_2026-11-09.md`](Direction_2026-11-09.md): the direction
  glam-in-bend has taken, the spike against the path to the product, and
  what to do or stop doing to get there; drafted for the maintainer at
  their request.
- [`Heap_2026-11-09.md`](Heap_2026-11-09.md): the heap's options and
  intentions toward high parallelism, where the current plans hinder
  it, and alternatives free of the Rust bootstrap and the sketch: heaps
  per net, nets as heaps; two reviewers, the agent and Fable; drafted
  for the maintainer at their request.
- [`HeapFable_2026-11-09.md`](HeapFable_2026-11-09.md): the second
  reviewer's review of the same question, by a Fable sub-agent, kept as
  written beside `Heap_2026-11-09.md`, which summarizes it.
- [`InsideData_2026-11-10.md`](InsideData_2026-11-10.md): the design
  round of `cells-lazy-data`, on how data holds a function's net, frozen
  or live. Revised after two rounds of the maintainer's answers.
  - The first draft's closures are withdrawn because they lost the work
    of partial applications.
  - The build already loses that work in two places (measured).
  - A function in data is a live template, the maintainer's batch
    materialization: finished parts frozen, unprocessed ones behind
    cursors in the source.
  - Two questions remain: whole copies or live templates first, and
    cursors or ports within a net.

  Drafted for the maintainer.

## Retired

- `LawsInBend_2026-11-06.md`: where Blend writes laws and proofs, against
  how Bend checks them; its decisions in Blend's `blend-laws-in-module`,
  built as Blend's `blend-module-laws`; last commit 03cb4ac.
