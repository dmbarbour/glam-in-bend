# Evaluator Spike — 2026-10-26

Find out how well Bend 2 hosts glam's evaluation before committing to a
representation: lazy, shared evaluation through monadically constructed
interaction nets (Design.md, "Interaction Nets"), on the split heap
(`split-heap`, `store-pages`) run in rounds (`rounds-of-coarse-work`).
Approved by the maintainer 2026-10-27, after a revision following their
first reading; skip a step (and its dependents) and say so here if it
sprawls. Paused the same day after `spike-net-rules`, for
[NetPairing](NetPairing_2026-10-26.md). The code lives in `spike/`, with
its own `LAWS.bend` and `PROOF.bend`. The code is throwaway; what it
learns becomes decision records. How fans pair has a plan of its
own, [NetPairing](NetPairing_2026-10-26.md).

## Known (2026-10-26, Bend 2.0.39, native unless noted)

- A scattered `Array<U32>` read and write costs about 1.5 ns; the JS target
  is 3–5× slower.
- `pure_hvm5_mini`, an interaction-calculus evaluator in Bend, runs about
  14M interactions/s on one thread.
- Array indexes wrap silently: that demo answers wrongly, without error,
  once its live cells outgrow its fixed environment.
- The checker takes about 0.5 s for 3K lines; a native build about 1 s.
- Bend has no laziness and no shared mutable state outside `@unsafe` forked
  arrays; the maintainer chose the split heap (the
  [architecture sketch](Architecture_2026-10-26.md), "The store").
- Pages of a store can be owned linearly by parallel workers in safe Bend:
  2.3–2.7× on this 4-core machine with cache-sized pages, 8–19 µs a round
  (the sketch's "Pages and rounds").
- A parallel call reached deep inside a task still runs in parallel: eight
  branches, each forking only after sequential work, ran 3.7× faster on 8
  threads than on 1; a fork tree at the surface, about 5.5×.
- An array cell of a small constructor costs 4 bytes for one `U32`
  field, 8 for two, 16 for three (`Bool` counting as one); in a sum type
  with a variant holding a list, as the store's payloads are, every cell
  costs 32 bytes whatever its variant holds (2026-10-27, 1M to 4M cells,
  linear). So shrinking one variant saves nothing there; a control, with
  two ports, could instead keep its index and offset in its node's free
  fourth word.
- Bend generates no code at run time. In-process fast paths are therefore
  specialized loops (an HVM5-style interaction loop, operator steps); a
  heavy, stable kernel could also be compiled out of process and run
  through the shell, as an accelerator.

## Questions

- Throughput and memory of glam's own node set (Bind, Copy N, Data, eraser)
  as a Bend step machine, against the hvm5 baseline.
- Whether the split heap holds up: ground data as Bend data; lazies,
  function nets and non-ground structure nodes in the store; marking that
  visits each non-ground node once and grounds what has been forced.
- How lazy fields inside data meet net sharing: memo cells in the store, or
  ports shared through `Copy` fans.
- How logical copies work over pages, after the Rust bootstrap's cursors: a
  copy materializes its source frontier by frontier, and a source pair
  reduces once, in its source, for every copy.
- When a net, or part of one, has no evaluation left, and how compactly it
  can then be held: like a forced thunk, as ground data outside the traced
  heap, copied whole without handle indirection, or compiled to operator
  steps.
- **Fixpoints**, the maintainer's chief worry: what object knots, recursive
  binding groups, recursive functions and `.fix` cost, and how recursion
  avoids unfolding through fans.
- Which nets, or parts, an HVM5-style interaction loop could run faster:
  the lowest-level fast path in-process.
- Where parallelism hides inside tasks, and how it reaches the cores:
  nested parallel calls within a worker, or new tasks for the coordinator.
- What growing the store costs, and whether laws guard capacity, linearity
  and free-list conservation cheaply.
- What rounds recover in parallelism for real evaluation, and which
  heuristics (round length, placing pages and tasks, when a needed thunk
  becomes a task of its own) serve it best.

## Steps

The core:

1. `spike-net-store` — the store as pages: cells in fixed-size `Array`s,
   a free list per page, handles of page and slot in one `U32`, growth by
   adding pages. Laws: allocation stays in bounds; allocating and freeing
   conserve cells.
   Built 2026-10-27 (`spike/store.bend`, `spike/bench_store.bend`). Laws
   `alloc_conserves` and `free_conserves` hold of the allocator's own
   metadata, a free list and `Nat` counts. "In bounds" got runtime guards
   instead: Bend cannot prove even `h & 4095 < 4096`, its `U32` facts
   being bit-level, so numeric laws must be stated over `Nat` models.
   Measured (1M nodes, native): allocate and write a node's four words
   76 ns, read 9 ns, free 14 ns; linear to 4M. Accessors cost 10–15 ns
   against 1.5 ns raw, rebuilding the store record each time: batching
   work on the current page is the obvious fix. Freed slots in old pages
   are not reused yet, since allocation draws only from the current page.
2. `spike-net-rules` — Bind, Copy, Data and eraser interactions as one
   fuel-driven loop over a stack of active pairs, fans paired by complete
   duplication histories (`pairing-histories`). Laws: a rewrite keeps
   every live port wired exactly once, and keeps the net polarized
   (`pairing-polarity-law`).
   Built 2026-10-27 (`spike/rules.bend`, `spike/net.bend`,
   `spike/tpl.bend`, `spike/test_net.bend`). Rules are data, a recipe of
   new nodes and links per kind pair, which the reducer interprets; laws
   `rules_polarized` and `rules_linear` hold of that table, so polarity
   and linearity are proven of the rules that run. Fans meet as copy
   against merge, the only polarity-compatible pair. Externals that are
   ports of the redex itself (the identity function's result wired to its
   own argument) are joined through the rule's links. An application
   meeting a builtin (`succ`, `add`) becomes a strict call node, its
   principal on the argument: it computes once the argument is data,
   distributes over a superposed argument (two calls, their results
   merged under the argument's fan identity) and passes an error value
   on, by rules in the table under its laws. It was first a list of calls
   polled until their arguments were data, which had no answer for a
   superposed argument: every pairing scheme then seemed to halt with no
   value.
   Found: identity, K, a function used twice and an n-fold chain reduce
   correctly. Where a fan duplicates a live function that holds fans,
   pairing decides the answer (native, 2026-10-27): extending both fans'
   histories on commutation, as the Rust bootstrap does, diverges on every
   Church exponentiation, `two two succ 0` included; static labels, one
   per lowering site and instantiation, are right on `m n succ 0` for
   distinct numerals (27 interactions for `two two`, 99 for `three
   three`) and diverge on self-application `(\t -> t t) n`; extending
   only the inner fan's history is right on all of those and on
   `(\t -> t t) two`, wherever a test-specific oracle could name the
   inner fan. Two meeting fans do not show which is inner; GAL's levels
   record it ([NetPairing](NetPairing_2026-10-26.md)). glam's own
   lowering may avoid the question: a function is data, copies share it,
   and each call instantiates a fresh net with a fresh fan namespace, so
   `spike-lowering` tests that. The spike has paired by static labels
   since, and `spike/trace.bend` traces its reductions
   (`pairing-trace`). The reducer works every active pair, needed or
   not: `K 5 (#3 #3 #3 succ 0)` grinds on the argument K discards.
   Reduction driven by demand, as glam's evaluation is, remains to be
   built, perhaps eager for erasure (the maintainer); `spike-lazy-data`
   meets it at the latest. One of 600 random terms still runs out of fuel
   this way under fused levels.
   Also found: allocating in whatever page was focused opened a page per
   allocation once reduction focused full pages (2944 pages for 5000
   interactions, gigabytes, a crashed session); allocation now tries the
   current page, then an allocation page, then a new page.
3. `spike-lowering` — a tiny untyped lambda calculus with numbers, lists and
   dicts, built as Bend values (no parser), lowered to nets. Functions are
   nets with arity (`functions-are-nets-with-arity`).

Sharing:

4. `spike-materialize` — find nets, and parts of nets, with no evaluation
   left, and hold them compactly: ground data outside the traced heap,
   with no handle indirection, copied whole. Normalize under fuel when an
   annotation asks, and compile a net that only builds values to operator
   steps, after the Rust bootstrap's compiled nets.
5. `spike-cursors` — logical copies after the Rust bootstrap's cursors: a
   call copies its function's net lazily, frontier by frontier, and a
   source pair reduces once, in the source, for every copy, so partial
   applications share their work. Over pages, a copy may need its source's
   pages, or only the compact form of the parts it reads.
6. `spike-fixpoints` — object-self knots over mixins (one cell per knot,
   entries capturing its handle; linearization computed once per spec),
   recursive binding groups, self-recursive functions (each call
   instantiating a compact template through a reference, never unfolding
   through fans), and `.fix` with forward references. Strict recursive
   demand is a dependency cycle, found also across tasks' waits.
   Workloads: deep mixin chains, repeated `with` and `extend`, recursive
   functions, recursive do over assembly labels. Law: unfolding a knot
   once changes no observation.
7. `spike-lazy-data` — the split heap with a stop-the-world collector
   (the sketch's "Collection"), against lazy fields as ports, on workloads
   that share a field many times, copy a large mostly unread dict, keep
   many persistent versions of a large lazy dict (the case where careless
   marking revisits shared structure), and churn a nursery beside a
   long-lived namespace.

Parallelism:

8. `spike-page-rounds` — a coordinator running independent tasks on
   workers that own their pages, in rounds (`rounds-of-coarse-work`):
   tasks report the pages and thunks they need, thunk waiters are restored
   only when ready, and fuel is one unit per logical step. Then marking as
   tasks in the same rounds. Laws: a round loses or duplicates no page and
   no task.
9. `spike-deep-parallelism` — parallelism found inside a task: nested
   parallel calls for pure work over what its worker holds (its pages,
   split between the calls, and ground data), and new tasks for the
   coordinator where work needs pages or thunks held elsewhere. Deep
   parallelism may simplify the coordinator by making it recursive: a
   worker coordinates subtasks over the pages it holds.

Speed:

10. `spike-hvm5-jit` — find the nets, or parts, that fit an HVM5-style
    interaction loop (lambda-shaped, fans that labels pair correctly, data
    limited to its constructors), translate them, and run them on such a
    loop; measure the speedup and how much of real workloads qualifies.
    `pure_hvm5_mini` is a demo, not a built-in: the loop would be ours,
    perhaps a finally tagless interpreter specialized by Bend's `~`
    templates at compile time.
11. `spike-measure` — interactions/s, peak cells, check and build times, JS
    against native, parallel speedup, at n, 2n and 4n; record the numbers
    here.
12. `spike-verdict` — decide the representation, record it in
    `docs/decisions/`, and retire this plan.

## Open questions

- Which stand-in workloads represent real assemblies well enough, before a
  parser exists?
