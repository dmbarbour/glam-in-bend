# Evaluator Spike — 2026-10-26

Find out how well Bend 2 hosts glam's evaluation before committing to a
representation: lazy, shared evaluation through monadically constructed
interaction nets (Design.md, "Interaction Nets"). **Drafted for the
maintainer's review before building.** The code is throwaway; what it
learns becomes decision records.

## Known (2026-10-26, Bend 2.0.39, native unless noted)

- A scattered `Array<U32>` read and write costs about 1.5 ns; the JS target
  is 3–5× slower.
- `pure_hvm5_mini`, an interaction-calculus evaluator in Bend, runs about
  14M interactions/s on one thread.
- Array indexes wrap silently: that demo answers wrongly, without error,
  once its live cells outgrow its fixed environment.
- The checker takes about 0.5 s for 3K lines; a native build about 1 s.
- Bend has no laziness and no shared mutable state outside `@unsafe` forked
  arrays (CAS about 6–10 ns, tested correct under contention); see the
  [architecture sketch](Architecture_2026-10-26.md), "The store". The
  maintainer chose the split heap (`split-heap`).
- Pages of a store can be owned linearly by parallel workers in safe Bend:
  2.3–2.7× on this 4-core machine with cache-sized pages, about 8–18 µs of
  dispatch per round (the sketch's "Pages and rounds").

## Questions

- Throughput and memory of glam's own node set (Bind, Copy N, Data, eraser)
  as a Bend step machine, against the hvm5 baseline.
- Whether the split heap (the sketch's option 1) holds up: ground data as
  Bend data; lazies, function nets and non-ground structure nodes in the
  store; marking that visits each non-ground node once and grounds what
  has been forced.
- How lazy fields inside data meet net sharing: memo cells in the store, or
  ports shared through `Copy` fans.
- What growing the store costs, and whether laws guard capacity, linearity
  and free-list conservation cheaply.
- What pages owned by workers in rounds recover in parallelism for real
  evaluation, and which policies (round length, moving a page or queueing
  a demand with its owner) serve it best.

## Steps

1. `spike-net-store` — the store as pages: cells in fixed-size `Array`s,
   a free list per page, handles of page and slot in one `U32`, growth by
   adding pages. Laws: allocation stays in bounds; allocating and freeing
   conserve cells.
2. `spike-net-rules` — Bind, Copy, Data and eraser interactions as one
   fuel-driven loop over a stack of active pairs. Law: a rewrite keeps every
   live port wired exactly once.
3. `spike-lowering` — a tiny untyped lambda calculus with numbers, lists and
   dicts, built as Bend values (no parser), lowered to nets. Functions are
   nets with arity (`functions-are-nets-with-arity`): a partial
   application's copies share the reductions of its source.
4. `spike-lazy-data` — the split heap and its collector, against lazy fields
   as ports, on workloads that share a field many times, copy a large
   mostly unread dict, keep many persistent versions of a large lazy dict
   (the case where careless marking revisits shared structure), and churn
   a nursery beside a long-lived namespace.
5. `spike-page-rounds` — independent tasks on workers that own their pages,
   in rounds; requests for pages held elsewhere served between rounds.
   Laws: a round loses or duplicates no page and no task.
6. `spike-measure` — interactions/s, peak cells, check and build times, JS
   against native, parallel speedup, at n, 2n and 4n; record the numbers
   here.
7. `spike-verdict` — decide the representation, record it in
   `docs/decisions/`, and retire this plan.

## Open questions

- Copy-copy pairing follows duplication identity (Design.md). Do hvm5-style
  labels suffice for the spike, deferring the GAL adaptation?
