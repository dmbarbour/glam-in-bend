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

## Questions

- Throughput and memory of glam's own node set (Bind, Copy N, Data, eraser)
  as a Bend step machine, against the hvm5 baseline.
- How lazy fields inside data meet net sharing: a field as a net port shared
  through `Copy` fans, or a memo cell (evaluated once, reclaimed by marking;
  see the [architecture sketch](Architecture_2026-10-26.md)) that a `Data`
  payload points to.
- What growing the store costs, and whether laws guard capacity, linearity
  and free-list conservation cheaply.
- What parallelism Bend's parallel calls can find in net reduction.

## Steps

1. `spike-net-store` — the net store: nodes in a flat `Array`, a free list,
   growth by copying into a larger array. Laws: allocation stays in bounds;
   allocating and freeing conserve cells.
2. `spike-net-rules` — Bind, Copy, Data and eraser interactions as one
   fuel-driven loop over a stack of active pairs. Law: a rewrite keeps every
   live port wired exactly once.
3. `spike-lowering` — a tiny untyped lambda calculus with numbers, lists and
   dicts, built as Bend values (no parser), lowered to nets.
4. `spike-lazy-data` — lazy dict fields both ways, as ports and as memo
   cells, on workloads that share a field many times and that copy a large,
   mostly unread dict.
5. `spike-measure` — interactions/s, peak cells, check and build times, JS
   against native, at n, 2n and 4n; record the numbers here.
6. `spike-verdict` — decide the representation, record it in
   `docs/decisions/`, and retire this plan.

## Open questions

- Copy-copy pairing follows duplication identity (Design.md). Do hvm5-style
  labels suffice for the spike, deferring the GAL adaptation?
