# Blend's benchmarks

How Blend's cost grows with the modules it emits. Each family is measured
at N, 2N and 4N, as one size hides superlinear growth.

- `families.bend` prints a module of N definitions of one shape, each
  definition i calling earlier ones, and a `main` calling the last:
  `chain`, i calling i-1; `fan`, i-1, i-2, i/2 and i/3; `dense`, every
  earlier definition.

      bend bench/families.bend chain|fan|dense N > module.blend

- `measure.sh` emits a family at N, 2N and 4N with Blend's built
  executable, each run capped (`scripts/capped.sh`, 4,000 MB and 600 s
  by default), and prints its instructions (`scripts/count.sh`, under
  `perf`) and seconds, recording them in the analysis store
  (`scripts/results.py`: a run, each size a row of `counts`, its seconds
  a metric). The modules and what Blend writes go to
  `results/bench` (out of git).

      bench/measure.sh chain|fan|dense N [MB SECONDS]

Results and what they found are in the plan step that uses them,
`blend-scale` (`docs/plans/Blend_2026-11-04.md`).
