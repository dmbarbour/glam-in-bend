# Benchmarks

Standalone Bend programs that measure what the design depends on, and
reproduce the shortfalls in [`docs/BendIssues.md`](../docs/BendIssues.md).
The gate checks that they still typecheck; nothing runs them automatically.
Build one natively, then run it:

    bend bench/bend/rounds.bend -o /tmp/rounds
    /tmp/rounds 3 1024 16384 16 +RTS --threads 8 -RTS

| Program | Measures | Arguments |
|---|---|---|
| `bend/rounds.bend` | parallel workers owning pages, moved between workers every round; the cost of a round | log2 workers, rounds, steps per worker per round, log2 cells per page |
| `bend/interleave.bend` | pure work sharing Bend's IO event loop with a computation sending every 10 ms | steps, slices, yield between slices (0 or 1) |
| `bend/zero_fill.bend` | making a zeroed array, filled word by word | log2 words |

Results on an i7-6700 (4 cores, 2 hyperthreads each), Bend 2.0.39,
2026-10-26:

- `rounds 0 1 134217728 16`: 159 ms. `rounds 3 1 16777216 16`: 70 ms on 8
  threads. Near-empty rounds (`rounds 3 100000 1 12`) cost about 19 µs each
  on 8 threads, 11 µs on 4, 7.6 µs on 2.
- `zero_fill 20` .. `23`: 8.7M, 17.1M, 33.9M, 67.4M instructions, 8.0 a
  word (about 3 cycles), 2026-10-27.
- `interleave 2000000000 1000 0`: no message arrives during the work.
  `interleave 2000000000 1000 1`: all of them arrive, about 30.
