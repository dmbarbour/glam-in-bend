# Bend Issues

Where Bend 2 falls short of what glam-in-bend needs: our need, the upstream
issue if one exists, our evidence, the workaround, and when to revisit. None
is a stopper. Commenting upstream waits for whole-system performance
tuning, by the maintainer or at their request (`host-bend2`). States are as
of 2026-10-26, Bend 2.0.39.

## Nice to have

### Pure evaluation off the IO loop thread

- **Need:** the IO shell runs core slices on Bend's one event-loop thread,
  so no file, timer or socket is served while a slice runs
  (`pure-core-io-shell`).
- **Upstream:** [#1575](https://github.com/bendlang/bend/issues/1575), open:
  an `IO.eval` running a pure computation, worker pool and all, on its own
  thread. Its implementation, PR #1578, was closed unmerged.
- **Evidence:** `bench/bend/interleave.bend`. Beside about 300 ms of pure
  work, a computation sending every 10 ms got nothing through one slice;
  through 1000 slices with `IO.sleep(0)` between them, all 30 arrived. A
  zero-wait `Chan.try_recv` alone does not yield.
- **Workaround:** fuel slices of 1–3 ms, yielding with `IO.sleep(0)`, about
  5 µs a yield.
- **Revisit:** when an IDE serves requests, or at whole-system tuning.

### File reads packed four bytes to a word

- **Need:** bytes stored four to a `U32` (`packed-texts-and-binaries`).
  Base's file reads answer one list cell per byte.
- **Upstream:** [#1573](https://github.com/bendlang/bend/issues/1573), open:
  reads into an `Array<U32>`, four little-endian bytes per word, exactly our
  layout. The issue measures 1.5 s in Bend against 57 ms in C to read and
  sum 384 MB.
- **Workaround:** pack after reading, which costs little at source sizes.
  For large binary imports, a foreign effect could fill an array through
  the runtime's internals, at the price of breaking across releases.
- **Revisit:** when large binary imports matter, or at whole-system tuning.

### Compile-time specialization

- **Need:** the spike's rewrites must stay answerable to the rule table its
  laws are proved over. Specializing the table's interpreter on each
  constant rule would make the interpreter itself the fast path, with
  parity by construction.
- **Upstream:** none known; a suggestion to raise later.
- **Evidence:** dispatching the interpreter on the kind pair, each rule a
  constant, ran no faster than interpreting the table (`spike-node-layout`
  in `docs/plans/EvalSpike_2026-10-26.md`; variant B of
  `spike/tools/rewrites/`); rewrites written by hand ran 1.6 times faster.
- **Workaround:** a generator, itself a Bend program reading the table,
  writes the rewrites out; the gate regenerates them and fails on any
  difference, and the test corpora run through both the table and the
  generated code (planned in `spike-node-layout`).
- **Revisit:** at whole-system tuning.

### Run-time code generation

- **Need:** glam compiles its inputs, so nearly all nets reach the
  evaluator at run time; Bend's compile-time specialization never sees
  them. Generating native code for hot nets or rule sets while running
  would be a large win.
- **Upstream:** none known; a suggestion to raise later, at
  whole-system tuning.
- **Evidence:** dispatching the spike's rule table on constant rules
  gains nothing, while rewrites written by hand run 1.6 times faster
  (`spike-node-layout` in `docs/plans/EvalSpike_2026-10-26.md`).
- **Workaround:** rewrites generated ahead of time from the rule table;
  for hot, stable kernels, compilation out of process run through the
  shell (`spike-hvm5-jit`).
- **Revisit:** at whole-system tuning.

### Inlining left to the C compiler

- **Need:** the kernel's small steps (`link`, `node`, the reads) inlined
  into its rewrites, whatever else changes.
- **Upstream:** none known; a suggestion to raise later, with a build
  option or an inlining hint.
- **Evidence:** removing a word from the kernel's state made the native
  build up to 17% slower when clang stopped inlining `link` or `node`,
  while the same code with every compiled function forced inline got 4%
  faster; across the steps of `spike-node-layout` in
  `docs/plans/EvalSpike_2026-10-26.md`, the default build moved by up
  to 15% for reasons of inlining alone.
- **Workaround:** `spike/tools/inline_build.sh` builds the emitted C with
  every compiled Bend function forced inline, to measure the work
  itself; the kernel still ships as `bend` builds it.
- **Revisit:** at whole-system tuning.

### Array creation fills word by word

- **Need:** the node store doubles as a net grows; each doubling makes a
  new array.
- **Upstream:** none known; a suggestion (`calloc`, or `memset` for a
  constant fill).
- **Evidence:** `bench/bend/zero_fill.bend`: 8 instructions (3 cycles) a
  word; growing the kernel's stores is 14 to 18% of a run at k 18,
  most of it this fill (EvalSpike, `spike-node-layout`).
- **Workaround:** none yet; larger first sizes would trade memory for it.
- **Revisit:** at whole-system tuning.

## Watch

### A barrier pair per parallel round

- **Need:** the coordinator runs parallel rounds (`rounds-of-coarse-work`).
- **Upstream:** no open issue. #1092, merged before 2.0.39, already removed a
  condition-variable wake per pool turn.
- **Evidence:** `bench/bend/rounds.bend`. Each fork tree pays a grow turn
  and a work turn: about 7.6 µs a round on 2 threads, 11 µs on 4, 19 µs on
  8 (i7-6700). Patching the emitted C to spin far longer before sleeping
  changed nothing, so the cost is the barriers, not waking.
- **Workaround:** coarse rounds, a few hundred microseconds of work per
  worker or more.
- **Revisit:** measure on a many-core machine before proposing anything.

### Large native builds

- **Need:** a large core built natively.
- **Upstream:** [#1388](https://github.com/bendlang/bend/issues/1388), open:
  one C translation unit, segments as wide as the widest record, names that
  shift with every edit. [#1262](https://github.com/bendlang/bend/issues/1262),
  open: C emission's memory on macOS.
- **Workaround:** the JS target for the dev loop.
- **Revisit:** when native builds of the core slow the cycle.

### The IO loop's waiter scan

- **Need:** an IDE serving many connections.
- **Upstream:** [#1250](https://github.com/bendlang/bend/issues/1250), open:
  each pass of the IO loop walks every waiter, so n arrivals cost O(n²).
- **Revisit:** with the IDE.

## Designed around

Bend's choices, not defects; listed so nobody waits for them.

- **No laziness or shared mutable state.** Shared nodes never change, by a
  runtime invariant that lock-free reads rely on. Answered by our own
  store (`split-heap`, `store-pages`).
- **Silent wraparound of array indexes.** Guarded by laws on allocation.
- **No qualified import of Base.** `import Base as B` is refused (only
  `.bend` files take an alias), and a file's own constructors share its
  namespace with Base's, so `Unit{}` or `Pair` clash; constructors are
  prefixed (`VUnit`, `Redex`), as upstream's own fix #1565 does. Sugar
  resolves Base names in the file's namespace (#1331, #1577), which is
  likely why.
- **Arrays of linear values.** An array of pages is an `Array` of
  `Array<U32>`, and `Array.new` and array literals take only `Data`
  elements, so such an array is built from `ALeaf` and `ANode` directly;
  an element comes out only by `Array.swap`, a placeholder holding its
  slot until it goes back (`spike/kmem_paged.bend`).
- **Records flatten into every call.** A product type's fields travel one
  by one through each function that takes it, so a wide state record
  costs every step (about 30 instructions an interaction a word in the
  kernel). A type with a recursive variant cannot be flattened and
  travels as one word, opened at the cost of an allocation: the kernel's
  cold record (`spike/kprim.bend`).
- **Fail-stop limits:** a reference count at 2^24 (`intern-hot-values`), a
  `Nat` at 2^48, an array past depth 31. A constructor holding a `Nat` is
  a heap node, so handles are `U32` (`store-pages`).
