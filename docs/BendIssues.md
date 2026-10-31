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
  A plain constant does fold: a `Bool` from another file guarding a check
  costs nothing when false (`bench/bend/const_flag/`), the guard gone
  from the disassembled hot loop, even with the guarded function shared
  by two call sites: a generated file reporting a build's mode can switch
  audits off. The kernel's larger functions should be checked where a
  guard is used.
- **Workaround:** a generator, itself a Bend program reading the table,
  writes the rewrites out; the gate regenerates them and fails on any
  difference, and the test corpora run through both the table and the
  generated code (planned in `spike-node-layout`). Templates (`~`
  parameters, a copy compiled for each distinct argument) now specialize
  a chain on a constant step (the erasure modes, `heap-strategies.erasure.
  kernel`); whether they can specialize the interpreter on a constant
  rule is EvalSpike's `spike-templates`.
- **Revisit:** at whole-system tuning.

### Recursion through templates

- **Need:** code written once over a family of strategies
  (`spike-templates`) includes loops: the events' drain, a strategy's run.
  A template that recursed, or closed a recursion through its argument,
  would let a loop be written once too.
- **Upstream:** none known; a suggestion to raise later.
- **Evidence:** a template may call only templates declared above it, so
  never itself. Closing the knot through an argument fails too: a def
  `loop.u` calling a template `step(~loop.u, ...)` whose body calls that
  argument is rejected, the template's copy checked before `loop.u` is
  filled ("an unfilled law is a dead claim: live code cannot use it";
  Bend 2.0.39, 2026-10-31; `bench/bend/template_knot/knot.bend.txt`).
- **Workaround:** the loop's body a template, its few lines of recursion
  one per family, each calling the body with the family's arguments
  (`spike/knet.bend`'s `ev.drain` and `ev.drain.e`; `spike/kstrat.bend`'s
  run loops).
- **Revisit:** when a later Bend accepts either form.

### Reasoning about U32 in proofs

- **Need:** the kernel's invariants live in `U32` words (the free list,
  capacities, offsets, the stack's bound, the data table's links).
  Proved as laws, they would replace run-time audits and checks; the
  maintainer judges many could go (2026-10-29).
- **Upstream:** #1850 (open), laws relating `U32` to `Nat` so that proofs
  can move into `Nat` arithmetic and back: 41 proven in another project
  (order, subtraction without underflow, conversions, shifts, division),
  the issue asking whether they belong in Base or a hub package.
- **Evidence:** `U32` is defined over `Word` bits, so its operations do not
  reduce on symbolic values: a `case _` after `U32` literal cases leaves
  the value symbolic, and a function matching on it never reduces in a
  proof. The laws so far are over constructors (`spike/rules.bend`) or a
  model in `Nat` (`spike/ctl.bend` for control runs), never the kernel's
  own state; that state is audited at run time instead (the data table,
  the free list, `KN.free_ok`).
- **Workaround:** small counts encoded as constructors; `U32` tests routed
  through a `Bool` helper whose lemma is proved over the `Bool`; models in
  `Nat` with laws, the kernel tested against them; audits in tests. The
  hub's `bend-mathlib` 0.8.0.0 (`0x78e347bf8d0582a322c01b02c727566f`, its
  `u32.bend`) already proves `U32` comparison, addition, subtraction and
  increment against `Nat`, exact or wrapping; with it the spike proves
  the kernel's own `U32` raise equal to its `Nat` model (law
  `lift_raise`, 2026-10-29), Bend caching the package under
  `~/.bend/lib` by its hash. Neither covers `.&.`, `.|.` or shifts, so
  the kernel decodes a header's field and an offset's amount by division
  and remainder instead, at no cost in instructions (store runs 58 and
  59: each of 20 counts, 3 to 13 x 10^8, within 37 of the shifts' and
  masks'), and the file #1850 points to, vendored as
  `vendor/wilderness-labs-stt/u32.bend` (MIT), proves `U32` division
  against `Nat`.
  With both, the laws bound a decoded field to 24 bits and an amount to
  31 (`fld_bits`, `off_by_bits`), so the kernel's raise of a decoded
  level is the model's without hypothesis (`lift_decoded`) and fits its
  field whenever the kernel's check passes it (`lift_fits`). The encoders
  still shift and mask, without laws.
- **Revisit:** before the kernel leaves the spike.

### Big constants in proofs

- **Need:** bounds such as 2^24 and 2^32 in the kernel's laws.
- **Upstream:** [#957](https://github.com/bendlang/bend/issues/957),
  open: the checker keeps a `Nat` unary, so a closed term over a big
  literal recurses once per successor; a fix waits on a rule BendTT's
  kernel lacks (#1291, closed as its duplicate). PR
  [#1832](https://github.com/bendlang/bend/pull/1832), open, would make
  a copy of one closed call met past an unfold compare as itself.
- **Evidence:** the checker's stack overflows at `{Nat.pow(2n, 16n) ==
  65536n : Nat}`, though 2^14 checks; `Nat.pow(2n, Nat.add(24n, 8n))`
  against `Nat.pow(2n, 32n)` overflows, and so does a field bound whose
  forms differ only in a `U32` call under `MNat.lt(_, Nat.pow(2n, 24n))`.
- **Workaround:** the one #1291 suggests: each lemma reasons under a
  variable bound and is applied at the power where both forms match
  exactly; a `U32` literal's value comes from its bits, as a word with one
  bit set (`spike/PROOF.bend`, "Field bounds").
- **Revisit:** when #957 or #1832 lands.

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
  every compiled Bend function forced inline, and given training runs,
  profile-guided too (which alone recovers most of the loss), to measure
  the work itself; the kernel still ships as `bend` builds it.
- **Revisit:** at whole-system tuning. Then a build script making the
  profile-guided build, trained on a workload kept realistic as glam
  grows, once glam has regular testing and performance checks across
  machines and GPGPUs (the maintainer, 2026-10-30): profile-guided, the
  full reduction runs 16% under the default build on `succ` and demand
  13% (store run 66).

### Dispatch on numbers

- **Need:** the kernel's rewrites dispatched on the pair of kinds, past
  16 kinds (`heap-strategies.kinds` in `docs/plans/HeapModel_2026-10-27.md`).
- **Upstream:** none known; a suggestion to raise later, a `switch` for
  a match on a number whose arms are code.
- **Evidence:** Bend 2.0.39 compiles a match on a `U32` into a chain of
  tests of its bits, and a match on a type's constructors into a chain
  of equality tests that clang left a chain; only a match whose arms are
  constants becomes a lookup table. A match on two kinds costs, per
  dispatch, 39 instructions with hot pairs and 57 with uniform ones at 16
  kinds and 100 pairs, 90 and 153 at 64 kinds and 400 pairs; one match on
  a dense rule number with 100 arms, about 190; a table of closures is
  refused, closures being linear (store run 80, i7-6700).
- **Workaround:** keep each match small: Bend's lookup table from the
  pair to a rule number, then a balanced tree of comparisons (28 to 33
  instructions at either size, the hottest pairs tested first: 17), or
  the high nibbles of the pair first, then the low (31 to 50).
- **Revisit:** when the kernel's kinds pass 16, or Bend emits jump
  tables.

### Array creation fills word by word

- **Need:** the node store doubles as a net grows; each doubling makes a
  new array.
- **Upstream:** #1890. The maintainer's preference over a faster fill:
  no initialization at all, with a proof that each slot is written before
  it is read. Half of it merged as #1928 (b576d5f, 2026-10-29): the fill
  loop in the runtime's `blk_new` written so that clang vectorizes it,
  the larger part for us; it leaves the doubling of the net's data table
  alone (the maintainer, 2026-10-30). In no release yet: 2.0.39, the
  pinned one, predates it.
- **Evidence:** `bench/bend/zero_fill.bend`: 8 instructions (3 cycles) a
  word; growing the kernel's stores is 14 to 18% of a run at k 18,
  most of it this fill (EvalSpike, `spike-node-layout`). With #1928's
  change applied to the C 2.0.39 emits: 0.88 instructions and 1.3
  cycles a word, and the kernel at k 18, four builds, 4.0% to 10.5%
  fewer instructions in every workload, the full reduction and demand
  alike, the same interactions (store runs 66, 67). What growth costs
  then is mostly the copy into each doubled array, word by word in Bend
  (`kmem_grow.bend`): 20% of the full reduction on `succ`.
- **Workaround:** none yet; larger first sizes would trade memory for it.
  Take #1928 with the release that carries it.
  Under the proof the issue asks for, the kernel's scans that read
  never-used nodes (the root's search, the table audit) would stop at a
  high-water mark instead of the capacity.
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
