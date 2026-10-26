# Architecture Sketch — 2026-10-26

How the assembler's larger structure could sit on Bend 2: concurrency and
the shell, values and large structures, the store, parallelism, the front
end. **Drafted for the maintainer's review before building.** It proposes;
records decide. Accepted parts become records and a standing
`docs/Architecture.md`; open parts become spikes. Measurements come from
scratch experiments on 2026-10-26 (Bend 2.0.39, native, 8 cores) and from
Bend's runtime paper (`paper/BendRT.pdf` in bendlang/bend).

## Layers

```
 ┌───────────── IO shell: Bend IO, one event loop ──────────────┐
 │ CLI · files · git via Process.run · outputs · TCP for an IDE │
 │ runs the core in fuel slices; logs every input it delivers   │
 └──────────────┬──────────────────────────────▲────────────────┘
   inputs, in   │                              │  requests: read, fetch,
   logged order │                              │  reply, write, done
 ┌──────────────▼──────────────────────────────┴────────────────┐
 │ core: step(fuel, Core) -> Done | Need(request) | More        │
 │   scheduler  tasks: assembly, reflection, conf.log, conf.ide │
 │   front end  bytes -> tokens -> syntax -> core terms, nets   │
 │   evaluator  live nets and memo cells over the store         │
 │   values     Val: numbers, ropes, dicts, functions, handles  │
 │   store      pages: lazies, nets, structure holding handles  │
 └──────────────────────────────────────────────────────────────┘
```

## Concurrency and the shell

What Bend gives:

- Pure code runs on every core through parallel calls. Effects run on one
  event-loop thread, between pure evaluations; the pure machine performs no
  IO.
- `IO.spawn` and `IO.fork` start computations that interleave at effects,
  linked by channels. `Chan.try_recv`, `TCP.try_accept` and the other
  `try_` operations poll with a timeout.
- A computation in pure code holds the loop until its next effect.
  Measured, with about 300 ms of pure work beside a computation sending
  every 10 ms: one slice let no message through, 10 slices 9, 1000 slices
  30. Each yield costs about 5 µs. `IO.sleep(0)` yields; a zero-wait
  `Chan.try_recv` alone does not.

Proposed:

- **The shell loop:** run the core for one slice (fuel sized to 1–3 ms),
  `IO.sleep(0)`, drain the inbound channel, deliver its inputs to the core
  in order while appending each to the event log, then perform the core's
  requests.
- **Blocking work runs aside.** File reads, `Process.run` for git and
  socket traffic go to spawned computations, which report back on the
  inbound channel, so the core runs meanwhile. Their results reach the core
  only through the log, in delivery order: the one nondeterminism, and
  replaying the log reproduces a run.
- **An IDE web service** is a spawned computation: it accepts connections,
  parses requests, and posts each inbound with an id. The core answers
  `Need{Reply{id, body}}`; the shell keeps the map from ids to sockets, so
  the core never holds a handle.
- **Limits.** One event loop serves all IO, and the core is one logical
  thread (`pure-core-io-shell`): ample for the bootstrap and an IDE. If IO
  dispatch ever bottlenecks, foreign C effects can do their work on helper
  threads, as native `Process.run` already does, and a Linux target can
  batch IO through `io_uring` behind such effects.

## Values and large structures

What Bend gives: a `Data` value is shared in O(1), by a counted redirect;
the last owner frees it, and there is no tracing collector. Matching a
shared node copies its fields out. Closures and arrays are affine (`Type`),
so they cannot sit inside shared data. Overflows are fail-stops: a
reference count at 2^24, a `Nat` at 2^48, an array past depth 31.

So glam values are one Bend `Data` type, and nothing in it is a Bend
closure or array:

```
type Val is Data:
  Unit{}                 # ()
  Num{q: Rat}            # exact rational, small integers packed
  Seq{r: Rope}           # lists, texts, binaries
  Map{d: Dict}           # dicts, atoms, tagged data, objects, namespaces
  Fun{net: U32, +arity: U32}   # a function's net in the store
  Lazy{cell: U32}        # a lazy value in the store
  ...                    # opaque handles: volumes, resolvers, carriers
```

A function is a net and its remaining arity (`functions-are-nets-with-arity`):
applying it copies the net logically, and a pair reducing in the source
reduces once there, for every copy, so partial applications share their
work. Its net is therefore shared and mutable, like a lazy value, and lives
in the store beside them. glam-in-bend interprets glam's nets itself: Bend 2
has no net runtime, and glam's rules differ from HVM's.

**Numbers.** Rationals over integers of `U32` limbs, normalized, with
small integers packed into one word. Laws: limb arithmetic agrees with
`Nat` where `Nat` reaches, and the ring laws hold.

**Ropes** (lists, texts, binaries): 2-3 finger trees over uniform nodes,
as glas encodes them (GlasObject.md, "Encoding Finger Tree Ropes"): leaf
chunks, sized nodes and concatenations, with each level's depth a
convention rather than a type. That is an ordinary regular Bend datatype,
needing neither nested types nor type classes, though Bend accepts both
(checked: a typed finger tree passes with a depth-fuel argument first).
Cached sizes measure each level. Bulk operations (map, fold, serialize)
recurse over the tree as balanced fork-join; a parallel fold over a
persistent tree ran 5.7× faster on 8 threads than on 1. Leaves are chunks,
never arrays: binaries pack four bytes per `U32` into fixed-width leaves, so
a megabyte is about 16K leaves, and texts pack code points alike
(`packed-texts-and-binaries`).

**Dicts**, hierarchical:

- A join-based balanced tree keyed in a canonical total order over
  comparable keys; reflection may list keys in that order
  (`reflection-key-order-free`). Join-based algorithms make union,
  intersection and map balanced fork-join.
- A path is nested dicts; `{a.b:1, a.c:2}` builds `a`'s dict once. A
  `with` update copies one path, O(log n), and the old version stays valid.
- Every node caches `ground`: true when no `Lazy` or `Fun` handle lies
  beneath it, which lets reclamation skip it.
- Objects and namespaces are dicts of mostly lazy entries; object-based
  modules need no structure of their own.
- Measured on a persistent bitwise trie of 1M hashed keys: insert 420 ns,
  lookup 215 ns, insert into a shared version 550 ns, folding shared data
  175 ns per node. Comparing canonical keys will cost more per step;
  `arch-structures-spike` measures it.

**Hot values.** A node shared more than 2^24 times fail-stops. Values
packed into one word (unit, small numbers) are never counted, so the
commonest are safe; values referenced from millions of places, as `env`
might be, are interned and passed as handles (`intern-hot-values`).

## The store: shared lazy state

**This is the crux, and could sink the project if mishandled.** Lazy values
and function nets are shared by many references, change once for all of
them (a thunk is forced, a source pair reduces), and must be reclaimed once
unreachable. What Bend offers, investigated 2026-10-26:

- **Natively, nothing.** Bend 2 evaluates eagerly and has no thunks or
  memoization. A closure may be called once, so it is at best a single-use
  thunk. Shared data never changes: the runtime's lock-free reads, on CPU
  and GPU, rely on "a shared node's fields never change" and on a
  redirect's target never changing. Its only collector is the last owner's
  drop; with immutable data no cycle can form, so nothing traces.
- **Through IO,** channels are native, reference-counted, shared mutable
  objects, so a write-once cell could be emulated, but only from the event
  loop, at microseconds per operation.
- **Under `@unsafe`,** `Array.fork` hands parallel calls two handles to one
  array, and `Array.atomic.*` (CAS, exchange, add, …) act on `Array<U32>`
  cells. Tested: 8 workers racing CAS over 1M cells won exactly 1M claims,
  at about 6–10 ns per CAS. Every def depending on it falls outside the
  proofs, and only word cells are atomic.
- **No small tweak.** A native write-once cell breaks the runtime invariant
  above: it needs a new term kind with CAS and acquire reads on the C,
  Metal, CUDA and JS backends, plus checker support. And reference counting
  alone would leak the cycles lazy fixpoints make, since an object's
  entries capture `self`. Upstream has no issue on laziness, mutable
  references or cycle collection.

The careless design, one global array of lazies marked from Bend data,
fails twice: one array serializes evaluation, and marking cannot mark Bend
data, so a shared structure holding handles is walked once per path to it,
for every version sharing it. Three options:

1. **Split heap, in pure Bend.** Ground data (no lazy or function handle
   beneath it) is plain Bend `Data`, shared, freed and processed in
   parallel by Bend for free. Everything non-ground has identity in our
   store: lazies, function nets, and the interior nodes of structures that
   hold handles, beyond a small inline bound. Marking then visits each
   non-ground node once, however many versions share it, and a collection
   *grounds* structures whose lazies have all been forced, moving them out
   of the traced heap. Generational: a nursery collected often, an old
   region (namespaces) rarely, with a remembered set for old cells written
   once with young values. Parallel work splits the store into pages that
   workers own in turn ("Pages and rounds", below). Laws remain available
   throughout.
2. **Parallel word heap, HVM2-style.** All lazy structure as net nodes in
   a forked `Array<U32>`, reduced in parallel with atomics; linear, so
   nothing to mark. Real parallel evaluation, at the price of an `@unsafe`
   kernel no law can cover, everything encoded in words, and glam's nets
   differing from HVM's. Bend 2's own runtime is not a net machine (Bend 1
   ran on HVM2).
3. **Change Bend.** A write-once shared cell plus cycle collection in
   BendRT: the cleanest semantics, but a fork of a young compiler that
   ships several releases a week. At most a feature request, once a spike
   shows what we would ask for.

Chosen (maintainer, 2026-10-26): option 1, with independent work split
across the store for parallelism (`split-heap`); EvalSpike measures it
before anything depends on it. It is the same remedy the Rust side is
heading for (each shared object marked once), without host concurrency.
Its risk is speed: our own collector, and parallelism only as good as the
partitioning.

Mechanics, whichever option:

- The store is pages, flat `Array`s of cells; a scattered read and write
  measured about 1.5 ns. Handles never move.
- Live nets are linear: an interaction frees what it consumes and erasers
  free dropped subnets.
- When a collection leaves no free cell, the store grows by adding pages;
  no page moves, so handles stay valid.
- Laws: allocation stays in bounds (`pure_hvm5_mini` wraps silently); a
  sweep frees no marked cell; growth preserves contents; a rewrite keeps
  every live port wired once; a merge of nurseries keeps every memo
  result.

## Pages and rounds

The maintainer's direction (`store-pages`, `rounds-of-coarse-work`): equal
pages of cells that never move, owned linearly, and a coordinator running
coarse work on workers in rounds. Feasibility, checked 2026-10-26:

**Pages and handles.**
- Pages are equal-size `Array`s of cells. A page has exactly one owner at a
  time, a worker during a round or the coordinator between rounds. An
  `Array` cannot be copied, so Bend's checker enforces exclusive ownership,
  with no locks, atomics or `@unsafe` (checked: a tree of pages handed to
  parallel calls passes cleanly).
- A handle is a `U32`: a page number in its high bits, the slot in the low
  bits (`store-pages`). Measured on lists of 4M elements:
  - A constructor with one `U32` field packs into the term word, in a
    single-constructor type or a tagged variant like `Val` alike: `Lazy{h}`
    costs no allocation, is copied by value and is never counted (16.5 bytes
    per list element, the cons cell alone).
  - A `Nat` is packed only bare. Any constructor holding one, tagged or not,
    and whatever its value, is a heap node counted when shared (24.5 bytes
    per list element: one more word). A `Nat` past 2^48 − 1 is a fail-stop.
  - Splitting costs the same either way: 0.73 ns with `Nat` div and mod,
    0.59 ns with `U32` shift and mask.

  So 2^32 cells, split between page bits and slot bits by the page size,
  behind a small handle module that could widen if an assembly ever needs
  more.

**Rounds.**
- The coordinator is pure core code: it keeps every task's state and
  needs, assigns tasks and pages to workers heuristically, and runs several
  rounds within one core slice. It is not Bend's IO shell, whose
  computations interleave on one event-loop thread and never run in
  parallel; only parallel calls do.
- A round runs W workers as balanced parallel calls. Each worker runs its
  tasks on the pages it holds, under heuristic fuel, until the fuel runs
  out or its tasks all stop.
- A task stops with its needs: pages it does not hold (perhaps several),
  thunks it cannot proceed past, IO. Its worker records them for the
  coordinator and goes on with its other tasks; the coordinator plans from
  the records.
  - A task waiting on pages becomes runnable once one worker can hold all
    of them; while they are split between busy workers it sits out.
  - A task waiting on a thunk is attached as one of the thunk's waiters,
    returning to the run queue only once the thunk is ready. A thunk no
    task is computing becomes a task of its own.
  - A value already forced needs no page: the coordinator shares it out
    between rounds, in O(1) as Bend data.
  - A write into a page held elsewhere, such as a thunk's result, is queued
    for that page's next holder.
- The coordinator owes no task to any worker; assignments may change every
  round. Fairness comes across rounds: a task that sat out gains priority.
- Fuel starts as one unit per logical step, however large the step;
  weights wait for profiles across several machines. Pure workers cannot
  read a clock, so any later calibration would come from the shell's
  timing of whole slices, shaping scheduling, never results.
- Scheduling, heuristic but deterministic given the shell's input log,
  decides the order diagnostics are observed in; results never depend on
  it (`diagnostic-order-follows-schedule`).
- The coordinator is pure, so results never depend on thread timing, and
  laws can state that a round loses or duplicates no page and no task.
- Programs must expose concurrent tasks for rounds to pay off; with one
  runnable task, a slice runs it without forking.

**Measured** on this machine (i7-6700: 4 cores, 2 hyperthreads each),
equal total work of 2^27 scattered read-modify-writes:

| Configuration | Time | Speedup |
|---|---|---|
| 1 worker | 101 ms (16 KB pages), 159 ms (256 KB) | 1× |
| 8 workers, 16 KB pages | 38 ms | 2.7× |
| 8 workers, 256 KB pages | 70 ms | 2.3× |
| 8 workers, 4 MB pages (32 MB, past the 8 MB L3) | 581 ms | slower than 1 |

- With 64 KB pages, 4 threads ran as fast as 8 (55 ms each, against 73 ms
  on 2): hyperthreads added nothing to scattered memory work, while each
  barrier cost more.
- Moving pages between workers costs nothing measurable.
- A round costs the barriers of one fork tree, a grow turn and a work turn:
  about 7.6 µs on 2 threads, 11 µs on 4 and 19 µs on 8, almost all of it
  synchronization; creating the tasks costs about 0.1 µs. Spinning longer
  does not help: patching the runtime's wait (128 `sched_yield`s, then a
  condition variable) to 65,536 yields, or to 2^24 `pause` instructions,
  left round costs unchanged.
- Rounds want a few hundred microseconds of work per worker to keep that
  under 5%; a request waits up to a round.

**Upstream.** The runtime has no spin or pool option. The round cost,
`IO.eval` for the shell, and packed file reads are tracked with their
upstream issues in [`BendIssues.md`](../BendIssues.md), reproduced by the
programs in `bench/bend/`.

**What follows.**
- Coarse, independent work parallelizes: sparks, reflection tasks, module
  compilation, independent active pairs. Fine-grained sharing across
  workers does not.
- Pages stay cache-sized (16–256 KB) and working sets small; big pages
  turned parallel runs memory-bound.
- A task allocates in its own nursery pages.
- Ground data crosses workers as Bend data, but each share across lanes
  costs an atomic count, so widely shared values are interned
  (`intern-hot-values`).
- Scale needs measuring on a many-core machine: this one has 4 cores.

**Verdict: feasible**, safe and lawful. Gains are bounded by how much
coarse independent work an assembly offers, by cache-sized working sets,
and by 10–20 µs a round: on this 4-core machine, perhaps 2–3× where work
splits well.

## Collection

The store needs a collector of its own: stop-the-world first, then
concurrent under fuel with an SATB barrier (`store-collection`). Both ride
the rounds, so collection runs in
parallel by pages, deterministically, and never changes results.

**Common ground.**
- Roots: the coordinator's task states (stacks, registers, needs), thunk
  waiters, pending IO requests, the intern table, the assembly's roots.
- Mark bits per page, owned with the page. Ground data holds no handles, so
  marking never enters it, and every non-ground node is a cell, visited
  once however many versions share it.
- Marking across pages is bulk-synchronous like evaluation: each worker
  marks from the cells it holds, and a handle into a page held elsewhere
  becomes a mark message, routed by the coordinator to that page's next
  holder. Marking ends with a round that sends no message.
- Shortcutting: a handle to a cell holding a ground value is replaced by
  the value itself wherever the handle's page is held, so forced structure
  leaves the traced heap and its cells come free.
- Sweeping per page: unmarked cells join the page's free list, and an
  empty page returns to the pool, or to the OS in long sessions.
- Generations: nursery pages per task, old pages otherwise. A remembered
  set per page records old cells written (a thunk forced) with handles into
  young pages, so a minor collection marks young pages from the roots and
  the remembered sets alone. Cells never move, so promotion relabels whole
  pages.

**Stop-the-world.** Evaluation pauses; rounds run only marking, then
sweeping, then evaluation resumes. The simplest, and the first to build.

**Concurrent, under fuel.**
- Marking tasks run in the same rounds as evaluation tasks, their fuel
  paced to allocation so a cycle ends before the store fills.
- Snapshot at the beginning: cells allocated during a cycle are born
  marked, and a write that overwrites a handle (a thunk forced, a live net
  rewired) first logs the old handle, so all reachable at the cycle's start
  stays marked. Floating garbage waits a cycle.
- Write logs are per worker, handed over at each round's end and routed as
  marks to the pages' holders.
- No fine-grained race exists: within a round, one worker runs both the
  evaluation and the marking of the pages it holds, in turn.
- A cycle ends with a short pause to drain the logs and rescan task
  stacks; sweeping then runs lazily, page by page, as allocation reaches
  each page.

**Laws.** A sweep frees no marked cell. After marking, every handle in a
marked cell names a marked cell. Shortcutting preserves the value read
through every handle. A collection loses or duplicates no page. During a
concurrent cycle, every evaluation step keeps the snapshot invariant: no
marked cell holds a handle to an unmarked cell unless the old handle was
logged.

**Long sessions** (an IDE) run concurrent major cycles periodically, and
pages emptied by retired versions return to the OS.

## Parallelism

Fork-join fits balanced work with no shared affine state:

- Lexing and parsing a batch of modules once their bytes are in.
- Bulk structure operations on ground data: map, fold and union on ropes
  and dicts, serializing outputs, hashing for content addressing and
  caching.
- Evaluation tasks (sparks, reflection tasks, independent active pairs) on
  workers that own their pages, in rounds ("Pages and rounds").

Not parallel: work within one task, and anything needing a page another
worker holds until the next round.

## Front end

- The lexer reads a source's bytes packed four per `U32` in an `Array` its
  state owns (`packed-texts-and-binaries`), loading a word and taking its
  four bytes with constant shifts: a 64 MB scan took 20 ms so, against
  29 ms at one byte per cell and 54 ms unpacking each byte by index. Not
  Bend `String`s, which are character lists. Tokens carry offsets.
  Imported binaries go straight to packed rope leaves.
- Bend allows no mutual recursion and no call to a def below. hvm5_mini
  writes its parser as a continuation monad over the parser state, with one
  recursive term parser and explicit phases for lookahead; a loop over an
  explicit frame stack is the alternative. Layout and `@name` macros follow
  the same shape, and fuel bounds every loop.
- Lowering yields core terms and nets; laws that lowering preserves
  meaning are the stretch goal.

## Bend constraints to design around

- Every loop takes fuel; the core's step returns `More` when fuel runs out.
- One loop def per machine, with non-recursive helpers above it.
- No match on a computed value; destructure through a helper.
- No Bend closures in values: functions are defunctionalized templates.
- Bend `String`s for messages only.
- Fail-stop limits: check sizes before they bite.

## Risks

- A young compiler: bugs and performance cliffs (`host-bend2`).
- One C file per program and no incremental builds: native builds of a
  large core may slow; the JS target keeps the dev loop fast.
- Reference-count saturation for hot values.
- The store (above): our own collector must be fast, marking must never
  revisit shared structure, and parallel gains hang on partitioning work
  into pages at about 20 µs a round.
- `@unsafe` code, such as forked arrays, falls outside the proofs; keep it
  out of the core, or confine it to a small kernel.

## Steps

1. `arch-review` — the maintainer reviews this sketch; record what is
   accepted in `docs/decisions/`.
2. `arch-structures-spike` — a join-based rope and dict with chunked leaves
   and canonical keys: build, lookup, update a shared version, concatenate,
   split and fold in parallel, at 1M, 2M and 4M; laws for the size and
   order invariants.
3. `arch-shell-spike` — a shell running a stand-in core in slices beside a
   spawned TCP server, measuring request latency under load.
4. `arch-standing-doc` — move the accepted parts into a standing
   `docs/Architecture.md`, then retire this plan.

The store and nets belong to [EvalSpike](EvalSpike_2026-10-26.md).

## Open questions

None open. A many-core machine comes in once EvalSpike reaches
`spike-page-rounds` and has work to keep it busy; pay-as-you-go suits
best, a time-based rental only with enough work queued.

Answered 2026-10-26 by the maintainer:
- any key order is fine for reflection (`reflection-key-order-free`);
- texts and binaries are packed, bytes four to a `U32`
  (`packed-texts-and-binaries`);
- hot values are interned (`intern-hot-values`);
- the store is a split heap, split for parallelism (`split-heap`), in
  equal pages of cells that never move, handles a `U32` page and slot
  (`store-pages`);
- a coordinator runs coarse work in rounds, fuel one unit per logical step
  for now, waiting on pages and on thunks differently
  (`rounds-of-coarse-work`);
- scheduling decides the order diagnostics are observed in
  (`diagnostic-order-follows-schedule`);
- the store gets a stop-the-world collector, then a concurrent one with an
  SATB barrier, both shortcutting (`store-collection`).
