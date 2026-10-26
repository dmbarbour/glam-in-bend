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
 │   store      flat Arrays: live net nodes, memo cells         │
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
   once with young values. Evaluation runs one thread per store
   (`pure-core-io-shell`); sparks run on private nurseries over a snapshot
   of their parent and merge back at the join. A thunk's value is fixed by
   its code, so merges are order-independent, though siblings may
   duplicate work. Laws remain available throughout.
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

Proposed: option 1, measured in EvalSpike before anything depends on it.
It is the same remedy the Rust side is heading for (each shared object
marked once), without host concurrency. Its risk is speed: a sequential
evaluator and our own collector, in a language whose array loops run near
C speed.

Mechanics, whichever option:

- The store is flat `Array`s owned by the core state; a scattered read and
  write measured about 1.5 ns. Handles never move.
- Live nets are linear: an interaction frees what it consumes and erasers
  free dropped subnets.
- When a collection leaves no free cell, the store grows by copying into
  an array twice the size (depth 31 at most).
- Laws: allocation stays in bounds (`pure_hvm5_mini` wraps silently); a
  sweep frees no marked cell; growth preserves contents; a rewrite keeps
  every live port wired once; a merge of nurseries keeps every memo
  result.

## Parallelism

Fork-join fits balanced work with no shared affine state:

- Lexing and parsing a batch of modules once their bytes are in.
- Bulk structure operations on ground data: map, fold and union on ropes
  and dicts, serializing outputs, hashing for content addressing and
  caching.
- Sparks, later: each evaluates on a private nursery over a snapshot of
  its parent's store, merged back at the join (option 1 of "The store").

Not parallel: the evaluator's main loop over one store, and marking over
one mark array.

## Front end

- The lexer reads a source's bytes from an `Array<U32>` its state owns, one
  byte per cell, as `File.read_bytes` yields them. That takes four times
  the memory of packing, little at source sizes; packing four per cell
  would cost a shift per read. Not Bend `String`s, which are character
  lists. Tokens carry offsets. Imported binaries go straight to packed rope
  leaves.
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
- The store (above): a sequential evaluator and our own collector must be
  fast enough, and marking must never revisit shared structure.
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

- The store: option 1 as proposed, pending EvalSpike's measurements?
- Is order-independent merging of spark nurseries, with possibly
  duplicated work, acceptable for sparks?
- How long-running sessions (an IDE) reclaim old regions: a periodic full
  collection, or regions retired per edit?

Answered 2026-10-26 by the maintainer: any key order is fine for reflection
(`reflection-key-order-free`); texts and binaries are packed
(`packed-texts-and-binaries`); hot values are interned
(`intern-hot-values`).
