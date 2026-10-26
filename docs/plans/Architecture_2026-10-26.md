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
  threads, as native `Process.run` already does.

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
  Fun{code: Tpl, env: Env}   # a closed net template and its captures
  Lazy{cell: U32}        # a memo cell in the store
  ...                    # opaque handles: volumes, resolvers, carriers
```

A function is data: a closed template, shared freely, copied into the live
net when applied (as `pure_hvm5_mini` instantiates definitions). Only
laziness needs the store.

**Numbers.** Rationals over integers of `U32` limbs, normalized, with
small integers packed into one word. Laws: limb arithmetic agrees with
`Nat` where `Nat` reaches, and the ring laws hold.

**Ropes** (lists, texts, binaries). Two candidates, both checked in Bend:

- A join-based weight-balanced tree with cached sizes: cons, snoc, index,
  split and concatenation in O(log n), worst case. Join-based algorithms
  give bulk operations (map, fold, filter, union) as balanced fork-join,
  Bend's model of parallelism. A parallel fold over a persistent tree ran
  5.7× faster on 8 threads than on 1.
- Finger trees: Bend accepts their nested type and polymorphic recursion,
  given a depth-fuel argument first, for amortized O(1) at both ends.
  Without type classes, measuring nested levels takes a uniform element
  type, or dependent element types like Base's `Word(n)`. Eager
  evaluation weakens amortized bounds under persistence.

Proposed: start with the join-based tree, which is simpler, bounded in the
worst case, parallel, and shares its code with dicts. Revisit finger trees
if profiles show end operations matter. Leaves are chunks, never arrays:
binaries pack four bytes per `U32` into fixed-width leaves, so a megabyte is
about 16K leaves; texts pack code points alike.

**Dicts**, hierarchical:

- A join-based balanced tree keyed in a canonical total order over
  comparable keys. glam exposes no key order; reflection, which lists keys,
  would list them in this order, deterministically.
- A path is nested dicts; `{a.b:1, a.c:2}` builds `a`'s dict once. A
  `with` update copies one path, O(log n), and the old version stays valid.
- Union, intersection and map run as join-based parallel algorithms.
- Every node caches `ground`: true when no `Lazy` handle lies beneath it,
  which lets reclamation skip it.
- Objects and namespaces are dicts of mostly lazy entries; object-based
  modules need no structure of their own.
- Measured on a persistent bitwise trie of 1M hashed keys: insert 420 ns,
  lookup 215 ns, insert into a shared version 550 ns, folding shared data
  175 ns per node. Comparing canonical keys will cost more per step;
  `arch-structures-spike` measures it.

**Hot values.** A node shared more than 2^24 times fail-stops. Values
packed into one word (unit, small numbers) are never counted, so the
commonest are safe; a value referenced from millions of places, as `env`
might be, could be interned in the store and passed as a handle.

## The store, laziness and reclamation

- The store is flat `Array`s owned by the core state: live net nodes and
  memo cells. A scattered read and write measured about 1.5 ns.
- Live nets are linear: an interaction frees what it consumes, and erasers
  free dropped subnets, so nets need no collector.
- Memo cells are shared through `Lazy` handles inside `Val`s, which Bend
  copies freely, so the store cannot count them. Reclaim them by
  mark-and-sweep: mark from the core's roots (scheduler, stacks, data in
  live net nodes, cells), skipping `ground` subtrees, then sweep unmarked
  cells to the free list. It never moves cells, so handles stay valid, and
  it is pure and deterministic. It runs between slices, before the store
  would grow.
- When a sweep leaves the free list empty, the store grows by copying into
  an array twice the size (depth 31 at most).
- Laws: allocation stays in bounds (`pure_hvm5_mini` wraps silently); a
  sweep frees no marked cell; growth preserves contents; a rewrite keeps
  every live port wired once. Marking completeness is harder to prove; try
  it on small stores first.
- `spike-lazy-data` (EvalSpike) weighs this against lazy fields as net
  ports.

## Parallelism

Fork-join fits balanced work with no shared affine state:

- Lexing and parsing a batch of modules once their bytes are in.
- Bulk structure operations: map, fold and union on ropes and dicts,
  serializing outputs, hashing for content addressing and caching.
- Later, sparks whose inputs are ground could evaluate on a private store
  and return ground results.

Not parallel: the evaluator's main loop over one store, and marking over
one mark array.

## Front end

- The lexer reads bytes in an `Array<U32>` its state owns, not Bend
  `String`s, which are character lists; tokens carry offsets.
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
- Marking cost on large live heaps with many lazy handles.

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

- Is a canonical internal key order acceptable, given that reflection
  lists keys in it?
- Should texts and binaries be ropes with specialized leaves, as proposed,
  or ordinary lists of numbers until measured?
- Is interning hot values worth doing before measuring?
