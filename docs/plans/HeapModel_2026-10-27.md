# Heap model: nets, thunks and functions as cells

Drafted for the maintainer's review before anything is built: a
preliminary model of where glam's shared lazy state lives, planned with
deep analysis rather than a design already written, compared with the Rust
bootstrap, with a sketch of what the spike needs now and what comes later.
It builds on `split-heap`, `store-pages`, `store-collection`,
`rounds-of-coarse-work`, `net-nodes-double`, `functions-are-nets-with-arity`,
`net-demand-whnf` and `copy-reduced-function-nets`, and on EvalSpike's
kernel (`spike-node-layout` in
[`EvalSpike_2026-10-26.md`](EvalSpike_2026-10-26.md)).

## What must hold

- Nets are first-class glam values: bound directly unless wrapped as
  functions (`net_arity N`) or thunks (`net_arity 0`), and shared. A raw net
  is opaque, already in weak head normal form, and composes only through
  interaction-net calls (DistilledDesign).
- Evaluation is call by need: a thunk forced twice computes once, and
  copies of a function share the reductions of its source
  (`functions-are-nets-with-arity`).
- Bend's values are immutable and shared by reference counts; arrays are
  affine, one owner each, never shared. Every shared mutable thing is ours:
  a cell in the store, named by a `U32` handle (`store-pages`).
- One worker reduces a net at a time (`net-nodes-double`); workers own their
  pages for a round (`rounds-of-coarse-work`).

## The preliminary model

**Values.** `Val` is Bend data: ground values, and handles naming cells. A
handle never owns its cell; the collector reclaims cells unreachable from
the roots (`store-collection`).

**Two forms of a net.** A *live* net is the kernel's state (`H`: node
array, free list, pair stack, data table): affine, one owner, being
reduced. A *frozen* net is an immutable template, Bend `Data` (its node
words packed in chunks, its table's values, its exposed port): shareable,
read by any number of workers at once, never reduced in place. Arrays
cannot be shared, so whatever many holders read must be frozen, and
whatever is reduced must be live. The Rust bootstrap instead keeps one
mutable net behind a lock and reduces a shared net in place; Bend rules
that out, and with it the lock bugs below.

**Cells**, provisionally:

    Cell = Free{next}
         | Net{tpl: Frozen, arity}          -- a net value, frozen, shared
         | Thunk{state}                     -- a lazy value
    state = Fresh{recipe}                   -- not started: an owned live
                                            --   net, a net to copy, or an
                                            --   application (function, arg)
          | Suspended{net: H, need}         -- its progress, in the cell
          | Busy{task}                      -- being forced this round
          | Forward{to: handle}             -- its value is another thunk's
          | Forced{v: Val}                  -- memoized, written once
          | Failed{e}                       -- a permanent failure, cached

- A *net value* (a raw net) is a handle to a `Net` cell; binding or sharing
  it copies the handle, and nothing reduces the frozen template.
- A *function* is `Fun{h, arity}` over a net cell. A function meeting an
  application, at the value level or inside a net, makes a *lazy
  application*: a thunk whose recipe is the function and the argument.
  Forcing it instantiates the function's frozen net into the thunk's own
  live net and binds the argument (`copy-reduced-function-nets`); with
  arguments still to come, its value is a function of one less arity.
  The Rust bootstrap does the same, and forbids opening a function's net
  where it meets an application, to keep partial application a value.
- A *raw net* meeting an application inside a net (an interaction-net
  call) is opened there: a copy of its frozen net is spliced into the
  running net, its pairing levels offset to fit (NetPairing).
- A *thunk* memoizes. One the evaluator makes owns its live net outright
  (its recipe holds the net, whose handle never escaped); one over a user's
  net value (`net_arity 0`) instantiates a copy when forced, since others
  may hold the same net. Bend cannot count handles, so uniqueness is known
  only by construction.
- *Progress lives in the cell*: a thunk stopped on a need keeps its live
  net there (`Suspended`), never in the task, so cycles through tasks
  cannot keep it alive (the Rust bootstrap learned this the hard way, and
  recorded it as its decision lazy-owns-partial-progress). A tail call becomes `Forward`, so tail
  recursion does not nest forces.
- *Faults are not failures*: a crash in the evaluator, or a kernel fault
  such as a free slot read as a value, is reported and never cached as a
  thunk's result; only a permanent failure of the program is (`Failed`).

**Local reduction** of a function's net, which every copy shares, happens
on a live net before it is frozen: build-only pairs only, never calls
(reducing a call there could unroll recursion without end), under fuel
(the Rust bootstrap's compiled nets allow 4 reductions a node, up to 256
nodes). What depends on the argument is done per copy; what does not, but
needs calls (`\x -> g 1000 + x`), would be redone per copy, so lowering
should hoist it into a thunk the function's net refers to, shared by every
copy through its handle.

**Forcing.** A worker takes a thunk's live net and reduces the path from
the root toward weak head normal form, erasing eagerly (`net-demand-whnf`);
the Rust bootstrap reduces only that path, erases only on it, and leaves
the rest as garbage. A pair on that path that needs another cell's value is
set aside and the thunk suspends with that need; pairs off the path that
need values do not block it, or the coordinator would report cycles that
are not there. Where the needed thunk can be forced in the same worker, it
is forced inline rather than sent round the coordinator: the Rust
bootstrap's largest evaluation cost was one coordinator round trip per lazy
value, about 60 per level of recursion. A value at the root ends the force:
data becomes `Forced{v}`; a function at the root, its arity coming from the
recipe, freezes the reduced remainder into a net cell (no copy, since the
thunk owned it) and the result is `Fun{h, arity}`.

**Values crossing.** Into a net: numbers inline in nodes, other values as
table entries (which may hold handles, never own cells). Out of a net: the
root's value, normalized (`V.norm`), placeholders held out by the laws of
`spike-node-layout`.

**Collection.** Roots: the coordinator's tasks and needs, thunk waiters,
the intern table, the assembly's roots. Marking a live net scans its data
table; marking a frozen net scans its template's values. Collect only
between rounds, since a net held by a worker is out of sight, and mark with
an explicit stack. Two lessons from the Rust bootstrap:
- Marking each cell once is not enough. Its lists and dicts were shared
  shells without mark bits, walked once per path to them: on one workload
  each cell was reached 120 to 150 times a collection, the cost grew as
  n^1.70, and collection took 45 to 47% of the time. A cached `ground` flag
  skips ground subtrees but not shared structure that holds handles, and
  goes stale as thunks are forced (the maintainer doubted it too). What
  marks shared structure once is identity: interior nodes holding handles,
  above a small inline bound, become cells themselves (`split-heap` says
  so), or are interned, with ground leaves skipped.
- A reused handle must not alias: a cell freed and reused while a stale
  handle survives somewhere (a fault, but one to catch) wants a generation
  check, at least in debug runs.

## Laws and runtime checks

Can laws replace runtime fault checks, such as the kernel's report of a
free table slot read as a value? In principle, yes. Base defines `Array` as
a pure tree of leaves and nodes that the compiler maps to native arrays, so
laws can see through array contents, by induction like any data, and the
rule-table generator could emit a proof for each rule beside its code.
What it takes is an inductive invariant over the whole kernel state (each
node of value form 0 holds a live entry, each live entry has one holder,
the free list holds exactly the free slots), proved preserved by every
primitive, every generated rewrite and fusion: a refinement proof of the
kernel against a pure model, far beyond the case splits proved so far.
Short of that, laws cover what is a pure function (the table's operations
on a well-formed free list; the rule table's payload discipline, each data
payload taken over, duplicated or dropped exactly once), leaving the
kernel's faithfulness to the generator, the differential tests and the
audit, with the runtime check as defence in depth (about 1% on `fma`).
The heap wants laws of the same kind: a forced thunk never changes; a busy
thunk has exactly one task; a waiter resumes only after its thunk's result
is written; a round loses or duplicates no task, page or cell.

## Comparison with the Rust bootstrap

Read at its commit 21912fc, in three parts (values and collection; nets
as values; evaluation and scheduling). Beyond what the model above already
takes from it:

- **Values.** Four classes: plain data; immutable shared shells that may
  hold handles (lists, dicts, partial builtins); single managed edges
  (lazy, promise, net, function, volume, resolver); external leases. A
  function is a net handle and an arity, as here. Dict keys never hold
  handles.
- **Nets.** A whole copy only when the source has nothing left to reduce
  and at most 64 nodes reachable from its interface; otherwise cursors,
  whose pending pairs reduce in the source, in place, once for every copy.
  Compiled nets (a reduced net as a list of operator steps) only on
  request. A `Bind` reaching the root is an error; only calls and the root
  force lazy values, operators never do.
- **Evaluation.** One producer per lazy value; waiters subscribe, then
  recheck; a result is published before its waiters wake; cycles are found
  by walking blocked producers' single dependencies, and all members fail
  together; cycles through a promise stay retryable waits. Divergence is
  never detected: a divergent spark holds a worker forever.
- **Concurrency.** Twelve recorded defects (a false deadlock report in
  about 1 run of 30, two sessions driving one lazy value, lost wake-ups, a
  CPU blowup between publishing a result and waking its waiters, lock
  re-entry, livelock, collector starvation). Their causes: many locks with
  no order, windows between checking and deciding, several places claiming
  the same work, destructors and callbacks holding authority. A pure
  coordinator running rounds removes these classes by construction; what
  it must answer instead is round latency times demand depth, which inline
  forcing addresses.
- **Missing here, needed later:** promise cells (a value filled once from
  outside) and exactly-once IO; abandonment of work after a cut, since busy
  tasks are roots and abandoned work would leak; weak references; bounds on
  steps whose cost grows with data.

## Steps

1. `heap-model-review` — the maintainer reviews this model; record what is
   decided in `docs/decisions/`.
2. `heap-demand` — demand in the kernel: reduce the root's path toward
   weak head normal form, erasing eagerly, other pairs left pending; a
   pair on the path needing another cell set aside with the need recorded.
   Workloads: terms whose arguments go unused, erasure-heavy ones.
3. `heap-freeze` — frozen nets: freeze a live net into a template,
   instantiate a template into a live net or splice one into a running
   net, at n, 2n and 4n nodes; local reduction of build-only pairs under
   fuel before freezing.
4. `heap-cells` — one page of cells: net and thunk cells; forcing with
   needs, suspension in the cell, resumption, inline forcing within a
   worker, forwarding; a function at the root becoming a net cell; laws on
   cell states.
5. `heap-apply` — lazy applications of function values, partial
   application, and interaction-net calls opening raw nets.
6. `heap-measure` — taking and returning nets, freezing and instantiating,
   memory per small net, forcing depth against round latency, at n, 2n and
   4n.

Later, in EvalSpike's steps: logical copies (`spike-cursors`) if whole
copies cost too much; the split heap's collector, with identity for shared
interior nodes (`spike-lazy-data`); rounds over pages (`spike-page-rounds`).

## Open questions

- Local reduction before freezing: which pairs exactly, what bound, and
  whether hoisting argument-independent calls into shared thunks belongs to
  lowering.
- How pairing levels are offset when a raw net is spliced into a running
  net, and whether copies need fresh identities (NetPairing).
- Whether a frozen net keeps the kernel's node words or a more compact
  form, and how a template is chunked for sharing across workers.
- Thunks over a user's net: whether some uses (a net bound once and forced
  once) can skip the copy safely.
- How far inline forcing goes before a need goes to the coordinator, and
  how divergence in one forced thunk is kept from holding a worker.
