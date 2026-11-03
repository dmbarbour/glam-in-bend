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

## The model

The maintainer's direction (2026-10-27 and 28), with the Rust bootstrap's
lessons; records follow at `heap-model-review`.

**Final and partial data.** Every value is one of two kinds:
- *Final* data is wholly computed and holds no handle: plain Bend data,
  shared freely, and tagged as final so the collector never walks it.
- *Partial* data holds a handle, or is a computation in progress. It keeps
  referential identity: it lives in a cell and is referred to by handle,
  never copied by value.
- Final data moves into partial data (a completed cell's final value
  replacing a handle to it), never the reverse. So every partial structure
  is reached through cells, each marked once, and final data is skipped:
  no tree is walked twice. Partial structures that versions share (a
  persistent dict of lazy entries, updated with `with`) keep identity at
  their interior nodes, above a small inline bound (`split-heap`), so what
  two versions share is cells.
- The tag is not a cached `ground` flag that goes stale: final data is
  final by construction, and partial data turns final only when its cell
  is rewritten.

**Cells.** One flat type, with no thunk header nested inside:

    Cell = Free{next}
         | Recipe{…}                -- not started: a function applied to
                                    --   arguments, a net cell to wait on
         | Live{net: H}             -- a live net, reduced here in place
         | Suspended{net: H, need}  -- its progress, kept in the cell
         | Forward{to: handle}      -- its value is another cell's
         | Value{v: Val}            -- wholly computed, written once
         | Failed{e}                -- a permanent failure, cached

A cell only moves forward, from a recipe or a live net to a value, and a
handle stays valid through every rewrite. Progress lives in the cell,
never in a task, so cycles through tasks cannot keep it alive (the Rust
bootstrap learned this, recording it as its decision
lazy-owns-partial-progress); a tail call becomes `Forward`, so tail
recursion does not nest forces. Faults (a crash in the evaluator, a kernel
fault such as a free slot read as a value) are reported and never cached
as a value; only a program's permanent failure is (`Failed`).

**Nets.** A *live* net is the kernel's arrays (`H`) in a cell, reduced
there by whichever one worker holds the cell. Its interface node sits
first after the net's header (node 2, `heap-strategies.header`) and never
moves: a negative principal port with no rules, the user's access to the
net (the Rust bootstrap's `Interface`, the kernel's `Root`, whose rules are
tuned to keep its slot). A `net_arity 0` computation is done exactly when
the interface faces a data node, `Interface >< Data`, and its value is the
interface's peer, read in one step.

A *frozen* net is a value: compact, plain data, made once, when reducing
is done, never as snapshots along the way. Freezing may be costly
(ordering nodes for materialization, encoding each node compactly, the
data array beside it), which is why it is done once. One format first,
made for materialization; whether a second, made for interpretation, earns
its place is open. A frozen net with no handle in its data is final; one
holding handles is partial and lives in a cell.

**Functions.** A function is a value referring to a net, frozen or still
live in its cell, with its remaining arity. A function meeting an argument
makes a lazy application: a recipe that, when forced, instantiates the
function's frozen net into its own cell and binds the argument, so the
cell owns its live net with no indirection (`copy-reduced-function-nets`).
Applied to all its arguments at once, a function is copied once and bound
to all; where a partial application is known to be used linearly, its
live net is taken over rather than frozen and copied. Callers of a
function whose net is not yet frozen wait for the freeze, as any lazy value
serializes its observers; sparks, tasks reducing lazy values ahead of
demand, recover the parallelism. The Rust bootstrap likewise never opens a
function's net where it meets an application, keeping partial application
a value.

Local reduction before freezing reduces build-only pairs only, never calls
(reducing a call there could unroll recursion without end), under fuel (the
Rust bootstrap's compiled nets allow 4 reductions a node, up to 256 nodes).
What depends on the argument is done per copy; what does not but needs
calls (`\x -> g 1000 + x`) would be redone per copy, unless lowering
hoists it into a thunk the function's net refers to, shared by every copy.

**Raw nets.** A raw net meeting an application inside a net (an
interaction-net call) is logically copied into the caller: first as a
whole copy of its frozen form, its pairing levels offset to fit
(NetPairing); cursors later. A thunk over a user's net (`net_arity 0`)
waits on that net's cell and takes the data result: the net is reduced in
place, once for every thunk over it, and never copied (the Rust bootstrap
does the same).

**Forcing.** A worker takes a cell's live net and reduces the path from the
interface toward weak head normal form (`net-demand-whnf`), reducing
only the pairs on the way, as the Rust bootstrap does, which leaves the
rest as garbage; unneeded work is for analysis ahead of evaluation. A pair on the path that needs
another cell's value is set aside and the cell suspends with that need;
pairs off the path do not block it, or the coordinator would report cycles
that are not there. Where the needed cell can be forced in the same worker,
it is forced inline rather than sent round the coordinator: the Rust
bootstrap's largest evaluation cost was one coordinator round trip per lazy
value, about 60 per level of recursion. When the interface faces data, the
cell becomes `Value{v}`; when it faces a function, arguments still to
come, the net freezes and the cell's value is a function over it, its
arity from the recipe.

**Values crossing.** Into a net: numbers inline in nodes, other values as
table entries (which may hold handles, never own cells). Out of a net: the
interface's value, normalized (`V.norm`), placeholders held out by the laws
of `spike-node-layout`.

**Cached copies during work.** A worker may pair a handle to partial data
with a copy of the cell's current value, to read without going back to the
cell. That copy must never be captured: stored where a value goes, it
would duplicate partial data by value, breaking identity, or freeze a value
that is still changing. The invalid state should be unrepresentable rather
than merely avoided: a cached copy is its own type, which can be read from
but not stored, and what can be stored is only the handle, or final data
(the maintainer, 2026-10-28; a proof that no store captures it would do,
but a type costs less to keep true). In Bend the wrapper is free while it
is passed between functions, since a record is flattened into its callers'
arguments, and would only cost if stored, which the type forbids.

**Workers and collection.** A worker holds the cells it works on for a
round, and Bend's linear types make that hold exclusive: nothing can race.
The collector runs between rounds, when the coordinator holds everything.
It marks partial cells, each once (a mark bit per cell, an explicit
stack), never walks final data, and may move a completed cell's final
value into the partial data referring to it (a live net's table entries, a
partial structure's slots), so the completed cell goes once nothing refers
to it. A reused handle must not alias a freed cell: a generation check, at
least in debug runs. What getting this wrong cost the Rust bootstrap: its
shared shells, without identity, were walked once per path, each cell
reached 120 to 150 times a collection, the cost growing as n^1.70, and
collection taking 45 to 47% of the time.

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

Preconditions are supported (checked 2026-10-27): a law takes a proof of
its precondition as a binder (`for h: {ok(s) == True{} : Bool}`), and the
proof uses it by rewriting or refutes an impossible case through a motive
into `Empty`; a law may quantify over an array, which its statement may
mention twice. So a pure round's postconditions under preconditions on its
inputs are within reach, as `alloc_conserves` already is for a page. What
makes such proofs hard is arithmetic on `U32`, whose case splits leave
symbolic words that do not reduce: counts a law reasons about are best
kept as `Nat` or as list lengths, predicates as `Bool` functions over
data, and the coordinator's steps small and structural, with no tactics
to lean on.

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
2. `heap-demand` — demand in the kernel: the interface at node 0, kept
   there by the rules and the loader; reduce the interface's path toward
   weak head normal form, erasing eagerly, other pairs left pending; a
   pair on the path needing another cell set aside with the need recorded;
   done when node 0 faces data. Workloads: terms whose arguments go
   unused, erasure-heavy ones.
   Built 2026-10-28. The loader makes the interface first, node 0, and
   `P.fresh2` frees a rule's B before its A, so the first new node takes
   A's slot and the root's rule keeps node 0; the result is read there
   rather than found by a scan. `KS.demand` walks from node 0 along
   principal ports, keeping the path, so a rewrite at its end resumes
   from the node below and cost stays linear. (Eager erasure, below, was
   dropped in `heap-strategies.net`.) Erasers' pairs reduce from
   the pair stack as rewrites make them (each removes a node that is no
   eraser and makes at most two erasers); other pairs stay in the net,
   unrecorded, found by the walk where they lie on its path and garbage
   where not, so a computation only an eraser takes is never started
   (`K 0 Ω` is 0). A fresh net may be assumed to hold no eraser in an
   active pair, lowering erasing as it builds (the maintainer,
   2026-10-28); the walk does not need it, draining the loader's pairs
   like a rewrite's, though it would let the loader leave them off the
   stack. Fusion at the link a rule made to the node below the
   path's end can free that node; the walk then steps past it. Done when
   node 0 faces any principal port but a control's; a handle there is the
   value, a forward. An application or strict call meeting a table entry
   that is a handle stops the walk with the handle and the data node, and
   `K.resume` puts the value there and goes on. Stuck pairs come from the
   rule table (`KR.stuck_by`, generated); where the payload test decides,
   the rewrite is told from a stuck pair by B's slot after it (law
   `rules_tested_small`), so the test keeps one caller: a second had
   clang move it out of line, and the full reduction cost 6 to 18% more
   in all four builds until it went. `spike/test_demand.bend`: 22 cases,
   needs met and resumed, stuck pairs, fuel.
   Measured (i7-6700, Bend 2.0.39, instructions, forced-inline build,
   k 18 or n, 2n, 4n): where every pair is needed, demand costs about
   770 instructions more per interaction than the full reduction (`succ`
   659 to 1,431, `fma` 986 to 1,766, levels 593 to 1,341), 1.7 to 2.3
   times in every build, linear in n; the full reduction itself is 0.1 to
   2.3% cheaper than before, no scan for the root. `K 0 (k 2 succ 0)`:
   2 interactions at k 14, 15, 16 against 32,946, 65,727, 131,276, the
   power left as garbage (42 to 46 nodes). `K 0 #n`, a value erased: the
   full reduction's interactions, n 16,384 to 65,536, 7% more
   instructions, 2 nodes left. `#n succ`, a function: 1 interaction
   against n. Ways to cut the walk's cost: the path in an array rather
   than a list; the pair a rewrite makes at the path's end taken straight
   from the stack; a narrower state record.
   The 3,600 random terms (`terms.py --kernel`, now with a demand run
   each): without levels, demand gets 89 of 600 per ending wrong where
   the full reduction gets 94, static labels' known failures, with 21%
   fewer interactions on the 506 both get right. With levels, demand gets
   8 of 600 wrong and makes more interactions than the full reduction on
   107 to 110, where the full reduction gets 1 wrong (#33 of seed 11,
   out of fuel; demand gets it right). The cause is fusion, not demand:
   with `P.fuse` a no-op, demand gets all 600 right, never more
   interactions than the full reduction, 24% fewer on the 599 both get
   right. Fusion is not sound in every order. Draining every pair rather
   than erasers' alone gives the right values, so the walk's choices are
   sound; with only one kind of control fused, the full reduction too
   goes wrong (`((\f. add (f #3) (f (mul (pow #2 #3) (pow #1 #2))))
   (\n. mul n #2)) succ 0`, 22, runs out of fuel). The smallest term
   found: `self (add #2 #1) succ 0`, 27, read as none on demand. Likely
   cause: NetPairing's caveat, a fused control crossing a facing control
   that its first part would have cancelled. Fixed since in NetPairing's
   `pairing-fusion` (`fuse-control-runs`): with fusion limited to runs of
   raises and runs peeled where a partner meets them, demand gets all 600
   right and never makes more interactions than the full reduction.
3. `heap-strategies` — a net's state apart from how it is evaluated (the
   maintainer, 2026-10-28): the net holds its nodes, free list, data table
   and faults; an evaluation strategy wraps it with state of its own,
   decides which pair is next, and is done when it hands the net back, so
   that a cell holds a bare live net at rest. Several strategies, each
   measured: eager pairs last in first out, demand toward the interface,
   parallel rounds; profiling and tracing as strategies wrapping another.
   Waypoints (2026-10-30), in the order intended:
   `heap-strategies.fusions.norm` (built), `heap-strategies.fusions.assume` (built),
   `heap-strategies.fusions.loops` (built), `heap-strategies.fusions.payloads.data` (built),
   `heap-strategies.fusions.payloads.levels` (built),
   `heap-strategies.fusions.fits` (built),
   `heap-strategies.fusions.controls` (built),
   `heap-strategies.erasure.kernel.parity` (built)
   with `heap-strategies.erasure.kernel.sites` (built),
   `heap-strategies.erasure.kernel.sites.random` (built),
   `heap-strategies.erasure.merge` (built), then `spike-templates` (built) and
   `heap-strategies.kinds.dispatch` (built) on the merged kernel, so
   that the generator is rebuilt once (the maintainer, 2026-10-31),
   `heap-strategies.kinds.layout` (built), `heap-strategies.kinds.class` (built),
   `heap-strategies.measure.spot` (built) and `heap-strategies.measure.builds` (built),
   `heap-strategies.erasure.deadcall` (built) before the operators (the
   maintainer, 2026-10-31), `heap-strategies.kinds.payloads` (built),
   `heap-strategies.kinds.payloads.links` (built),
   `heap-strategies.erasure.deadcall.chain` (built),
   `heap-strategies.measure.differential` (built),
   `heap-strategies.measure.loader` (built),
   `spike-operators` (EvalSpike, built) with
   `heap-strategies.erasure.deadcall.eraser` (built),
   `heap-strategies.erasure.load` (built),
   `heap-strategies.erasure.load.cycle` (built),
   `heap-strategies.fusions.immediate`,
   `heap-strategies.fusions.upto`; later
   `heap-strategies.erasure.load.cycle.cost` (built),
   `heap-strategies.erasure.load.cycle.stress` (built),
   `heap-strategies.erasure.load.cycle.fuse` (dropped),
   `heap-strategies.erasure.load.cycle.stress.events`,
   `heap-strategies.erasure.load.cycle.oom`,
   `heap-strategies.erasure.load.cycle.loops`,
   `heap-strategies.erasure.load.cycle.library`,
   `heap-strategies.erasure.load.cycle.trace` (dropped),
   `heap-strategies.erasure.load.cycle.trace.lean` (built),
   `heap-strategies.erasure.load.cycle.room` (dropped),
   `heap-strategies.erasure.load.cycle.perf` (built),
   `heap-strategies.erasure.load.cycle.third`,
   `heap-strategies.erasure.load.cycle.dispatch` (dropped),
   `heap-strategies.erasure.load.cycle.leaves` (dropped),
   `heap-strategies.erasure.load.cycle.entry` (dropped),
   `heap-strategies.erasure.load.cycle.walk` (built),
   `heap-strategies.erasure.load.cycle.walk.lean` (built),
   `heap-strategies.erasure.load.cycle.walk.trim` (built),
   `heap-strategies.erasure.load.cycle.walk.inhead` (dropped),
   `heap-strategies.erasure.load.cycle.walk.nil`,
   `heap-strategies.erasure.load.cycle.buffers` (dropped),
   `heap-strategies.erasure.load.cycle.parts` (built),
   `heap-strategies.erasure.load.cycle.sweep-full` (built),
   `heap-strategies.erasure.load.cycle.chunks` (built),
   `heap-strategies.erasure.load.cycle.chunks.budget` (dropped),
   `heap-strategies.erasure.load.cycle.chunks.floor` (built),
   `heap-strategies.erasure.load.cycle.chunks.base` (dropped),
   `heap-strategies.erasure.load.cycle.chunks.finish` (dropped),
   `heap-strategies.erasure.load.cycle.eval-need` (built),
   `heap-strategies.erasure.load.cycle.bench` (built),
   `heap-strategies.erasure.load.cycle.shrink` (built),
   `heap-strategies.erasure.load.cycle.shrink.beta`,
   `heap-strategies.erasure.load.cycle.shrink.fuel`,
   `heap-strategies.erasure.load.cycle.shrink.untested`,
   `heap-strategies.erasure.load.cycle.shrink.ctl-cost`,
   `heap-strategies.erasure.load.cycle.shrink.copy` (dropped),
   `heap-strategies.erasure.load.cycle.bench.corpus`,
   `heap-strategies.erasure.load.cycle.walk.directed`,
   `heap-strategies.erasure.load.cycle.walk.directed.census` (built),
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds`,
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links`,
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.read` (built),
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.load` (built),
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.meet`,
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.dead-ports`,
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.propagate`,
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.walk`,
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.native`,
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.kinds`,
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.static.table`,
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.census` (built),
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.copy` (built),
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.copied` (built),
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.fn` (built),
   `heap-strategies.erasure.load.cycle.walk.directed.dataflow`,
   `heap-strategies.erasure.load.cycle.walk.directed.dataflow.check` (built),
   `heap-strategies.erasure.load.cycle.walk.directed.dataflow.report` (built),
   `heap-strategies.erasure.load.cycle.walk.directed.dataflow.report.cost` (built),
   `heap-strategies.erasure.load.cycle.walk.directed.dataflow.report.cost.bits`,
   `heap-strategies.erasure.load.cycle.walk.directed.dataflow.report.void` (built),
   `heap-strategies.erasure.load.cycle.walk.directed.dataflow.proof`,
   `heap-strategies.erasure.load.cycle.walk.directed.dataflow.stuck`,
   `heap-strategies.erasure.load.cycle.walk.directed.dataflow.walk` (built),
   `heap-strategies.erasure.load.cycle.walk.directed.dataflow.walk.loops` (built),
   `heap-strategies.erasure.load.cycle.walk.directed.dataflow.walk.loops.rest`,
   `heap-strategies.erasure.load.cycle.walk.directed.dataflow.walk.laws`,
   `heap-strategies.erasure.load.cycle.walk.directed.dataflow.dead-ap`,
   `heap-strategies.erasure.load.cycle.walk.directed.lowering` (built),
   `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.static`,
   `heap-strategies.erasure.load.cycle.walk.directed.eager`,
   `heap-strategies.erasure.load.cycle.reserve` (built),
   `heap-strategies.erasure.load.cycle.adaptive` (dropped),
   `heap-strategies.erasure.load.cycle.lazy-sweep` (dropped),
   `heap-strategies.erasure.load.cycle.loops.levels`,
   `heap-strategies.generate`,
   `heap-strategies.erasure.typed`,
   `heap-strategies.erasure.strategies`, `.aot`, `.trees`,
   `heap-strategies.fresh`, `heap-strategies.fusions.fits.load`,
   `heap-strategies.fusions.ktests`, `heap-strategies.fusions.distinct`,
   `heap-strategies.fusions.controls.peel`,
   `heap-strategies.fusions.controls.kpeel`,
   `heap-strategies.fusions.controls.cross`,
   `heap-strategies.erasure.kernel.sites.law`,
   `heap-strategies.erasure.kernel.sites.fuse`,
   `heap-strategies.measure.pgo`.
   Each step's state is in its line below.
   - `heap-strategies.net` — built 2026-10-28 — the net's operations in
     `spike/knet.bend`, strategies in `spike/kstrat.bend`, the program
     and the tests' entry points in `spike/kernel.bend`; demand without
     eager erasure, which the maintainer did not want, clearing the pairs
     the net still collects. Against f73b932, four builds at k 18 (store
     runs 30, 31): the full reduction unchanged (0.0%, -0.6% to -0.9%
     profile-guided), demand 13.7% to 17.5% cheaper, the same interactions.
     The full differential test (store run 32): the full reduction the
     same on all 3,600 terms; demand the same values, fewer interactions
     on 1,866 terms and more nodes left on 1,605, what eager erasure freed.
     - `heap-strategies.net.freelist` — built 2026-10-29 — the free
       list audited after every test's run (`KN.free_ok`), as the data
       table is (the maintainer, 2026-10-29): a node is free exactly
       when its header is 0, so the list from its head holds only nodes
       past the header and within the capacity, each with a zero header,
       ends within as many steps as there are nodes, and holds as many
       nodes as have a zero header. A failure flags the run as the table
       audit does (`TABLE MISMATCH`). `free` left the header set, or not
       linking the node, each fails 22 of the 25 demand tests, every one
       that frees a node.
       - `heap-strategies.net.freelist.law` — built 2026-10-29 — the
         same exactness as laws, over a model in `Nat`
         (`spike/freelist.bend`): slots as the kernel's nodes, a free one
         linking the next as a free node's word 1 does, and beside them
         the list the links should spell. `FL.ok` says the links from the
         head spell that list, which holds every free slot and no slot
         twice: what the audit tells by the chain ending within as many
         steps as there are nodes and holding as many as are free.
         `free_list_alloc` and `free_list_free` say each operation keeps
         it, and `free_list_takes_free` that alloc takes a free slot
         (the maintainer, 2026-10-29). A free that leaves the old head
         unlinked, or an alloc that leaves its slot free, fails the
         proofs. The kernel's own `U32` free list is not proved against
         the model; the audit still checks it after every test.
     - `heap-strategies.net.wiring` — built 2026-10-29 — the net's
       wiring as laws, over a model in `Nat` (`spike/wiring.bend`): node
       kinds, and links between ports. `W.wired` says the links' ends
       name each live port once and nothing else: every live node is
       referenced once at each of its ports, and no dead one is (the
       maintainer, 2026-10-29). `rewrite_wired`: replacing an active pair
       by a rule's new nodes and links keeps it, for any rule `R.exact`
       accepts (its links' ends repeat none and are the ends
       `rules_linear` expects); `rules_exact` proves every rule of the
       table exact, and `rules_keep_wired` puts the two together. A
       rewrite that leaves a node of the pair live, or drops the other
       links, fails the proof. Simplified from the kernel: new nodes are
       appended rather than taken from the free list; the net is focused
       on its pair, its links' ends grouped (the pair's ports, their
       peers, the other links'). A peer that is itself a port of the pair
       came later (`heap-strategies.net.wiring.pairs`).
       Reachability from the root is no invariant: erasure leaves unreached
       garbage, which `KN.sweep` collects.
       - `heap-strategies.net.wiring.audit` — built 2026-10-29 — the
         kernel audited for what `W.wired` says (the maintainer,
         2026-10-29): after every test's run, `KN.wired_ok` checks that
         every port of a live node links a port of a live node, past the
         header and within the capacity, below its kind's arity, that links
         it back and is not itself; so each live port is referenced once
         and no free node at all. It joins the table and free-list audits
         in `KRes`'s flag (`TABLE MISMATCH` names any of them). A `link`
         writing one direction fails all 25 demand tests; a rule making no
         nodes that frees only one of its pair fails 16, 4 of them caught
         by this audit alone, values right. The benchmarks now measure
         without audits: demand reports as the full reduction does, not
         through the tests' results with their audits and reachability
         walk, which its counts had included since
         `heap-strategies.net.freelist`. Against 6223582, four builds at
         k 18 (store runs 60, 61): demand 4.1% to 9.3% fewer instructions;
         the full reductions the same within 260 instructions as built,
         -3.8% to +0.8% profile-guided, whose training runs take the new
         demand path.
       - `heap-strategies.net.wiring.pairs` — built 2026-10-29 — a peer
         of the pair's auxiliary ports that is a port of the pair itself
         (a's auxiliary port linked to b's, or to a's other), as the
         maintainer asked (2026-10-29). A pattern (`R.Pat`, ten of them:
         none, one such link, or two) says which `Ext` ends face inside;
         the focused net lists only the outside peers (`W.fends_in`); and
         `R.contract` mirrors `knet.bend`'s `link_plain` and `link_pairs`:
         the rule's links facing outside, then for each inside pair, i
         below j, a link joining what the rule links to `Ext` i and `Ext`
         j, an error where either is inside (until
         `heap-strategies.net.wiring.circles`) or missing. `rules_pairs_exact`
         proves, by computation over every rule and every pattern the
         pair's arities allow, that the result links exactly the ends
         left, or is that error; `rewrite_pairs_wired` that a rewrite by it
         keeps a wired net wired; `rules_keep_wired_in` puts them
         together. The rewrite's proof is now one, `wired_gen`, over any
         outside peers, `rewrite_wired` an instance of it. A contraction
         dropping the joined pairs, or joining an end to itself, fails the
         proofs. The model keeps the kernel's links in its order, plain
         then pairs, though a net's links have none.
       - `heap-strategies.net.wiring.place` — built 2026-10-29 — new
         nodes wherever the kernel puts them: a placement lists each new
         node's slot (`W.place`, `W.sigp`), and `rewrite_placed_wired`
         says the rewrite keeps a wired net wired whenever the slots are
         distinct and each is the pair's own or free. The kernel's
         placement, the pair's two slots then the free list's, is one;
         appending, which `rewrite_wired` and `rewrite_pairs_wired` state,
         is another (`W.range`, slots past the end), so they are now proved
         through it, one proof (`wired_place`) where there were two. A slot
         condition that admits a live node fails the proof. Which slots
         the free list gives, and that they are free, is the next step.
       - `heap-strategies.net.wiring.alloc` — built 2026-10-29 — the
         free-list and wiring models joined (`spike/kplace.bend`), as the
         maintainer asked (2026-10-29): the kernel's placement, a
         rewrite's first two new nodes in the pair's own slots and the
         rest in the free list's heads, one node freeing b, none freeing
         b then a (`kprim.bend`'s renode, alloc, fresh2); `KP.in_step`
         says the free list's free slots are the kinds' free nodes. With
         an exact free list holding enough, kinds in step with it, and the
         pair's nodes distinct and live: `kernel_slots_ok`, the slots meet
         `rewrite_placed_wired`'s conditions; `kernel_free_ok`, the free
         list after is exact; `kernel_rewrite_wired`, the net stays wired;
         `kernel_in_step`, the two still agree, every new node's kind
         live. So the joint state carries from one rewrite to the next.
         Reusing a slot twice, or allocating one more slot than is
         placed, fails the proofs. Not modelled: growing the storage when
         the free list runs short (`has` is a hypothesis; since,
         `heap-strategies.net.wiring.grow`), and the kernel's U32 words
         themselves, which the audits check at run time
         (`spike-refinement`).
       - `heap-strategies.net.wiring.circles` — built 2026-10-29 — where
         an end the rule links to a pair's inside `Ext` end is itself
         inside, the rule's links and the pair's own close a loop of bare
         wire with no node on it, a vicious circle of length 0 in
         Lafont's terms (length counts the nodes on a circle), which no
         port outside the pair touches, so nothing is left to link; but
         the kernel (`knet.bend`, `net.bend`) reported an error. Polarity allows
         nine such cases among the table's rules and patterns, all of
         them rules linking two `Ext` ends (beta, fan and control
         annihilation), and with no rule linking two `Ext` ends and also
         making nodes, every chain through the pair closes. The kernel,
         the reference net and the model now drop the loop;
         `rules_pairs_total` proves, by computation, that the kernel's
         joining never errors under any pattern the arities allow, and
         `rules_pairs_exact` still holds. The library's
         `vicious-circle-beta` and `vicious-circle-controls` failed before,
         an error in every strategy, and pass now, the wiring audit with
         them. Nothing takes the loop's place, not an eraser: every port
         on it is one of the pair's, freed with the pair, and every
         outside peer is still linked exactly once (`rules_pairs_exact`),
         so none is left open. In `vicious-circle-beta`, a function whose
         body is the application's own result (`r` where
         `r = (\_ -> r) 7`, which nothing uses), beta links the body to
         the result, two ends that are the pair's own, and the argument
         to the eraser of the unused variable. Lafont keeps such a
         cyclic wire as a component of the net; a net stored as ports
         has nowhere to keep it, a loop with no ports and no nodes. A
         vicious circle with a node on it stays in the net, stuck, and
         demand reaching it reports a cycle: with `r` used, a copy shares
         it, and beta joins the copy's input to its own output
         (`vicious-circle-formed`). The loop with no node vanishes from
         the net, no error, and diagnostics show it once they are built
         (the maintainer, 2026-10-29). Is it a sign of garbage (the maintainer,
         2026-10-29)? The loop itself is: nothing touches it. The pair
         that forms it need not be: its ports not facing each other may
         lead to the root, as in `vicious-circle-live`, where the root is
         the function's variable, beta gives it the argument, and the
         loop vanishes beside it. Only a pair whose every auxiliary port
         faces another of its own (`vicious-circle-controls`) is a
         component apart. And demand reduces only the pairs it reaches
         from the root, so under demand a loop forms only in a pair the
         root reaches: `vicious-circle-beta`'s pair, apart from the root,
         is left as garbage, unreduced. Full reductions form loops in
         garbage too.
         - `heap-strategies.net.wiring.circles.events` — tentative —
           loops counted where they form, by pair and pattern, over the
           library and the corpus, by the profiling strategy; marked in
           traces (`heap-strategies.trace`) and drawn
           (`heap-strategies.trace.render`), to see how often they arise
           and where (the maintainer, 2026-10-29).
       - `heap-strategies.net.wiring.kinds` — built 2026-10-29 —
         `kernel_in_step` took as a hypothesis that a rule's new nodes
         are live; `rules_kinds_live` proves it of every rule, by
         computation (`KP.rule_live`), and `kernel_rules_in_step` states
         the step for the rule table without it (`KP.step_kinds`,
         `KP.step_free`, `KP.step_has`; a stuck pair changes nothing). A
         rule making a free node besides its others fails
         `rules_kinds_live` and no law before it: a free node has no
         ports, so the rules stay exact.
       - `heap-strategies.net.wiring.grow` — built 2026-10-29 — growth
         (`KP.grow`, `KP.grow_kinds`): n free slots appended, each
         linking the next, the last the old head, the first now the
         head, as `kprim.bend`'s `grow.done` and `thread` do with the old
         head none; the kinds grow by as many free nodes. It keeps the
         free list exact (`free_list_grow`), the two models in step
         (`grow_in_step`), every node's kind (`grow_kind_at`) and the
         wiring (`grow_wired`), and the list then holds the slots grown
         (`grow_has`), the placement's `KP.has`. A last new slot not
         linking the old head, or kinds grown live, fails the proofs.
         Growing by 1+m is growing by m above one more slot, in use, and
         freeing it, so `free_list_free` does the work. Not yet: growth
         in the kernel's order, inside `alloc` when the list runs out
         partway through a rewrite, which would retire the `KP.has`
         hypothesis; its laws are drafted at the end of
         `spike/LAWS.bend`. The maintainer finds the hypothesis, a free
         list never short, reasonable (2026-10-29); improving on it is
         welcome.
     - `heap-strategies.net.capacity` — tentative — a net that cannot
       grow stops its strategy at the first such error. Given fuel
       enough, the library's `demand-dead-factor` passes the 2^21 nodes
       in a full reduction, and the kernel counts 2,534,093 errors while
       it goes on reducing a corrupted net, with pairs no polarized net
       has (a freed node and data, two merges): reported, not crashed,
       but work wasted on a net already failed.
   - `heap-strategies.stack` — built 2026-10-28 — no
     pairs kept in the net (the maintainer, 2026-10-28): every active pair
     is in such a set once, every strategy but one would clear it, and
     switching strategies rebuilds it anyway. A stack strategy builds its
     stack when it starts, walking the net for the lower node of each
     pair, and learns of the pairs its rewrites make from a variant of
     the generated rewrites that notes each link joining two principals,
     its stack beside the net; demand's variant notes nothing, its state
     narrower; the interpreter returns the links it made. The spike's
     reducer starts from the same walk. Against 54a7481, four builds at
     k 18 (store run 35): demand 7.0% to 13.2% cheaper, the full
     reduction -4.6% to +3.8%, once the eager chain had its own payload
     test (shared, it cost 5% to 12%). The full differential test (run
     33) clean, kernel and spike step for step. With the kernel's fusion
     off, the new starting order gives every count and value of the old
     (run 34 against run 3, all 3,600 terms): a complete reduction's
     interactions do not depend on order, and the stack loses or repeats
     no pair. With fusion on, 378 of the 1,800 leveled terms change
     count with the order, 126 fewer and 252 more, -0.09% in all
     (run 33 against run 32): fusion's savings depend on order. After
     the maintainer's review: the stack keeps room for the most pairs one
     rewrite makes, four (a commutation's new nodes, each facing an
     external peer), counted over the rule table by the generator
     (`KR.most_pairs`, from `R.pairs_made`) where it had kept sixteen; the
     payload test, copied by hand for the eager chain, is generated for
     both chains from one source, and a pair whose variants differ
     without a test fails to compile. The test lost its Lift and LiftC
     arm, dead since peeling decides that pair: 0.7% to 3.5% fewer
     instructions in all four builds at k 18, the same interactions
     (store run 36, by the new `spike/tools/count_builds.sh`); the full
     differential test clean (run 37).
   - `heap-strategies.profile` — built 2026-10-28 — interactions
     counted per pair of kinds and peels, per term, into the analysis
     store. Also as logical interactions (the maintainer, 2026-10-28),
     those of the unit system: a run of k crossing a node or cancelling
     its equal is k, two runs crossing c times b, a peeled pair what
     peeling leaves; they are the unfused interactions, as many in every
     order of a complete evaluation, and fusion's savings are they less
     the interactions made, which may differ by order. Equal counts across orders test fusion's
     soundness on whole nets, beyond `ctlwire.py`'s one wire. Fusions by
     shape are not counted: one shape remains, and the savings measure
     what fusion does; controls alive wait for `heap-strategies.trace`.
     - `heap-strategies.profile.weights` — built 2026-10-28 — the
       logical interactions of each move checked on the one-wire model
       (`ctlwire.py --logical`): a fused start's reductions, every move
       counted so, all total the interactions of its runs as unit
       brackets reduced unfused. A run crossing a value, a consumer or
       another run counts its units times the other's, equal runs
       cancelling their units, a peel what it cancels or the run a drop
       crosses whole, a fusion nothing. The kernel's rule (`--peel --shapes 0`) holds on all
       4,001,400 starts to length 4 and 20,000 sampled at each of
       lengths 6, 8 and 10 (indices to 3, levels to 6), the unit counts
       never depending on order; the old fusion fails 46,872 of the
       222,264 starts of length 3 (store runs 38 to 42).
     - `heap-strategies.profile.strategy` — built 2026-10-28 — a
       profiling strategy in `kstrat.bend`: the eager one, each pair
       counted by kinds, A's principal negative, and as logical
       interactions before it interacts, the sum in two words; `kernel K
       W profile`, and `profile_t` for tests. On `lvl` at k 10, 12 and
       14 the logical interactions are as many with the kernel's fusion
       on and off (6,458,
       24,962, 98,762) while fusion saves 24% of the interactions. The
       eager and demand strategies cost what they did (store run 43
       against run 36: 0.0% in the default, inlined and profile-guided
       builds; +1.4% to +1.7% on full reductions where inlined and
       profile-guided both), though the eager rewrites now have two
       callers.
     - `heap-strategies.profile.store` — built 2026-10-28 —
       `terms.py --profile` writes each term through `K.profile_t`;
       `spike/tools/profile.sh` profiles three seeds of 200 terms per
       ending, with levels, labels and unit brackets (`--unfused`),
       into the store's `profiles` and `pair_counts` tables, and with
       `FUSE=off` a copy of the spike whose kernel never fuses;
       `results.py fusion ON OFF` compares two runs mode by mode. Store
       runs 44 (fusion on) and 45 (off).
     - `heap-strategies.profile.check` — built 2026-10-28 — fusion is
       sound on whole nets, on every term both runs complete: with
       unit brackets the logical interactions with fusion are the
       interactions made without it, on all 1,791 (3,778,521 in all);
       with levels the logical interactions with and without fusion
       agree on all 1,797. The 21 rows that do not complete ran out of
       fuel, none wrong. The kernel's fusion saves 23.3% of the logical
       interactions with levels, 21.9% with unit brackets. The
       lowering's own fused controls, a croissant cancelled against
       brackets, save far more: on the 1,794 terms both lowerings
       complete, 1,296,183 logical interactions against 8,682,189, since
       runs crossing count their product. No
       term of the 5,400 peels; only the hand-built nets of
       `test_levels.bend` do, whose profiles are now regressions there.
   - `heap-strategies.trace` — contingent on `heap-strategies.net` — the
     net as rows at boundaries the caller sets (every n interactions, a
     demand step, a count of live controls), into a store of traces,
     written from Bend once its SQLite package is vetted, else imported.
     - `heap-strategies.trace.render` — tentative — a drawing of a net
       from its rows that can focus on a part of it: a pair about to
       form a loop with no node, a vicious circle demand found, a stuck
       eraser, with the nodes within a few links and the path from the
       root (the maintainer, 2026-10-29).
   - `heap-strategies.demand` — contingent on `heap-strategies.net` —
     demand's own cost: the path in an array, the walk's layers folded
     (its profile is store run 26).
     - `heap-strategies.demand.cycle` — built 2026-10-28 — a deadlock
       reported, not walked (the maintainer, 2026-10-28): on a cycle of
       principal ports each facing an auxiliary one, the walk went round
       until its fuel ran out (the library's `costly-6` with labels: 84
       interactions, then 2.56M steps, its depth cap a fixed 2^22). A
       path as long as the net has nodes is such a cycle, so the walk
       reads the net's capacity where its depth is a power of two from
       128 and stops there in a new state, a cycle. Each push tests only
       for a multiple of 128 (a full test on every push cost demand 1.3%
       to 2.1%, store run 47); now demand costs -0.1% to +0.3% more, the
       full reduction nothing (store run 48 against 43). Lowered terms make
       no cycle with levels, but nets users wire may (`pairing-nets`):
       `test_demand.bend` and the library's `cycle-copy-lift` build one,
       and in `vicious-circle-formed` beta forms one. The walk follows
       principal ports, so the cycles it finds are exactly the vicious
       circles it reaches. The capacity test is replaced since
       (`heap-strategies.demand.cycle.early`).
     - `heap-strategies.demand.array` — built 2026-10-29 — the path in
       an array of words (`kmem_grow.bend`), its capacity in word 0 and
       the nodes from the interface on in words 1 to the depth, starting
       at 64 words and doubling, for the list with a cell per push. A
       push tests only whether the depth plus one is a power of two,
       where alone the array can be full, and reads the capacity there.
       Against 70f086f, four builds at k 18 (store runs 62, 63): demand
       6.3% to 12.3% fewer instructions, the same interactions; the full
       reduction the same within 600 instructions, -0.3% on `fma`
       profile-guided.
       - `heap-strategies.demand.cycle.early` — built 2026-10-29 — a
         cycle found soon after the walk repeats, not once the path is
         as long as the net, as the Rust bootstrap did with a two-pointer
         cycle finder (the maintainer, 2026-10-29); simpler than Brent's
         algorithm, with the path in an array (the maintainer,
         2026-10-29): just before the array grows, the node being pushed
         is compared with every node on the path. Apart from a cycle the
         path's nodes are distinct, and the walk, following principal
         ports, repeats for good once it repeats at all; so the first
         growth after it closes finds it, by twice the depth where it
         closes, and the scan costs a constant per push, amortized, as
         the copy that grows the array does. The net's capacity is no
         longer read. `test_demand.bend` adds a ring of 200 lifts through
         a copy, a vicious circle of 201 nodes found at the third
         growth, and a line of 300 lifts with no cycle, the path grown
         three times; with the comparison always false, both cycle tests
         run out of fuel. Not done: finding a circle once for later
         demands, which a cell holding the failure would do
         (`heap-cells`).
     - `heap-strategies.demand.fold` — built 2026-10-29 — the walk's
       steps made fewer and its state narrower (the maintainer,
       2026-10-29). Profiled at k 18 on `succ`, the walk's own functions
       were about a third of demand's instructions, and it took 2.0 steps
       per interaction, each a round through demand's loop returning the
       whole state: Bend cannot branch on a computed value within one
       function, nor a helper call back into the loop, so a step is that
       round. A push and what follows it are now one step: where the last
       node faces an auxiliary port and the array has room, it is pushed
       and the next node's link read before the step looks at what it
       faces, in one place, so that the rewrite's chain keeps its one
       caller (looking in two places split it into a function of its own
       and lost most of the gain): 1.5 steps per interaction. And the
       state is seven words, not nine: the handle a need waits on and the
       data node holding it, rare, left it, first for the path array's
       words 1 and 2, then for nothing (`heap-strategies.demand.need`).
       Against ffb4eee, four
       builds at k 18 (store runs 63, 64): demand 4.9% to 6.6% fewer
       instructions, the same interactions; the full reduction the same
       within 300 instructions. Then the pushes looped (`wk.down`):
       while the last node faces an auxiliary port and the array has
       room, push and read on, then look once, so that long descents
       (on `succ`, some 262,000 pushes before the first pair) take one
       step: one step per interaction on `succ` and `lvl`. Against
       51a472a (store runs 64, 65): demand 2.1% to 6.0% fewer
       instructions, the full reduction the same within 30; against
       ffb4eee, 6.8% to 12.2% fewer, and against the list (run 62),
       16.4% to 19.5%. Left: the array fill, 28% of demand on `succ`
       against 27% of the full reduction, demand's share the path, which
       there grows to about the node store's size (Bend #1890,
       `docs/BendIssues.md`).
     - `heap-strategies.demand.need` — built 2026-10-30 — waiting on a
       lazy value as one shape for any task, not a record each kind keeps
       its own way (the maintainer, 2026-10-30): a task reports that it
       is done, or waits and on what handle; the scheduler holds the
       handle while the task is parked, and the task's kind says only how
       to resume with the value. Demand keeps nothing for its need.
       Stopped (state 2), its top is the application or strict call,
       unchanged, facing the data node whose table entry is the handle:
       `KS.need` reads the handle from the net, 0 in any other state, and
       `KS.resume` finds the node again the same way (`d.at`), puts the
       value there and goes on. The path array's header is its capacity
       alone again, the nodes from word 1.
   - `heap-strategies.rewrite` — dropped 2026-10-30 — the rewrite's
     cost cut by its shape (the maintainer, 2026-10-30): reading each of
     the pair's nodes whole rather than a word at a time, narrowing the
     generated rules' arguments to what each uses, folding the payload
     test into the rule dispatch. Measured first, none holds. Reads:
     `bench/bend/node_read.bend`, four helpers each carrying six words of
     context against one four-word read, 31 instructions a step either
     way, the same code. Arguments: the rule whose body the default
     build leaves out of line, 11% of the full reduction on `succ` (a
     call meeting a merge), narrowed by hand to what each step uses,
     saved 1,088 of 351,868,256 instructions (k 18; `succ`, `lvl` and
     `fma` alike): clang drops unused arguments of these static
     functions itself, and the stack moves there are the rule's own live
     values. The payload test is inlined already, a few compares of kind
     codes an interaction. Where the full reduction's instructions go on
     `succ` (store run 66's default build): the array fill 29% (Bend
     #1890), the rewrite and its inlined rules 32%, that one rule 11%,
     the stack's loop 9%, node allocation 4.5%, applying data 5%. The
     levers left are the toolchain's: profile-guided builds run the full
     reduction 16% under the default build and demand 13% on `succ`, 14%
     and 11% on `lvl` (store run 66), and the fill.
   - `heap-strategies.erasure` — active — deadness that travels (the
     maintainer, 2026-10-30): erasers propagated as far as they can go,
     at run time, so that nothing is copied into a branch already known
     dead. An eraser at an auxiliary port forms no active pair, so the
     links rules make are inspected, as control fusion inspects them,
     and the node there changes its kind in place: a copy with one output
     erased becomes a linear copy, two ports and the side it keeps; a
     merge with one input an error value, a linear merge; a fan with
     both erased, an eraser (a fan into two erasers is one); an
     application, call or control whose output is erased, an eraser
     facing what it took in. Changing kinds in place keeps every node a
     strategy holds where it was, and frees only the erasers absorbed,
     which are in no active pair, the invariant fusion keeps. A linear
     fan still carries its identity, level or label, and its side: its
     dual must still annihilate with it, the live side wired through and
     the dead side's partner erased, so it cannot simply become a wire.
     It goes only where its full fan would go, annihilating with a dual
     or at a leaf: it selects its side at every fan of its identity it
     meets, and no local test tells when it has met them all. Dropping a
     dual pair together, the copy on a function's body and the merge on
     its argument made by one commutation and dead on one side, looked
     safe and is not: copy `\y. \x. y x` with fan A, apply the second
     copy to `a2` and drop its result, and the inner body's copy and the
     inner variable's merge learn together that side 2 is dead, while
     `y`'s merge, of identity A too, still holds `a2` live; dropped, the
     inner body's copy is not there to select side 1 at it, and the
     body's `y` stays a superposition. What a linear fan saves is the
     dead side's copies: meeting a function, it makes one function and
     linear residuals, not two functions and full ones. Only a fan that
     has never commuted, with no residuals anywhere, can become a wire
     when a side is erased (`heap-strategies.erasure.aot`). In trees of
     fans, liveness is kept fan by fan, a dead leaf making its parent
     linear and a parent with both outputs dead an eraser, so a tree
     duplicates into a subtree exactly where some leaf lives.
     - `heap-strategies.erasure.rules` — built 2026-10-30 — linear fans
       in the rule table (`spike/rules.bend`): four kinds, `KCopyL`,
       `KCopyR`, `KMergeL`, `KMergeR`, two ports each, named for the side
       kept (the kernel's codes 12 to 15, its four bits of kind full;
       the split of a header's low byte between kind and form is
       arbitrary, and 64 or 128 kinds are to be expected, reserved for
       builtin operators, all of one form: the maintainer, 2026-10-30).
       Their
       rules are derived from the full fan's (`rule.full`): the full rule
       rewrites, an eraser stands where the dead side was, erasures and
       the events above run among the new nodes until none can, and fans
       left with one side erased become linear. Every law over the rule
       table now covers them and holds: polarized, linear, exact, exact
       and total with peers inside, the test's rules small, the new
       nodes live. Two more: `rules_linear_rewrites`, a linear fan
       rewriting exactly where its full fan does, and
       `rules_linear_fewer`, where the full fan's rule makes nodes, the
       linear fan's making fewer. A derivation that leaves the fans full,
       their erasers beside them, fails the second. Derived, a linear
       copy meeting a function makes the function, a linear copy on its
       body and a linear merge on its argument (three nodes for four); an
       application meeting a linear merge, the application, a linear
       copy on its argument and a linear merge on its result; a linear
       copy meeting data, one datum; a linear copy annihilating a full
       merge, the wire and an eraser for the merge's other input
       (`spike/tools/rules_dump.bend` prints them all). The kernel's
       generated rewrites leave the new kinds out until
       `heap-strategies.erasure.kernel`. Drafted with dual pairs dropped,
       which the derivation no longer does (above).
     - `heap-strategies.erasure.events` — built 2026-10-30 — the events
       as rules (`R.event` in `spike/rules.bend`): A the node, B the
       eraser facing its port p, A's other ports the external peers in
       order, so that the kernel's placement, A's slot first, changes the
       node's kind in place. An application whose result is erased
       becomes two erasers, its function's in its own slot and its
       argument's in the eraser's; a call or control, an eraser; a copy,
       a linear copy keeping the other output, and a linear copy, an
       eraser; a merge, a linear merge, and a linear merge, an error
       value. Laws computed over every kind, eraser and port:
       `events_exact`, exact under every pattern of peers inside;
       `events_polarized`; `events_shrink`, fewer ports after, so events
       end; `events_kinds_live`; `events_side`, the side an event erases
       the side the derived rules erase. Composed: `events_keep_wired_in`,
       from the wiring proofs, and `kernel_events_in_step`, the kernel's
       placement keeping the free list and the kinds agreeing, the free
       list exact by `kernel_free_ok`, which holds for any count of new
       nodes. An event marking the wrong side fails `events_side`; one
       leaving the result's eraser where it was, `events_exact`.
     - `heap-strategies.erasure.kernel` — active — the events in the
       kernel, at the links rules make, as control fusion looks at them,
       and the linear kinds' generated rewrites; every strategy measured
       on the library's families
       (`mixin-chain` against `mixin-once`, `list-head`, `search-first`,
       `parse-cut`, `K 2 Ω`, the mixins' full reductions), and the
       standard workloads in four builds, for what the checks cost nets
       with nothing dead.
       - `heap-strategies.erasure.kernel.inert` — built 2026-10-30, on
         branch `erasure-kernel` — the linear kinds in the generated
         rewrites, which nothing yet makes: the generator tests and
         checks a linear fan's pairs as its full fan's. Values and
         interactions unchanged, but against 4ab0efc's kernel, four builds
         at k 18 (store runs 66, 69): 0.2% to 3.2% more instructions for
         the full reduction, 2.3% to 5.0% for demand. Not the rule
         table's new dispatch, which only the interpreter calls (the old
         generated tables with it: -0.3% to +0.4%, one build), but the
         generated tables' longer matches on kind codes, which Bend makes
         chains of comparisons: a cost that grows with the kinds, and so
         with the 64 or 128 expected.
       - `heap-strategies.erasure.kernel.events` — built 2026-10-30, on
         branch `erasure-kernel` — the events, in modes a strategy picks:
         each strategy has a loop running them beside its own (the
         kernel's `ev`, `evlazy`, `evtwo`), calling the rewrite chain, a
         template over the step after each rewrite, with the events where
         the other passes nothing (`generated-sources`). After a rewrite, its
         external peers are looked at (`spike/knet.bend`'s Events): every
         link a rule makes has one but those between its new nodes, and
         the generator checks no rule makes an event there
         (`inner_events`). The events' rewrites are generated from
         `R.event` with the rules', the link at the node's principal left
         as it is, so that a pair the node is in keeps its place on a
         stack, and with tables of which ports and erasers make events. A
         cascade waits on a list, not the stack; each eager event is given
         room for the one pair it may note. No interpreter for events: a
         copy's or merge's principal facing its own other output is the
         only peer an event's node can be its own, which the generated
         rewrite handles and the rule interpreter misreads (found on
         `K 0 Ω`, where eager reduction leaves such a copy). Demand first
         declined an event making its node an eraser while the node's
         other auxiliary port faced a principal, so that no node on the
         walk's path was freed; `.exact` removed the need. The header
         gains nodes for the events, counted by the kind of node each acts
         on. The library runs every entry in four
         erasure modes too (eager by the generated rewrites and by the
         interpreted table, on demand, with two stacks): values as every
         strategy's, no errors, audits passing, the two eager modes'
         interactions and events equal; all 114 cases pass. Over the
         library, interactions: eager 7,556,957 to 6,838,156 (-9.5%, with
         23,093 events), two stacks 7,554,741 to 5,787,943 (-23%, 51,082
         events), demand unchanged at 2,671,126 (58 events), fewer nodes
         live where they fire (`mixin-once-16` labels 888 to 144). The
         largest: `costly-133` levels eager 207,315 to 116,225 on two
         events; `list-bind-32` unfused, two stacks, 848,389 to 149,435;
         `demand-dead-factor` levels, two stacks, out of fuel at 100,000
         to done in 472; `K 0 (k 2 succ 0)` at k 10, two stacks, 2,174 to
         15 and 29 events. The mixins' full reductions still run out of
         fuel. Its cost, four builds at k 18 (store runs 71 and 72 to
         77, each against run 69): first, a run-time mode word guarding
         the events after each rewrite, 6% to 13% more instructions with
         events off, from no single cause the header node (run 73) or the
         word (run 74, which matched run 69 with the events unreachable)
         explains. The chain a template over the step after the rewrite
         (runs 76, 77): 9% to 15%. What the variants share beneath the
         templates, `go.which` and the generated rewrites, each gains a
         second caller, which Bend folds into neither (the cost the
         eager family's own copy of the payload test once avoided, 5% to
         12%). With events and nothing dead, 15% to 33% more than events
         off (packed tables for the checks: 5% of that recovered, run 75).
       - `heap-strategies.erasure.kernel.parity` — built 2026-10-31, on
         branch `erasure-kernel` — events off
         costing nothing, by the templates carried down through the
         generated rewrites, so that neither copy shares a function Bend
         would fold (the maintainer, 2026-10-30, over a build-time
         constant), with `.sites` the template's argument, the check at
         each site. Built: the template over `after` now reaches from
         `interact` through `go.which`, the payload test and every
         generated rule rewrite, each strategy's copy calling its own;
         each rewrite calls `after` itself at its sites, the interpreter
         at all four peers (a Lift facing a LiftC at the peers peeling
         leaves). Events off, four builds at k 18 (store run 82 against
         69, from before the modes): the same instructions within about
         2,100 in the default and forced-inline builds and their
         profile-guided one; the profile-guided build alone +0.6% to
         +0.8% on three eager workloads. The library's interactions and
         events the same as run 79's, case for case (run 81).
       - `heap-strategies.erasure.kernel.sites` — built 2026-10-31, on
         branch `erasure-kernel` — the checks
         after a rewrite only where its rule can make an event, known
         from the rule as fusion's ends are: an external peer linked to a
         new eraser's principal; one linked to a new node's auxiliary port
         at which an eraser makes an event, where the peer, by the port it
         faced, could be that eraser's principal; and one end of each wire
         joining two external peers, whose other end is read only if the
         first may be in an event. The rest are skipped: today all four
         are read after every rewrite, each call spilling registers,
         which costs the erasure modes 15% to 33% more instructions where
         nothing is dead. Built: the generator reads each rule's sites
         from its links (`gen_krules.bend`'s Sites), the others passed as
         none, and a rule with no site, 74 of the 118 rewrites, calls no
         `after`; the library's check that the generated and interpreted
         eager modes make the same events, the interpreter looking at all
         four peers, passes. With events and nothing dead (run 82): 0.0%
         to 1.0% over events off in the default and forced-inline builds
         and their profile-guided one, 20% to 34% fewer instructions
         than run 71; the profile-guided build alone 30% to 47% over,
         trained without the events, so its events loops cold. That the
         sites miss no event rests on the library's 117 nets and on
         reasoning; what would make it complete:
         - `heap-strategies.erasure.kernel.sites.random` — built
           2026-10-31 — the random-term differential test
           (`differential.sh`, `terms.py --kernel`) in the erasure modes
           too: the generated rewrites, looking at sites, against the
           interpreted table, looking at all four peers, events and
           interactions term by term, peeled pairs among them, as the
           library checks its nets. Evidence where the library's
           coverage ends. Built: each term also runs with events, eagerly
           and with two stacks, both ways; the store keeps both (store
           run 83). On the 3,600 terms, both ways agree on every term in
           value, interactions, errors and events (8,418 events eager,
           11,964 with two stacks), and no value the full reduction gets
           right changes with events. The terms' other results are run
           37's, term for term (its wrong values, static labels' and
           three leveled terms', as they were).
         - `heap-strategies.erasure.kernel.sites.law` — tentative — the
           sites read from the model, one owner for the generator and a
           law: whether a port may be in an event with some peer (an
           eraser's principal, or an auxiliary port an eraser makes an
           event at) exact against the event table for every peer, and no
           rule linking two of its own new nodes into an event (a law in
           place of `KR.inner_events`, now a check the generated file
           fails to compile without); each rule's sites then cover every
           link it makes by construction.
         - `heap-strategies.erasure.kernel.sites.fuse` — tentative —
           fusion and peeling make no event: each link they make gives
           its far end a port of the kind and number it faced before, a
           control's, so its events are as they were; stated with
           `fusion_polarized`, among the kernel's claims `spike/LAWS.bend`
           lists, once the kernel's operations have a model to refine.
       - `heap-strategies.erasure.kernel.exact` — built 2026-10-30 — the
         model's part on main, the kernel's on branch `erasure-kernel` —
         each event
         checked to preserve meaning exactly. The linear fans' rules are
         the full rules followed by erasure, by derivation, which uses no
         application event (the rule table dumped with it left out is the
         same). A call's or a control's output erased, an eraser of its
         input: the node is pure. A dead application, an eraser of its
         function and of its argument, is not exact where a variable is
         used outside its function's body, which the `interaction_net`
         escape hatch allows (`docs/Design.md`): applying the function
         would bind the variable. Shown on a net the library does not yet
         hold, `F = \v. 5` passed to `f = \g. g 7`, the result dead, the
         root reading v: 7 by every strategy, none by the eager and
         two-stack erasure modes. Demand's exception is the same case: of
         the events making a node an eraser, only the application's
         leaves it another auxiliary port, and demand reaches an
         application through its argument only past a function entered
         by its variable, since every positive auxiliary port but a
         function's variable belongs to a node with a negative principal.
         Without the application event, over the library: eager +0.3%
         interactions, two stacks +6.1% (5,787,943 to 6,141,359), and
         `demand-dead-factor` with two stacks out of fuel again; demand
         the same. Then every event making an eraser erases its node's
         last auxiliary port, and demand needs no exception. Dropped
         (the maintainer, 2026-10-30): no event for a dead application,
         in `R.event` or the derivation; the rule kept as an optimization
         where it is exact, as at lowering where a function's scope is
         known; part of its use may be masked where data nodes capture
         and copy closed subnets (the maintainer). Law
         `events_erase_last`: an event making its node an eraser erased
         its last auxiliary port (it fails with the event restored), so
         demand's exception is gone. The net above in the library,
         `ap-dead-extruded`. Over the library now: eager 7,556,961 to
         6,856,871 interactions (-9.3%, 18,964 events), two stacks
         7,554,745 to 6,141,363 (-18.7%, 35,805), demand the same.
         The calls and the controls reviewed (the maintainer, 2026-10-30:
         stuck is not to become an error value by default), by the law
         teased out of it, `events_erase_exact`: an event that makes its
         node an eraser leaves, whatever the node's principal meets, what
         the eraser alone leaves there, the rule followed by the erasure
         against the eraser's rule, both normalized by the derivation's
         normalizer, linear fans as their full fans with the dead side
         erased (`R.ev_exact`; the interface left out). Tabulated over
         every kind and test: the linear fans' collapses exact; a call's
         event not, against a function, where its rule is stuck and the
         event erased the function: dropped, from `R.event` and the
         derivation, whose rules are unchanged. A control's event exact
         but against a function, where lifting leaves a co-control holding
         an error value; a co-control whose input is an error value
         becoming that error value, a new event, closes it and is exact
         against everything: added. The law fails with the call's event
         restored. Over the library: eager 6,849,159 interactions (19,420
         events), two stacks 6,108,846 (36,151), demand the same; but the
         kernel's `K 0 (k 2 succ 0)` at k 10, with two stacks, back to
         2,174 interactions, its dead calls of `succ` no longer erased.
         Generalized (the maintainer, 2026-10-30): every fusion behaves
         as its components, the fused op as the ops it stands for, and
         what does not reduce expanded does not reduce fused. Two laws
         replace `events_erase_exact`, which compared only what the
         partner's external peers faced: `linear_as_components`, a linear
         fan against its full fan with the dead side erased, and
         `events_as_components`, each event's pattern, the node and the
         eraser at the port it erases, against the node the event makes;
         each stuck where the other is, or else leaving the same graph,
         linear fans expanded, normalized up to the events (each itself
         under the law), compared in a canonical order from the external
         peers. All hold over every kind, port, partner and test. Four
         mutations each fail them: the call's event restored (10 cases),
         the linear copy's sides swapped (28; `events_side` is implied),
         the co-control's event left out of the normalizer (13), one
         linear rule replaced by its full fan's (2). Control fusion is
         the third kind of fusion: `units_are_run`, `run_splits` and
         `peel_pairs_units` say it of levels; the same of a run's rules
         against each partner, and where it is stuck, against its unit
         controls', is wanted. Recorded as `fusions-as-components`; what
         the laws must still say is `heap-strategies.fusions`.
     - `heap-strategies.erasure.strategies` — tentative — erasure under
       demand as a strategy of its own; or demand with eager collection
       on a second stack, as the two-stack strategy keeps its deferred
       pairs; and the two-stack strategy with only collection on its
       priority stack (the maintainer, 2026-10-30), the rules a
       collection admits (`KR.collects`) on its second stack (the
       maintainer, 2026-11-01).
     - `heap-strategies.erasure.aot` — tentative — the simple case ahead
       of time (the maintainer, 2026-10-30): a fan that has no remote
       dual yet, as a variable's tree of fans before it commutes with
       anything, has nothing to annihilate with, so an erased side makes
       it a wire, and its tree can be rebalanced.
     - `heap-strategies.erasure.trees` — tentative — chains of linear
       fans, if they come to dominate, compressed into one node holding
       the tree's identity and the path, as runs of controls fuse.
     - `heap-strategies.erasure.deadcall` — built 2026-10-31 — a dead call, a
       call fused with the eraser at its output, under the same law
       (the maintainer, 2026-10-30). Its components against each
       partner, derived as the linear fans' rules are: stuck against a
       function, as a call is; two dead calls against a superposition;
       nothing against data or an error value, so the builtin need not
       run; one dead call against a co-control or a linear merge: so
       the kind is closed, and stuck where a call is. A dead call facing
       another call's output making that call dead too is exact where a
       call against data never sticks, as the table has it, so a chain
       of calls dies whole: what `K 0 (k 2 succ 0)` lost. It cannot
       erase its input before the input is a value. It needs a kind
       code past the 16 the header's four bits hold, so the kind field
       widened first (the maintainer, 2026-10-30: 64 or 128 kinds
       expected for builtins).
       Built as the kind `KDCall`, code 16, its rules derived as the
       linear fans' are (`lf.derive`) and generated with the rest, and
       one event, a call's output facing an eraser making the call dead
       (`R.event`'s `ev.call`), found where a rewrite makes a call (the
       sites). Every law over kinds widens to it, the proofs a case more
       each; a new law, `events_fit_header`, holds that only kinds coded
       below 16 make events, since the net's header counts them a word a
       kind. The profile counts pairs of classes, 32 to a row, not
       pairs of kinds. Four library entries: a dead call meeting data,
       one whose argument is computed by a live call, one that dies too
       late since beta joins its output to the eraser after the call is
       made (the full reductions call first), and one copied with its
       function, meeting a superposition and, unfused, co-controls.
       Against store run 81, the library (run 94) makes 1 to 4
       interactions fewer and an event more in `costly-107`,
       `costly-124`, `list-head` and `list-sum`; `K 0 (k 2 succ 0)`
       at k 10, with two stacks and events, 2,173 interactions and 3
       events against 2,174, the eager reduction unchanged: the calls of `k 2 succ 0` still run,
       each feeding the next, which is the chain's work. Four builds at
       k 18 (run 95 against 92): -2.2% to +1.1%, the interactions
       unchanged; the seventeenth kind costs nothing measured. Merged,
       the dead call's payload read as none by the rewrites and the
       sweep (`knet.bend`'s `payload.k`, `sw.payload`), which only a
       function held in the data table shows: the library's
       `dead-call-table`, a copied `fma 1` whose dead side freed the
       live side's entry, now kept.
       - `heap-strategies.kinds.payloads` — built 2026-10-31 — which
         kinds hold a value and in which word, written by hand in the
         kernel (`knet.bend`'s `is_data`, `payload.k`, `sw.payload`),
         three places a new kind can be missed in, as the dead call
         was. Now the generator's `holds` says what each kind's payload
         word holds, a value, a control's index and offset or nothing,
         every kind named, so that Bend refuses a new kind left out
         (tried); it writes `is_data` and `payload.k`, the word where
         `kprim.bend`'s `node.word` puts it, and the sweep reads that
         word. The generated maps are the hand-written ones case for
         case. Spot check (store run 96 against 95): the default build
         0.8% to 1.4% more, forced inline -0.4% to +1.7%, all of it the
         dead call's arm added by the fix before (main alone, run 97,
         the same counts); the move costs nothing.
         - `heap-strategies.kinds.payloads.links` — built 2026-11-01 —
           which of a node's words are links follows from its kind alone,
           not its form or field (the maintainer, 2026-11-01): the
           kernel's ports are R.arity's, kind_arity generated from it and
           read from the header's six kind bits; the payload's word comes
           from the kind too (`kprim.bend`'s `node.word`). Law
           `payload_past_links`: a kind holding a payload keeps it past
           its links, so that a kind of three ports holds none. The
           generator's `holds` moved to the model (`rules.bend`'s
           `R.holds`) for the law to read; the generated rewrites are
           unchanged. The law fails where a kind of three ports is given
           a payload, or an operator's payload word is moved onto its
           second port's link (both tried). The operator's rotation,
           which kept an argument in the word a consumed link freed,
           retired with `operator-nodes`.
       - `heap-strategies.erasure.deadcall.chain` — built 2026-10-31 — a
         call whose output faces a dead call's principal dies too: the
         dead call met is B to the event, freed with its builtin, whose
         payload the events path then drops (an eraser has none). Exact
         since a call's output is data, which a dead call always
         erases. A call here is a builtin's alone: an application
         meeting data that is a builtin function (`net.bend`'s
         `rule_test`, `is_builtin`), which waits for its argument to be
         data and makes data of it (`rules.bend`'s `rule.call`). The
         Rust bootstrap's call, applying a function or net value held
         as data, lowered a closed net whose output need not be data
         (the maintainer, 2026-10-31); a rewrite like that is no call in
         this sense, and neither the dead call nor the chain is exact
         for it; a copy's output facing one makes no event, since what
         it carries may be a function, against which a dead call is
         stuck. `R.event` gives the call's event for both B;
         `events_as_components` checks it for both, a dead call in the
         pattern as its components, and the derivation's normalizer runs
         a dead call's events as it runs an eraser's, so that a call
         feeding one dies. Against data, the components compute and
         erase what the dead call erases unread; against a
         superposition, both sides end in two dead calls, the result's
         by the eraser's event alone. The chain event erasing the call's
         input instead, the law fails. The generator finds the kinds B
         may be from `R.event` (`is_ev_b`: the erasers and the dead
         call), widens the sites to a new dead call's principal (the
         dead call's four rules), and dispatches an event by B's kind
         too; `ev_also` answers for B besides the erasers, and a port
         where only such a B makes an event would not compile
         (`ev_only`), since `ev_end` would not look at it. The kernel
         reads B's payload word for every event. Library: the chain
         (`dead-call-chain`, the outer call made first: 2 events, 4
         interactions, no builtin run), the inner call made first
         (`dead-call-chain-late`: it calls, nothing to chain), and B's
         function in the data table (`dead-call-chain-table`; without
         the drop, the audit fails in every erasure mode).
         `K 0 (k 2 succ 0)` at k 10, with two stacks and events: 1,661
         interactions and 515 events, against 2,174; the eager
         reduction, which calls before the eraser reaches it, unchanged.
         The random terms (store run 98) give run 83's values and
         counts term for term, the events more (the dead calls and the
         chain). Four builds at k 18 (run 100 against main, run 99):
         without events the same instructions; with them -0.8% to
         +0.3%.
     - `heap-strategies.erasure.deadcall.eraser` — built 2026-11-01 — a
       dead operator is a data-only eraser (the
       maintainer, 2026-10-31): an operator's input and output are
       always data, so once its output is erased nothing it holds, its
       function, opcode or collected arguments, is ever observed. The
       dead call keeps its function until its argument arrives, to
       copy it against a superposition and drop it at the end; dropped
       at the event instead, its table entry freed then, one
       payload-free kind serves every dead operator, and the chain
       reads no payload of B's. Its law as components holds if the
       eraser's event drops the payload too, so that the components
       end in the same payload-free nodes. Built: the operator's event,
       by an eraser or a dead operator, makes a dead operator holding
       nothing, the builtin dropped there; `events_as_components` holds
       unchanged, and the dead operator's derived rules take nothing of
       its (against a merge, two dead operators, no entry duplicated).
       New laws: no rule or event takes a payload from a kind that holds
       none (`R.bare`, every kind named: the free slot, the erasers, the
       root, the dead operator; `rules_take_held`, `events_take_held`),
       so the kernel never reads a word such a node does not hold, nor
       B's word at an event; the generator names any B that holds a
       payload (`inner_events`). Mutated, the chain's dead operator
       taking B's payload fails the second; the dead operator given a
       payload again names itself in the generated file. The random
       terms give run 107's results term for term, events too (store run
       109); four builds at k 18 (run 110 against 108): the same
       interactions, -5.0% to +0.5% instructions, most builds fewer.
     - `heap-strategies.erasure.load` — built 2026-11-01 — patterns recognized
       only when lowering or loading a fresh net, perhaps after a GC
       cycle (the maintainer, 2026-10-30), against after every rewrite:
       nothing paid per rewrite, but the events that arise while
       reducing (`K 0 Ω`'s copy, the library's search and list
       families) missed until the next load; to be counted. What is
       recognized there answers to the same law, each pattern behaving
       as its components, and lowering knows more than the kernel does:
       a dead application is exact where the function is known to keep
       its variable inside its body, a dead call's input erasable where
       it is known to be data (the maintainer, 2026-10-30).
       Built: a net's collection, at load or wherever a net is
       collected (the maintainer, 2026-11-01: cheap work that carries
       erasers belongs to a collection; with only the sweep, everything
       is still joined to the initial lowering). Its events once
       (`knet.bend`'s `ev_load`: every eraser and dead operator's
       principal on the events' worklist); the pairs that do not grow
       the net (`kstrat.bend`'s `collect_h`, after
       `heap-strategies.cascade.nongrow`: the eager loop, events on,
       from every active pair, rewriting those `KR.collects` admits,
       never stuck, no more nodes made than freed, no builtin applied,
       no data copied (admitted since `.load.cycle`), no need for a lazy
       value touched, which the
       generator writes from the rule table, a header test deciding where
       the variants differ: erasure, annihilation, beta at one level,
       controls passing data or each other); then the sweep by
       reachability (`KN.sweep`). The library ran both on every case,
       the value and state demand reaches kept and the audits passing;
       the collection at load, finding nothing worth its pass, is retired
       (the maintainer, 2026-11-01), its mode and `KS.collect_h` with it.
       On a freshly lowered net, before demand: 2,462 interactions and
       42 events over the 126 cases, demand after them 2,668,962
       interactions against 2,671,168 alone, 0.01% more in all; a sweep
       there frees what lowering left unreached (`dead-call-data` 6 nodes
       to 2). On what demand leaves: 230,585 nodes live, 95,332 after the
       collection's pairs (20,186 events, 141,837 interactions; erasure
       pairs alone left 126,346), 317 after the sweep, which reduces
       nothing. A fresh net offers little cheap work; a net reduced
       offers much, and the sweep takes what the cheap work cuts off.
       - `heap-strategies.erasure.load.cycle` — built 2026-11-01 — a
         collection in the middle of a run, where work still lives. At
         demand's end it is no use: a net is collected there by freezing
         it, which copies only what is reached (the maintainer,
         2026-11-01), so the library's collection after demand (`gc`)
         is retired. It pays before demand grows its net, its fuel
         proportional to the net's capacity, amortized a constant per
         node, its pairs taken as a queue so that it spreads over the net
         rather than following one part down, data copies admitted, the
         table's growth bounded by the copy nodes they consume (the
         maintainer, 2026-11-01). Built: before each step `kstrat.bend`'s
         `demand.c` checks that the free list holds the most nodes a
         rewrite takes (`KR.most_alloc`, 2, generated from the rule
         table); where it does not, `collect_cycle` runs the events at
         load, the pairs `KR.collects` admits first in first out
         (`P.popq`: the stack's array as a queue, its pairs sliding down
         where half of it is taken), at most twice the capacity of them
         looked at, then the sweep, and doubles the net unless a quarter
         of it is then free (`P.frees`; `P.grow_more` keeps the free
         list it finds, which the library's free-list audit caught); the
         walk restarts at the interface. Copy meeting data joins
         `KR.collects`, the only rule that changes. The library runs it
         on every case (mode `dc`), value and state kept and the audits
         passing (store run 113): 79 of 126 cases collect, 1 to 7 times;
         their capacities sum to 216,448 nodes against demand's 411,264
         (`costly-133` with levels 65,536 to 4,096; `list-sum` with
         levels 16,384 to 4,096, unfused 32,768 to 8,192; `mixin-once-16`
         with levels 4,096 to 1,024); demand makes 2,631,396 interactions
         against 2,671,168 and the collections 103,272 (13,759 events),
         2.4% more in all, the collections doing some of demand's work.
         A net that keeps all it makes pays and gets nothing back: `succ`
         on demand at k 14, 15 and 16 collects 8 to 10 times, doubling
         each time, for 29% more instructions (7.9M, 15.7M, 31.4M more:
         linear, about 240 a node of the capacities scanned; the
         default build). Every other mode is unchanged: the spot check's
         interactions the same, its instructions within 0.4% (run 114
         against 112).
         Ablated on the library, one change at a time, every case passing
         (capacities summed; interactions, demand's and the collections',
         against demand's alone): as built 216,448 (+2.38%); a stack
         rather than a queue 214,144 (+2.35%); no data copies 216,448
         (+2.38%: copies hardly arise); no events 218,496 (+2.45%);
         collecting only where the free list is empty 219,520 (+2.46%);
         doubling unless half is free 263,040 (+1.92%), unless an eighth
         is 202,752 (+2.22%); the sweep alone 411,264, nothing changed,
         as `heap-strategies.cascade.reach` found. The pairs a collection
         rewrites cut the garbage off, and the threshold sets how much is
         kept; the queue, the copies and the events barely move it here.
         Where `heap-strategies.cascade.combined` halved three
         capacities, this halves most: its growth (`P.grow_more` then)
         dropped the free list it found, as this one's did until the
         library's audit caught it, and that branch had no free-list
         audit, so a collection short of its threshold lost what it
         freed; likely the difference, not rerun.
         Revised the same day, after the maintainer's review: room asked
         for per rewrite, by what it takes, most rewrites asking nothing;
         a quarter's margin trades too much speed for space (a collection
         touches up to three live nodes per node made there, one at half),
         so the net doubles unless half is free; the collections'
         interactions and events count in the total, apart for analysis;
         running out of memory is not being stuck
         (`machine-limits-not-errors`); the collection at load freed
         nothing worth its pass and is retired (the library's `ld` mode,
         `KS.collect_h`). Built: the rule table gives, per rule, its stuck
         code with the nodes each variant takes from the free list
         (`KR.room_hd`, the variant picked by the header test that
         `KR.collects` makes; the generator refuses a rule whose variants
         differ any other way); demand's walk takes its rewrite and that
         code as templates (`~rw`, `~sbf`), so plain demand's code is as it
         was, and the collecting demand reads the free list only for the
         16 of 56 rules that take nodes. The walk goes on where it was
         after a collection, not from the interface: the pair it stands on
         takes nodes, so no collectable rule rewrites it; but the
         collection's events change kinds in place and could make it
         collectable (an eraser on a fan's auxiliary port making it
         linear; two linear fans commute into two nodes), so the
         collection leaves that pair out, a boundary (the maintainer,
         2026-11-01). Where its path or net cannot grow, the walk returns
         out of memory (6), an error of the runtime and no state of the
         net (the maintainer). With half: the capacities of the 126
         earlier cases sum to 262,784 nodes, 1.9% more interactions in all
         (store run 121, 144 cases with the loops, 2.0%); the collections
         scan 0.14 nodes per interaction.
         - `heap-strategies.erasure.load.cycle.cost` — built 2026-11-01 —
           what a collection costs where it frees nothing, measured on
           `succ` on demand at k 14 to 16, every collection doubling the
           net, and ablated pass by pass. Room asked per rewrite through
           calls of its own cost more than the per-step test, about 280
           instructions a rewrite against about 30 a step: each call
           between functions is a task boundary in Bend's runtime. So the
           walk's templates carry the code, and the rewrite is written out
           where the calls would fall
           (a wrapper over one templated rewrite cost plain demand 4%;
           reusing a walk's specialization from the stress test cost it
           3% to 5%, forced-inline builds too). Then the cycle: arrays
           made at their size (the sweep's worklist had doubled from 64
           words, copying, to twice the capacity); the sweep counting the
           free nodes, read a mark word per 32 nodes, so no walk of the
           free list decides growth; one scan for the events and the
           pairs, the walk's pair left out by scanning around its lower
           node, a pair being noted from that node alone (the maintainer;
           a test a node had cost no more, the tests stopping at the
           first that fails). From 240 instructions a node of the
           capacities scanned to 174 (run 123, the default build): 21% more
           than plain demand on `succ`, linear, where it was 29% with a
           quarter's margin.
           What remains, a node of final capacity: the sweep 86 (the
           marking walk and the pass), the scan with the events and pairs
           42, the room asked 32. Every other mode unchanged (spot run 122
           against 114: forced-inline builds equal, default builds within
           -0.4% to +1.1% on the event modes alone).
           - `heap-strategies.erasure.load.cycle.fuse` — dropped
             2026-11-01, for `.trace.lean`, the walk finding what the
             pass would have — the
             scan folded into the sweep's pass, the pairs run after the
             sweep: what they cut off waits for the next collection.
             Emulated on the library: 447,360 nodes deciding growth on
             the free list after the pairs, 451,712 on the sweep's own
             count, against 435,072, for one pass less.
         - `heap-strategies.erasure.load.cycle.stress` — built 2026-11-01
           — a stress test (library mode `dcs`): a net of 1024 nodes or
           fewer collected before every rewrite that takes nodes, grown
           only where that rewrite lacks room, the walk going on as after
           any collection (the node it collected for noted in the net's
           header, so as not to collect for it again). 162,002 collections
           over 123 cases, every value and state kept. It finds nothing
           with the boundary removed either: no library net has events
           make the walk's pair collectable. Since `.reserve`, whose
           collections come between steps, it collects a net of 1024
           nodes or fewer every 16 steps instead (11,229 collections over
           132 cases, every value and state kept); chunks of 4 steps made
           no progress, the walk starting again from the interface each
           time, a step for each power of two in its depth.
           - `heap-strategies.erasure.load.cycle.stress.events` —
             tentative — a net where they do: a copy meeting a merge at
             two levels, erasers on an auxiliary port of each; it needs
             merges and positive erasers in the library's nets
             (`terms.py`'s node kinds).
         - `heap-strategies.erasure.load.cycle.oom` — planned — a failed
           growth counted apart from the program's errors (`P.h_err`), in
           the eager strategies too (`machine-limits-not-errors`). With
           it, configured memory limits, if their cost is negligible (the
           maintainer, 2026-11-03): a net may hold 2^28 nodes
           (`net-capacity`), more than a machine may give, and an
           allocation the machine refuses is a crash, not out of memory.
         - `heap-strategies.erasure.load.cycle.loops` — tentative — loops
           in constant space, as functional programs run them (the
           maintainer): the library's `loop-toggle` and `loop-junk`
           families, a Church boolean toggled 2^6, 2^8, 2^10 times in
           continuation-passing style, a branch dropped each step, the
           continuation shared by both. In the net they are not: demand's
           live nodes grow with the steps (levels 557, 2,019, 7,801), and
           collecting keeps the same capacities (16,384 at 1,024 steps);
           only with labels does it keep half. A census after a collection
           mid-run finds what lives reached: lifts and lift controls
           chained on the continuation's path, with copies and merges
           (unit brackets, 16,000 steps: 4,540 lifts, 1,536 lift
           controls). No collection by reachability frees them; fusing
           control chains might (`fuse-control-runs`); a chain's levels
           stay bounded here (the largest 12 over the whole run, the
           largest raise 9: levels as deep as the count was built, 2^10).
           The motive for collection wants such loops in constant space
           first. A tail-recursive loop by a fixpoint (`loop-fix`, 16, 32,
           64 steps, a Scott numeral counted down, the dropped branch
           sharing the loop) is worse: demand's interactions grow about
           3.4 times a doubling with levels (8,044, 26,446, 94,440), 2.9
           with labels, near quadratic, each step's copy of the loop
           passing the fans the dropped branches left on it; and its
           levels count the recursion, about two a step (`.loops.levels`).
         - `heap-strategies.erasure.load.cycle.library` — tentative — the
           threshold and the fuel decided on programs that drop more as
           they run (`pairing-library.programs`), speed weighed with space
           (half, or a quarter with a collection that learns: one freeing
           little making the next growth larger), the queue against the
           stack there too, and on what a reload after freezing finds
           (`heap-freeze`).
     - `heap-strategies.erasure.load.cycle.loops.levels` — tentative —
       levels that count a recursion's depth (the maintainer, 2026-11-01: after fusing, a
       long-running loop may run out of levels). Measured on `loop-fix`
       with unit brackets: the largest live level 15, 25, 37, 55, 81, 119
       at 5,000 to 160,000 steps, about two a step of the loop, so a
       24-bit field holds some eight million steps of a tail-recursive
       loop; the quadratic cost hides it for now. A level past the field
       is caught (`P.lift_wraps`) and an error, a limit of the
       representation. Wanted: more bits, levels renumbered where a
       collection traces every live node (only their equalities and the
       lifts' offsets matter, if the window of live levels drifts up), or
       a stated limit on what one net can represent. The window does not
       drift: the live levels run from 0 up, nodes at levels 0 to 2
       growing too (93, 173, 256 at 5,000, 20,000, 80,000 steps), so
       renumbering from the least live level gains nothing; more bits, or
       a stated limit, remain.
     - `heap-strategies.erasure.load.cycle.trace` — dropped 2026-11-01,
       for `.trace.lean`, rewriting as the walk reaches pairs costing
       twice the scan it saved (the prototype below) — more
       phases in one (the maintainer, 2026-11-01: more to squeeze from
       collection, eval as part of tracing; it is heuristic, trading
       completeness, space and speed): the marking walk finding the pairs
       and events as it reaches them and rewriting the collectable ones
       there, what they cut off then never marked, the sweep's pass
       after; one walk and one pass where there are two scans, a walk
       and a pass. Prototyped 2026-11-01 on branch `gc-trace-proto`
       (efa0583), not merged. A rewrite relinks its ends, so it needs a
       barrier: each marked end sees what its port now faces, and the
       redex's slots lose their marks; control fusion frees a control and
       links its far peer across, one step past the ends, so the far
       peers of ends on controls are barriered too (without that, five
       levels-mode loop cases broke, caught by the library's audits).
       Then all 153 cases pass, the stress mode too; capacity within 0.3%
       of the current cycle, the collections' interactions 6% fewer
       (114,892 against 122,594: pairs in garbage left to the sweep);
       but 364 instructions a node of final capacity on `succ`, against
       174, the walk carrying an eight-field state through some ten
       calls a node, each dear in Bend's runtime.
       - `heap-strategies.erasure.load.cycle.trace.lean` — built
         2026-11-01 — the marking walk notes the pairs (from their lower
         node) and the possible events it reaches; the sweep's pass frees
         what it did not reach and counts the free nodes; then the noted
         events and collectable pairs run, first in first out, the walk's
         own pair excluded there. What they free is free at once; what
         they cut off, and their part in deciding growth, wait for the
         next collection: latency traded for simplicity (the maintainer).
         One walk and one pass where a scan, a walk and a pass were:
         159 instructions a node of final capacity on `succ` against 174
         (run 125), 19% more than plain demand, linear; capacities 2.7%
         greater on the library (650,368 nodes against 633,472, store run
         126), interactions 2.37% past demand's against 2.50%; every case
         kept, the stress mode too. Other modes unchanged (spot run 124).
         This replaces the scan (`.load.cycle.fuse` with discovery in the
         walk).
         - `heap-strategies.erasure.load.cycle.trace.lean.count` — built
           2026-11-01 — the eval's frees counted
           toward growth (the maintainer): its rules take no node from
           the free list, so what it frees lies above the list's head as
           the sweep left it, counted by walking down to that head
           (`P.freed_since`), a step a node freed. Capacities 645,760
           against 650,368 (the scan-first cycle 633,472); of the six
           cases whose capacity differs among the three, it brings
           three back (`costly-133` with levels, 8,192 to 4,096;
           `list-bind-16` and `mixin-once-16` with labels); `search-count`
           and `list-length` stay doubled, what they lack cut off, not
           freed. Instructions unchanged (158 a node on `succ`).
     - `heap-strategies.erasure.load.cycle.perf` — built 2026-11-01 — the
       lean trace's costs by part (store run 127), on `succ` at k 14 and
       16 (no garbage: every collection grows) and on 16 library terms
       that drop what they make (`costly-133`, `search-count`,
       `list-sum`, `list-length`, `mixin-once-16`, `loop-junk-1024`, by
       `spike/runmode.bend` on nets from `tools/library_nets.py`). On
       `succ`, 158 instructions a node of final capacity over plain
       demand: some 46 without any collection (the room asked, the
       growth), the sweep's pass and the eval a few, the marking walk the
       rest, about 110. On the dropping terms, collecting costs 7.6% over
       plain demand; 4.5% of it is there with no collection at all, 3.5%
       with no free-list check either: the collecting walk's own path,
       some 33 instructions a rewrite, the rules that take nodes passing
       two more calls. Without the eval it costs more (8.6%): the nets
       grow, and later collections scan more. Growing unless two thirds
       are free rather than half (the maintainer: at worst two nodes made
       for each kept) changes no instruction count here and one capacity
       on the library (`mixin-once-16` with labels, 256 to 512; 646,272
       nodes against 645,760): these programs seldom end a collection
       with between half and two thirds free.
       - `heap-strategies.erasure.load.cycle.third` — tentative — two
         thirds free before no growth, its bound worth having for loops
         that keep a steady live set (half the collections at worst), at
         no cost measured here. Half for now (the maintainer,
         2026-11-01).
       - `heap-strategies.erasure.load.cycle.dispatch` — dropped
         2026-11-01, retired by `.reserve`, which asks no room — the
         collecting walk's own cost, 3.5% on dropping terms with no
         check made: the rules that take nodes reach their rewrite
         through two more calls (`wk.room`, `wk.room.go`); a path as
         short as plain demand's, the free-list test made where the
         rewrite is written out.
       - `heap-strategies.erasure.load.cycle.leaves` — dropped
         2026-11-01, for `.walk`, where it is implicit — nodes of one
         port (data, erasers, dead operators) marked without a visit.
       - `heap-strategies.erasure.load.cycle.entry` — dropped
         2026-11-01, for `.walk`, where it is implicit — the worklist
         holding the reference each node was reached by, its visit
         skipping that port.
       - `heap-strategies.erasure.load.cycle.walk` — built 2026-11-01,
         in its lean form (`.walk.lean`) — the
         marking walk the maintainer envisions (2026-11-01): its state a
         mark bitmap and a visit stack, one array; a node marked before
         it goes on the stack; the walk follows links, a node of two
         ports passing it on through its other port, a node of three
         pushing one of its other two (if the node behind is unmarked,
         marked as it is pushed) and following the other, a node of one
         port, or one marked already, ending the run, the stack popped
         then. The port a node is entered by is known (the reference
         followed or pushed carries it), so it is never looked at again,
         and leaves cost a mark. A pair is noted where the walk crosses
         its principals' link into an unmarked node (that node, entered
         by its principal, looks no further), or, both ends marked, by
         the lower; an event's B where the walk enters it from an
         auxiliary port. The notes grow from the array's other end and
         become the eval's queue. Against the present walk, a pop, a
         push and a look back saved a node, fewer calls; the walk is
         some 110 of `succ`'s 158 instructions a node. Prototyped
         2026-11-01 on branch `gc-walk-proto` (1aaa1da), not merged:
         every library case kept, the same capacities, but 183 to 188
         instructions a node of final capacity on `succ` against 116 to
         122 (store runs 132, 130), 6.0% over plain demand on the
         dropping terms against 4.3%. Bend returns a helper's result
         through an array its caller copies, at every level, and the
         walk passes its nine-word state through some ten levels a node
         (`docs/BendIssues.md`, "Records returned through every level,
         where clang will not inline"). Forced inline it is the cheaper
         walk, 86 to 92 against 116 to 122, 74 to 80 against 102 to 108
         with the next Bend's fill; clang inlines the worklist walk's
         chain in the default build and not this one's, and a
         profile-guided build does not help (store run 134). So the
         walk's design does less work; what is wanted is a state small
         enough and a chain short enough that clang inlines it by
         default (the maintainer, 2026-11-01).
         - `heap-strategies.erasure.load.cycle.walk.lean` — built
           2026-11-01 — the walk in a state clang inlines whole (the
           lean trace's walk in `spike/kstrat.bend`): five words (the
           net's words, its data table set aside; the walk's one array;
           the reference to enter; the stack's top; the next note's
           word), each helper called from one place. One array of twice
           the capacity holds the marks, the notes and the stack; a nil
           link finds its mark in the array's last word, set whole, since
           Bend's indexes wrap. The worklist walk it replaces is removed.
           Every library case kept, with the same capacities, collections
           and nodes scanned as the worklist walk, 27 more interactions
           collecting and 13 more events in 3.37 million, the queue's
           order differing (store runs 135, 131). On `succ`,
           instructions a node of final capacity over plain demand, k 16
           to 14 (store run 136):

               walk                   default   forced    next Bend  next, forced
               worklist (main)        116-122   116-122   108-114    102-108
               maintainer's (proto)   183-188    86-92    168-174     74-80
               lean, a: branchless    119-125   118-124   103-109    103-109
               lean, b: branches      105-110    99-104
               lean, c: o2 lazily      93-99     88-94
               lean, d (merged)        82-88     81-87     68-74      67-73

           Commits a to d on branch `gc-lean-walk`: 0f45dbc, 4d00ba9,
           473d2c9, cd86179. (a) The state cut and each helper called
           once, written without branches (a note's word written whether
           kept or not, the stack's top read whether popped or not):
           clang inlines it whole, the default build counting as the
           forced, but the work grew. (b) Branches back where a word would be read or written
           for nothing. (c) A node's third link read only where it has
           three ports, and nil found by the wrapped index rather than
           masked at every link. (d) A pair's candidacy one test, `(l1 |
           o1) & 3 == 0`, rather than three, o1 being `1 >> p`. On the 16
           dropping terms, 3.76% over plain demand against the worklist
           walk's 4.38% (forced inline, 3.11% against 3.80%; store run
           136).
           - `heap-strategies.erasure.load.cycle.walk.trim` — built
             2026-11-01 — two tests a node fewer: the stack popped where
             a run is known to end (a leaf, or a marked node behind o1)
             rather than tested for after every step, so that the loop's
             own test of the reference finds only the walk's end; and
             the arity split once, by its half (a leaf, or two or three
             ports), the third port asked for only where there are two
             or three. On `succ`, 80 to 86 instructions a node of final
             capacity by default and 77 to 83 forced inline, against 82
             to 88 and 81 to 87; with the next Bend's fill 64 to 69 and
             65 to 70; on the 16 dropping terms 3.74% over plain demand
             (forced inline 3.02%); the plain workloads unchanged in the
             four builds (store runs 139, 138 against 137). The library's
             figures are the lean walk's.
           - `heap-strategies.erasure.load.cycle.walk.inhead` — dropped
             2026-11-01, no gain once Bend fills arrays fast (the
             maintainer: to adopt given enough benefit) — the mark kept in
             the node rather than a bitmap, so that the walk, marking the
             node behind a link, brings in the line its visit reads. The
             header word has no bit to spare (`header-kind-byte`: six of
             kind, two of form, 24 of field); port 0's link word has
             nine, a link being below 2^23 (2^21 nodes of four ports), and
             every live kind has a port 0. So the top bit of word 1 was
             tried (branch `gc-walk-inword`, d674eb4): the walk marks
             there, masks it from a node's own port 0 link where it reads
             it, and the sweep, reading word 1 of every node in use, frees
             the unmarked and clears the rest; the walk's array keeps the
             notes and the stack alone, half as large. Every library case
             kept, the same figures. On `succ`, 74 to 79 instructions a
             node by default and 74 to 80 forced inline against the
             trimmed bitmap's 80 to 86 and 77 to 83, all of it the
             array's fill halved: with the next Bend's fill, 66 to 72
             and 65 to 71 against 64 to 69 and 65 to 70, the sweep's read
             and write of every live node's word 1 taking back what the
             cheaper marks save; cycles at k 16 alike, `succ` allocating
             mostly in order (store run 139). It would also add the bound
             on links as an invariant to own, and a nil link could no
             longer be caught for nothing.
         - `heap-strategies.erasure.load.cycle.walk.nil` — contingent on
           `spike-refinement` — whether to keep the walk's net under nil
           links (its array's last word set whole, one write a
           collection): the maintainer asks whether nil links are used
           at all (2026-11-01). The kernel makes none: every link it
           writes joins two ports, a peer read from a live port or a new
           node's; `P.nil()` is only a sentinel (no partner, a rule's
           unused external end, the audits' guards). An unlinked port
           would not hold nil anyway but a stale word, a node fresh from
           the free list keeping its old ones. What excludes both is the
           wiring: the models prove every rewrite keeps a wired net wired
           (`rewrite_wired`, `kernel_rewrite_wired`), and the library
           audits the kernel's nets for it (`KN.wired_ok`, which a nil
           link fails); that the kernel's rewrites do what the model's do
           is a draft (`kernel_rewrite_refines`). Once it is a law, the
           net goes or stays as the maintainer chooses.
         - `heap-strategies.erasure.load.cycle.walk.directed` — active —
           the maintainer's (2026-11-02): links run both ways, but data
           and demand do not. Data flows from a positive port to a
           negative one, demand back; reaching a fan by one of its
           outputs, its input is needed, but its other output only if
           something needed reaches it another way. A walk that follows,
           from a node reached, its principal and its negative ports,
           never its positive auxiliary ones, marks what demand could
           need, a subset of what is connected. The principal is followed
           whatever its polarity because a node's auxiliary ports gain
           their values only by its principal's interaction: a function
           reached by its argument (a variable used outside its body,
           which a net need not exclude) must keep what it meets. What
           the walk does not mark is dead though connected: the other
           branch of a fan whose consumer leads nowhere, an application
           waiting on its function whose result is erased (an eraser on
           an application's result, or a function's argument, makes no
           event, so today's cascade stops there), and all they alone
           hold. The sweep frees it, and where a freed node faced a
           marked node's positive auxiliary port puts a consuming eraser
           there (whose event, on a fan, makes it linear): meant to come
           to what erasing the dead part would, all of it at once, even
           where a cascade stops, and without its interactions. To weigh: how much more it frees,
           measured first by marking both ways in one collection and
           counting the difference; the sweep's added work at the
           boundary, only where it frees; a port polarity table in the
           kernel; and a proof that freeing what the walk leaves unmarked
           keeps the interface's value (a structural law, the patched net
           wired and polarized, comes first). A walk this way would also
           free dead structure where today's collections wait for an
           eval a whole cycle later (the maintainer, hoping it works out,
           2026-11-02).
           - `heap-strategies.erasure.load.cycle.walk.directed.census` —
             built 2026-11-02 — what the directed walk would mark, counted
             at every collection of the benchmark's cases, before it (on
             branch `gc-census`, 64a3daf: the walk's ports a generated
             table, `KR.kind_follow`, from `R.port_pol`; `KN.reach_dir`;
             the counts in header words no event uses; store run 166).
             Over 317 collections in 102 cases: 581,678 nodes reached,
             515,299 live after today's collections, 497,853 marked by the
             directed walk. It marks fewer than today keeps in 52 cases
             and more in 39, where today's eval frees what is needed but
             doomed: voids flowing forward from a providing eraser, which
             a walk back from the interface cannot see, and rewrites
             within the needed part; a directed design keeps the eval for
             those. Of the nodes live after today's collections, 30,259
             are unmarked by the directed walk: consuming erasers 60%,
             functions 13%, applications 9%, level controls 14%, fans the
             rest. But 16,890 of them are links into marked nodes, each
             needing a consuming eraser after a directed sweep, and most
             already are one, an unused variable's eraser on a needed
             function, say. The net gain, some 13,369 nodes (2.6% of what
             today keeps), falls to 37 cases, none losing: `loop-fix-64`
             with labels 29% of its live nodes, `mixin-late` unfused 25%,
             `list-length` and `search-count` with labels about 20%,
             `costly-6` unfused 13% (1,014 nodes for 7 erasers), others
             10% to 12%. A snapshot of today's runs: a directed design's
             runs diverge, its nets smaller sooner, and the census sees
             nothing of the erasure cascades it would no longer run, 96% of
             today's collection interactions.
           - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds`
             — active — the maintainer's (2026-11-02): a dead variant
             of a kind for each positive auxiliary port, so that the
             sweep, finding a marked node's output facing what it frees,
             rewrites the node's kind rather than making an eraser, and
             no event is wanted. A variant matters only where the node
             keeps another live port: a function with its argument dead
             (a variable unused, new) and a copy with one output dead
             (the linear copies, already kinds). A node whose one output
             is dead is dead whole and is freed, unless something keeps
             it live by its principal (`.dataflow`): then an application
             kept only to bind, an operator (the dead operator, already a
             kind), and a consumer left with nothing to provide, which is
             an eraser. With erasers on the boundary rewritten into
             kinds, the census's directed walk alone keeps 497,853 nodes
             where today's collections keep 515,299 (3.4% fewer) with no
             eval at all; per case 52 fewer, 39 more (where today's eval
             frees doomed nodes the walk must keep: voids flowing
             forward, rewrites within what is needed), 11 alike. The
             cost: kinds and their rules, which the model would derive as
             it derives the linear fans', the laws over every kind then
             covering them. The maintainer (2026-11-02), on the directed
             sweep's erasers (`.dataflow.walk`): make no eraser node, nor
             turn a node into one; have a kind of no allocation for
             every fused eraser. The directed walk enters a node by an
             output, so a kept node has one live output, and a boundary
             lies only at a node with two: a copy (the linear copies) and
             a function, by its variable (unused, new) or, reached by its
             variable alone, by its principal (`.dataflow.walk`: its
             erasure voids the variable and erases the body, events on
             the merge and the copy that copying made).
             - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.census`
               — built 2026-11-02 — the erasers the directed sweep made,
               over the benchmark's 154 rows (scratch builds counting them
               in the net's errors word): 20,063, at a function's variable
               10,664 (53%), a copy's output 5,574 (28%), a function's
               principal, the function reached by its variable alone,
               3,825 (19%), nowhere else. Of those functions, 3,529 (92%)
               sit between the fans copying made, a copy's output feeding
               their result and their variable a merge's input.
             - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.copy`
               — built 2026-11-02 — the sweep makes a copy whose output it
               frees the linear copy keeping its other side, in place, the
               fan's identity kept, counted as the event an eraser there
               makes (`lin.drop`).
             - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.copied`
               — built 2026-11-02 — a function reached by its variable
               alone, between the fans copying made, erased in place: both
               fans made linear and the function freed, counted as its
               erasure and the two events after it. Elsewhere it keeps the
               eraser and the eval. With `.copy` (gcbench runs 180, main,
               and 181): collecting 0.27% over plain demand against 0.65%,
               capacities and collections' interactions the same; 52 cases
               better, 1 worse (`pow-2-12` with labels, +0.1% of plain), 49
               alike; `loop-toggle-1024` with levels from 16.8% over plain
               demand to 4.5%. `list-length` and `search-count` with
               labels stay some 25% over: their 8 and 21 dead copies, none
               between fans, are erased by the eval, whose cascade takes
               the interpreted table, some 10% of the run (`.walk.loops`).
               The library and 3,600 random terms (`dcterms.sh`) pass. An
               identity's copy, its result its own variable, never comes
               here: the walk reaches it by its principal or not at all.
             - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.fn`
               — built 2026-11-02 — a function with its variable dead, a
               kind of its own (`KFnD`, code 17, `[+ fn, - result]`), for
               the erasers at a function's variable, 53% of them: a fused
               kind (`R.lf.full` a function, `R.ex.dead` its port 2, a
               consuming eraser there), its rules derived as the linear
               fans' are, each fused side's eraser its own
               (`R.ex.eraser`), a function whose variable meets an eraser
               becoming one in the derivation's marking (`R.lf.mark2`); an
               application tests its level as a function's (`R.test_eq`,
               `N.rule_test`, the kernel's test through `R.lf.full`). Its
               rewrites: an application's argument erased in the
               application's slot, a copy making two, an eraser erasing the
               body, a control crossing, the linear copies; no other
               pair's rewrite changed. The sweep makes a kept function
               whose variable it frees one in place (`fnd.make`). Laws:
               `linear_as_components` now holds for it against every
               partner and test; every law split by kind gained its arm
               (367, the function's copied, `free_arity`'s arity mended);
               the derived eraser put on the result instead of the
               variable fails `rules_polarized`. Against main (gcbench
               runs 181 and 184): collecting 0.99% below plain demand,
               against 0.27% above; capacity 505,216 nodes against
               542,080 (6.8% less), 291 collections against 307; 82 cases
               better, none worse, 20 alike; an application meets a
               function with its variable dead 4,020 times in 85 cases (a
               scratch count). The library and 3,600 random terms pass.
               With `.copy` and `.copied`, the sweep makes an eraser only
               for a function reached by its variable alone away from the
               fans copying made, 296 over the benchmark, 1.5% of the
               erasers it made before. Lowering may make one for an unused
               variable (`.lowering`), so that plain demand has them too.
               Workloads that never meet the kind move with the larger
               generated dispatch, six more pairs and an eighteenth kind
               (store run 185 against 183, k 18): eager succ and lvl
               +1.3% to +2.2% forced inline, -0.2% to -0.3% in the default
               build, +0.3% to +0.5% profile-guided; plain demand -0.3% to
               +0.7%. Layout, not work: none of them makes the new kind.
             - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links`
               — active — the maintainer (2026-11-02, unsure it is a
               good one): static links standing for `EraP` and `EraN`
               instead of nodes, a port facing one being erased or void
               without a node there. Depends on how much the kinds
               bring: a kind is dispatched on by the rules, a link would
               be tested where a port is read, as nil is. The maintainer
               (2026-11-02): would they take the remaining 1.5% of the
               sweep's erasers (the dead copies away from the fans
               copying made, `.copied`), and help or hurt overall? An
               experiment to tell. The plan, as the maintainer revised it
               (2026-11-02): a reference whose port bits are 3, the value
               no port has, is static, standing for a leaf in the one link
               word of the port it faces; a few low bits of type after
               them, no kind or form encoded at the cost of a subspace,
               each eraser one value (`netdata-refs`, in
               [`NetData_2026-11-02.md`](NetData_2026-11-02.md), for the
               layout); a static meeting a rewrite first made a node
               (materialized), native rewrites after; data table entries
               a step of their own (`.static.table`).
               - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.read`
                 — built 2026-11-03, refined the same day — every reader
                 of a link made static-safe, statics made by the sweep's
                 boundary alone. One departure from the plan, for a reason
                 found on the way: no static is materialized. A node made
                 for one in a collection's eval comes off the free list
                 its count runs down to (P.freed_since stops at the head
                 the sweep left, which a materialization may take), so a
                 node meeting a static eraser at its principal is erased
                 natively (KN.static_erase): freed, its payload dropped,
                 each auxiliary port's peer given a static eraser,
                 consuming at an input's producer and providing at an
                 output's consumer, no node made; law `static_erasure`
                 proves that this is the table's rule for every kind, or
                 the pair is stuck for both tests (the root's), and the
                 kernel leaves it. The readers: a link from a rewrite to
                 an external peer tests it before writing back (P.link_x,
                 P.link_xx, in the generated rewrites, the interpreter,
                 fusion and peeling); a pair's partner tested where an
                 eager family interacts (KN.interact.f) and where demand's
                 descent meets it (wk.c, in the test nil already had; an
                 erasure there goes back down the path as a rewrite does);
                 a static counted principal in a pair's note (P.pri), the
                 generated notes putting a new node's end first and, of
                 two external peers, the one not static (P.site); the
                 events looking from the end facing a static (P.site in
                 the generated sites, the worklist's ws.add), a static B
                 read from its reference (P.st_hd) and never freed
                 (P.free_b); fusion's and reachability's nil tests
                 widened; the collection's walk reading a static as
                 marked (lw.mw, by its port bits, as nil was) and noting
                 the pair a node makes with one at its principal, but not
                 a static void's event at an auxiliary input, which demand
                 meets where it gets there, so that notes stay one a node
                 within the walk's array; the sweep passing statics by;
                 the audit accepting the two erasers; the interface's
                 value none facing one; the interpreter's test for the
                 redex's own ports (KN.partner) knowing a static from a
                 port. The first form (merged at 9b9ea11) chose the
                 erasers' values so that a write-back landed on a scratch
                 word of the header, moving the free list's head, and let
                 two statics meeting vanish uncounted. The maintainer
                 (2026-11-03, `static-links-count-as-nodes`): numbering
                 for a scratch word won't generalize to immediates and
                 packed pointers and gives statics a location they lack;
                 statics count as the nodes they stand for. Refined:
                 plain codes (an eraser's kind code in the constants'
                 class), the header as before, write-backs tested, two
                 statics meeting noted as a pair where a strategy keeps
                 pairs, a static standing for it on the stack (P.note,
                 KN.static_meet), and in native erasure where a peer is a
                 static or the node's two ports are joined; demand, which
                 notes nothing, leaves them uncounted, as it leaves a pair
                 of allocated erasers off its path, which a collection
                 sweeps unreduced. Statics made: where the sweep gave a
                 kept output an eraser, in valid nets only a function's
                 principal reached by its variable alone away from the
                 fans copying made (`.copied`'s 1.5%); the eval erases the
                 function natively, and the erasure cascades through
                 statics with no node made (an instrumented build, one
                 random set: 1,169 static erasures under collecting
                 demand in 5 terms, 1,268 under stress in 23). The
                 library and 3,600 random terms pass, unchanged on plain,
                 collecting and stress demand. Measured against main
                 (gcbench runs 195 and 209): collecting 0.08% below plain
                 demand against 0.06%; 27 cases better, 16 worse (at most
                 0.51% of plain, the walk's longer mark index on large
                 walks: pow-2-12, loop-fix-64), 61 alike; capacity and
                 every case's interactions in collections as on main.
                 Workloads holding no static (count_builds runs 197 and
                 208, k 18): plain demand +0.03% to +1.63%, +0.38% to
                 +0.56% in the default build; eager +1.2% to +4.9%. Of
                 that (ablations 199 to 201, the first form's runs 198,
                 202 and 203): the write-back tests 0.75 points of plain
                 demand and 1.3 to 2.1 of eager, the partner's test at
                 each pair 1.2 to 1.9 of eager; the price of static links
                 for every rewrite, whether or not a net holds any.
               - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.load`
                 — built 2026-11-03 — the loader makes the templates'
                 erasers and voids static (KN.load's ld.statics): each
                 eraser whose principal faces a port that is no eraser's
                 becomes a static in that port's link word, its node
                 freed; two erasers facing stay two nodes, a pair every
                 strategy finds and counts as it finds any. Lowering makes
                 no eraser or void since `.lowering`, so only the
                 library's hand-written nets hold any: the step changes
                 nothing the benchmark measures (gcbench run 210 against
                 209: every case's interactions and capacity alike; 11
                 lowered cases a little faster, layout; count_builds run
                 211 against 208, no workload moved but by layout, at
                 most 0.55%), and its worth is that the library now runs
                 statics through every strategy: eager, two stacks, the
                 profile, the erasure modes, the interpreted table. That
                 found two faults, both fixed: native erasure noted the
                 absent peers of a node of fewer than three ports, nil,
                 which reads as static, as two statics meeting, counted
                 by the profile (2 logical interactions too many on six
                 entries; latent on main, where the collection's eval left
                 them uncollected); and the interpreted table looked for
                 events at a static external peer rather than at the end
                 the rewrite linked it to, as the generated rewrites do
                 (KN.wd.sites, carried in the table's result). The library
                 passes with its logical interactions as with allocated
                 erasers, the interpreted and generated rewrites making
                 the same interactions and events. Where erasers are made
                 is the rules: in the library's eager profiles 5.1% of the
                 interactions involve one (445,275 of 8,804,291), two
                 erasers meeting 0.8% (`.links.native`).
               - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.meet`
                 — planned — the stats of two statics meeting: a meeting's
                 stack entry holds one static, and the other is taken for
                 the eraser of the other polarity (P.st_other), true only
                 while erasers alone are static. The maintainer's options
                 (2026-11-03): encode the kind pair in the entry, or count
                 the meeting's stats before the stack; and profiles kept
                 in the net's header, so that no count relies on feedback
                 through a strategy's stack. Counters by kind pair in the
                 header, counted where the meeting happens in any
                 strategy, the stack's meeting entries gone; the header
                 may grow by a node (the maintainer, 2026-11-03). Its 28
                 words now: 12 of the net's own (the free list's head,
                 errors, interactions, capacity; the data table's four;
                 the collections' two; the reserve's two) and 16 event
                 counters, one a kind code below 16.
               - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.dead-ports`
                 — planned — on a side branch (the maintainer,
                 2026-11-03): a static eraser at a port is that port's
                 deadness, read from a link word a rewrite reads anyway,
                 so the dead kinds give way to dead ports. The function
                 with its variable dead goes: beta links the argument's
                 producer to the variable's peer, and a static there
                 erases the argument through that link. The linear fans
                 go: a fan's rewrite dispatches on the static bits of its
                 auxiliary links, to the linear rewrite derived as now
                 (the full rule with an eraser attached at the dead port,
                 simplified) but in the full fan's layout. The dead
                 operator becomes a static constant meanwhile
                 (`heap-strategies.erasure.typed` would make it an
                 eraser). Laws restated: a dead port behaves as its
                 components. Changes laws on main and the library's
                 counts: plain demand makes fewer interactions than with
                 allocated erasers where a fan has a dead side, as the
                 linear kinds did with events. In plain demand over the
                 library, 614 fan interactions (0.02%, in 31 cases) meet
                 a static eraser at a fan port: the gain here is
                 simplicity more than speed. The maintainer's aside
                 (2026-11-03): the consuming eraser, the providing one and
                 nil as one value, an eraser's polarity being its port's;
                 all ones names no node, so that no static passes for a
                 redex's own port, and the walk already reads it as
                 marked; what uses nil for a port a node lacks (the
                 events' worklist) then wants a marker of its own, and the
                 audit no longer tells an erased port from a lost link.
               - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.propagate`
                 — planned — the maintainer's design (2026-11-03):
                 erasure events travel through auxiliary ports alone. A
                 node whose last auxiliary is erased (a fan's two sides, a
                 merge's two inputs, a control's other port, an operator's
                 result) is erased at its principal, an eraser of its
                 principal's polarity written to the principal's peer;
                 landing on a principal is an interaction, not an event:
                 eager notes the pair, lazy leaves it until demand reaches
                 it. Each event makes one eraser at most, at the node's
                 one principal, so a chain is linear and needs no stack;
                 specialized by kind and entry port, peeking at most at
                 the other auxiliary. Replaces the events' worklist and
                 their kind changes.
               - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.walk`
                 — planned — the collection's walk back to `.links.read`'s
                 once dead ports leave the sweep no kinds to convert. The
                 sweep frees the dead part in bulk and erases only at the
                 cut, a dead node's inputs facing live outputs (a static
                 pointer among those inputs dropped with it): an eraser on
                 the live side, an event at an auxiliary port, an
                 interaction at a principal, run at the collection. Settled
                 (the maintainer, 2026-11-03): a collection applies erasure
                 interactions, since marking reaches a dead copy of a
                 function through the merge of the copies' variables and
                 cannot tell which branch of a merge is live. The case: a
                 node marked through one output while another faces the
                 dead part; at an auxiliary that is a dead port, the
                 static saying so; at the principal, the node is dead in
                 that context, and only an interaction frees it, its
                 variable voided at the merge, sound by the calculus'
                 sharing in a valid net. It needs a positive principal
                 and a positive auxiliary: of our kinds the function alone
                 (a dead, unmarked function needs nothing: a live
                 consumer of its variable would have marked it). The rule
                 general, by polarity, for a law to pin: the kinds with a
                 positive principal and a positive auxiliary are the
                 function, so that a kind added with two outputs, one its
                 principal, fails the law and its erasure from the
                 principal is reviewed. The sweep finds the case from the
                 dead consumer's input; a static eraser that demand's own
                 rewrite left on such a principal has no dead node facing
                 it, so the walk reads the principal of such a node when
                 it enters by its positive auxiliary (a table generated
                 from the rules), noting the pair for the eval (left
                 unreduced, dead copies kept their fans whole: five cases
                 grew, mixin-chain-16 by 8.7%, gcbench run 212). At write
                 time instead: a function's erasure, an interaction, makes
                 two erasers; its variable's chain is linear and never
                 reaches a positive principal, but its body's eraser may
                 land on another function's principal (a curried body, a
                 copied function), so a complete rule needs a worklist and
                 a partial one leaves the case to the collection anyway.
                 Not pursued: normal evaluation leaves an eraser that
                 lands on a principal to demand (lazy) or notes it
                 (eager).
               - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.native`
                 — active — built 2026-11-03 on branch `links-native`
                 (eaec5cb), unmerged, the maintainer to decide: the rules
                 that make erasers make them static. Every eraser a rule
                 makes faces an external peer, or another of its erasers,
                 and a rule making one makes nothing else (31 rules: 21
                 making one, 10 two; law `erasers_native`, on the branch),
                 so the generator emits such a rule with no node made,
                 both slots freed, a static put in each facing peer's link
                 word (P.put_st), two facing a meeting noted as a pair.
                 Events keep their eraser in the node's own slot, since a
                 pair the node is in keeps its place on a stack by that
                 node. The collection needs statics where it found eraser
                 nodes: a function's or a copy's second output facing a
                 static eraser is the boundary the sweep noted when it
                 freed an eraser's node there (a function reached by its
                 variable alone, its principal facing one, kept its body
                 alive otherwise: five cases grew, mixin-chain-16 by 8.7%,
                 gcbench run 212), so the walk reads that output for
                 nodes of one input (gcbench run 221 against 210):
                 capacity as with allocated erasers, none grown, one
                 shrunk; the collections' interactions 15,634 against
                 15,668; collecting 0.03% over plain demand against 0.12%
                 below, 68 cases worse, 4 better. Noting static voids at
                 auxiliary inputs as events too cost as much and restored
                 nothing (runs 213 to 218; 214 holds no rows); forced
                 inline, the same cost (runs 219, 220). Plain demand over
                 the library: +0.05% (+0.42% forced inline), the
                 interactions alike, 2% to 4% faster on the cases heavy
                 in erasure (search-pairs, mixin-chain-4, list-bind-16), up
                 to 0.2% slower on five. So far, erasers as statics do not
                 pay here: they save little allocation, and the
                 collection pays to find them. Building it found three
                 faults on main's interpreted path, fixed there: its notes
                 dropped two statics meeting; its fans and lifts lost their
                 form (`pay`: a fan made by the table, in a net without
                 levels, then failed to pair with one made at load by the
                 same site, which the generated rewrites never did); and
                 the identity's test and the choice of where fusion is
                 tried read a static whose value names a node's index (an
                 eraser's kind code, nodes 447 and 511) as one of the
                 redex's own ports (KN.own). A static of another kind,
                 data immediates (`.static`), would want rewrites of its
                 own, its payload from the reference.
               - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.kinds`
                 — planned — what the kinds that capture an erased
                 auxiliary buy over a static eraser at that port (the
                 maintainer, 2026-11-02): builds where the function with
                 its variable dead, and even the linear fans, give way to
                 their full kind with a static eraser, measured against
                 the kinds, toward a hybrid kept for speed and
                 simplicity.
             - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.static`
               — contingent on `netdata-refs` — the maintainer (2026-11-02): immediate data
               as static nodes too, a reference whose port field holds
               the unused fourth value (3) standing for a node
               interpreted locally, the value in the reference, perhaps
               serving better on average than distinct kinds and forms;
               and the data table using such immediates instead of nodes
               of its own. To weigh: what a static reference saves (a
               node, its loads) against what every port read then tests,
               where kinds now dispatch.
               - `heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.static.table`
                 — contingent on `netdata-table` — the data table's
                 entries referenced by packed pointers rather than by data
                 nodes, a step of its own within the experiment (the
                 maintainer, 2026-11-02).
           - `heap-strategies.erasure.load.cycle.walk.directed.dataflow` —
             active — which closure. Following only negative ports,
             data's flow reversed, a dead node stays dead: no rewrite of
             the live part links a dead output into a live input, since a
             live redex's peers in the dead part are dead inputs, and
             polarity links an input only to an output. Following
             principals too keeps whatever a live node will interact
             with, as demand would reach it (a function reached by its
             argument keeps its applier), but loses that invariant: after
             a function is copied, each copy's variable feeds the shared
             body's merge, so every copy's applier is kept, dead or not,
             and a dead node can be drawn back in. Neither is sound by
             structure alone for any net: freeing what is unmarked cuts
             links whose values only contexts (fan levels) keep apart, so
             soundness rests on the calculus's sharing, as fan
             linearization by an erased output already does. Following
             only negative ports further assumes every variable is used
             within its binder's body, per sharing context, which glam's
             lowering gives and a net written out by hand need not (the
             library holds some). To measure: the census again without
             principals, and the library's outcomes.

             Measured (the maintainer: is demand's own walk, entering a
             node by an auxiliary port and leaving by its principal,
             consistent with the closure? 2026-11-02). Demand's walk
             ignores polarity. From the interface each step leaves a node
             by a negative principal for its producer, entering the next
             by an output; a step forward, from a positive principal to
             its consumer, first needs a node with a positive principal
             entered by another output, which only a function has: demand
             entering a function by its argument, a variable demanded
             before its binder applies (extrusion), then going on forward
             through what has its output at its principal. A build of
             demand stopping there (branch `gc-forward`, aa05f19) stops in
             3 of the library's 153 cases, the hand-written
             `ap-dead-extruded`, `ap-self-extruded` and
             `vicious-circle-live`, written for the extrusion the
             `interaction_net` escape hatch allows (the first recording a
             bug of this very kind: an event erasing a dead application's
             function, so that the extruded variable read an error), and
             in none of 1,800 random terms (the differential test, 100 a
             set) nor any term-built case (store run 167). So following
             only negative ports would free what demand steps onto in
             those three: inconsistent with the escape hatch. Following
             principals as well is closed under demand's own step, so
             consistent with it, and differs from following negative
             ports only where a walk from the interface reaches a node not
             by its principal and that principal is positive: a function
             reached by its argument, and the forward chain from there.
             Where demand takes no forward step, as in every term-built
             net measured, its walk stays within the negative ports'
             closure, in which a dead node stays dead, so that what it
             leaves unmarked demand never reaches, now or later: pruning
             it is invisible to demand, its rewrites the same step for
             step (an eraser at each boundary; or the boundary's kinds
             rewritten, as the events are, law `events_as_components`).
             What following principals costs there: the census without
             principals (branch `gc-census-pd`, b6329dc) marks 454,650
             nodes against 497,853 and frees some 46,149 more than today
             (9.0% of what today keeps, in 56 cases) against 13,369 (2.6%,
             37 cases), the difference in dead appliers of copied
             functions (`loop-fix-64` with labels 8,866 nodes more,
             `loop-junk-1024` and `loop-toggle-1024` unfused some 3,200
             each). The maintainer's to choose: keep extrusion and follow
             principals; or refuse it, `interaction_net` treating a
             variable used outside its function's body as an obvious error
             (`net-obvious-errors`) and demand reporting a forward step as
             it reports a cycle, and follow only negative ports; or both
             closures, by whether a net may extrude.

             The maintainer (2026-11-02): an acceptable structural
             constraint on valid nets, if (1) easy to analyze statically
             and explain, and (2) `interaction_net` still bypasses lambda
             calculus's tree-structured dataflow. (1): a walk back from the
             exposed port finds only an orphan read, a variable read while
             its function is never applied; the rule wanted is scoping on
             the graph, every live use of a function's argument within its
             body, the part of the net feeding its result: on the graph of
             ports, an output needing its node's inputs and an input the
             output it is linked to, the function's result port dominates
             its argument port from the exposed port, as a definition
             dominates its uses in SSA. A dominator tree, near linear; a
             prototype (`spike/tools/scope_check.py` on branch
             `gc-scope-check`, fea45d8) flags exactly the three extrusion
             entries of the library's 153 cases and none of 5,400 random
             nets (200 terms, three endings, three seeds, lowered three
             ways), as demand's forward steps did. (2): only a function's
             argument is constrained, since only a function has a positive
             principal and another output; every static wiring stays,
             graphs of any shape with copies, results and operators wired
             to any consumer, a function's body reading any producer in the
             net (free variables), cycles of data (`r = f r`). What goes is
             the scopeless binder: a function value used as a write-once
             channel, its application by opaque code sending the argument
             to wherever the variable is read, as for a callback reporting
             to its creator, or an early return. If wanted, it could return
             as a kind of its own with its own edge for the collection
             (reading it keeps its writer's flow), the rest following only
             negative ports. Scoping holds of a net as built; after a
             function is copied, the copies share a body, and a copy's
             argument is then dominated by its body only per sharing
             context, not by structure, so demand would report a forward
             step as it reports a cycle: a valid net never takes one, and
             one that did would be reported the same, pruned or not, since
             demand's walk until then stays within what both keep.

             The maintainer (2026-11-02): "Alright, I'm convinced. Let's do
             this." Scoping is a rule (`net-scoped-arguments`, in
             `docs/Design.md`, Interaction Nets), and the collection
             follows only negative ports.
             - `heap-strategies.erasure.load.cycle.walk.directed.dataflow.check`
               — built 2026-11-02 — the check where nets are made until
               glam's construction exists: `polarity.unscoped` (the
               prototype's dominators, Cooper, Harvey and Kennedy's
               iteration), which `library.py` runs on every case, failing
               one flagged unless it expects `unscoped VALUE`: demand,
               collecting or not, reports it, and the full reductions,
               refusing nothing, reach VALUE. The three extrusion entries
               expect that, their outcomes before in their `why` (the
               first's bug guarded since by law `events_erase_last`), and
               `copy-extruded` joins them: the variable copied, one copy
               the body and one the root's, found by dominance, not at the
               root, which is all the three exercise. Of the library's 154
               cases those four are flagged, and none of `polarity.py`'s
               5,400 random nets. The check is stricter than demand: a
               variable read outside its body only after its function is
               applied (the root adding the function's result to the
               variable, say) is refused, though demand never steps
               forward there. The library's expectation for such nets
               (`unscoped VALUE`, the full reductions' values still
               checked) the maintainer accepts until we are confident in
               the static checks and that invalid nets are indeed refused
               (2026-11-02).
             - `heap-strategies.erasure.load.cycle.walk.directed.dataflow.report`
               — built 2026-11-02 — demand stops, in a state of its own
               (7, `unscoped`, among the net's outcomes beside a cycle),
               where it would enter a node by an auxiliary port whose
               principal is positive: before each push, in the descent
               (`dn.step.go`) and where the array grows (`wk.into`), a
               read of the node's header and its kind's polarity. Stopping
               there kept the walk within what the inputs-only collection
               keeps until the report; the maintainer accepted a later one
               (`.report.cost`). The cost, on plain demand at k 18 (store runs
               168, main, and 169; the eager workloads unchanged): succ
               +1.5% in the default build, +2.6% profile-guided, +4.3%
               forced inline, +4.4% both; lvl +1.6%, +2.7%, +4.9%, +5.0%.
               The descent's loop goes from 23 instructions a push to 35
               in the forced-inline build: the header's load, the kind's
               range check and bit test, and clang computing the loop's
               condition without branches where it branched on each
               part. Tried, default and forced inline, succ and lvl (spot
               runs 171 to 173, branches `gc-scoped-mask`, `-p2`,
               `-fold`): the kinds as a constant mask, +2.3% to +6.6%;
               the header read only for an entry by port 2, the only
               positive auxiliary port a function has, +1.1% to +4.4%;
               the polarity folded into the descent's condition, the
               stop reported by `wk.into`, +3.4% to +3.8%. Kept the
               plain check, generic over kinds, until `.report.cost` moved
               it to the pairs.
               - `heap-strategies.erasure.load.cycle.walk.directed.dataflow.report.void`
                 — built 2026-11-02 — the maintainer chose C (2026-11-02,
                 no performance hit expected): demand finding a void at the
                 interface stops in a state of its own, 8, a void
                 (`net-void-demanded`), one test where demand reaches the
                 interface: no change in the four builds (store run 179
                 against 178). The library gains a void node (`void`, `EraP`,
                 the row format's tag 13) and the expectation `void`, its
                 entries `void-demanded` and `void-applied`. Before:
                 a void reaching the interface reported as a
                 variable used outside its body, state 7: built 2026-11-02
                 on the claim that a void arises only as an erased
                 function's variable (`EraN` meeting `Fn`), then reverted
                 the same day. The maintainer (2026-11-02), uncertain: a
                 user may wire a `.copy 0` port to a negative port,
                 supplying a void directly; presenting a void at the
                 interface as an error would make such a void an error in
                 general, which wants a proper discussion, not a judgement
                 in passing. The options, for that discussion:
                 - A, as now: the interface facing a void is done with no
                   value, as facing a function is, and `net_arity` takes a
                   non-data normal form for an error already. For: no new
                   outcome, a user's void a value like any other. Against:
                   nothing says where a void came from; and on a refused
                   net, collecting demand, which may erase a function
                   reached by its variable alone (`.walk`), can end done
                   where plain demand reports the variable (accepted for
                   refused nets, the maintainer, 2026-11-02).
                 - B, reverted: a void at the interface reported as a
                   variable used outside its body. For: plain and
                   collecting demand agree on refused nets, and a void from
                   an erased function is called what it is. Against: wrong
                   for a user's void, unless D refuses those.
                 - C: an outcome of its own, a void demanded. For: says
                   what demand found and no more, a user's void reaching
                   the interface surfacing where it does, not at the
                   bridge. Against: a new outcome; on a refused net plain
                   and collecting demand still end differently, both in
                   error.
                 - D: construction refuses a void supplied directly, a
                   `.copy 0` port wired as an output, so that every void is
                   an erased function's variable and B holds. For: one
                   source of voids, the scoping argument covering them all.
                   Against: no direct way to supply nothing (a placeholder
                   for an argument known to be ignored takes a data value
                   instead), and the copy loses at 0 the mirrored polarity
                   a bind has.
               - `heap-strategies.erasure.load.cycle.walk.directed.dataflow.report.cost`
                 — built 2026-11-02 — the maintainer (2026-11-02): 1.5% to
                 5% is much for a one-time check of a property; check only
                 the active pair, discovering some violations later, and
                 scan the demand path for the earliest one once one is
                 found; ideally the static check would make the dynamic
                 one needless, with a proof (`.proof`). The walk enters
                 every node by an output, so in a valid net its last node
                 meets a pair with a negative principal; the branch that
                 orients the pair (`wk.ori`), taken anyway, now reports a
                 positive one after scanning the path for the earliest node
                 whose principal is positive (`fw.scan`), and a walk ending
                 stuck or in a cycle scans its path too, so that no forward
                 step is hidden behind those outcomes; only the runtime's
                 (fuel, memory) and a need, which resumes, come first. Going
                 forward, the walk may rewrite before reporting:
                 `ap-dead-extruded` reports after one rewrite, the other
                 extrusion entries at once. The descent is as before the
                 push check. Cost, the four builds at k 18 (store run 178):
                 plain demand 4.2% to 5.4% below main before the push check
                 (run 168), 5.6% to 9.4% below main with it (run 177), the
                 eager workloads unchanged. More than the check's own cost
                 came back: the orientation's other branch, which no valid
                 walk takes, was the second caller of the pair's rewrite
                 chain (`nd.go`), which therefore stayed a segment of its
                 own, 7.8% of plain demand's instructions on succ; with one
                 caller it is inlined into the walk's. The library passes;
                 3,600 random terms (`dcterms.sh`, 200 a set) agree on
                 plain, collecting and stress demand, none reported.
                 - `heap-strategies.erasure.load.cycle.walk.directed.dataflow.report.cost.bits`
                   — tentative — deferred until a greater benefit shows (the
                   maintainer, 2026-11-02): it is the remote port's
                   polarity, so a reference moved needs no update, and the
                   Rust bootstrap kept such a bit for its dynamic polarity
                   check, where preservation of polarity was not proved.
                   The maintainer (2026-11-02): a link could
                   record the polarity of the port it references, so that
                   a step's polarity is a test on a word already read.
                   Room: a reference is a node's word and a port, below
                   2^30 (`net-capacity`), so its top two bits are free in
                   a link, though a static (`netdata-refs`) takes the
                   whole word, and the walk tags references in its notes
                   with them, so a reference noted would be masked first;
                   the low two bits are the
                   port, and a reference plus one is its link's word
                   (`P.link`), so no low bit is spare without changing how
                   every link is found. Upkeep: a rewrite's new ports
                   have polarities known when the rewrite is generated, so
                   the generated rewrites set the bit as a constant, and a
                   reference moved keeps its bit, its port unchanged; the
                   loader, the interpreted table, the events (a node
                   re-kinded keeps its ports' polarities, law
                   `fused_polarity`) and the fusions set it from kinds.
                   Uses: demand's forward step seen before any rewrite past
                   it, at no load (each link the descent reads says whether
                   it leads to an input), which would make the report
                   immediate again and plain and collecting demand agree
                   on refused nets; a static eraser (`.dead-kinds.links`)
                   told from a static void by the bit alone; and an audit
                   of polarization, each link's two words holding opposite
                   bits. Not a use: the collection's walk and sweep still
                   read a node's head for its arity, a two-port node's
                   word 3 holding its payload. Against: a second record of
                   what the kinds already say, which a missed update makes
                   wrong silently, so the wiring audit (`KN.wired_ok`)
                   would check every bit against its port's kind; and
                   every comparison and address made from a reference
                   masks the bit, an and each, or leans on the arrays'
                   indexes wrapping, as the walk's nil does. Worth it with
                   static erasers, or a
                   measured need; to measure first what keeping the bit
                   costs plain demand, expected nothing.
             - `heap-strategies.erasure.load.cycle.walk.directed.dataflow.walk`
               — built 2026-11-02 — the collection following only
               negative ports. The lean walk follows a node's inputs, the
               first and the second by its kind (`KR.kind_dir`, generated
               from `R.walk_first` and `R.walk_second`; law
               `walk_follows_inputs`: they name exactly the inputs, so a
               kind has at most two), entering every node by an output;
               a pair is noted by its negative node, which alone follows
               its principal, and a void facing an input for its event.
               An eraser has no output and is never entered: the sweep
               (`sd.*`), freeing what the walk left unmarked, notes each
               input of a freed node that faces a marked node (only those
               can: a marked node's inputs were all followed), a kept
               output whose consumer goes; after the pass each is given an
               eraser (`bd.go`), its event noted where the output is an
               auxiliary port (a copy's, made linear; a function's
               variable, none), and where it is a principal, a function
               reached by its variable alone, the pair noted for the
               eval. That happens in valid nets: a copy of a function
               whose body copying shared reaches the body by its
               variable, through the merge of the copies' variables,
               while its own consumer is gone, and is dead in its sharing
               context. Left unnoted (gcbench run 175), such copies stay:
               `costly-133` with levels grew from 2,048 nodes to 65,536,
               `costly-124` unfused and `mixin-chain-16` with labels
               doubled. Noted (run 176), erasing one voids its variable
               only in its own context, as the linear fans' events do
               (sound if scoping holds per sharing context: `.proof`);
               where a variable is used outside its body, in a net refused
               when built, the void may reach the interface, read as no
               value (`.report.void`, open). The erasers the sweep makes,
               and the nodes it turns into none, are to go: the maintainer
               (2026-11-02) wants no eraser made, nor a node turned into
               one, but a kind of no allocation for every fused eraser
               (`.dead-kinds`).
               Against main (gcbench runs 174 and 176, 154 cases, outcomes
               all kept): collecting 0.63% over plain demand against
               2.77%; capacity 541,824 nodes against 650,368 (16.7% less),
               none grown and 24 shrunk; 307 collections against 317, their
               interactions 16,365 against 64,224, the cascades of erasers
               no longer run; 72 cases better, 9 worse, 21 alike. The
               worse are the toggling and junk loops (`loop-toggle` and
               `loop-junk` at 64 to 1024, +0.4% to +8.0% of plain demand),
               where the eval's erasures of dead copies cost work and free
               nothing that changes growth; and against run 175,
               `list-length` and `search-count` with labels cost 2.2M and
               2.0M instructions more for some 400 more interactions each,
               the profile showing the interpreted table (`KN.apply_rule`,
               `R.lf_peer`), which takes a redex whose peers include its own
               ports: a dead copy of the identity, a function whose body is
               its variable (law `copy_identity`), erased (`.walk.loops`).
               Random terms (`spike/tools/dcterms.sh`, a build of
               `spike/runmode.bend`, which gains the stress test as mode
               `dcs`): the differential test's 18 sets of 400 terms, on
               plain demand, collecting and under stress, agree on every
               term, the stress test collecting in 376 to 399 of each 400;
               plain demand ended only done or in a cycle. A walk skipping
               the second input (scratch branch `gc-dataflow-mut`) differs
               in 14 to 18 terms of every set of 20, the tool exiting 1.
               The library: 154 cases pass. Cost: plain demand and the
               eager workloads unchanged in the four builds at k 18 (store
               run 177 against 169); collecting on succ, all of it live, 66
               to 70 instructions a node of final capacity at k 14 and 16
               in the default and forced-inline builds, as main's 67 to
               70: the walk reading a node's head before the link it
               follows costs nothing measurable.
               - `heap-strategies.erasure.load.cycle.walk.directed.dataflow.walk.loops`
                 — built 2026-11-02 — generated rewrites for a redex whose
                 peers include its own ports, which the kernel interpreted
                 at some 6,000 instructions a rewrite. Counted over the
                 benchmark (scratch builds, the errors word): 903 such
                 rewrites on plain demand, 941 collecting, in 35 cases,
                 all but a few with labels (`list-sum`, `list-length`,
                 `search-count` some 200 each, 10% of their runs); by pair,
                 a copy meeting the identity 717, an application 169, an
                 eraser 38 collecting, the rest some 20 to 95. The
                 identity, a function whose body is its variable, its
                 ports 1 and 2 wired to each other: A's rule against it
                 with that loop resolved ahead (`R.rule_id`, by
                 `R.loop.resolve`, which joins what a rule links to the two
                 looped peers, a wire with no node vanishing), law
                 `identity_resolved`: it rewrites the looped redex as the
                 full rule does, both by the laws' application (`lf.apply`,
                 resolving the loop as the interpreter does), for every A
                 and test; joining the wrong ends fails it. Generated as
                 any rule is, A's level checks kept, reached by A's kind
                 (`KR.rewrite_id`) from the cold side of the generated
                 dispatch's one test (`KN.go.loop`), where `is_id` finds the
                 pattern. The interpreted table takes the same resolved
                 rule as a plain one (`KN.go.interp.id`): the interpreter
                 had joined the loop after the rule's other links and
                 looked for events at the redex's own, reused, ports, so
                 that with events the two differed (`costly-124` with
                 labels, 3 events against 15); taking the resolved rule
                 both ways, they agree by construction, as plain rules do.
                 Interpreted rewrites over the benchmark: 903 to 20 on
                 plain demand, 941 to 20 collecting. The library passes;
                 the differential test's 3,600 terms as on main (store run
                 190). The benchmark against main (gcbench runs 188 and
                 193, the default build, outcomes the same): `list-length`,
                 `list-sum` and `search-count` with labels 15% to 16%
                 fewer instructions on plain demand, 29% to 30% fewer
                 collecting, `search-pairs` 8%; 86 other cases some 0.5%
                 more, in all plain demand +0.23%, collecting -0.06%. The
                 standard workloads, which take no loop (store run 194
                 against 189): eager -0.5% to -2.5% but +0.2%
                 profile-guided; plain demand -1.2% to -1.3% forced inline,
                 +0.1% to +0.5% in the default and profile-guided builds:
                 layout, the generated file larger. A first dispatch, a
                 three-way choice at every rewrite, cost plain demand 0.4%
                 (run 191); the generated rewrites' one test was kept.
                 - `heap-strategies.erasure.load.cycle.walk.directed.dataflow.walk.loops.rest`
                   — tentative — the maintainer (2026-11-02): to revisit,
                   the redexes with loops the interpreted table still
                   takes, 20 over the benchmark on plain demand and as
                   many collecting, 2 at most a case, in 14 cases with
                   labels (`mixin-once`, `list-sum`, `list-length`,
                   `search-count` among them): which patterns they are,
                   counted as `.walk.loops` counted; `R.loop.resolve` takes
                   any pair of looped peers, so a pattern that matters
                   resolves ahead as the identity's did, a law like
                   `identity_resolved` its check. Also there: the
                   identity's erasure and copy resolved faithfully, an
                   eraser and a void, or a copy and a merge, made to
                   annihilate next, which a normalized rule would not make.
               - `heap-strategies.erasure.load.cycle.walk.directed.dataflow.walk.laws`
                 — tentative — the structure as laws: that the sweep's
                 net is wired and polarized, every kept output facing an
                 input, and that a dead node stays dead, no rewrite of the
                 kept part linking a freed output into a kept input; then
                 that pruning keeps the interface's value, which rests on
                 the sharing calculus (per sharing context), as the linear
                 fans' events do.
             - `heap-strategies.erasure.load.cycle.walk.directed.dataflow.proof`
               — tentative — the maintainer (2026-11-02): can erasing a
               function reached by its variable alone (`.walk`) be proved
               to keep demand's outcome? Ideally the same proof would make
               the dynamic check of `.report` needless, and found turning
               dead operators into erasers (`.stuck`). The lemma all three
               want: in a scoped net, erasing a function whose consumer is
               gone (never to be applied) changes nothing the interface
               can observe. Provable now, by rules and polarities: a dead
               node stays dead (no rewrite of the kept part links a freed
               output into a kept input; every rule links a positive port
               to a negative one), and the sweep's net is wired and
               polarized (`.walk.laws`). Provable with a model of nets and
               of what demand observes, for nets as built: scoping there
               is structural, the function's result dominating every use
               of its variable, so a function never applied has its body,
               uses of its variable and all, unobserved. Not provable
               without a model of sharing: once copying shares a body,
               scoping holds per sharing context, and the claim rests on
               fans keeping contexts apart, the correctness of the levels
               encoding itself (labels are known to fail on some
               self-applications, the library's `wrong` entries). The
               evidence meanwhile: the library and 7,200 random terms, on
               plain, collecting and stress demand, in both encodings.
             - `heap-strategies.erasure.load.cycle.walk.directed.dataflow.stuck`
               — tentative — the maintainer (2026-11-02): revisit
               `fusions-as-components`' "stuck where they are stuck",
               perhaps refining it by who is stuck. A dead operator is
               stuck where an operator is, awaiting its bind; turned into
               an eraser it would erase its input at once. Demand never
               reaches a dead operator, which has no output, so where it
               is stuck nothing observes; what an eraser does beyond it,
               erasing what it faces, a function among them, is `.proof`'s
               lemma. A refinement: a fusion is stuck where its components
               are, as observed from the interface. The directed
               collection already frees dead operators, unmarked.
             - `heap-strategies.erasure.load.cycle.walk.directed.dataflow.dead-ap`
               — tentative — the dead application's event, dropped where a
               function's scope was unknown
               (`heap-strategies.erasure.kernel.exact`; the maintainer,
               2026-10-30: kept as an optimization where it is exact, as at
               lowering where a function's scope is known). With scoping a
               rule, every built net's scopes are known, and the event
               erasing a dead application's function may be exact, per
               sharing context; to weigh against what the directed walk
               frees without it (a dead application, and a function only
               it applies, go unmarked). Restoring it changes law
               `events_erase_last`, the maintainer's to approve.
           - `heap-strategies.erasure.load.cycle.walk.directed.lowering` —
             built 2026-11-02 — erasers fused or applied at lowering (the
             maintainer, 2026-11-02): an unused variable lowered to the
             dead-argument function, a value with one use dead copied
             linearly or not at all, a discarded expression not built.
             Built nets would hold no eraser; erasers would arise only
             from rules, briefly, until the next sweep folds them. The
             spike's lowering (`terms.py`) puts an eraser in one place
             only, an unused variable: it copies a value only for its
             uses and discards no expression it builds. That function is
             now lowered as one with its variable dead (`fnd`, `fndl` in
             the templates, the row format's tags 14 and 15), so that
             lowered nets hold no eraser; the hand-built K combinator of
             EvalSpike's tests keeps its own (`nets.bend`'s `t_k`). The
             loader marks it built without levels as it marks a function
             (`KN.bare_hd`); before it did, an application met it at a
             mismatched level and stuck, in 34 entries with labels. The
             library: values and states unchanged, 56 entries' logical
             interactions fewer (6,807,581 to 6,635,565 over them,
             -2.5%), updated. The differential test, 3,600 terms (store
             runs 186 and 187, main): every correctness column the same.
             The benchmark, its rows lowered anew (gcbench runs 184 and
             188): plain demand 1.38% fewer instructions, 101 cases
             better, none worse, interactions the same; collecting 0.15%
             fewer, capacity 497,024 nodes against 505,216, 84 cases
             better, 4 worse, all with labels: `search-once` and
             `parse-greedy`, now just past the threshold, collect once
             more; `list-sum` and `search-first` send more of their
             collections' rewrites through the interpreted table
             (`.walk.loops`). Measured against each run's own plain
             demand, which now has what only collecting had, collecting
             reads 0.24% over plain demand.
           - `heap-strategies.erasure.load.cycle.walk.directed.eager` —
             tentative — the same collection under eager reduction (the
             maintainer, 2026-11-02), the stack of pairs filtered by the
             marks after the sweep (a pair's two nodes share their fate,
             a principal partner being kept with its partner), the pairs
             a sweep's rewritten kinds make noted. Eager reduction wastes
             most on dead work, which this prunes at each collection, and
             a dead divergent computation that allocates is pruned in
             time; one that never allocates would want a trigger by work.
             Under eager reduction functions are copied early, so the
             merges' conservatism (`.dataflow`) costs more there.
         - `heap-strategies.erasure.load.cycle.buffers` — dropped
           2026-11-01 (the maintainer: not worth pursuing) — the
           collection's arrays kept with the net from one collection
           to the next, whatever the walk: Bend fills a new array at
           eight instructions a word (`docs/BendIssues.md`, "Array
           creation fills word by word"), and a collection makes about
           two words a node of capacity (the walk's one array, which the
           eval's queue takes over), so perhaps 16 of the 82 instructions
           a node on `succ`. With the next Bend's fill (#1928,
           `inline_build.sh` with `NEXT_FILL=1`) a collection costs some
           14 a node less (store run 136; 8 with the worklist walk, run
           134), and what keeping the array would then save is near 2:
           weigh it against that release, as every comparison of resizing
           (the maintainer, 2026-11-01).
       - `heap-strategies.erasure.load.cycle.parts` — built 2026-11-01 —
         a collection's cost by part, each measured by doing it twice and
         counting the instructions added, which keeps every term's
         semantics where removing a part would not (store run 142, main
         at 7a19843, the default build): on `succ`, of 81 to 86
         instructions a node of final capacity, the walk some 39, its
         array's fill some 17, the sweep 11, the chunks 2 at k 16 and 7
         at k 14; on the 16 dropping terms, of their 3.74% over plain
         demand, the walk 25%, its array 9%, the sweep 6%, the chunks
         25%, and the rest, mostly the eval's own interactions (some
         38,500 across them), about 36%. Doing the walk twice changes
         how clang compiles it, so the forced-inline build's parts come
         out larger; the default build's are the ones cited. The walk is
         near what this design allows in Bend: a profile shows each
         array access masking its index for wrapping, two arrays' bases
         reloaded from the stack, the arity's table clamped and o1's
         variable shift. A profile wants a sampling period of 100,000
         instructions or more on runs of a tenth of a second or longer,
         and `perf annotate --asm-raw` (AGENTS.md, "Measuring").
       - `heap-strategies.erasure.load.cycle.sweep-full` — built
         2026-11-01 — the sweep passes a block of 32 nodes whose marks
         are all set: every node in it was reached, so none is free or
         dead. On `succ`, whose nets are nearly all live when collected,
         the sweep's 11 instructions a node fall to almost none.
       - `heap-strategies.erasure.load.cycle.chunks` — built 2026-11-01 —
         chunks a 64th of the capacity are short in small nets (4 steps
         at 256 nodes): the 16 dropping terms run some 12,700 chunks to
         66 collections, and a chunk cost some 590 instructions, each of
         its helpers calling into what may suspend, so that the loop
         crossed five or six segments a chunk, and its matches on
         numbers duplicated the chunk's call in every arm. The loop's
         next move is now planned between moves by helpers that only
         read the net, and the loop makes one call a move (`demand.go`,
         or `collect_cycle`): some 240 instructions a chunk. Every
         library case kept, the same figures as the walk merged (store
         run 140); the plain workloads unchanged in the four builds (run
         141 against 137). With `.sweep-full`, on `succ` 68 to 71
         instructions a node by default and 67 to 70 forced inline,
         against 80 to 86 and 77 to 83, and 53 to 56 and 52 to 54 with
         the next Bend's fill; on the dropping terms 3.03% over plain
         demand (forced inline 2.14%) against 3.74% (3.02%; store run
         142).
         - `heap-strategies.erasure.load.cycle.chunks.budget` — dropped
           2026-11-01, too few collections to pay — a collection's free
           count as the next chunk's budget: its free list holds at least
           the nodes it counted free, less the reserve set aside next,
           which half as many steps cannot exhaust, so the chunk after
           it may run that many steps besides its S. Exact (a collection
           takes no node from below the list's old head) and safe either
           way (a short count only grows the net), but it lengthens one
           chunk a collection, and collections are rare: 0.12 million
           instructions on the dropping terms, about one a node on
           `succ` (store run 142, `nobud` against `dp`).
         - `heap-strategies.erasure.load.cycle.chunks.floor` — built
           2026-11-02, at 16 steps — a floor on a chunk's steps for small
           nets, the reserve twice it (the maintainer asks, 2026-11-02): a 256-node net's chunk is
           4 steps, some 60 instructions a step at 240 a chunk. The
           reserve comes off the free list before each chunk, so a floor
           grows a small net that could not spare it, by one doubling at
           most. Measured (store run 143), floors of 16, 32 and 64 steps
           against none: on the 16 dropping terms 2.96%, 2.91% and 2.69%
           over plain demand against 3.03% (forced inline 2.09%, 2.05%,
           1.83% against 2.14%); on `succ` a node or two fewer at k 14;
           the library's capacities 652,288, 655,744 and 664,320 against
           649,984 (0.4%, 0.9%, 2.2% more), its nets of 256 nodes or
           fewer 55, 51 and 47 of 153 against 57, its collections 318,
           315 and 296 against 332; every case kept. A floor of 64 holds
           128 nodes (2 KB) in reserve. Its cost is a live net's: a frozen
           net is compact, copying only what is reached, so the room
           lasts while a net is reduced or held partial in a cell, and
           many live nets are expected in cells, most waiting on other
           cells (the maintainer, 2026-11-02). A floor of 16 (the
           maintainer's lean: at most 15 instructions a step at 240 a
           chunk, the formula holding from 1024 nodes, 16 KB) is merged;
           64 is a bit much for a net of 128 nodes.
         - `heap-strategies.erasure.load.cycle.chunks.base` — dropped
           2026-11-02, the floor alone kept for simplicity (the
           maintainer: it would change were it moving the needle more) —
           larger chunks at every size, the maintainer's suggestion
           (2026-11-02): a 32nd of the capacity with a reserve of a 16th,
           collecting at 94% full rather than 97%. Measured with the
           floor of 16 (store run 144): the 16 dropping terms counted one
           by one gain on 15 (2.24% over plain demand without the one
           that loses, against 2.82% with the floor alone), but a run
           that ends or blocks between 94% and 97% full now collects once
           more, and that collection, finding under half the net free,
           doubles it: `loop-junk-1024` unfused grows to 65,536 nodes and
           its collections' interactions go from 191 to 8,393, all 16 at
           4.25% against 2.96%; the library's capacities 7.6% more (five
           nets of 1,024 to 32,768 nodes doubled). A net in a cell that
           blocks is at such an end. A variant keeps the trigger at 97%:
           the reserve a 32nd too, so that it covers a chunk's steps at
           one node a step rather than two, a chunk that takes more after
           the reserve growing the net as plain demand would (safe, only
           a growth without a collection). On the library it grows no
           net beyond the floor's nine (capacities 652,288, as the floor
           alone), with fewer collections and their interactions (316 and
           109,910 against 318 and 113,412); on the dropping terms 2.36%
           over plain demand (forced inline 1.61%) against 2.96% (2.09%)
           with the floor alone. Its guarantee is a typical chunk's, not
           the worst's: the maintainer's to weigh.
           - `heap-strategies.erasure.load.cycle.chunks.finish` —
             dropped 2026-11-02 (the maintainer: not counting a linked
             list again and again to put off a collection when the net
             is nearly full) — the maintainer's alternative
             (2026-11-02): large
             chunks kept safe, a 32nd with a reserve of a 16th, and where
             a chunk ends with the reserve taken, finishing chunks rather
             than the collection at once, each as long as the free list
             still covers at two nodes a step (counted by walking it, a
             chunk's worth at most), until it covers fewer than 16 steps.
             The collection then comes with the net all but full,
             whatever the reserve's size, which sets only the chunks'
             length. Prototyped on branch `gc-chunk-finish` (9910895):
             every library case kept; the library's capacities 648,192,
             the least of any setting (two nets stay at 2,048 nodes where
             the floor alone grows them to 4,096; none grows), 314
             collections; the dropping terms 3.05% over plain demand
             together (forced inline 2.23%), 2.89% without
             `loop-junk-1024` unfused, against 2.94% and 2.82% with the
             floor alone; `succ` 68 to 70 instructions a node (store run
             145). So the gains of a 16th's reserve on 15 dropping terms
             came from collecting at 94%, not from the halved chunks
             (some 6,000 chunks fewer, about 0.2 points): where
             collections fall shifts a term's cost by more than that,
             either way. What finishing buys is space, never growing
             before the net is full, and a reserve that no longer moves
             the trigger.
       - `heap-strategies.erasure.load.cycle.bench` — built 2026-11-02 —
         the collecting demand's benchmark (`spike/tools/gcbench.py`):
         every library case as a net, run by a build of
         `spike/runmode.bend` on plain and collecting demand, counted and
         stored (table `gcbench`), about 6 seconds for the 153 cases. Two
         runs compare case by case: how many of the cases that collect
         the second improves, worsens or leaves alike (a change counting
         past 2,000 instructions or 0.1% of plain demand), the totals,
         capacities grown and shrunk, the exceptions each with what
         changed, and any case whose collecting outcome differs from
         plain demand's. The 16 dropping terms, too few, had let the
         timing of collections pass for a design's effect (`.chunks.base`).
         The maintainer asks for such counts, improved and worsened, as
         a matter of course, with the exceptions examined (2026-11-02;
         AGENTS.md, "Measuring"). Main with the floor of 16: 102 of the
         153 cases collect, 3.23% over plain demand (forced inline
         2.56%), 652,288 nodes of capacity (store runs 146, 147).
         - `heap-strategies.erasure.load.cycle.bench.corpus` — tentative
           — the library is a set of nets kept for what they exercise,
           not a sample of programs, so a finding over it rules a
           hypothesis out more surely than in: that data copies scarcely
           happen here says nothing of programs that copy data often
           (the maintainer, 2026-11-02). Broader populations would help:
           the differential test's random terms (`terms.py`), and larger
           programs once there are any; and each negative finding read
           against why it holds, by logic, before it is relied on.
       - `heap-strategies.erasure.load.cycle.eval-need` — built
         2026-11-02 — what work a collection's eval should do, and how
         much (the maintainer: does a data copy help, does beta, is fuel
         needed or are recognized prunings once enough, 2026-11-02).
         Running the eval only where a sweep falls short was set aside:
         it would not cut dead subnets off before the collections that
         sweep them. Measured over the benchmark against main (store
         runs 146 and 148 to 162), each variant changing one thing:

             variant                 over plain  capacity   coll. itrs   cases better/worse
             main                    3.23%       652,288    113,412
             no eval, sweep only     3.20%       895,488    0            68/27, 29 grown
             noted events only       3.09%       892,928    0            71/26, 28 grown
             no noted events         3.24%       652,032    114,021      7/5
             noted pairs once        2.99%       873,984    6,147        74/20, 21 grown
             no data copies          3.23%       652,288    113,380      0/0
             no beta                 3.14%       650,496    109,971      16/6
             no fan annihilations    3.20%       654,592    110,744      24/3, 3 grown
             erasures alone          2.72%       652,800    60,604       71/8, 4 grown

         The cascades carry the memory (the noted pairs once keep 5% of
         the interactions and lose it); data copies scarcely happen (32
         in the library); beta and annihilations each help some nets and
         cost others. Logically: a sweep frees only what is cut off from
         the interface, and links run both ways, so a dead computation
         whose result an eraser faces stays reachable through its inputs
         until erasures consume it. The rules a collection may run fall
         in three: those that leave fewer nodes (annihilations, beta at
         one level, erasers meeting each other or data, an eraser on a
         node of two ports), those that turn a node of three ports into
         two erasers, and those that move controls or linear fans past
         each other without shrinking anything, which can only help by
         unblocking a later shrinking rewrite. A measure tells them apart
         (`.shrink`). A collection's interactions beyond plain demand's
         are work demand never needed, paid for only by the memory they
         free: in main 75,327 of 113,412, the rest demand's own work done
         early.
       - `heap-strategies.erasure.load.cycle.shrink` — built 2026-11-02
         — a collection rewrites only where the pair's rule leaves fewer
         ports than the pair had (the generator's `collect_r`, by
         `R.ports_of`), as an event does (law `events_shrink`): every
         rewrite and event of a collection then lowers the net's ports,
         so its cascade ends within them. Erasures, annihilations, beta
         at one level and copies of data stay; controls passing, and
         linear fans meeting at different levels, which leave as many
         ports as they take, are left to demand; `Lift-LiftC` shrinks at
         one level only and no header test tells its forms apart, so the
         generator now collects neither form of such a pair rather than
         stopping (it named the missing test). Over the benchmark: 52 of
         102 cases better, none worse, one net 2,048 nodes rather than
         4,096, 2.79% over plain demand against 3.23%, the collections'
         interactions 64,224 against 113,412, 96% of them beyond plain
         demand's (store run 163); forced inline 40 better and 5 worse,
         2.23% against 2.56% (run 164), the worse ones control passing
         that demand now does itself, the same interactions in all
         (`costly-124`: 13,063 against 13,062), costlier there in that
         build; the plain workloads unchanged in the four builds (run
         165 against 141). Without the noted events, though, it loses
         (`costly-133` with levels grows to 65,536 nodes): the events now
         do what the controls' passing had done (run 162).
         - `heap-strategies.erasure.load.cycle.shrink.beta` — tentative —
           whether beta belongs: without it, 18 cases better and 5 worse
           against `.shrink`, `list-sum` with labels 2,048 nodes rather
           than 4,096 and `mixin-chain-16` with labels 15% dearer, one
           collection more (run 161); of beta's some 3,300 interactions,
           about 1,900 demand's own done early, 1,400 work nobody needed.
           Beta shrinks the net, but it is evaluation: what it exposes
           runs too.
         - `heap-strategies.erasure.load.cycle.shrink.fuel` — tentative —
           the eval's fuel (twice the capacity in pairs looked at) no
           longer needed for the cascade to end, which the ports bound;
           it could still bind (each rewrite may note pairs to look at),
           so whether to keep it as a bound on a collection's work, or
           drop it, is the maintainer's.
         - `heap-strategies.erasure.load.cycle.shrink.untested` —
           tentative — pairs collectable in one variant only that no
           header test tells apart are left uncollected, each named in
           the generator's `collect_untested`, any other stopping the
           generator by naming the test it lacks, so that none is
           forgotten for want of a test (the maintainer, 2026-11-02). One
           so far: a level control meeting its co-control, which
           annihilates where their indexes agree, an agreement read from
           their payloads after peeling a fused run (`P.Pl`), which the
           collection's header test cannot see; collecting it needs the
           payloads read, and the peel's test without its rewrite.
         - `heap-strategies.erasure.load.cycle.shrink.ctl-cost` — planned
           — control passing that collections no longer do, demand now
           doing it, costs more in the forced-inline build: `costly-124`
           with the same interactions, some 0.2 million instructions
           dearer there, cheaper in the default build (store runs 163,
           164). A signal to look at control passing's cost on demand's
           path (the maintainer, 2026-11-02).
         - `heap-strategies.erasure.load.cycle.shrink.copy` — dropped
           2026-11-02 (the maintainer: data copied is 8 bytes at most,
           the table's resizing aside, and a copy splits the fan, which
           would otherwise hold garbage through an auxiliary port until
           the directed walk, `.walk.directed`, cuts it) — a full copy
           meeting data passes the ports test (four ports to two) but
           frees no node, its two nodes becoming two, and table
           data gains an entry, a value duplicated, perhaps a large one:
           in a collection it is at best demand's work done early, at
           worst a copy nobody needed. Not so in the sample (32 in the
           library, none mattering), but by the accounting. Counting
           nodes rather than ports leaves it out: fewer nodes other than
           erasers and dead operators, or as many and fewer nodes in all,
           keeps every other collected rule and still ends every cascade.
           The maintainer's to choose.
       - `heap-strategies.erasure.load.cycle.adaptive` — dropped
         2026-11-01 (the maintainer: doubling, the growth kept) —
         growth by four where it is likely to be wanted: the first few
         growths, many functions growing fast at first, then reluctant
         growth by two (the maintainer, 2026-11-01); or by the evidence,
         four after a collection that freed little (an eighth, say), two
         once collections pay, which covers a fast start and a later
         phase of growth alike. While a net only grows, its collections
         scan about its final capacity growing by two, a third of it by
         four, for up to twice the space at the end; growing by four the
         first few times alone saves the small early collections, much
         to a small program, little to a large one. Measured 2026-11-01
         (store run 133, the library's capacities summed): (A) by four
         below 4,096 nodes, by two after, the maintainer's: on `succ` 102
         and 112 instructions a node of final capacity at k 14 and 16
         against 122 and 116, on the dropping terms 3.7% over plain
         demand against 4.3%, capacities 732,160 against 649,984 (12.6%
         more, small nets at 512 and 2,048 where they stopped at 256 and
         1,024), the nodes scanned 23% fewer; (B) by four after a
         collection freeing under an eighth: 186 and 181 on `succ`, its
         late fourfold growths ending at twice the capacity (262,144
         against 131,072 at k 16) and each growth copying the store word
         by word, 4.0% on the dropping terms, capacities 727,296, the
         nodes scanned 29% fewer. A is the cheaper; neither is merged.
       - `heap-strategies.erasure.load.cycle.lazy-sweep` — dropped
         2026-11-01 (the maintainer: a little saved on the free list's
         building, for much state and complexity) — growth decided from
         the walk's count of marked nodes, the unmarked freed as the
         allocator needs them.
       - `heap-strategies.erasure.load.cycle.reserve` — built 2026-11-01
         — the
         maintainer's batching (2026-11-01: K nodes seen free, then K/2
         interactions run without asking, K wanted before growing),
         refined. A demand step makes one interaction at most, and an
         interaction takes two free nodes at most, so S steps take 2S
         at most. Plain demand runs in chunks of S steps, its own walk
         asking nothing; a reserve of 2S free nodes is kept off the free
         list, and where the allocator finds its list empty it takes the
         reserve, rather than growing, and raises a flag in the net's
         header; at the chunk's end the flag calls a collection, the walk
         starts again from the interface, the reserve is set aside again
         and the net grows unless half is free. No count of the free
         list kept (each allocation and free in every strategy would pay
         for it, and reading it is a call where a check is made), no
         room asked a rewrite, no walk of the collecting demand's own
         (4.5% on dropping terms), no pair left out (a collection comes
         between steps); the plain modes pay a header read where their
         list runs dry, which is growth. It retires `.room` and
         `.dispatch`, the room tables and the hand-written rewrites
         (`heap-strategies.generate`'s case): the walk back to one
         template over its `after`. Built: `P.reserve` sets aside the
         first nodes of the free list on a list of their own (header
         words `at_rsv`, `at_tap`), the allocator's growth path
         (`alloc.grow`) taking it before doubling; plain demand's loop is
         `demand.go`, plain demand `d.end` of it, so that the walk keeps
         one caller; `demand.c` runs it a chunk at a time, S a 64th of
         the capacity, the reserve a 32nd, and fuel kept exact; the
         audit walks the reserve after the free list. Every library case
         kept (store run 131), capacities 649,984 against 645,760,
         interactions 2.29% past demand's against 2.37%. On `succ`, 116
         to 122 instructions a node of final capacity against 158 (run
         130); on the 16 dropping terms, 4.3% over plain demand against
         7.6%. Plain demand the same in the default build; the
         forced-inline builds move by half a percent either way, the
         eager modes too, which share nothing changed but the smaller
         generated rule table (spot run 129 against 124).
     - `heap-strategies.erasure.load.cycle.room` — dropped 2026-11-01,
       retired by `.reserve`, which asks no room — the
       nodes the room check walks to on the free list popped there and
       handed to the rewrite, rather than walked and then popped again
       by the allocator (the maintainer, 2026-11-01); the generated
       rewrites would take nodes as arguments.

     - `heap-strategies.generate` — planned — code wanted in variants
       that templates serve badly generated, not copied by hand (the
       maintainer, 2026-11-01: templates where they serve, else
       generation), and generation made easier first, by a preprocessor
       of our own written in Bend, with keywords of our own (the
       maintainer, 2026-11-01: M4 was ruled out for its external
       dependency and logistics; `generated-sources` revised). The case
       that raised it, the rewrite written out by hand in `kstrat.bend`
       for the collecting demand, retired with `.reserve`; the next such
       case takes it up.
       - `heap-strategies.generate.revisit` — tentative — the maintainer
         (2026-11-03): revisit our approach to generators at some point.
         Now one generator, `spike/tools/gen_krules.bend` (1,922 lines),
         writes the kernel's rewrites, `spike/krules.bend` (3,394 lines),
         and the gate and the pre-commit hook regenerate it to compare.
     - `heap-strategies.erasure.typed` — planned — erasure assuming type
       safety (the maintainer, 2026-11-01): a dead operator, sure to
       receive data, becomes an eraser at once, and in general a node
       whose stuckness only a type error could show may be erased as
       though the program were typed. Valid reasoning, but it gives up
       diagnostics (a type error erased rather than reported) and
       weakens the laws on stuckness. The maintainer (2026-11-03) favors
       it for dead operators, valid for any type-safe net, which further
       simplifies static erasure (`.dead-kinds.links.dead-ports`); a
       transition of its own, since it makes optimizations assume type
       safety and so touches laws. It changes eager interaction counts,
       as a collection at arbitrary points does, unless erasers carry a
       weight; not worth it, the maintainer (2026-11-03): the profile
       keeps dead operators' events, for the analysis of discrepancies.
     - `heap-strategies.erasure.merge` — built 2026-10-31 (the
       maintainer's approval, 2026-10-31) — branch `erasure-kernel` onto main: the events in their
       own strategies, costing nothing where they are off. It changes no
       law: the law changes went to main with the model's half
       (bca342c), the kernel's half alone left here.
     - Logical interactions count no event: events are patterns that a
       graph language recognizes and names for performance, each meant to
       preserve meaning exactly (the maintainer, 2026-10-30). Events are
       still profiled, apart: the profiling strategy runs them in a loop
       of its own (the kernel's `evprofile`, the library's `evprof`), its
       logical interactions those of the interactions made, its events
       counted by the kind of node each acts on. Over the library, with
       events: 9.0% fewer logical interactions (9,303,412 to 8,461,554).
   - `heap-strategies.kinds` — active — room past the 16 kinds a
     header's four bits hold, for dead calls first and builtins'
     kinds later: options set out for the maintainer, 2026-10-30. The
     maintainer: 4 bits of kind and 4 of form too tight for builtin
     operators, 6 and 2 viable, 8 and 2 room to spare. Dispatch
     measured first (`docs/BendIssues.md`, "Dispatch on numbers";
     store run 80): Bend's match on two kinds grows with the cases
     (per dispatch, 39 to 57 instructions at 16 kinds, 90 to 153 at
     64), where a rule number from Bend's own lookup table, then a
     balanced tree of comparisons, holds at 28 to 33, the hottest
     pairs tested first 17; the high nibbles then the low, 31 to 50.
     Next, the kernel's dispatch rebuilt that way at 16 kinds, in the
     four builds.
     - `heap-strategies.kinds.dispatch` — built 2026-10-31 — the
       kernel's dispatch rebuilt as measured best: a rule number from
       Bend's own lookup table for the pair of kinds, the hottest rules
       (by the profiling strategy's pair counts) tested first, then a
       balanced tree of comparisons; and every table of kinds' facts
       (arity, polarity, stuck, grows) a lookup table. Measured at 16
       kinds, in the four builds and on the library, before any kind
       is added; generated, as the rewrites are. Built: `KR.rule_no`
       numbers a pair's rule from a table over A's code times 16 plus
       B's, an arm for every index (a match over the 50 pairs alone
       compiled to a chain, and the dispatch on it cost 4% to 10% more
       than the match on two kinds); `KR.rewrite` tests four hot rules
       first (a call meeting a merge, data or a co-control; a control
       meeting a co-control: the standard workloads' and the random
       terms' hottest), then a balanced tree of comparisons, each
       rule's arm a function called once; the payload test, the stuck
       states demand reads and the growth the two stacks read are
       tables by rule number, the principal's polarity by kind; the
       number is read once a rewrite. The library passes. Four builds
       at k 18 (store run 86 against 85): 4.8% to 15.6% fewer
       instructions throughout, but for the profile-guided build of
       eager `lvl` with events, 2.2% more, its events loop cold in
       training.
     - `heap-strategies.kinds.layout` — built 2026-10-31 — the header
       widened to 8 bits of kind, 2 of form and a 22-bit field, levels
       and sites to 4M (the maintainer, 2026-10-30: `header-kind-byte`);
       the model's kinds widened with it; dispatch in tiers, kind to
       class by a lookup table, the class pair to a rule, an operator's
       own code chosen only inside its step. Built: `kprim.bend`'s
       header and the reference interpreter's kind mask at 8 bits; the
       value forms, 0 to 3, in 2; the field's laws restated for 22 bits
       (`fld_bits`, `lift_fits`; `lift_decoded` over the narrower
       field); the class tier, the rule table indexed by the pair of
       classes. The library passes, and the random terms give run 83's
       results term for term (store run 87). Four builds with the class
       a table over the 256 codes (run 88 against 86): 0.6% to 4.9%
       more, about half the table's two lookups a rewrite and half the
       header's (the default build without the tier, 1.8% more). The
       class now the code's minimum with the count of base kinds
       (`.class`, below). Still at 16 kinds: the
       profile's table by pair of kinds and the events' counters by
       kind in the header nodes, which widen with the first kind past
       15: the profile's now by pair of classes, the events' kept to
       codes below 16 by law (`heap-strategies.erasure.deadcall`).
       - `heap-strategies.kinds.class` — built 2026-10-31 — the class
         tier's cost, the table's 2.3% on eager `lvl` in the default
         build. Every code from some constant up is an operator (the
         maintainer, 2026-10-31): so a kind's class is `U32.min` of its
         code and the count of base kinds, each base kind its own class,
         the operators one, whose rule picks the operation by the code
         inside its step; the rule table (count + 1) squared, 289
         entries now; the minimum by a native comparison, Base's
         `U32.min` being defined over the word's bits. Default build:
         within 0.3% of no tier, where the table cost 2.3%. Four builds
         (store run 90 against 88, the table): 2.2% fewer in the default
         build and 0.9% in the profile-guided on eager `lvl`, 1.3% and
         0.8% more in the forced-inline ones; a minimum by arithmetic
         alone, no comparison, traded places again (default `lvl` 694
         million, forced inline 629, against the table's 696 and 631 and
         the comparison's 680 and 639). Differences of 2% that change
         sign with the build are clang's inlining, not the class's
         cost; the minimum stays, as the maintainer chose. The two
         steps with it against run 85: 0.1% to 12.8% fewer throughout,
         but for the profile-guided build of eager `lvl` with events,
         4.2% more (`heap-strategies.measure.pgo`).
   - `heap-strategies.fusions` — active — every fusion behaving as its
     components, proven (`fusions-as-components`); built so far in
     `heap-strategies.erasure.kernel.exact` (laws `linear_as_components`,
     `events_as_components`).
     - `heap-strategies.fusions.norm` — built 2026-10-30 — the
       derivation's normalizer running the events
       of `R.event` itself, its own copy of them (`lf.ev`) gone, and
       reducing any pair whose rule the payload test cannot change (the
       normalizer knows no payload), linear fans expanded into their
       components first. An event of one node applies in place, its
       node in the node's own slot as the kernel places it, the eraser's
       link dropped and a kept port renamed, as fans were marked linear:
       the derived rules are the same, link for link, and the kernel
       too. The derivation's fuel raised to 64 steps. Both laws hold
       still; mutated, they now fail for the reason alone: the call's
       event restored, 2 cases, against a function (10 before, 8 of
       them calls the old normalizer left); the co-control's event
       gone from `R.event`, 2, a control against a function; a linear
       copy's sides swapped, 50. A pattern of several nodes can now be
       checked: a call feeding a dead call (a call with its output
       erased), against a dead call, is the same against a function
       (both stuck), data and an error value, and against a
       superposition, a co-control or a linear merge leaves the same
       pattern again: equal up to itself. Once dead calls are a kind and
       that chain an event of `R.event`, the normalizer runs it, and
       `events_as_components` covers it (`heap-strategies.erasure.deadcall.chain`).
     - `heap-strategies.fusions.payloads` — built 2026-10-30 — the comparison to
       include what payloads and fields go where, in two parts, data the
       easier (the maintainer, 2026-10-30).
       - `heap-strategies.fusions.payloads.data` — built 2026-10-30 —
         each data payload's provenance: which node's payload goes where,
         copied, moved or dropped, a function applied to data a term of
         the two, no value observed, beyond whether it is immediate.
         Built: in the laws' graphs the pattern's node and its partner
         each carry their own payload as a source (A's, B's), data and
         calls only, a level or an index not followed; a rewrite
         resolves its new nodes' sources against the two nodes it took,
         a function applied to data the term of theirs (`SAp`, a source
         only the laws' graphs compose); the canonical order lists each
         node's source after its kind. No value is observed: the
         normalizer runs only rules the payload test cannot change, and
         the model has no immediates yet. No rule or event makes a
         composed source (laws `rules_base_sources`,
         `events_base_sources`), so the kernel meets none, its
         interpreters' arms for one unreachable. Both fusion laws hold,
         now over payloads; derived rules and the generated rewrites
         unchanged. Mutated: the derived rules' payloads A's for B's and
         B's for A's, `linear_as_components` at 8 cases (the linear
         copies against data, the linear merges against a call); B's
         dropped, 4; the call's rule on data making a composed source,
         `rules_base_sources` at 2; a linear copy's event making one,
         `events_base_sources` there and `rules_base_sources` at 9 rules
         derived through it. No fused pattern yet combines two payloads,
         a call and its data in one: that waits for operators
         (`heap-strategies.fusions.operators`).
       - `heap-strategies.fusions.payloads.levels` — built 2026-10-30 —
         each field's: a fan's identity and level, a control's raise, the
         fused form's update against the expanded form's; and with them
         a fan meeting a fan of one source reduced, its label known.
         Built: every node that carries something, a level, a fan's
         identity, a control's index, data or a call's function, has its
         source followed, erasers and the root none; a fan's identity
         resolves to its node's source, and what one node carries passed
         through a control to a term of the two (`SLft`, a source only
         the laws' graphs compose, as `SAp`). An event's node takes its
         source as a rule's does, and the law on events now builds the
         event's result with the source the event gives, not one
         assumed. The normalizer runs a pair whose test compares its two
         payloads (two fans, an application and a function, two
         controls: `R.test_eq`) where both have one source, the test
         passing; the reference interpreter's test passes for a payload
         met by itself (law `tests_reflexive`, through the hub's lemma
         that `U32` equality tests the values). So the identity function
         copied normalizes to two identities (law `copy_identity`), the
         case `heap-strategies.fusions.loops` left open. Different
         sources tell nothing: such a pair stays. Derived rules and the
         generated rewrites unchanged; all laws hold. Mutated, each
         fails: derived rules dropping a control's raise or swapping its
         two terms, `linear_as_components` at 8 cases (linear copies
         against a co-control, linear merges against a control); a fan's
         identity dropped, 16, A's and B's swapped, 24 (data with them,
         24, B's dropped, 12); a linear copy's event without its fan's
         identity, `events_as_components` at 2, which the law missed
         before taking the event's source; a composed source in a rule
         or event, `rules_base_sources`, `events_base_sources`; no
         equal-source decision, `copy_identity`; an application meeting
         data counted an equality test, `tests_reflexive`.
     - `heap-strategies.fusions.controls` — built 2026-10-31 — control
       fusion at the level of rules: a run, against each partner, as its
       unit controls, stuck where they are, its levels as theirs (the
       levels themselves already: `units_are_run`, `run_splits`,
       `peel_pairs_units`). Built: in the laws' graphs a run's units are
       segments of it (`SSeg`, units i to j - 1 of the run whose payload
       is c, a source only the laws compose); a value passed through two
       segments of one run in order is passed through their join, the
       rule-level form of `run_splits`; and the normalizer fuses two
       controls of one kind where the first's auxiliary feeds the
       second's principal and their segments join, as `V.compose` does
       after each rewrite. Law `runs_as_units`: a control of either kind
       standing for a run of two units, facing any partner but a
       control, is stuck where its units in series are and otherwise
       leaves what they leave (both kinds alike: the first unit at the
       principal, each one's auxiliary feeding the next one's
       principal). Two units stand for any split, the normalizer
       reading segment bounds only to join them. Derived rules and the
       generated rewrites unchanged. Mutated, each fails: no fusion, 18
       cases (every partner a control is copied onto: functions,
       merges, linear merges, applications, copies, linear copies,
       calls); no joining of a value's segments, 16 (all but calls,
       which carry no level); fusion in the wrong order, 18; a
       control's copies laid backwards on a merge's inputs, 6.
       - `heap-strategies.fusions.controls.peel` — tentative — facing
         controls at one index, a run peeled against the units both
         stand for: the laws' graphs to read two runs' units at one
         index as one value each, and the normalizer to peel the longer
         where they meet, as `net.bend` and the kernel do.
       - `heap-strategies.fusions.controls.kpeel` — tentative — the
         kernel's peeling arithmetic (`kprim.bend`'s `peel.amt` and
         `pe.do`: the units kept, the rest's index and offset) proved
         against `CT.peel`, as `lift_raise` proves the kernel's raise;
         the drop case, a raise run facing a croissant and keeping one
         unit, modeled in `ctl.bend` first, which knows raises only.
         With `.peel` at the level of rules, peeling would rest on laws
         from the kernel's words to the units.
       - `heap-strategies.fusions.controls.cross` — tentative — facing
         controls at different indices, crossing, the higher adjusted by
         the lower: the laws' graphs to know which index is lower, so
         that a value passed through a control above it is itself.
     - `heap-strategies.fusions.assume` — built 2026-10-30 — what the
       normalizer takes for granted, as laws: no eraser's rule depends on
       the payload test (`erasers_untested`; the negative eraser's rules
       take no test at all, the positive's go through rules that do); no
       rule links two ports of one new node (`rules_no_self_links`);
       every event makes one node, linked only to external peers
       (`events_one_node`), so the normalizer applies events in place
       alone, the general application gone (untested, and taking a fan's
       identity from the wrong slot for a second node): an event of more
       nodes makes no step there, the law failing first (the maintainer,
       2026-10-30: a law's failure the signal to generalize). Each law
       fails on its mutation alone: the dead application's event of two
       nodes restored, `events_one_node` at that event; a negative
       eraser's rule stuck when the test fails, `erasers_untested` at 6
       kinds; a self-link in erasing a function, `rules_no_self_links` at
       6 rules (that one and the linear ones derived through it).
     - `heap-strategies.fusions.loops` — built 2026-10-30 — a node with
       a port facing its own other port (the maintainer, 2026-10-30): principal
       to auxiliary, a vicious circle on any node, never interacting;
       auxiliary to auxiliary, by polarity only a function's (body to
       variable, the identity) or an application's (argument to result),
       a fan's a polarity violation, an operator's (payload to result)
       stuck, the payload waiting on its own result. An application so
       looped is unobservable only where no variable leaves its
       function's body: `ap-self-extruded` reads it, 5 in every strategy,
       through a variable the root reads; `fn-self-identity` checks the
       identity. Fused nodes keep their components' polarities at the
       ports they keep, so their loops classify as the components' do (a
       law, `fused_polarity`). Built: the law checks' rule application
       resolving a peer that is the redex's own port as the kernel's
       interpreter does (the rule's links with no end inside the redex,
       then those its own ports join, a loop with no node vanishing);
       laws `aux_loops` (opposite polarities on auxiliary ports only on
       a function or an application), `fused_polarity`, and `beta_loops`
       (beta with the function looped the identity, the application
       looped a knot of the function's body into its variable, both
       nothing, neither beta). Each fails on its mutation: pairs not
       joined, `beta_loops`; a copy's second output negative,
       `aux_loops` (and `fused_polarity` through the right linear copy);
       a right linear copy's port negative, `fused_polarity`. Derived
       rules unchanged. An operator's loop, payload to result, waits for
       operators (`spike-operators`); a copy of a looped function, two
       identities, for payloads (`heap-strategies.fusions.payloads`):
       its copy and merge meet with one fan's label, which the
       normalizer cannot know yet.
     - `heap-strategies.fusions.upto` — tentative — the argument the laws
       lean on, stated as laws where it can be: equal up to the events
       means equal (events end, one step observes all, rules with
       events are confluent).
     - `heap-strategies.fusions.operators` — dropped 2026-11-01 — each
       fused form of an operator against the general two-stage operator:
       one operator kind, holding its opcode and accumulator, has no
       general form to answer to (`operator-nodes`, revised).
     - `heap-strategies.fusions.immediate` — contingent on
       `heap-strategies.kinds.layout` — a fusion may observe whether a
       payload is immediate and nothing more (`fusions-as-components`):
       immediacy modeled in the laws' graphs once the model has
       immediates, and a law that no fused rule's choice depends on
       more.
     - `heap-strategies.fusions.fits` — built 2026-10-31 — the condition
       `tests_reflexive` takes, kept by rewriting: every control or
       co-control a rule makes carries a control's index and offset
       whenever the pair's own payloads fit their kinds
       (`rules_keep_fits`, by cases on the kinds, the test and, where a
       rule makes a control, the payload it is made from: controls come
       only from controls), and no event makes a control
       (`events_keep_fits`). Mutated, a co-control made from a
       function's level fails it.
       - `heap-strategies.fusions.fits.load` — tentative — the same of a
         loaded net: a template's control carries a control's payload by
         its shape, as a fan's identity has `T.TF`, or the loader
         reports a template whose control carries another, never
         reducing it.
     - `heap-strategies.fusions.ktests` — tentative — the kernel's own
       payload tests pass for one source, as `tests_reflexive` says of
       the reference's: `P.same_lvl` on two headers built from one form
       and field with different kinds, `P.peel_ctl` on one control's
       offset met by itself, peeling nothing. Wants `U32` lemmas for
       shifts and masks, a header's kind in its low bits, which the hub
       lacks.
     - `heap-strategies.fusions.distinct` — tentative — the normalizer
       knows two payloads equal by one source, never unequal; fans of
       different sources the rules make fresh could be known distinct
       (`heap-strategies.fresh` marks a related property), should a law
       need such a pair reduced.
   - `heap-strategies.measure` — tentative — measuring that keeps pace
     with development (the maintainer, 2026-10-31). Today a four-build
     count (`spike/tools/count_builds.sh`) takes about half an hour:
     `inline_build.sh` runs `bend` twice on one program, then compiles
     its 3 MB of C some eight times in turn at `-O3` (two GCC builds no
     count reads among them, an instrumented build, training runs, two
     profile-guided builds), and 40 counts at k 18 run one after another
     on an 8-core machine.
     - `heap-strategies.measure.spot` — built 2026-10-31 — a spot check
       in a few minutes, for development: the C emitted once, the
       default and forced-inline builds compiled side by side, the
       standard workloads at a smaller k, or two sizes apart so that
       start-up cancels in the difference, the counts run side by side
       (instruction counts are a process's own); the profile-guided
       builds and k 18 kept for merges. Built: `spike/tools/spot.sh`,
       `count_builds.sh` with the default and forced-inline builds
       alone (its new `BUILDS`), nothing trained, the erasure modes
       counted too, at k 18 after all: a count there takes 0.3 s, so
       the builds were the whole cost, and k 18 compares with every
       count in the store. 54 s; its 20 counts are run 90's within 300
       instructions (store run 91).
     - `heap-strategies.measure.builds` — built 2026-10-31 — the full
       count faster: one `bend` emission, the GCC builds only on
       request, the compiles and the counts in parallel. Built: the C
       emitted once and compiled as `bend -o` compiles it (`clang
       -std=c11 -O3`, which `bend` runs on its C in a temporary
       directory whose name the binary keeps, so that its own builds of
       one program already differ by a few hundred instructions); the
       default, forced-inline and instrumented builds compiled side by
       side, then the two profile-guided ones; GCC with `GCC_BUILDS=1`.
       The counts stay one after another, 40 taking about 12 s. 94 s
       for the four builds with events, its 40 counts run 90's within
       579 instructions (run 92); the GCC builds had taken most of the
       half hour. Bend's flags are captured at every build, whatever its
       version (`scripts/bend-cc.sh`: a one-line program built through a
       logging `clang`, under a second; the maintainer, 2026-10-31); the
       spot check the same within 30 instructions (run 93).
     - `heap-strategies.measure.differential` — built 2026-10-31 — the
       random-term differential faster (the maintainer, 2026-10-31): 27
       minutes for its 18 sets (store run 98), built one after another.
       A set's build is nearly all its time, about a minute at 200
       terms: half Bend emitting the C, at 2.3 GB, half clang at `-O3`;
       its run takes 2 s. `-O1` saves 5 s of the 31; `-O0` compiles in
       12 s but runs in 25, every level giving the same output. So the
       sets are built and run in a pool, three by default (`JOBS`) so
       that their builds fit in memory together, and recorded in order
       once all are done: 12.3 minutes, the store's 3,600 rows run
       98's exactly (run 101). Three at once take two minutes each
       rather than one, so the builds contend for more than memory.
       - `heap-strategies.measure.loader` — built 2026-10-31 — one
         build for every set: a one-term set still took 39 s to build
         (1.4 GB), two thirds of a set's build being the spike itself,
         compiled 18 times over (the maintainer, 2026-10-31: try it).
         `spike/runterms.bend`, the test program `terms.py` had written
         for each set, is now a source built once, which reads a set's
         nets from a file at run time (`spike/load.bend`: decimal
         numbers, the nodes by `nets.bend`'s constructors, so that a
         loaded net is the compiled one); `terms.py --kernel` writes the
         file. A set's output is the compiled program's byte for byte;
         the 18 sets, written and run on every core, take 4 minutes
         with the build (store run 102, its 3,600 rows run 101's
         exactly), against 12.3 and 27: writing a set's nets takes
         Python 4 to 8 s, and its run from 2 s up.
         - `heap-strategies.measure.loader.profile` — tentative — the
           profiling script (`spike/tools/profile.sh`) builds a program
           per family too (`terms.py --profile`): the same loader would
           serve it. The library is built once a gate either way; a
           build kept while the spike's sources are unchanged would
           spare a gate that changes no source.
     - `heap-strategies.measure.pgo` — tentative — profile-guided
       builds trained with events on too: today they train without
       them, so their events loops are cold and their counts with
       events say little (+2.2% to +4.6% where the other builds fall).
       Trained on both modes, a mode's count reads a profile shaped by
       the other, which makes comparisons across modes hard to call
       fair; a profile per mode keeps each fair, at a build each. Train
       too on programs that behave like real ones (the library's
       mixins, searches, parsers): random terms and the standard
       workloads never make the best profiles.
   - `heap-strategies.fresh` — tentative — a future experiment, apart
     from `heap-strategies.erasure` (the maintainer, 2026-10-30): a mark
     on a fan that has never commuted, which has no residuals anywhere,
     so that an erased side makes it a wire at run time too, as
     `heap-strategies.erasure.aot` does ahead of time. Each mixin's copy
     of `super` is such a fan when `super T` dies. Whether it is worth
     its complexity, a profile is to say first.
   - `heap-strategies.header` — built 2026-10-29 — the net's own words
     in slots of the node array, not fields of the record Bend passes through
     every function (the maintainer, 2026-10-29): the free list's head,
     the counters, the data table's head, so that a live net is an
     array of words paired with an array of values. A first measurement
     moved the free list's head alone into node 1, which the free list
     never holds (branch `heap-header`, 93bccb2, deleted 2026-10-30): demand 2.9% to 5.3%
     fewer instructions in all four builds at k 18, the full reduction
     3.8% to 4.9% fewer by default and -2.7% to +0.8% inlined or
     profile-guided, the same interactions (store run 49 against 48).
     Then the layout itself: a header of two nodes at the array's
     start, which the free list never holds, with the free list's head,
     errors, interactions and capacity, and the data table's head,
     high-water mark, capacity and depth; the interface the first node
     after it, node 2; the record the two arrays, words and values, the
     cold record gone. Against main (store run 50 against 48), every
     workload cheaper in every build: `fma` 4.0% to 6.3%, the data
     table no longer behind a record opened by allocating; demand 3.8%
     to 5.6%; full reductions 0.3% to 5.5%. The same interactions; the
     library's 44 cases print the same on both layouts, two of them new
     to cover the data table (`pow-2-6-plus`, `pow-2-6-fma`).
     - `heap-strategies.header.stack` — built 2026-10-29 — the eager
       strategy's stack keeps its count at its word 0 the same way, and
       its room at word 1 (the maintainer, 2026-10-29): the stack is one
       array, the pop's record two words narrower. Full reductions 0.9%
       to 3.4% fewer instructions in every build, demand untouched, the
       same interactions (store run 51 against 50).
   - `heap-strategies.bitmap` — tentative — under discussion (the
     maintainer, 2026-10-28 and 29): active pairs marked in a bitmap, a
     bit per node at the lower node of each pair, kept in pages of the
     node array, one node of each 128 holding its page's bits (0.8% of
     memory, nothing added to the record). A link joining two
     principals sets a bit, an interaction clears one. Where it belongs
     is open. In the net, every strategy keeps it, so it holds whatever
     runs, switching strategies needs no scan, parallel rounds take
     their pairs from the pages they own, and erasure pairs off
     demand's path could be reduced in batches, as before the net
     doubles; demand pays for bits it never reads. As a strategy's, the
     way the stack is now, demand pays nothing and an eager strategy
     starts with a scan. How new pairs are tracked is then a parameter
     of the rewrites (none, a stack, bits): Bend does not specialize
     static higher-order code (`docs/BendIssues.md`, "Compile-time
     specialization"), so the generator writes one family per tracker,
     as it writes the plain and eager families now. Choosing pairs
     eagerly from the bits alone loses order and locality, and a chain
     whose next pair always lands behind the sweep costs a sweep per
     interaction; a stack of hints checked against the bits keeps the
     order, but any bound independent of the heap is still quadratic
     at worst, a sweep per overflow (the maintainer). Hints in
     proportion to the pages, one per page, amortize a sweep's n/32
     words over at least n/128 interactions. A summary bit per page, or
     a meta-bitmap passing 32 empty pages a word (8 if it tracks bitmap
     words), only makes a sweep cheaper where pairs are compact: still
     quadratic, and bits kept in two places (the maintainer,
     2026-10-29). The simpler alternatives: one stack of half the
     heap's size, so that no operation grows it, at 12.5% of memory; or
     a growing stack whose limit is checked before every push, which is
     simpler than bits in two places, its head kept at its position 0
     as the net's free list is (`heap-strategies.header`). To measure:
     the bits' cost to demand, sweeps on families at n, 2n and 4n, how
     often hints overflow, against the stack as it is. Measured
     2026-10-29 on branch `heap-pages` (d6841f9, deleted 2026-10-30): pages of 128 nodes,
     each with its bit node, the bits kept by both rewrite families, the
     interpreter and the loader, cleared as `fresh2` frees a pair, every
     bit checked against the links after each test run; the library's
     output the same as main's. Read by nothing yet, the bits cost every
     build at k 18: demand 5.6% to 9.4%, full reductions 3.8% to 7.8%
     (store run 52 against 51). Pages alone, the marks and clears
     disabled: demand 1.8% to 5.4%, full reductions -1.5% to +2.3% (run
     53). A table for the bit instead of a shift by a `Nat` was no
     cheaper. Each bit set or cleared is a read and a write through the
     net's array; bits a strategy keeps for itself would cost demand
     nothing.
   - `heap-strategies.twostack` — active — eager with two stacks (the
     maintainer, 2026-10-29): the pairs whose rewrite would grow the net
     wait at one end of the stack's array, the rest at the other, and the
     rest drain first, so erasures, annihilations and cascades run before
     anything duplicates; the basis for eraser cascades under eager
     evaluation. A rule grows when it makes more nodes than the two it
     frees, as the generator reads the rule table (`KR.grows`): fans,
     calls, applications and controls meeting a fan, copies, controls
     meeting a function; a copy meeting a merge only where they
     commute. Erasers meeting anything, data copied, an application
     meeting data do not. Pairs are noted to the near end and sorted as
     popped, where their headers are read anyway: one that grows moves
     to the far end. The total interactions cannot change, every complete
     reduction making as many (fusion's savings aside); what may change
     is the net's peak size, and locality. To measure: instructions and
     peak capacity against the one stack, on families at n, 2n, 4n and
     the library.
     - `heap-strategies.twostack.first` — built 2026-10-29 — `kernel K
       W two` and `K.run_two`; the stack's far end grows down from the
       array's last word, its count there (`P.far_push`, `P.pop2`).
       The library runs every case with it: the same values, no errors,
       interactions within fusion's order effects (0% to +4.8%). On
       `succ`, `fma` and `lvl` at k 14, 16 and 18 (store run 54) the
       peak capacity halves at every size, 16,384 nodes against 32,768
       at k 14, the interactions the same (`lvl` 0.02% to 0.2% more);
       but instructions rise 19% to 28%, about 220 an interaction on
       `succ`: every pop reads both ends' counts, every pair is sorted
       by two header reads as it is popped, and each pair that grows is
       popped twice. Cheaper: sort pairs as they are noted, the
       generator knowing a new node's kind and reading only an external
       peer's header; read the far end's count only when the near end
       is empty.
     - `heap-strategies.twostack.cheaper` — built 2026-10-29 — the
       low-hanging part (the maintainer judged the trade poor in most
       cases, 2026-10-29). The stack's word 1 marks where the far end
       begins and word 2 holds the capacity, so either pop reads two
       words and the far end's only when the near end is empty: two
       stacks 0.9% to 1.1% cheaper by default, one stack unchanged in
       all four builds (store run 56 against 55).
       Passing the headers read to sort a pair into the interaction
       (`KN.ori.e`) gave two stacks nothing and cost one stack 3.7% to
       4.0%, `ori.e` with a second caller: dropped. What remains, about
       +18% to +27%, is the sorting and the moves; sorting pairs as they
       are noted needs a third copy of the interaction chain in
       `knet.bend`, beside the plain and eager ones, which a template
       or generator should write rather than a hand. Copy meeting data keeps the node count and so does not
       grow, the data table not counted (the maintainer, 2026-10-29:
       either that, or growth where the data is a table entry, which
       the data node's header tells).
   - `heap-strategies.reuse` — built 2026-10-29 — a rewrite's first two
     new nodes take the redex's two slots in place (`P.renode`), a rule
     making one frees b's slot alone, one making none both: the slots the
     free list would have handed back, so the net is the same node for
     node, without the free list's traffic. Generated for every rule;
     the interpreter keeps the free list, its nets the same. The library
     prints the same; every workload cheaper in every build, by 8.0% to
     15.5% by default and 2.5% to 13.9% inlined or profile-guided, the
     same interactions (store run 57 against 56). Erasing `K 0 #k` (k
     2^14 to 2^18) gains only 1.5%, its cost mostly the template's load.
     It is the eraser cascade's "allocating nothing" (the maintainer,
     2026-10-29), for every rule.
   - `heap-strategies.cascade` — active — erasure cascades (the
     maintainer, 2026-10-29: a reduced two-stack approach). Under the
     eager strategy they happen already: an erasure rule makes only
     erasers, its pairs go on top of a stack taken last in first out, so
     a cascade runs depth first to its end before older work, and with
     `heap-strategies.reuse` its steps allocate nothing. Demand leaves
     what it drops in the net. There, collect before growing: where a
     rewrite finds the free list empty, scan the net for pairs with an
     eraser, seed a fresh stack with them alone and run the eager loop,
     which then makes only erasure pairs; the walk restarts from the
     interface, its path a cache. No new family of rewrites, nothing
     noted per rewrite; demand pays a test of the free list's head per
     rewrite. To measure: demand's peak capacity and live nodes on the
     library's costly entries, and its instructions.
     - `heap-strategies.cascade.collect` — built 2026-10-29 on branch
       `heap-collect` (7719115), not merged, the branch deleted 2026-10-30: as above, a collection that
       erases less than a quarter of the capacity doubling the net too,
       so the scans stay linear. Demand's result now reports the
       capacity it grew to (merged). On the library it frees 2 to 27
       nodes more on the costly entries and changes no capacity:
       `costly-133` ends with 45,296 of 65,536 nodes live either way,
       `costly-124` 2,273 of 8,192. Demand's garbage is not erasure
       pairs but unevaluated work hanging off an eraser at its result,
       an auxiliary port, which an eraser can take apart only by doing
       the work. Such a subnet is joined to the rest only through its
       eraser, so it is cut off from the interface: a collection by
       reachability, marking from the interface along every link and
       freeing what is unmarked (releasing their table entries), would
       reclaim it without reducing it. Unobservable, as divergence is.
     - `heap-strategies.cascade.nongrow` — built 2026-10-29 on branch
       `heap-collect` (96ceaca), not merged: the maintainer's version,
       collecting every pair that does not grow the net, and doubling
       unless the collection made more interactions than half the
       capacity. The pairs are the generator's `KR.collects`: never
       stuck, no more nodes made than freed, no builtin applied, no data
       copied, a need for a lazy value never touched. It frees more
       (`costly-6` with unit brackets ends with 1,360 live nodes, not
       2,399) and changes no capacity: no collection comes near half.
     - `heap-strategies.cascade.reach` — built 2026-10-29: `KN.reach`
       counts the nodes a walk along links reaches from the interface,
       marking each in a bitmap, and `KN.sweep` frees every live node
       it does not reach, releasing table entries; demand's result
       reports the count, and `K.run_ds` sweeps after demand
       (`test_demand.bend`: `K 0 #64` from 132 live nodes to 2). At
       demand's end the interface reaches 2 nodes, itself and its value,
       on every library case but the cycle: everything else left is cut
       off (`costly-133` 45,290 nodes). Demand sweeping wherever its
       free list is empty (branch `heap-collect`, dc983fa) changes no
       capacity, doubling unless half or even a quarter was freed:
       wherever the net fills, three quarters of it or more is still
       reached. The garbage comes as a computation collapses at its
       end. A frozen net needs no sweep (the maintainer, 2026-10-29):
       freezing walks from the interface to write the compact form, so
       it copies only what is reached.
     - `heap-strategies.cascade.combined` — built 2026-10-29 on branch
       `heap-collect` (af51729), not merged: the non-growing pairs
       first, cutting more off the interface (the maintainer:
       structure held only by unreached erasers), then the sweep, the
       net doubling unless pairs and nodes swept pass half its
       capacity. It reclaims more than either alone (`costly-124` with
       levels ends with 1,112 live nodes, against 2,263 and 2,228) and,
       at half, changes no capacity. Doubling unless an eighth was
       collected, three capacities halve: `costly-124` with levels and
       `search-pairs` with labels and unit brackets; the others do not
       move. Garbage at a growth point is real but between an eighth
       and a half of the net on this library; a library of programs
       that drop more as they run (`pairing-library.programs`) should
       decide the threshold.
   - `heap-strategies.rounds` — tentative — parallel rounds in two
     phases: every pair's local outcome, nothing written outside its own
     nodes, then the links between outcomes resolved and the next pairs
     found; pages owned by workers as `spike-page-rounds` measured. Kept
     as an experiment (the maintainer, 2026-10-28): sparks, tasks
     reducing lazy values ahead of demand, are the anticipated main
     source of parallelism, but not decided. This measures what reducing
     a net's pairs together costs, the sequential case above all, so
     that Bend's lightweight parallelism is kept wherever careful design
     makes it cheap.
4. `heap-freeze` — frozen nets: freeze a live net once its reduction is
   done, instantiate a frozen net into a live one or splice it into a
   running net, at n, 2n and 4n nodes; local reduction of build-only pairs
   under fuel before freezing.
5. `heap-cells` — one page of the flat cells: recipes, live nets,
   suspension in the cell, resumption, inline forcing within a worker,
   forwarding, values; final and partial data told apart by tag; laws on
   cell states (a cell only moves forward; a value is written once).
   From `spike-operators.lazy`: an operator takes its argument unforced,
   only that it is data (`operator-nodes`), so a lazy cell's handle may
   reach an operator, which today computes on the handle; demand's need
   reads and resumes B's data, and must read the operator's held value
   instead, or the operator must ask for the cell.
6. `heap-apply` — lazy applications of function values, applied to all
   arguments at once where known, partial applications taken over where
   used linearly; interaction-net calls copying raw nets.
7. `heap-measure` — taking and returning nets, freezing and instantiating,
   memory per small net, forcing depth against round latency, at n, 2n and
   4n.

Later, in EvalSpike's steps: logical copies (`spike-cursors`) if whole
copies cost too much; the split heap's collector, with identity for shared
interior nodes (`spike-lazy-data`); rounds over pages (`spike-page-rounds`).

## Open questions

- `net-demand-whnf` says pairs that only feed erasers reduce as found.
  Read literally that would start `K 0 Ω`'s Ω. Built instead: an eraser
  meeting a value reduces as found; a computation only an eraser takes is
  never started, as in the Rust bootstrap. The record's wording, for the
  maintainer.
- What "done reducing" means for a function's net: which pairs local
  reduction takes, under what bound, and whether hoisting
  argument-independent calls into shared thunks belongs to lowering.
- The frozen format: one made for materialization first; whether one made
  for interpretation is worth a second type.
- Linear partial applications beyond the obvious cases. The obvious ones
  (the maintainer, 2026-10-28) the model must handle: applications chained
  within a net, an application's result wired straight to the function
  port of the next, up to a copy of the function (each copy's chain is
  linear on its own); and curried arguments in syntax, `f a b c`, which
  lowering emits as one application of three arguments. Both gather into
  one recipe, a function and its arguments, copied once. Beyond those:
  annotations, or analysis. And when lowering emits sparks.
- How pairing levels are offset when a raw net is copied into a running
  net, and whether copies need fresh identities (NetPairing).
- How far inline forcing goes before a need goes to the coordinator, and
  how divergence in one forced cell is kept from holding a worker.
- Where partial structures keep identity: the inline bound below which an
  interior node holding handles is copied by value inside its cell.
