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
there by whichever one worker holds the cell. Its interface node is node 0
and never moves: a negative principal port with no rules, the user's
access to the net (the Rust bootstrap's `Interface`, the kernel's `Root`,
whose rules are tuned to keep slot 0). A `net_arity 0` computation is done
exactly when node 0 faces a data node, `Interface >< Data`, and its value
is node 0's peer, read in one step.

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
value, about 60 per level of recursion. When node 0 faces data, the cell
becomes `Value{v}`; when it faces a function, arguments still to come, the
net freezes and the cell's value is a function over it, its arity from the
recipe.

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
     store. Also counted as the unit system would (the maintainer,
     2026-10-28): a run of k
     crossing a node or cancelling its equal counts k, two runs crossing
     c times b, a peeled pair what peeling leaves; that count is the
     unfused interactions, the same in every order of a complete
     evaluation, and fusion's savings are it less the interactions made,
     which may differ by order. Equal counts across orders test fusion's
     soundness on whole nets, beyond `ctlwire.py`'s one wire. Fusions by
     shape are not counted: one shape remains, and the savings measure
     what fusion does; controls alive wait for `heap-strategies.trace`.
     - `heap-strategies.profile.weights` — built 2026-10-28 — each
       move's weight checked on the one-wire model (`ctlwire.py
       --weights`): a fused start's reductions, every move weighted, all
       total the interactions of its runs as unit brackets reduced
       unfused. A run crossing a value, a consumer or another run weighs
       its units times the other's, equal runs cancelling their units, a
       peel what it cancels or the run a drop crosses whole, a fusion
       nothing. The kernel's rule (`--peel --shapes 0`) holds on all
       4,001,400 starts to length 4 and 20,000 sampled at each of
       lengths 6, 8 and 10 (indices to 3, levels to 6), the unit counts
       never depending on order; the old fusion fails 46,872 of the
       222,264 starts of length 3 (store runs 38 to 42).
     - `heap-strategies.profile.strategy` — built 2026-10-28 — a
       profiling strategy in `kstrat.bend`: the eager one, each pair
       counted by kinds, A's principal negative, and weighted before it
       interacts, the sum in two words; `kernel K W profile`, and
       `profile_t` for tests. On `lvl` at k 10, 12 and 14 the weighted
       count is the same with the kernel's fusion on and off (6,458,
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
       unit brackets the weighted count with fusion is the interactions
       made without it, on all 1,791 (3,778,521 in all); with levels the
       weighted counts with and without fusion agree on all 1,797. The
       21 rows that do not complete ran out of fuel, none wrong. The
       kernel's fusion saves 23.3% of the weighted interactions with
       levels, 21.9% with unit brackets. The lowering's own fused
       controls, a croissant cancelled against brackets, save far more:
       on the 1,794 terms both lowerings complete, 1,296,183 weighted
       against 8,682,189, since runs crossing weigh their product. No
       term of the 5,400 peels; only the hand-built nets of
       `test_levels.bend` do, whose profiles are now regressions there.
   - `heap-strategies.trace` — contingent on `heap-strategies.net` — the
     net as rows at boundaries the caller sets (every n interactions, a
     demand step, a count of live controls), into a store of traces,
     written from Bend once its SQLite package is vetted, else imported.
   - `heap-strategies.demand` — contingent on `heap-strategies.net` —
     demand's own cost: the path in an array, the walk's layers folded
     (its profile is store run 26).
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
