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
     - `heap-strategies.erasure.kernel` — tentative — the events in the
       kernel, at the links rules make, as control fusion looks at them,
       and the linear kinds' generated rewrites; every strategy measured
       on the library's families
       (`mixin-chain` against `mixin-once`, `list-head`, `search-first`,
       `parse-cut`, `K 2 Ω`, the mixins' full reductions), and the
       standard workloads in four builds, for what the checks cost nets
       with nothing dead.
     - `heap-strategies.erasure.strategies` — tentative — erasure under
       demand as a strategy of its own; or demand with eager collection
       on a second stack, as the two-stack strategy keeps its deferred
       pairs; and the two-stack strategy with only collection on its
       priority stack (the maintainer, 2026-10-30).
     - `heap-strategies.erasure.aot` — tentative — the simple case ahead
       of time (the maintainer, 2026-10-30): a fan that has no remote
       dual yet, as a variable's tree of fans before it commutes with
       anything, has nothing to annihilate with, so an erased side makes
       it a wire, and its tree can be rebalanced.
     - `heap-strategies.erasure.trees` — tentative — chains of linear
       fans, if they come to dominate, compressed into one node holding
       the tree's identity and the path, as runs of controls fuse.
     - Open: how logical interactions count a linear fan's interaction;
       perhaps twice, for the eraser's it stands for (the maintainer,
       2026-10-30).
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
     never holds (branch `heap-header`, 93bccb2): demand 2.9% to 5.3%
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
     2026-10-29 on branch `heap-pages` (d6841f9): pages of 128 nodes,
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
       `heap-collect` (7719115), not merged: as above, a collection that
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
