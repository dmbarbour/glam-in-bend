# Heap review (Fable): intentions, hindrances, the maintainer's ideas, alternatives

Written by a Fable sub-agent on 2026-11-09, at the agent's request, as
the second reviewer beside [`Heap_2026-11-09.md`](Heap_2026-11-09.md),
which summarizes it and reports where the two differ. Kept as written;
its quotes were checked against the repository.

Second, independent review of the maintainer's message of 2026-11-09 on
the heap of cells, parallelism, hierarchical heaps and nets as heaps.
Read only; nothing built or measured. Claims taken from the repository
carry their path; everything else is my inference, marked *inference*
where it could be mistaken for a fact of the repository.

## 1. Intentions: what the docs require of the heap and of evaluation

One test separates the two kinds of requirement, and I apply it
throughout: a requirement is **semantic** iff relaxing it can change
`asm.result` (its bytes, or the error value it carries); otherwise it is
a **cost goal**, which parallelism may relax. The test is the docs' own:
"Assembly-time performance never affects results, only speed"
(`docs/DistilledDesign.md`, Assembler Executable, Performance) and
"Bend's parallel calls speed up the core; they never decide results"
(`docs/decisions/pure-core-io-shell.md`).

| Requirement | Where stated | Kind | Why |
|---|---|---|---|
| Reproducibility: same sources, same bytes | `DistilledDesign.md` Guiding Principles; `pure-core-io-shell` | Semantic | The product's first promise. Parallel work may never choose a result. |
| Demand: a result is computed iff needed; `K 0 Ω` is `0` | `net-demand-whnf`: "a computation only an eraser takes is never started"; `DistilledDesign.md` Semantics: "Pure, lazy" | Semantic | Termination is observable. Any strategy that runs ahead of demand must be bounded (fuel), or a diverging unneeded term holds a worker, as the Rust bootstrap saw: "a divergent spark holds a worker forever" (`HeapModel_2026-10-27.md`, Comparison). Running ahead is admissible; depending on it is not. |
| Call-by-need sharing: "a thunk forced twice computes once, and copies of a function share the reductions of its source" | `HeapModel_2026-10-27.md`, What must hold; `functions-are-nets-with-arity` | **Cost goal** | A second evaluation of a pure, terminating thunk gives the same value; a second evaluation of a diverging one is never demanded (it is only ever demanded once the first diverges, and then the result is lost anyway). glam cannot catch errors and divergence is unobservable to evaluation (`DistilledDesign.md`, Annotations), so nothing in `asm.result` can tell one evaluation from two. HeapModel lists sharing under "What must hold", but under the test it is the most consequential cost goal, not a semantic one. This is the premise of section 4: duplicated evaluation of a pure cell is wasted work, never an error. |
| The error value a result carries is deterministic | `net-error-values`: errors are data, demanded only where needed | Semantic | Interaction nets are strongly confluent (Lafont 1990), so every reduction order reaches the same value, error values included. Confluence is what licenses parallel reduction without touching results. *Inference*: it holds for glam's nets only if every rule is a function of its pair alone; operators over builtins and reads of cells (a pure value written once) keep it. |
| Which diagnostic surfaces first | `diagnostic-order-follows-schedule` | Cost goal, by decision | "Results never depend on it." |
| A cycle is reported, never spun on | Cells plan item 6; `HeapModel` Comparison ("cycles are found by walking blocked producers' single dependencies") | Semantic in outcome, implementation in method | A strict cycle must end as an error value, deterministically; *how* it is found is the heap's business, and section 2 shows the current method assumes one thread. |
| Nets as first-class opaque values in WHNF, composed through interaction-net calls; `net_arity` | `DistilledDesign.md` Semantics; `docs/Design.md`, Interaction Nets | Semantic | A user-facing feature. It also fixes one representation the heap must have anyway: a closed net value with one `+` port, loaded by `Bind >< Data(Net)`. |
| Reflection may inspect evaluation, never influence it | `DistilledDesign.md`, Reflection and Annotations | Semantic | Constrains the heap to be *inspectable* (provenance, the meta channel) without evaluation depending on the inspection. A heap partitioned into tasks must still be addressable for reflection, but only reflection pays for that. |
| No crash on user input; a machine's limit is not a program's failure; never cache a crash or an out-of-memory as a value | `AGENTS.md`, Working Rules; `machine-limits-not-errors` | Semantic (as a correctness rule) | A fail-stop of Bend (`Nat` past 2^48, a 24-bit count overflow, an array too deep) reached from user input is a bug. Parallel designs add new limits (counts on shared templates, round buffers) that must be checked, not trusted. |
| Scalability: "no upper bound on assembly ambition"; a computation larger than one net "spans nets and cells" | `DistilledDesign.md` Guiding Principles; `net-capacity` | Semantic in spirit | A single net is bounded at 2^28 nodes; the design must split large computations across nets or the bound becomes a semantics of size. Today nothing splits a net (section 2). |
| Laws over the core; no `@unsafe` in it | `AGENTS.md`, Laws; `split-heap` Consequences ("The core stays pure and free of `@unsafe`, so laws can cover the store") | Governance goal, high priority | Not glam semantics, but the project's chosen method; it rules out `Array.fork` and atomics in the evaluator (Architecture's option 2). Any parallel design must stay in pure Bend: affine arrays owned by one task, parallel calls, plain data crossing joins. |
| Reclamation of unreachable lazy state | `store-collection`; `Architecture_2026-10-26.md`, Collection | Cost goal, essential in practice | A batch assembly can finish before garbage matters (Cells plan item 9), an IDE session cannot. Cycles through `self` knots rule out counting alone ("reference counting alone would leak the cycles lazy fixpoints make", Architecture, The store). |
| Parallelism | `Architecture_2026-10-26.md`, Parallelism; `rounds-of-coarse-work`; `Design.md` Performance ("sparks") | Cost goal | Explicitly: speed only. Its constraint is Bend's: balanced fork-join, tasks dealt once, affine arrays never shared, a shared value read by every lane costing an atomic per read (`bend guide`, Parallelism). |
| The kernel's data types adopted into the final evaluator | `lambdas-lower-to-nets` Consequences | Engineering commitment | Not semantics; it says the spike's `Val`, table and node layout are meant to last, so changes to them are changes to the product. |
| Persistent, shareable caching; incremental assembly | `DistilledDesign.md`, Performance | Cost goal with a structural demand | A cached outcome must be a value with no identity in a run: closed, serializable data (a frozen net, a value), never a live net. *Inference*: whatever the heap keeps as plain `Data` can be cached; whatever lives as a live array cannot. |

Three observations follow from the table and carry the rest of the
review.

**Sharing is the lever.** Every hard mechanism in the current plans
exists to preserve call-by-need sharing across tasks: cells that are
written once and read by many (`store-pages`), pages owned by one worker
so a cell is never raced (`rounds-of-coarse-work`), function nets that
are "shared, mutable and must be reclaimed, like a lazy value"
(`functions-are-nets-with-arity`), cursors that share a source's pending
pairs among copies (`copy-reduced-function-nets`, deferred). Since
sharing is a cost goal, every one of these may be relaxed where the
sharing it buys costs more coordination than it saves, and the decision
is a measurement, not a principle. The Rust bootstrap paid dearly for
exactly-once production ("one producer per lazy value; waiters
subscribe, then recheck", with twelve recorded concurrency defects,
`HeapModel_2026-10-27.md`, Comparison).

**Demand is the constraint.** Whatever runs ahead of demand, sparks
above all, must be bounded in fuel and must never be waited on by the
demanded path except through the same wait any thunk imposes. This is
compatible with any heap shape.

**Determinism is free inside nets and costs only at cells.** Inside one
net, confluence gives any order the same result. Across nets, a cell's
value is a pure function of its recipe, so the only way a schedule could
leak into results is through the *reporting* of cycles and errors
(section 2, finding 1) and through limits reached by one schedule and
not another (`machine-limits-not-errors` covers this: a limit is never a
result).

The maintainer's two directions, hierarchical heaps and nets as heaps,
are consistent with every semantic row of the table. What they bear on
is the cost rows: how much sharing is kept, where reclamation happens,
and how large the unit of independent work is.

## 2. Hindrances: where the plans and records work against parallelism or integration

Rated **blocking** (parallel evaluation cannot be correct or cannot
exist while this stands), **costly** (it works but takes a rewrite or
leaves speed on the table), **minor** (a wording or a later chore).

**H1. A busy cell read as a cycle. Blocking if kept as written.**
`docs/plans/Cells_2026-11-09.md`, The model proposed: "**Busy:** a
strict cycle (item 6)"; item 6: "A need on a busy cell is a strict
cycle. Proposed: serve that need an error naming the cells around the
cycle, so that each of them caches an error as its outcome." With one
depth-first stack this is exact. Under rounds, `Busy` also means
"another worker holds this cell's net this round"; the same rule would
report a cycle that is not there, and cache an error as the cell's
outcome, forever, in a schedule-dependent way: a semantic leak. The
earlier plans had the right state, waiters: "A task waiting on a thunk
is attached as one of the thunk's waiters" (`Architecture_2026-10-26.md`,
Pages and rounds) and cycles "found by walking blocked producers' single
dependencies, and all members fail together" (`HeapModel_2026-10-27.md`,
Comparison). The Cells plan dropped them for the single stack. The fix
is cheap now and dear later: make `Busy` carry an owner (the stack
frame, or the task) and define a cycle as a need whose owner is the
needing task's own ancestor on the waits-for graph; the single-stack
case is the special case where the graph is a path.

**H2. The program is one net, and a net is one worker's. Blocking until
cells split it.** `docs/plans/Cells_2026-11-09.md`, Where the ladder
stands: "A definition is lowered into the net of each assembly that
needs it, shared within that net by fans"; `docs/decisions/net-nodes-double.md`:
"at most one worker reduces a net at a time; parallelism inside a net
comes from accelerated operations, not from spreading the net across
workers" and "A net does not spread across the heap's pages: the heap
holds nets as values, each taken whole by the worker that reduces it."
Together: today there is exactly one unit of work. The Cells plan splits
it at top-level definitions and function cells, which is the right
place; the point is that *the granularity of cells is the granularity of
parallelism*, and nothing in the plans measures it. A cell per global is
coarse where a program is a few big definitions and fine where it is
many small ones ("Each reference now costs a need and a resume", Cells
plan, Cost). Section 5 asks for the number.

**H3. A value in another worker's page waits a round. Costly; the
maintainer's "halting early to query a heap state" exactly.**
`Architecture_2026-10-26.md`, Pages and rounds: "A value already forced
needs no page: the coordinator shares it out between rounds, in O(1) as
Bend data"; "A task waiting on pages becomes runnable once one worker
can hold all of them; while they are split between busy workers it sits
out"; "A write into a page held elsewhere, such as a thunk's result, is
queued for that page's next holder." The mechanism: the page is the unit
of exclusive ownership, and a page holds cells of every state. So a
*read of a finished value*, the commonest and cheapest operation, stalls
a task to the next round (10 to 20 µs here, against interactions of
nanoseconds) whenever the value's page is held elsewhere, and handle
assignment ("named by a `U32` handle assigned before any definition is
lowered", Cells plan) places cells by declaration order, not by use.
HeapModel's remedy, inline forcing, is conditioned on the same thing:
"Where the needed cell can be forced in the same worker"
(`HeapModel_2026-10-27.md`, Forcing). The condition should be about the
*cell's state*, not its page: a Recipe or a Value is immutable Bend data
and could be handed to any worker; only a live net is exclusive.
Section 4, A2.

**H4. One depth-first stack baked into the protocol. Costly later,
cheap now.** `Cells_2026-11-09.md`, item 4: "with one task forcing
depth-first, every live net is a frame on the core's stack (`KD.D`), and
the store holds only `Data`", and "The migration is a frame moving into
its cell as `Suspended` when sparks come." `need`, `resume` and `splice`
(item 3) assume the needing net is the frame on top and the needed cell
is served by the same stack. That is right for the single-task mode and
should stay its fast path; but the state the protocol returns to the
core should already be a *task* (its frame, its need, its owner), so
that moving a frame into a cell is a change of container, not of API.
HeapModel's reason for progress in the cell, "cycles through tasks
cannot keep it alive" (The model), also returns the moment there are
tasks.

**H5. Function nets as shared mutable state. Costly; a record, so a
revision needs the maintainer.** `docs/decisions/functions-are-nets-with-arity.md`:
"A function's net is shared, mutable and must be reclaimed, like a lazy
value". Combined with `copy-reduced-function-nets` ("First, a function's
net reduces locally, as far as it goes without an argument; then each
application copies the whole net") and the maintainer's answer to item 5
(evaluate the function's net eagerly before freezing), the *frozen* net
is in practice immutable after its one freeze, and every copy is of
immutable data. What stays mutable is the window between a function
cell's creation and its freeze, and partial applications that are
values. The record's consequence, a store cell per function with
collection, is paid for a mutability that the plans have since narrowed
to that window. I do not recommend changing the record on this review
alone; I recommend measuring (section 5) what sharing of post-freeze
reductions would buy, since the Church-numeral workloads that motivated
it exaggerate it.

**H6. Two representations of every structure. Costly for integration.**
`docs/decisions/split-heap.md`, Consequences: "Structures holding
handles have two representations, inline and in the store; rope and
dict code handles both"; `Architecture_2026-10-26.md`, Values: "Every
node caches `ground`". Today `spike/val.bend` has only the plain forms
(`VList{xs: List<&2, Val>}`, `VDict{es: List<&2, Ent>}`, "its first
form"), so the partial forms, their `ground` tags, the inline bound
("the inline bound below which an interior node holding handles is
copied by value", HeapModel, Open questions) and every operation's
branch on them are all still to write, and `netdata-structures` is
undecided. The hierarchical view (section 3) shrinks this: a structure
built inside a net is nodes and table entries until it leaves the net,
and leaves as Bend data or a handle; the two-representation problem
remains only for structures that hold handles *after* leaving, chiefly
objects.

**H7. Marks cross pages as messages. Costly later.**
`Architecture_2026-10-26.md`, Collection: "a handle into a page held
elsewhere becomes a mark message, routed by the coordinator to that
page's next holder. Marking ends with a round that sends no message."
The cost grows with the number of cross-page edges and the diameter of
the handle graph in pages, each hop a round. A heap per net makes most
edges internal to a net, freed by the net's own linear reduction and
sweep (`KN.reach`, `KN.sweep`, Cells plan), and leaves the store's
collector only the shared cells.

**H8. Levels couple a copy to its destination. Minor for parallelism,
real for "nets as heaps".** `Cells_2026-11-09.md`, item 2: "shift every
level of the copy, of binds, applications and fans and each control's
index, by the applying node's level minus the root's", with a wrap
guard. A closed template is level-free only relative to its own root,
so capturing a subnet as a value (`Data(Net)`) must record its base
level and re-base on instantiation. This is the same offset the Cells
plan already needs for Func splices; it is not new cost, but it is a
reason a `Data(Net)` made at run time cannot be a plain memcpy.

**H9. Shared Bend data across lanes costs an atomic per read.** `bend
guide`, Parallelism: "a `+` value read by every lane costs an atomic
per read". `intern-hot-values` answers the count overflow, not the
per-read cost. *Inference*: the values every task reads (the namespace,
`env`, templates of hot functions) should be reached through handles
into per-worker copies or through the store, and the measurements in
`Architecture_2026-10-26.md` (a parallel fold 5.7× on 8 threads) were on
data each lane owned a part of, not data every lane read. Worth one
measurement before any design counts on sharing templates by reference.

**H10. The one-slice shell.** `Architecture_2026-10-26.md`, Concurrency
and the shell: slices "sized to 1–3 ms", rounds wanting "a few hundred
microseconds of work per worker". A slice holds a handful of rounds, and
the slice boundary is itself a barrier. Minor: it bounds how coarse a
round can be, and the IDE's latency goal and the round cost pull the
same way.

**H11. The whole-program net has no split.** `net-capacity`: "A
computation larger than one net spans nets and cells", but no mechanism
splits a net that grows (H2's one net, before cells). Minor once cells
exist; until then a large assembly meets the 2^28 bound as out of
memory, which `machine-limits-not-errors` reports correctly but does
not avoid.

Not hindrances, though they look like ones: `net-demand-whnf` (one path
of demand) does not forbid parallelism, since other tasks' demands are
other paths; `pure-core-io-shell`'s "one logical thread" is the
coordinator, which Bend's parallel calls serve underneath; the ban on
`@unsafe` costs the HVM2-style word heap but costs the fractal design
nothing, since a net already is an affine array owned by whoever
reduces it.

## 3. The maintainer's ideas

Two facts in the repository anchor both ideas: the kernel *already is* a
heap per net, a node array that doubles plus a data table of its own
(`net-nodes-double`; `spike/kprim.bend`, header: "a net as four-word
nodes in storage that doubles, its free list and active pairs, and a
data table of its own, kept linear"); and `Data(Net)` *already is* the
design's raw-net value, with its rule "`Bind >< Data(Net)` loads the net"
(`operator-nodes`; `docs/Design.md`, Interaction Nets: "a raw net is
loaded by logical copy through its exposed port"). So neither idea is a
pivot. What is new is making such values at run time from a running
net, nesting them, and treating the store as the level above them.

### 3a. Hierarchical, fractal heaps

**What it buys.** Three things, each large. (1) Locality without a
coordinator: a net allocates in its own array and table, frees by
interaction (an active pair consumes its nodes) and by its own sweep,
and no other task can see inside it, so none of that is contention or
collection. The sharing *within* a net needs no cells at all: a local
shared by fans at its level is already call-by-need sharing
(*inference*: the fan tree plays the part of a thunk's reference count,
GAL levels of its identity), which is
why `lowering-uses-levels` and HeapModel agree that "a thunk [is] a net
waiting at its interface". Cells are needed only across nets. (2) The
unit of exclusive ownership becomes the live net, an affine `Array`,
exactly what Bend's checker enforces for free; the page machinery of
H3 (grants, "write queued for the page's next holder", mark messages)
disappears for everything that is not shared. (3) A generational
collector by construction: a child net's garbage, everything off
demand's path that `net-demand-whnf` leaves "garbage until the net
goes", dies when the child's result crosses out as data.

**What it costs.** Boundaries. A subnet can migrate "without leaving a
trace" iff it is closed: one `+` port out and no other wire crossing.
In a lowered lambda net, the candidates are boxes (an argument's box,
a `let`'s value, `lowering-uses-levels`), and a box is closed only when
it has no free variables. This is exactly where the Cells plan stopped:
item 8, "A dict member computed in a running net has free variables
wired into that net, and cannot become a cell until it is closed." The
distinction the maintainer draws, linear versus shared, is the same
distinction at the boundary: *linear* is no fan on the port, *shared*
is a fan on it. A fan on a closed subnet's one port is lazy duplication
of a closed thing, which has two well-known implementations: copy the
whole thing on demand (the Cells plan's splice; HVM2's expansion of a
closed definition) or share its reductions through cursors (the Rust
bootstrap's, deferred by `copy-reduced-function-nets`). Nothing in the
fractal view is lost by choosing the first.

**Where it fails.** (1) Free wires. A box with free wires is not a heap
of its own; making it one means cutting each crossing wire into a cell
or a value, the Cells plan's fourth option for item 8 ("Cells at box
boundaries"). That is the STG machine's answer, Peyton Jones 1992: a
thunk captures pointers to heap objects, so every captured thing is
itself a cell. In nets it costs a cut of a fan tree at the boundary and
an allocation per free variable; in exchange the copies made by that
fan become copies of a *handle* (a word, no levels, no controls) instead
of lazy duplication of a subnet. *Inference*: for the member boxes of
objects, whose free variables are mostly `self` and a few locals, this
is cheap; for a deeply nested closure over many locals it is not, and
the front end can tell them apart statically. (2) Knots. `self` is
shared by construction: "an instance is a cell and `self` is its
handle, given out before its value exists" (Cells plan, What the
answers change). Objects therefore live at the shared level, and
"tracking where things went" is the store's forwarding (`Forward{to}`,
HeapModel's cells) plus shortcutting at collection; the current global
`U32` handle space is right for them and should stay. (3) Deep
hierarchies hide needs: a need met three nets down must reach the
worker's task record; fine if a child is always reduced by its parent's
worker (it is: a `Bind >< Data(Net)` is one interaction of the parent),
and it argues against the coordinator ever seeing nested nets at all.
(4) Reflection must address nested nets; a path of ports, the
bootstrap's `RemoteCursor` shape. A reflection cost only.

**How it meets balanced fork-join.** Well, if tasks are closed nets.
A round forks W workers, each given a list of live nets (affine, moved
in and out of the coordinator's table) and the recipes and values it
may need (Bend data, copied by count); each reduces under equal fuel
and returns its nets, its values and its needs. Balance is in logical
steps, which Bend's deterministic result needs anyway; a worker whose
nets all block early idles until the barrier, so the coordinator wants
slack (more runnable nets than workers) and a cost estimate (last
round's fuel use) to deal them, the LPT heuristic (Graham 1969). The
10–20 µs round cost stands; what the fractal design removes is the
*reasons to end a round early*: no page faults, only true needs.

### 3b. Nets as heaps: data as net structure

**Encodings (Church, Scott, Mogensen–Scott).** They buy uniformity:
matching is application, laziness is free, pipelining between a
producer and a consumer happens by interaction, and the sharing graph
handles sharing. They cost a node per constructor and per field, fans
for every non-linear use, and a conversion at every boundary where
glam's data must be native: comparison and dict keys ("Only numbers,
and lists or dicts of them, compare", `DistilledDesign.md`), hashing for
caching, bignum limbs, and above all output, which is bytes: a megabyte
binary is 16K packed rope leaves (`Architecture_2026-10-26.md`, Ropes)
and would be millions of nodes Scott-encoded. The HVM lineage tried
both and settled on native constructors beside combinators (HVM2 has
`CON`/`DUP` combinators with native numbers, operators and a numeric
switch; I believe that is the paper's node set). Verdict: encodings for
control (booleans, options, the pass/fail of conditionals, which the
Church-boolean sample already runs) and for *lazy* lists streamed
inside a net; native Bend data for anything that leaves a net, is
compared, or is big.

**Specialized node kinds (cons, nil, dict nodes).** This is
`netdata-structures` ("lists as nodes, a cons and an end, so a producer
and a consumer stream through the net"). It buys pipelining and
element-wise laziness with no encoding tax; a cons node is four words
like any other. It costs rules (match as interaction, a copy rule per
kind), 64 kinds in the header (`header-kind-byte`) of which many are
spoken for, and a freeze into ropes and dicts at the boundary. The
level discipline applies to these nodes as to fans. Worth having for
lists; for dicts I am less sure, since a dict's value is mostly looked
up by key, a native tree's strength, and a knot over `self` is an
object, which section 3a puts at the shared level anyway.

**Reference-counted data nodes as allocations within a net.** A node
with a count is a non-linear node: k references to one subnet, which is
a local cell. It buys O(1) sharing of a *closed* subnet without fans or
levels, and local thunks that several wires read. It costs the two
hazards of counting: cycles leak, and a 24-bit count saturates (Bend's
own limit, `Architecture`, Values). Inside one net both are bounded:
the net's reach-and-sweep from its interface is the backstop that
collects a leaked cycle, and a count that would saturate can fall back
to a fan. *Inference*: this is the cheapest form of "cells at box
boundaries": a local cell that never needs the store because nothing
outside the net can name it. The net's data table already has the
ownership discipline ("an entry has one owner, is handed on when its
owner's value moves, duplicated when it is copied, freed when it is
dropped", `kprim.bend`); a counted entry is one more form.

**`Data(Net)` capturing a closed subnet.** Already the raw-net value;
new is making one from a running net. Statically, the front end knows
which boxes are closed and can emit them frozen at compile time (the
G-machine's supercombinators, Hughes 1982; GHC's CAFs for closed
top-level thunks), at no run-time cost, with their constants borrowed
rather than copied (`netdata-borrow`). Dynamically, a freeze is the
Cells plan's `cells-freeze` generalized from "the root faces a bind" to
"a port faces a closed subnet": reach, sweep, write out, with the level
base recorded (H8). Its cost is the walk, so it should be done once per
subnet and only where a value is leaving a net or being shared by a fan
that would otherwise duplicate lazily. Where it fails is the same as
3a: a subnet with free wires is not closed, and closing it allocates.

**Fork-join.** A `Data(Net)` with a demand on its port is the natural
spark: independent, closed, owned by whoever reduces it, its result a
value that crosses as data. That is the unit of work the rounds design
was looking for and did not have while the program was one net (H2).

## 4. Alternatives, unconstrained by the bootstrap or the sketch

Each: the idea, its mapping onto Bend 2, risks, a cheap deciding
experiment. Prior art is named where I am confident; "I believe" where
not.

**A1. The live net is the unit of exclusive ownership; recipes and
values are free data; claims are optimistic.** Replace pages with the
cell table split by *state*: `Recipe{Tpl}` and `Value{v}` are immutable
Bend `Data`, handed to any worker that may need them, by count, in
O(1); only a live net (`Busy`, an affine array) is held by one worker a
round. Two workers given the same Recipe may both force it; the
coordinator keeps the first result and drops the second (pure, so
identical: section 1's premise). This is GHC's lazy blackholing and
duplicate evaluation (Harris, Marlow, Peyton Jones 2005; sparks that
"fizzle" when their thunk is already forced, Marlow, Peyton Jones, Singh
2009), the Par monad's IVars written once (Marlow, Newton, Peyton Jones
2011), and Concurrent Revisions' per-task state merged at join
(Burckhardt, Baldassin, Leijen 2010), with the merge trivial because
cells are single-assignment. Bend mapping: the coordinator holds
`Array<Cell>`; a round's dealing takes each worker's live nets out
(`Array.swap` with a placeholder) and puts them back; recipes and
values are read and copied. No `@unsafe`; laws as the plans state them
(a cell only moves forward, written once, a round loses no net). Risks:
duplicated work on hot cells, bounded by fuel and by a claim bit the
coordinator sets when it deals a Recipe; the store array's split and
merge per round, O(tasks). Experiment: a stand-in coordinator over the
existing `KD` demand, on a chain of N cells each needing the next and on
a balanced tree of them, at n, 2n and 4n, counting rounds, idle fuel and
duplicated interactions.

**A2. Function values as closed, immutable templates first; shared
mutable function nets only if measured.** A frozen function is a
`Tpl` in a `Data(Net)`; an application splices a copy (Cells plan items
1 to 3); a partial application that leaves its net freezes again. No
store cell for functions, no collection of them, no freeze window to
wait on; sharing of post-freeze reductions is given up. HVM2's book of
closed definitions, expanded on demand and copied in O(1) because
closed (I believe this is how its `REF` nodes work), and the
supercombinator machines (Hughes 1982) are the precedents. Risk: it
narrows `functions-are-nets-with-arity`, a record; the maintainer
decides, not this review. Experiment: the Cells plan's differential run
already produces it: interactions of the ladder and the library under
"copy the frozen template" versus the static linker's inlined copies;
add one workload that partially applies an expensive function many
times, the case the record protects.

**A3. Close boxes in the front end: full laziness and lambda lifting,
cells only at the boundaries that remain.** Float maximal free
expressions to the nearest enclosing lambda (Peyton Jones & Lester
1991), lift local recursive groups (the Cells plan already plans this,
item 6), and emit closed boxes as compile-time `Data(Net)` templates.
What stays open after that are boxes capturing locals; for those, cut
each free wire at the boundary into a local counted cell (section 3b)
or, if it must leave the net, a store cell: the STG discipline, every
captured thing a heap object. The fan that copied the box now copies
handles. Bend mapping: all in `glam/lower.bend`, data only. Risk: more
cells, each a need; a box with many free wires allocates many. The
front end knows the count statically, so the policy can be a threshold.
Experiment: a static census over the ladder's lowered nets: boxes by
number of free wires (0, 1 to 3, more), before any run-time mechanism
is built.

**A4. Treat the coordinator as BSP and budget communication.** Valiant's
bulk-synchronous model (1990) prices a round as work plus the
h-relation (messages per worker) plus the barrier (10 to 20 µs here).
The design metric is then the *need rate*: cross-net needs per thousand
interactions. Mapping: count it in `KS.need`. Risk: none; it is
instrumentation. Experiment: the first number section 5 asks for.

**A5. Closed templates as cache keys.** A frozen `Data(Net)` is
canonical data; hashing it (nodes, links, table) gives a content
address for incremental and shared caching (`DistilledDesign.md`,
Performance), as Unison identifies definitions by hash. Live nets never
qualify, which is one more reason to freeze at boundaries. Experiment:
hash the frozen ladder samples twice across runs and check equality.

**A6. Parallel reduction inside one net.** `heap-strategies.rounds` in
HeapModel, kept tentative. Interaction nets are strongly confluent, so
reducing many pairs at once is deterministic; but demand to WHNF is one
path, so this helps only eager strategies on build-only pairs or
accelerated bulk operations, and in pure Bend it means partitioning a
net's array (measured four times slower per interaction,
`net-nodes-double`). Deprioritize behind A1 to A3; the record already
says parallelism inside a net comes from accelerated operations.

## 5. Recommendation

**Decide now, at plan level (the Cells plan is undecided, so these
touch no record).**
1. `Busy` carries its owner; a cycle is a need on an ancestor in the
   waits-for graph (H1). Write it so before `cells-data`, even though
   the first build has one stack.
2. The protocol's state is a task, the single stack its first container
   (H4).
3. Boxes are closed in the front end where they can be; a run-time
   freeze is for the rest (A3). Item 8 of the Cells plan gets its design
   round with this as the starting point.

**Propose now, at record level (each touches a record, so each is the
maintainer's to decide; this review only argues for them).**
1. The exclusive resource is a live net, never a page; recipes and
   values are shareable data (A1, H3). This changes
   `rounds-of-coarse-work` ("Pages of the store are owned linearly, so
   parallel workers must each hold the pages they touch") and
   `split-heap`'s consequence on partitioning: the rounds stay, pages
   become at most an allocation unit for cells, never an ownership unit
   for scheduling; `store-pages`' handles are unaffected.
2. A new record: sharing is a cost goal, so a pure cell may be evaluated
   twice and the second outcome dropped (section 1). Its precondition:
   no evaluation step mints an identity that depends on how many times
   it ran. `anno 'scope_unique` "wraps a given atom with unique
   metadata. If ever we compare the same atom with different metadata,
   we diverge" (`docs/Syntax.md`, line 866), and objects made at run
   time get "a request to the core for fresh cells" (Cells plan, item
   7). Both stay safe under duplication only if a mark or a fresh handle
   is a function of the forcing cell's handle and the ordinal of the
   mint within its evaluation, never of a global counter: then two
   evaluations mint the same identities, and a dropped duplicate leaves
   nothing behind that differs. The record should say so, and a law
   should hold it.
3. Whether `functions-are-nets-with-arity` stands as written or is
   narrowed to "a function is a closed template and its arity; sharing
   of reductions before its freeze" (A2), after measurement 3 below.

**Measure first, in this order.**
1. The need rate on the ladder under cells: cross-cell needs per
   thousand interactions, and the depth of need chains (A4). High, and
   no ownership scheme saves rounds, so the answer is fewer, coarser
   cells; low, and pages were never needed.
2. The closed-box census of the lowered ladder (A3): how much
   `Data(Net)` buys at compile time.
3. The template-copy differential (A2): interactions with frozen
   templates versus the linker, plus one partial-application workload.
4. Rounds over cells on a chain and a tree (A1): round count, idle fuel,
   duplicated work.
5. One measurement of the per-read atomic on data every lane reads (H9).

**Keep open.** `netdata-structures` (lists as nodes yes, dicts
doubtful); cursors; intra-net parallel reduction (A6); the concurrent
collector; the handle width; where reflection addresses nested nets.

**What I am least confident of.** That duplicated evaluation never
changes a result: it rests on errors being uncatchable and divergence
unobservable, both stated, but a future `try` over errors would break
it, and so would any identity minted by evaluation count (unique-atom
marks, fresh handles) unless they are derived as proposal 2 says; I
could not verify from the docs how marks are derived today. That HVM2's
`REF` works as I describe. And that the member boxes of objects have few
free wires, which the census settles.
