# Freeze and templates: design review (Fable, 2026-11-21)

The second reviewer's review for `cells-freeze.nested.host.templates`, at
commit 2884596, written apart from the agent's. Read whole:
`docs/reviews/Freeze_2026-11-21.md`, `glam/freeze.bend`,
`glam/materialize.bend`, `glam/position.bend`, `glam/splice.bend`,
`glam/splice_copy.bend`, `glam/ring.bend`, `glam/serve_model.bend`,
`glam/splice_model.bend`, `glam/SERVE_LAWS.bend`, and the records
`copy-reduced-function-nets`, `finished-sources-freeze`,
`finished-trees-cached`, `early-evaluation-optimization`,
`copied-nodes-untouched`, `copied-controls-unfused`,
`splice-erasers-static`, `static-links-count-as-nodes`,
`self-copies-are-cursors`, `templates-spliced-at-level`. Read in part, by
search: `spike/kprim.bend` (headers, statics, the free list, the table,
the mark), `spike/knet.bend` (the loader's statics pass),
`spike/tpl.bend`, `glam/core.bend` (the book, sources, frames,
`--refreeze`), `spike/krules.bend` (where eraser nodes are made), the
Cells plan's `cells-freeze.*` steps, NetData's steps 5 to 9, HeapModel's
note on the bootstrap, my earlier reviews' idea 3, A5 and Q2.5, and the
records `net-demand-whnf`, `net-nodes-double`, `splice-frame-premises`.
Skimmed, comments only: `glam/SPLICE_LAWS.bend`. Not read: the walk's
state 7 in `spike/kdemand.bend`, `glam/ring_model.bend` beyond
`bases`.

Everything here is by reading: nothing was built or run. "Checked" means
I traced it in the code cited; "proposal" marks what is mine. Sizes and
costs are estimates to be measured.

Finding IDs: C1 (section 8), B1 to B8 (section 9), A1 (section 3, a
claim of the agent's account that the code contradicts).

## 1. The frozen form

**What the list form costs (checked, sizes estimated).** A serve builds
`Tpl{nodes, links, root, size}` and a crossing list, then interprets
them: a node pass that allocates and records each node's reference in a
map; a links pass that looks both ends of each link up in the map and
writes two words; a crossings pass that looks each hole up again. A
tree of n nodes with h holes and e statics has n + h + e list nodes and
n - 1 + h + e links or more. Counting a constructor's fields as words,
a node is about 6 (`Con`, `TN`, a kind, a payload), a link about 8
(`Con`, `TL`, two `TE` of two fields), a crossing about 6: near 14
words a node and 20 a hole, before Bend's own overhead. All of it is
built and dropped at every serve.

**Options.**

| Form | For | Against |
|---|---|---|
| Lists (now) | plain data, the laws exist | size; three passes; two maps; every tree edge spelled out and re-checked |
| Relocatable image | near a block copy | needs adjacent nodes, which the free list does not give (the maintainer); levels, table words and holes still need a pass over it |
| Bytecode, postfix (the agent's sketch) | tree edges implicit | the root is made last, so its target is linked after everything; children wait on a stack of references |
| Bytecode, prefix, one stack of open ports (proposed) | tree edges implicit; the root's target is the stack's first entry, so root and interior are one rule; a subtree is a contiguous span | wires between auxiliary ports need slots |

`net-nodes-double` already rules that a small evaluated function "is
compacted, or compiled to a short string, rather than kept as a net",
and the bootstrap had "Compiled nets (a reduced net as a list of
operator steps)" (`docs/plans/HeapModel_2026-10-27.md:214`). My Q2.5 of
`SpliceFable_2026-11-19.md`, links stored per node and port, aimed at
the same proof gain inside the list form; the prefix form gets it for
tree edges without rewriting `T.Tpl` for lowering, so I withdraw Q2.5
in its favour.

**Proposal: an instruction word is the header of the node it makes.**
A fragment is

    Frag{code: words, vals: values, +nodes, +holes, +slots, +maxlvl}

`code` is a sequence of `U32` in the densest immutable form Bend has
(to be measured: `List<&2, U32>` read once front to back may beat an
array). The machine has one stack, the **open ports**: references in
the host awaiting what hangs there. It starts holding one entry, the
root's target (B6: the port the replaced ring cursor faced). Each
instruction pops one port and attaches to it. At the end the stack is
empty.

| Word | Reads | Does |
|---|---|---|
| a node's header (kind below 32, not 6, 7, 18) | a payload word after it, for a control's offset, or a number of value form 1 or 3; the next of `vals`, for value form 0 | allocates, writes the header with its level field raised, links its principal to the popped port, pushes port 2 then port 1 where it has them |
| an eraser's header (kind 6 or 7) | nothing | writes the static in the popped port: no node |
| a cursor's header (kind 18, form 0 or 1 for its polarity) | one word, `src` | makes the hole at the popped port; it is crossing number k, the k-th hole in order |
| `BIND s` (a kind of 32 or more, slot in the field) | nothing | pops a port into slot s of the wire table |
| `USE s` | nothing | pops a port and links it to slot s's |
| `AT1`, `AT2` (only for nets that are not trees) | nothing | the next node attaches by its port 1 or 2, and pushes its other ports, its principal among them |

So:
- **Tree links** cost nothing: a child's parent port is on the stack.
- **Wires between auxiliary ports** inside the fragment (a variable to
  its use, `\x -> x`) are a `BIND` at the end met first and a `USE` at
  the other; `slots` sizes the table. This is the maintainer's "aux"
  stack; it must be indexed, since such wires do not nest.
- **Holes** carry `src`, the source's reference of the port, which the
  ring needs as the cursor's position. `far` is not stored (section 2).
  `neg` is the header's form bit, as in the heap (`cur.form`,
  `glam/ring.bend:148`).
- **Statics** are one word and no allocation, as `splice-erasers-static`
  has it, without a map entry.
- **Levels** stay as the source has them and are raised by the copy's
  offset at each node, as `sp.node` does. `maxlvl` lets one test before
  the run replace `P.too_big` at every node (a law: the test at the
  maximum implies it at each).
- **Data values** are the second sequence, consumed in order: the
  maintainer's "data table" stack. A cached fragment owns `vals`; a
  serve shares each into the host's table, or, under `netdata-borrow`,
  the host's nodes name the fragment's pool and nothing is copied.
- **The root** has no encoding: it is the first node, at its principal.
  Section 8 shows that is all freeze_tree ever makes.
- `nodes` lets the allocator grow once before the run.

With `AT1` and `AT2` the form also holds any connected net as a
spanning tree plus wires, active pairs included: a lowered template
(`ETpl`), a source frozen whole, a melt. I would build the tree subset
first and add those two when `cells-freeze.whole` needs them.

**Size and cost (estimates).** One word a node, two for a control or a
number, two a hole, one a static, one each wire end: about 1.3 words a
node against 14 or more, and nothing rebuilt on a cache hit. The splice
is one pass: per node an allocation, a header write, two link writes, a
push or two; no map, no second lookup of each end. I expect the run to
approach the allocator's own cost. What remains per crossing is the
ring's find (B5), which the form does not touch.

**The decode law, and whether lists stay the specification.** Yes, as
the model no code runs on the serve path:

- `decode : Frag -> Maybe<Tpl & crossings>`, a total fold with a
  simulated stack of ends, giving the list template with its nodes in
  instruction order, holes and statics in place where they are met (not
  after the nodes, as freeze orders them now; nothing depends on that
  order but a comment in `SV.root.ok`).
- `run_decodes`: for a fragment that decodes, running it on a heap
  equals `sp.links(links, sp.nodes(nodes, ...))` of the decoded
  template on that heap, then the crossings. Allocation order agrees
  because the node pass allocates in list order; link writes agree as
  sets, each port in one link. `splice-frame-premises` rules "Port
  uniqueness is no frame premise"; this keeps to it: uniqueness is a
  fact decode computes for the equivalence, not a premise added to the
  frame laws.
- `decode_ok`: a decoded template satisfies `SM.tpl.ok`, `SV.copy.ok`
  and section 8's root law. This is where the form pays in proof: a
  tree edge cannot name a missing node or a port past the arity, a hole
  has exactly one link at port 0 to the node that pushed its port, and
  no link can name the root's port. What is left to check is the wire
  table (each slot bound once and used once) and the stack ending
  empty, both computed by decode itself. AGENTS.md's rule applies:
  "Prefer state shapes in which an invariant holds by computation".

The serve's laws then carry over by rewriting with `run_decodes`, their
template premises discharged by `decode_ok`. Freeze's own law becomes
`decode(freeze_tree(h, v))` is some template, with the meaning of that
template against the heap (what it read is what is there) left for the
canonization work (section 7).

**Risks.** A bytecode interpreter in Bend may lose to the list passes
if clang stops folding it into one segment (AGENTS.md, Measuring:
`sharing.py`). `run_decodes` is a simulation between a stack machine
and two folds, a costly kind of proof here; prove it for the tree
subset only.

**To measure.** Words a node for both forms over the library's sources;
instructions a served node, lists against bytecode, at n, 2n and 4n
nodes a tree; the share of a serve spent in the ring.

## 2. The fragment cache

**What a cache hit must still do (checked).** A serve today is:
positioned demand (`Q.positioned`), which for an already finished tree
is two reads (`pd.peer`, then `pd.v` on the node's header); the freeze;
the splice; the crossings. Only the freeze's walk and read-back are
saved by a cache. The ring's work stays.

**`far` must not be cached (the main point of this section).** A
crossing holds `far`, "the port it faces in the source"
(`glam/ring.bend:244-250`), read when the tree is frozen, and
`R.cross` looks the ring up by it. Where the hole faced unfinished
structure, that structure has since been rewritten: the wire now leads
elsewhere, and the old port's node may be freed and its slot reused. A
cached `far` would then miss a cursor it should join, or, on a reused
slot that another copied node now occupies, join a cursor it should
not. So a fragment keeps `(src, neg)` for each hole and the serve reads
`far` from the source at `src + 1` when it runs: one read a crossing,
and the source must be in hand for a hit, which it is (the frame holds
it).

**A cached tree is not the tree a fresh freeze would make, and that is
sound.** The tree frozen at time t1 is maximal then; at t2 its holes
may face children finished since. A copy served from the cache gets
cursors there. A negative one is served later and finds a value. A
positive one facing a principal port is reached from the other side:
the copy's demand walks into the finished child, the walk ends at the
frontier, the climb finds the positive cursor's position and
materializes there (`sv.front.m`, `cl.go`). This is the path a copy
already takes when a child finishes after its parent was copied, so the
cache adds no new case. But the law is not "a hit equals a fresh
serve". It is: a tree finished at t1 is still a finished tree at t2,
and the materializer is correct for any finished tree hanging at the
position, maximal or not. That second half is worth stating on its own;
today's code is only exercised on maximal trees.

**Key.** Options: the position `pos`; the tree's root node `v`; a hash
of the tree's content.

- `pos` saves the two reads but misses the frontier's path, where the
  tree is found by a climb, not at the served position.
- `v`, the root's base, serves both paths. It is stable once a copy has
  taken the node, given the marks.
- Content, for sharing across sources: the hash costs the walk the
  cache exists to save. No.

Recommendation: key on `v`, within the source.

**Where it lives.** Options: in the book's entry; beside the source's
heap; in the heap itself.

- The book is "copied freely" and searched by index
  (`glam/core.bend:58-61`); an entry rewritten at each new fragment is
  a `book_set` a serve.
- Beside the heap, `SrcIn{h, frags}`: taken out and put back with the
  source, linear with it, dropped with it. A self-copy (`serve1`) needs
  the same table for its own net, so the table belongs to the net as a
  source, not to the frame.
- In the heap: a fragment is not node-shaped; no.

Recommendation: beside the heap, a map from node index to fragment.
With the bitmap of copied nodes (B3) the lookup is tried only when the
root's bit is set, so a first serve pays one bit test.

**What it stores.** The fragment of section 1: code, values, counts. On
a hit nothing is decoded or rebuilt.

**Space: a bound, then a policy.** If every serve at `v` uses the
fragment first frozen there, fragments never overlap: each copied node
is in exactly one, the one that first took it (by the upward closure of
section 8, a later tree never includes a node already taken). So the
cache holds at most the copied part of the source once, at about 1.3
words a node where the heap holds 4. That is a bound without eviction:
**the cache is never more than about a third of the words of the
source's own copied nodes, and goes with the source.** Options for policy:

- **Cache at the first freeze.** Simple, the bound above. A source
  copied once pays for fragments nobody reads.
- **Cache at the second serve of a root.** The copied bit is "taken
  once"; a serve that finds it set and no fragment freezes and keeps
  one. Sources used once pay nothing. The second tree may be larger
  than the first, so fragments can overlap the first copy's later
  roots; the bound doubles at worst.
- **A budget and eviction.** Needed only if the bound proves too loose
  in measurement. An evicted fragment is frozen again on demand; that
  is safe because the heap, kept by the marks, is still the truth.

Recommendation: cache at the second serve; no eviction until measured.
The maintainer's concern about space is answered by the bound if the
measurements bear out the size estimate.

**Marks.** The cache needs the same thing cursors need: a copied node
keeps its slot, kind and ports (`copied-nodes-untouched`). The fragment
itself is a snapshot and would survive the node's reuse; the key `v`
and each hole's `src` would not. So the bitmap is a prerequisite, not a
companion (B3). The control marks already set by `fz.copied` must still
be written on the first freeze; a hit writes nothing in the source.

**Rings.** Unchanged (B5). If measured long, the fragment's dense hole
numbers give idea 3's array lookup; not before the measurement.

**Self-copies.** `materialize1` freezes then splices in one net
(`glam/materialize.bend:225-236`), relying on the template being a
whole snapshot before any write. A cached fragment is that snapshot
already. One care: a hit reads `far` words from the heap it is writing,
and a join may rewrite the link word of a port a ring member faced.
Read every `far` before the first write: a short list, and no
question.

**Laws (proposals).** `finished_stays`: a finished tree at `v` is
unchanged by any step of the source, given the marks; it is the
statement `copied-nodes-untouched` promises and nothing yet proves.
`serve_any_finished`: the serve's laws hold for a non-maximal finished
tree (I believe they already do, since they are stated over the
template; say so). `cache_same`: a hit runs the fragment `freeze_tree`
returned at the time of caching.

**To measure.** Serves per root, as a distribution (how many roots are
served twice or more); fragment words against source words; hits
against misses over the sharing families and the library; ring length
at each serve.

## 3. A wholly finished source becomes its cell's value

**Detecting it costs nothing (proposal, from the code as it is).** A
serve at the source's root (`at_root`, `glam/materialize.bend:165`)
freezes the tree at the interface. If its crossing list is empty, that
tree is everything the interface reaches, every node finished, no
cursor: the source is wholly finished and the `Fz` in hand is its whole
frozen template, up to the order of its nodes (A1 below; B2 does not
bite, since a cursor in the source would have made a crossing). So
`mz.fz` can return "whole" beside its count, and the frame sets the
cell's entry to the template. No extra walk, no flag kept in the heap.

That catches a source finished by the time a first copy takes its
root. Two more places, in order of cost:

- **A later serve empties the residue.** A serve off the root sees
  only its own tree. Cheapest: a serve that makes no crossing marks the
  source "maybe whole", and the next use at the root runs
  `freeze_finished` once; crossings clear the mark. One walk of the
  source for each false alarm, none otherwise.
- **The collector.** A collection's walk from the interface visits
  every live node (`spike/knet.bend:1562`); it can report whether it
  met a node whose principal does not face its parent, or a cursor. A
  source that collects learns for free. Sources do not collect today
  (B3), so this waits on the marks.

**A1. `freeze_finished` without cursors is not equal to `freeze`.** The
agent's F4 says it "leaves no cursor and equals `freeze`". The two
walks differ: whole, a node's three peers are pushed, auxiliary ports'
peers reached through any port (`fz.reach.q`, `:45-46`; `fz.ports`,
`:98-103`); finished, only principal peers of ports 1 and 2. On
`\x -> (x 5) 6` the whole walk pushes the outer application from the
function's port 2 and visits it second; the finished walk reaches it
only under the inner one, third. The templates are isomorphic, their
indices differ. Harmless for a splice; it matters to `--refreeze`
comparisons and to any key over templates (section 7). Proposal: one
walk order for both, the finished one, a whole freeze continuing from
the unfinished ends after it.

**What the cell holds after.** `ETpl{t}` in the book would make later
uses `S.splice`, the path templates take now, with no ring, as the
record asks. But stale cursors name the cell, and `frame.e` answers
"a cursor's source is no live source" for anything but `ESrc`
(`glam/core.bend:1065`). So either the entry stays `ESrc` with the
template added (`ESrc{i, t, name}` already has a `t`, the recipe "for
`--refreeze` alone", which the whole template can replace, plus a flag
that says new uses splice), or a new entry carries both. Recommendation:
keep `ESrc`, replace its `t`, add the flag. `--refreeze` then refreezes
the frozen value, which is the stronger test.

**Rings and cursors still held: three tactics.**

1. **Keep the source until no ring names it; the cell layer collects
   it.** A source is live while some heap holds a situating node with
   its handle. Count rings per source: up when a use makes a ring
   (`use.src`), down when a ring's last cursor leaves (the situating
   node then links to itself, a test in `rg.unlink`) or when the heap
   holding it is dropped. The second needs the cell layer to know which
   sources a heap names, which it must learn anyway for other partial
   values. Simple, exact for rings that drain, conservative for a
   long-lived host that never demands a cursor.
2. **Drain.** When a source turns whole, serve every negative cursor of
   every ring into it at once: finite, the source holding no cursor.
   It copies what demand may never ask for, and needs the cell layer to
   find the rings, as tactic 1 does. The bootstrap's "at most 64
   nodes" (`docs/plans/HeapModel_2026-10-27.md:212`) is a precedent
   for a threshold.
3. **Serve stale cursors from fragments, and free the heap.** When a
   source is whole and every node reached lies in a cached fragment,
   the heap adds two things only: which fragment roots at which
   position, and each hole's `far`. Read both once into a table (hole's
   `src` to its `far`, root's position to its fragment) and the heap
   can go; positions live on as names. This is "something particular
   to sources": it frees four words a node at once and keeps about
   1.3. It depends on the cache covering everything, so it follows
   `cells-freeze.fragments`.

Recommendation: tactic 1 now, as the baseline the maintainer leans to,
because the cell layer's collection is needed regardless and it changes
no serve; tactic 3 as the later step if sources held by old cursors
prove to cost memory in measurement; drain only under a small size
bound, if at all, since it is the one tactic that spends before demand
asks.

**Risk.** A cell's entry must not change while a frame holds a walk in
its source (`FdGo d`); the walk is finished or released first, as
`serve1` releases the walk it re-enters.

**Laws (proposals).** `whole_no_crossings`: a tree frozen at the
interface with no crossings equals `freeze` of the net, once A1 gives
both one order and B1 is fixed.
`whole_splice_serve`, that splicing the whole template equals a ring
served to exhaustion up to addresses, is hard and should not block
`.whole`; it is the honest reason to want canonization (section 7).

**To measure.** How many sources are whole at their first root serve,
over the library and the ladder; sources alive at the run's end, their
words, and rings still open on them.

## 4. Early evaluation and the collector finding nets to freeze

**What an opportunity looks like.** A source is a function's net after
weak head normal form (`net-demand-whnf`): a `Fn` at the root, its body
unreduced. Three places could finish it without being asked:

1. **At the cell's outcome** (`cell.src`, `glam/core.bend:1183-1194`):
   before the net is filed as a source, reduce it under fuel. This is
   the maintainer's "eager evaluation of the function's net, reducing
   all active pairs", made bounded.
2. **At a root serve that finds residue**: the serve already knows the
   source is not whole (section 3). It can spend a bounded amount on the
   pairs behind the holes it just made, since a copy now exists that
   may ask for them.
3. **At a collection**: the walk meets the remaining pairs; it can note
   how many, and reduce them if few. This is "net-layer GC finding
   opportunities": the collector sees the whole net and nothing else
   does.

**The two blockers, made concrete (proposal).** The record: early
evaluation "stops where it might not end, under fuel, and before a
reflection task, which it does not emit".

- **No new task.** Early evaluation in a source never leaves its heap:
  a need (state 2) for a recipe, a busy cell, or another live source is
  a stop, not a force. Forcing another cell could start a reflection
  task or a divergent computation on the early path, with nobody having
  demanded it. So early evaluation is closed over one net: it reduces
  pairs whose both nodes are present. This is checkable in one place,
  the stop it treats as final.
- **No template splice.** A leaf naming a top-level function (`ETpl`)
  is present data, but splicing it early unfolds recursion without
  bound; fuel would stop it, after having grown the source by copies
  nobody asked for. Treat a template leaf as a stop too.
- **Fuel per source, spent once.** A fixed budget per source, in
  interactions, proportional to its size at filing (say a small
  multiple of its nodes: to be measured). Spent, the source is never
  tried again early, or early evaluation becomes a second scheduler.
- **Counts kept apart**, in a column of their own, or every baseline
  moves with the fuel constant.

**Which strategy.** Demand walks one path; early evaluation wants all
pairs. The kernel has eager strategies (`spike/tpl.bend:133-137`, the
seed of pairs "found by walking the store in node order"). Running a
different strategy in a source is what B3 warns about. Before any copy
is taken (place 1) nothing is copied, so any strategy is safe, events
and collection included; after (places 2 and 3) only one that respects
the marks. Place 1 is the cheap and safe one, and the natural spark
when parallelism arrives: a filed source is a linear heap with one
owner and no observer yet.

**The bootstrap.** I did not fetch it. The docs record a whole copy
"only when the source has nothing left to reduce and at most 64 nodes
reachable from its interface" and compiled nets "only on request"
(`docs/plans/HeapModel_2026-10-27.md:211-215`): a size threshold and a
compiled form. Neither says how it found nets to reduce early;
`cells-freeze.early` rightly reads the bootstrap first.

**Recommendation.** Build place 1 only, behind a flag, closed over one
net, with its own counter; measure how many sources it makes whole and
what it costs sources never used. Leave places 2 and 3 until the marks
exist.

**Risks.** Early evaluation moves fragment boundaries and every count
downstream, so differential runs compare outcomes, not counts. Work
done in a source never used is lost; the fuel bounds it. Law
(proposal): early evaluation of a source makes no entry busy and starts
no task.

**To measure.** The share of sources whole after place 1 at fuel n, 2n,
4n; interactions spent early against interactions later saved, by
source; sources filed and never used.

## 5. The melt of a single-use source

**Knowing a use is the only one.** Options:

- **A count on the cell at run time.** A use is a data node holding the
  cell's handle, and such nodes are duplicated by the net's own copy
  rule (`P.dup`, the Bend value shared, `spike/kprim.bend:1001`) and
  carried into every copy of a template or source. A true count needs
  a hook on each duplication and drop of a handle, across heaps, kept
  in the book. Costly, and it arrives late: the first use cannot know
  it is the last.
- **Linearity at lowering.** Sound only if the one leaf naming the cell
  sits where it is instantiated once: in the recipe of a cell forced
  once, outside every function body and every shared subterm of that
  recipe, since either can copy the leaf at run time. And the cells so
  related must form no cycle, or inlining unfolds what the busy check
  would report. Narrow, but static and free at run time.

**The mechanism.** "`freeze` whole, a splice, the source dropped" has
three faults: `freeze` loses the source's cursors (B2); a source with a
walk in progress cannot be frozen; and it copies a net, node by node,
to avoid copying. Proposal: **melt before anything freezes.** A cell
lowering proves used once is never forced on a task of its own: its
recipe is spliced at its use, the path `ETpl` takes today
(`needed.e`, `glam/core.bend:824-825`). No source, no ring, no freeze;
the host reduces it lazily where it is needed. The work is shared with
nobody because there is nobody. This is the maintainer's "melt into its
only observer" with the least machinery I can find.

**Risks.** A cell's identity in diagnostics and reflection disappears
if it is inlined; if cells are observable there, the melt must keep the
name. A value whose outcome is data, not a function, is computed in the
host's net and never becomes an `EValue` others could share; fine for
one use.

**To measure.** How many root cells are used once by this definition,
over the library; serves and cursors saved. **Law:** none in the
kernel; lowering's analysis wants a property test against a run-time
count of uses.

## 6. Statics and erasers

**As built (checked).** Four conventions meet:

- Freeze writes a static at a port as an eraser node of the opposite
  polarity, after the real nodes (`fz.era`, `:247`); an eraser node the
  heap really holds is read back among the real nodes.
- The splice maps any eraser's index to `P.era()` and lets the link
  write it (`sp.node_k`, `glam/splice_copy.bend:87`); the polarity
  freeze chose is never read.
- The loader makes eraser nodes, links them, then frees each and writes
  the static, except an eraser facing an eraser or a static
  (`ld.hq`, `spike/knet.bend:1234-1236`).
- Positioned demand serves an eraser node at the interface as the
  static, but not elsewhere (C1).

**Proposal: a static is an end, not a node.** In the list template a
link's end is a node's port or the static; in the bytecode it is the
eraser's header word that makes no node. Then:

- the eraser's polarity, the `eras` list, `kind_at`'s case 2 and
  `sp.is_era` go from the specification;
- an eraser pair cannot be written by freeze at all. It already never
  is: a pair is not reachable from the interface. The eager loader's
  count of one matters only for hand-written templates; lowering emits
  no erasers (`splice-erasers-static`). I would drop the loader's
  statics pass with the nodes it serves, and let a test template that
  wants a pair build it in the heap;
- freeze reads an eraser node back as the static end, the same value
  (`static-links-count-as-nodes`), so a net freezes alike whichever
  way it holds its erasers (section 7), and C1's fix is the same rule
  seen from demand: an eraser node at any position is the static;
- an erased root is a template with no nodes whose root is the static,
  which fixes B1's shape by having a way to say it.

**A caveat for `--refreeze`.** Freeze drops what the interface does not
reach, an eraser pair or any detached active pair. Under demand nobody
counts those (`static-links-count-as-nodes`); under an eager strategy a
refrozen net would count fewer interactions than its original. The
differential should compare demand's counts only, or say so.

**To measure.** Erasers per served tree over the library, and whether
any template in the book holds an eraser node after the change (none
should).

**Law (proposal).** Loading a template with static ends writes the
static in exactly the ports named and allocates `made` nodes: the
splice's law, with one case fewer.

## 7. Canonization and persistent caching

**Is freeze canonical?** In its walk, yes: order follows ports from the
root, not addresses, and a node's index is its place in that order
(checked; the visited map is keyed by address but only answers "seen").
In its output, not yet:

- an eraser held as a node and one held as a static freeze differently
  (section 6);
- `Fz` for a tree carries `src` and `far`, heap references: fragments
  are never canonical, and need not be;
- data values are copied as they are, and a `VLazy{h}`
  (`spike/val.bend:7`) is a handle whose number belongs to this run's
  book;
- levels are the source's own, relative to its depth 0, so two frozen
  functions agree only if lowered alike; fan sites in nets without
  levels are lowering's numbers (`fz.fan`, `:167`);
- the marks are invisible (`P.rk` masks them; freeze reads a control's
  field and offset word only). Good.
- `freeze` and `freeze_finished` order one net's nodes differently
  (A1), so "canonical" must name its walk.

So F5's "looks canonical" holds for whole templates of finished nets
with no handles, after section 6's change. A law worth having first,
because it is testable today with `--refreeze` run twice:
`freeze(load(freeze(h)))` equals `freeze(h)`. Today it fails where `h`
holds an eraser node, read back among the nodes the first time and as
a static the second, and for B1's root. Invariance under
renumbering a template's nodes is the real claim and harder; property
tests before a proof.

**What a persistent cache keys on.** Not the frozen result. The key is
the input: the lowered recipe and the keys of everything it names. The
frozen template is the value stored. Canonical output buys one thing,
early cutoff: a dependent need not rebuild when a changed input yields
the same template. That is why the maintainer's separation is right,
and it gives an order:

1. **Serialization first.** Any deterministic encoding of the section 1
   form, handles written as names (the agent's "names in a persistent
   cache, never addresses"). Needs only that decode inverts encode.
2. **Canonization later**, when early cutoff is measured to matter.

**References to unfinished nets.** A finished template may hold handles
to cells not yet forced, or to live sources. Stored, each is the cell's
name and its key: a dependency edge. On load it binds to this run's
entry for that name, forced or not; the stored template is valid while
the keys match. A cursor into another source is different: freeze makes
it a crossing, so the net is not whole and is not stored. Rule
(proposal): only a template with no holes is persisted, and every
handle in it is serialized by name.

**To measure.** My A5's experiment: freeze the ladder's samples in two
runs and compare; then the share of templates holding a handle.

**Risk.** A key that omits something evaluation read (a reflection
task's answer, an environment's fact) caches a wrong result;
DistilledDesign's rule that evaluation never depends on reflection is
what makes input keys sound, and worth citing in the cache's record.

## 8. Freeze's obligations to the serve's laws

What `freeze_tree(h, v)` builds (checked, `glam/freeze.bend:399-411`):
the walk starts with `v` alone on its stack, so `v` is always node 0 and
`n` is at least 1; the nodes reached are indices 0 to n-1 in the walk's
order; statics and holes take n to ne-1, numbered as the read-back meets
them; `size` is ne (`fz.tpl`, `:357`).

**`SM.tpl.ok`: holds, given a well-formed heap.** Every link end is one
of: `(i, p)` for a node reached and a port below its kind's arity
(`fz.peers`, at most three, `:319`); `(ne, 0)` for a static's eraser or
a hole (`fz.peer.k`, `fz.peer.v`, `:278-299`); `(v-1, q & 3)` for the
peer, a node reached, where `q` is not static so `q & 3` is below 3. An
eraser node read back as a node (kind 6 or 7, which `ev.*` rules make,
`spike/krules.bend:2393-2442`) has arity 1, so its own end is port 0;
an end naming it from the other side is port 0 unless the heap links an
eraser's port 1 or 2, which is corruption, not freeze's to exclude. So
`tm.k` (`glam/splice_model.bend:151`) is met at every end. Not checked
by freeze, and it should not be: a kind's arity against the port bits of
references to it is the heap's invariant.

**Nodes no more than the map's slots: holds.** The splice's map is
`[0 : U32^T.depth_for(31n, size, 0n)]` (`glam/materialize.bend:81`),
`size` is ne, the list has exactly ne nodes (n, then ne-n), and
`depth_for` gives the least d with 2^d at least `size`
(`spike/tpl.bend:47`). `size` is a counter kept beside the list, which
a law would have to prove equal to its length.

**`SV.copy.ok`: fails for one shape (C1).** `hole.end`
(`glam/serve_model.bend:64`) asks that a hole's partner be `node.at`,
kind 1, "a node no hole". Freeze links a hole to whatever node the wire
left, and that node can be an eraser node, kind 2 in `SM.kind_at`:

- The shape: a copy took `Fn` at the root while its body was unfinished,
  so the copy holds a negative cursor at `Fn`'s port 2. The body then
  reduces to an eraser node (kind 7) whose principal faces that port.
  The cursor is served: `pd.q.k` reads a principal port facing the
  position and calls `pd.v` with `root` false; `pd.v` diverts an eraser
  only "`root && ...`" (`glam/position.bend:128-129`), so this is a
  `PdValue`, and `materialize` freezes the tree at the eraser.
- The template: `Tpl{[TN{KEraN}, TN{KCur}], [TL{TE{0,0}, TE{1,0}}],
  TE{0,0}, 2}` with one crossing at index 1. `hole.end(1, 0, 0, ...)`
  needs `node.at(ts, dm, 0)`, and index 0 is an eraser: `copy.ok` is
  false. `SM.tpl.ok` holds.
- What the code does with it (traced): the node pass maps index 0 to
  the static, the link writes the static in the hole's word 1
  (`P.link_xx`, `spike/kprim.bend:441`), the crossing finds the served
  cursor at `far` and `join1` writes the static in the port the cursor
  faced. That is the right outcome, the same as `PdStatic`'s, with a
  placeholder allocated and freed on the way. So it is a hole in the
  laws' cover, not a wrong result.
- Reach today: latent, as far as I searched. In `spike/krules.bend`
  the plain eraser rewrites write statics (`rw.EraN.*`, `P.put_st`,
  `:1841-1863`); only the event rules `ev.*.p1` write an eraser's
  header (`:2393-2442`), and the loader leaves an eraser node only
  where it faces another eraser or a static. The
  core runs sources under plain demand (`KD.Demand.demand`,
  `glam/core.bend:1281`; `pd.walk` passes mode 0,
  `glam/position.bend:105`). The comment at `position.bend:121-127`
  knows the shape ("elsewhere freeze links it to a crossing first"); the
  premise does not admit it. It becomes live when events run in sources,
  which `copied-nodes-untouched` plans for.
- Fix (proposal): drop `root &&` in `pd.v`, serving an eraser node at
  any position as the static, as `PdStatic` does. Then `freeze_tree`'s
  `v` is never an eraser, every hole's partner is a kind-1 node, and
  `copy.ok` holds by the argument below. The climbed path
  (`sv.climbed`) needs no change: a climb starts at a node holding an
  auxiliary port and goes up, so it never ends at an eraser.

With C1 excluded, `copy.ok` holds: holes are distinct indices below
2^dm, so apart; a hole is `KCur`, a node; one link names it, at its port
0, written with it in `fz.peer.v`; its partner is the node the wire
left, reached, kind 1.

**`SV.root.ok`: holds, and says less than is true.** The materializer
is at the root only for `PdValue` at the interface, the node neither a
cursor nor an eraser (`pd.v`). The interface has one port, and `v`'s
principal faces it, so `fz.peer.k`'s `rt` branch sets `root` to
`TE{0, 0}`, never another end. Off the root, `root` keeps its initial
`TE{0, 0}` (`:368`) and nobody reads it. So for every tree freeze makes,
the root is node 0's port 0. Proposal: say so in the model
(`root.ok` as `rn == 0 && rp == 0` plus "index 0 is a node"), and drop
`root` from the fragment form (section 1).

**No link naming the root's port: holds at the root.** The `rt` branch
adds no link (`:302`). Off the root, node 0's port 0 is linked to a
hole, and `mz.root` does nothing, so the leave never overwrites it.

**`SV.dyn` is redundant, by definition.** `RG.bases(ns)` asks
`P.base(m) == m` of each member (`glam/ring_model.bend:251-256`), that
is, low two bits 00; `P.is_static` is low two bits 11
(`spike/kprim.bend:408`). So `bases(ns)` implies `dyn(ns)`. Proposal: a
lemma `bases_dyn`, and the premise `hdy` leaves the four laws: a change
to laws on main, though each only loses a premise the others imply, so
the maintainer's to approve.

**Obligations the plan's list omits** (checked to hold, but nothing
states them):

- `RG.unfound` at the root: no crossing looks for the interface's
  position. Holds because the one port facing the interface is the
  root, which makes no crossing.
- The crossings' `far` ends are distinct, each a different port of the
  source, so two crossings never join one ring cursor.
- `SM.made(ts)` equals the allocations: an eraser makes none. Freeze's
  `Fz.n`, though, counts eraser nodes read back as nodes among "nodes
  read back", so the serve's count of nodes copied (`Mz.m`, the core's
  `cn.copy`) is over by one for each. A count, not a fault.
- Upward closure: each tree a copy takes hangs from a port of a node
  the copy already holds (the served position, or the ring position a
  climb ends at). By induction the copied set contains every finished
  ancestor of its members, so no later tree re-copies a node the copy
  holds. Freeze relies on this and never looks at the ring. It deserves
  a law over the model before a cache is built on positions (section 2).
- A climb that ends without `done` (section 9, B4).

**Laws this section asks for** (proposals): `freeze_tree_tpl_ok`,
`freeze_tree_copy_ok` (after C1's fix), `freeze_tree_root` (node 0, port
0, no link), `freeze_tree_size`. Each wants a model of a well-formed
heap that the proofs do not have yet. Section 1 argues most of them
vanish with a form in which tree edges are implicit.

## 9. Other findings in freeze and the materializer

Each checked against the code; none was run.

**B1. Whole `freeze` of a net whose root is static gives a cursor
(latent bug).** `fz.start` pushes the interface's peer only if it is
reachable or the interface itself (`glam/freeze.bend:375-377`); a
static is neither, so n is 0 and `fz.written.k` returns the template
kept for "nothing finished": one `KCur` node as root, with a crossing at
the interface (`:366`). `fz.whole` (`:385`) then drops the crossing. So
`freeze(KN.load(Tpl{[era], [], TE{0,0}, 1}))` is a lone cursor node, not
the eraser: the round trip the header promises ("loading what is frozen
gives the net frozen") fails, and a splice of the result puts a cursor
with no ring in the host. Reach today: `--refreeze`
(`glam/core.bend:2476`) on a template whose root is an eraser, which
lowering does not emit (`splice-erasers-static`), so tests and
hand-made templates only; I found no such case in
`glam/test_freeze.bend`. It becomes live with `cells-freeze.whole` if a
source whose value is erased is ever frozen whole. Fix (proposal): in
`fz.written.k`, a static at the interface is the eraser template when
`all`, and the same for `freeze_finished`, where "nothing finished" and
"the root is void" are different facts.

**B2. Whole `freeze` loses every cursor the net holds.** `fz.port.c`
refuses kind 18 whatever `all` is (`:59-61`), so a cursor node is never
reached; its neighbour's port becomes a hole and a crossing
(`fz.peer.v`), and `fz.whole` drops the crossings. Nothing reads a
cursor's word 2 (its position), word 3 (its ring) or the situating
node. So `freeze` of a source that holds a copy of another live source,
or of itself (every recursive function, `self-copies-are-cursors`),
returns `KCur` placeholders with no ring, no source and no position.
Two consequences:

- F4 of the agent's account says that with "no active pair and no
  vicious circle, every node the interface reaches is finished", so
  `freeze_finished` "leaves no cursor and equals `freeze`". That needs
  one more condition: the net holds no cursor. A source waiting on an
  unserved copy of another source has no active pair of its own and is
  not finished. `freeze_finished` does report it (a crossing whose
  `far` is the cursor's port), so the check "no crossings" is right;
  the stated condition is not.
- `cells-freeze.melt` as planned, "`freeze`, a splice, the source
  dropped", is wrong for any source holding a ring. Section 5 proposes
  a melt that needs no freeze.

Also in whole mode, a cursor node at the interface is pushed by
`fz.start`, which does not test the kind, and read back as a bare
`KCur` node with the root at its port: again a cursor with no ring.

**B3. Only controls are marked; the rest of `copied-nodes-untouched`
is not built.** `fz.copied` marks kinds 10 and 11 alone (`:120-121`).
There is no bitmap of copied nodes, and no reader of one in events or
the collector; `glam/materialize.bend:41-43` says so ("Not yet: the
marks on copied nodes ... so a source must run no events, fusion or
collection near copied nodes"). The agent's account ("the marks keep
fusion, eraser events and the collector off copied ones") and
`finished-trees-cached` ("the marks keep eraser events, fusion and the
collector off copied nodes") read as if it were. What protects copied
nodes today is that the core runs sources under plain demand, with no
events and no collection (`glam/core.bend:1281`,
`glam/position.bend:105`). That is a property of one call site, not an
invariant: nothing stops a later strategy choice from breaking every
copy's positions silently. Proposal: build the bitmap before the cache
(section 2 uses it twice), and until then state the restriction as a
check, not a comment: a source's demand mode is fixed where sources are
made.

**B4. A climb that fails is served as a success.** `sv.climbed`
(`glam/materialize.bend:141-144`) ignores `done`. `cl.go` runs up to
1,000,000 steps (`:154`, and `:285` in one net), each a ring walk (`R.rg.find`), and if no
step finds a ring position it materializes the tree at whatever node it
stopped on and returns `SvOk`; the served cursor `nc` is then joined
only if some crossing happens to face its position. By the upward
closure of section 8 a climb in a well-formed source and ring always
ends, so this is the corrupt case, and `corruption-reported-when-cheap`
applies: `P.err_if(Bool.not(done), h)` on the host and no copy
(proposal). A climb that reaches the interface without a hit
alternates between it and the root node until the fuel ends, a million
ring walks, which looks like a hang; take the fuel from the source's
node count, as the ring's walks take the heap's words (`rg.fuel`).

**B5. A serve's cost grows with its ring, several times over.** Per
serve: `rg.situ` walks from the cursor to the situating node; each
crossing calls `rg.find`, a walk of the whole ring on a miss
(`glam/ring.bend:88`); each join or leave calls `rg.pred`, another walk
(`:123`), since the ring is singly linked; a frontier's climb calls
`rg.find` once a level. So a serve of c crossings into a ring of r
cursors costs about c·r reads, and a copy that takes a wide structure
piece by piece is quadratic in its frontier. The agent's reading that a
serve's cost "does not grow with the copies" is right, but it grows
with the copy's own open cursors, and a cached fragment's crossings are
found the same way. Measure ring lengths and finds per serve before
fixing the cache's design; if rings are long, the source-numbered
frontier of `CursorsFable_2026-11-10.md`, idea 3, gives an array lookup
per crossing.

**B6. The root placeholder is avoidable.** Off the root, the tree's
principal becomes a hole, a node allocated, linked, found in the ring by
`far`, joined and freed, to connect the tree to the port the served
cursor faced. In every serve the materializer already knows the ring
cursor the root will meet: `nc` for a value, the cursor the climb found
for a frontier. Proposal: the copy's root links directly to that
cursor's peer and the cursor leaves, as `mz.root` does at the source's
root. One uniform rule, "the root replaces a ring cursor", then covers
all three cases, `at_root` goes, and one allocation, one free and one
ring walk go with it per serve.

**B7. Two maps a serve, both arrays made fresh.** F1 names the freeze's
map, sized to the source's capacity (`:383`, `:403`). The splice makes
a second, sized to the template (`glam/materialize.bend:81`). For a
tree neither is needed for tree edges: a finished tree's node has one
parent, so the walk needs no visited set, and a parent's reference is
on the walk's stack when its child is made. Only wires between two
auxiliary ports inside the tree need a lookup, and a table keyed by
port reference, sized by the open wires, serves (section 1). Whether
`[0 : U32^d]` costs 2^d at each freeze or is shared lazily by Bend I
did not measure; measure before claiming F1's size.

**B8. Data values are copied through Bend values.** `fz.word` peeks the
value out of the source's table, the entry kept (`:182-184`), and the
splice puts it in the host's (`sp.tn`, `P.put`). Each serve of a data
node is a table read, a list cell and a table write, the Bend value
shared. That is correct, and it is where `netdata-borrow`'s question
lands; a cached fragment is the natural owner of such a pool (sections
1, 2).
NetData's other questions for freeze: the table "when the net freezes"
is the fragment's `vals`, compact by construction; structures as nodes
freezing "into ropes and dicts" (`netdata-structures`) would be a
rewrite of a finished spine into one value node before the read-back,
a pass of its own that I would keep out of freeze until those nodes
exist.

## Questions for the maintainer

1. C1: may `pd.v` serve an eraser node as the static at every
   position, not only the interface? It closes the one gap I found
   between freeze and `SV.copy.ok`.
2. B3: do you want the copied-nodes bitmap built before the fragment
   cache, with a check until then that sources run plain demand only?
3. Release: is tactic 1 (rings counted per source, the cell layer
   collecting) the baseline, with "serve stale cursors from fragments
   and free the heap" as a later step?
4. The melt: is splicing the recipe of a cell lowering proves used once
   acceptable, or must a cell keep an identity (diagnostics,
   reflection) that inlining would lose?
5. Statics as ends, the loader's statics pass retired, an eraser pair
   left to hand-built heaps: agreed? It revisits part of
   `splice-erasers-static` ("The loader keeps its statics pass for
   now").
6. `SV.dyn` follows from `RG.bases`. May the premise be dropped from
   the four serve laws (each then claims the same from less)?
