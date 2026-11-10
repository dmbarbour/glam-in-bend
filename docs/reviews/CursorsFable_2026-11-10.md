# Joining cursors in a live template's copy

Written by a Fable sub-agent on 2026-11-10 at the agent's request, as a
second, independent brainstorm on joining cursors; kept as written.

## The problem, restated

A copy of a function's net takes the source's finished nodes whole and
leaves a cursor wherever it cannot copy through
(`docs/decisions/copy-reduced-function-nets.md`; the draft mechanism in
`docs/plans/Cells_2026-11-09.md`, `cells-freeze.cursors`). The
maintainer's objection: the identity function's lambda has its body port
wired straight to its variable port, and the draft's walk leaves a cursor
at each, two cursors for one wire.

The kernel's lambda is a Fn node, ports `[+ fn, - result, + arg]`
(`spike/rules.bend`, header): port 1 takes the body's value, port 2 gives
the variable. In `\x -> x`, port 1 is wired to port 2. Neither is a
principal port, so neither end is "reached through a principal port
facing up", and the walk sees an aux-to-aux wire at both ends.

**A taxonomy, my inference.** From a finished node, an auxiliary port's
peer is one of three things:

| The peer is | What the copy needs |
|---|---|
| (i) an aux port of a finished node | a plain link between the two copied nodes |
| (ii) a port of an unfinished node | a cursor |
| (iii) the source's interface | the copy's root, as the splice links it today |

The identity is case (i), and the draft's bug is treating (i) as (ii).
`glam/splice.bend` already does (i) right for closed templates: it
places every node first (`sp.nodes`), then every link (`sp.links`),
aux-to-aux links included, through a map from template index to
reference. So the first thing to fix is not the cursor but the walk:
**"finished" is a property of the node, a fixpoint, not of the order the
walk reached it in**. A node is finished when its principal port faces
the interface or an aux port of a finished node. `\f -> \x -> f x x`
shows why: its inner application's result port is reached from the
inner lambda's body port first, through an aux-to-aux wire, yet the
application is finished (its principal faces the outer application's
result, whose principal faces the lift under `f`, whose principal faces
`f`'s variable port). A walk that decides at first contact leaves five
cursors in a net that has none.

Once (i) is handled, two cursors never sit on one wire: a wire with an
unfinished end has exactly one finished end, so exactly one cursor. What
remains is the join **across time**: a later materialization, bringing
newly finished structure out of the residue, reaches a port the copy
already holds. By polarity there are two kinds of position:

- **A negative position** (the copy awaits a value: a Fn's body port, an
  Ap's argument port, a merge's input). The draft's cursor: demand there
  is a task on the source. A data node holding a handle fits, and the
  need stop fires there today (`may_need` in `spike/kdemand.blend`: an
  application or strict call meeting table data).
- **A positive position** (the copy supplies a value into pending work:
  a Fn's variable port, a fan's or lift's output, as in `\x -> (g c) x`
  with `g` a leaf). Nothing can be demanded there; the copy's argument
  must never enter the shared source. The copy needs a placeholder with a
  negative principal, holding the argument's wire until the consumer of
  that argument becomes finished and is copied. Not a data node (positive
  port), not `KEraN` (demand would treat it as an eraser): an anchor kind
  of its own. My inference, and the answer to the plan's open question
  "a data node or a kind of its own": both, by polarity.

(The lifts are `KLift`, made by `X.ctl` in `glam/lower.bend`'s `edge`
with their principal linked to the variable side, `spike/nets.bend`;
verified, not assumed.)

**A claim that bounds the join table** (my inference; an invariant to
prove, not yet proved). Finishedness is monotone under source reduction:
a rewrite rewires only the external peers of the pair's aux ports, and a
finished node is never in a pair, so a wire between two finished nodes is
never touched, and a finished node stays finished. One hole: control
fusion after a rewrite composes a new lift into the one whose out port
it faces and frees the new one (`spike/net.bend`, `fl.fuse`: "p stays,
l goes"), so a residue rewrite can change a finished lift's offset after
a copy took it, and a later join there would lose a level. Fusion must
be refused across the frontier, or idea 3's boundary node sits between
them and prevents it. Hence a later
materialization can reach an already-copied node only at a port that
was a cursor position when that node was copied. The per-copy join table
is keyed by cursor positions, O(cursors), never by every finished node.
This is what "efficiently" can mean here.

Every idea below is judged on one question: how does materialization N
find what the initial copy or materialization N-1 placed in this copy?
And on what it needs from the kernel, since demand from a position is new
either way: a task starting at a cursor's peer walks the residue and
stops where it meets a finished node's port, which today reads as "a
variable demanded outside its function's body" (state 7, `fw.scan` in
`spike/kdemand.blend`) and must become "frontier reached, materialize".

## Idea 1. Nodes then links, placeholders by polarity, a per-copy table of positions (pull)

**The idea.** Materialize as the splice does: collect the finished set
from the start position (a fixpoint: a node is taken when its principal
faces a taken node's aux port or the start), place every taken node
raised by the copy's offset, then place every link. A link whose two
ends are taken is a wire. A link with one untaken end gets a placeholder
at the taken end: a data node holding a cursor handle at a negative
position, an anchor at a positive one. Each placeholder is recorded in a
table of the copy, keyed by source position (node, port). A later
materialization into the same copy, on reaching a source position in the
table, links the new node to the placeholder's peer and frees the
placeholder. Joins are pull-driven: they happen only when this copy
demands.

**Identity.** Fn is taken; the link (Fn,1)-(Fn,2) has both ends taken;
one wire, no placeholder. **`\f -> \x -> f x x`**: everything is taken,
nothing in the table, a whole copy, as the lowering's lifts under `f`
and `x` all face variable ports and never pair (`glam/lower.bend`,
header). **`\x -> (g c) x`**, `g` a leaf: `g c` is a need, an active pair
in the source; the outer application waits on its result, so both
applications are untaken. Fn is taken. Table: (Fn,1) → a cursor data node
D facing nothing yet (the copy's root faces Fn); (Fn,2) → an anchor A.
The copy is applied: beta links the argument to A. Demand reaches D: a
task on the source from (Fn,1)'s peer serves `g`, reduces both betas, and
stops where the walk meets Fn's variable port, state 7 reinterpreted.
The materialization from (Fn,1) takes the new structure, and its link
reaching (Fn,2) finds A in the table: link to A's peer, the argument.

**Cost.** Per copy: the finished region twice (nodes, links), as the
splice. Per cursor: a table entry and a placeholder node. The table is
O(cursors) by the restatement's claim. Lookup: a sorted small list or a
hash per copy; or no table at all, the placeholders of one copy threaded
through their spare word (a one-port node has words 2 and 3 free; a data
node word 3) and scanned, O(placeholders) per join, which is fine while
frontiers are small and costs nothing when a copy has none. Memory in the
source: none.

**Kernel.** An anchor kind (one negative port, a payload: `holds` must
place it); demand treating an argument meeting an anchor as no pair; a
cursor value in the data table (source handle, position, offset); a task
started at a position; the state 7 reinterpretation. The transient map
(source node → copy node) during one materialization is the splice's
map array, sized to the source: idea 2's stamps if that proves costly.

**Levels.** As the splice: every level raised by the copy's offset; a
cursor carries the offset, and a cursor into a source that is itself a
copy with cursors into a second source adds offsets, checked against
`lvl_cap` as the splice checks now.

**Open.** Where the table lives when a copy's placeholders are in a net
the collector may free (the table must go with them). Two copies of one
source in one net share positions: the key needs the copy's identity, or
the table is per copy by construction (the threaded list is). A source
with several demanding copies serializes on its task.

**Experiment.** In Bend over `spike/net.bend`: materialize the three
nets above and count placeholders (expect 0, 0, 2); reduce the source,
materialize again, and compare the result with reducing first and
copying whole (`spike/wiring.bend` models wiring for such a comparison).
Then a family with n, 2n, 4n cursors for the table's cost.

## Idea 2. Forwarding in the source, keyed by copy (push)

**The idea.** Keep the join table in the source instead: a side table of
the source, keyed by (copy id, position) → the placeholder's reference in
that copy's net. Cheney's copying collector keeps a forwarding pointer in
the old object so that every later reference to it finds the copy
(Cheney 1970; confident). Here the "old object" is a source position and
there is one forward per copy, so the table is a hash, not a word in the
node. The payoff is push: when a demand from any copy finishes a region
of the residue, the source knows every copy's placeholder at every
position the new region reaches, and can materialize it into all of
them at once, or lazily on each copy's demand as idea 1 does but with
the lookup on the source's side.

**Identity.** As idea 1, no entry. **The harder case, `\x -> (g c) x`
copied twice.** The source holds four entries: ((c1,(Fn,1)), (c1,(Fn,2)),
(c2,(Fn,1)), (c2,(Fn,2))). Copy 1 demands; the residue reduces once; the
source materializes the result into copy 1 and may do so into copy 2 at
once (push), joining each copy's anchor. Copy 2 then never asks.

**Cost.** Per copy: as idea 1 plus a hash insert per cursor. Per join: a
hash lookup. Memory in the source: one entry per (copy, cursor), living
as long as the copy, which is the hazard: a copy's net collected without
telling the source leaves stale forwards, a dangling reference into a
freed net or a reused slot. Needs epochs (a copy id never reused, the
entry ignored when the copy is gone) or a liveness rule in the
collector. Pushing eagerly also does work for copies that may never
demand the result, against `net-demand-whnf`'s pure demand; so push
should at most prepare, not reduce.

**Kernel.** As idea 1, plus the hash beside the source's net (the data
table pattern: an array in the net's record) and a copy id in each
cursor. Levels as idea 1.

**Where it fails.** A source outliving many short-lived copies
accumulates entries unless the collector reports deaths. A copy in a net
that itself is copied (a copy's placeholder duplicated by a fan) has two
placeholders for one entry: the entry must then be split, which the
per-copy table of idea 1 handles by the fan's rule on the placeholder
node and this one cannot see. I believe this last point is decisive
against keeping the table in the source.

**Experiment.** On `partial_in_cell.g` at 1, 2, 4, 8 uses
(`glam/sharing.txt`): how many live copies ever demand the same cursor.

## Idea 3. The source numbers its frontier: dense ids, boundary nodes

**The idea.** The source, not the copy, assigns each frontier position
a small dense id when it first becomes a cursor position, and keeps the
map position → id (a hash in the source, or a boundary node on the wire,
below). A cursor is then (source, id, offset), and a copy's join table is
an array indexed by id: O(1) joins, no hashing, no scan. Ids are
assigned once per position for every copy, so k copies share the
numbering. The finished part at freeze time is literally a template with
ports: nodes, links, and a list of (id, end), which `spike/tpl.bend`
nearly is already (`Tpl{nodes, links, root, size}` plus a port list), so
the initial copy is a splice. As the residue reduces, each newly finished
region is cut into a fragment the same way, with its own ports, cached in
the source, so the second copy to demand it splices the fragment instead
of walking.

**Boundary nodes, a variant.** Instead of a hash, splice a one-port
"port" node into every frontier wire of the source, holding the id in
its field. A port node facing a principal port is then the event "the
residue has reached id k": the demand walk stops there with no climb
through finished nodes and no state 7 reinterpretation, and the node
names the cut. Its rules: it pairs with nothing; the walk treats it as
a stop. It costs a node per frontier wire in the source and a kind in
the table, and every rewrite in the residue that rewires an external
peer now rewires the port node's wire, which is what we want.

**Identity.** The template is Fn with the link (Fn,1)-(Fn,2), no ports;
a splice. **`\x -> (g c) x`**: ports id 0 at (Fn,1), id 1 at (Fn,2). A
copy's table is a two-slot array. Demand at id 0 reduces the residue;
the walk stops at port node 1 (variant) or at Fn's variable port; the
new fragment has one port, id 1, cached. Every copy joins id 1 by index.
**A variable used twice through a fan, `\x -> (g c) x x`**: the fan is
finished (its principal faces the variable); ids at its two outputs;
the fragment reaching both joins both; the same fragment serves every
copy.

**Cost.** Per copy: a splice of the template, O(size); an array of
O(ids). Per cursor: one id. Memory in the source: the hash or a node per
frontier wire, plus cached fragments (which double the finished
structure: once in the net, once as a template, unless the net's nodes
are themselves the template, as idea 1 reads them).

**Kernel.** The port kind (variant), or the hash; fragment cutting; the
cursor value. Levels: as the splice, the fragment lowered at the source's
depth and raised by the copy's offset.

**Where it fails.** Fragments are cut once but a residue reduces only as
far as one demand asks (`net-demand-whnf`), so a fragment's ports lead
into a residue another copy may demand further: fragments are a cache
of the frontier at one time, fine, but a copy that demands a fragment
already superseded by a deeper one must take the deeper one or chain.
Boundary nodes change the source's net: proofs over wiring
(`spike/wiring.bend`) and the rules' linearity must admit a kind that
never interacts.

**Experiment.** Count frontier positions on the F2 families and random
terms from `spike/tools/terms.py`: how many, how dense, how often the
same position is a cursor for several copies. Dense and shared favours
ids; sparse and private favours idea 1.

## Idea 4. Pairs-only residue: cursor groups joined by the rule's external index

**The idea.** Narrow "unfinished" to the nodes of active pairs and needs
themselves. Everything else, including nodes whose principal faces a
pending result, is copied. Each pending pair in the source then has an
interface of at most four external wires (the aux ports of its two
nodes), and a copy holds a *group* of up to four cursors per pair,
indexed by the pair's external slot. When the pair reduces in the source,
its rule says where each external peer goes, including to another
external peer of the same pair: the kernel's `link_pairs` already joins
those at every rewrite ("takes every redex whose external peers include
its own ports: the identity function's body is its argument",
`spike/knet.bend`, header). A materialization of the pair's result into
a copy is the same rule applied to the group: new nodes copied, external
slot i linked to cursor i's peer, slot i to slot j linked cursor to
cursor. No table, no positions: the join is by index within a group.

**Identity.** No pairs; a whole copy. **`\x -> (g c) x`**: the need `g c`
is the only pair; the outer application is copied. Group: slot for the
need's result (facing the outer application's port 0 in the copy). The
need is served once in the source; its result, a function, materializes
into each copy's slot; the outer beta then runs per copy. **A pair whose
result is wired back into its own argument** (`(\y -> y) x`, the beta
linking Ap's argument to Ap's result): the two cursors are in one group;
the rule's link says slot 1 to slot 2; cursor to cursor, joined.

**Cost.** Per copy: the finished-by-this-definition region, larger than
idea 1's. Per pair: a group of up to four placeholders. Memory in the
source: none. Simplest join of all, and the cascade is bounded: a rule
makes at most a few nodes and a few new pairs, each with its own group.

**What it gives up.** Sharing. The maintainer's rule is that a pair
reduces in the source even when its wires reach the parameter, and that
"only what waits on an argument's data is done per copy"
(`copy-reduced-function-nets`). Under this idea a node waiting on a
*pending result* (the outer application above) reduces per copy, since
it is copied before the pair it waits on resolves. Reducing the source
first, the optimization `early-evaluation-optimization` names, recovers
the sharing where the demand is known; a copy taken mid-way does not.
The new pairs a rule makes also need groups in every copy that holds the
old group, a fan-out per copy.

**Kernel.** Placeholders by polarity as idea 1; a group as four
placeholders knowing their slot and pair; materialization reusing the
rule table's link spec (`R.rule`, `link_pairs`). Levels as the splice.

**Where it fails.** A pair that reduces to a long chain of new pairs
(a recursive function's body unfolding) drags each copy through the
chain, groups all the way: the sharing the live template exists for.

**Experiment.** `glam/sharing.txt`'s check at 4 and 8 uses on
`partial_in_cell.g` and `closed_work.g`, with the source reduced first
and not: the interactions per use must be flat for the idea to stand.

## Idea 5. Cursors as fans: joins by annihilation (the ports alternative)

**The idea.** Do not copy out of band at all. A cursor is a copy fan of
the copy's identity sitting on a source wire, and the join of two
cursors on one wire is what happens in every sharing graph when two fans
of the same duplication meet principal to principal: they annihilate
and their outputs cross-link. Lamping's algorithm and GAL (Lamping
1990; Asperti and Guerrini, *The Optimal Implementation of Functional
Programming Languages*; confident) duplicate a lambda exactly so: a fan
meets the lambda, yields two lambdas with a fan on the body side and one
on the variable side, and in the identity the two fans meet and vanish,
leaving each copy's body wired to its own variable. HVM's dup and sup
nodes do the same with labels (confident). The repo already pairs fans
by GAL levels (`lowering-uses-levels`), and `functions-are-nets-with-
arity` names "copy-copy pairing by duplication identity". In this idea a
function value held by a cell is wired into the applying net through a
fan at the applying level with lifts for the offset, and the copy
proceeds by interactions: a finished node is copied when a fan reaches
it, pending work is reached by a fan that cannot pass a pair and waits
for the pair to reduce, once, in the source. This is the review's
"ports" column (`docs/reviews/InsideData_2026-11-10.md`, "Weighed,
within a net").

**Identity.** Fan meets Fn: two Fns, a fan on the body wire, a fan on the
variable wire, the two fans meet, annihilate, cross-link: each copy's
port 1 to its own port 2. No lookup, by the rule table. **`\x -> (g c)
x`**: the fan copies Fn; the body-side fan reaches the outer application
by its result port, an aux port, and waits; the variable-side fan
likewise at the argument port. The need `g c` is served by demand
through the body fan (demand follows the fan's principal into the
residue); the betas run in the source; the residue becomes finished
structure that the two fans then copy, and where they meet they
annihilate: the join.

**Cost.** One interaction per node copied, as a splice is one node per
node, but through the rule table rather than a tight loop; plus the
controls: fans cross box boundaries and need brackets, the overhead
NetPairing measured (`docs/plans/NetPairing_2026-10-26.md`, n^1.7 with
levels against n^2.7 with unit brackets on its ladders). Memory: the
source is consumed and replaced by fans and copies in place; no second
representation. A copy that is dropped is erased by an eraser meeting
the fan.

**Kernel.** Nothing new: the rules exist. What changes is the model: a
function value is no longer a net of its own but a region of the
applying net reached through a fan; cells hold a wire into a shared net
rather than a handle to a separate one; the copy is not separate from
the source, which `copy-reduced-function-nets` assumes ("the source
stays live while any copy can reach it"). Levels are the mechanism, not
a bookkeeping field.

**Where it fails.** Across nets: a cell's net and the applying net are
separate stores, and a fan cannot span them; the sources would have to
live in one net, or the first use would move the cell's net in (a
splice of a live net, with its pairs). The sharing of pending work
across copies is then exactly GAL's, which is right but costs controls,
and which the kernel's demand (`net-demand-whnf`) serves one path at a
time, so a wide frontier copies slowly. It also gives up the batch: no
frozen form, no compact copy of finished data (`spike-materialize`).

**Experiment.** `spike/tools/terms.py` lowers `let f = <partial
application> in ... f a ... f b` with levels today: count interactions
and controls for 1, 2, 4, 8 uses against the splice route's counts in
the sharing check. It is also the oracle for ideas 1 to 4: a
differential run must find the same values.

## Comparison

| | 1 Per-copy table (pull) | 2 Source table (push) | 3 Dense ids, boundary nodes | 4 Pairs-only groups | 5 Fans |
|---|---|---|---|---|---|
| Join lookup | small list or scan, O(cursors) | hash in the source | array by id, O(1) | index within a group, none | the rule table |
| Memory in the source | none | an entry per copy per cursor | a hash or a node per frontier wire; fragments | none | the source becomes the copies |
| Sharing of pending work | the maintainer's | the maintainer's | the maintainer's | lost for what waits on a result | GAL's, exact |
| Kernel changes | anchor kind, cursor value, demand from a position, state 7 | idea 1 plus the hash and copy ids | idea 1 plus a port kind or hash, fragment cuts | placeholders, groups, the rule spec reused | none; the model changes |
| Hazards | table must follow the copy's net | stale forwards; a copied placeholder | superseded fragments; proofs over a passive kind | sharing; chains of pairs | controls' cost; one net; no batch |
| Decided by | counts at n, 2n, 4n cursors | live copies per source | density of frontier positions | the sharing check | NetPairing's counts |

## Recommendation

Build idea 1, in two halves. First the walk's fix, which is independent
of any cursor design and which the identity exposes: materialize as the
splice does, nodes then links over a finished set computed as a fixpoint,
so that a wire between two finished nodes is a wire. This alone makes
`\f -> \x -> f x x` a whole copy with no cursor, and is testable now
against reducing first and copying whole. Second, placeholders by
polarity (a cursor data node at negative positions, an anchor kind at
positive ones) with the copy's placeholders threaded through their spare
word and scanned at joins: no table to allocate, nothing in the source,
correct for a copy that is itself copied (the fan's rule duplicates the
placeholder, and each half is found by its own net's scan). Move to idea
3's ids only if the scan shows in the counts, which the restatement's
bound (joins keyed by cursor positions only) makes unlikely for the
frontiers the ladder has. Keep idea 5 as the oracle for the differential
run, and as the fallback the review already names should the mechanism
fail.

I do not recommend idea 2: the push it buys is work before demand, and a
copy whose placeholder is duplicated by a fan breaks its table. Idea 4 is
the quickest to build and the simplest join, but it gives up the sharing
the live template exists for; it is a fair second step only if the
source is always reduced first, which the maintainer made optional.

Before any of it, two invariants to state as laws, cheaply: finishedness
is monotone under reduction (a finished node stays finished, a
finished-to-finished wire is never rewired), and a materialization
reaches an already-copied node only at a former cursor position. The
second follows from the first and bounds every table above. The
experiment that decides the whole direction is the first half: a Bend
program over `spike/net.bend` materializing the three nets of the
restatement, then the F2 families, counting placeholders and comparing
with whole copies of the reduced source.

## Questions for the maintainer

1. Is a node whose principal faces a *parameter* (a fan or lift under a
   variable port) finished, copied and reduced per copy with the real
   argument? The draft's "facing up, toward the interface" reads so to
   me, and it decides that positive positions exist at all.
2. Does the copy's argument never enter the source, so that what consumes
   it is copied once finished, as the anchors assume? The alternative,
   a per-copy instance of the residue, is idea 4.
3. Did the Rust bootstrap join cursors, and how? The repo's record says
   only that pending pairs reduce in the source once for every copy
   (`docs/plans/HeapModel_2026-10-27.md`, "Nets"); I could not find its
   join, and a documented one would settle idea 1 against idea 3.
4. One demand task on a source at a time, as a cell has, with a second
   copy's demand a wait rather than a cycle?
5. A cursor into a source that is itself a copy: chain through it, or
   forward to the deeper source with offsets added?
6. Is a kind that never interacts (the anchor; idea 3's port node)
   acceptable in the rule table, with its proofs?
