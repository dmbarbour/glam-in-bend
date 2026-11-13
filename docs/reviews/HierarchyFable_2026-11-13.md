# Hierarchy (second reviewer) — 2026-11-13

Written by a Fable sub-agent as the second reviewer, at the maintainer's
request relayed by the agent (2026-11-13), independently of the agent's
own review, which it did not read. Line numbers are of commit `22f1ff0`
(`main`). While this was written the working tree held uncommitted edits
to seven files (`git status`: `glam/core.bend`, `glam/materialize.bend`,
`glam/freeze.bend`, `glam/main.bend`, two tests and the Cells plan), and
`results/build/glam` was built from that tree, which is why its `--count`
prints a "cursor interactions" column that HEAD's `glam/main.bend` does
not; those edits are cited as uncommitted, without line numbers. Each
finding ends with a verdict: keep, adjust, replace, or open question.

## (a) A two-way glossary

**F1. "Hierarchical heap", "cells allocated locally".** The image exists
at one level of the build and not at the next. The kernel's net is a
heap of its own: `H{w: KM.M, a: Array<V.Val>}` (`spike/kprim.bend:158-159`),
"a net as four-word nodes in storage that doubles, its free list and
active pairs, and a data table of its own, kept linear" (`:6-8`), with
"node references ... indices local to their net" (`net-nodes-double`,
Consequences). Every live net, a cell's or a source, allocates its nodes
and its values locally, and a serve's fresh nodes are popped from the
host's own free list (`S.sp.nodes`, `glam/splice.bend:91`). What is not
local is what a net names outside itself: the book, one flat
`List<&2, Ent>` indexed by a `U32` handle (`glam/core.bend:48-53`,
`book_get` at `:258`), and the sources, one flat linear list `Srcs`
indexed by place (`:59-65`; `srcs.take`, `:348-357`, walks `i` cells).
A net reaches another net only through these: a leaf holds a book
handle, and a ring's situating node holds the source's entry in its
word 2 (`use.situ`, `:554-557`, writes `k` there). The root owns every
cell, as the re-scoping says: "owned by the root heap and named relative
to it, never with a meaning global to the run"
(`docs/plans/Cells_2026-11-09.md:30-32`). Nothing nests statically. What
is hierarchical is dynamic: the stack of frames, each serving into the
task below it (`glam/core.bend:371-380`), and the chain of cursors, a
copy's ring pointing to a source whose own rings point deeper, "the deep
cursor chained through the source between" (`glam/freeze.bend:54-57`).
The rings make a net's imports explicit: the situating nodes of a net's
rings name exactly the sources it depends on. That graph is a DAG, not a
tree: in `nested_sources.g` every `g{i}` holds a copy of the one `p`
(`samples/sharing/nested_sources.g:3-8`). Cheap to close later: the book
and the sources as one array of entries, each holding its net (the
Positions review already asked for "the book as an array",
`docs/reviews/Positions_2026-11-11.md:205-207`). Costly: a handle's
meaning. A handle inside a net, a leaf's `VLazy` or a situating node's
word 2, is relative to the one root; a tree of heaps needs it relative to
the holding net and rebased when a value moves, the heap review's A6
(`docs/reviews/Heap_2026-11-09.md:287-289`). Verdict: keep, and say the
difference in the plan: the image is a tree of owners, the build is one
owner with a dynamic chain.

**F2. "Ownership transfer to the parent", "linear transfer to another
net".** One transfer exists: a cell's net that ends as a function moves
whole from the task that reduced it into the sources, `cell.out` to
`srcs.push(ss, h, 0)` (`glam/core.bend:940-945`), its entry becoming
`ESrc{i, t, name}` (`:925-930`). That is a move from a task to the store,
never to a parent net. From a source into a host nothing moves:
`materialize` copies "the finished tree at node base v of source s ...
into host h" (`glam/materialize.bend:277-281`), and the source keeps the
nodes for its life (`copied-nodes-untouched`, Consequences: "A copied
node keeps its slot, its kind and its ports while its source lives").
What moves between nets is wires: a join replaces two cursors "by one
wire between what each faced" (`:188-191`). A linear transfer, the
source's finished tree moved rather than copied, needs to know that no
other copy will ever ask for it. Nothing records that: `ESrc` holds no
count of uses or rings, and the book keeps the entry for the run. Cheap:
a count of rings made from each source, bumped at `use.situ` (`:554-557`)
and where a copy of a source is itself copied (`fz.port.c`,
`glam/freeze.bend:54-60`). Costly: liveness, knowing a leaf will not be
demanded again, the collector over rings the plan defers (`.ring`,
`docs/plans/Cells_2026-11-09.md:1003`). Verdict: open question; nothing
today is a transfer, and the first step toward one is the count.

**F3. "Cursor interaction", `AnyNode >< Cursor`.** No rule in the table
does it. `KCur` is a kind (`spike/rules.bend:63`), and the walk stops
when its last node's negative principal meets a kind-18 node: "a need,
as a lazy handle met is, its node found again by d.at when served"
(`spike/kdemand.blend:317-326`, state 2). The core then pushes a frame
(`need.k`, `glam/core.bend:626-634`). The maintainer's interaction is the
serve: positioned demand at the cursor's position, then the whole
finished tree frozen, spliced at the offset, and every wire leaving it
joined or given a new cursor (`glam/materialize.bend:23-37`). It is one
batch, replacing one cursor by many nodes "with new cursors behind"
them: the maintainer's picture summed over a tree. Positive cursors never
interact (the Joins review's second rule,
`docs/reviews/Joins_2026-11-11.md:50-58`). Verdict: keep the batch; count
it per node (part d).

**F4. "Re-entrant access", "releasing walks".** Built as `release`
(`glam/core.bend:481-493`): every `TkSvD`, a frame holding its walk and
with it its source's net, from the top of the stack down to the first
cell's task, becomes a `TkSv`, its net put back among the sources and a
stop counted (`rl.d`, `:474-479`). It runs in two places: when a frame
is pushed to serve a source that a frame below holds out
(`frame.push.o`, `:526-531`, through `srcs.in`), and when a cell must be
forced above frames (`frame.wait`, `:673-678`). The maintainer's rule,
"kill the existing walks upon re-entrant access to a net", is applied
more coarsely: every kept walk on the chain dies, not only the one in
the re-entered net. The plan says why for the cell case: "else the
cell's work, using one of those sources, finds it out and fails"
(`docs/plans/Cells_2026-11-09.md:1090-1095`). The frame case could
release only the frame holding source `k`, since the stated invariant,
"A frame keeps its walk only while every task above it is a frame"
(`glam/core.bend:382-383`), still holds for the frames above it. The
cost is small on the samples (`hello_nested_wait.g`: 3 source stops, 5
steps walked again, my run). Verdict: keep now; narrow if stops grow (F9
shows where they would).

**F5. "Self copy".** Decided (`self-copies-are-cursors`), not built: a
source's walk meeting its own leaf still splices its recipe, `frame.src`
with `other` false (`glam/core.bend:662-671`), and the plan's
`.nested.self` is tentative (`docs/plans/Cells_2026-11-09.md:1126-1136`).
The code shape resists it in two places: `serve(s, h, ...)` and
`materialize(s, h, ...)` take two affine nets
(`glam/materialize.bend:382-386`, `:277-281`), and a frame whose host
holds the same source would meet `SrcOut`, "a live source served twice
at once" (`frame.t`, `glam/core.bend:832-839`). F10 has the detail.
Verdict: adjust, as the step says.

**F6. The jargon as built, read back.** *Book*: the entries by handle,
`Ent` (`glam/core.bend:40-53`). *Store, sources*: `Srcs`, the live nets of
function-valued cells, one taken out for a step and put back
(`:55-65`). *Frame*: `TkSv{k, nc, pos}`, a task serving negative cursor
`nc` at position `pos` of source `k` into the task below; `TkSvD` the
same with the walk it keeps in its source (`:67-77`). *Serve*: one pull
of one cursor's value from its source into the copy that holds it:
positioned demand, then materialize, join or static
(`glam/materialize.bend:382-386`). *Ring*: a copy's cursors in the host,
linked through word 3, with one situating node (form 2) holding the
source's handle and the copy's level offset (`:14-21`). *Situating
node*: that node, made at a use (`use.top`, `glam/core.bend:559-561`,
with the applying node's level, `S.sp.by`). *Positioned demand*: the
kernel's walk started at a finished node's port rather than at the
interface, looped until a value, the frontier, a cursor or a static
faces the position (`glam/position.bend:8-31`). *Host*: the task a frame
serves into, of three kinds, `Hb` (`glam/core.bend:741-747`). *Release*:
F4. On the maintainer's question: nothing about serving is configured.
`sharing.txt` states, per family, how many live sources a use passes
through (`sources=2`, `glam/sharing.txt:9-11, 18`) so that the families
check can bound serves per use at `SLACK_SERVES` times that number
(`scripts/ladder.py:69, 275-276`): a use of `g{i}` pulls once from `g`'s
source and once from `p`'s through `g`'s copy. The number is a property
of the family the script cannot see, so it is written beside it. It
exists only because a serve is no interaction; part (d) makes it
unnecessary. Verdict: replace the `sources=` mark by counting (F15).

## (b) The stack, the frames and release

**F7. The invariant that makes one stack safe is held by the push sites,
not by the type.** `Stk` is a list of `Tk` in any order
(`glam/core.bend:79-83`). The protocol needs "A frame keeps its walk only
while every task above it is a frame" (`:382-383`): a kept walk holds
its source's net inside the task (`TkSvD{..., d}`, the net in `d`), so
anything above it that wants that source must find it out and release
it. I checked the sites that push. A cell's task is pushed by `needed.e`
(`:607-608`) from a cell's own slice, so the top was a `Tk` and, by
induction, nothing below keeps a walk; and by `frame.wait` (`:673-678`),
which releases first. Frames are pushed by `frame.over` (`:533-538`)
over a host that is a `Tk`, a `TkSvD` or a `TkSv`, all allowed. The
guards that would catch a breach are errors: "a value forced for a frame
going on" (`finished.v`, `:907-908`; `finished.src`, `:920-921`) and "a
live source served twice at once" (`:838-839`, `:862-863`). Verdict:
adjust, to a shape that holds it by computation: the stack as segments,
each a cell's task with the frames above it, `Stk = Nil | Seg{cell: Tk,
frames: List<Frame>, rest: Stk}`, where only the top segment's frames
may be `TkSvD` and a segment below the top holds `TkSv` alone. Pushing
a cell then has to convert the top segment's frames, which is
`release`, before it can close the segment; the guards become
unreachable and go.

**F8. Re-entrancy, three kinds, all handled on one stack.** (i) The same
source at another position, from above: `busy` scans the whole stack for
a frame at `(k, pos)` (`:393-417`), the host included (`frame.push.l`,
`:521-524`); a different position is served. (ii) The same `(k, pos)` is
a cycle, reported with the source's name (`frame.push.k`, `:509-514`):
`live_mutual_cycle.g` (`samples/invalid/eval/live_mutual_cycle.g:3-6`).
(iii) The source held out by a frame below: released, then served
(F4). This is sound for one stack by the argument the Positions review
adopted from its second reviewer: below its top a path is safe, and a
second walk into the same region shares the suffix and is a cycle
(`docs/reviews/Positions_2026-11-11.md:166-176`). Two things rest on it.
The busy key is a position, "a node a copy took and one of its ports"
(`copied-nodes-untouched`, Context); positions are stable today only
because the core runs plain demand everywhere, mode 0
(`K.demand_ev(0, ...)` in `pd.walk`, `glam/position.bend:102-104`;
`KD.Demand.demand`, `glam/core.bend:1022`; "0 plain ... 1 running events
... 2 collecting", `spike/kernel.bend:215-218`), with no events and no
collection, and fusion refuses marked controls; the mark the decision
names is "Not yet" (`glam/materialize.bend:39-41`;
`docs/plans/Cells_2026-11-09.md:1001-1002`). And `busy` costs the stack's
depth at every frame push; the count of tasks in flight per source that
would skip the scan (`docs/reviews/Positions_2026-11-11.md:190-200`) is
not built. Verdict: keep the protocol; build the mark before anything
runs events or collection in a source (R1).

**F9. Circular copies that are not cycles re-walk at every alternation.**
Take two function-valued cells whose work applies each other at
different positions, `even`/`odd` over a number, both live. A frame
serving `odd` into `even`'s source stops in `odd`'s walk needing `even`
(`frame.need.k`, `glam/core.bend:708-716`), whose net is held by the
frame below: `release` (F4), and a frame for `even` at a new position
goes above. One level later the same happens the other way, releasing
the new `odd` frame. Each level releases the one kept walk below it,
to be walked again from a position one level deeper, so a recursion of
depth n would cost up to n^2/2 steps walked again: the cost
`cells-freeze.rewalk` measured for one source
(`docs/plans/Cells_2026-11-09.md:1014-1016`) and then removed for needs
met on the spot (`:1022-1030`); here the need is a source held below,
which that fix does not cover. I have not run it. No sample has this
shape: `hello_nested_wait.g` waits through cells
(`samples/hello/hello_nested_wait.g:3-8`), `live_mutual_cycle.g` is a
cycle. Two remedies are in the plan already: following a deep cursor
straight to the deepest source, "allowed only once proved to lose no
sharing" (`:1122-1123`), which removes the intermediate frame; or
releasing only the frame holding the re-entered source (F4). Verdict:
open question. Add the family to `glam/sharing.txt` and read its stops
and steps walked again before choosing.

**F10. A cursor into itself: the decided case against the code.**
`self-copies-are-cursors` says: "The walk that needs it is reentered, so
it is released first, and the serve runs positioned demand and the copy
in one net" (`docs/decisions/self-copies-are-cursors.md:19-23`). Today's
path would not do that. `frame.src` (`glam/core.bend:662-671`) splices
the recipe when the leaf names the frame's own source; were it to call
`use.src` instead, the host would be `task.of(WhSv, d, k)`, a `TkSvD`
holding source `k`'s net (`:502-507`); `frame.push.o` releases the stack
below the host but passes the host beside it with its walk kept
(`:526-531`); and the new frame's step would find source `k` already
out, held in the host's walk or taken for a host without one, meeting
`SrcOut` (`frame.t`, `:832-839`; `frame.ho.t`, `:856-863`). So the self
case
needs three things: the reentered host released by construction, a
`TkSv` rather than a `TkSvD` from `task.of`; a one-net serve, which runs
positioned demand in `h` and then `freeze_tree` and the splice on the
same array (`mz.fz`, `glam/materialize.bend:269-275`, with the source it
returns being the host it writes); and a host of a fourth kind, or none,
the host being the net itself. The busy check then does what the
decision wants: `g = k (g id ++ "")` serves `g` at its interface,
positioned demand from the interface reaches the same application
facing the same cursor, `SvCur` (`:291-293`) pushes a frame at
`(g, iface)` over a frame at `(g, iface)`, a cycle (`frame.push.k`).
Divergence elsewhere stops at the slices' budget, as the decision
allows. One hazard is specific to the self ring: its cursors are keyed
by positions in the very net that positioned demand reduces, so the
stability F8 relies on is used in the same net, at once; the finished
mark is not optional there. Verdict: adjust, in this order: the mark,
the segment shape (F7), then `.nested.self`.

**F11. `SvCur`, a position facing a copy the source holds.** When
positioned demand ends at a cursor of the source (`PdCur`,
`glam/position.bend:38-39`), the core serves that cursor into the source
first, by a frame above "which keeps no walk, having none"
(`glam/core.bend:782-789`), and reports a positive cursor there as a
fault of the copies' layout (`:799-806`). That is the right place to
stop: the outer serve has read one position and lost nothing
(`docs/plans/Cells_2026-11-09.md:1066-1068`). Verdict: keep.

## (c) The inner-frame-write allowance, as a proof

**F12. What the proof must state.** The allowance in the code: a frame
takes the host's net out of the host's own `KD.D` (`frame`,
`glam/core.bend:876-888`, `h0` and `h1`), serves into it, and gives it
back with the host's `path`, `top` and `depth` as they were (`host.go`,
`:752-760`: `KD.d.go(h, path, top, depth, n)`); the walk's next step
reads `top`'s principal link first (`demand.go`,
`spike/kdemand.blend:454-463`: `P.rd(h, (top + 1 : U32))`). The claim
has three parts.

*The write set of a serve into host `h`*, read off
`glam/materialize.bend`: (1) nodes allocated fresh for the copy
(`S.sp.nodes`, `S.sp.links`, `S.sp.statics`, `:275`), popped from the
free list, the array possibly grown, which keeps indices
(`net-nodes-double`); (2) the link word of the one port each joined
cursor faced, `P.link_xx(h, u, w)` with `w` read from the cursor's own
port (`jn1.w`, `:193-195`; `jn.w`, `:180-182`; `mz.root.w`,
`:243-245`), and that cursor freed; (3) the ring's word-3 chain and the
situating node's word 3 (`rg.unlink`, `:132`; `rg.insert`, `:140`); (4)
for a static, an eraser written at the port the served cursor faced
(`sv.static.w`, `:347-349`). Nothing else in `h` is written. The source
`s` is read by `freeze_tree` and written only by positioned demand.

*What resuming reads.* The walk reads `top`'s principal link and goes
on; when it pops back it reads each path node's principal link in turn,
never an auxiliary link of a path node ("Only the path's last node can
be in a pair, the others facing auxiliary ports, so a rewrite there
leaves the rest of the path as it was", `spike/kdemand.blend:19-21`).
The path holds node bases (`:33-35`).

*The invariant.* After the serve, every node on the path keeps its slot
and its header; the principal link of every path node below `top` is
unchanged; `top`'s principal faces the copy's root, a joined wire's far
end, or a static. It follows from two facts about ports. A cursor is a
one-port node the walk never pushes: it stops the walk as a need
(`nd.cur`, `spike/kdemand.blend:317-326`, state 2 when `top`'s negative
principal meets kind 18), and `wk.push` pushes only a node entered by an
auxiliary port (`:205`); so no path node is freed by (2). A path node
below `top` faces an auxiliary port of the next with its principal, not
a cursor, so (2) never writes its principal link. A path node's
auxiliary port may face a cursor of the ring and be rewired by a join:
transparent, since the walk reads no auxiliary link of a path node.
`top`'s principal faced `nc` ("the data node a stopped demand waits on",
`d.at`, `spike/kstrat.bend:1383-1386`), the one port (2) rewrites on
purpose. A state that holds the whole claim by computation is not
available while the copy and the walk's region share one array. What
the shape already gives is the first fact, a cursor cannot be on a path
because it has one port, and the proof should lean on that rather than
on a guard. Verdict: adjust; state it as three lemmas, below.

**F13. Where it lives, and in what order.** The gate takes "every
PROOF.bend outside bench/, and one beside every LAWS.bend"
(`scripts/check.sh:55-60`), so `glam/LAWS.bend` with `glam/PROOF.bend` is
admissible now; none exists, and the kernel's laws import only `spike/`
(`spike/LAWS.bend:4-14`). Split by where each fact comes from:

- in `spike/`, the path law the Positions review's second reviewer
  proposed and "the kernel already assumes": a node on a demand's path
  below its top is in no active pair and is the outer peer of none
  (`docs/reviews/Positions_2026-11-11.md:183-185`), with its corollary
  that no kind-18 node is on a path. It serves `cells-freeze.rewalk` and
  the cell host alike: a cell's demand has kept its path across a serve
  since `cells-freeze.cells` (`HbTk`, `glam/core.bend:752-756`), so the
  allowance is older than nesting;
- in `glam/`, the write-set law, over a host-side function split out of
  the serve: today the serve interleaves the source's walk with the
  host's writes, and a lemma wants the host's writes as one function of
  a template, a cursor list and the ring (`mz.sp`,
  `glam/materialize.bend:264-267`, is nearly that). The law: for every
  port `p` of `h` that is not fresh, `link(p)` is unchanged unless `p`
  faced a node of `situ`'s ring; and every node of the ring is freed or
  still on it;
- the resumption lemma joins them, over `host.go`.

Mutants to keep beside it: a join writing the far end's partner (`u` for
`w` in `jn1.w`); `mz.root.w` freeing the copy's root instead of `nc`;
`release` skipped for `HbSvD`. The uncertainty: these functions are
`Array` and `KM.M` heavy, and proofs over such code have stuck before
(`docs/BendIssues.md`); the path law over the kernel's walk has
precedent (`net-demand-whnf`'s laws, `spike/LAWS.bend:92`). A law on
`main` is a commitment the maintainer must approve before it is
weakened (AGENTS.md, Laws), so a first law should claim the path fact
alone and list the rest as missing pieces, as `docs/Proving.md`'s "A
weaker law, and its missing pieces" asks. Verdict: adjust; the path law
first, in `spike/`, the write-set law once the host-side function is
split out.

## (d) Copied nodes as cursor interactions

**F14. What is counted today, and what the maintainer's count adds.**
`--count` reports interactions (every net's rewrites, the sources'
walks included through `SvOk`'s `n`, `cn.add`, `glam/core.bend:214-217`,
`:819-820`), splices, values forced, serves (one per `SvOk`, `:229`) and
the frames' stops with the steps walked again (`:235-239`). A copy's
size is invisible: "splices and serves are no interactions, so the size
of the copies is invisible to it, and only their number is bounded"
(`scripts/ladder.py:30-32`). The uncommitted tree adds the maintainer's
count: a serve's cursor interactions, the nodes it copied, or one for a
join or a static (a result `Mz`, `SvOk` with `m`, `cn.copy`;
uncommitted). What to count, precisely, under "the replacement of that
cursor by another node, often with new cursors behind it": one per node
copied, each a cursor replaced by a node, the new cursors behind it
being the next replacements; one per join, cursor meeting cursor, which
copies nothing (the identity's case, `sv.front.m`,
`glam/materialize.bend:339-343`); one per static given. Not the ring
searches (`rg.find`, `:97`, a walk of the ring for each wire leaving the
copy): that is lookup cost, worth a counter of its own if rings grow, as
the Joins review asked (`docs/reviews/Joins_2026-11-11.md:211-215`).
A splice is the same event from a template, a leaf replaced by the
template's nodes, which the linked run pays for by fans at one
interaction a node; counting a splice's nodes alike makes the two sides
commensurable. Verdict: keep the counter; add the splices' nodes.

**F15. The families' check with copies folded in.** I ran both families
at 4 and 8 uses from the uncommitted build, the families made in my
scratchpad as `scripts/ladder.py` makes them (`nested`, `:197-224`). Per
use from 4 to 8:

- `nested_sources`: 6 interactions, 2 splices, 3 serves, 4 cursor
  interactions; 28 linked;
- `partial_in_cell`: 4 interactions, 2 splices, 1 serve, 2 cursor
  interactions; 11 linked.

Folded, 10 against 28 and 6 against 11: inside `SLACK_ITRS` (`:67`, "at
most 8 interactions more than it does linked", `:22-23`) with room. So
the serve bound and `sources=N` (`:69`, `:275-276`;
`glam/sharing.txt:9-11`) could go, the check reading one number. What I
did not measure is the splices' nodes, which F14 would fold in too;
`use`'s and `k`'s templates are small here, but the bound should be set
after that run, not before. The linked side is the honest baseline: a
definition "lowered into the net of each assembly that needs it, shared
within that net by fans" (`docs/plans/Cells_2026-11-09.md:42-46`), where
every node of a copy costs a fan interaction. Verdict: replace
`SLACK_SERVES` and `sources=` by the folded count; keep the breakdown
in `--count`.

**F16. Quotas.** Fuel meters walks, not copies: a cell's slice is
`slice()` steps (`glam/core.bend:211-212`, 2^20), a frame's serve gets
eight walks of a slice each of positioned demand (`:837`,
`M.serve(hs, h0, nc, 8n, slice())`), and `freeze_tree` with the splice
runs to completion whatever its size. Under `rounds-of-coarse-work`
("Fuel starts as one unit per logical step, however large the step"), a
serve is one step of unbounded size. Counting copied nodes as
interactions gives the natural charge: a serve costs its nodes, taken
from the slice's fuel after the fact, so a slice overruns by at most
one serve, which is bounded by the source's finished part. Interrupting
a batch copy is the hard case: the copy is atomic, nodes then links
then statics then joins (`glam/materialize.bend:275`), and a copy
stopped half-way would leave placeholders unjoined. Verdict: open
question, for the maintainer's tuning; charge after the fact now, chunk
only if a profile shows serves longer than a slice.

**F17. What `AnyNode >< Cursor` as an interaction implies.** As a kernel
rule, per node: the walk meeting a negative cursor copies the node at
its position, puts cursors on that node's free ports, and goes on; a
frame only when the position's region is unfinished. That is lazier
than the batch (a copy that erases part of the tree never pulls it; an
eraser meeting a cursor is a drop) and interruptible at every node. It
does not fit Bend's kernel: a rule rewrites one net, and the source is
another affine array the rule cannot hold at the same time ("one owner
for a net", `docs/reviews/Positions_2026-11-11.md:41-49`), which is why
the frame exists. The batch is the one grain that fits, and counted per
node it costs the same in the accounting as the per-node rule. The self
case is the exception, source and host one net, where a per-node rule
would be possible; but the one-net batch (F10) counts the same, and the
decision's "the finished tree frozen to a template, spliced back where
the cursor stands" (`docs/decisions/self-copies-are-cursors.md:21-23`)
is the batch. Verdict: keep the batch, count per node; note in the plan
that per-node pulls are a Bend constraint, not a design choice.

## (e) Adjustments in direction, by value

Each with what it costs to reverse later.

**F18. R1: the finished mark before `.nested.self`** (F8, F10). The busy
check, the joins and the self ring all key on positions, and positions
are stable today only because the core runs plain demand with no
events and no collection (F8). `copied-nodes-untouched` names the mark;
the self ring reads it in the net being reduced. Build the bitmap and
the three refusals (events, fusion, the collector's keep) before the
self serve, and a library entry that fails without it. Reversal: a
bitmap per source and three tests of it; removable in a commit.
Verdict: adjust the order of the plan's waypoints.

**F19. R2: fold copies into the families' check, retire `sources=`**
(F14, F15). Count copied nodes, joins and statics as interactions in the
check's one number, count a splice's nodes the same way, measure, then
set `SLACK_ITRS` once; drop `SLACK_SERVES` and the `sources=N` mark, and
keep serves and copies as columns of `--count`. Reversal: one script
and one line of `glam/sharing.txt`. Verdict: replace.

**F20. R3: the two laws for the allowance** (F12, F13). The path law in
`spike/` first, since it also carries `cells-freeze.rewalk` and the cell
host; then the host-side function split out of the serve, and its
write-set law in a new `glam/LAWS.bend`, with the three mutants. Reversal:
none for the split; a law on `main` is a commitment, so start with the
weaker claim and its listed missing pieces. Verdict: adjust.

**F21. R4: the stack as segments** (F7). A cell's task with the frames
above it as one value; `release` the segment's operation; the two
"forced for a frame going on" guards and "served twice at once" go,
proved unreachable by shape. Do it before `.nested.self`, which adds a
fourth host relation. Reversal: a type local to `glam/core.bend`; the
guards return. Verdict: adjust.

**F22. R5: a family for mutual recursion through live sources** (F9).
Two function-valued cells applying each other at new positions each
level, in `glam/sharing.txt`, with its stops and steps walked again
read. Then choose: the deep cursor straight to the deepest source, or
`release` narrowed to the frame holding the re-entered source. Reversal:
a sample. Verdict: open question until measured.

**F23. R6: toward the hierarchical heap, without pivoting** (F1, F2).
Three cheap moves keep the tree open: no new names with global meaning
(the rings' positions are per source, a good sign; a book handle in a
situating node is the one global name, and it is already "relative to
the root"); the book and the sources as one array of entries, each
holding its net, so that a source's owner is one place; and a count of
rings per source in `ESrc`, the precondition of any linear transfer and
of collecting a source. What stays costly is a handle's meaning inside
nets, which these moves do not touch. The maintainer's picture, a net
with cells of its own, would then be an entry whose book is nested in
its parent's; the dynamic chain of frames is already the walk down that
tree. Reversal: cheap while the book is a few hundred entries.
Verdict: adjust, in that order, not before R1 to R3.

**F24. R7: no per-node pulls** (F16, F17). The batch is what Bend's one
owner per net allows; charge it per node and after the fact. Revisit
only if quotas need copies interruptible mid-serve. Reversal: none,
nothing built. Verdict: keep.
