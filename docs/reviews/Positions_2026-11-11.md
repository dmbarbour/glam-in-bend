# Positions — 2026-11-11

How a live template's source keeps track of the positions its copies
demand: busy state, its cost and representation, and how a demanded
position finds its way back to the cursor that asked. Held at the
maintainer's request (2026-11-11), on the proposal that cursor positions
carry busy states: "This 'should' seems implementation-dependent and best
answered by analysis, detailed design, brainstorming of alternatives. ...
Investigate it further, or have Fable do so. What does the busy state
cost? How is it represented and managed? How are we tracking needed
positions back to cursors?"

Two reviewers investigate independently: the agent, here, and a Fable
sub-agent, whose analysis is kept as written in
[`PositionsFable_2026-11-11.md`](PositionsFable_2026-11-11.md). The last
section compares them. The context is the Cells plan's `cells-freeze`
steps and the reviews `Cursors_2026-11-10.md` and `Demand_2026-11-11.md`.

## The problem

A copy's negative cursor names a position in a source: a finished node
and one of its ports, facing an unfinished region. When the copy's
demand reaches the cursor, the source is demanded at that position, and
the region reduces there once for every copy. Positions are demanded
while others are in progress in three ways:
- **Another position of the same source.** A walk at P stops on a need
  whose service demands the same source at Q. A body re-entering its own
  source, as a fold does, or two copies of one function calling each
  other, are legitimate and must not be cycles.
- **The same position, on the same chain.** The walk at P needs, through
  any number of steps, the same P: `f y = f (g y)`, where `f`'s body
  applies a copy of `f`, whose body is a cursor to that same P. This is a
  true cycle, and the program diverges under weak head normal form too.
- **The same position from another chain.** Only once tasks run in
  parallel: then it is a wait, not a cycle.

With today's single stack, every busy position is on the current chain,
so a busy position needed again is a cycle, exactly as a busy cell is
today (`EBusy` in `glam/core.bend`).

## A constraint from Bend: one owner for a net

A net is an affine array, and a task's demand holds it (`KD.D{h, ...}`):
today each cell's net belongs to the one task forcing it. A source, by
contrast, is demanded at several positions, possibly with one walk
suspended while another runs. So a source's net must live in its entry
in the book, and a task borrows it only while it runs. A walk that stops
on a need gives the net back, keeping only its own state: its position,
and perhaps its path.

## The hazard: several suspended walks in one net

Today each net has at most one demand walk, and the walk's path is safe
because "Only the path's last node can be in a pair, the others facing
auxiliary ports, so a rewrite there leaves the rest of the path as it
was" (`spike/kdemand.blend`). With two walks in one net that no longer
holds.

A walk at P may hold on its path a Copy fan, entered by one output and
waiting on its input. A walk at Q may enter the same fan by the other
output, reduce the shared value, and fire the fan's pair. That rewrites
a node on P's stored path. Resuming P from its stored path would then
read freed or rewired nodes.

Remedies:
- **Re-walk on resume.** A suspended walk keeps only its position. On
  resume it walks again from the position down the principal links,
  which costs the path's length, and finds whatever progress other
  walks made. The path is a cache, and this throws it away when the net
  has been lent out meanwhile.
- **Validate the path.** Keep a counter in the net's header bumped by
  every rewrite. A resumed walk reuses its path only if no other walk
  ran since it stopped, and walks again otherwise.
- **Serialize walks per source.** Not possible: P's walk may wait on
  Q's, in the same source.

Re-walking with a validity check is cheap and safe. The agent recommends
it, measured on the counts. (The second reviewer shows that this
example cannot happen as stated; see the comparison.)

## Representing busy state

| Where | Test | Memory | Cleared |
|---|---|---|---|
| a table of busy positions in the source's book entry | search the table, O(k) for k busy | one entry per position in progress | when its walk ends |
| the task stack, scanned | search the stack, O(depth) | none beyond the task's record | with the task |
| a bit for each port in the net | O(1) | 2 bits per node, beside the finished bitmap | reset when the walk ends |
| positions as cells made at run time | O(1), as a cell's state | a book entry per demanded position | the entry dropped once done |
| none | — | — | — |

Notes on each:
- **The table** is small, since k is at most the chain's depth through
  that source.
- **Scanning the stack** needs a task to record its source and position
  in place of the cell it computes.
- **The bit per port** needs the net, which a waiting task does not
  hold.
- **Positions as cells** reuse the cell protocol: busy, done, a cycle as
  a need on busy. A map from a source's position to the entry is still
  needed to find it.
- **None** leaves `f y = f (g y)` looping without a report, and a second
  demand of a busy position walking a region already in progress.

**Recommended for the single stack.** A task records what it computes,
a cell or a source position. A busy test scans the source's table of
positions in progress, kept in its book entry. That stores nothing in
the net, which the maintainer wants left alone, and costs one short
search per demand at a cursor. When tasks run in parallel, the table's
entries gain waiter lists, and a busy position on another chain becomes
a wait, with the ancestor test on chains.

## Tracking a position back to its cursor

This follows how a need on a cell is served today, with nothing new in
the kernel:
1. A negative cursor in a copy is a data node holding a handle: the
   source, the position, and the copy's level offset, as an entry in the
   copy's data table. Demand meeting it stops as at a need (state 2),
   its top the node facing the cursor (`may_need`; `d.at` in
   `spike/kstrat.bend` finds it again).
2. The core reads the handle, sets the copy's task aside on the stack,
   waiting on the position, and starts or joins the source's walk at it.
3. When the source's walk ends, at a value or the frontier, the core
   resumes the copy's task. It finds the cursor node again, frees it, and
   materializes from the position, raised by the offset, into the copy's
   net in its place, as a splice replaces a leaf today.

There is no index from positions to cursors. Each waiting copy knows its
own cursor, in its stopped demand, and the position's entry knows only
who waits on it. With a single stack, that is the task directly below.

## Costs

- **Per demand at a cursor:** a table search and an insertion, a push
  on the stack, the source's walk, and a materialization.
- **Per resume after the net was lent out:** a re-walk from the
  position.
- **Memory:** a table entry for each position in progress, and for each
  suspended walk its position, with its path only while valid.

## Experiments and laws

- **A law:** a walk resumed by re-walking from its position reaches the
  same next pair as one that kept a still-valid path.
- **Counts on the sharing families** once cursors exist: re-walks and
  their lengths, busy-table searches, cycles reported.
- **Library entries:** `f y = f (g y)` applied, expecting a cycle at a
  position; and a fold re-entering its own source at another position,
  expecting a value.

## Comparison with the second reviewer

The two agree on most of the design:
- a source's positions demanded while others are in progress, with the
  same position on the same chain a true cycle and another position a
  legitimate re-entry;
- a paused walk that re-walks from its position on resume;
- cursors as data nodes holding a handle, stopped on as needs are and
  served by a copy at the waiting task's top, as a splice serves a leaf;
- no index from positions to cursors, since each copy pulls its own
  result;
- waiter lists only once tasks run in parallel.

**The second reviewer corrects the hazard.** This review claimed that a
walk Q could fire a copy fan on a paused walk P's path. It cannot.
- **Below its top, P's path is safe.** Each node of P's path below its
  top faces an auxiliary port, so it is in no pair and is the outer peer
  of no pair. Rules, fusion, events and collection all leave it alone.
- **Q goes down the same way.** Entering the fan by its other output,
  Q descends through the same nodes and reaches P's own top, the same
  need: the two walks share a suffix.
- **With one stack that suffix is a cycle,** reported before anything
  is rewritten, since Q helps serve P's need and needs the same thing.

So walks cannot stale each other today. They can in two cases:
- **Cycle errors served into the net.** Once a cycle's error is served
  into the net as the Cells plan's item 6 proposes, Q resumes with the
  error, rewrites the shared suffix, and stales P.
- **Parallel chains** waiting on one need.

Re-walking from the position is then required, not optional. It is
cheap, a descent in reads of the path's depth, and collecting demand
already walks again after each collection. The second reviewer proposes
a law the kernel already assumes: a node on a demand's path below its
top is in no active pair and is no outer peer of any pair.

**Where the two differ on busy state.** This review proposed a table of
positions in progress in the source's book entry. The second proposes
storing nothing:
- **Done** is the finished bitmap: a finished position needs no walk,
  only a copy;
- **Busy** is that some task is at the position, found by scanning the
  task records, and only when a count of the source's tasks in flight,
  kept in its entry, is above zero.

That costs a scan of the stack's depth where this review searched a
table, and keeps only a count in the entry. The difference is small,
and the second is simpler. Adopted as the proposal: the scan is rare
and short, by the measurements to come.

**What else the second reviewer adds:**
- **A suspended walk keeps no path at all:** three words, its source,
  its position, and what it waits on. The rewrite counter becomes an
  optimization for later, if re-walks show in profiles.
- **The book as a list costs.** A suspension moves a source's net out
  of the book and back, each a `book_set` through a list. It asks
  whether the book may become an array before sources are many.
- **`VCursor` as a value variant** beside `VLazy` reuses `may_need`,
  `need` and `resume` unchanged; a node kind of its own would buy only
  a faster dispatch.
- **Pull, not delivery.** A waiter woken by the owner's end pulls its
  own result. Delivery to every waiter would need the observer table
  the Rust bootstrap regretted.
- **Experiments:**
  - how often cursor demands find a position done, busy, or new, and
    the depth of each scan;
  - how often positioned walks suspend, and how deep;
  - library entries for `f y = f (g y)`, a pair re-entering its own
    source legitimately (`f x = (c + 1, x + 1)` with `c = snd (f 0)`),
    members calling each other through `self`, a fan duplicating one
    cursor, and the shared-suffix case made small;
  - a runaway position under fuel shown as one busy position across
    slices.

**Open, for the holistic design, not for a ruling:**
- whether cycle errors are served into the net (the Cells plan's
  item 6), which makes re-walking required;
- the book as an array;
- `VCursor` as a variant or a kind;
- pull or delivery under parallel tasks.
