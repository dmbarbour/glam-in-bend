# Hierarchy — 2026-11-13

Drafted for the maintainer, at their request (2026-11-13): how live
sources holding copies of other sources are represented and integrated,
set beside the maintainer's image of hierarchical heaps; the walk kept
under an inner frame's writes, docketed for a proof; copies counted as
cursor interactions; and adjustments in direction. Two reviewers read
the same sources: the agent, and a Fable sub-agent working
independently (`HierarchyFable_2026-11-13.md`), whose findings are
compared at the end and were checked against their sources before they
were reported. This review proposes; the maintainer decides. The two
plan steps it names were added at the maintainer's request.

## The question

The maintainer (2026-11-13), after `cells-freeze.nested`: "I don't have
a firm grasp of your current design or how it will need to transition.
E.g. Is there any transfer or migration of ownership at present?", and
"I imagine you hold some computation state where you're processing one
live net at a time, and that net may copy a net. [...] the general case
includes circular copies, including even a net having a cursor into
itself." Then: "I'm still envisioning true hierarchical heaps, where
each live net may have its own collection of cells allocated locally.
[...] a lot of my comments are probably framed confusingly based on
mismatch with current implementation." And: "if counting interactions,
I'd be inclined to track the number of nodes copied as a number of
cursor interactions. Conceptually, I view the interaction for
`AnyNode >< Cursor` as the replacement of that cursor by another node,
often with new cursors behind it." The image is the one of the heap
review (`Heap_2026-11-09.md`, "The maintainer's ideas"): each heap owns
its net, its table, its own cells and its child heaps; "there is no
clear 'global', just a node in a tree that we locally view as root".

## The image and the build

**F1. A heap per net exists below the core; above it, everything is one
level.** The kernel's heap is one net's: `type H is Type: H{w: KM.M, a:
Array<V.Val>}` (`spike/kprim.bend:158-159`), its node words and its own
value table, as `net-nodes-double` has it. Above the kernel the core
keeps one of each (`glam/core.bend:36-100`; `Ent` at 49, `Srcs` at 64, `Tk` at 75, `Stk` at 82):

| The core's state | What it is | In the image |
|---|---|---|
| the book, `List<Ent>` | an entry per top-level definition, built from the module before the run (`book.t`, `book.c`, `glam/core.bend:1308-1338`) and never grown | the root heap's cells |
| the store, `Srcs` | the live nets of function-valued cells, a flat list of siblings, never freed (`srcs.push`, `glam/core.bend:340`) | the root heap's child heaps, though owned by no net |
| the stack, `Stk` | the tasks, each waiting on the one above it; only the top runs | the chain of nets entered, one at a time |

Verdict: keep. The image's root heap is what the core already is, read
as the module's net with its cells (the heap review's "the toplevel as
a net"); what is missing is every level below it.

**F2. A glossary, the image's terms onto the build.**

| The maintainer's term | As built |
|---|---|
| hierarchical heap | none above the kernel; the only tree is the chain of rings, a net holding cursors into a source that holds cursors into another: a graph of use, not of ownership |
| cells allocated locally | none at run time: a cell is a root definition. A value made at run time inside a net stays in that net, shared by its fans, which is local but not a cell (`Cells_2026-11-09.md`, "Data definitions stay linked") |
| ownership transferred to the parent | none. Two moves only: a forced cell's net, owned by its task, moves into the store when it ends as a function (`cell.out`, `srcs.push`), for the rest of the run; and a frame takes its source out for a step and puts it back (`srcs.take`, `srcs.put`) |
| linear transfer to another net | none: a serve copies, even a source used once |
| cursor interaction | a *serve*, which is a batch of them: positioned demand in the source at the cursor's position, then the finished tree there copied whole, or the cursor joined or given a static (`glam/materialize.bend:23-39`) |
| re-entrant access | a frame needing a source that a frame below holds, or a cell forced above frames (`release`, `glam/core.bend`, "Frames and their sources") |
| releasing walks | `release`: each frame keeping a walk (`TkSvD`), down to the first cell's task, gives its source back and becomes `TkSv`, walking again from its position later, a counted stop |
| self copy | not yet: a source needing itself splices its own recipe; to become a ring into itself (`self-copies-are-cursors`) |

And the build's jargon back:

| As built | Meaning |
|---|---|
| source | a function-valued cell's live net, in the store |
| ring | a copy's cursors in a host, linked through word 3 to a situating node holding the source's book entry (word 2) and the copy's level offset (its field) |
| position | a finished node's port in the source, held by a cursor (word 2) |
| positioned demand | walks in the source until the position faces a value, the frontier, a static or a cursor (`glam/position.bend`) |
| serve | one positioned demand and its batch of cursor interactions |
| frame | a stack task that serves one cursor of the task below it, its host |
| host | the net a frame serves into: a cell's net, or another frame's source |
| walk | a demand's path, top and depth in one net (`KD.D`) |

Verdict: adjust the vocabulary in the docs going forward: "a cursor
interaction" for one node copied, or one cursor joined or given a
static; "a serve" for the batch. The maintainer's confusion over
"serve" came from the batch being named where the interaction was meant.

**F3. Run-global names inside live nets are few, and cheap to make
relative.** A ring's situating node holds the source's book entry, a
name with a meaning global to the run: written at
`glam/core.bend:564` (`use.situ`), read at `:596` (`frame.at.s`) and
`:801` (`frame.cur.s`). The leaves of templates hold handles to book
entries too (`V.VLazy`, chased at `glam/core.bend:290`). Under a tree
of heaps either becomes a reference up the tree and an index there, as
the heap review proposed ("an offset up the tree and an index there,
adjusted as a value moves up, as a splice offsets levels"); each is an
interpretation of a `U32` at a handful of sites. Verdict: keep; the
choice the heap review called costly to reverse ("a handle with global
meaning inside `Val`") has not been made by nesting.

**F4. Transfer needs an owner, and only run-time cells would have one.**
A root cell is named by the book, so any later demand may use it
again: its source can never move linearly into a host. A source with a
single user is one no book entry names and one cursor reaches: a cell
allocated at run time, inside a net, as the image's local cells are.
Collection is the same prerequisite: nothing frees a source, and the
plan's ring liveness (`.ring`) is unbuilt. Verdict: open; not close.
The order is local cells first (a net allocating a cell its fans would
otherwise share, or a spark), then their liveness, then transfer and
collection, which the image makes local.

## Re-entry and cycles

**F5. The stack is the chain of nets entered, and the top frame touches
two.** A frame step takes its source out of the store and its host's net
from the task below (`frame`, `host.go`, `host.back`); nothing else runs
until it puts them back or keeps them. Exclusivity is the store's
checkout (`SrcOut`) and the stack's order, so two walks never run in one
net at once. Verdict: keep. Under parallel children each would have its
own stack, the checkout acting as the lock, and the release rule
unchanged.

**F6. Release is eager and coarse.** At a wait, `frame.wait` releases
every kept walk down to the first cell's task before the cell runs,
whether or not the cell touches them; a frame needing a held source
releases the same set (`frame.push.o`). The maintainer: "it makes sense
to me that we'd kill the existing walks upon re-entrant access to a
net". A lazy, per-source release is within reach: release only the
frame holding the needed source, found by searching the whole stack,
when a frame is pushed for it; and let a frame keep its walk across its
own wait, resuming it with the forced value (as `frame.keep` resumes a
value now) unless the cell reentered its source. The cost: `finished.v`
and `finished.src` learn a `TkSvD` below (today an error,
`glam/core.bend:916` and `:929`, "a value forced for a frame going on"), and the
invariant that kept walks lie above the topmost cell's task goes. On
`hello_live_positions.g` the walk is still lost (its cell `c` uses
`g`); a wait whose cell uses nothing held loses none. Verdict: adjust,
when a measured workload waits often.

**F7. Circular copies are handled, the self copy next.** Two sources
copying each other at different positions work, and the same position
again is a cycle, by the busy check keyed on source and position whatever
the host (`live_mutual_cycle.g`, `hello_nested_wait.g`). The self copy
as decided needs a serve within one net: the walk that needs it
released (it is reentered), positioned demand at the position, the
finished tree frozen to a template and spliced at the cursor in the same
heap. The materializer already copies by way of a template
(`mz.fz` in `glam/materialize.bend`), so the change is to its signature,
one heap where it takes two. Verdict: keep the order,
`cells-freeze.nested.self` next among these.

## The walk under an inner frame's writes

**F8. The allowance predates nesting, and its proof wants a shape.**
Since `cells-freeze.cells` a cell's demand stopped at a cursor keeps its
path while a frame serves into its net (`host.go`, `HbTk`); nesting
extends it to a frame's walk in its source (`HbSvD`). A walk's path is
node indices by depth (`D{h: P.H, path: KM.M, +top, +depth, ...}`,
`spike/kdemand.bend:14-15`). What must be proved (docketed as
`cells-freeze.nested.host`): a serve writes only the served cursor, the
cursors of its ring it joins, the nodes it allocates, and the ports
those cursors faced; and the walk resumed finds every node of its path
still there, what it kept of each unchanged, and the port where it
stopped facing the copy. Two routes:
- *State it as a function.* The materializer's writes as a write set
  over a heap model, proved in Bend over `spike/`'s heap; the
  materializer lives in `glam/`, so its core moves where the prover
  sees it, or a model of it does.
- *Hold it by a shape.* A cursor is a leaf the walk stops at, never a
  node the walk passes through, so no path node is a cursor; what a
  join rewires is a cursor's peer port, which may be a path node's
  auxiliary port. The proof then reduces to: the walk keeps node
  indices, not ports, and reads each port afresh when it climbs.

Verdict: the second route first, since it may make the law a case
split, as AGENTS asks of state shapes; the first if it does not hold.

## Copies counted as cursor interactions

**F9. Counted now; small per use.** `--count` reports a serve's cursor
interactions: each node it copies, or one where it joins its cursor or
gives it a static (`Mz`, `Sv` in `glam/materialize.bend`; the nodes a
freeze reads back, without the placeholders of statics and cursors,
`Fz`'s `n` in `glam/freeze.bend`). From 4 uses to 8, per use:

| Family | Interactions | Cursor interactions | Linked |
|---|---|---|---|
| `nested_sources` | 6 | 4 | 28 |
| `partial_in_cell` | 4 | 2 | 11 |
| `data_in_cell`, `partial_in_net`, `closed_work` | 5, 9, 147 | 0 | 19, 21, 19 |

Folded into interactions, both live families stay inside the families'
bound (at most 8 over linked). Verdict: fold them in, and drop the
ladder's serve bound and `sources=N` (`cells-freeze.sharing.copies`),
once the maintainer rules on the tuning.

**F10. Splices are copies too.** A splice copies a template's nodes into
a net, as a serve copies a frozen tree; the families count splices
apart, at most 2 a use, the size of each invisible (`Cells_2026-11-09.md`,
`cells-freeze.sharing`, "Blind spot"). Counting a splice's nodes as
interactions would give one cost for every copy. Verdict: open question
for the maintainer.

**F11. `AnyNode >< Cursor` as the model, batch as the mechanism.** Read
literally, the interaction pulls one node through the cursor, with
cursors behind it; the build copies the whole finished tree at once,
which is that interaction repeated over every node the tree holds
(`copy-reduced-function-nets`, "batch materialization"). Counting nodes
makes the two cost the same, which is what a quota should see. They
differ in what gets copied: a batch copies a finished tree whether or
not the host demands all of it, a pull only what demand reaches; a
large finished data structure whose head alone is demanded is the case
that would tell them apart, and no sample has one. A pull per node
through today's frames would cost a frame step each. Verdict: keep the
batch; measure a family whose copies are large and little demanded
before considering pulls.

## Recommendations

In order of value, with what each costs to reverse:
1. **The vocabulary** (F2): cursor interactions for nodes, a serve for
   the batch. Free.
2. **Fold cursor interactions into interactions**, drop the serve bound
   and `sources=N` (F9), on the maintainer's ruling. Reversed by
   restoring a constant.
3. **The self copy** (F7), as decided. A change of the materializer's
   signature.
4. **The proof of the kept walk** by its shape (F8). A law, kept.
5. **Lazy, per-source release** (F6), when a measured workload waits
   often. Reversed by releasing eagerly again; the invariant it drops
   is not relied on elsewhere.
6. **Local cells before transfer** (F4): transfer and collection follow
   a cell owned by a net, which a spark or a lazy member leaving a net
   would make. Not now.

## Questions for the maintainer

- Should a cursor interaction count as an interaction against quotas,
  and should a splice count its template's nodes (F9, F10)?
- Is the root heap the module's net with the book as its cells (F1)?
  If so, the store becomes its child heaps when local cells come.
- Which comes first for local cells: sparks, or lazy members leaving a
  net (`Data(Net)` in the heap review)?

## The second reviewer

Added when the second reviewer's review is in.
