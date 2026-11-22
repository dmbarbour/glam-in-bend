# Dead cursors: forgetting one once no serve can reach it (Fable, 2026-11-22)

Option B of `cells-freeze.sharing.cursors.erased`, scouted by a Fable
sub-agent at 2437be3 at the maintainer's request ("I don't have high
expectations, but I'm willing to be pleasantly surprised"), kept as
written. Checked after by the agent: a join onto a cursor found frees it
(`join1`, `glam/ring.bend`), so dead cursors that are reached clean
themselves up; the serve's climb that finds no ring position runs its
whole fuel, a ring walk a step (`cl.go`, `glam/materialize.bend`).

A Fable sub-agent's scouting, 2026-11-22, at the maintainer's request.
Advice only; nothing built, nothing run. "Checked" means read in the
code or a record named; "inferred" means argued from them, untested.

Short answer: no cheap criterion proves a dead cursor unreachable on
the measured workload. A relaxation exists (forget dead *negative*
cursors, keep dead positive ones) that would flatten the workload, but
it rests on an unproved lemma and worsens a neighbouring case. Not
low-hanging; a count in a measurement build would say whether the
relaxation is worth more thought (section 3).

## 1. When a dead cursor's position can be reached

**What a cursor is, in the code (checked).** `glam/freeze.bend`,
`fz.peer.v`: a wire from a node the freeze reached to one it did not
becomes `FzC{at, src, neg, far}`, `src` the reached node's own port
(`b + p`), `neg` that port's polarity, `far` the port it faces in the
source. So every cursor's position (word 2) is a port of a node this
copy took, the interface's first cursor aside (`use.cursor`,
`glam/core.bend`). A static at a reached node's port makes no cursor
(`fz.peer.k`, an eraser in the template). `freeze_tree` lists the
tree's own root principal as a crossing too, its `far` the position the
tree hangs from.

**The three lookups by position (checked, `glam/materialize.bend`,
`glam/ring.bend`).** A ring is searched by position in exactly three
places:

- L1, `sv.front.m`: positioned demand ended at the frontier, port `q`
  facing the served position; `rg.find(q)`; a hit joins the served
  cursor to the one found, nothing copied.
- L2, `cl.f` in the climb: for each node `x` up the principal chain,
  `rg.find` of the port `x`'s principal faces; a hit makes `x` the root
  of the tree to copy.
- L3, `cross`: for each wire leaving a newly copied tree,
  `rg.find(far)`; a hit joins (`join1`: the new port gets whatever the
  found cursor faced, a static if it was dead, and the found cursor is
  unlinked and freed); a miss makes a new cursor at `src`, its polarity
  the new tree's port's (`cross.k`).

Nothing else reads a cursor's position. `rg.situ` and `rg.pred` walk
the ring without reading positions, but pay for every member.

**Which dead cursors each can reach.** Let the dead cursor stand at
port `p` of copied node `N`. Two kinds, very different:

- *Dead negative*: `p` is an input of `N`; the host erased the consumer
  of the value awaited there (an unused head). Nothing is lost by
  forgetting the value; the cursor only remembers "this wire's copy end
  is erased".
- *Dead positive*: `p` is an output of `N` (a function's variable, a
  neutral application's result); the host supplied the void. That
  static is a *value* the copy owes to whatever in the source reads
  `p`.

A wire has one positive and one negative end (the Joins review,
checked there), so:

- L1 reaches only a dead *positive* cursor: the served cursor is
  negative, at an input, and faces an output `q`. This is ordinary: a
  host passing void for an argument the source's result returns.
  Inferred from polarity; the code does not check the found cursor's
  form.
- L2 lands on `p` when a finished tree's root principal faces `p` and
  some serve reached the frontier at an auxiliary output of a node in
  that tree. For dead positive `p` the tree is neutral (applications,
  operators, fans, lifts hanging from a variable or a neutral result):
  ordinary, the Joins review's `\x -> g (h x)`. For dead negative `p`
  the tree is a value (its root principal positive), and the only
  kind with a positive principal and an output besides is `Fn`
  (`spike/rules.bend`, the port table, checked): the frontier port is
  the variable of a function inside the value under `p`, or the output
  of a neutral node hanging from such a variable. Call this case (a):
  *a variable of a function the host discarded, demanded from outside
  that function*.
- L3 hits `p` when a tree copied later has an auxiliary port facing
  `p` directly (the root-principal crossing after an L2 hit is the same
  event as that hit). For dead negative `p` the facing port is an
  output of a neutral node `X`, copied by a route other than `p`:
  typically a copy fan under a host-supplied variable or neutral value,
  one output feeding a live position, another feeding `p`. Call this
  case (b): *a discarded input aliasing something the copy uses
  elsewhere, the alias a finished fan not yet copied when `N` was*.

**Case (b) is ordinary (inferred, traced by hand).** `g = \x -> mk x`,
`mk y = cons y y`, the fold using the first head. Serving `g`'s result
copies the cons's functions and its neutral chain; the fan of `y`,
finished since the beta put its principal on `x`'s wire, hangs under
the positive cursor at `x` and is in another tree, so both head
positions get negative cursors. The host erases the second. Serving the
first reaches the frontier at the fan's left output, climbs to the
cursor at `x`, copies the fan; its right output's far end is the dead
position; L3 finds the dead cursor, the fan's side gets the eraser, and
the dead cursor leaves the ring. The same happens for `let t = f x in
cons t t` when `t`'s value turns out neutral (the pending fan over `t`
becomes a finished fan under a host-dependent output).

Note what today's design does here: the join onto the dead cursor
*removes* it. Dead cursors that are ever reached clean themselves up;
the clutter is the ones never reached.

**Case (a) needs a scoping violation (inferred).** The walk enters
every node by an output (`spike/kdemand.blend`, header, checked). In
the whole copy the incremental one stands for, the function under `p`
has its principal erased, and by `net-scoped-arguments` every dataflow
path from the interface to its argument passes through its result,
reached only through that principal. So a valid net's demand never
asks for that variable. The record's own caveat applies: after a fan
copies a function, scoping holds per sharing context, not by
structure. Traced for one function shared by a fan, one copy under a
dead head: the dead side's `Merge` input gets a live negative cursor
when the `Merge` is copied, but a host walk demands it only after
entering the matching `Copy` by its dead-side output, which in the host
ends in a positive cursor that nothing joins. I found no valid term
reaching (a); I have not proved there is none. With the dead cursor
kept, (a) materializes the tree with an erased root and the demand
gets a void; with it forgotten, the climb passes `N`, finds no position
up to the interface, spins there until its fuel ends (`cl.go`, fuel the
source's capacity, a find each step) and reports `SvBad`.

**The measured workload (inferred from the source text, not run).**
`heads6`: each cell is `\c n -> c h0 .. h5 (t c n)`; the copy takes the
neutral chain of seven applications under `c`'s variable, a negative
cursor at each argument port. The fold erases five. Each dead position
faces its own pending `lit ""`, shared with nothing; nothing but a
serve at that position, from another copy, would ever reduce it. No
L2 or L3 can reach these positions: no finished node will face them in
this run, and if another copy made one, it would be a string's `Data`,
a value with no output. They are the never-reached kind, kept for a
join that cannot come. What they cost is every `rg.find` miss walking
past them (each climb step's L2, each new cell's seven L3 misses) and
the `rg.situ` and `rg.pred` walks.

## 2. Criteria tested

**Where a criterion can run at all (checked).** The host's erasure is a
static written into the cursor's link word (`erasure-at-write`; the
plan: "no flag and no step at erasure"). No code runs, and neither the
ring nor the source is in hand. `rg.find` holds the host alone. Only a
serve holds both nets (`sv.pd`). So a test "at erasure" does not exist
without a new kernel step; any criterion that reads the source runs
inside a later serve of the same ring, when a walk meets the dead
cursor.

**C1. The position is a port of a node the copy has already taken.**
True of every cursor but the interface's (section 1, `fz.peer.v`). It
separates nothing. Fails as a criterion: in case (b) above the dead
cursor's node was taken long before the fan reaches it.

**C2. Linearity: the far end is reached only through this wire.**
Meaning: the pending region feeding `p` has no output leading anywhere
but toward `p`. Plausibly sound (inferred: a rewrite adds no dataflow
path out of a region closed that way; then no node that ever faces `p`
has another output for a climb to arrive by, and no fan feeding `p`
feeds a live position). It covers the workload: `lit ""` is an
application of a handle to a constant. But:

- it fails, rightly, on `cons t t` and on `mk y = cons y y` (the
  region's fan has an output elsewhere), so those keep their cursors;
- to test it, a walker must trace the pending net backward from `far`
  through every kind, handles not yet loaded, the source's own
  cursors into other sources, and fans whose other side is already
  erased; its cost is the size of the thunk, per dead cursor, inside a
  serve; nothing like it exists (the collector follows inputs from the
  interface, a different question);
- its soundness lemma is new and is not a ring law: it speaks of the
  source's future reductions.

Not cheap. This is the maintainer's "trace demand across negative
cursors", from the other side.

**C3. One copy of the source, and telling the source.** Two failures.

- The program does not know (checked): a source's entry is
  `ESrc{i, t, name, whole}` (`glam/core.bend`), no count of copies;
  rings live in host heaps, and the core "sees no erasure and no
  collection" (the Joins reviews). A named cell can be used again at
  any time, each use a new ring. `use x = g (\l -> l cat x)` called
  twice is two copies of `g`; the workload's single use is not
  something the core can tell from a first use of many.
- Erasing in the source is wrong with a second copy, present or
  future: `asm.result = use1 "" ++ use2 ""`, `use2` folding by the
  second head. Erasing the far part for `use1`'s ring leaves a static
  at a port of a copied node, which `use2`'s copy reads as void. It
  also writes at a node copies took, against `copied-nodes-untouched`,
  and needs a message from the host's erasure to the source, where
  today there is no step.

A source with exactly one copy forever is a value moved, not shared;
the cells design exists because that is not known.

**C4. The far end is itself erased in the source.** Sound and cheap
(inferred from the Joins review's monotonicity and
`copied-nodes-untouched`): if the source's link word at `p` holds a
static, nothing faces `p` again, so no climb lands there and no
crossing has it as far end; the cursor may go, live or dead. One read
of the source, in a serve. It does not cover the workload: the heads'
thunks are alive in the source, since the source never learns the host
dropped them. Rare otherwise: a static there at copy time makes no
cursor at all.

**C5. The far end is finished.** Three sub-cases, none useful:

- a principal port (a value, computed for another copy): the tree
  stays under `p` for good; reachable only by case (a); droppable only
  on the scoping lemma;
- an auxiliary port of a node this copy took: both ends of one wire
  are cursors of this ring. The negative one is dead, so no serve
  joins them, and the positive one is a sink for good, today too. A
  serve could join them on sight, giving the eraser to what the
  positive one holds: a small cleanup of a leak the design already
  tolerates (the Joins review, Q7), not this workload;
- an auxiliary port of a finished node not yet taken: that is case (b)
  pending; the cursor must stay.

**C6. Death by absence: no cursor at a taken node's port means
erased.** Then nothing need be kept. It needs "did *this copy* take
that node", which the ring cannot say once the cursor is gone. The
source's marks are set by the first copy to take a node, one bitmap a
source (`copied-nodes-untouched`, checked; today on controls only,
`cl.marked`). Counterexample: copies A and B of one source; A took `N`,
B did not; B copies a fan whose output faces `N`'s port; marked, no
cursor in B's ring; B wrongly gives the fan an eraser where it owes a
cursor. A bitmap per copy is a structure the size of the source per
ring: Option A's territory and dearer.

**R. The relaxation: forget every dead negative cursor, keep dead
positive ones.** Not a criterion; a change of what the ring promises.
A cursor of form 0 whose word 1 is static is unlinked and freed when a
serve's walk meets it. Dead positive cursors must stay (inferred):
with one forgotten, L1 and L2 miss and the serve climbs to nothing,
`SvBad` on a valid program (`\x -> g (h x)`, the host passing void for
`x`); L3 misses and makes a live negative cursor (`cross.k`) whose
serve ends the same way.

What R does in each case:

- the workload: the five dead heads a cell go at the next serve; the
  ring holds live cursors only (inferred; flat growth is the
  prediction, unmeasured);
- case (a): `SvBad`, after a climb to the interface costing the
  source's capacity in finds, where today the demand gets a void. On
  the scoping lemma this never happens in a valid net; the lemma is
  unproved, and the record itself says scoping after fan copies is per
  sharing context and reported at run time;
- case (b): the crossing misses and makes a positive cursor at the
  fan's output, a sink. The result is still right. But the fan now
  duplicates each part of the argument the live side demands and
  parks the duplicate at the sink, where today the join hands it an
  eraser and it copies nothing; and the sink stays in the ring for
  good, where today the join *removed* the dead cursor. For `mk y =
  cons y y y y y y` folded by the first head, R trades five dead
  cursors a cell, cleaned up at the first serve, for five sinks a cell
  never cleaned, plus doubled copying: the same clutter this plan step
  is about, moved to a neighbouring program and made permanent.

That last point is the finding I would weigh most: dead cursors that
matter to correctness are exactly the ones the present design already
removes when they are reached; R removes the others at the price of
making the reached ones worse.

## 3. Verdict

**Not low-hanging.** Of the criteria, only C4 is both sound and cheap,
and it does not touch the workload. C2 would cover it and is neither
cheap nor proved. C3 and C6 fail on a second copy. What remains is R,
which is not "erase earlier where safe" but a weaker promise with a
known regression (case b) and an unproved premise (case a).

The structural reason, in one line: a dead negative cursor is a
tombstone for "this wire's copy end is erased", and the only cheap
place that fact can live is at the position itself; whether anyone
will read it depends on the source's future, which the host cannot
see. So the fruit is in making tombstones cheap to walk past (Option
A, not designed here), not in digging them up.

**If the maintainer still wants R tried, what it would take.**

- Code, small: a pass over the ring at the start or the end of a
  serve, unlinking and freeing each member of form 0 whose word 1 is
  static. The walk has the predecessor in hand (`Rw`'s `p`), so each
  removal is O(1); a header read and a word-1 read a member, a serve.
  At the *end* of the serve is the better place: the serve's own
  crossings then still find cursors that died before it, as in the
  `mk y = cons y y` trace, and only aliases copied by later serves
  become sinks. That narrows case (b); it does not close it.
- Laws, if the pass is a function of its own and `rg.find` is left
  alone: no existing law changes (checked: every law of
  `glam/LAWS.bend` and `glam/SERVE_LAWS.bend` is of a ring's exactness
  or of a write set; none, nor the models, speaks of which wires hold
  cursors, of dead ones or of polarity). New ones beside `glam/LAWS.bend`'s
  unlink and frame laws: the pass leaves an exact ring exact
  (`RG.without`, folded) and writes only the removed members' words,
  their predecessors' word 3 and the free list's head. The serve laws
  (`glam/SERVE_LAWS.bend`: `copy_pend`, `serve_keeps`,
  `serve_ring_exact`) speak of the ring's shape and the write set, not
  of which wires have cursors, so they stand, with the pass's write
  set added to a whole serve's when that law is written.
- Laws, if instead the removal is folded into `rg.find`'s walk to save
  the extra pass: the find law changes (it hands the heap back
  unwritten and finds `RG.first`), and with it the cross and crossings
  models and the `RG.unfound` premise that build on it. That is a
  change to existing laws on main, the maintainer's to approve, and
  the costlier proof. Not recommended.
- What no ring law would cover: R's actual claim, "no valid program's
  serve looks up a forgotten position, or if one does the result is
  still right". That is the join-sites invariant of the Joins second
  review (its law 3, in no law file, checked by search) weakened, plus the scoping
  lemma for case (a). It would be listed as a missing piece, with the
  differential oracle (serve-then-reduce against copy-whole) as its
  only evidence, and a library entry for case (b) showing the sink.

**The cheap step worth taking first: count.** AGENTS.md's rule for
this situation: before building, count how often it arises. In a
measurement build in a worktree, count as kernel errors (`P.err_if`):

1. a join onto a dead negative cursor at a crossing (`cross.k`'s hit,
   the found cursor of form 0, its word 1 static): case (b);
2. a climb's hit at a dead negative cursor (`cl.k`'s hit likewise):
   case (a);
3. for scale, dead cursors standing in the ring at each serve, by
   polarity.

Run the ladder, the sharing families, the library and the heads
families, and add two samples written for the purpose: `mk y = cons y
y ...` under a host-supplied argument, folded by the first head, and
`let t = f x in cons t t` with `t` neutral. Expected (inferred): count
2 zero everywhere; count 1 zero on everything but the two new samples;
count 3 large on the heads families alone. If count 2 is ever nonzero
on a valid program, R is dead and the reason is worth a library entry.
If count 1 is zero outside the samples written to provoke it, the
maintainer has the real trade in numbers: R flattens the heads
families at the price of sinks in aliasing programs nobody has
written yet. I would still not take it without Option A's answer on
the table, since A fixes the same cost with no change to what the ring
promises.

**Smaller things found on the way.**

- Dead cursors are self-cleaning when reached: `join1` unlinks and
  frees the cursor found. The clutter is only the never-reached ones.
  Worth saying in the plan step, since it bounds what any index must
  hold.
- Dead positive cursors are values (the void the host supplied), not
  garbage; no variant of B may touch them. The plan's wording treats
  both polarities alike.
- A miss in the climb costs far more than a miss in a crossing: with
  the cursor at the root gone, `cl.go` runs to its fuel, the source's
  capacity, a ring walk each step, before `SvBad`. Whatever is
  decided, a climb reaching the interface could stop there (inferred
  from `cl.f`: the interface's base read again yields the root, a
  circle of two).
- C5's middle case, a dead negative cursor whose far end is a positive
  cursor of the same ring, is a sink that could be given the eraser on
  sight. A leak the design tolerates today; unmeasured.
- The count of members a find walks (live, dead negative, dead
  positive, sinks) is not recorded anywhere I found; the Joins second
  review asked for ring lengths and scan lengths before any structure.
  The same build as the count above could record them for Option A.

**Not confident of.** That case (a) is unreachable in valid nets
across fan-copied functions (traced for one shape only). That the
heads workload has no lookup of a dead position (read from the source
text; the count would check it). That flat growth follows from
removing the dead heads (the `rg.situ` and `rg.pred` walks and the
climb's misses are the suspected cost; no profile read).
