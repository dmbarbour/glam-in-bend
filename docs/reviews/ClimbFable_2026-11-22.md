# The climb before a positioned walk: second review (Fable, 2026-11-22)

The second reviewer's review of `cells-freeze.sharing.cursors.growth.climb`,
by a Fable sub-agent at 02e7ad9, kept as written; the maintainer asked
for it before any law: "The 8 nodes heuristic feels arbitrary, and we
should try to understand what we should be doing, whether it should be a
heuristic at all." Checked after by the agent: its section 2 prediction
holds, more strongly than stated: cells of m heads on main grow again
from m = 2, instructions an element at 100, 200 and 400 elements 263K,
265K and 281K (m = 2), 466K, 510K and 608K (5), 548K, 619K and 773K
(6), 695K, 808K and 1,048K (8), interactions linear throughout, where
one head is flat (201K, 195K, 192K; `results/measure/climb/heads.py`,
out of git); and the serve already climbs the same principal links,
fuelled by the source's capacity plus one (`sv.climb.f`,
`glam/materialize.bend`). The logs and scripts it cites are under
`results/`, out of git.

Second reviewer, 2026-11-22, for `cells-freeze.sharing.cursors.growth.climb`.
Advice only. Tags: **[checked]** read at the cited place or computed from
the logs; **[inferred]** reasoned from what was read, not run;
**[relayed]** taken from the plan or the brief, not checked here.
Scratch: `results/advice/climb/stats.py` (the log statistics below).

## 1. What the walk and the climb establish

### The walk does not stop at finished nodes; it tests finishedness by reaching the root

- **[checked]** The walk's descent (`Demand.wk.q`, `dn.step`, `wk.push`,
  `spike/kdemand.bend:639-685`) reads the peer of the top node's
  principal; if that is an auxiliary port it pushes and moves to that
  node, whatever its kind. It reads no header on the way. A positive
  node (a `Fn` entered by its variable) does not stop it: every logged
  path runs on through `Fn@264` to `Ap@168` and `Lift*@176`.
- **[checked]** State 7 is set in three places, all at the walk's end:
  the top's principal faces a principal and the top is positive
  (`wk.ori`, line 416); it faces a static and the top is positive
  (`wk.sn`, 623); or any scan (`fw.scan`, `fw.end`, `kdemand.blend:141-151`) finds a
  positive node on the path, which converts a stuck stop (3) and a cycle
  (5) into 7 as well. So state 7 says "the walk could not go on, and a
  positive node is on its path". It does not say "finished".
- **[checked]** Finished is defined as reached from the interface
  through auxiliary ports whose peers are principal ports (the Cells
  plan, `cells-freeze.cursors`; `freeze_finished`). Each node has one
  principal, so a node is finished exactly when the chain of
  principal-on-auxiliary links from it reaches the interface. That chain
  is the walk's descent and the climb's.
- **[inferred]** So, for a finished start node b: the walk pushes the
  whole chain from b to the root, the root is positive with its
  principal on the interface (`wk.pair` with top not the interface, then
  `wk.ori` positive), and the end is state 7 with no interaction and the
  net unchanged. On this workload the walk is a finishedness test paid
  at the depth of b in the finished tree, with a path allocated and
  grown to hold it. The term agrees: `g = \f -> f LIST`, the tail
  `Fn@264 Ap@168 Lift*@176` being the first cons's `\c`, the application
  `f LIST`, and the control on `f`, whose principal faces the root `Fn`.
  The logs do not show the last top (it is not on the path), so "the
  root" is read from the term, not seen.
- **[inferred]** The converse fails. State 7 with no interaction is also
  what the walk answers when the chain ends, off the root, at a positive
  top in a pair (a function entered by its variable while its
  application is still a redex), at a positive top facing a static (a
  dead function's variable), or at a stuck or cyclic stop with a `Fn`
  below it. In those cases b is not finished, yet `pd.ended.k` answers
  `PdFront`, and the serve's own climb (`sv.climb.f`,
  `glam/materialize.bend:187-192`) then finds no ring position and ends
  in `SvBad`, or reads through a static. I did not construct a program
  that reaches one; the order of a host's demands may exclude the
  redex case. It is worth a count (section 5).

### What the climb's hit establishes

- **[checked]** Marks are set in one place, `fz.copied.k`
  (`glam/freeze.bend:204-210`), on controls reached in a finished part's
  freeze; a frozen template carries kinds and fields, not headers
  (`freeze.bend:288-316`), so a mark does not travel into a host. Tests
  set marks by hand (`glam/test_position.bend:73`).
- **[inferred]** The sound argument for the climb is not "a marked
  control ends walks". It is closure: if a node M on b's chain is
  finished, every node between b and M has its principal on an auxiliary
  port of the next, so each is finished by definition, b included, and
  the position faces a finished node's auxiliary port: the frontier, as
  `position.bend`'s header defines it. A mark is evidence that M was
  finished when a copy took it. What must hold besides: M is still
  finished, that is, M's chain to the interface is intact.
- **[inferred]** That invariant holds today for what the program builds,
  with two debts:
  - A rewrite cannot break the chain: no node on it is in a pair. The
    root is the exception to watch: a walk from the interface interacts
    a kind-11 control (`LiftC`, positive) at the root with the interface
    (`wk.root.go`, **[checked]**), so "the root is never rewritten"
    needs the premise that a copied source's root is no `LiftC`. I did
    not check whether a freeze at the interface can take one.
  - Fusion leaves marked controls (`marked_unfused`), and folding into
    an unmarked finished control keeps the node in place.
  - Eraser events skip marked controls only (`ev.at`,
    `spike/knet.bend:748`). The chain's copied `Ap`, `Fn` and `Copy`
    nodes are unmarked (Erasers review, X1, open for non-controls). By
    polarity an event erases from outputs toward inputs: it can turn a
    copied `Ap` above M into an eraser and leave a consuming eraser at a
    positive child's principal. The walk then ends at that child,
    positive facing a static: state 7, no interaction. Walk and climb
    still agree, and both are then wrong about "finished" (the serve's
    climb fails). I found no event that puts a static or a pair at a
    negative chain node's principal, which is what a disagreement needs.
  - Collection: nothing in `glam/` runs the collector on a source
    **[checked]** by grep; `materialize.bend:42` says a source must not.
    Latent: the collector reads no copy marks (`rc.mark`'s bitmap is its
    own), so once sources are collected an unmarked copied ancestor can
    be freed under a kept marked control, and the walk reads a reused
    slot where the climb has already answered.

### Counterexamples

1. **By a hand-set mark [inferred, a few lines of test].** A marked
   `Lift` whose principal faces a `Fn`'s principal (a pair), an `Ap`
   with its principal on the `Lift`'s auxiliary, the position facing the
   `Ap`. The climb answers the frontier; the walk reduces `Lift ~ Fn` or
   stops stuck there (I did not read that pair's rule): not the
   frontier either way, no positive node being on its path.
   No freeze makes this net, since it marks finished nodes only. It
   shows the law cannot be stated over arbitrary heaps: the premise that
   marks sit on finished nodes carries all the weight.
2. **Fuel and memory [checked, intended].** With too little fuel the walk
   stops in state 4 (`d.end`) and with a path that cannot grow in 6; the
   climb answers anyway (`test_position.bend`, "marked with no fuel to
   walk"). Any equivalence is "given fuel and room", or is stated on the
   net rather than on the walk.
3. **Latent: a marked negative control whose principal comes to face an
   eraser.** `se.go` and `Demand.go` test no mark, so a walk would erase
   it (`static_erase`, an interaction) where the climb says frontier.
   Not reachable while the chain above is intact; it is the same debt as
   X1, on the interaction side.
4. **None found in what the program builds today.** Nested sources: a
   serve into a source replaces a cursor, a leaf, and adds nodes below;
   it relinks no finished node's principal **[inferred]**.

### The evidence, as it stands

- **[checked, logs]** `seq` at 8 and 100: 108 state-7 walks, all with no
  interaction, all with a marked control on the path; the first mark is
  at path index 4 in 106 (`Ap Ap Lift Copy Lift*`) and index 2 in 2. No
  walk of another state (218 state 2, 216 state 1) has a marked control
  among its first 40 path entries. Paths are logged to 40 entries only.
- **[relayed]** The 826 walks, the ladder, `deep`, and the costs after.
- The measurement shows hit implies state 7 on these runs. It does not
  test state 7 implies finished, and it could not: every state-7 walk
  seen was of the finished kind.

## 2. The bound

### Eight is fitted to this term, and is not what keeps the climb sound or finite

- **[checked]** Past the bound the walk runs, so the bound never changes
  an answer; it only decides which walks are saved.
- **[checked, logs]** The first mark sits at index 4. **[inferred]**
  Because each list element adds four finished nodes no copy has taken
  yet (the logs mark controls only: the `Lift` is seen unmarked, the two
  applications below it follow, the `Copy` is read from the pattern): the two
  applications of `c h (t c n)`, a `Lift` and a `Copy` of the fold
  function, then the `Lift*` the previous serve took.
- **[inferred, a prediction to run]** `cl.run` looks at the eight nodes
  above the start. A cons of m heads, `c h1 ... hm (t c n)`, puts m + 1
  applications before the `Lift Copy Lift*`, the first mark at index
  m + 3: with six heads the climb misses and instructions an element
  grow with the list again. A fold whose function crosses no level
  (no `Lift` on the chain) has no marked control short of the root, and
  grows at any bound. Either family in `scripts/cursors.py` would show
  it.
- **[checked]** The start node itself is never tested (`pd.q.k` starts
  `cl.run` at b with `hit` false; `cl.hd` runs on nodes reached). A
  marked control facing the position directly costs a step for nothing.

### An unbounded climb already runs, after every frontier

- **[checked]** On `PdFront` with no cursor at the port, the serve climbs
  the same principal links from the same node (`sv.front.m`,
  `sv.climb.f`, `cl.go`, `glam/materialize.bend:118-192`) until it
  reaches a position the copy's ring holds, with a ring find at each
  step, and materializes the tree hanging there. Its fuel is the
  source's node count plus one: "one step a node at most".
- **[inferred]** So on this workload, where the ring find at the port
  itself must miss for the serve to climb, every element's chain is
  climbed twice with the change (the new climb to the mark, the serve's to the ring position)
  and was walked once and climbed once before. The serve's climb is the
  principled one: its stop is "a port this copy holds a cursor at",
  which is what the frontier means for the copy.

### Could it loop, and what would it cost

- **[inferred]** A chain of principal-on-auxiliary links without a repeat
  visits each node once, so the source's node count bounds any climb
  that is not a vicious circle, and a climb still going after that many
  steps has found one. A circle cannot hold a finished node (the
  finished part is a tree under the interface), so a circle means "not
  finished": fall to the walk, which reports the cycle in its own state.
  That is the same guard `sv.climb.f` uses, and the one bound that is a
  fact about the net, not a guess about the term.
- **[inferred]** Cost on a miss: the climb is two reads a node (a link
  word, a header), no path write, no allocation; the walk that follows
  descends the same chain with a path push a node. So a miss costs a
  fraction of the walk it precedes, on every round of `pd.loop`. A deep
  unfinished chain pays that fraction; it was never free.
- **[inferred]** Cost on a hit, the argument that removes the need for a
  heuristic: every node the climb passes below its stop is finished and
  not yet held by the asking copy, and the serve that follows
  materializes the tree hanging from the stop (`freeze_tree` at the
  climb's top), which contains all of them. So the climb's steps are
  bounded by the nodes that serve copies: the climb is paid for by the
  copy it enables, whatever the chain's length. This holds when the stop
  is the first node a copy holds. It does not hold for control-only
  marks, where the climb also passes copied nodes of other kinds on its
  way to the next control; that gap is what the eight papers over.

### The principled stopping points

In order of what they prove:

1. **The interface.** The climb reaches the root: b is finished by
   definition, no mark and no invariant needed. Cost: b's depth, which
   on this workload still grows with the list (less than the walk: no
   path, no growth, no cycle scans).
2. **A port the copy's ring holds** (the serve's stop). Finished by the
   ring's invariant, that a position is a port of a node the copy took.
   A ring find a step is too dear where the ring is wide (`deep`; the
   plan's `cursors.ring`).
3. **A marked node.** Finished by the invariant of section 1. Cheap, one
   header or bitmap read a step. With marks on every copied kind it is
   the same stop as 2 for a source with one copy, and an earlier, still
   sound stop where another copy took the node first.
4. **A non-auxiliary peer** (a pair, a static): not finished; walk.
5. **The node count exhausted:** a circle; walk.

"The first finished node" is not a separate stop: finishedness is what
is being decided, and it is known only at 1 to 3. "The first node whose
principal faces up" is every node of the climb.

## 3. Alternatives, ranked

Ranked by soundness first, then simplicity, cost, and what must be
proved. All **[inferred]** designs; none built or measured.

### A. One climb, to a known-finished node or the interface, its fuel the source's nodes (recommended now)

Keep the climb, change what stops it:

- test the start node too;
- a hit at a marked control, as now, and also at the interface (the
  climb's peer is the interface's port and the node is positive);
- no constant: fuel is the source's node count, as `sv.climb.f` takes
  it from `P.stats`;
- a miss (a pair, a static, fuel out) runs the walk, as now.

Then the frontier is answered from the definition of finished, and the
mark is a shortcut to it. Simple: a dozen changed lines in
`glam/position.bend`, nothing in the kernel. Cost: flat on `seq` as
now; on a chain with no marked control, b's depth in reads (the growth
returns in a milder form, which B removes). Proof: the root hit needs
nothing but the definition; the mark hit needs the invariant "a marked
node is finished".

Not in this slice: handing the climb's stop to the serve so that the
chain is climbed once. The serve's climb ends at the node whose
principal faces a ring position (`cl.f`), which lies at or below the
mark's stop, and with control-only marks the ring's position can be a
port of an unmarked copied node below the first marked control. Started
at the stop, the serve would pass its position and end in `SvBad`. Under
B the hand-over is sound for the copy that set the mark: the last node
below the first marked one is the serve's answer, checked by one ring
find, the serve climbing on only when another copy set it.

### B. Marks on every copied kind, as `copied-nodes-untouched` already rules (recommended next)

The decision's text is a bitmap for each source, a word for 32 nodes,
set when a copy takes a node and read by events, fusion and the
collector. Built for controls alone, in the header's form bits, which
other kinds use for other things. With the bitmap:

- the climb stops at the first copied node of any kind, so its length
  is the finished nodes not yet copied, and the copy that follows pays
  for it (section 2). No workload-shaped constant is left anywhere;
- X1 closes for the other kinds (events), the collector can keep copied
  nodes when sources are collected, and `finished-trees-cached` gets
  the stability it says it needs first;
- the invariant "marked implies finished and its chain intact" becomes
  true by construction: every ancestor of a marked node is marked, and
  nothing touches a marked node.

Cost: one bitmap read a climb step and a write a node copied; a third
reader in `static_erase` and the interaction rules if marked nodes must
also be safe from a walk (counterexample 3). Proof: the per-reader
guards are case splits like `marked_unfused`; the invariant is a law in
the wiring model (section 4).

This is the same work three open items wait on. The climb is a reason
to do it sooner, not a new mechanism.

### C. The mark test inside the walk's descent (a positioned variant of the walk)

A third instance of the Blend template beside `Demand` and `DemandEv`,
whose `dn.step` reads the header and ends at a marked node in state 7.
One pass on a miss where A makes two, and the walk's own cycle
detection. Against it: a header read on every step of every positioned
walk, a path still allocated for walks that never needed one (most of
the measured cost was the path's growth), more kernel surface, and a
third variant to keep in step. Sound on the same invariant as A. Not
worth it unless a measurement shows the double pass on misses matters.

### D. Record "finished" where a walk learns it

A state-7 walk to the root learns that its whole path is finished; a
bit a node would let the next walk stop at once (the first Positions
review proposed a finished bitmap extended at each walk's end). Weaker
than B on every count:

- finished but uncopied nodes are deliberately unprotected ("events,
  fusion and collection keep their gains there"), so the bit can go
  stale: an event turns the node into an eraser, the collector frees and
  reuses its slot. Every such site would have to clear it, a coupling
  the copied mark does not need;
- it writes to the source on a query, against the grain of "the source
  is not touched by a copy"; the copied mark is already the one
  sanctioned write, and it records an act (a copy took this), not a
  deduction;
- after B there is little left for it to save: the uncopied finished
  nodes are climbed once and then copied.

### E. A path positioned demand keeps

`positioned.from` already resumes one walk's path at one position. The
growth here is across positions: each element's walk starts at a new
cell and shares only a suffix with the last. Keeping a path across
positions means knowing which suffix is still valid after the walks
between, which is the finished question again with more state. No.

### F. Reshape the serve so that no chain forms

The chain is the term's own sharing: the fold function's copies,
threaded through the cells as each `t c n` reduces in the source. A
serve cannot avoid it without copying ahead of demand or changing what
reduces where, both against `copy-reduced-function-nets`. The chain is
not the fault; walking it to the root to learn nothing was. No.

### Beside the ranking: what state 7 should mean to positioned demand

With A, a finished b never reaches the walk. A walk that still ends in
state 7 has an unfinished b and could not go on (section 1's converse
cases), and `PdFront` is then the wrong answer to give the serve. Once
a count shows whether it happens, state 7 after a missed climb should
become a stop of its own for the core, not a frontier.

## 4. A law

### Not the law the plan names, and not yet

`cells-freeze.sharing.cursors.growth.law` asks for "what the climb
answers is what the walk would". I advise against it in that form:

- over arbitrary heaps it is false (counterexample 1), so it needs the
  premise that the heap is one the program builds, which no model holds
  yet (`cells-freeze.cursors.laws` is tentative, waiting on the finished
  predicate in the wiring model);
- it pins the climb to the walk's state 7, and state 7 is the weaker
  notion of the two (section 1). The walk should not be the
  specification of the frontier; the definition of finished should;
- a law over a constant of 8 proves a fitted number.

After alternative A the claims separate into three, of very different
cost. Sketches in the style of `spike/LAWS.bend`; names of functions not
yet written are marked new.

### L1. A climb's hit at the interface is finishedness, by computation

Claim the climb against the definition, which is top-down: the tree a
freeze walks from the interface (`fz.reach`, or the model's
`W.finished` once it exists). A law against a second copy of the climb
would prove the copy (`docs/Proving.md`, What to claim). All names here
are new but `cl.run`:

    # LAW: a climb that reports a hit with no mark on its way reached
    # the interface: the start node is finished (cells-freeze.cursors).
    # Record: copy-reduced-function-nets
    law climb_root_finished:
      for k: Nat
      for h: P.H
      for +b: U32
      for e: {cl.at_root(cl.run(k, cl.start(h, b))) == True{} : Bool}
      {F.in_finished(h, b) == True{} : Bool}

with the climb's state telling a hit by mark from a hit at the root
(`cl.at_root`), and `F.in_finished` membership in what the freeze's own
walk from the interface reaches. The content is the duality: bottom-up
by principal links and top-down by auxiliary ports facing principals
name the same nodes. An induction on the climb with the freeze's step
unfolded once a node; dearer than a case split, cheaper in the wiring
model than on the heap. It claims nothing about marks.

### L2. A marked node is finished: the invariant, and the real obligation

    # LAW: in a source the program builds, a marked node's chain of
    # principal links reaches the interface (copied-nodes-untouched).
    # Record: copied-nodes-untouched
    law marked_finished:
      for s: W.Net            # the wiring model, with marks (new)
      for r: W.Built(s)       # s reached by the program's steps (new)
      for +x: U32
      for m: {W.marked(s, x) == True{} : Bool}
      {W.finished(s, x) == True{} : Bool}

It rests on, one law each, in the model:

- freeze marks only nodes of the finished tree it walks (`fz.reach`
  follows auxiliary ports whose peers are principal);
- a rewrite keeps every node but its pair and every link not touching
  it (the locality law the plan already notes holds "almost by
  definition", `W.rw_links`), and a finished node is in no pair;
- fusion leaves a marked node (`marked_unfused`, proved);
- an event leaves a marked node (`ev.at`'s guard, a case split; today
  for controls only);
- a splice into a source adds nodes and relinks only the cursor's peer;
- once sources are collected, the collector keeps marked nodes.

With control-only marks the chain above a marked control passes
unmarked copied nodes, and the event and collector clauses do not cover
them: L2 is then provable only under "no event or collection has
touched a copied node", a premise the program does not keep (X1). With
alternative B every ancestor of a marked node is marked and the clauses
close. So L2 should be written after B, or be stated with its missing
pieces listed beside it (`docs/Proving.md`, What to claim).

### L3. The walk agrees, if the walk is kept as a witness

Only if the maintainer wants the walk tied in. On the kernel, no model:

    # LAW: from a finished node, with fuel and room, demand ends at the
    # frontier having done nothing.
    law finished_walk_frontier:
      for k: Nat
      for f: Nat
      for h: P.H
      for path: KM.M
      for +b: U32
      for e: {F.in_finished(h, b) == True{} : Bool}
      for g: {Nat.lte(walk_fuel(k), f) == True{} : Bool}   # new
      for c: {path_room(path, k) == True{} : Bool}           # new
      {d.st_n(KD.Demand.demand(f, KD.d.go(h, path, b, 0, 0))) == (7, 0) : U32 & U32}

and a second law that the heap is the one given. This is the dear one:
the walk's descent batches steps between powers of two, scans for
cycles when its path fills and grows the path through `KM.m_ensure`, so
the induction carries the path's contents and capacity. It also needs
"the root is positive", a polarity fact about built nets. I would not
write it. Its one-step core is cheap and may be worth having on its
own: a top whose principal faces an auxiliary port is pushed with no
interaction and the heap unchanged (`dn.step`, a case split).

### What the laws together would and would not claim

- L1 and L2 give: `PdFront` answered by the climb implies the start
  node is finished. That is the property the serve relies on (its own
  climb then finds a ring position: a law of the ring's, "each tree a
  copy takes hangs from a node it holds", already assumed in
  `sv.climbed.k`'s comment and worth stating there).
- Not claimed: that a miss means unfinished (true by the same
  definition once the root is a hit, and cheap to add); that the walk
  after a miss never answers a frontier (section 3's last point; a
  measurement first); anything about cost.
- Mutants to keep beside them: the climb following an auxiliary port
  instead of the principal; a hit at an unmarked control; the root hit
  taken for a negative node; the start node skipped.

## 5. Verdict and next step

### Verdict

- **The idea is sound; the reason given for it is not the right one,
  and the eight is a heuristic that should go.** A marked control ends
  the question not because walks happen to stop there (they do not:
  they run on to the root) but because finished is closed along the
  climb: a finished node above makes every node below it on the chain
  finished, and a finished start node is what "the frontier" means.
- **The walk was never the right tool for this case.** For a finished
  start node it is a finishedness test that allocates a path, walks to
  the root and learns one bit. The climb is that test done directly.
  The serve already runs the same climb, unbounded.
- **No counterexample in what the program builds today.** A hand-marked
  unfinished control separates climb from walk at once, so everything
  rests on "marked implies still finished", which today leans on two
  things that are not built: marks on the other copied kinds (X1) and a
  collector that keeps copied nodes. Neither bites yet (the event cases
  I traced leave walk and climb agreeing; no source is collected).
- **The bound is not needed for soundness or termination.** The
  source's node count bounds any climb and detects a circle. A climb
  that hits is paid for by the copy that follows, once the stop is the
  first copied node of any kind.
- **Do not write the walk-equivalence law.** Make the frontier's answer
  follow from the definition of finished (L1, cheap), and treat "a
  marked node is finished" (L2) as the real obligation, written with or
  after the all-kinds marks.

### Recommended next steps, in order

1. **A count before anything is built** (AGENTS.md, Measuring): in the
   measurement worktree, beside each positioned walk run an unbounded
   climb to the root and count, as kernel errors,
   (a) state 7 where the climb did not reach the root (an unfinished
   node answered as a frontier), and
   (b) a climb that reached the root where the walk did not end in
   state 7 with no interaction.
   Both should be zero over the ladder, its families and the workloads.
   (a) decides whether state 7 after a missed climb must become a stop;
   (b) is the evidence for alternative A that the 826 are for the
   present code.
2. **Two workloads that the eight fails**, added to
   `scripts/cursors.py`: a cons of six or more heads, and a fold whose
   function crosses no level. Predicted: instructions an element grow
   with the list on today's main. If they do not, my reading of the
   chain is wrong somewhere and this review should be reread.
3. **Alternative A**: test the start node, hit at the interface (a
   positive root that is no `LiftC`), fuel from the source's node
   count, the constant removed. Rerun `seq`,
   `deep` and the two new families at n, 2n, 4n.
4. **Alternative B**, as its own plan step, since X1, the collector and
   the fragment cache wait on it too: the copy marks as the decision's
   bitmap, every kind, read by events, fusion, the interaction on a
   marked node's principal, and the collector.
5. **Laws**: L1 with step 3; L2 with step 4, its missing pieces listed
   if it comes sooner; L3 not at all, its one-step lemma if wanted.

### Where I am least sure

- That a copied source's root is never a `LiftC`, which a walk from
  the interface would interact: A's root hit and L2 both need it.
- That the last top of the logged walks is the root `Fn`: read from the
  term, the logs stopping one node short. Step 1's count (b) settles it.
- The converse cases of section 1 (state 7 for an unfinished node):
  read from the code, no program found. Step 1's count (a) settles it.
- The event analysis for unmarked ancestors: argued from polarity and
  `ev.at`, not from the event table entry by entry (`KR.ev_by`).
- The amortization argument assumes `freeze_tree` at the climb's top
  takes every finished node below it, the start node among them: the
  definition says so; I did not trace `fz.reach` for it.
- The prediction of six heads assumes the application spine lowers as
  one `Ap` a head, as the two-head-and-tail case in the logs suggests.
