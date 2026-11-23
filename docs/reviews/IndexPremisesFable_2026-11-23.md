# The premises of the laws over the index: the second reviewer (Fable, 2026-11-23)

The second reviewer's review of the premises of the cursor and serve
laws over the index (`cells-freeze.sharing.cursors.index.ring.premises`),
by a Fable sub-agent at 6ec317a on `cursor-index-spike`, kept as written.
Part A was written before the first reviewer's file
(`docs/reviews/IndexPremises_2026-11-23.md`) was opened; Part B is the
once-over of it and of the ring-era laws' retirement.

Nothing was built or run: no typecheck, no verdict, no `one_law`. A claim
is marked **[checked]** where I read it at the place cited, **[inferred]**
where I reasoned from definitions I read, on paper, not by Bend;
**[unchecked]** where I did neither. Line numbers are of the files at
6ec317a.

## Part A: the premises, law by law

### A1. The shared four: `hf`, `hd32`, `hN`, `hB` (every law)

Every law of `glam/LAWS.bend` and `glam/SERVE_LAWS.bend` takes the words
full at depth `d` (`hf`), `d` below 32 (`hd32`), the tracked nodes laid
out apart (`hN: RG.layout(N, d)`) and each its own base (`hB:
RG.bases(N)`). **[checked]** e.g. `glam/LAWS.bend:109-112`.

1. Necessary, all four: the view reads by slots (`hf`, `hd32`); without
   `hN` two tracked nodes may share a slot and a free of one overwrites
   the other; without `hB` `P.free` (which frees `P.base(r)`,
   `spike/kprim.bend:581`) frees another node than the model's.
2. **Not re-established by any conclusion.** Each `_pend` law concludes
   `RG.px.ok` over the words after, and nothing else: not that the words
   after are full, nor (for `copy_pend`, which changes `N` from `M ++ ns`
   to `M ++ pls`) that the new `N` is laid out and its own bases. The
   proofs have these facts (the plan: "The cursor's, the join's and the
   crossing's proofs now give the words full after them as well ... the
   laws projecting the invariant", `docs/plans/Cells_2026-11-09.md`,
   `.ring.fold`; `copy_full` at `glam/SERVE_PROOF.bend:368`,
   `lay_suffix` at `:291`), but a caller who chains two laws cannot take
   them from the laws. So today the laws compose only inside the proof
   files. **[checked: no conclusion in `glam/LAWS.bend`,
   `glam/SERVE_LAWS.bend` or `glam/SPLICE_LAWS.bend` mentions `AD.full`,
   `layout` or `bases`; the index's laws do export it, `insert_full`,
   `remove_full`, `free_full`, the precedent.]**
3. Proposal, in two sizes:
   - small: export what the proofs have as laws: `cursor_full`,
     `join1_full`, `crossings_full`, `leave_full`, `join_full`,
     `copy_full` (heap and map), and `copy_lay` (layout and bases of
     `M ++ pls` from those of `M ++ ns`);
   - larger, better: fold `layout(N, d) && bases(N)` into `px.ok` as two
     conjuncts. They speak of `N` and `d` alone, so every step but the
     copy keeps them by identity, and each law loses two premises while
     its conclusion gains what the next step asks. `KMd.past(N, d)` (A10)
     could join them. `AD.full` cannot (it is over the array, not the
     view); a list-length conjunct on `v` would stand in for it only if
     the hub ties the two **[unchecked]**.
4. The bundle recurs 14 times; with (3) it shrinks to `hf`, `hd32`.

### A2. `cursor_pend` (`glam/LAWS.bend:95`)

Premises beyond A1: `hp` with `Con{x, ps}` pending and the free list's
first nodes `IM.ix.take(I, b, F)`; `ha: look(I, src) == None` (`:114`).

- `ha`. Necessary: with the key present `X.ix.insert` counts a kernel
  error and leaves the tree (`glam/index.bend:250-253`), so the
  conclusion's `ix.put(I, x, src, b)` is false of the heap. Not
  dischargeable from the host's heap: that a crossing's position is no
  cursor's is a fact of the *source* (a finished node is copied once),
  which no model here holds. Keep as a premise. What can be a law is the
  other half of `cursors-indexed`'s "an insert meeting its own key is a
  kernel error, the tree unchanged, and a law"
  (`docs/decisions/cursors-indexed.md:41-42`): no law of
  `glam/INDEX_LAWS.bend` states it **[checked: every insert law takes
  `ha`]**. `insert_dup`: `look(I, k) == Some{y}` gives the words after
  `X.ix.insert` equal but the error count's. Then a caller that cannot
  prove `ha` still knows the fault is counted, not silent. Small law
  (the descent's proof exists for `find_tree`).
- `take(I, b, F)`: the branch is the list's first node, needed only in a
  tree. Necessary for a fixed `d` (else `P.alloc` grows,
  `spike/kprim.bend:513-516`). See A5 on room.
- Conclusion: `ps`, `L`, `N` unchanged, `F` the rest: gives the next
  crossing's `hp` directly. Good.

### A3. `cursor_head` (`glam/LAWS.bend:62`)

The same premises as `cursor_pend` for one word. They are stronger than
the claim needs: the header write precedes the insert, and the insert's
frame keeps `x`'s word 0 whether or not the key is absent (an error
writes the header's error count only). A weaker premise (the index real,
on its invariant, laid out, `x` off it) would do, but nobody calls the
law with less, so I would leave it. A more useful shape: the realization
`IM.tr.real` could ask a leaf's header to be a cursor's (kind 18, form 0
or 1) instead of "no branch's" (`glam/index_model.bend:246`); then every
`_pend` law would keep cursors cursors, and a served cursor's kind, which
`sv.pd` trusts, would be the invariant's. Cost: the index's realization
laws all change; low priority.

### A4. `join1_pend` (`:127`), `cross_pend` (`:158`)

- `join1_pend`'s `hy: look(I, k) == Some{y}` is what `find_tree` gives at
  `k = far`; `cross_pend` discharges it so. Nothing to tighten. `x != y`
  follows from the invariant (`x` pending, so no node of the index).
- `cross_pend`'s `ha: RG.cx.ab(...)` and the `cx.F0` shape are A2's two
  premises behind the find's case split; fine. `b` is a free variable
  only so that `F0` can name the branch: fine.
- Conclusion to next premise: `cx.F1` is not syntactically a `cx.F0` of
  the next crossing; `RG.cxs` bridges it with `cx.hd`/`cx.tl` and
  `cx.room`. Sound, and the reason for A5.

### A5. `crossings_pend`, `crossings_keeps` (`:193`, `:227`): `RG.cxs.ok`

`hok: RG.cxs.ok(cs, vm, dm, I, F)` (`glam/ring_model.bend:449`) is two
premises a crossing:

- **`cx.ab`** (position absent where a cursor is made). Necessary (A2).
  The stepwise form is the weakest; the record's form (positions absent
  at the start and distinct, `serve-premises-over-index`, premise 1) is
  what a caller can know. The bridge the plan owes (`.ring.fold`: "by a
  bridge still owed") needs two model lemmas that
  `glam/INDEX_LAWS.bend` lacks **[checked: 39 laws, none of a lookup
  after an operation; the plan says so too: "no law yet gives a find
  after a removal or an insert"]**:
  - `look_put`: `ix.inv(I)`, `look(I, k) == None`, `k2 != k` give
    `look(put(I, x, k, b), k2) == look(I, k2)`; and at `k` itself
    `Some{x}`;
  - `look_del`: `ix.inv(I)`, `look(I, k) == Some{x}`, `k2 != k` give
    `look(del(I, x, k), k2) == look(I, k2)`; and at `k`, `None`.
  With them, `cxs_ab`: a join only removes keys and a put adds its own
  `src`, so "the `src`s distinct and absent from `I`" gives every step's
  `cx.ab` **[inferred]**; a fold over `cs`. These two lemmas are the
  single most reused missing piece: they also discharge A8's `hy` and
  A11's `hc`.
- **`cx.room`** (a node on the known free list for the branch). This is
  premise 4 of the record, growth unclaimed. It is not a fault of the
  code (the allocator grows); it is the laws' fixed `d`. A count
  discharges it: `length(F)` at least the number of crossings, since a
  join only lengthens `F` **[inferred]**; `cxs_room`, a small fold. Who
  gives the count: nobody today; `P.stats` gives a capacity, not the
  free list's length. See A12 on growth.
- `crossings_pend`'s `hp` asks the pending list to be exactly
  `RG.pls(cs, vm, dm)`; `copy_pend` concludes exactly that. Good.
  `pl.of`'s default 0 for an index past the map is harmless (0 would
  have to be live).
- `crossings_keeps`' region: `j` off all four words of every tracked
  node, though a crossing writes a leaf's words 0, 2, 3 once, at its
  making, and a live node's word 1 only where a link lands. Coarser than
  needed, but nothing reads a tracked node's words through the frame;
  the invariant carries them. `hjf` (off the link words of ports faced
  at the start) is exact enough: a join writes two of them. Leave it.
- Conclusion to next premise: `Nil` pending, `L`, `F` by the model. For
  the next serve see A12.

### A6. `leave_pend`, `leave_keeps` (`glam/LAWS.bend:264`, `:331`)

- `hc: look(I, k) == Some{c}` (`:282`). Necessary (the removal's
  premise). Dischargeable at both call sites by `look_member`
  (`glam/INDEX_LAWS.bend:343`) with `k` the word the serve reads at
  `nc + 2` (`glam/materialize.bend:241`), given that `nc` is a leaf of
  `I`: the one thing the core owes of the cursor it serves. A corollary
  stated so (`has(leaves(I), c)`, `k` the heap's word) would fit the
  caller better than a model lookup; small.
- `hpo: RG.po.all(p, Nil{}, d, N)` (`:283`): `p`'s link word off all four
  words of every tracked node and off the head. Necessary where `p` is a
  node's port: linked into a free node's word 1 it breaks the chain,
  into a leaf's word 2 a key. For the static site,
  `R.leave(h, P.era(), nc)` (`glam/materialize.bend:221`, `:365`), every
  `KMd.off.port(d, P.era(), j)` is `True` by computation
  (`spike/kmodel.bend:14-34`), but `po.all` recurs on `N`, so the caller
  needs an induction: `po_static`, a five-line lemma, not yet a law
  **[checked: `P.era()` occurs twice in `glam/PROOF.bend`, both inside
  one proof term at `:1000-1001`, in no lemma's statement]**.
- `hpk: RG.port.ok(L, d, p)` (`:284`). **Redundant, I believe**
  **[inferred]**: for a `p` not static, `hpo` over no live node already
  puts `p + 1` off words 2 and 3 of every node of `N`, and `sub(L, N)` is
  a conjunct of `hp`; for a static `p`, `port.ok` holds by alignment
  (`glam/ring_model.bend:187-197`'s own comment), from `hB` and `d >= 2`
  (`hN`, `N` not empty since `s` is in it). So `port_of_po`: `po.all(p,
  Nil, d, N)`, `sub(L, N)`, `layout(N, d)`, `bases(N)` give `port.ok(L,
  d, p)`. The static half is a bit fact (a slot keeps a word's low two
  bits), and none such is proved yet **[checked: no lemma of the proof
  files joins `P.is_static` to `RG.bases` or `P.base`]**; the
  non-static half is a fold. `link_leave`, which takes no `bases`, would
  keep `hpk`.
- With both: a corollary `leave_era_pend` (no `p`, no `hpo`, no `hpk`)
  is exactly the static call site.
- Conclusion: `L` without `c`, `F` with `c` and the parent: the next
  step's shapes (A12).
- `leave_keeps`: region exact enough (`hjp`, `hjw`: the two ports).

### A7. `join_pend`, `join_keeps` (`:298`, `:26`)

- `hx: look(I, kx) == Some{x}`: as A6's `hc`, by `look_member`.
- `hy: look(del(I, x, kx), ky) == Some{y}` (`:318`, `:47`). The call
  site has it in another form: `sv.front.m` gets `c` from
  `R.rg.find(h, situ, q)` (`glam/materialize.bend:198-202`), which
  `find_tree` reads as `look(I, q) == Some{c}`, a lookup in `I`, not in
  `del(I, nc, pos)`. The gap is A5's `look_del` plus `q != pos`.
  Restated with `hy0: look(I, ky) == Some{y}` and `hne: U32.is_eq(kx,
  ky) == False`, the law matches its caller.
- **`q != pos` is not checked by the code.** `PdFront`'s `q` is the port
  facing the position (`glam/position.bend:38-39`); `q == pos` would be
  a port facing itself in the source. Then `c == nc` and
  `R.join(h, nc, nc)` unlinks and frees one node twice. A well-formed
  source excludes it, but under `corruption-reported-when-cheap` the
  compare `c == nc` in `sv.front.m` is one test on a path taken once a
  serve, and it would discharge `hne` in the code instead of from the
  source's wiring. **[inferred; I did not trace positioned demand to see
  whether another guard excludes it.]**
- No port premises: both ports are faced by live nodes, so the invariant
  covers them. Good.

### A8. What neither `_pend` nor `_keeps` says: the wire is made

For a join whose two faced ports belong to untracked nodes (the usual
case: ordinary net nodes on both sides), the invariant says nothing of
those ports after (it speaks of live nodes only) and the frame law
excludes exactly their link words. So no law states that `u`'s link word
holds `w` and `w`'s holds `u` after `R.join`, nor `p` and the faced port
after `R.leave`. A mutant that drops `P.link_xx` from `jn.w` or `lv.w`
(`glam/ring.bend:60`, `:129`) writes fewer words. The `_pend` laws do
refute it, on a witness where a live node faces `x`, `y` or `c` (that
node then faces a freed node, `po.n` false); what no conclusion tells
apart is the mutant on untracked peers, the usual case **[inferred; not
run]**. `glam/MUTANTS.txt` has links moved
(`join_link_next_port`, `leave_links_past_port`, `join_links_static`)
but none dropped **[checked: the 28 names in `glam/MUTANTS.txt`]**. The
ring's laws did not say it either (`join_exact` concluded `RG.ring.ok`
only), so nothing was lost; but it is the operation's purpose.
`join_links`, `leave_links`: on the `_pend` premises, for `u` not static
with its link word off `N`, `word(u + 1) == w` after; likewise the other
end. Proof: `P.link_xx`'s own law, then the removal's and frees' frames,
all already used by `join_keeps`. A new law each, no fold.

### A9. `copy_pend` and the serve's four (`glam/SERVE_LAWS.bend:41`)

The four share 15 premises; judged once.

- `hfm`, `hdm` (the map full, depth below 32). Necessary. The
  materializer's map is `[0 : U32^T.depth_for(31n, size, 0n)]`
  (`glam/materialize.bend:97`, `:282`); that it is full at a depth below 32
  wants a small law of `T.depth_for` **[unchecked whether one exists]**.
- `hp` in the shape `Nil` pending, `Con{s, t}` live, `ns ++ F` free,
  `M ++ ns` tracked. The shapes are for the proof (suffix lemmas,
  `lay_suffix`); see A12 for what they cost a caller.
- `hl: SM.made(ts) == length(ns)`. Necessary; by the caller's choice of
  `ns`.
- `hdy: SV.dyn(ns)` (`:65`). **Redundant** **[inferred]**: `hB` gives
  `P.base(n) == n` for each of `ns`, low bits 00; a static's are 11
  (`spike/kprim.bend:408-409`, `:576-577`). `dyn_of_bases`: a bit fact,
  small. The model's own comment calls it "the allocator's to show"
  (`glam/serve_model.bend:94-96`); `bases` shows it.
- `hfr: RG.faces(Con{s, t}, v, d, ns)` (`:68`). **Redundant**
  **[inferred]**: `hp`'s `px.off(L, v, d, L, M ++ ns)` puts each faced
  port's link word off words 1 to 3 of every tracked node that is not
  live; `ns` is tracked and, by `none.in(ns ++ F, L)`, not live. That is
  `port.ok(ns, d, r)` for a port not static, and A6's alignment for a
  static. It reads as a ring-era premise that the pending invariant has
  since absorbed (the plan's `.ring.copy`: "their ring premise only
  passed along, so dropped" did the same to another).
  `faces_fresh`: a fold over `L` on `port_of_po`'s parts.
- `hLd: RG.distinct(Con{s, t})` (`:69`). Needed (the plan: "the hole
  lemmas need" it), and returned by no conclusion: A12.
- `hpa: KMd.past(M ++ ns, d)`: tracked nodes off the header's words.
  Necessary (the splice writes the header). A fact of `N` and `d` alone:
  fold into the invariant with `layout` (A1).
- `hhd: KMd.off.words(KMd.hdr_words(), d, P.at_fh())` (`:67`). A fact of
  `d` alone: true for every `d` past the header's width. Restate as a
  bound on `d` or prove once from one (`hdr_apart`); the kernel starts
  at 128 nodes (`spike/kprim.bend:219`), so any heap has it. Small.
- `ht: SM.tpl.ok`, `hcp: SV.copy.ok`, `hro: SV.root.ok`: freeze's
  obligations, "not claimed" by the laws' own text. Checked against
  `glam/freeze.bend` by reading only: a crossing's hole is linked once,
  at its port 0, to the finished node (`:385`), as `hole.end` asks. One
  template fails `copy.ok`: nothing finished, `[RN.FzC{0, P.iface(),
  True{}, P.iface()}]` with no link (`glam/freeze.bend:490`), whose hole
  no link names (`SV.names`, `glam/serve_model.bend:49`). `root.ok`'s
  comment argues it is never a value's; `materialize` is also reached
  from the climb (`sv.climbed.k`, `glam/materialize.bend:180`), where
  the tree found is finished by construction. So unreachable, by an
  argument no law holds. A freeze law (`freeze_copy_ok`) is the large
  item this review does not cost.
- Conclusion: `N` becomes `M ++ pls`: the copy's other nodes leave the
  tracked list, which strengthens every later frame. Good. But `hN`,
  `hB` for it are not returned (A1).

### A10. `serve_ring_exact`, `serve_root_keeps`: `hc`, and the serve that is not at the root

- `hc` (`glam/SERVE_LAWS.bend:183`): `nc` found at `k` in the index *the
  crossings leave*, a lookup in `RG.cxs.I(RG.cxs(...))`. No caller can
  compute that; the law's own comment says "over the model: no law yet
  gives a find after a removal or an insert". With A5's two lemmas a
  fold gives `cxs_look`: a key present that is no crossing's `far` is
  looked up alike before and after (no put can be at it: `cx.ab`, which
  `hok` gives at each step). Then `hc` becomes `look(I, k) == Some{nc}`
  at the start (A6: `look_member`) and "`k` no crossing's `far`", the
  ring's `unfound` again. At the root `k` is the interface
  (`at_root` is `U32.is_eq(pos, P.iface())`,
  `glam/materialize.bend:215`), and freeze makes no crossing whose far
  end is the interface's (`fz.peer.e` tests `U32.is_eq(P.base(q),
  P.iface())` and sets the root instead, `glam/freeze.bend:415`,
  `:403-406`) **[checked there]**. So `hc` reduces to a
  one-line predicate on `cs` that freeze can be shown to meet.
- **No law gives the invariant after a serve away from the root.**
  `serve_keeps` is that serve's frame; `serve_ring_exact` is the
  invariant with the leave. A serve with `at_root` false
  (`mz.root`'s `False` case, `glam/materialize.bend:57-58`; every climb,
  `:180`, and every value not at the interface) is `crossings_pend` on
  `copy_pend`, which a caller cannot chain for want of A1's facts. The
  proof should exist inside `rx.core` (`glam/SERVE_PROOF.bend:1795`)
  **[inferred from the plan's "leave_pend on crossings_pend on
  copy_pend"; I read the definition's name only]**.
  `serve_pend`: `serve_keeps`' premises without `j`, concluding `px.ok`
  over `RG.cxs(...)`. Cheap, and it is the common serve.

### A11. The invariant's facing clauses (`glam/ring_model.bend:277-320`)

- `px.off` asks of each faced port `r`, over each tracked node `n`:
  `KMd.off.port(d, r, n)` (word 0), words 1 to 3 unless `n` is live, and
  the head (`po.n`, `po.all`, `:277-286`). The word-0 and head parts
  hold **by alignment** **[inferred]**: a port not static ends in 00,
  01 or 10, so its link word `r + 1` ends in 01, 10 or 11, never 00,
  while a base and `P.at_fh()` (0, `spike/kprim.bend:171-172`) end in
  00. This is the record's first candidate ("a faced port's link word
  off nodes' words by alignment"). It could leave the invariant for a
  lemma (`off_base`), every `_pend` proof then proving less; but those
  proofs are written, so the gain is for callers only: the first
  invariant (A13) and anyone re-establishing it after the host ran.
- The rest (words 1 to 3 of a branch or a free node) is semantic: no
  live node faces a branch or a free node. Not derivable here; it is
  the allocator's and the net's well-formedness. Keep.
- `px.tw`'s first half (no node facing itself) and `copy-links-two-way`:
  kept by every step, owed at the start. Keep.
- `faces(L, v, d, L)` beside `px.off`: for a port not static `px.off`
  gives it only against nodes not live; `faces` adds the live nodes'
  words 2 and 3. Not redundant.
- `L` is a free parameter bounded on both sides (`sub(Con{s, leaves(I)},
  L)`, `sub(ps, L)`, `none.in(L, branches)`, `none.in(F, L)`), and may
  list a node twice or hold nodes of no role. A state shape in which
  `L` is computed, `Con{s, leaves(I) ++ ps}`, would make it distinct by
  `ix.lay` and `distinct(ps)`, drop four conjuncts and `copy_pend`'s
  `t`, and replace the `without` chains by `del_leaves`. That touches
  every pending law and proof: not before merge. The cheap form is one
  more conjunct, `distinct(L)` (A12).

### A12. Does a serve's conclusion give the next serve's premises?

No, on five counts, taking `serve_ring_exact`'s (or A10's
`serve_pend`'s) conclusion against `copy_pend`'s premises:

1. `hf` for the words after: not returned (A1).
2. `hLd`: `distinct` of the live nodes is no conjunct of `px.ok` and no
   law returns it. `without` and the holes' append keep it, so
   `distinct(L)` as a nineteenth conjunct is kept by every step with a
   list lemma each; or one law `cxs_distinct` beside the fold.
3. The live list's shape `Con{s, t}`: after the crossings it is a
   `without` chain, whose head is `s` only by a lemma (`s` is no leaf
   and not pending).
4. The shapes `ns ++ F` and `M ++ ns`: the next copy's fresh nodes are
   first the nodes the joins freed (`y`, `x`, the parent), which sit in
   the middle of `N`, then nodes of the free list the model does not
   know. The caller must (a) re-partition `N`, and `RG.layout` is
   order-dependent by definition (`:165`), with no permutation lemma
   **[checked: no `perm` in the proof files' definitions]**; (b) extend
   `F` and `N` by further nodes of the chain, which asks that no live
   node faces them (`px.off` over the larger `N`): the allocator's fact.
   A law `px_sub` (the invariant over any `N2` with the roles' nodes in
   it and `sub(N2, N)`) and `layout_sub` (exists as `GP.lay_sub`,
   `glam/PROOF.bend:490`, used with a distinctness premise at
   `glam/SERVE_PROOF.bend:1599`) would make
   (a) a law; (b) stays owed.
5. The depth `d`: a serve whose copy or crossings outrun the known free
   list grows the heap; every law is at one `d`. "Not claimed: growth"
   is stated, and honest. A single law `px_grow` (the invariant at
   `d + 1` over the grown words) would carry every serve law across a
   growth without restating any; it needs the tracked nodes in range,
   which no conjunct says (apart slots do not imply it). Medium to
   large; after merge.

And between serves the host runs: an interaction relinks a cursor's peer
(its word 1), allocates and frees. The facing clauses and the chain are
then re-owed whole; no law of the kernel's wiring is stated over
`px.ok`'s terms (`copy-links-two-way`: "not derived from the kernel's
wiring laws"). That is the far end of the road, named so that the
smaller steps are not mistaken for it.

### A13. Nothing establishes the invariant

Every law keeps `px.ok`; none concludes it from a state without it. The
first index is built in `glam/core.bend`: `use.top` allocates the
situating node (`:784`), `use.situ` writes its eraser, key and root
(`:779`), `use.cursor` the leaf's header, the interface as its key, its
home (`:774-775`). **[checked]** No law covers these writes; the
witnesses (`glam/witness.bend`) build by other writes. `situate_pend`:
those five writes, moved to `glam/ring.bend` as `cursor` and `leave`
were, give `px.ok(v, d, s, Has{Lf{leaf, P.iface()}}, Nil, [s, leaf], F,
[s, leaf] ++ F)` on: the two nodes apart and their own bases, `F` the
chain, the leaf's faced port not its own and off `s`, `leaf` and `F`.
With A11's alignment lemma the premises are few. A new law, no fold;
and it is the base case without which the others are conditionals on a
premise never met by a law.

### A14. `link_live`, `link_leave` (`glam/JOIN_LAWS.bend:25`, `:63`)

Lemma laws; their premises (`hs1`, `hs2`, `hx2`: `L2` is `L` but the
two) are the general form of `without`, well chosen. `hxy` is met by
`join_pend`'s lookups. `link_leave`'s `hpk` stays (no `bases`, A6). The
two could be one law over "an end that is a live node's faced port or an
outside port", but the case trees were searched out by an aid; leave
them.

### Part A: ranked proposals

By value against cost. Costs: **S** a lemma or a law projecting a proof
already written; **M** a new law with a fold or a new proof; **L** an
invariant change touching every pending law.

1. **A1 + A10: make the laws compose as laws** (S). Export `_full` for
   each step, `copy_lay`, and `serve_pend` for the serve away from the
   root. The proofs hold all of it. Without them the stated laws do not
   chain outside their proof files, and the common serve has no
   invariant law.
2. **A5: `look_put`, `look_del`** (M: two inductions on the tree, on
   `ix.inv`), then `cxs_ab`, `cxs_look` (M, folds). Discharges the
   bridge the plan owes, turns `join_pend`'s `hy` into what
   `sv.front.m` has (A7), and `serve_ring_exact`'s `hc` into a start
   lookup plus a predicate on `cs` (A10).
3. **A13: `situate_pend`** (M). The base case.
4. **A8: `join_links`, `leave_links`** (M), with the two dropped-link
   mutants. The wire made between untracked peers is the purpose, and
   no conclusion states it.
5. **A6 + A9: three premises that follow from the others** (S each, on
   one shared bit fact): `hpk` from `hpo`, `hfr` from `hp`, `hdy` from
   `hB`; and `po_static`, giving `leave_era_pend` for the static site.
   Each should be checked by Bend before a premise is dropped: all
   three are **[inferred]**.
6. **A12.2: `distinct(L)`** into the invariant (L, but mechanical), or
   `cxs_distinct` (M). Needed for a second serve.
7. **A7: the guard `c == nc` in `sv.front.m`** (code, one compare), if
   the trace of positioned demand finds no other guard.
8. **A2: `insert_dup`** (S/M): the premise `ha` failing is then provably
   a counted error.
9. **A1 larger: `layout`, `bases`, `past` into `px.ok`** (L). Best done
   with 6, once.
10. **A12.4, A12.5: `px_sub`, `px_grow`** (M, M-L): after merge.
11. **A11: `L` computed** (L): a redesign; only if 6 and 9 are being
    paid anyway.

## Part B: the once-over

Of `docs/reviews/IndexPremises_2026-11-23.md` (F1 to F8, its table, its
"Done without approval"), then of the retirement. Its opening claims
that every law passes alone, catches its mutants and that the gate
passes are **[unchecked]**: I ran nothing.

### The first reviewer's findings

**B1. F1 (`hc` over the model after the fold): agree, and it is
cheaper to meet than F1 says.** The premise is as quoted
(`glam/SERVE_LAWS.bend:183`, `:239`); the ring-era `serve_exact` took
`hc: RG.has(t, nc)` and `hu: RG.unfound(cs, view w, d, nc)`
**[checked: `git show ebc5887~1:glam/LAWS.bend`]**. The two lemmas F1
names are A5's `look_put` and `look_del`. Two additions: the put's
lemma needs the key absent (`look(I, k) == None`), which `cxs.ok` gives
at each step, and both need `ix.inv`; the same `cx.ab` keeps a put off
`nc`'s key, so "unfound" need cover the `far`s only, as before. At the
root the key is the interface, which freeze makes no crossing's far end
(A10).

**B2. F2 (`hy` over `del`): agree.** As quoted (`glam/LAWS.bend:47`,
`:318`); `join_exact` took `has(t, x)`, `has(t, y)`, `x != y`
**[checked, same commit]**. Addition: the call site does not check
`c != nc` (A7), so `kx != ky` is owed by the source's wiring, not by
anything the host's laws see.

**B3. F3 (`hLd`): agree with one correction.** The premise and its
cause are right (`glam/SERVE_LAWS.bend:69`; `px.ok`,
`glam/ring_model.bend:320-321`, has `distinct(ps)` and `distinct(F)`,
none of `L`). The parenthesis "a crossing, a leave and a join only take
nodes out of `L`; a cursor made keeps it" omits the one step that adds
to `L`: `copy_pend` concludes the live nodes `Con{s, t} ++ pls`
(`:72`), so the conjunct there needs `distinct(pls)` and the holes
apart from `Con{s, t}`; both are in hand (`pls` becomes the pending
list, `distinct(ps)`; the holes come from `ns`, `none.in(ns ++ F, L)`).
Still cheap.

**B4. F4 (`hpo` beside `hpk`): disagree in two places.**
- "Both call sites discharge it": the root's is proved (inside
  `serve_ring_exact`); the static site's is argued, not proved. "`po.all`
  holding of it by computation" is true of each `KMd.off.port(d,
  P.era(), j)` but `po.all` recurs on a universally quantified `N`
  (`glam/ring_model.bend:281-286`), so it wants an induction; and
  "`port.ok` by alignment" is a bit fact with no lemma in the proof
  files **[checked by grep of the four proof files: no definition's
  statement concludes `RG.port.ok` or `RG.po.all` from a static port;
  `P.era()` appears in `glam/PROOF.bend` only inside one proof term,
  `:1000-1001`, and in `glam/SERVE_PROOF.bend` only in the splice's
  kind lemmas]**. So `R.leave(h, P.era(), nc)`
  (`glam/materialize.bend:221`, `:365`) is covered by `leave_pend` only
  through two lemmas nobody has written.
- "No change proposed": `hpk` looks redundant given `hpo`, `sub(L, N)`,
  `hN` and `hB` (A6) **[inferred]**. The comparison with `leave_exact`
  ("took `port.ok` alone", correct: `hp: RG.port.ok(Con{s, t}, d, p)`)
  hides that the new premise subsumes the old one.

**B5. F5 (`cxs.ok`, and the record's count): agree, with an addition.**
`serve-premises-over-index` lists four premises
(`docs/decisions/serve-premises-over-index.md:11-23`), and F1 to F3 are
not among them. Nor is F4's `hpo` for an outside port, by F4's own
comparison; the record's item 2 speaks of ports "a live node faces",
not of the port a leave links. So the additions are four, not three.

**B6. F6 (frames widened to tracked nodes): agree.** The ring-era
`join_keeps` took `off.links(Con{s, t}, d, j)` and `off.node` of `x`
and `y`; `serve_root_keeps` took `hjr: off.nodes(Con{s, t}, d, j)`
**[checked: `git show main:glam/LAWS.bend`, `main:glam/SERVE_LAWS.bend`]**.
"Weaker by region, not by kind" is fair. One thing F6 could say: for
the serve's laws the region is narrower in one respect, `M` not `M ++
ns` after the copy drops the copy's ordinary nodes from the tracked
list (A9).

**B7. F7 (the new parameters): agree as far as it goes; it stops short
of the composition.** `layout`, `bases`, `past` over `M ++ ns` do
replace `hlay: layout(Con{s, t} ++ ns)`, `hbs: bases(ns)`, `hpa`
**[checked on main]**. But "the caller threads them through a serve"
understates it: no conclusion returns `full`, `layout` or `bases` (A1),
the shapes `Con{s, t}`, `ns ++ F`, `M ++ ns` are not what a conclusion
leaves (A12), and no law gives the invariant after a serve away from
the root (A10). The inventory compares each law with its ring-era self
and so misses what holds between laws.

**B8. F8 (the law check reads `LAWS.bend` alone): agree.**
`scripts/check_laws.py:3` says so and `:131` tests `path ==
"LAWS.bend" or path.endswith("/LAWS.bend")`, which `SERVE_LAWS.bend`
does not match. The counts add up: `glam/LAWS.bend` had 23 laws on main
and has 10, so 15 removed, 8 changed, 2 added, 25; `INDEX_LAWS.bend` 39
(none on main); `SPLICE_LAWS.bend` 6 against 5 **[checked by `grep -c
"^law "`]**; 25 + 39 + 2 + 4 + 1 = 71. I did not diff the 8 "changed"
one by one. A consequence F8 leaves implicit: the serve's four and the
splice's laws were never under the check on main either, so the rule
against weakening a law on main has not been enforced for them.

**B9. The table: two slips, and one omission.**
- `cross_pend` is given "—" for what it replaced, but it exists on main
  **[checked: main's law list]** and F8 counts it "changed".
- `cursor_head`'s ring-era premise is given as `enter.ok`; not checked.
- The table lists only premises *new* over the index. It therefore
  cannot show the ring-era premises the index made redundant: `hfr` and
  `hdy` were premises of the ring's `copy_pend` too **[checked on
  main]** and now follow from `hp` and `hB` (A9) **[inferred]**; the
  ring's `hc: KMd.chain(ns, ...)` did move into `hp`.

### The retirement (`ebc5887`, `ac241c7`, `2578713`; the plan's `.retire`)

**B10. The disposition's arithmetic holds.** Of main's 23 laws, six
were over the index before `.retire` (`cursor_pend`, `join1_pend`,
`cross_pend`, `crossings_pend`, `crossings_keeps`, `leave_keeps`),
leaving 17 ring-era; 15 retired, `cursor_head` and `join_keeps`
restated. `ebc5887` carries 15 `Law:` trailers, the 15 names of the
plan's disposition **[checked]**. `rg.pred` and the walk are gone from
`glam/ring.bend` **[checked: the file]**.

**B11. "`R.cursor` and `R.join1` only in a crossing": borne out.** No
module but `glam/ring.bend` calls either (`glam/materialize.bend` calls
`R.leave`, `R.join`, `R.crossings`, `R.rg.find`, `R.rg.situ` only; the
one-net path the same) **[checked by grep over `glam/*.bend`]**. So
`cursor_keeps` and `join1_keeps` are replaced by `crossings_keeps`
without loss to a caller.

**B12. Nothing retired stated the wire made; nothing does now.**
`join_exact`, `join1_exact`, `leave_exact` concluded `RG.ring.ok` only,
so the retirement lost no positive claim about the link. The gap is
A8's, older than the branch.

**B13. `find_exact` to `find_tree`: kept whole.** `find_exact` gave the
heap back with `RG.first`; `find_tree` gives the heap back with
`IM.ix.look` (`glam/INDEX_LAWS.bend:49-60`), and `at_first` ties the
two (`:243`). `cursor_pos` (word 2 holds `src`) survives only inside
`ix.real` of the put's tree: true, but a caller wanting the word must
unfold the realization. Minor.

**B14. `ac241c7`'s "22 defs no law reached": the criterion is not the
one applied.** The message says the ring's model "which no law states
anything over now" went. By that criterion `RG.apart`, `RG.apart.all`
and `RG.minus` (`glam/ring_model.bend:59`, `:80`, `:252`) should have
gone too: no `*LAWS.bend` names them; only `glam/PROOF.bend` and
`glam/SERVE_PROOF.bend` do **[checked by grep]**. They stay because
proofs reach them, which is the right criterion (the plan's
"reachability cut"); the message's wording is looser than what was
done. Harmless. `RG.first` and `RG.pos.is` are reached by a law
(`at_first`), correctly kept.

**B15. Stale text the retirement left, beyond what "Not done" lists.**
"Not done" names the materializer's and the core's comments. Also:
- `glam/ring.bend:66-67`, on `join`: "two cursors x and y of one index
  (or a placeholder x, not in it, and a cursor y)". Now wrong, not
  merely stale: `jn.w` unlinks `x` from its home's index (`:60`), so a
  placeholder `x` would have its word 3 read as a home. `join1` is that
  case.
- `glam/ring_model.bend:57-58`, `:70-71`, `:88`, `:190-191` still speak
  of the ring's links and "the exact ring's laws".
- `ring-ports-faced-off-positions` was to be "restated for the tree's
  members with them" (`docs/decisions/cursors-indexed.md:69-70`). It
  was not: its last change predates the branch (`36ecfef`), and its
  consequences still name `RG.ring.ok`, `node.ok`, `enter.ok` and
  `leave_exact`, none of which exists. A maintainer record, so a
  question for the maintainer, as the two record changes under "Done
  without approval" were.
- `2578713`'s "stale names out" touched `glam/PROOF.bend`,
  `glam/SERVE_PROOF.bend`, `glam/INDEX_LAWS.bend`, `glam/witness.bend`
  and `docs/Proving.md` only **[checked: its stat]**; the commit's
  title is wider than its diff.

**B16. Retired, and still mattering: one, by restatement.** The ring's
`leave_exact` and `join_exact` took membership (`has(t, c)`), which a
caller has; their replacements take model lookups (`hc`, `hx`, `hy`).
`look_member` restores membership for `hc` and `hx`; for `hy` nothing
does yet (B2). That is the one place where the retirement left a
caller worse off than the ring did, and F2 names it.

## Summary

- Done: the premises of 16 laws judged (Part A), the first reviewer's
  eight findings and the retirement checked against the source (Part B).
  Nothing built, typechecked or run.
- Least confident: the three redundancies (`hpk`, `hfr`, `hdy`), each
  resting on an alignment fact I reasoned but Bend has not checked; that no
  conclusion states the wire between untracked peers (A8); that `q != pos` has
  no guard upstream (A7).
- Next: the ranked list in Part A, items 1 to 5 before merge if the
  maintainer wants the laws to compose as stated.
- Not done: `docs/reviews/README.md` has no entry for this file; I was
  to write this file only.
