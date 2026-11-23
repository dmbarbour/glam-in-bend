# The laws over the index: their premises, before merge

Part 1 is the agent's inventory; Part 2 the tightening proposed with the
second reviewer, whose review is kept as written beside this one
(`IndexPremisesFable_2026-11-23.md`, A1 to A14, B1 to B16).

The agent's inventory of the premises the laws over a copy's index take
(`cells-freeze.sharing.cursors.index`, side branch `cursor-index-spike`),
for the review the maintainer asked before merge (2026-11-23: "We'll do
a big review and discuss what can be tightened up or improved before
merge"). Each law's premises against the ring-era law it replaced,
those that shift a burden to the caller first, then what was done on the
branch without the maintainer's approval. Every law here passes alone
and catches each of its mutants; every serve law is shown met at
concrete instances (its witnesses' premises proved by computation,
`results/index_bits/retire/wcheck.py`); the gate passes (ac241c7).

## Findings

**F1. A lookup after the crossings stated over the model** (the serve's
exact and root frame laws). `serve_ring_exact` and `serve_root_keeps`
take

    hc: IM.ix.look(RG.cxs.I(RG.cxs(cs, view(map'), dm, I, Con{s, t} ++ PLS, F)), k) == Some{nc}

where the ring-era `serve_exact` took `RG.has(t, nc)` and
`RG.unfound(cs, view w, d, nc)` (no crossing looks for nc's position).
The model is executable and shares none of the code's finds, but a
caller now owes a fact about the index after the whole fold. Discharge:
two index laws, a lookup after a removal and after an insert at another
key (`look(del(I, x, kx), k) == look(I, k)` for `kx ≠ k`, and the
put's likewise), then the premise over `I` with nc's key unfound, as
before. Recommended before merge if cheap; otherwise listed.

**F2. The join's second cursor found in the index without the first**
(`join_pend`, `join_keeps`): `hy: look(del(I, x, kx), ky) == Some{y}`.
The ring-era `join_exact` took `has(t, y)` and `x ≠ y`. Discharged by
F1's first lemma, `hy` then over `I` with `kx ≠ ky`.

**F3. The live nodes distinct** (`copy_pend` and the serve's three):
`hLd: RG.distinct(Con{s, t})`, which the ring's `ring.ok` gave. The
invariant (`RG.px.ok`) does not carry it: `layout(N)` makes `N`
distinct, but `L ⊆ N` lets `L` list a node twice. Discharge: a
conjunct `distinct(L)` in `px.ok`, kept by every step (a crossing, a
leave and a join only take nodes out of `L`; a cursor made keeps it).
Reported 2026-11-23, unresolved.

**F4. The leave's port off every tracked node** (`leave_pend`,
`leave_keeps`): `hpo: RG.po.all(p, Nil{}, d, N)` beside `hpk:
RG.port.ok(L, d, p)`, where `leave_exact` took `port.ok` alone. Both
call sites discharge it: the copy's root port is a fresh node's that is
no hole (proved inside `serve_ring_exact`, `off_fresh`, `off_fresh2`);
the eraser is static, `po.all` holding of it by computation and
`port.ok` by alignment (`ring-ports-faced-off-positions`). No change
proposed.

**F5. The crossings' premises in turn** (`crossings_pend`,
`crossings_keeps`, the serve's three): `hok: RG.cxs.ok(...)`, each
crossing's position absent where it makes a cursor and room on the free
list for its branch: `serve-premises-over-index` items 1 and 4, ruled
reasonable. The record names four premises; F1 to F3 are additions it
does not list. Asked: rule on them, or have the record list them.

**F6. The frames' regions widened to the tracked nodes.** The ring-era
frames allowed the ring's links and the nodes a step frees
(`join_keeps`: the members' word 3, x's and y's words; `serve_root_keeps`:
`off.nodes(Con{s, t})`). Over the index a frame allows every word of a
tracked node (`off.nodes(N, d, j)`; the serve's `hjM: off.nodes(M, d,
j)`), since an insert takes a branch from the free list and a removal
frees one. The claims are weaker by region, not by kind: what the
demand's walk resumed reads (outside the tracked nodes) is still bound.
Tightening would state, per step, the words of the branches the step
touches; no consumer needs it yet.

**F7. The invariant's new parameters** (`I`, the tracked nodes `N` or
`M ++ ns`, the free list's first nodes `F`): the caller threads them
through a serve (`RG.cxs` computes them after the crossings). Their
premises (`layout`, `bases`, `past` over `M ++ ns`) replace
`layout(Con{s, t} ++ ns)` and the ring. No change proposed.

**F8. The law check reads `LAWS.bend` alone** (`scripts/check_laws.py`:
"A law is a `law <name>:` block in a file named LAWS.bend"). A trial
merge onto main (staged, checked with `--commit-msg`, aborted) asks
trailers for `glam/LAWS.bend`'s 25 changes only, while the merge adds,
removes or changes 71 laws: `glam/LAWS.bend` 25 (`join_pend`,
`leave_pend` added; the 15 ring-era laws removed; `cross_pend`,
`crossings_keeps`, `crossings_pend`, `cursor_head`, `cursor_pend`,
`join1_pend`, `join_keeps`, `leave_keeps` changed),
`glam/INDEX_LAWS.bend` 39 added, `glam/JOIN_LAWS.bend` 2 added
(`link_live`, `link_leave`), `glam/SERVE_LAWS.bend` 4 changed (the
serve's four), `glam/SPLICE_LAWS.bend` 1 added (`splice_free`); the
list is `results/index_bits/retire/merge_laws.txt`. The merge commit
names all 71. Asked: should the check read every `*LAWS.bend` (main's
history would then be rechecked against those files too)?

## Per law

The ring-era counterpart, then the premises over the index that it did
not have. `hf`, `hd32` (and `hfm`, `hdm`) are as before throughout.

| Law | Replaced | Premises new over the index |
|---|---|---|
| `cursor_pend` | `cursor_ok`, `cursor_pos` | `hN`, `hB`, `hp: px.ok(..., Con{x, ps}, L, take(I, b, F), N)`, `ha: look(I, src) == None` |
| `cursor_head` | `cursor_head` (`enter.ok`) | as `cursor_pend` |
| `join1_pend` | `join1_exact` | `hN`, `hB`, `hp`, `hy: look(I, k) == Some{y}` |
| `cross_pend` | `cross_pend` (over the ring, on main) | `hp` (free list per `cx.F0`), `ha: cx.ab` |
| `crossings_pend`, `crossings_keeps` | `serve_exact`'s first half, `cursor_keeps`, `join1_keeps` | `hp`, `hok` (F5); the frame `hj: off.nodes(N)` (F6), `hjh`, `hjf` |
| `leave_pend` | `leave_exact` | `hp`, `hc: look(I, k) == Some{c}`, `hpo` (F4), `hpk` |
| `leave_keeps` | `leave_keeps` | as `leave_pend`; `hj: off.nodes(N)` (F6), `hjh`, `hjp`, `hjw` |
| `join_pend` | `join_exact` | `hp`, `hx`, `hy` over `del` (F2) |
| `join_keeps` | `join_keeps` | as `join_pend`; `hj: off.nodes(N)` (F6), `hjh`, `hju`, `hjw` |
| `copy_pend` | `copy_pend` (ring) | `hN`, `hB` over `M ++ ns`, `hp` with `I`, `F`, `M` (F7), `hLd` (F3) |
| `serve_keeps` | `serve_keeps` (ring) | as `copy_pend`; `hok` (F5); `hjM: off.nodes(M)` (F6) |
| `serve_ring_exact` | `serve_ring_exact` (ring) | as `serve_keeps`; `hc` (F1) for `hnc`, `hu` |
| `serve_root_keeps` | `serve_root_keeps` (ring) | as `serve_ring_exact`; `hj`, `hjM`, `hjh`, `hjf` |

`JOIN_LAWS.bend`'s `link_live` and `link_leave` are lemmas over the
facing (`faces`, `px.off`, `px.tw`) the pending laws compose; `link_leave`
takes F4's premises.

## Done without approval

On the branch, by the plan's step `.retire` and the maintainer's
"continue to get things working based on best judgement":

- **Deleted a maintainer record**, `ring-walks-fueled-by-heap`, with
  its index line: the walks it fueled are gone, as `cursors-indexed`
  foresaw ("retires with the walks it fuels"). Its slug is still cited
  there and in the plan's and reviews' history.
- **Revised a maintainer record**, `corruption-reported-when-cheap`:
  its rule now lives in the index's descents (`glam/index.bend`), the
  walks' consequence restated for them; rev bumped to 268f30d.
- **Deleted two laws that still passed**, `pred_in_ring` and
  `pred_exact`, with the dead walk they were about (`rg.pred`), and
  thirteen that failed against the indexed code; restated three over the
  index (`cursor_head`, `join_keeps`, `leave_keeps`). The merge's
  `Law:` trailers name all of them.
- **Removed the `SPIKE` markers** from `glam/ring.bend`'s routes through
  the index, and its walk code and comments: the index is the decided
  architecture (`cursors-indexed`); the module's names stay the ring's.
- **Removed the ring's model** (22 defs of `glam/ring_model.bend`, no
  law reaching them) and the ring's witness builders.

## Not done

- The materializer's and the core's comments still say ring.
- F1 and F2's lemmas, F3's conjunct.

## Part 2: what to tighten, with the second reviewer

The second reviewer judged every premise from the laws and the code
before reading Part 1, then checked Part 1 against the source. Its
corrections, each checked here against the source:

- **B3 (F3)**: the copy adds to the live nodes (`Con{s, t} ++ pls`), so
  a `distinct(L)` conjunct needs the holes distinct and apart from
  `Con{s, t}` there; both in hand. Accepted.
- **B4 (F4)**: the eraser's call site (`R.leave(h, P.era(), nc)`,
  `glam/materialize.bend:221`) is argued, not proved: `po.all` of a
  static wants an induction over `N` (`po_static`), and `port.ok` of a
  static by alignment a bit lemma no proof has. And `hpk` looks implied
  by `hpo`, `sub(L, N)`, `layout`, `bases` (A6). Accepted: F4's "no
  change" withdrawn.
- **B5 (F5)**: the additions beyond `serve-premises-over-index` are
  four, `hpo` among them. Accepted.
- **B7, A12 (F7)**: the inventory compared each law with its ring-era
  self and missed what holds *between* laws: no conclusion returns the
  words full, the layout or the bases; the shapes a conclusion leaves are
  not the next copy's; no law gives the invariant after a serve away from
  the root (the common serve). Accepted: the largest gap found.
- **B9**: `cross_pend` existed on main (the table fixed); `cursor_head`'s
  ring-era premise was `enter.ok` (checked: `git show main:glam/LAWS.bend`).
- **B15**: `glam/ring.bend`'s comment on `join` ("or a placeholder x,
  not in it") is now wrong, not stale (`join1` is that case);
  `glam/ring_model.bend` keeps ring wording; and
  `ring-ports-faced-off-positions`, which `cursors-indexed` said would be
  restated for the tree, was not: its consequences name retired laws. A
  maintainer record: asked.
- **A7**: `sv.front.m` joins `nc` with the cursor found at the frontier
  without testing that they differ (`glam/materialize.bend:200-202`,
  checked); a port facing its own position would free one node twice.

Checked here as well: `look_member` (`glam/INDEX_LAWS.bend`) gives
`look(I, word(y + 2)) == Some{y}` of a leaf of a real index, so a
lookup premise over `I` is membership at the call site (A6); `SV.dyn`
is "none static" (`glam/serve_model.bend:97`), which `bases` implies by
alignment (A9).

**Prototyped since** (a scratch copy, `results/index_bits/review/
gen_ldo.py`): the lookup after a removal at another key
(`look_del_other.k`, about 100 lines) and after an insert at another key
(`look_put_other.k`, about 60), both through `look_at` (a lookup is the
leftmost leaf at its key under the invariant; a removal's cut and an
insert's place keep the other leaves' order), check against
`glam/INDEX_PROOF.bend`. A5's two lemmas are small, not medium.

### Proposals, ranked

Cost: **S** a lemma or a law projecting a proof already written; **M** a
new law with a fold; **L** an invariant change touching every pending
law. "Before" is proposed before merge.

| # | Proposal | From | Cost | When |
|---|---|---|---|---|
| P1 | The laws compose as laws: `_full` for each step, `copy_lay` (layout and bases of `M ++ pls`), `serve_pend` (the invariant after a serve away from the root) | A1, A10 | S | before |
| P2 | `look_del_other`, `look_put_other` (prototyped), then `join_pend`'s and `join_keeps`' `hy` over `I` with `x != y`, and the serve's `hc` as `nc` a leaf at the start (`look_member`) and no crossing's far end at its key, through the crossings' fold | F1, F2, A5, A7, A10 | S + M | before |
| P3 | Three premises implied by the others, each checked by Bend before it goes: `hpk` from `hpo` (`port_of_po`), `hfr` from `px.off` (`faces_fresh`), `hdy` from `bases` (`dyn_of_bases`), on one alignment lemma; with `po_static`, a `leave_era_pend` for the eraser's site | A6, A9, B4 | S each | before |
| P4 | Stale text: `ring.bend`'s `join` comment, `ring_model.bend`'s ring wording | B15 | S | before |
| P5 | `distinct(L)` a conjunct of the invariant, for a second serve | F3, A12 | L | after |
| P6 | `situate_pend`: the first index's writes (`glam/core.bend:774-784`) give the invariant, the base case | A13 | M | after |
| P7 | `join_links`, `leave_links`: the wire a join or leave makes between untracked peers, with dropped-link mutants | A8 | M | after |
| P8 | `cxs_ab`, `cxs_room`: the crossings' stepwise premise from a start condition (positions absent and distinct, a count of free nodes) | A5 | M | after |
| P9 | `insert_dup`: an insert meeting its own key is a counted error, the words otherwise kept | A2 | S/M | after |
| P10 | `layout`, `bases`, `past` folded into the invariant; or the live nodes computed (`Con{s, leaves(I) ++ ps}`) | A1, A11 | L | after, with P5 |
| P11 | `px_sub` (the invariant over a sub-list of tracked nodes), `px_grow` (across a heap's growth) | A12 | M, M-L | after |

### Asked of the maintainer

1. Which of P1 to P4 before merge (recommended: all four; P2's core is
   built).
2. A7: test `c != nc` in `sv.front.m`, one compare on a path taken once
   a serve, by `corruption-reported-when-cheap`, or owe it to the
   source's wiring as a law of freeze?
3. F8: should the law check read every `*LAWS.bend` (main's history then
   rechecked against them too)?
4. B15: restate `ring-ports-faced-off-positions` for the index's live
   nodes, as `cursors-indexed` said it would be?
