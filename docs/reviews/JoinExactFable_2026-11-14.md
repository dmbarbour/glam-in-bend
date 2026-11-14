# `join_exact` reviewed — 2026-11-14

Written by a Fable sub-agent as the second reviewer, at the maintainer's
request relayed by the agent (2026-11-14), independently of the agent's
own review, which it did not read. The commit reviewed: `cbd26cc` on the
branch `host-ring-exact`, forked from `main` at `075b251` (`main` has
since recorded `serve-write-sets-hybrid`, `f3bca8f`, read here with
`git show`). The subject: `join_exact` (`glam/LAWS.bend:228-253`), its
siblings `pred_exact`, `unlink_exact`, `insert_exact` (`:168-217`), the
model (`glam/ring_model.bend`) and the code (`glam/ring.bend`). Nothing
was run but read-only `git` and `grep`; the proofs were read, not
rechecked.

## The worked ring

One ring serves every finding. Words a perfect tree of depth `d = 6`
(64 words); the header holds words 0 to 27, the free list's head at
word 0 (`P.at_fh()`, `spike/kprim.bend:171`). The situating node `s` is
at 36, as `glam/test_materialize.bend:69-70` lays it; cursors `x`, `y`,
`z` at 40, 44, 48.

| node | word 0 | word 1 (faces) | word 2 (position) | word 3 (next) |
| --- | --- | --- | --- | --- |
| `s`, 36 | header, form 2 | static eraser | handle | 40 |
| `x`, 40 | header, kind 18 | 53 | 7 | 44 |
| `y`, 44 | header, kind 18 | 60 | 9 | 48 |
| `z`, 48 | header, kind 18 | 57 | 5 | 36 |

The members' word 3 are words 39, 43, 47, 51: `RG.ring(v, 6, 36, [40,
44, 48])` holds (`glam/ring_model.bend:109-110`). `x` faces 53, port 1
of a copied node at 52 (link word 54); `y` faces 60, port 0 of a node at
60 (link word 61). `R.join(h, 40, 44)` (`glam/ring.bend:156-167`)
writes, in order: 54 := 60 and 61 := 53 (the link); 39 := 44 (the walk
from 40 finds 36 before it); 39 := 48 (the walk from 44 finds 36 again);
40 := 0, 41 := head, 0 := 11 (x freed, `kprim.bend:579-582`); 44 := 0,
45 := head, 0 := 12. The ring left: `s`, then `z` alone.

`join_exact` states this ring as `pa = []`, `x = 40`, `pb = [44, 48]`,
then `pa ++ pb = [44, 48]` as `pc = []`, `y = 44`, `pd = [48]`, and
concludes `RG.ring(v', 6, 36, [48])`.

## Q1. The fourteen premises

| premise | says | needed | true as the code runs | how to discharge |
| --- | --- | --- | --- | --- |
| `hf`, `hd32` | the words a perfect tree, depth below 32 | yes: every heap law of the spike's takes them (`spike/LAWS.bend`) | yes, by construction (`KM.m_new`, `KM.grow`) | keep; a heap record carrying them is a later convenience |
| `hr` | the ring exact, split at `x` | the subject | the materializer's rings, once every step has its exact law | keep (the split, Q3) |
| `hsp` | `pa ++ pb` split at `y` | for the second unlink | — | Q3: replace by `has` and `without` |
| `hn` | fewer than a million cursors | for both walks | yes, for the rings seen; not in general | Q2 |
| `hbx`, `hby` | `x`, `y` node bases | only to rewrite `hx0..hy1` to `P.base(x)` | yes: every member came from `P.node`, `(fh - 1) << 2` (`node_index`) | F2 |
| `hu`, `hw` | the faced ports' link words no member's word 3 | yes | yes (F3) | F3: a `faces` predicate of the ring's own; not `faces_out` |
| `hx0`, `hx1`, `hy0`, `hy1` | the frees' words 0 and 1 no remaining member's word 3 | yes | yes, by 4-alignment | F4: from `bases`, or a model of whole nodes |
| `hh` | the head's word no remaining member's word 3 | yes | yes: 0 against a word 3 at 3 mod 4 | F4 |

### F1. Two premises carry the proof; twelve are side conditions of the heap's layout

`glam/LAWS.bend:239-252`. Of the fourteen, `hr` and `hsp` state the
ring and `hn` the fuel; the other eleven say which words the join writes
are no member's word 3 (`hu`, `hw`, `hx0`..`hh`, seven) or let the proof
say so (`hf`, `hd32`, `hbx`, `hby`). None is false of the code; none is
redundant against the others as stated: each is consumed once in
`join_exact.go` (`glam/PROOF.bend:1180-1225`): `hu`/`hw` by `lx_ring`
(`:1133`), `hx0`/`hx1` and `hy0`/`hy1` by the two `fr_ring` calls
(`:1160`), `hh` by both, `hbx`/`hby` by the two `ME.subst` rewrites in
front of them. The smell is real but it is the model's: the ring model
knows its members' word 3 and nothing else about them, so every fact
about their other words, their alignment and the header must enter as a
premise. Verdict: adjust by enriching the model (F2 to F4), not by
trimming premises one at a time.

### F2. `hbx`, `hby`: used only as rewrites; two ways out

`glam/LAWS.bend:244-245`; used at `glam/PROOF.bend:1206` and `:1208` solely to
turn `hx0` (about `x`) into `fr_ring`'s `h0` (about `P.base(x)`,
`kprim.bend:576`, the low two bits cleared). So they can go at no cost
by stating `hx0`, `hx1`, `hy0`, `hy1` on `P.base(x)` and `P.base(y)`
(as `free_keeps` states its own, `spike/LAWS.bend:473-489`): ten
premises left, nothing proved anew. The statement gets uglier where
every reader knows `x` is a base.

The principled way: a model predicate `bases(ys)`, every member `m` with
`U32.is_eq(P.base(m), m)`, a conjunct of `ring`. Kept by an unlink and a
join (sublists) and by an insert given the cursor inserted is a base,
which the serve has from `node_index` and the shift: `((fh - 1) << 2)
.&. 4294967292 == (fh - 1) << 2`. That one fact is the single arithmetic
debt of this whole review: `lawful-words`' territory, no package states
it (`ArrayLaws_2026-11-13.md` F5), and Bend's U32 masks have no laws
(`docs/BendIssues.md`). Cost it before choosing: if the hub cannot give
it in an afternoon, take the free route first and leave `bases` for the
model's next touch. A third route, a kernel `P.free_node(h, b)` that
skips the mask for a base the caller vouches for, removes `P.base` from
the ring laws entirely at the price of a primitive and its keeps law;
not recommended while the mask costs one `and` and `free_keeps` is
already proved over it. Verdict: adjust (`bases` in the model; the
`P.base` restatement meanwhile).

### F3. `hu`, `hw`: true, and the plan's `faces_out` is the wrong predicate for them

`glam/LAWS.bend:246-247`; consumed by `lx_ring`, `glam/PROOF.bend:1133`.
The link writes `u + 1` and `w + 1`, the link words of the two faced
ports (`P.link_xx`, `kprim.bend:441`, each unless static). A link word
is a member's word 3 only where the port is a member's port 2: `u + 1 =
m + 3` iff `u = m + 2`. In the worked ring: 54 and 61 against {39, 43,
47, 51}, both off.

Two facts fix the right predicate.

Cursors may face each other. Give `x` word 1 = 44 and `y` word 1 = 40,
the two cursors an active pair. Then `u = 44`, `w = 40`, the link writes
45 := 40 and 41 := 44 (their own words, unchanged in value), and `hu`,
`hw` hold: 45 and 41 are no word 3. `join_exact` applies and is true.
But the plan's candidate, `faces_out` ("every member's word 1 a static
or a port of a node outside the ring", `docs/plans/Cells_2026-11-09.md`,
`.host.ring.exact`, after `JoinLawsFable_2026-11-14.md` F6), is false
of this ring, so it cannot be the invariant that discharges `hu`. The
same for `x` facing a third member `z`'s port 0 (word 41 = 48): `u + 1
= 49`, `z`'s word 1, written := 60; `hu` holds, `faces_out` does not.
Nor is `faces_out` kept across rings: a join in ring A writes `w + 1`
where `w` may be a port of ring B's cursor, which then faces what `y`
faced, perhaps a cursor of B. The plan step should drop `faces_out` as
stated (its "Next: `bases` and `faces_out`").

Cursors may face a port 2. The freeze links a placeholder to `T.TE{i,
p}` for any port `p` of a copied node (`glam/freeze.bend:284`), port 2
of a three-port node included; then `u + 1` is that node's word 3, and
the premise holds only because the node is no member. So "no member
faces a port 2" is false of the code; the statement must be about the
members' word 3, as `hu` is.

The predicate the proof consumes, member by member: `faces(v, d, ys)`,
for every member `m` of `ys` with word 1 holding a non-static `r`,
`off.links(ys, d, r + 1)`. It holds in all three cases above. Kept by an
unlink (no word 1 written, the ring a sublist); by a join: the link
changes a member's word 1 only where that member is `u`'s or `w`'s node
(`z` above), whose new word 1 is `w` or `u`, whose `+ 1` is off the
links by the other cursor's instance, and the ring after is a sublist;
by an insert given two facts about the new cursor `x`: its own word 1
off the links (what a placeholder faces, a copied node's port,
`freeze.bend:284`), and no member's faced link word in `x`'s word 3
slot (`r + 1 = x + 3` iff a member faces `x + 2`, a port the placeholder
has none of, `fz.hole`). The serve discharges both from the splice. With
`faces` a conjunct of `ring`, `hu` and `hw` are derived by `has`.
Verdict: keep the premises now; replace `faces_out` in the plan by
`faces` as above; derive at the model's next touch.

### F4. `hx0`, `hx1`, `hy0`, `hy1`, `hh`: alignment facts the model does not know

`glam/LAWS.bend:248-252`; consumed by `fr_ring` (`glam/PROOF.bend:1160`)
as `h0`, `h1`, `hh`. A free writes `base(r)`, `base(r) + 1` and word 0.
A member's word 3 is 3 mod 4; `x` and `x + 1` are 0 and 1 mod 4, word 0
is 0: as indices they never meet. Slots are indices mod `2^d`
(`defs.bend:34`, `Nat.mod(U32.to_nat(i), Nat.pow(2n, d))`), which keeps
residues mod 4 for `d >= 2`, where all five hold; at `d <= 1` every
base's word 3 has the one slot (1, or 0), so `hr`'s `apart.all` fails
for any ring with a cursor and excludes those depths (at `d = 1`, 41 and
39 share slot 1, so residues alone would not do). So all five are
true as the code runs and follow from `bases` (F2) by one lemma family
over `Nat.mod` and `Nat.pow` (the hub has `div_mod_eq`, `zero_mod`,
`mod_self`; not "a multiple of 4 under mod `2^d`", to be written), with
the `d < 2` edge handled through `hr`.

The other route needs no arithmetic: widen the model's distinctness from
word 3s to nodes. Today `apart(ys, d, x)` says `x`'s word 3 slot is no
member's word 3 slot (`ring_model.bend:54-59`); a `disjoint(ys, d, x)`
would say none of `x`'s four word slots is any member's word 3 slot and
none of theirs is `x`'s. Then `hx0`, `hx1`, `hy0`, `hy1` are
`disjoint`'s instances at `x` and `y`, by `has`, with no lemma on
residues; `hh` stays, or becomes a conjunct `off.links(Con{s, t}, d,
P.at_fh())` of `ring`, kept by every operation (sublists; an insert
given the new cursor's word 3 is not word 0, which `disjoint` against
the header could also say). The price: the `apart_*` and `ap_*` lemmas
(`glam/PROOF.bend:785-830`, `928-972`) re-proved over the wider
predicate, and `insert_exact`'s `hx` widened to `disjoint`, which the
serve discharges from freshness exactly as it would `apart`. Judging by
the present lemmas, two or three hundred lines, mechanical, no U32 bits.

Note the asymmetry the law keeps and a model route must reproduce:
`hu`, `hw` are over the ring before (`Con{s, pa ++ x :: pb}`, the link
comes first), `hx0`..`hh` over the ring after (`Con{s, pc ++ pd}`, the
frees come last). With `bases`, `faces` and `disjoint` in `ring`, every
fact is stated before and the after-facts come by sublist (`ap_remove`'s
shape, `:956`). Verdict: adjust; prefer `disjoint` in the model, since
it holds by computation and costs no arithmetic; take the `bases` route
only once F2's mask lemma exists anyway.

## Q2. The fuel

### F5. A walk out of fuel corrupts silently; that is the code's fault before it is the law's

`glam/ring.bend:97`, `rg.pred.go(1000000n, ...)`; the same literal at
`:66` (`rg.find`) and `:151` (`rg.situ`), and in the materializer's
climb (`glam/materialize.bend:194`, `:329`). At fuel 0 `rg.pred.go`
returns its walk as it is (`:78-80`), `rg.pred.w` yields the last node
reached (`:90-93`), and `rg.unlink` writes that node's word 3
(`:99-109`): a ring of a million cursors is left with a wrong link and
no error. `rg.find` out of fuel answers `None`, so `mz.found` inserts a
second cursor at a position the ring already holds
(`glam/materialize.bend:56-62`); `rg.situ` returns wherever it stopped.
No `P.err_if` (`kprim.bend:269`) is reached. Under Working Rules a
failure on user input is reported, never silent; the laws' premise `hn`
is where that silence shows: the law says nothing past a million
members. Whichever option below is taken for the laws, the walks should
report exhaustion (`P.err_if` on fuel 0, as the splice does,
`glam/splice.bend:58-68`), or be given fuel the heap proves enough (B).
Verdict: adjust the code.

### F6. Taking the literal out: three options

The proof is already abstract: `wk` (`glam/PROOF.bend:865`) walks with
any fuel `f` given `length(L) < f`; only `pred_exact.go` (`:897`) and
the two unlink calls in `join_exact.go` (`:1198`, `:1204`) pass the literal,
and `join_exact` carries it to the second walk by `len_mid` and
`lt_trans` (`hn1`, `hn2`, `:1201-1202`).

(A) A named constant. `def fuel() -> Nat: 1000000n` in `glam/ring.bend`,
the three walks calling it, the three laws stating `Nat.is_lt(length,
R.fuel())`. This is the maintainer's "abstract static-variable fuel
limit": no number in a law, the premise kept, its meaning "fewer
cursors than the walk's fuel" now literal. Cost: nil (a nullary def
reduces where the proof needs the number; the lemma `wk` sees a
variable). What it does not do: justify the number. The kernel allows
`2^28` nodes (`net-capacity`, `kprim.bend:218-222`), so a ring can
exceed any constant below that, and nothing in the heap bounds a ring
by a million.

(B) Fuel from the heap, and the premise derived. A ring's members have
distinct word 3 slots (`apart.all`), slots are below `2^d`, so a ring
has at most `2^d` members, `s` included, and any fuel of at least `2^d`
suffices: `length(t) < 2^d` is a pigeonhole on `apart.all` alone, no
range premise, since slots already wrap. The heap knows `2^d`: `at_wcap`
holds the nodes that fit, set to `cap >> 2` where `cap` is the words
(`kprim.bend:466-470`, `KM.m_new`, `KM.grow` doubling), so the words are
`4 * wcap`. A walk given `U32.to_nat(wcap) * 4` as fuel, one header read
per walk, can never run out on an exact ring; `hn` leaves all three laws,
replaced by one heap-consistency premise, `4 * wcap == 2^d` (stated as
`node_keeps` states the head, `spike/LAWS.bend:404`), which the kernel's
growth keeps and a kernel law could own later. Cost: the pigeonhole over
lists of pairwise distinct `Nat`s below a bound (the hub's `list.bend`
has `length_*` lemmas but no `nodup`; a hundred to two hundred lines, a
hub candidate), the consistency premise, and a walk on a corrupt ring
that runs to the heap's size before stopping rather than a million
steps. This is Proving.md's "a proof that the fuel suffices ... by a
potential", the potential the ring's length.

(C) Fuel threaded from the caller: `rg.pred(h, f, x)`, `join(h, f, x,
y)`, laws over any `f`. Moves the literal into the serve, where it must
still be stated or justified; nothing gained.

Verdict: (A) now, in this branch, one commit; (B) as the step that
removes `hn`, after the model's touch (Q4's order), with the pigeonhole
offered to the hub. Not (C).

## Q3. The list structure

### F7. The two splits are the law's existential, pushed to every consumer

`glam/LAWS.bend:241-243`. `hr` names the ring as `pa ++ x :: pb` and
`hsp` names `pa ++ pb` as `pc ++ y :: pd`; the conclusion is `pc ++ pd`.
It is correct and it is the cheapest to prove: the proof file's header
records the choice ("a list split at a member is a premise, not an
existential"). Two costs fall on the consumer. A serve has `y` from
`rg.find` (a member at position `q`, once that law exists) and `x` as
the served cursor: it knows `has(t, x)` and `has(t, y)`, and must
manufacture `pa`, `pb`, `pc`, `pd` to apply the law; two joins in a row
split and resplit. And the two-split form gets `x /= y` silently:
`apart.all` forbids `x` in `pa ++ pb`, so a self-join is outside the
law's domain without the law saying so; `.host.join.self` has nowhere
to land its proof.

The better statement, the invariant by computation (AGENTS.md, Laws):
`without(ys, x)`, the list with the first `x` removed, and `before(ys,
s, x)`, the member listed before `x` (or `s`):

    ring(v, d, s, t), has(t, x), has(t, y), U32.is_eq(x, y) == False
      |- ring(v', d, s, without(without(t, x), y))

with `unlink_exact` as `ring(.., without(t, x))` and `pred_exact` as
`pred(x) == before(t, s, x)`. Three list premises replace the two
splits; the self-join premise is explicit, which is exactly what
`.host.join.self` wants to discharge at `sv.front.m`
(`glam/materialize.bend:188-194`); two joins compose by nesting
`without`. On the worked ring: `without(without([40, 44, 48], 40), 44)
= [48]`, `before([40, 44, 48], 36, 44) = 40`.

The cost. Keep the split-form proofs as the internal `.go` lemmas they
already are, and add: `split_of_has(t, x, h) -> Split(t, x)`, a
dependent pair of `pre`, `post` and `t == pre ++ x :: post`, by
induction on `t` (the proofs already consume such a pair, `LAT.Mirror`,
`glam/PROOF.bend:897-901`; the header's lesson is about the law's
statement, not about pairs as such); `without_mid`, `apart.all(pre ++ x
:: post) -> without(pre ++ x :: post, x) == pre ++ post`, from
`apart_notin` (`:820`), `x` not in `pre`; `before_mid`, the twin for
`last(pre, s)`; and for the join, that `has(pa ++ pb, y)` with `y /= x`
follows from `has(pa ++ x :: pb, y)`. Sixty to a hundred lines. The
mutants stay as they are: each witness is a concrete ring, and
`join_unlinks_x_twice` (`glam/MUTANTS.txt`) is refuted by the same
statement, `y` left in `without(without(t, x), y)`. Verdict: replace,
after (A) and before the model's touch, so that the model's conjuncts
are proved once over the `without` statement.

## Q4. The refactored laws, their cost, and the order

### F8. The shape: a ring that knows its nodes

The model's `ring` grows from two conjuncts to five, every one of them a
fact of the rings the materializer builds:

    ring(v, d, s, t) :=
      chain(v, d, t, s, s)                 -- walk order, the last's s
      && disjoint.all(Con{s, t}, d)        -- no member's four words in another's word 3 (F4; apart.all is its word 3 case)
      && bases(Con{s, t})                  -- every member its own P.base (F2)
      && faces(v, d, Con{s, t})            -- every faced link word off the members' word 3 (F3)
      && off.links(Con{s, t}, d, P.at_fh())  -- the head's word no member's word 3 (F4)

`join_exact` then reads:

    for hf, hd32              -- the heap's shape
    for hr: ring(view(w), d, s, t)
    for hx: has(t, x)
    for hy: has(t, y)
    for hne: U32.is_eq(x, y) == False
    for hn: length(t) < R.fuel()          -- gone under F6 (B)
    |- ring(view(words(join(h, x, y))), d, s, without(without(t, x), y))

Seven premises, six without the fuel; two of them the heap's standing
ones. `hu`, `hw` come from `faces` at `x` and `y`; `hx0`..`hy1` from
`disjoint` at `x` and `y` against the ring after, a sublist; `hh` from
the last conjunct; `hbx`, `hby` from `bases`. `unlink_exact` keeps `hr`,
`hx`, `hn`; `insert_exact` takes `hr` and, for the new cursor, one
premise `fresh(v, d, Con{s, t}, x)` bundling what F2 to F4 ask of it:
its node disjoint from the members' word 3 and theirs from its, a base,
its faced link word off the links, no member facing its port 2, its word
3 not word 0. That bundle is the serve's obligation at `mz.cursor`
(`glam/materialize.bend:53-54`), discharged from the splice (a fresh
node, `node_index`; what it faces, `freeze.bend:284`) and the free
list's exactness, the one piece still over a model (`spike/LAWS.bend`,
`free_list_alloc`), as the earlier reviews found (F8 there).

Each conjunct must be kept by each operation, the join with cursors
facing each other included. The table says by what:

| conjunct | unlink | insert (given `fresh`) | join, incl. facing cursors |
| --- | --- | --- | --- |
| `chain` | `ul_chain` | `ins_chain` | the two unlinks |
| `disjoint.all` | sublist (`ap_remove`'s twin) | `fresh` | sublist |
| `bases` | sublist | `fresh` | sublist |
| `faces` | no word 1 written | `fresh`, both halves | F3: the link rewrites a member's word 1 only at `u`'s or `w`'s node, to a port whose `+ 1` the other instance covers; then sublist |
| head off | sublist | `fresh` | sublist |

Nothing here is false of the code as it runs: the only candidate that
was, `faces_out`, is replaced (F3). A join of a cursor with itself is
outside the law by `hne`, as the maintainer wants it, proved at the
serve (`.host.join.self`), not guarded.

What the refactored law still catches: the three exact mutants and
`join_unlinks_x_twice` (`glam/MUTANTS.txt`), as F7 says; `join_keeps`'s
six, untouched. What it still does not claim: where the wire went, the
freed nodes on the free list, the second ring's `faces` where `w` is
another ring's cursor (F3's cross-ring note belongs to a law over every
ring of a heap, `.host.path`'s territory). Verdict: replace the
two-conjunct `ring` by this one, and the four laws' premises by its
instances.

### F9. The siblings the serve will ask for

`glam/materialize.bend:60` calls `R.join1` for every crossing found:
`join1_exact` is the law the serve uses most, with `has(t, y)`, `x` given
`fresh`-like facts (its words off the links, a base), concluding
`without(t, y)`; it is `join_exact`'s proof with one unlink, as
`join1_keeps` is of `join_keeps`. And two paths unlink and free with no
law: `mz.root.w` (`:83-85`, the copy's root joined to the served cursor)
and `sv.static.w` (`:196-198`, `sv1.static.w` `:331-333`, a static put at
the faced port). Both are a link or a `put_st`, an unlink and a free:
one function in `glam/ring.bend`, `leave(h, x)` say, with `leave_exact`
(`without(t, x)`) and the materializer calling it, as
`JoinLawsFable_2026-11-14.md` F2 asked. Verdict: adjust; before
`.host.serve` is stated.

### F10. Cost and order

In order, each a commit with its laws named:

1. `R.fuel()` (F6 A) and `P.err_if` at fuel 0 in the three walks (F5):
   the literal out of the laws the same day; two mutants' witnesses
   unaffected. Hours.
2. `without`/`before` statements (F7), the split forms kept as `.go`
   lemmas: `split_of_has`, `without_mid`, `before_mid`. Half a day.
3. The model's conjuncts (F8), one at a time, each with its kept-by
   lemmas and the premise it retires: `disjoint` first (retires `hx0`..
   `hy1`, no arithmetic, re-proves `apart_*`), then `faces` (retires
   `hu`, `hw`; the plan's `faces_out` struck), then the head conjunct
   (`hh`), then `bases` (retires `hbx`, `hby`; needs the mask lemma,
   F2, else the `P.base` restatement meanwhile). One to two days; the
   mask lemma apart, no U32 bits.
4. `join1_exact`, `leave_exact` (F9). Half a day.
5. Fuel from the heap (F6 B): the pigeonhole, `hn` retired, the walks
   given `4 * wcap`. A day; a hub candidate.

Four laws change on `main`, so a side branch and one holistic approval
at the merge, the `Law:` trailers naming `pred_exact`, `unlink_exact`,
`insert_exact`, `join_exact` and the new siblings. Verdict: adjust, in
this order.

## Verdicts

- F1 the fourteen premises: adjust, by the model, not one by one.
- F2 `hbx`, `hby`: adjust (`bases`; the `P.base` restatement meanwhile).
- F3 `hu`, `hw`: keep now; `faces` replaces the plan's `faces_out`,
  which is false when cursors face each other.
- F4 `hx0`..`hy1`, `hh`: adjust (`disjoint` and a head conjunct in the
  model).
- F5 a walk out of fuel writes silently: adjust the code.
- F6 the literal million: replace by `R.fuel()` now, by the heap's size
  with a pigeonhole later.
- F7 the two splits: replace by `has` and `without`, with `x /= y`
  explicit.
- F8 the refactored shape: seven premises, every conjunct kept by every
  operation.
- F9 `join1_exact`, `leave_exact`: adjust, before `.host.serve`.
- F10 order: fuel constant, statement, model, siblings, heap fuel.
