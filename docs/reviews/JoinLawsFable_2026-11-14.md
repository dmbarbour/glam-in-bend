# Review: the join laws `join_keeps` and `join1_keeps`

Written by a Fable sub-agent as the second reviewer, at the maintainer's
request relayed by the agent (2026-11-14), independently of the agent's
own review, which it did not read. Commit reviewed: `b613c1f` on the
branch `host-join-keeps` (`66daf35` and `b613c1f` on main's `cc060dd`).
Files read: `glam/LAWS.bend`, `glam/ring_model.bend`, `glam/ring.bend`,
`glam/materialize.bend`, `glam/core.bend` (the ring's making and the
serve's reads), `spike/kprim.bend`, `spike/LAWS.bend`, `glam/MUTANTS.txt`,
the statements and headers of `glam/PROOF.bend`, the Cells plan's
`cells-freeze.nested.host` steps, `docs/Proving.md`. The proofs were not
rerun.

In one line: the two laws are true, non-vacuous and refuted by their
mutants, and they are the right shape for a step; but their write set is
coarser than the next step of a serve can bear, so as stated they do not
compose with themselves, with `insert_closed`, or into `.host.serve`.
Findings F1 to F3 say where; F4 to F8 answer the maintainer's questions
on form, model and premises; F9 and F10 list what the laws let through.

## The worked ring

The layout of `glam/test_materialize.bend:66-68` and `glam/core.bend:775-781`,
one cursor more. Nodes start at word 28 (seven header nodes); a node's
reference is its base, port p's reference is base + p and its link word
base + p + 1 (`spike/kprim.bend:382-386`), so a cursor, of one port, has
its one link word at word 1 and its ring link at word 3.

    s  = 36  w[36] = hd2(18, 2, k)  w[37] = era (static)  w[38] = handle  w[39] = 40
    c1 = 40  w[40] = hd2(18, 0, 0)  w[41] = 61            w[42] = pos1    w[43] = 44
    c2 = 44  w[44] = hd2(18, 1, 0)  w[45] = 73            w[46] = pos2    w[47] = 48
    c3 = 48  w[48] = hd2(18, 0, 0)  w[49] = 85            w[50] = pos3    w[51] = 36
    w[0] = 20  the free list's head: a node's index plus one, so node 19, base 76

The ring is s, c1, c2, c3, s. c1 faces port 61 (node 60's port 1, link
word 62), c2 faces 73 (node 72's port 1, link word 74), c3 faces 85. The
model's `xs` is `[36, 40, 44, 48]`; `closed` holds (`glam/ring_model.bend:41`);
`outside(xs, d, j)` holds for every j off words 36 to 51.

`R.join(h, 40, 44)` (`glam/ring.bend:156-167`), step by step:

1. `jn.u` reads `u = w[41] = 61`; `jn.w` reads `w = w[45] = 73`. No write.
2. `P.link_xx(h, 61, 73)` (`spike/kprim.bend:441-442`): neither static, so
   `w[62] := 73` and `w[74] := 61`.
3. `rg.unlink(h, 40)`: `rg.pred` walks from 40: next 44, 48, 36, then 40
   found with p = 36. `rg.unlink.set` writes `w[39] := w[43] = 44`. The
   ring is now s, c2, c3, s; c1's own word 3 still holds 44.
4. `rg.unlink(h, 44)`: the walk from 44 meets 48, 36 (whose word 3 is
   now 44), finds 44 with p = 36. Writes `w[39] := w[47] = 48`. The ring
   is s, c3, s.
5. `P.free(h, 40)` (`spike/kprim.bend:579-587`): `w[40] := 0`,
   `w[41] := 20` (the old head), `w[0] := 11`.
6. `P.free(h, 44)`: `w[44] := 0`, `w[45] := 11`, `w[0] := 12`.

Written: words 62, 74, 39, 40, 41, 44, 45 and 0. Allowed by
`join_keeps` (`glam/LAWS.bend:102-123`) but not written: 36, 37, 38 (the
situating node's header with the level offset, its static, the source's
handle), 42 and 43 (c1's position and next), 46 and 47 (c2's), and all
of 48 to 51 (c3's header, faced port, position and next). The law is
exact about the faced ports' link words and the head, and silent about
which of the sixteen ring words move: that silence is what the rest of
this review is about.

For `R.join1(h, pl, 44)` with a placeholder pl = 76 facing a copied
node's port, the writes are the two link words, `w[43]` once (the ring
intact, the walk from 44 finds c1 before it), pl's and c2's headers and
words 1, and the head twice; the law
allows pl's four words too (`hjx`, `glam/LAWS.bend:148`) and otherwise the
same.

## Q1: is this the claim to compose into `.host.serve` and `.host.path`?

### F1. The write set admits every member's words 0 to 2, which the next step of a serve reads

`glam/LAWS.bend:91-93`: "writes no word outside the ring's members' four
words, the free list's head and the link words of the two ports x and y
faced"; `glam/LAWS.bend:98-99`: "Not claimed: which members' words are
written". In the example the law permits the first join to write words
42, 46, 49, 50, 36 and 38. A serve then reads exactly those:

- `mz.curs` (`glam/materialize.bend:74-79`) handles the crossings in
  turn: each `mz.pl` (`glam/materialize.bend:64-66`) calls `R.rg.find`,
  whose walk reads each member's word 2 against `far`
  (`glam/ring.bend:44`) and its word 3 (`glam/ring.bend:14-15`). After the
  first `join1`, `join1_keeps` leaves c3's word 2 unconstrained: the
  second `rg.find` may, for all the law says, find nothing or the wrong
  cursor.
- The second `join1` reads `w[y2 + 1]` (`glam/ring.bend:175,179`), the
  port its cursor faces: a member's word 1, which the first law allows
  written. So the second law's own premises `hu`, `hw`, `hju`, `hjw`
  (`glam/LAWS.bend:145-151`), stated on the heap it starts from, cannot
  be carried back to the serve's initial heap through the first law's
  conclusion. The law does not compose with itself over one ring.
- `mz.root.w` (`glam/materialize.bend:83-85`) reads `w[nc + 1]` after
  every crossing join, and `sv.front.m` joins nc after the find
  (`glam/materialize.bend:190-192`): nc's word 1 is a member's word 1.
- `rg.situ` (`glam/ring.bend:127-129`) reads every member's header for
  form 2 at the start of each serve, `sv.k` (`glam/materialize.bend:219-221`)
  reads situ's header for the level offset `P.fld(hd)`, and the core
  reads situ's word 2 for the source (`glam/core.bend:812,1007`). A join
  of the previous serve is allowed to have written any of them.

So the concrete later step: the second crossing's `rg.find` and `join1`
in one `mz.curs`, and the root's join after them. The proof already has
the finer fact in hand: `unlink_keeps` (`glam/LAWS.bend:23-32`) names the
one word an unlink writes, `R.rg.pred(...) + 3`, and `free_keeps` names
the freed node. The law should say what it knows: the write set of a join
is x's and y's four words, the two words `rg.pred(h1, x) + 3` and
`rg.pred(h2, y) + 3` (members, by `pred_in_ring`), the head, and `u + 1`
and `w + 1`. A cheaper first step that already unblocks the serve: a
companion law `join_members`, for a member m other than x and y, words
m, m + 1 and m + 2 read as before. Verdict: adjust.

### F2. Two join-shaped compositions live outside `glam/ring.bend` and no law names them

`glam/materialize.bend:85`: `P.free(R.rg.unlink(P.link_xx(h, x, w), nc), nc)`,
the copy's root joined to the served cursor, where x is a copied node's
port, not a cursor; and `glam/materialize.bend:198`:
`P.free(R.rg.unlink(P.put_st(h, w, P.era()), nc), nc)`, the served cursor
given a static; their twins `sv1` at `glam/materialize.bend:333`. Each is
a link, an unlink and a free, like `join1` without the placeholder, but
written out in the materializer. `.host.serve` must cover them;
`docs/Proving.md` ("name the construction by the function the program
itself calls") rules out proving a copy of their bodies. Move them into
`glam/ring.bend` as, say, `join0(h, x, nc)` (a port and a member) and
`join_st(h, nc, s)` and give each its keeps law, parts of
`join1_keeps`'s proof reused (a link with one static test, one unlink,
one free). Verdict: adjust.

### F3. Two conclusions the plan's next steps need and no law gives

`.host.path` (the plan, "the port the served cursor faced, where it
stopped, now facing the copy") is a positive claim about a written word:
after `join(h, nc, c)`, `rd(u + 1) == w` and `rd(w + 1) == u` unless
static, where `u = w[nc + 1]` is top's principal port. `join_keeps` is
a keeps law and says nothing of the words it allows; `link_keeps`
(`spike/LAWS.bend:452`) likewise. A `join_links` law is small (two
`rd_wr_same` steps carried through the unlinks and frees by the keeps
laws) and is also the law that catches the mutants F9 lists.

`.host.serve` interleaves joins and inserts: `mz.found`
(`glam/materialize.bend:56-62`) either joins the placeholder or inserts it
as a cursor. `insert_closed` (`glam/LAWS.bend:76-88`) needs `hc`, the ring
closed, on the heap a `join1` left; `join1_keeps` does not conclude it.
The proof keeps the ring closed through the link and the first unlink
"for the walks after" (`glam/PROOF.bend:18-20`), then stops. A
`join1_closed` (and `join_closed`) stating `closed(words(join1(...)), d, xs)`
costs what `unlink_closed` cost plus the frees, which leave word 3
(`spike/kprim.bend:582`, the node's two writes, neither word 3), though `free_keeps`
does not promise that and the proof would state it on the parts, as
`fr_parts` already does. Verdict: adjust, both laws added before
`.host.serve` is attempted.

## Q2: separate premises on j, or one write set?

### F4. Name the write set once; the separate premises multiply and hide the composition's one real obligation

`join_keeps` puts four premises on j (`glam/LAWS.bend:119-122`):
`outside(xs, d, j)`, j off the head, off `u + 1`, off `w + 1`;
`join1_keeps` five, `off.node(d, x, j)` added (`glam/LAWS.bend:147-151`).
`node_keeps` has five (`spike/LAWS.bend:394`), `free_keeps` five, each
spelled as `Nat.is_eq(AD.slot(i, d), AD.slot(j, d)) == False{}`. A serve of
k crossings and n copied nodes then carries about 5(k + n) premises on j,
each stated against the heap its step starts from, and `.host.path` must
restate every one against the heap the serve started from.

A list composes where the premises do not. Define the write set as data:
`W.join(w, xs, x, y) : List<U32>` of word indices (x's and y's four, the
head, `u + 1`, `w + 1`, the two predecessors' word 3 once F1 is taken),
`W.node(fh)`, `W.insert(situ, x)`, and one predicate `off(ws, d, j)`, j's
slot in none, with one lemma `off(ws1 ++ ws2, d, j) == off(ws1, d, j) &&
off(ws2, d, j)`. The ring model is already half there: `outside`
(`glam/ring_model.bend:67-72`) is `off` over a list of node bases, and
`off.links` (`glam/ring_model.bend:75-80`) over their word 3s; unifying
them costs little. A serve's write set is then the append of its steps',
a function the prover sees, which is what the plan's own statement of
`.host.serve` asks for ("the write set must be stated as a function the
prover sees"), and `.host.path`'s premise is `off(W.serve(...), d, j)`
for each path word.

The honest caveat, which the list form does not remove but states once:
the write set is heap dependent. `u` is `w[x + 1]`, read at the step; the
second join's set is computed on the heap the first left. To evaluate
`W.serve` on the initial heap one needs that each step keeps the words
that define the later steps' sets, which is F1 again: with the present
law, a member's word 1 may change, so `W.join2` on the initial heap and
on the real heap may differ. In the list form that obligation is one
lemma per step kind ("the reads defining `W.join` are off `W.join`");
in the premise form it is smeared over four premises per step with no
place to state it. Verdict: adjust, in favour of one predicate and a
list, built on `outside` and `off.links`.

One detail worth keeping either way: the premises on `u + 1` and `w + 1`
are demanded even when the port is static and nothing is written there
(`spike/kprim.bend:428-432`). Harmless: the eraser is `nil`, all ones
(`spike/kprim.bend:31-32`), so `u + 1` wraps to 0, the head, and `hju`
coincides with `hjh`. The list form would put the two words in
conditionally (`link_keeps` already splits the static tests), which is
tidier and no stronger.

## Q3: closed, not a cycle; the cursor stays listed

### F5. The stale listing meets the free list at the next serve

`closed` (`glam/ring_model.bend:39-42`) asks that every member's word 3
hold a member; nothing says each member is some member's next, so a
member unlinked stays listed and the model cannot shed it: with two
members pointing at x (a shape `closed` admits), unlinking x leaves one
of them pointing out of `xs` minus x. Within one serve this costs
nothing, because `mz.fz` (`glam/materialize.bend:115-121`) runs the
splice's `S.sp.nodes` before `mz.sp`'s joins: every fresh node is taken
before any cursor is freed. The cost comes at the second serve.

Continue the example after `join(40, 44)`: the head is 12, the free list
is 44, 40, 76, ...; `xs` still lists 44 and 40. The next serve's splice
pops 44 (`spike/kprim.bend:513-518`, node 11): `P.node` writes `w[44]`
and, for any kind but data, `w[47]` (`spike/kprim.bend:547-555`, the
payload word 3, 0 for most kinds; a node of three ports later gets its
port 2's link there, `S.sp.links`). Then:

- `closed(view(w), d, xs)` is false: 44's word 3 is 0, no member. Every
  later `join_keeps`, `join1_keeps`, `unlink_closed` and `insert_closed`
  on this ring has an unsatisfiable premise, though the real ring, s and
  c3, is as closed as ever.
- If the node popped into 44 is a placeholder that `mz.cursor`
  (`glam/materialize.bend:53-54`) inserts, `insert_closed`'s `apart(xs, d, 44)`
  (`glam/ring_model.bend:54-59`) is false, 44 + 3 being the stale member's
  own word 3: the law that should admit the common case, a fresh cursor
  in a slot an old one left, refuses it.
- `outside(xs, d, j)` is false for words 44 to 47 and 40 to 43 for ever
  after, so the serve's kept claim is silent about live copied nodes
  standing in old cursors' slots, which the resumed walk visits;
  `xs` grows by two with every join and never shrinks.

The way out is the plan's own idea (`docs/plans/Cells_2026-11-09.md`,
the `.host.ring` step): a ring stated as the walk's members from situ,
so that a cycle holds by computation, an unlink takes a member off by
`pred`'s one write, an insert puts one on, and `apart` and `outside` are
over live members alone. With that, a freed slot reused is simply not a
member, and the free list's exactness is needed only to show the fresh
node is not a live member, a premise the serve law can carry until FL's
laws reach `P.alloc`. Short of the cycle, a cheaper patch would state
every law over `xs` with the two joined members removed, which needs
exactly the one-predecessor fact the cycle gives, so it is not cheaper.
Verdict: adjust, before `.host.serve`; the join laws themselves are
right to leave it to the model.

## Q4: the premises taken without derivation

### F6. `off.links` for the faced ports' link words: true as the code runs, dischargeable from a local invariant rather than the kernel's

`glam/LAWS.bend:117-118`. `u + 1` is a member's word 3 only if `base(u)`
is a member and `port(u)` is 2 (the commit `b613c1f`'s note in the plan
is right). What the materializer links: a crossing's placeholder faces a
copied node's port, `T.TL{T.TE{i, p}, T.TE{ne, 0}}` at
`glam/freeze.bend:284`, i a node of the frozen tree, never a hole; the
first cursor faces the host application's port, where the demand stopped
(`glam/core.bend:775-781`, nc the leaf's slot); and the situating node's
word 1 holds a static eraser (`P.put_st(h, situ, P.era())`,
`glam/core.bend:780`), for which `u + 1` wraps to word 0 and
`off.links(xs, d, 0)` holds while every member lies below 2^d minus 3.
So as the code runs no member faces a member, and the premise holds with
room to spare: the faced port's link word is no member's word at all.

Two ways to discharge it. The kernel's: every link word holds a static or
a port below its node's arity, and cursors have arity 1; a net
well-formedness invariant no law states yet, over every rewrite, far too
costly for this. The ring's: a model predicate `faces_out(v, d, xs)`,
every member's word 1 a static or a port of a node outside `xs`, kept by
`insert` (the placeholder's link is the splice's, to a copied node) and
by a join (the other members' word 1 unchanged, which is F1's refined
claim). It discharges `off.links` and also what F1 needs. Verdict: keep
the premise for now; record `faces_out` as the piece to prove, in the
plan beside the law.

### F7. `P.base(x) == x`: true, and cheap to derive

`glam/LAWS.bend:115-116,143-144`. Every reference the ring holds is a
base: `insert` is given the placeholder's reference from the splice's
map, `P.node`'s result `(fh - 1) << 2` (`node_index`, `spike/LAWS.bend`),
a multiple of 4; the first cursor is the leaf's slot; `rg.find` and
`rg.pred` return what word 3s hold. The proof uses the premise to turn
`free_keeps`'s premises on `P.base(r)` into `outside`'s on the member. A
model predicate `bases(xs)`, every member its own base, kept by
`insert_closed` given `P.base(x) == x` for the inserted node, discharges
`hbx` and `hby` for both laws; the one arithmetic fact,
`(n << 2) .&. 4294967292 == n << 2`, is lawful-words' territory
(ArrayLaws F5). For `join1`'s placeholder, `node_index` gives it directly.
Verdict: adjust, when the model is next touched.

### F8. `insert_closed`'s `apart`: true within a serve, false across serves until F5

`glam/LAWS.bend:87`. Within one serve the fresh node's slot is no live
member's, because every live member is in use and the free list holds no
node in use: that is the free list's exactness, which the plan says FL's
laws prove over a model and not over `P.alloc`, plus the fact that no
member is on the free list, which no law states. Across serves the
premise is false against the model's stale listing (F5's second item)
even though the code is right. So `apart` cannot be discharged before the
model sheds freed members; after that it reduces to "the fresh node is
not a live member", a premise the serve law can carry with FL's
exactness listed as its missing piece. Verdict: open question, F5 first.

## Q5: what the laws let through

### F9. Mutations of `glam/ring.bend:156-158` that survive both laws

Each of these writes only inside the allowed set, so the laws hold of it:

- `P.free(P.free(..., x), x)`: x freed twice, y never. The free list holds
  x twice (a later `alloc` hands one slot out twice) and y, unlinked,
  keeps its stale words. Writes: x's words, the head.
- `P.link_xx(h, u, u)` or `P.link_xx(h, u, x)`: the faced port linked to
  itself or to the cursor about to be freed. Writes: `u + 1`, or `u + 1`
  and x's word 1.
- `rg.unlink(rg.unlink(h', x), x)`: x unlinked twice, y never. The second
  walk starts from x, which no member links any more, runs its million
  steps and writes the word 3 of whatever member it stopped before
  (`pred_in_ring` holds whatever the fuel, so the write is inside the
  set); y is then freed while still in the ring, a free node among the
  members.
- `rg.unlink.set` writing `p + 2` (the existing mutant `unlink_word2`):
  inside the set for `join_keeps`, which lets it through; `unlink_keeps`
  catches it only because the mutants file names that law.

None is a fault of the "keeps" kind, and the laws' comments say they do
not claim the join's effect. But they show the coarseness of F1 and the
gap of F3: `join_members` would catch the fourth and `join_links` (after
the join, `rd(u + 1) == w`, `rd(w + 1) == u`, and the walk from situ meets
neither x nor y) the first three. Verdict: keep the laws as they claim;
add F3's laws with these as their mutants.

### F10. The case `x == y`, and two wordings

`sv.front.m` (`glam/materialize.bend:190-192`) calls `R.join(h, nc, c)` with
c the cursor `rg.find` found at the frontier port q. If q could equal
nc's own position, c is nc: `link_xx(u, u)` links the port to itself,
the second `rg.pred` walk from nc never meets nc and exhausts its fuel
(a million reads), then writes a member's word 3, and nc is freed twice.
Both laws permit all of it. Whether `Q.positioned` from `pos` can report a
frontier at `pos` itself I could not settle from the code read; if it
can, a `P.err_if(U32.is_eq(x, y), ...)` in `join` is the shape, with a law
that the guard never fires where the serve calls it. Verdict: open
question.

Wordings: `glam/LAWS.bend:93-94`, "(each one's word 1 holds its port)",
reads as the cursor's own port; "the port it faces" is meant. And
`join1_keeps` does not ask that x be no member (its comment says "in no
ring"): the law is true either way, since x's words are allowed, so the
weaker premise is right; the comment could say so. Verdict: keep, with
the wording touched.

## Summary of verdicts

- F1 adjust: the write set should be x's and y's words, the two
  predecessors' word 3, the head, `u + 1`, `w + 1`; at least a
  `join_members` companion.
- F2 adjust: `mz.root.w` and `sv.static.w` into `glam/ring.bend`, each
  with a keeps law.
- F3 adjust: `join_links` and `join1_closed` before `.host.serve`.
- F4 adjust: one write-set list and `off`, built on `outside` and
  `off.links`; the heap dependence stated once.
- F5 adjust: the ring as the walk's members from situ, before the
  second serve is modelled.
- F6 keep the premise; record `faces_out` as the piece to prove.
- F7 adjust: a `bases(xs)` predicate, cheap.
- F8 open question, after F5.
- F9 keep; F3's laws take these mutants.
- F10 open question on `x == y`; wording kept, touched.

This file is not yet listed in `docs/reviews/README.md`; the agent adds
the entry, this review having changed no other file.
