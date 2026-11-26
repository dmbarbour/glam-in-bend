# Allocation and the heap's growth under the laws (second reviewer)

Written for `cursor-laws.alloc` (`docs/plans/CursorLaws_2026-11-23.md`),
beside the lead reviewer's review and independent of it.

## Scope

Read in full: `glam/loop_model.bend`, `glam/LOOP_LAWS.bend`,
`spike/kmodel.bend`, `spike/freelist.bend`, `spike/kmem_grow.bend`,
`spike/HEAP_LAWS.bend`, `docs/plans/KernelRefine_2026-11-24.md`, the
plan's entries `cursor-laws.loop.shape` and `cursor-laws.alloc`, and the
records `splice-frame-premises`, `net-obvious-errors`,
`serve-premises-over-index`, `copied-nodes-untouched`.

Read in part: `spike/kprim.bend` (lines 150-260 and 440-740: the header,
`thread`, `alloc`, `free`, `grow_more`, `frees`, `reserve`);
`glam/ring_model.bend` (`layout`, `bases`, `po.all`, `px.off`, `px.ok`);
`glam/index_model.bend` (`tr.real`, `ix.real`, `nd.ok`, `fl.ok`);
`spike/knet.bend` (the audit `free_ok`); `spike/wired_model.bend`
(`port.ok`); `spike/kplace.bend` (`in_step`, `grow`); the statements of
the laws in `spike/LAWS.bend`, `glam/SPLICE_LAWS.bend`,
`glam/SERVE_LAWS.bend`, `glam/INDEX_LAWS.bend`, `glam/LAWS.bend`;
`glam/proofgen/align/ALIGN.bend`'s signatures; `docs/Proving.md` (What to
claim); `docs/BendIssues.md` (Reasoning about U32 in proofs);
`glam/core.bend` by its comments and a few definitions around the
serve's end.

Sampled by pattern only: every `law` in the twelve `*LAWS.bend` files,
its premises and conclusion matched against the free list's names (a
script, kept out of the tree). No proof file was read beyond signatures.

Nothing was built, typechecked or run. Every implication claimed below
between predicates is from reading their definitions; none was checked
by Bend. Where I did not trace code to its end I say so.

## Inventory

### F1. Fifty-one laws take a premise on the free list, in seven groups

My count, by matching each law's premises against `KMd.chain`,
`P.at_fh()`, `IM.fl.ok`, `IM.ix.flsep`, `FL.ok`, `RG.px.ok`, `LM.lx.ok`
and `LM.ext.ok` (the plan's rough count was 49):

| Group | Laws | What the premise says of the free list |
|---|---|---|
| A. The model in `Nat` (`spike/LAWS.bend`) | 10: `free_list_alloc`, `free_list_free`, `free_list_takes_free`, `free_list_grow`, `kernel_slots_ok`, `kernel_free_ok`, `kernel_rewrite_wired`, `kernel_in_step`, `kernel_rules_in_step`, `kernel_events_in_step` | `FL.ok`: the links spell a list of every free slot, none twice |
| B. The primitives' frames (`spike/HEAP_LAWS.bend`) | 4: `node_keeps`, `node_next`, `node_index`, `free_keeps` | the head's word read, not 0; a word off the head's |
| C. The splice (`glam/SPLICE_LAWS.bend`) | 4: `nodes_keeps`, `nodes_maps`, `splice_keeps`, `splice_free` | `KMd.chain(ns, ...)`, `KMd.apart(ns)`, `KMd.past(ns)` |
| D. The index (`glam/INDEX_LAWS.bend`) | 9: `insert_free`, `remove_free`, `free_push`, `chain_kept` (the chain); `insert_keeps`, `remove_keeps`, `free_real` (a word off the head's); `put_flsep`, `del_flsep` (`flsep`) | `KMd.chain`, `IM.fl.ok`, `IM.ix.flsep` |
| E. The crossings and leaves (`glam/LAWS.bend`) | 12: `cursor_head`, `cursor_pend`, `join1_pend`, `cross_pend`, `crossings_look`, `crossings_pend`, `crossings_keeps`, `join_pend`, `join_keeps`, `leave_pend`, `leave_era_pend`, `leave_keeps` | `RG.px.ok`, which carries the chain; each takes `RG.layout(N, d)` and `RG.bases(N)` beside it |
| F. The serve (`glam/SERVE_LAWS.bend`) | 6: `copy_pend`, `copy_root_off`, `serve_pend`, `serve_keeps`, `serve_ring_exact`, `serve_root_keeps` | `RG.px.ok` over `ns ++ F`; `layout`, `bases`, `KMd.past`, `distinct` beside it |
| G. The loop (`glam/LOOP_LAWS.bend`) | 6: `situate_pend`, `px_sub`, `serve_loop`, `lx_split`, `lx_extend`, `serve_next` | the chain, `LM.lx.ok`, `LM.ext.ok` |

Two kinds of premise must be told apart. In groups E, F and G (but
`lx_extend` and `situate_pend`) the free list is *carried*: the law
takes the invariant and returns it, and the premise costs nothing more
once the invariant holds. In groups B, C, D and at `situate_pend` and
`LM.ext.ok` it is *owed*: nothing in the laws yet says a heap the
kernel builds satisfies it. The owed premises are few in kind: the
chain from the head, the nodes' layout, the head not 0. The count of 51
overstates the debt; the debt is at the two places where nodes enter
the tracked lists (`situate_pend`'s `hch`, `hdF`, `hlf`,
`glam/LOOP_LAWS.bend:40`; `LM.ext.ok`, `glam/loop_model.bend:37`), and
at the base of the splice's and index's chains, which the loop's
invariant already feeds.

### F2. There are six descriptions of the free list, none tied to another

Beyond the three the plan names:

1. `FL.ok` (`spike/freelist.bend:106`): slots in `Nat`, a ghost list
   `l`; `walks(l, s, fh) && (nodup(l) && listed(s, length, l))`.
   Exact: sound (listed slots are free) and complete (free slots are
   listed).
2. `KP.in_step` (`spike/kplace.bend:24`): a slot free exactly when its
   kind is `KFree`; kind code 0 (`spike/net.bend:16`).
3. `KMd.chain` (`spike/kmodel.bend:85`): a prefix of the list read from
   the words, with no end, no range, and no fact of the nodes' headers.
4. `IM.fl.ok` (`glam/index_model.bend:473`): each node its own base, its
   four words in four slots off the head's (`nd.ok`); with `ix.flsep`,
   apart from the index.
5. The audit `KN.free_ok` (`spike/knet.bend:1486`, "is the free list in
   step with the nodes' headers?"): the list and then the reserve's
   walked to their ends within the capacity, each node in
   `[P.first(), cap)`, their count equal to the count of zero headers.
   It is the only one that covers the reserve.
6. The wiring's reading of "live" at the words:
   `U32.is_ne(KMd.word(v, d, P.base(y)), 0)`
   (`spike/wired_model.bend:22`), which a law already uses
   (`wired_port`, `spike/WIRED_LAWS.bend`).

The code agrees with 5 and 6: `P.free` zeroes the header
(`spike/kprim.bend:581`, `KM.m_set(w, base(r), 0)`), a grown store is
zero-filled (`spike/kmem_grow.bend:61`), and every node made writes a
header (`node.fin`, `node.hd`). So "free" has a reading at the words
that costs the kernel nothing: header 0. No law states it of the free
list's nodes, and `node_keeps` and `free_keeps` disclaim the node's own
words on the maintainer's word of 2026-11-13 ("none for code to rely
on", `spike/HEAP_LAWS.bend:14-24`). That ruling is about code; whether
a law may rely on the zero header is a question for the maintainer
(Q2 below).

### F3. The target is already recorded; five laws wait on it by name

`splice-frame-premises` (`docs/decisions/splice-frame-premises.md:21-26`)
records "the allocator's target (the second reviewer's): one prefix
law, 'the free list's first k nodes are distinct, laid out apart, past
the header, below the capacity, and none live' ... `FL`, the free
list's model in Nat, is the model it refines." The laws name it as
their missing piece: `glam/SPLICE_LAWS.bend:24-26` ("that ns are free
and none live (the allocator's prefix law, to come)"), `:136-137`,
`glam/SERVE_LAWS.bend:39` ("Not claimed: growth; that ns are free"),
`spike/HEAP_LAWS.bend:21-24`, `glam/LOOP_LAWS.bend:35-36`.

`LM.ext.ok` is that prefix law's conclusion, restated: its conjuncts 1,
2, 5, 7 and 8 are "distinct, laid out apart, past the header"; 3 and 4
are "none live"; only 6 is new, and "below the capacity" is missing
(F6). So the maintainer's remark is the 2026-11-19 decision coming due,
not a new kind of debt.

### F4. What could go, and what cannot

- *Could go at once, by list lemmas*: three of `LM.ext.ok`'s conjuncts,
  implied by the others (F5).
- *Could go by arithmetic*: `RG.layout`, `RG.bases`, `KMd.past` and
  `IM.fl.ok` wherever they stand as separate premises (28 laws by my
  count, in groups C to G and `glam/JOIN_LAWS.bend`), given one per-node fact, a base in range (F6); and
  `hhd` (`KMd.off.words(KMd.hdr_words(), d, P.at_fh())`, twelve laws),
  which is `3 <= d` spelled as slots, a new heap being of depth 9
  (`spike/kprim.bend:258`, `KM.m_new(9n, ...)`).
- *Irreducible without a kernel invariant*: that the list from the head
  is a list (it ends, so repeats none), that its nodes are in range, and
  that none is in use. No arithmetic gives these; they are facts of
  every write the kernel has made. They need group A's model bridged to
  the words, in some form, and a law that each kernel step keeps it.
- *Irreducible in any model*: that the list holds as many nodes as a
  serve takes. It is a fact of a run, to be tested by code (`P.frees`,
  `spike/kprim.bend:653`) or supplied by growth.

## The eight premises

`LM.ext.ok` (`glam/loop_model.bend:37-38`), its conjuncts numbered as
the brief numbers them:

    KMd.chain(F ++ E, v, d, word(v, d, P.at_fh()))      1
    && RG.distinct(F ++ E)                              2
    && RG.none.in(E, L)                                 3
    && RG.none.in(E, Con{s, IM.ix.nodes(I)})            4
    && RG.layout(N ++ E, d)                             5
    && RG.px.off(L, v, d, L, E)                         6
    && RG.bases(E)                                      7
    && KMd.past(E, d)                                   8

### F5. Premises 2, 3 and 4 follow from 5 and the invariant already

`RG.layout` (`glam/ring_model.bend:169-174`) asks of each node `a`
before the rest `t` that `cross(t, d, a)`, and `cross` asks `disj4(d,
a, b)` of each `b` in `t`, whose first conjunct is `off(nw(b), d, a)`:
`a`'s slot is not `b`'s. Two equal nodes share a slot. So
`layout(N ++ E, d)` says no node of `N` is a node of `E`, and that `E`
repeats none.

`LM.lx.ok` holds `RG.px.ok`, which holds `sub(L, N)`, `sub(F, N)`,
`sub(IM.ix.nodes(I), N)`, `sub(Con{s, IM.ix.leaves(I)}, L)` and
`distinct(F)` (`glam/ring_model.bend:343-344`). Hence:

- 3, `none.in(E, L)`: `L` is within `N`, and no node of `N` is in `E`.
- 4, `none.in(E, Con{s, ix.nodes(I)})`: `s` is in `L`, the index's nodes
  within `N`.
- 2, `distinct(F ++ E)`: `F` distinct by the invariant, `E` by its own
  layout, `F` within `N` and so sharing none with `E`; the append by
  `dist_app`, which `glam/LOOP_PROOF.bend` has (the plan,
  `.loop.shape.distinct`).

The lemmas wanted are of the kind `.loop.shape.track` already used
(`GP.lay_sub`, `SP.apall_of`, `SP.none_flip`): `layout(N ++ E)` gives
`none.in(E, N)` and `distinct(E)`; `none.in(E, N)` and `sub(X, N)` give
`none.in(E, X)`. I expect a day or less, S; unchecked. `lx_extend` is
not yet merged (the plan: "`.loop.shape.next` waits on its verdict on
`LM.ext.ok` before merging"), so `ext.ok` can shrink to five conjuncts
on the side branch with no law on main changed.

So the six premises "related to free lists" are three: the chain, the
bases, past the header. The other three were premise 5 said again.

### F6. Premises 5, 7 and 8 are one fact a node, a base in range; and the range is missing

Where each comes from in the kernel: the free list's links name nodes by
index (`at_idx`, `spike/kmodel.bend:80`: `(h - 1) << 2`), so a node read
from a link is a multiple of 4, its own base (7), whatever the heap
holds. Past the header (8) and apart from other nodes (5) come from the
index lying in `[P.first(), wcap)`: the list is threaded from
`first()`, 7 (`spike/kprim.bend:252-255`), and from the old capacity at
a doubling (`:466-470`), `P.free` gives back only what was taken, and
`4 * wcap` words are `2^d`.

For a base `n` with `28 <= n` and `n + 3 < 2^d`, a slot is the word
itself (`AD.slot(i, d)` is `i mod 2^d`, the hub's `defs.bend:34`), so:

- the node's four words are four slots, off word 0 and off the header's
  words `KMd.hdr_all` names (all below 8): `layout`'s per-node part,
  `IM.nd.ok`, `KMd.past`;
- two such nodes that differ are apart (`disj4`, `nd.sep`,
  `KMd.apart`): the generalized `bases_apart`;
- the same holds at depth `d + 1`, and a word read at `d + 1` after the
  doubling's copy is the word read at `d`.

`LM.lx.ok` has no range. `RG.layout` says four slots and off the head's
word; `bases` says a multiple of 4; `past` says off five header words.
None bounds a node by the capacity. Yet `px_grow` (`.loop.shape.grow`)
needs it: `KM.grow` copies `cap` words (`spike/kmem_grow.bend:59-61`),
so `IM.ix.real` read at depth `d + 1` equals itself at `d` only for
nodes below `2^d`. Without range, the invariant is not kept across the
doubling. The prefix law's target had the clause ("below the
capacity"); the loop's invariant dropped it.

So: one predicate, say `KMd.nd.in(n, d)` (its own base, at or past
`P.iface()`, its last word below `2^d`), and three lemmas
(`in_own`, `in_apart`, `in_up`). With `nodes.in(N, d)` and
`distinct(N)` in the invariant, `layout(N, d)`, `bases(N)` and
`past(N, d)` are consequences, and premise 5 becomes `none.in(E, N)`
(membership, no slots), 7 and 8 become `nodes.in(E, d)`. The
arithmetic is `U32` against `Nat` without wrapping, which
`bend-mathlib` and `lawful-words` cover (`docs/BendIssues.md:133-160`);
`ALIGN.bend` already carries the harder half, residues mod 4 through a
slot (`slot_mod4`, `slot_base`). I rate it M. It discharges nothing by
itself: `nodes.in(E, d)` is still owed by the kernel. But it is a
per-node test with no pairs, which a kernel invariant can state and
which a grown range satisfies by computation.

### F7. Premise 1 is a definition, if `E` is read rather than given

`chain(F ++ E, ...)` says `E` is what the links spell after `F`. It is
a premise only because `E` is a free variable of the law. A reading
function, `KMd.walk(v, d, h, k)`, the first `k` nodes from link `h`,
stopping at 0, satisfies `chain(walk(v, d, h, k), v, d, h)` for every
heap, one induction. Then premise 1 is gone and what is owed is the
length: that the walk returned `k` nodes. That is the run's fact (F4),
the meaning of `P.frees(k, h)`.

### F8. Premise 6 needs the wiring and the free list together

`px.off(L, v, d, L, E)`: the port each live node faces has its link
word off every word of `E`'s nodes. The brief calls it the host's
wiring. The wiring alone does not give it: `WR.port.ok`
(`spike/wired_model.bend:22-34`) says a live node's port links a
static, or a port of a node in range whose header is not 0. To
conclude that port is in no node of `E`, `E`'s nodes must have header
0. So premise 6 is `KN.wired_ok` (through `wired_port`) *and* "a node
on the free list has a zero header", then F6's arithmetic to turn
"another node" into "another slot". The accepted premise depends on the
unaccepted ones' source. This is the strongest reason to bridge the
free list to the words at all: without the zero header, the kernel's
refinement of the wiring cannot discharge 6 either.

The live side needs its half too: `px.ok` does not say a live node's
header is not 0. `tr.real` says a leaf's header is "no branch's"
(`glam/index_model.bend:246`), which 0 satisfies. A conjunct, or a
fact of the kinds the cursors are made with (`P.hd2(18, ...)`,
`glam/ring.bend:54`), is owed there.

### F9. The tracked prefix `F` does not outlive a serve, so `E` is the whole prefix

`lx_extend` is framed as growth "past the free list's tracked prefix".
But after a serve the host goes on: `frame.ok.k` ends a clean serve
with `host.go(ho, h, ss, b, c)` (`glam/core.bend:1061-1068`, "the host
going on otherwise"), and the next serve comes when "a host's demand
stopped needing" a cursor (`:763-767`). Between the two the kernel's
rewrites pop the list's head and push what they free. `host.go` sets
the host's demand going again (`KD.d.go`, `:985-992`); I did not read
`spike/kdemand.bend` to see which steps follow, and a host may stop
again with no rewrite between; but in general the `F` one serve leaves is not a
prefix of the list the next serve finds, and some of its nodes are the
host's.

So `serve_next`, which reads `LM.ext.ok` on the very heap the serve
left, covers two serves with nothing between. The step the loop
really takes has the kernel in the middle, and after it the invariant
holds at best with `F` empty and the nodes of `F` out of `N`. Then
`LM.ext.ok` at `F = Nil` is the whole of what the next serve asks of
the free list: its first `k` nodes chained, in range, none tracked, no
live port facing them. That is the prefix law, exactly (F3). The
conjuncts need not be weighed as increments to a tracked prefix; they
are the kernel's contract with the materializer, asked afresh at each
serve, and `F` in the invariant between serves is dead weight (kept
within a serve, where the crossings take from it).

The rest of `lx.ok` crosses the kernel's steps only by the kernel's
refinement too: a rewrite relinks what a cursor faces (`faces`,
`px.off`, `px.tw`). So the loop's laws cannot close without
`kernel-refine` whatever is done about allocation; what can be settled
now is the shape of the contract.

### Summary

| # | Premise | Source in the kernel | Becomes |
|---|---|---|---|
| 1 | chain over `F ++ E` | the links, `alloc.k`'s pop | by computation, `E` read by a walk; the length owed by the run |
| 2 | `F ++ E` distinct | the list ends | implied by 5 now; later by a list that ends |
| 3, 4 | `E` none live, none of `s` or the index | a node free or in use | implied by 5 now; later by zero headers |
| 5 | `N ++ E` laid out | indices in range, distinct | `none.in(E, N)` and `nodes.in`, by arithmetic |
| 6 | no faced port into `E` | wiring, and zero headers | `wired_port` with the free list's zero headers |
| 7, 8 | bases, past the header | links are indices from `first()` | `nodes.in(E, d)` |

## Approaches

### A0. My proposal: a sound free list read from the words, nodes by arithmetic, growth between serves

Three parts, separable.

**A0.1 Nodes by arithmetic** (F6). Invariant: `nodes.in(N, d)` and
`distinct(N)` in place of `layout`, `bases`, `past`. Discharges 5, 7, 8
down to a per-node test, and the 28 separate layout premises once the
loop's laws feed them. By computation: `nodes.in` over an append,
`minus`, a sub-list are folds; `in_up` across the doubling is one lemma
with no list. Proof cost: M, three arithmetic lemmas and two bridges
(`lay_of`: distinct and in give `RG.layout`; the same for
`IM.fl.ok`). No law on main is restated: the step laws keep their
`layout` premises and the loop's laws discharge them through the
bridges. Runtime: none, no code changes.

**A0.2 A sound list, not an exact one.** The materializer needs less
than `FL.ok`. It needs: listed nodes are free. It never needs: free
nodes are listed. Completeness is what the reserve breaks
(`heap-laws-align.statics`, `docs/plans/HeapModel_2026-10-27.md:3958`:
"the reserve cut from the free list fails `FL.ok`'s one list"), and
what leaks would break; neither can hurt a serve. So state at the
words, with a ghost list `l` as `FL` has:

    fs.ok(v, d, l) =
      ends(l, v, d, word(v, d, P.at_fh()))   -- KMd.chain, and 0 after the last
      && nodes.in(l, d)                      -- in range (A0.1)
      && zero(l, v, d)                       -- each header 0

`ends` gives distinctness for nothing: a walk is a function of the
heap and the link, so a node met twice would start the same tail
twice, and a list equal to a proper suffix of itself has two lengths.
(By the same argument `FL.ok`'s `nodup` follows from its `walks`; I
have not seen that proved, and say so as an observation.) Then one
read-only law, the prefix law: under `fs.ok(v, d, l)`, any prefix `E`
of `l` satisfies premises 1, 2, 7, 8, and has zero headers; with "live
nodes have headers not 0" (F8) and `wired_port`, 3, 4, 5 and 6. Every
conjunct of `LM.ext.ok` is then discharged from two standing premises
of the heap, `fs.ok` and `KN.wired_ok`, plus the length.

By computation? Partly. `zero` and `nodes.in` are folds; a pop keeps
`fs.ok` of the tail by a case split (the tail's nodes are not the node
popped, by distinctness, so its words stand: `node_keeps`). A free
keeps it under a premise at the words, that the freed node's header was
not 0 (so it is not on `l`) and in range. That premise at each of the
kernel's free sites is where `kernel-refine.rewrite` pays: a rewrite
frees the pair it dispatched on, whose kinds it read. A write to a
free node's word 1 by a link would break `ends`; ruling it out is the
wiring again. So the *keeping* is the kernel refinement's work; the
*reading* (the prefix law) and the primitives' laws (`alloc` pop,
`free`, `grow.done`, `grow_more`) are M each and need no rewrite.

Runtime: none. The header is zeroed already; `l` is ghost. This
depends on a law relying on a free node's header (Q2).

**A0.3 Growth between serves, never within one.** As the code stands a
copy or a crossing's insert that finds the list empty doubles the
store in the middle of `S.sp.nodes` or `R.crossings`
(`alloc.k`, `spike/kprim.bend:513-518`), and the depth `d` every
predicate is stated at changes mid-serve. Each of the splice's, the
index's and the crossings' laws would need a growth case. Instead: the
materializer makes room before it serves, `P.frees(k, h)` for the
copy's nodes and the crossings' branches, and `P.grow_more`
(`spike/kprim.bend:630`) while it fails, as `rs.got.go`
(`spike/kstrat.bend:1253-1258`) does for the reserve. Then a serve's
depth is fixed, by a guard at one site, and `px_grow` is one law about
`grow_more` between serves. After `grow_more` the new nodes head the
list ("its new nodes all on the free list, the nodes free before after
them", `spike/kprim.bend:626-628`): `E` is the range from the old
capacity, and every conjunct of `LM.ext.ok` but 6 holds of it by
arithmetic with no kernel invariant (in range at `d + 1`, at or past
`2^d` and so none of `N`, which is below it).

Runtime: on the materializer's path, not the kernel's rewrite. A walk
of `k` links before a copy that then writes `k` nodes, and a doubling
up to `k` allocations sooner than otherwise. Not free: it must be
measured on the sharing families at n, 2n, 4n, and its guard is a
check whose law (that room suffices for the serve) must be stated, or
the alternative kept, growth inside the steps. It also needs
`KM.depth` reshaped as `alloc.k` was, a test in place of the literal
match (`spike/kmem_grow.bend:48-56`; the Cells plan, `.host.alloc`:
"growth ... waits on `depth`, which matches the literal 1 and so wants
the same reshape"), on the cold path, to be confirmed by instruction
counts.

### A1. Premises, as now

Invariant: none new. Discharges nothing. Cost now: nothing. Its risk is
shape drift: `.root` takes `LM.ext.ok` again, `.grow` meets the missing
range (F6), and the contract the kernel is later asked to meet has
eight conjuncts of which three are redundant (F5) and one is under-
stated (F8). Acceptable only with F5 applied; premises are fine, these
premises are not yet the right ones.

### A2. `FL.ok`'s partition bridged to the words

Invariant: an abstraction from the words to `FL.FL` (slots from
headers and word 1, the ghost list) with `FL.ok`. Discharges 1 to 4, 7,
8, and 6 with the wiring. By computation: no more than A0.2, and less,
since `listed` quantifies over every slot of the heap and an allocation
must re-establish it over the whole store. Proof cost: A0.2's, plus
`listed`, plus the reserve (two lists, or one read back as list then
reserve, `kernel-refine.align`), plus the `Nat`-to-`U32` abstraction,
for which group A's ten laws are restated or wrapped. What it buys over
A0.2: no leaks, and the kernel's placement laws
(`kernel_slots_ok` and its kin) tied to the heap. Those belong to
`kernel-refine`, whose Open section asks whether the free list is
refined at all or "left to [its] audits"
(`docs/plans/KernelRefine_2026-11-24.md:60-63`). Runtime: none. I
would not build it for the materializer; A0.2 is its sound half, and
can be widened to it if the refinement wants exactness.

### A3. The layout by arithmetic over any two distinct bases

A0.1 is this, with range. As the plan words it ("so that the tracked
list needs no growth") it claims too much: with pairs apart by
arithmetic the tracked list is not needed for *layout*, but `px.off`
still reads `N` (`po.all` over every tracked node,
`glam/ring_model.bend:304-309`), so nodes entering still need premise
6 over them. The tracked list could be computed from the roles (`L`,
`F`, the index's branches), which IndexPremises P10 floated; that
restates `px.ok` and with it groups E and F, L. I would keep `N` and
change only what is said of it.

### A4. A mark past which every node is free and untouched

Invariant: nodes at or past a mark `m` have never been taken; they are
the list's tail, ascending. `thread` builds exactly that
(`spike/kprim.bend:240-246`), and `S.Meta`'s `fresh` count is the same
idea in the page store (`spike/store.bend:18-21`). By computation: yes,
for nodes past the mark, everything but 6 is arithmetic. But the head
of the list is where recycled nodes are, and a copy takes from the
head; the mark describes the nodes a serve takes only when nothing has
been freed since the last doubling, or just after `grow_more`, which is
A0.3. To make every copy take from past the mark would be a second,
bump allocator for copies: recycled nodes unused by the materializer,
more memory, and a mark word written on the kernel's allocation path or
a second path beside it. That is a change to the hot path's shape and
to `net-nodes-double`'s measured trade; I would not propose it without
a measured need. As a ghost, the mark adds nothing A0.2's list does not
say. Its sound use is A0.3's: the grown range.

### A5. The kernel's reserve

Two readings. As a model question (`kernel-refine.align`: "the reserve
in the free list's model, or read back as free list then reserve"), it
is only A2's problem: a sound list (A0.2) holds of the free list and of
the reserve separately, and the tap (`alloc.tap`,
`spike/kprim.bend:494-500`) swaps one for the other; one more
primitive's law, with a premise that the two share no node. As a
mechanism, a reserve kept *for the materializer* (set aside before a
serve, taken by it) would make "room for the serve" a state rather
than a walk, but `P.reserve` walks `k` links as `frees` does, and a
second reserve beside the collector's is new kernel state. No gain
over A0.3. Whether a host the materializer serves ever keeps the
collector's reserve I did not establish: `glam/core.bend` imports
`spike/kstrat.bend`, where `P.reserve` is called (`:1240`), and I did
not trace which demand a host runs. If none does, `word(at_rsv) == 0`
is a standing fact and the tap is dead for these laws; worth checking
before any reserve law is written.

### A6. A check at the pop (named for completeness)

The copy could test each node it takes: header 0, in range, counting an
error otherwise, the law then holding where no error is counted.
`docs/Proving.md` allows a run-time check that "names the law meant to
replace it", and warns that a guard "must not stand in for a premise
the law leaves out". It costs a read a copied node, to be measured,
and proves nothing of the kernel. I would use it only as a test's
audit, which `KN.free_ok` already is.

### Comparison

| | Discharges | By computation | Laws restated | Runtime |
|---|---|---|---|---|
| A0.1 nodes by arithmetic | 5, 7, 8 to a per-node test; range for `px_grow` | yes | none on main; `lx.ok`, `ext.ok` on the side branch | none |
| A0.2 sound list | 1 to 4, 7, 8; 6 with wiring | reading yes; keeping needs the kernel's steps | none; new laws | none |
| A0.3 room before a serve | growth inside steps; grown `E` wholly | yes, a guard | none; `px_grow` simpler | materializer path, to measure |
| A1 as now | nothing | n/a | none | none |
| A2 `FL.ok` bridged | as A0.2, and leaks | less (`listed`) | group A wrapped | none |
| A4 mark as allocator | all but 6 | yes | splice, serve | hot path, to measure |
| A5 reserve for serves | room | yes | new | new state, to measure |

## When

The question as put offers three times. I think the work divides, and
each part has its own time.

**Now, before `.root` and `.grow`** (days, no kernel code):

- F5: `LM.ext.ok` cut to five conjuncts before `.loop.shape.next`
  merges. Cost S. Risk: none I can see; if a lemma resists, the
  conjuncts stay.
- A0.1 with the range, as the first slice of `.loop.shape.grow`, since
  `px_grow` cannot be stated without range (F6). Cost M. Risk: `U32`
  arithmetic in Bend runs over estimate (`docs/BendIssues.md`); bounded
  by doing `in_up` first, which `.grow` needs whatever else is decided.
- `LM.ext.ok` restated as the contract (F9): what the next serve asks
  of a heap, at `F = Nil`, each conjunct with its owner named in the
  comment (the sound list, the wiring, the run). `.root` then takes the
  same predicate, once.

Doing these now costs `.root` a short wait and saves it taking a
predicate that would change under it. Not doing them means `.root` and
`.grow` are written over `layout`, `bases` and `past` as lists, and
restated when range arrives.

**After the loop's laws close, before or as `kernel-refine.align`**:

- A0.2's predicate `fs.ok`, the prefix law, and the primitives' laws
  (pop, free under its premise, `grow.done`, `grow_more`). They are
  about `spike/kprim.bend` alone, read-only or one primitive each, in
  the style of `spike/HEAP_LAWS.bend`. They discharge `HEAP_LAWS`' own
  "not claimed" (that the node taken was free) and give
  `kernel-refine.audit` a second read-only bridge beside the wiring's.
- A0.3, if the maintainer wants growth out of the steps (Q3): a code
  change with its measurement, its own step.

Why not now: until a kernel step is shown to keep `fs.ok`, it is one
premise in place of several, a renaming of the debt. Its worth before
then is the contract's shape and premise 6's dependence (F8), which the
comment on `ext.ok` can carry. Why not later than `kernel-refine.align`:
that step decides how the reserve and the free list are modelled, and
should decide it knowing the materializer needs only soundness.

**With `kernel-refine.rewrite` and `.discharge`**: every rewrite keeps
`fs.ok` (each free of a node whose header it read; no link into a free
node), and with `KN.wired_ok` kept, `LM.ext.ok` discharged at each
serve. This is where the loop actually closes (F9), for the wiring and
the free list together. The free list's part is a small rider on the
wiring's: the same sites, one more fact a site.

**What each order risks.** All now (A0.2 before `.root`): a week or
more of kernel-facing proof whose statement `kernel-refine.align` may
then reshape (the reserve; statics), on a plan (`cursor-laws`) that is
about the materializer; the loop's remaining steps wait behind it.
All after the loop: `.root` and `.grow` built on eight conjuncts and no
range, then restated; the plan's own rule ("`.loop` restates every
law, so it comes after the steps that add laws") argues against adding
to the pile. All with `kernel-refine`: the same, and the contract's
shape is discovered late, by the plan least able to change the
materializer's laws.

## Recommendation

1. Merge `.loop.shape.next` after F5: `LM.ext.ok` with the chain, the
   layout, the faced ports, bases and past; three conjuncts proved from
   the rest.
2. Open `.loop.shape.grow` with the node-in-range predicate and its
   three lemmas (A0.1); add range and `distinct(N)` to `LM.lx.ok`;
   derive `layout`, `bases`, `past`; restate `ext.ok` over
   `none.in(E, N)` and `nodes.in(E, d)`. Then `.root`.
3. Record the contract (a decision record, superseding the prefix
   law's wording in `splice-frame-premises`): at each serve the kernel
   owes the free list's first `k` nodes chained, in range, with zero
   headers, the list ending; the wiring owes live ports linking live
   ports; the materializer owes the room. Name `fs.ok` as the form,
   soundness without completeness, and put its building in
   `kernel-refine` as a step before `.align`, the keeping in
   `.rewrite`.
4. Decide A0.3 on a measurement, not before: a spike build with room
   made before each serve, the sharing families counted at n, 2n, 4n.
5. Leave `FL.ok` and group A as they are until `kernel-refine` decides
   whether exactness is wanted.

Confidence. High in F5 and F6 as readings of the definitions, unproved.
High that premise 6 needs the zero header (F8). Moderate in F9: the
control flow is read from `glam/core.bend`'s frame and its comments,
not traced through `KD`. Moderate that `ends` gives distinctness as
cheaply as argued; the argument is short on paper and I have not seen
its Bend form. Low on A0.3's cost either way until measured.

Semantic choices made here that I am least sure of: reading the
maintainer's "none for code to rely on" as leaving laws free to rely on
a free node's header; and treating leaks (completeness) as outside what
the materializer's laws should claim.

## Questions for the maintainer

1. **Soundness or exactness.** The materializer's laws need only that a
   node on the free list is not in use. Should the laws also claim that
   every unused node is on the free list or the reserve (no leaks), as
   `FL.ok` does, or is that a property for the audit and a later plan?
2. **The meaning of a zero header.** May a law take "a node whose
   header word is 0 is free, and a node in use has a header that is
   not" as part of what the heap means, as the audit and the wiring's
   model already read it? Your ruling of 2026-11-13 kept a taken or
   freed node's words out of what code may rely on; I read it as
   leaving this open for laws, and would rather ask.
3. **Growth during a serve.** Should a serve be an operation the heap
   never grows under, the materializer making room first, so that
   growth is its own step between serves? Or should a serve remain
   free to grow the heap wherever it allocates, the laws following it
   there?
4. **The kernel between serves.** The loop's invariant is stated from
   one serve to the next on one heap, but the host reduces between
   them. Is the intended claim "serves compose, given the kernel keeps
   the contract" (the contract a premise until `kernel-refine`), or
   should `cursor-laws.loop` not be called closed until a law carries
   the invariant across a kernel step?
5. **Who owes the room.** That the free list holds as many nodes as a
   serve takes is a fact of a run. Should it stay a premise the caller
   owes, become a check the materializer makes, or be made true by
   construction?
