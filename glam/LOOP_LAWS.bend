# Laws of the pending invariant across serves (the CursorLaws plan's
# cursor-laws.loop): its base case, at a live source's first use, and
# what keeps it from one serve to the next; proved in
# glam/LOOP_PROOF.bend.

import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/kmodel.bend as KMd
import ../spike/grow_model.bend as GM
import ./ring.bend as R
import ./ring_model.bend as RG
import ./index_model.bend as IM
import ./loop_model.bend as LM
import ../spike/tpl.bend as T
import ./splice_copy.bend as S
import ./splice_model.bend as SM
import ./serve_model.bend as SV
import ./serve.bend as SC
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: a situating node taken from the free list and written an empty
# index (R.situate, the first use of a live source, glam/core.bend's
# use.top) gives the pending invariant (RG.px.ok) over that index, the
# leaf the use stopped needing pending, the situating node and the leaf
# live, the rest of the free list F free, every node of N tracked; and
# the words full. So that cursor_pend, putting the leaf in the index,
# applies to the first use as to every crossing
# (cursor-laws.loop.base.situate). Premises: the free list's chain
# starting s, then F, distinct; the leaf none of them; the tracked nodes
# laid out apart, each its own base, at a depth of 2 or more; the leaf's
# link word q, which the writes leave, facing a port off the live nodes'
# keys and homes (port.ok), its link word off the tracked nodes' words
# but the live ones' (po.all), and facing neither the leaf nor the
# situating node. Not claimed: the reserve's and the doubling's paths,
# where the free list is empty (px_grow, cursor-laws.loop.shape).
# Record: cursors-indexed
# Record: copy-links-two-way
# Record: net-obvious-errors
law situate_pend:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +by: U32
  for +k: U32
  for +s: U32
  for +leaf: U32
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +hf: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +h2: {Nat.is_le(2n, d) == True{} : Bool}
  for +hch: {KMd.chain(Con{s, F}, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}
  for +hdF: {RG.distinct(Con{s, F}) == True{} : Bool}
  for +hN: {RG.layout(N, d) == True{} : Bool}
  for +hB: {RG.bases(N) == True{} : Bool}
  for +hsN: {RG.sub(Con{s, Con{leaf, Nil{}}}, N) == True{} : Bool}
  for +hFN: {RG.sub(F, N) == True{} : Bool}
  for +hlf: {RG.none.in(Con{leaf, Nil{}}, Con{s, F}) == True{} : Bool}
  for +hq1: {RG.port.ok(Con{s, Con{leaf, Nil{}}}, d, KMd.word(AD.view(U32, w), d, (leaf + 1 : U32))) == True{} : Bool}
  for +hq2: {RG.po.all(KMd.word(AD.view(U32, w), d, (leaf + 1 : U32)), Con{s, Con{leaf, Nil{}}}, d, N) == True{} : Bool}
  for +hq3: {KMd.off.port(d, KMd.word(AD.view(U32, w), d, (leaf + 1 : U32)), (leaf + 1 : U32)) == True{} : Bool}
  for +hq4: {KMd.off.port(d, KMd.word(AD.view(U32, w), d, (leaf + 1 : U32)), (s + 1 : U32)) == True{} : Bool}
  {RG.px.ok(AD.view(U32, RG.words(Pair.fst(P.H, U32, R.situate(P.H{KM.MG{w}, a}, by, k)))), d, s, IM.Ept{}, Con{leaf, Nil{}}, Con{s, Con{leaf, Nil{}}}, F, N) && AD.full(U32, RG.words(Pair.fst(P.H, U32, R.situate(P.H{KM.MG{w}, a}, by, k))), d) == True{} : Bool}

# LAW: the crossings keep the live nodes distinct (P5,
# cursor-laws.loop.shape.distinct): each crossing either makes a cursor,
# its live list as it was, or joins two cursors, taking both out of the
# list (RG.cx.L, RG.without), never adding to it. A model law.
# Record: cursors-indexed
law cxs_distinct:
  for cs: List<&2, R.FzC>
  for +vm: List<&2, U32>
  for +dm: Nat
  for +I: IM.Ix
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +h: {RG.distinct(L) == True{} : Bool}
  {RG.distinct(RG.cxs.L(RG.cxs(cs, vm, dm, I, L, F))) == True{} : Bool}

# LAW: the pending invariant over a sub-list of the tracked nodes, the
# live, free and index's nodes still among it (P11,
# cursor-laws.loop.shape.track): so that one tracked list serves a whole
# run, each serve's laws taking the sub-list they name (the old nodes and
# the copy's). Only the faced ports' link words read the tracked list,
# kept off every one of its nodes, so off a sub-list's.
# Record: cursors-indexed
law px_sub:
  for +v: List<&2, U32>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +ps: List<&2, U32>
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +N2: List<&2, U32>
  for +hp: {RG.px.ok(v, d, s, I, ps, L, F, N) == True{} : Bool}
  for +hs: {RG.sub(N2, N) == True{} : Bool}
  for +hL: {RG.sub(L, N2) == True{} : Bool}
  for +hF: {RG.sub(F, N2) == True{} : Bool}
  for +hI: {RG.sub(IM.ix.nodes(I), N2) == True{} : Bool}
  {RG.px.ok(v, d, s, I, ps, L, F, N2) == True{} : Bool}

# LAW: a serve away from the source's root keeps the wider invariant
# (LM.lx.ok: the pending one with nothing pending, the live nodes
# distinct, the tracked distinct and in range, each its own base, past
# the header, so laid out apart by bases_apart, given 2 <= d), its
# tracked nodes then the old ones and the copy's holes
# (cursor-laws.loop.shape.serve): serve_pend composed with the live
# nodes' distinctness (cxs_distinct; the copy's holes fresh, among the
# nodes taken from the free list) and the tracked facts over a sub-list.
# So that a serve's conclusion is the next one's premise but for the
# tracked list's growth, which the next copy's nodes need (premises, the
# maintainer, 2026-11-26).
# Record: cursors-indexed
# Record: serve-premises-over-index
# Record: copy-reduced-function-nets
law serve_loop:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for dm: Nat
  for ts: List<&2, T.TNode>
  for ls: List<&2, T.TLink>
  for by: U32
  for ns: List<&2, U32>
  for s: U32
  for t: List<&2, U32>
  for cs: List<&2, R.FzC>
  for I: IM.Ix
  for F: List<&2, U32>
  for M: List<&2, U32>
  for nc: U32
  for rn: U32
  for rp: U32
  for +hf: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +h2: {Nat.is_le(2n, d) == True{} : Bool}
  for +hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for +hlx: {LM.lx.ok(AD.view(U32, w), d, s, I, Con{s, t}, List.append(&2, U32, ns, F), List.append(&2, U32, M, ns)) == True{} : Bool}
  for +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}
  for +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  for +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}
  for +hcp: {SV.copy.ok(cs, ls, ts, dm) == True{} : Bool}
  for +hok: {RG.cxs.ok(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, F) == True{} : Bool}
  {LM.lx.ok(AD.view(U32, RG.words(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, False{}))), d, s, RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), RG.cxs.L(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), RG.cxs.F(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), List.append(&2, U32, M, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm))) && AD.full(U32, RG.words(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, False{})), d) == True{} : Bool}

# LAW: the live list after the crossings is still headed by the situating
# node s (cursor-laws.loop.shape.next.head): no crossing takes s out, a
# join taking its placeholder, a hole, which s is not, and the cursor the
# index finds, one of its leaves, which s is never among: a removal keeps
# the leaves' members (adds none), a put adds the placeholder. So that the
# next serve's live list is Con{s, ...}, as its laws ask. A model law.
# Record: cursors-indexed
law cxs_head:
  for cs: List<&2, R.FzC>
  for +vm: List<&2, U32>
  for +dm: Nat
  for +I: IM.Ix
  for +s: U32
  for +t: List<&2, U32>
  for +F: List<&2, U32>
  for +hI: {RG.has(IM.ix.leaves(I), s) == False{} : Bool}
  for +hp: {RG.has(RG.pls(cs, vm, dm), s) == False{} : Bool}
  {LM.headed(RG.cxs.L(RG.cxs(cs, vm, dm, I, Con{s, t}, F)), s) == True{} : Bool}

# LAW: the wider invariant over the next serve's lists
# (cursor-laws.loop.shape.next.split): the live list as Con{s, tl}, the
# free list's tracked prefix split into the next copy's k nodes and the
# rest (List.take, List.drop), the tracked list the old nodes but those,
# then those (RG.minus), the live list headed by s (cxs_head). The serve's
# laws ask their lists in that shape; the members are the same.
# Record: cursors-indexed
law lx_split:
  for +v: List<&2, U32>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +k: Nat
  for +hlx: {LM.lx.ok(v, d, s, I, L, F, N) == True{} : Bool}
  for +hh: {LM.headed(L, s) == True{} : Bool}
  {LM.lx.ok(v, d, s, I, Con{s, LM.tl(L)}, List.append(&2, U32, List.take(&2, U32, F, k), List.drop(&2, U32, F, k)), List.append(&2, U32, RG.minus(N, List.take(&2, U32, F, k)), List.take(&2, U32, F, k))) == True{} : Bool}

# LAW: the wider invariant over the tracked list and the free list's
# tracked prefix grown by free nodes E past it
# (cursor-laws.loop.shape.next.extend), for the next copy needing more
# nodes than the prefix holds. Premises (LM.ext.ok), the kernel's to
# discharge (kernel-refine; the maintainer, 2026-11-26: "Premises now is
# acceptable."): E laid out apart from the tracked nodes, stated as E
# none twice, none of them, and in range (RG.nodes.in), the layout then
# arithmetic (bases_apart); and no live node's faced port linking into E
# (px.off over E), the host's wiring (net-obvious-errors). Besides: the
# free list's chain over F ++ E, each its own base, past the header. That
# E is none of the live nodes, s or the index's follows from its being
# none of the tracked (docs/reviews/AllocFable_2026-11-26.md, F5).
# Record: cursors-indexed
# Record: net-obvious-errors
law lx_extend:
  for +v: List<&2, U32>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +E: List<&2, U32>
  for +hlx: {LM.lx.ok(v, d, s, I, L, F, N) == True{} : Bool}
  for +hE: {LM.ext.ok(v, d, s, I, L, F, N, E) == True{} : Bool}
  {LM.lx.ok(v, d, s, I, L, List.append(&2, U32, F, E), List.append(&2, U32, N, E)) == True{} : Bool}

# LAW: one serve's conclusion to the next one's premise
# (cursor-laws.loop.shape.next.compose): serve_loop, the live list headed
# by s after it (cxs_head: s no leaf of the index, which is laid out
# apart from it, and none of the copy's holes, taken from the free list),
# the tracked lists grown by free nodes E past them (lx_extend, under the
# growth premises, LM.ext.ok) and split for the next copy's k nodes
# (lx_split): the next serve's live list Con{s, tl}, its free list
# take ++ drop, its tracked list the rest, then those, as serve_loop asks.
# Two serves with no kernel step between: the host reduces between serves
# (host.go), and carrying the invariant across its steps is the kernel
# refinement's (docs/reviews/Alloc_2026-11-26.md).
# Record: cursors-indexed
# Record: serve-premises-over-index
# Record: copy-reduced-function-nets
# Record: net-obvious-errors
law serve_next:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for dm: Nat
  for ts: List<&2, T.TNode>
  for ls: List<&2, T.TLink>
  for by: U32
  for ns: List<&2, U32>
  for s: U32
  for t: List<&2, U32>
  for cs: List<&2, R.FzC>
  for I: IM.Ix
  for F: List<&2, U32>
  for M: List<&2, U32>
  for nc: U32
  for rn: U32
  for rp: U32
  for +E: List<&2, U32>
  for +k: Nat
  for +hf: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +h2: {Nat.is_le(2n, d) == True{} : Bool}
  for +hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for +hlx: {LM.lx.ok(AD.view(U32, w), d, s, I, Con{s, t}, List.append(&2, U32, ns, F), List.append(&2, U32, M, ns)) == True{} : Bool}
  for +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}
  for +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  for +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}
  for +hcp: {SV.copy.ok(cs, ls, ts, dm) == True{} : Bool}
  for +hok: {RG.cxs.ok(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, F) == True{} : Bool}
  for +hE: {LM.ext.ok(AD.view(U32, RG.words(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, False{}))), d, s, RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), RG.cxs.L(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), RG.cxs.F(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), List.append(&2, U32, M, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), E) == True{} : Bool}
  {LM.lx.ok(AD.view(U32, RG.words(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, False{}))), d, s, RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), Con{s, LM.tl(RG.cxs.L(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)))}, List.append(&2, U32, List.take(&2, U32, List.append(&2, U32, RG.cxs.F(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), E), k), List.drop(&2, U32, List.append(&2, U32, RG.cxs.F(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), E), k)), List.append(&2, U32, RG.minus(List.append(&2, U32, List.append(&2, U32, M, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), E), List.take(&2, U32, List.append(&2, U32, RG.cxs.F(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), E), k)), List.take(&2, U32, List.append(&2, U32, RG.cxs.F(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), E), k))) && AD.full(U32, RG.words(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, False{})), d) == True{} : Bool}

# LAW: the layout by arithmetic (cursor-laws.loop.shape.grow.layout; the
# generalized bases_apart): nodes each its own base, past the header, its
# words below the words' count (RG.nodes.in), none twice, are laid out
# apart. A node's four words differ modulo 4, and from the head's word by
# being past the header; two nodes' words at one offset differ as their
# bases do, a slot being the word itself below 2^d. So that the tracked
# list's layout is per-node facts and distinctness, which an append, a
# sub-list and the heap's doubling keep. The arithmetic law the maintainer
# deferred (2026-11-26: "Premises now is acceptable.").
# Record: cursors-indexed
law bases_apart:
  for +N: List<&2, U32>
  for +d: Nat
  for +h2: {Nat.is_le(2n, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +hB: {RG.bases(N) == True{} : Bool}
  for +hP: {KMd.past(N, d) == True{} : Bool}
  for +hI: {RG.nodes.in(N, d) == True{} : Bool}
  for +hD: {RG.distinct(N) == True{} : Bool}
  {RG.layout(N, d) == True{} : Bool}

# LAW: the wider invariant with the free list's tracked prefix dropped
# (cursor-laws.loop.shape.grow.copy.drop): between serves the kernel's
# steps take and give free nodes, so the prefix one serve leaves is not
# the next one's (docs/reviews/AllocFable_2026-11-26.md, F9); the
# invariant handed on holds nothing of the free list, which the next
# serve's contract asks afresh (LM.ext.ok at F = Nil). Structural: it
# forgets facts, so no mutation of the code can make it false.
# Record: cursors-indexed
# Record: laws-across-steps-iterative
law lx_drop:
  for +v: List<&2, U32>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +hlx: {LM.lx.ok(v, d, s, I, L, F, N) == True{} : Bool}
  {LM.lx.ok(v, d, s, I, L, Nil{}, N) == True{} : Bool}

# LAW: the wider invariant, its free prefix dropped (lx_drop), carried
# across the heap's doubling (cursor-laws.loop.shape.grow.copy.up): from
# the view v at depth d to the grown view v2 at 1n+d, where each word of
# each tracked node reads alike (LM.kept, the growth law's to discharge)
# and the port each live node faces links a word in range (LM.faced.in,
# the wiring's): the reads by the kept words, every slot inequality kept
# from d to 1n+d, and the one slot equality, a live node faced back, by
# both its words in range. Then lx_extend at 1n+d adds the fresh nodes.
# Record: cursors-indexed
# Record: laws-across-steps-iterative
# Record: net-obvious-errors
law lx_up:
  for +v: List<&2, U32>
  for +v2: List<&2, U32>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +L: List<&2, U32>
  for +N: List<&2, U32>
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +hlx: {LM.lx.ok(v, d, s, I, L, Nil{}, N) == True{} : Bool}
  for +hk: {LM.kept(N, v, d, v2) == True{} : Bool}
  for +hfi: {LM.faced.in(L, v, d) == True{} : Bool}
  {LM.lx.ok(v2, 1n+d, s, I, L, Nil{}, N) == True{} : Bool}

# LAW: the wider invariant across the heap's doubling, for the next serve
# (cursor-laws.loop.shape.grow.copy.up): its free prefix dropped
# (lx_drop), carried to the grown view at 1n+d (lx_up), and the fresh
# nodes E, the free list's first, added under the growth premises at
# 1n+d (lx_extend, LM.ext.ok over no prefix). So that after growth the
# next serve finds the invariant it asks, the fresh nodes its copy's.
# Record: cursors-indexed
# Record: laws-across-steps-iterative
law grow_next:
  for +v: List<&2, U32>
  for +v2: List<&2, U32>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +E: List<&2, U32>
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +hlx: {LM.lx.ok(v, d, s, I, L, F, N) == True{} : Bool}
  for +hk: {LM.kept(N, v, d, v2) == True{} : Bool}
  for +hfi: {LM.faced.in(L, v, d) == True{} : Bool}
  for +hE: {LM.ext.ok(v2, 1n+d, s, I, L, Nil{}, N, E) == True{} : Bool}
  {LM.lx.ok(v2, 1n+d, s, I, L, E, List.append(&2, U32, N, E)) == True{} : Bool}

# LAW: the serve at the source's root keeps the wider invariant
# (cursor-laws.loop.shape.root): serve_ring_exact composed as serve_loop
# composes serve_pend, the served cursor nc, found at k, taken out of the
# live list (without_distinct) and freed with the branch above it, which
# head the free list; the tracked nodes the old ones and the copy's holes.
# Its premises serve_loop's and the root's (the cursor found, no crossing
# looking for its key at its far end, the root no hole at a port below 3).
# Record: cursors-indexed
# Record: serve-premises-over-index
# Record: copy-reduced-function-nets
law serve_root_loop:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for dm: Nat
  for ts: List<&2, T.TNode>
  for ls: List<&2, T.TLink>
  for by: U32
  for ns: List<&2, U32>
  for s: U32
  for t: List<&2, U32>
  for cs: List<&2, R.FzC>
  for I: IM.Ix
  for F: List<&2, U32>
  for M: List<&2, U32>
  for nc: U32
  for k: U32
  for rn: U32
  for rp: U32
  for +hf: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +h2: {Nat.is_le(2n, d) == True{} : Bool}
  for +hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for +hlx: {LM.lx.ok(AD.view(U32, w), d, s, I, Con{s, t}, List.append(&2, U32, ns, F), List.append(&2, U32, M, ns)) == True{} : Bool}
  for +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}
  for +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  for +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}
  for +hcp: {SV.copy.ok(cs, ls, ts, dm) == True{} : Bool}
  for +hok: {RG.cxs.ok(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, F) == True{} : Bool}
  for +hc: {IM.ix.look(I, k) == Some{nc} : Maybe<&2, U32>}
  for +hu: {RG.far.off(cs, k) == True{} : Bool}
  for +hro: {SV.root.ok(rn, rp, ts, dm, cs) == True{} : Bool}
  {LM.lx.ok(AD.view(U32, RG.words(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, True{}))), d, s, IM.ix.del(RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc, k), RG.without(RG.cxs.L(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc), Con{nc, IM.mb.cons(IM.ix.par(RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc, k), RG.cxs.F(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)))}, List.append(&2, U32, M, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm))) && AD.full(U32, RG.words(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, True{})), d) == True{} : Bool}

# LAW: the root serve's conclusion to the next serve's premise
# (cursor-laws.loop.shape.root.next), as serve_next for serve_loop: the
# live list still headed by s, the served cursor, a leaf of the index
# before the crossings, not s, which is none (wo_headed, lay_nl); the
# tracked lists grown by free nodes E past them (lx_extend) and split for
# the next copy's kn nodes (lx_split). Two serves with no kernel step
# between, as serve_next.
# Record: cursors-indexed
# Record: serve-premises-over-index
# Record: copy-reduced-function-nets
# Record: net-obvious-errors
law serve_root_next:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for dm: Nat
  for ts: List<&2, T.TNode>
  for ls: List<&2, T.TLink>
  for by: U32
  for ns: List<&2, U32>
  for s: U32
  for t: List<&2, U32>
  for cs: List<&2, R.FzC>
  for I: IM.Ix
  for F: List<&2, U32>
  for M: List<&2, U32>
  for nc: U32
  for k: U32
  for rn: U32
  for rp: U32
  for +E: List<&2, U32>
  for +kn: Nat
  for +hf: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +h2: {Nat.is_le(2n, d) == True{} : Bool}
  for +hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for +hlx: {LM.lx.ok(AD.view(U32, w), d, s, I, Con{s, t}, List.append(&2, U32, ns, F), List.append(&2, U32, M, ns)) == True{} : Bool}
  for +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}
  for +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  for +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}
  for +hcp: {SV.copy.ok(cs, ls, ts, dm) == True{} : Bool}
  for +hok: {RG.cxs.ok(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, F) == True{} : Bool}
  for +hc: {IM.ix.look(I, k) == Some{nc} : Maybe<&2, U32>}
  for +hu: {RG.far.off(cs, k) == True{} : Bool}
  for +hro: {SV.root.ok(rn, rp, ts, dm, cs) == True{} : Bool}
  for +hE: {LM.ext.ok(AD.view(U32, RG.words(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, True{}))), d, s, IM.ix.del(RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc, k), RG.without(RG.cxs.L(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc), Con{nc, IM.mb.cons(IM.ix.par(RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc, k), RG.cxs.F(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)))}, List.append(&2, U32, M, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), E) == True{} : Bool}
  {LM.lx.ok(AD.view(U32, RG.words(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, True{}))), d, s, IM.ix.del(RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc, k), Con{s, LM.tl(RG.without(RG.cxs.L(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc))}, List.append(&2, U32, List.take(&2, U32, List.append(&2, U32, Con{nc, IM.mb.cons(IM.ix.par(RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc, k), RG.cxs.F(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)))}, E), kn), List.drop(&2, U32, List.append(&2, U32, Con{nc, IM.mb.cons(IM.ix.par(RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc, k), RG.cxs.F(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)))}, E), kn)), List.append(&2, U32, RG.minus(List.append(&2, U32, List.append(&2, U32, M, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), E), List.take(&2, U32, List.append(&2, U32, Con{nc, IM.mb.cons(IM.ix.par(RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc, k), RG.cxs.F(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)))}, E), kn)), List.take(&2, U32, List.append(&2, U32, Con{nc, IM.mb.cons(IM.ix.par(RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc, k), RG.cxs.F(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)))}, E), kn))) && AD.full(U32, RG.words(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, True{})), d) == True{} : Bool}

# LAW: the wider invariant across the heap's doubling (P.grow_more,
# cursor-laws.loop.shape.grow.copy.store.kept.carry): from the view of a
# heap of 2^(e + 2) words whose capacity word reads wc = 2^e nodes,
# 3 <= e < 28, to the grown heap's view one level deeper, the fresh nodes
# (GM.fresh) the free list's first and tracked: grow_next, its premises
# discharged by the growth laws (glam/GROWN_LAWS.bend), each faced port
# linking a word in range (LM.faced.in, the wiring's). The heap's shape a
# premise until cursor-laws.loop.shape.grow.copy.store.shape.
# Record: net-nodes-double
# Record: laws-across-steps-iterative
law grow_loop:
  for w: Array<U32>
  for a: Array<V.Val>
  for +wc: U32
  for +e: Nat
  for +s: U32
  for +I: IM.Ix
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +hf: {AD.full(U32, w, 2n+e) == True{} : Bool}
  for +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_wcap())) == wc : U32}
  for +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}
  for +he3: {Nat.is_le(3n, e) == True{} : Bool}
  for +he27: {Nat.is_lt(e, 28n) == True{} : Bool}
  for +hlx: {LM.lx.ok(AD.view(U32, w), 2n+e, s, I, L, F, N) == True{} : Bool}
  for +hfi: {LM.faced.in(L, AD.view(U32, w), 2n+e) == True{} : Bool}
  {LM.lx.ok(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a})))), 3n+e, s, I, L, GM.fresh(U32.to_nat(wc), wc), List.append(&2, U32, N, GM.fresh(U32.to_nat(wc), wc))) == True{} : Bool}

# LAW: the wider invariant and the heap's shape across the heap's
# doubling together (grow_loop over GM.shape): from a heap of the shape
# at e < 28, the grown heap has the shape at e + 1 and the invariant
# holds over its view, the fresh nodes (those of its capacity word) the
# free list's first and tracked.
# Record: net-nodes-double
# Record: laws-across-steps-iterative
law grow_shape_loop:
  for w: Array<U32>
  for a: Array<V.Val>
  for +e: Nat
  for +s: U32
  for +I: IM.Ix
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +hs: {GM.shape(w, e) == True{} : Bool}
  for +he: {Nat.is_lt(e, 28n) == True{} : Bool}
  for +hlx: {LM.lx.ok(AD.view(U32, w), 2n+e, s, I, L, F, N) == True{} : Bool}
  for +hfi: {LM.faced.in(L, AD.view(U32, w), 2n+e) == True{} : Bool}
  {LM.lx.ok(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a})))), 3n+e, s, I, L, GM.fresh(U32.to_nat(Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_wcap()))), Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_wcap()))), List.append(&2, U32, N, GM.fresh(U32.to_nat(Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_wcap()))), Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_wcap()))))) && GM.shape(KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a}))), 1n+e) == True{} : Bool}
