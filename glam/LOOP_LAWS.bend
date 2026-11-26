# Laws of the pending invariant across serves (the CursorLaws plan's
# cursor-laws.loop): its base case, at a live source's first use, and
# what keeps it from one serve to the next; proved in
# glam/LOOP_PROOF.bend.

import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/kmodel.bend as KMd
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
# distinct, the tracked laid out apart, each its own base, past the
# header), its tracked nodes then the old ones and the copy's holes
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
