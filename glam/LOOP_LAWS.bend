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
