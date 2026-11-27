# Laws of the grown heap in the loop's views (the CursorLaws plan's
# cursor-laws.loop.shape.grow.copy.store.kept): P.grow_more's laws at the
# array level (spike/GROW_LAWS.bend) carried to the views the loop's
# invariant reads, so that the loop laws' growth premises are discharged;
# proved in glam/GROWN_PROOF.bend.

import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/kmodel.bend as KMd
import ./ring_model.bend as RG
import ./loop_model.bend as LM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: each word of each tracked node reads alike after growth (LM.kept,
# lx_up's and grow_next's premise): the view of a heap of 2^(e + 2)
# words whose capacity word reads wc = 2^e nodes, 3 <= e < 28, and the
# view of the grown heap one level deeper, for tracked nodes in range and
# past the header's words. A node off words 0, 1 and 4 is at word 4 or
# past it, so its words miss the capacity's too, which growth writes.
# Record: net-nodes-double
# Record: laws-across-steps-iterative
law grown_kept:
  for w: Array<U32>
  for a: Array<V.Val>
  for +wc: U32
  for +e: Nat
  for N: List<&2, U32>
  for +hf: {AD.full(U32, w, 2n+e) == True{} : Bool}
  for +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_wcap())) == wc : U32}
  for +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}
  for +he3: {Nat.is_le(3n, e) == True{} : Bool}
  for +he27: {Nat.is_lt(e, 28n) == True{} : Bool}
  for +hin: {RG.nodes.in(N, 2n+e) == True{} : Bool}
  for +hp: {KMd.past(N, 2n+e) == True{} : Bool}
  {LM.kept(N, AD.view(U32, w), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a}))))) == True{} : Bool}
