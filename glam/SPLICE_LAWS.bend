# The splice's laws (cells-freeze.nested.host.splice): a frame over an
# exact list of words (serve-write-sets-hybrid; splice-frame-premises).
# Apart from glam/LAWS.bend, the ring's, so that the ring's laws keep
# their imports to the heap's primitives: the splice's reach the kernel's
# loader (knet.bend), and every change to the kernel reruns these.

import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/tpl.bend as T
import ../spike/kmodel.bend as KMd
import ./splice.bend as S
import ./splice_model.bend as SM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: the splice's node pass, its fresh nodes ns the free list's first
# ones (KMd.chain), laid out apart and past the header's words a splice
# writes, one for each template node, writes no word but theirs, the
# head, and the header's words a value or an error writes
# (KMd.hdr_all), the heap deep enough that those words are apart from
# the head's: every other word reads as before
# (cells-freeze.nested.host.splice.pops). Not claimed: the reserve's and
# the doubling's paths, the list running out; that ns are free and none
# live (the allocator's prefix law, to come).
# Record: splice-frame-premises
# Record: serve-write-sets-hybrid
law nodes_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for +ts: List<&2, T.TNode>
  for +i: U32
  for +by: U32
  for +ns: List<&2, U32>
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}
  for hl: {List.length(&2, T.TNode, ts) == List.length(&2, U32, ns) : Nat}
  for hap: {KMd.apart(ns, d) == True{} : Bool}
  for hpa: {KMd.past(ns, d) == True{} : Bool}
  for hj: {KMd.nodes.off(ns, d, j) == True{} : Bool}
  for hjh: {KMd.off.words(KMd.hdr_all(), d, j) == True{} : Bool}
  for hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(ts, i, S.Sp{P.H{KM.MG{w}, a}, map}, by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}
