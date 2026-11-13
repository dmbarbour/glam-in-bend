# glam's laws over its own modules, proved in glam/PROOF.bend, beside the
# evaluator spike's (spike/LAWS.bend), whose laws of the kernel's heap
# they build on. As there, a heap is stated by its parts, its words w and
# its value table a, the words a perfect tree of depth d below 32
# (lawful-arrays, hub-laws-reused).

import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ./materialize.bend as M
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: unlinking a cursor x from its ring writes one word alone: word 3
# of the node the ring's walk finds before x (M.rg.pred), given x's next;
# every other word reads as before (cells-freeze.nested.host.join). Not
# claimed: that the node found is x's predecessor, a member of its ring,
# which a model of rings would show; so that its word 3 is no word a
# walk's path reads.
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law unlink_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +x: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hj: {Nat.is_eq(AD.slot((Pair.snd(P.H, U32, M.rg.pred(P.H{KM.MG{w}, a}, x)) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(M.rg.unlink(P.H{KM.MG{w}, a}, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}
