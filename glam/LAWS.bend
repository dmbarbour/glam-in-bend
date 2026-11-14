# glam's laws over its own modules, proved in glam/PROOF.bend, beside the
# evaluator spike's (spike/LAWS.bend), whose laws of the kernel's heap
# they build on. As there, a heap is stated by its parts, its words w and
# its value table a, the words a perfect tree of depth d below 32
# (lawful-arrays, hub-laws-reused).

import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ./ring.bend as R
import ./ring_model.bend as RG
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: unlinking a cursor x from its ring writes one word alone: word 3
# of the node the ring's walk finds before x (R.rg.pred), given x's next;
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
  for hj: {Nat.is_eq(AD.slot((Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{w}, a}, x)) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(R.rg.unlink(P.H{KM.MG{w}, a}, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: the node the ring's walk finds before a member x, the one whose
# word 3 unlinking writes (unlink_keeps), is a member of x's ring, the
# ring closed on the heap's words (glam/ring_model.bend), whatever fuel the
# walk stops with (cells-freeze.nested.host.ring).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law pred_in_ring:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +x: U32
  for +xs: List<&2, U32>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hc: {RG.closed(AD.view(U32, w), d, xs) == True{} : Bool}
  for hx: {RG.has(xs, x) == True{} : Bool}
  {RG.has(xs, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{w}, a}, x))) == True{} : Bool}

# LAW: unlinking a member x of a closed ring leaves it closed: the one
# word written, the found node's word 3 (unlink_keeps, a member,
# pred_in_ring), given x's next, itself a member (cells-freeze.nested.
# host.ring). The member list is the same: x stays listed, its own word
# 3 a member still.
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law unlink_closed:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +x: U32
  for +xs: List<&2, U32>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hc: {RG.closed(AD.view(U32, w), d, xs) == True{} : Bool}
  for hx: {RG.has(xs, x) == True{} : Bool}
  {RG.closed(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{w}, a}, x))), d, xs) == True{} : Bool}

# LAW: inserting a cursor x apart from a closed ring, after its member
# situ, leaves the ring with x added closed: x's word 3 given situ's
# next, a member, and situ's given x (cells-freeze.nested.host.ring).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law insert_closed:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +situ: U32
  for +x: U32
  for +xs: List<&2, U32>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hc: {RG.closed(AD.view(U32, w), d, xs) == True{} : Bool}
  for hs: {RG.has(xs, situ) == True{} : Bool}
  for hx: {RG.apart(xs, d, x) == True{} : Bool}
  {RG.closed(AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{w}, a}, situ, x))), d, Con{x, xs}) == True{} : Bool}

