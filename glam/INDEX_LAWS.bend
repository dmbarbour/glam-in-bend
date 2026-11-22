# A copy's index's laws (glam/index.bend; the Cells plan's
# cells-freeze.sharing.cursors.index.laws): the tree's operations on the
# heap's words against its model (glam/index_model.bend), and the model's
# own. Apart from glam/LAWS.bend, the ring's, so that a change to either
# reruns its own proofs alone. As there, a heap is stated by its parts,
# its words w and its value table a, the words a perfect tree of depth d
# below 32 (lawful-arrays, hub-laws-reused).

import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/kmodel.bend as KMd
import ./index.bend as X
import ./index_model.bend as IM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: two keys unequal, the scan of their 32 bits from the lowest
# (X.ix.diff) stops, at a bit they differ at, so that an insert of a key
# absent from a tree finds the bit its new branch tests and raises no
# error: a U32 is its 32 bits.
# Record: cursors-indexed
# Record: hub-laws-reused
law ne_found:
  for +a: U32
  for +b: U32
  for hne: {U32.is_eq(a, b) == False{} : Bool}
  {IM.cr.go(X.ix.diff(a, b)) == False{} : Bool}

# LAW: a tree's descent for key k (the model's look, as the code's find
# goes) hands back the leaf at k, if any (IM.tr.at, a search of every
# leaf): every key below a branch on the side its bit gives, so that no
# leaf off the descent's way holds k.
# Record: cursors-indexed
law look_at:
  for +I: IM.Ix
  for +k: U32
  for hi: {IM.ix.inv(I) == True{} : Bool}
  {IM.ix.look(I, k) == IM.ix.at(I, k) : Maybe<&2, U32>}

# LAW: a find for key k in the index of situating node s, the heap's
# words realizing the model I (IM.ix.real) on its invariant, hands the
# heap back, no error raised, and gives the model's look: the cursor at
# k, if any (look_at). The descent's fuel, 33, is enough: bits rise from
# the root, each below 32.
# Record: cursors-indexed
# Record: hub-laws-reused
law find_tree:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +k: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  {X.ix.find(P.H{KM.MG{w}, a}, s, k) == (P.H{KM.MG{w}, a}, IM.ix.look(I, k)) : P.H & Maybe<&2, U32>}

# LAW: removing cursor x, the leaf at key k (IM.ix.look), from the index
# of situating node s, the heap's words realizing the model I on its
# invariant and its nodes laid out apart (IM.ix.lay), leaves the words
# realizing the model without x (IM.ix.del): x's parent, if any, given
# up for x's sibling, the pointer to it rewritten and the parent freed
# (IM.tr.cutat); where x was the tree, the index empty.
# Record: cursors-indexed
# Record: hub-laws-reused
law remove_tree:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}
  {IM.ix.real(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{w}, a}, s, x))), d, s, IM.ix.del(I, x, k)) == True{} : Bool}
