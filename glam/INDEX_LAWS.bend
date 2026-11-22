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
# (IM.tr.cutat); where x was the tree, the index empty. Not claimed: that
# the parent is freed (the free list's head after), which the
# realization does not read; the serve's laws over the free list will.
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

# LAW: inserting cursor x, its key k written at its word 2 and its
# header a leaf's, into the index of situating node s, the heap's words
# realizing the model I on its invariant and laid out apart, k absent
# from it, x and the free list's first node b fresh (IM.ix.fresh,
# IM.ix.room), leaves the words realizing the model with x put
# (IM.ix.put): in an empty index, x alone; else a branch at b, of the
# lowest bit k and the key its descent meets differ at, above the first
# node on k's way not a branch of a bit below it. Not claimed: growth,
# the free list empty with a tree to put into (the splice's precedent).
# Record: cursors-indexed
# Record: hub-laws-reused
law insert_tree:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +b: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}
  for hm: {IM.ix.room(I, AD.view(U32, w), d, b) == True{} : Bool}
  for hk: {KMd.word(AD.view(U32, w), d, (x + 2 : U32)) == k : U32}
  for hb: {X.ix.branch(KMd.word(AD.view(U32, w), d, x)) == False{} : Bool}
  for ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}
  {IM.ix.real(AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{w}, a}, s, x))), d, s, IM.ix.put(I, x, k, b)) == True{} : Bool}

# LAW: and a removal, on remove_tree's premises, writes no word but the
# situating node's word 3, the branches' words and the free list's head
# (the pointer to the parent rewritten, the parent freed): every other
# word reads as before, every cursor's words among them, which a serve's
# next finds and joins read, and the kernel's error count, which no
# removal on these premises raises.
# Record: cursors-indexed
# Record: hub-laws-reused
law remove_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}
  for hj: {IM.ix.offb(I, s, d, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(X.ix.remove(P.H{KM.MG{w}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: and an insert, on insert_tree's premises, writes no word but the
# situating node's word 3, the branches' words, the free list's head,
# the words of the node it takes for its branch, if any, and the new
# cursor's word 3: every other word reads as before, the cursors' words
# and the error count among them.
# Record: cursors-indexed
# Record: hub-laws-reused
law insert_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +b: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}
  for hm: {IM.ix.room(I, AD.view(U32, w), d, b) == True{} : Bool}
  for hk: {KMd.word(AD.view(U32, w), d, (x + 2 : U32)) == k : U32}
  for hb: {X.ix.branch(KMd.word(AD.view(U32, w), d, x)) == False{} : Bool}
  for ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}
  for hj: {IM.ix.offb(I, s, d, j) == True{} : Bool}
  for hjb: {IM.ix.newb(I, b, d, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  for hjx: {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(X.ix.insert(P.H{KM.MG{w}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}
