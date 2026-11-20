# The heap primitives' frame laws (spike/kprim.bend's node, link, free,
# put and err_if): each writes no word but those it names. Apart from
# spike/LAWS.bend so that a proof citing them (glam/SPLICE_PROOF.bend's)
# imports these alone, not spike's whole proof file (the Cells plan's
# .host.witness.verdicts); their proofs in spike/HEAP_PROOF.bend.

import Base
import ./val.bend as V
import ./kprim.bend as P
import ./kmem_grow.bend as KM
import ./kmodel.bend as KMd
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: a node taken from a free list that has one leaves every word
# outside that node and the list's head (word P.at_fh()) as it was
# (cells-freeze.nested.host.alloc). The node's own four words are not
# claimed, none for code to rely on (the maintainer, 2026-11-13): the
# code writes its header and its payload word (P.node.fin) and leaves the
# others as the free list left them. The head fh, a node's index plus
# one, is not 0, and the node taken is (fh - 1) << 2. The words a perfect
# tree of depth d below 32. Not claimed: the reserve's and the doubling's
# paths, where the list is empty; that the node taken was free (the free
# list's exactness, FL's laws over a model).
# Record: net-nodes-double
# Record: hub-laws-reused
law node_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +fh: U32
  for +hd: U32
  for +p: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hfh: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_fh())) == fh : U32}
  for hne: {U32.is_eq(fh, 0) == False{} : Bool}
  for hj0: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  for hw0: {Nat.is_eq(AD.slot(((fh - 1 : U32) << 2n : U32), d), AD.slot(j, d)) == False{} : Bool}
  for hw1: {Nat.is_eq(AD.slot((((fh - 1 : U32) << 2n : U32) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}
  for hw2: {Nat.is_eq(AD.slot((((fh - 1 : U32) << 2n : U32) + 2 : U32), d), AD.slot(j, d)) == False{} : Bool}
  for hw3: {Nat.is_eq(AD.slot((((fh - 1 : U32) << 2n : U32) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.node(P.H{KM.MG{w}, a}, hd, p)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: and the head then reads the next free node, the link the node
# taken held in its word 1, where neither of the node's own writes lands
# on the head's word.
# Record: net-nodes-double
# Record: hub-laws-reused
law node_next:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +fh: U32
  for +hd: U32
  for +p: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hfh: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_fh())) == fh : U32}
  for hne: {U32.is_eq(fh, 0) == False{} : Bool}
  for hn1: {Nat.is_eq(AD.slot(((fh - 1 : U32) << 2n : U32), d), AD.slot(P.at_fh(), d)) == False{} : Bool}
  for hn2: {Nat.is_eq(AD.slot((((fh - 1 : U32) << 2n : U32) + P.node.word(hd) : U32), d), AD.slot(P.at_fh(), d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.node(P.H{KM.MG{w}, a}, hd, p)), P.at_fh())) == Pair.snd(Array<U32>, U32, Array.get(U32, w, ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))) : U32}

# LAW: and the node taken is the head's: (fh - 1) << 2.
# Record: net-nodes-double
# Record: hub-laws-reused
law node_index:
  for w: Array<U32>
  for a: Array<V.Val>
  for +fh: U32
  for +hd: U32
  for +p: U32
  for hfh: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_fh())) == fh : U32}
  for hne: {U32.is_eq(fh, 0) == False{} : Bool}
  {Pair.snd(P.H, U32, P.node(P.H{KM.MG{w}, a}, hd, p)) == ((fh - 1 : U32) << 2n : U32) : U32}

# LAW: linking two ports writes at most their two link words
# (cells-freeze.nested.host.join): port y's, unless y is static, and
# z's, unless z is (KMd.off.port; a static has none); every other word
# reads as before. The words a perfect tree of depth d below 32.
# Record: net-nodes-double
# Record: hub-laws-reused
law link_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +y: U32
  for +z: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hy: {KMd.off.port(d, y, j) == True{} : Bool}
  for hz: {KMd.off.port(d, z, j) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(P.link_xx(P.H{KM.MG{w}, a}, y, z), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: freeing the node behind reference r leaves every word outside
# that node and the free list's head as it was. The freed node's four
# words are not claimed, none of them for code to rely on (the
# maintainer, 2026-11-13): the code writes its header and its word 1,
# the next free node, and leaves words 2 and 3 as they were, which no
# law promises.
# Record: net-nodes-double
# Record: hub-laws-reused
law free_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +r: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for h0: {Nat.is_eq(AD.slot(P.base(r), d), AD.slot(j, d)) == False{} : Bool}
  for h1: {Nat.is_eq(AD.slot((P.base(r) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}
  for h2: {Nat.is_eq(AD.slot((P.base(r) + 2 : U32), d), AD.slot(j, d)) == False{} : Bool}
  for h3: {Nat.is_eq(AD.slot((P.base(r) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}
  for hh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(P.free(P.H{KM.MG{w}, a}, r), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: a value put in the form a node holds it (P.put) writes no word of
# the net but the value table's bookkeeping in the header (KMd.tab_words:
# its free head, count, capacity and depth), so that a splice's value
# nodes write nothing else of the host (cells-freeze.nested.host.splice.put).
# The table's values are no words, and not claimed.
# Record: splice-frame-premises
# Record: hub-laws-reused
law put_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +v: V.Val
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hj: {KMd.off.words(KMd.tab_words(), d, j) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, P.PW, P.put(P.H{KM.MG{w}, a}, v)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: and an error counted, or not (P.err_if), writes no word but the
# error count (KMd.err_words) (cells-freeze.nested.host.splice.put).
# Record: splice-frame-premises
# Record: hub-laws-reused
law err_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +b: Bool
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hj: {KMd.off.words(KMd.err_words(), d, j) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(P.err_if(b, P.H{KM.MG{w}, a}), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}
