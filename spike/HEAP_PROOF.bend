# The heap primitives' frame laws' proofs (spike/HEAP_LAWS.bend), moved
# whole from spike/PROOF.bend with the lemmas only they use.

import Base
import ./HEAP_LAWS.bend as Laws
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/LAWS.bend as LA
import ./val.bend as V
import ./kprim.bend as P
import ./kmem_grow.bend as KM
import ./kmodel.bend as KMd
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/PROOF.bend as LAP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_base.bend as LAB

def alloc_pop(+t: LAT.Tree<U32>, -a: Array<V.Val>, +fh: U32,
  hfh: {Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())) == fh : U32},
  hne: {U32.is_eq(fh, 0) == False{} : Bool}) ->
  {P.alloc(P.H{KM.MG{LAT.fromT(U32, t)}, a}) == (P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))))}, a}, ((fh - 1 : U32) << 2n : U32)) : P.H & U32}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), LA.get_pair(U32, LAT.fromT(U32, t), P.at_fh())) :
    {P.alloc.fh(KM.m_get.fin(_), a) == (P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))))}, a}, ((fh - 1 : U32) << 2n : U32)) : P.H & U32}
  %Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), fh, hfh) :
    {P.alloc.k(U32.is_eq(_, 0), _, KM.MG{LAT.fromT(U32, t)}, a) == (P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))))}, a}, ((fh - 1 : U32) << 2n : U32)) : P.H & U32}
  %Equal.sym(Bool, U32.is_eq(fh, 0), False{}, hne) :
    {P.alloc.k(_, fh, KM.MG{LAT.fromT(U32, t)}, a) == (P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))))}, a}, ((fh - 1 : U32) << 2n : U32)) : P.H & U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))) :
    {P.alloc.pop(KM.m_get.fin(_), ((fh - 1 : U32) << 2n : U32), a) == (P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))))}, a}, ((fh - 1 : U32) << 2n : U32)) : P.H & U32}
  {==}

# a node's payload word, 2 or 3 by its kind: the slot it writes is
# neither of the slots the law's premises keep it from
def word_ne(+hd: U32, +n: U32, +d: Nat, +j: U32, +b: Bool, e: {U32.is_eq((hd .&. 63 : U32), 5) == b : Bool},
  +h2: {Nat.is_eq(AD.slot((n + 2 : U32), d), AD.slot(j, d)) == False{} : Bool},
  +h3: {Nat.is_eq(AD.slot((n + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}) ->
  {Nat.is_eq(AD.slot((n + P.node.word(hd) : U32), d), AD.slot(j, d)) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq((hd .&. 63 : U32), 5), True{}, e) :
        {Nat.is_eq(AD.slot((n + P.node.word.t(_) : U32), d), AD.slot(j, d)) == False{} : Bool}
      h2
    case False{}:
      %Equal.sym(Bool, U32.is_eq((hd .&. 63 : U32), 5), False{}, e) :
        {Nat.is_eq(AD.slot((n + P.node.word.t(_) : U32), d), AD.slot(j, d)) == False{} : Bool}
      h3

def node_keeps.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +fh: U32, +hd: U32, +p: U32, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hfh: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_fh())) == fh : U32},
  +hne: {U32.is_eq(fh, 0) == False{} : Bool},
  +hj0: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool},
  +hw0: {Nat.is_eq(AD.slot(((fh - 1 : U32) << 2n : U32), d), AD.slot(j, d)) == False{} : Bool},
  -hw1: {Nat.is_eq(AD.slot((((fh - 1 : U32) << 2n : U32) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool},
  +hw2: {Nat.is_eq(AD.slot((((fh - 1 : U32) << 2n : U32) + 2 : U32), d), AD.slot(j, d)) == False{} : Bool},
  +hw3: {Nat.is_eq(AD.slot((((fh - 1 : U32) << 2n : U32) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool},
  m: LAT.Mirror(U32, w)) ->
  {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.node(P.H{KM.MG{w}, a}, hd, p)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hfht = LAB.subst(Array<U32>, x => {Pair.snd(Array<U32>, U32, Array.get(U32, x, P.at_fh())) == fh : U32}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hfh)
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))), hft)
  +hf2 = LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), d, ((fh - 1 : U32) << 2n : U32), hd, hf1)
  %e : {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.node(P.H{KM.MG{_}, a}, hd, p)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %Equal.sym(P.H & U32, P.alloc(P.H{KM.MG{LAT.fromT(U32, t)}, a}), (P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))))}, a}, ((fh - 1 : U32) << 2n : U32)), alloc_pop(t, a, fh, hfht, hne)) :
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.node.fin(_, hd, p)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, a}, j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), ((((fh - 1 : U32) << 2n : U32)) + P.node.word(hd) : U32), p), j), (Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), ((((fh - 1 : U32) << 2n : U32)) + P.node.word(hd) : U32), p), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), ((((fh - 1 : U32) << 2n : U32)) + P.node.word(hd) : U32), p), j))), LA.get_pair(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), ((((fh - 1 : U32) << 2n : U32)) + P.node.word(hd) : U32), p), j)) :
    {Pair.snd(P.H, U32, P.rd.fin(KM.m_get.fin(_), a)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, a}, j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), j), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j))), LA.get_pair(U32, LAT.fromT(U32, t), j)) :
    {Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), ((((fh - 1 : U32) << 2n : U32)) + P.node.word(hd) : U32), p), j)) == Pair.snd(P.H, U32, P.rd.fin(KM.m_get.fin(_), a)) : U32}
  Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), ((((fh - 1 : U32) << 2n : U32)) + P.node.word(hd) : U32), p), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)),
    LA.get_set_other(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), d, ((((fh - 1 : U32) << 2n : U32)) + P.node.word(hd) : U32), j, p, hf2, hd32, word_ne(hd, ((fh - 1 : U32) << 2n : U32), d, j, U32.is_eq((hd .&. 63 : U32), 5), {==}, hw2, hw3)),
    Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)),
      LA.get_set_other(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), d, ((fh - 1 : U32) << 2n : U32), j, hd, hf1, hd32, hw0),
      LA.get_set_other(U32, LAT.fromT(U32, t), d, P.at_fh(), j, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))), hft, hd32, hj0)))

def Laws.node_keeps(w, a, d, fh, hd, p, j, hf, hd32, hfh, hne, hj0, hw0, hw1, hw2, hw3):
  node_keeps.go(w, a, d, fh, hd, p, j, hf, hd32, hfh, hne, hj0, hw0, hw1, hw2, hw3, LAT.mirror(U32, w))

def node_next.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +fh: U32, +hd: U32, +p: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hfh: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_fh())) == fh : U32},
  +hne: {U32.is_eq(fh, 0) == False{} : Bool},
  +hn1: {Nat.is_eq(AD.slot(((fh - 1 : U32) << 2n : U32), d), AD.slot(P.at_fh(), d)) == False{} : Bool},
  +hn2: {Nat.is_eq(AD.slot(((((fh - 1 : U32) << 2n : U32)) + P.node.word(hd) : U32), d), AD.slot(P.at_fh(), d)) == False{} : Bool},
  m: LAT.Mirror(U32, w)) ->
  {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.node(P.H{KM.MG{w}, a}, hd, p)), P.at_fh())) == Pair.snd(Array<U32>, U32, Array.get(U32, w, ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))) : U32}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hfht = LAB.subst(Array<U32>, x => {Pair.snd(Array<U32>, U32, Array.get(U32, x, P.at_fh())) == fh : U32}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hfh)
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))), hft)
  +hf2 = LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), d, ((fh - 1 : U32) << 2n : U32), hd, hf1)
  %e : {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.node(P.H{KM.MG{_}, a}, hd, p)), P.at_fh())) == Pair.snd(Array<U32>, U32, Array.get(U32, _, ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))) : U32}
  %Equal.sym(P.H & U32, P.alloc(P.H{KM.MG{LAT.fromT(U32, t)}, a}), (P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))))}, a}, ((fh - 1 : U32) << 2n : U32)), alloc_pop(t, a, fh, hfht, hne)) :
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.node.fin(_, hd, p)), P.at_fh())) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), ((((fh - 1 : U32) << 2n : U32)) + P.node.word(hd) : U32), p), P.at_fh()), (Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), ((((fh - 1 : U32) << 2n : U32)) + P.node.word(hd) : U32), p), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), ((((fh - 1 : U32) << 2n : U32)) + P.node.word(hd) : U32), p), P.at_fh()))), LA.get_pair(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), ((((fh - 1 : U32) << 2n : U32)) + P.node.word(hd) : U32), p), P.at_fh())) :
    {Pair.snd(P.H, U32, P.rd.fin(KM.m_get.fin(_), a)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))) : U32}
  Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), ((((fh - 1 : U32) << 2n : U32)) + P.node.word(hd) : U32), p), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))),
    LA.get_set_other(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), d, ((((fh - 1 : U32) << 2n : U32)) + P.node.word(hd) : U32), P.at_fh(), p, hf2, hd32, hn2),
    Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))),
      LA.get_set_other(U32, Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), d, ((fh - 1 : U32) << 2n : U32), P.at_fh(), hd, hf1, hd32, hn1),
      LA.get_set_same(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))))))

def Laws.node_next(w, a, d, fh, hd, p, hf, hd32, hfh, hne, hn1, hn2):
  node_next.go(w, a, d, fh, hd, p, hf, hd32, hfh, hne, hn1, hn2, LAT.mirror(U32, w))

def node_index.go(-w: Array<U32>, -a: Array<V.Val>, +fh: U32, +hd: U32, +p: U32,
  hfh: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_fh())) == fh : U32},
  +hne: {U32.is_eq(fh, 0) == False{} : Bool},
  m: LAT.Mirror(U32, w)) ->
  {Pair.snd(P.H, U32, P.node(P.H{KM.MG{w}, a}, hd, p)) == ((fh - 1 : U32) << 2n : U32) : U32}:
  (+t, +e) = m
  +hfht = LAB.subst(Array<U32>, x => {Pair.snd(Array<U32>, U32, Array.get(U32, x, P.at_fh())) == fh : U32}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hfh)
  %e : {Pair.snd(P.H, U32, P.node(P.H{KM.MG{_}, a}, hd, p)) == ((fh - 1 : U32) << 2n : U32) : U32}
  %Equal.sym(P.H & U32, P.alloc(P.H{KM.MG{LAT.fromT(U32, t)}, a}), (P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))))}, a}, ((fh - 1 : U32) << 2n : U32)), alloc_pop(t, a, fh, hfht, hne)) :
    {Pair.snd(P.H, U32, P.node.fin(_, hd, p)) == ((fh - 1 : U32) << 2n : U32) : U32}
  {==}

def Laws.node_index(w, a, fh, hd, p, hfh, hne):
  node_index.go(w, a, fh, hd, p, hfh, hne, LAT.mirror(U32, w))

# A read of a heap made the read of its words, the get made a literal pair
def rd_get(w: Array<U32>, -a: Array<V.Val>, +j: U32) ->
  {Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) == Pair.snd(Array<U32>, U32, Array.get(U32, w, j)) : U32}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, w, j), (w, Pair.snd(Array<U32>, U32, Array.get(U32, w, j))), LA.get_pair(U32, w, j)) :
    {Pair.snd(P.H, U32, P.rd.fin(KM.m_get.fin(_), a)) == Pair.snd(Array<U32>, U32, Array.get(U32, w, j)) : U32}
  {==}

# Linking: by the two static tests, each a write or none
def link2(+sy: Bool, +sz: Bool, +t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +y: U32, +z: U32, +j: U32,
  +hf: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hy: {KMd.off.lw(KMd.lw.k(sy, y), d, j) == True{} : Bool},
  +hz: {KMd.off.lw(KMd.lw.k(sz, z), d, j) == True{} : Bool}) ->
  {Pair.snd(P.H, U32, P.rd(P.link.to(sz, P.link.to(sy, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, z), z, y), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)) : U32}:
  match sy:
    case True{}:
      match sz:
        case True{}:
          rd_get(LAT.fromT(U32, t), a, j)
        case False{}:
          Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t), (z + 1 : U32), y)}, a}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t), (z + 1 : U32), y), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), rd_get(Array.set(U32, LAT.fromT(U32, t), (z + 1 : U32), y), a, j), LA.get_set_other(U32, LAT.fromT(U32, t), d, (z + 1 : U32), j, y, hf, hd32, MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((z + 1 : U32), d), AD.slot(j, d)), hz)))
    case False{}:
      match sz:
        case True{}:
          Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z)}, a}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), rd_get(Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), a, j), LA.get_set_other(U32, LAT.fromT(U32, t), d, (y + 1 : U32), j, z, hf, hd32, MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), hy)))
        case False{}:
          Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{Array.set(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), (z + 1 : U32), y)}, a}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), (z + 1 : U32), y), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), rd_get(Array.set(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), (z + 1 : U32), y), a, j), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), (z + 1 : U32), y), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), LA.get_set_other(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), d, (z + 1 : U32), j, y, LA.set_full(U32, LAT.fromT(U32, t), d, (y + 1 : U32), z, hf), hd32, MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((z + 1 : U32), d), AD.slot(j, d)), hz)), LA.get_set_other(U32, LAT.fromT(U32, t), d, (y + 1 : U32), j, z, hf, hd32, MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), hy))))

def link_keeps.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +y: U32, +z: U32, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hy: {KMd.off.port(d, y, j) == True{} : Bool},
  +hz: {KMd.off.port(d, z, j) == True{} : Bool},
  m: LAT.Mirror(U32, w)) ->
  {Pair.snd(P.H, U32, P.rd(P.link_xx(P.H{KM.MG{w}, a}, y, z), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  %e : {Pair.snd(P.H, U32, P.rd(P.link_xx(P.H{KM.MG{_}, a}, y, z), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, a}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), rd_get(LAT.fromT(U32, t), a, j)) :
    {Pair.snd(P.H, U32, P.rd(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, z), j)) == _ : U32}
  link2(P.is_static(y), P.is_static(z), t, a, d, y, z, j, hft, hd32, hy, hz)

def Laws.link_keeps(w, a, d, y, z, j, hf, hd32, hy, hz):
  link_keeps.go(w, a, d, y, z, j, hf, hd32, hy, hz, LAT.mirror(U32, w))

def free_keeps.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +r: U32, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +h0: {Nat.is_eq(AD.slot(P.base(r), d), AD.slot(j, d)) == False{} : Bool},
  +h1: {Nat.is_eq(AD.slot((P.base(r) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool},
  -h2: {Nat.is_eq(AD.slot((P.base(r) + 2 : U32), d), AD.slot(j, d)) == False{} : Bool},
  -h3: {Nat.is_eq(AD.slot((P.base(r) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool},
  +hh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool},
  m: LAT.Mirror(U32, w)) ->
  {Pair.snd(P.H, U32, P.rd(P.free(P.H{KM.MG{w}, a}, r), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t), d, P.base(r), 0, hft)
  +hf2 = LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), d, (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), hf1)
  %e : {Pair.snd(P.H, U32, P.rd(P.free(P.H{KM.MG{_}, a}, r), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), LA.get_pair(U32, LAT.fromT(U32, t), P.at_fh())) :
    {Pair.snd(P.H, U32, P.rd(P.free.fh(KM.m_get.fin(_), a, r), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, a}, j)) : U32}
  %Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, a}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), rd_get(LAT.fromT(U32, t), a, j)) :
    {Pair.snd(P.H, U32, P.rd(P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), P.at_fh(), ((r >> 2n : U32) + 1 : U32))}, a}, j)) == _ : U32}
  Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), P.at_fh(), ((r >> 2n : U32) + 1 : U32))}, a}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), P.at_fh(), ((r >> 2n : U32) + 1 : U32)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), rd_get(Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), P.at_fh(), ((r >> 2n : U32) + 1 : U32)), a, j), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), P.at_fh(), ((r >> 2n : U32) + 1 : U32)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), d, P.at_fh(), j, ((r >> 2n : U32) + 1 : U32), hf2, hd32, hh), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), LA.get_set_other(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), d, (P.base(r) + 1 : U32), j, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), hf1, hd32, h1), LA.get_set_other(U32, LAT.fromT(U32, t), d, P.base(r), j, 0, hft, hd32, h0))))

def Laws.free_keeps(w, a, d, r, j, hf, hd32, h0, h1, h2, h3, hh):
  free_keeps.go(w, a, d, r, j, hf, hd32, h0, h1, h2, h3, hh, LAT.mirror(U32, w))

# the table's bookkeeping written back (dt_back): its four words alone,
# whatever the table holds
def dtb_keeps(+t0: LAT.Tree<U32>, tb: P.DT, +d: Nat, +j: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hj: {KMd.off.words(KMd.tab_words(), d, j) == True{} : Bool}) ->
    {Pair.snd(P.H, U32, P.rd(P.dt_back(KM.MG{LAT.fromT(U32, t0)}, tb), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}:
  match tb:
    case P.DT{a2, +fh, +n, +cap, +dd}:
      +hf1 = LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_tfh(), fh, hft)
      +hf2 = LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), d, P.at_tn(), n, hf1)
      +hf3 = LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), P.at_tn(), n), d, P.at_tcap(), cap, hf2)
      Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), P.at_tn(), n), P.at_tcap(), cap), P.at_td(), U32.from_nat(dd))}, a2}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), P.at_tn(), n), P.at_tcap(), cap), P.at_td(), U32.from_nat(dd)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), rd_get(Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), P.at_tn(), n), P.at_tcap(), cap), P.at_td(), U32.from_nat(dd)), a2, j), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), P.at_tn(), n), P.at_tcap(), cap), P.at_td(), U32.from_nat(dd)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), P.at_tn(), n), P.at_tcap(), cap), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), P.at_tn(), n), P.at_tcap(), cap), d, P.at_td(), j, U32.from_nat(dd), hf3, hd32, MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(P.at_td(), d), AD.slot(j, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_td(), d), AD.slot(j, d))), KMd.off.words(Nil{}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(P.at_tcap(), d), AD.slot(j, d))), KMd.off.words(Con{P.at_td(), Nil{}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(P.at_tn(), d), AD.slot(j, d))), KMd.off.words(Con{P.at_tcap(), Con{P.at_td(), Nil{}}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(P.at_tfh(), d), AD.slot(j, d))), KMd.off.words(Con{P.at_tn(), Con{P.at_tcap(), Con{P.at_td(), Nil{}}}}, d, j), hj)))))), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), P.at_tn(), n), P.at_tcap(), cap), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), P.at_tn(), n), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), P.at_tn(), n), d, P.at_tcap(), j, cap, hf2, hd32, MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(P.at_tcap(), d), AD.slot(j, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_tcap(), d), AD.slot(j, d))), KMd.off.words(Con{P.at_td(), Nil{}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(P.at_tn(), d), AD.slot(j, d))), KMd.off.words(Con{P.at_tcap(), Con{P.at_td(), Nil{}}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(P.at_tfh(), d), AD.slot(j, d))), KMd.off.words(Con{P.at_tn(), Con{P.at_tcap(), Con{P.at_td(), Nil{}}}}, d, j), hj))))), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), P.at_tn(), n), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), LA.get_set_other(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), d, P.at_tn(), j, n, hf1, hd32, MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(P.at_tn(), d), AD.slot(j, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_tn(), d), AD.slot(j, d))), KMd.off.words(Con{P.at_tcap(), Con{P.at_td(), Nil{}}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(P.at_tfh(), d), AD.slot(j, d))), KMd.off.words(Con{P.at_tn(), Con{P.at_tcap(), Con{P.at_td(), Nil{}}}}, d, j), hj)))), LA.get_set_other(U32, LAT.fromT(U32, t0), d, P.at_tfh(), j, fh, hft, hd32, MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(P.at_tfh(), d), AD.slot(j, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_tfh(), d), AD.slot(j, d))), KMd.off.words(Con{P.at_tn(), Con{P.at_tcap(), Con{P.at_td(), Nil{}}}}, d, j), hj)))))))

# and through the table's put, its pair matched, whatever it computed
def dto_keeps(+t0: LAT.Tree<U32>, r: P.DT & U32, +d: Nat, +j: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hj: {KMd.off.words(KMd.tab_words(), d, j) == True{} : Bool}) ->
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.dt_op.fin(r, KM.MG{LAT.fromT(U32, t0)})), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}:
  match r:
    case (tb, +i):
      dtb_keeps(t0, tb, d, j, hft, hd32, hj)

# a value put in the table: its four reads of the header made pairs,
# then the table's put, whatever it computed
def tab_keeps(+t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +x: V.Val, +d: Nat, +j: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hj: {KMd.off.words(KMd.tab_words(), d, j) == True{} : Bool}) ->
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, x)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tfh()), (LAT.fromT(U32, t0), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tfh()))), LA.get_pair(U32, LAT.fromT(U32, t0), P.at_tfh())) :
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.tab_put.t(P.dt.fh(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), x)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tn()), (LAT.fromT(U32, t0), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tn()))), LA.get_pair(U32, LAT.fromT(U32, t0), P.at_tn())) :
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.tab_put.t(P.dt.n(KM.m_get.fin(_), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tfh()))), x)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tcap()), (LAT.fromT(U32, t0), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tcap()))), LA.get_pair(U32, LAT.fromT(U32, t0), P.at_tcap())) :
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.tab_put.t(P.dt.cap(KM.m_get.fin(_), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tfh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tn()))), x)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), P.at_td()), (LAT.fromT(U32, t0), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_td()))), LA.get_pair(U32, LAT.fromT(U32, t0), P.at_td())) :
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.tab_put.t(P.dt.d(KM.m_get.fin(_), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tfh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tn())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tcap()))), x)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}
  dto_keeps(t0, P.dt_put(P.DT{LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tfh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tn())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tcap())), U32.to_nat(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_td())))}, x), d, j, hft, hd32, hj)

# a pair's node form put beside it (pw.tab), the heap its first
def pwt_keeps(r: P.H & U32, +f: U32, +t0: LAT.Tree<U32>, +j: U32, h: {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, r), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}) ->
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, P.PW, P.pw.tab(r, f)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}:
  match r:
    case (h2, +i):
      h

# P.put's cases, as it takes them: a number or a builtin that fits
# written in the node, nothing in the heap; anything else an entry. Each
# value named: a proof's match reduces the code's only at a constructor
def put2_k(t: List<&2, V.Val>, +op: U32, +need: U32, +a: U32, +v: V.Val, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +j: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hj: {KMd.off.words(KMd.tab_words(), d, j) == True{} : Bool}) ->
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, P.PW, P.put.two(t, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, op, need, a, v)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}:
  match t:
    case Nil{}:
      pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
    case Con{x, +u}:
      match x:
        case V.VNum{+b}:
          match u:
            case Nil{}:
              pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, V.VP2{op, need, a, b}), P.benc(op, need), t0, j, tab_keeps(t0, ta, V.VP2{op, need, a, b}, d, j, hft, hd32, hj))
            case Con{+y, +z}:
              pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VUnit{}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VLazy{+h}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VFun{+op2, +need2, +args2}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VList{+xs}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VDict{+es}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VErr{+e}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VFree{+next}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VP2{+op2, +need2, +a2, +b2}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))

def putgo_k(args: List<&2, V.Val>, +op: U32, +need: U32, +v: V.Val, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +j: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hj: {KMd.off.words(KMd.tab_words(), d, j) == True{} : Bool}) ->
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, P.PW, P.put.fun.go(args, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, op, need, v)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}:
  match args:
    case Nil{}:
      rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), j)
    case Con{x, +t}:
      match x:
        case V.VNum{+n}:
          match t:
            case Nil{}:
              rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), j)
            case Con{+y, +z}:
              put2_k(Con{y, z}, op, need, n, v, t0, ta, d, j, hft, hd32, hj)
        case V.VUnit{}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VLazy{+h}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VFun{+op2, +need2, +args2}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VList{+xs}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VDict{+es}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VErr{+e}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VFree{+next}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))
        case V.VP2{+op2, +need2, +a2, +b2}:
          pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))

def putfun_k(fits: Bool, args: List<&2, V.Val>, +op: U32, +need: U32, +v: V.Val, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +j: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hj: {KMd.off.words(KMd.tab_words(), d, j) == True{} : Bool}) ->
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, P.PW, P.put.fun(fits, args, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, op, need, v)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}:
  match fits:
    case True{}:
      putgo_k(args, op, need, v, t0, ta, d, j, hft, hd32, hj)
    case False{}:
      pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), 0, t0, j, tab_keeps(t0, ta, v, d, j, hft, hd32, hj))

def put_k(v: V.Val, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +j: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hj: {KMd.off.words(KMd.tab_words(), d, j) == True{} : Bool}) ->
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, P.PW, P.put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}:
  match v:
    case V.VNum{+n}:
      rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), j)
    case V.VFun{+op, +need, +args}:
      putfun_k(P.bfits(op, need), args, op, need, V.VFun{op, need, args}, t0, ta, d, j, hft, hd32, hj)
    case V.VP2{+op, +need, +a, +b}:
      putfun_k(P.bfits(op, need), [V.VNum{a}, V.VNum{b}], op, need, V.VP2{op, need, a, b}, t0, ta, d, j, hft, hd32, hj)
      case V.VUnit{}:
        pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, V.VUnit{}), 0, t0, j, tab_keeps(t0, ta, V.VUnit{}, d, j, hft, hd32, hj))
      case V.VLazy{+h}:
        pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, V.VLazy{h}), 0, t0, j, tab_keeps(t0, ta, V.VLazy{h}, d, j, hft, hd32, hj))
      case V.VList{+xs}:
        pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, V.VList{xs}), 0, t0, j, tab_keeps(t0, ta, V.VList{xs}, d, j, hft, hd32, hj))
      case V.VDict{+es}:
        pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, V.VDict{es}), 0, t0, j, tab_keeps(t0, ta, V.VDict{es}, d, j, hft, hd32, hj))
      case V.VErr{+e}:
        pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, V.VErr{e}), 0, t0, j, tab_keeps(t0, ta, V.VErr{e}, d, j, hft, hd32, hj))
      case V.VFree{+next}:
        pwt_keeps(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, V.VFree{next}), 0, t0, j, tab_keeps(t0, ta, V.VFree{next}, d, j, hft, hd32, hj))

def put_keeps.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +v: V.Val, +j: U32, hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hj: {KMd.off.words(KMd.tab_words(), d, j) == True{} : Bool},
    m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, P.PW, P.put(P.H{KM.MG{w}, a}, v)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t0, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  %e : {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, P.PW, P.put(P.H{KM.MG{_}, a}, v)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %ea : {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, P.PW, P.put(P.H{KM.MG{LAT.fromT(U32, t0)}, _}, v)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, _}, j)) : U32}
  %Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), j)) :
    {Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, P.PW, P.put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v)), j)) == _ : U32}
  put_k(v, t0, ta, d, j, hft, hd32, hj)

def Laws.put_keeps(w, a, d, v, j, hf, hd32, hj):
  put_keeps.go(w, a, d, v, j, hf, hd32, hj, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# an error counted writes the error count alone
def err_k(b: Bool, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +j: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hj: {KMd.off.words(KMd.err_words(), d, j) == True{} : Bool}) ->
    {Pair.snd(P.H, U32, P.rd(P.err_if(b, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}:
  match b:
    case True{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), P.at_errs()), (LAT.fromT(U32, t0), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_errs()))), LA.get_pair(U32, LAT.fromT(U32, t0), P.at_errs())) :
        {Pair.snd(P.H, U32, P.rd(P.h_err.n(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}
      Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), P.at_errs(), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_errs())) + 1 : U32))}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_errs(), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_errs())) + 1 : U32)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), rd_get(Array.set(U32, LAT.fromT(U32, t0), P.at_errs(), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_errs())) + 1 : U32)), LAT.fromT(V.Val, ta), j), LA.get_set_other(U32, LAT.fromT(U32, t0), d, P.at_errs(), j, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_errs())) + 1 : U32), hft, hd32, MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(j, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(j, d))), KMd.off.words(Nil{}, d, j), hj))))
    case False{}:
      rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), j)

def err_keeps.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +b: Bool, +j: U32, hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hj: {KMd.off.words(KMd.err_words(), d, j) == True{} : Bool},
    m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
    {Pair.snd(P.H, U32, P.rd(P.err_if(b, P.H{KM.MG{w}, a}), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t0, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  %e : {Pair.snd(P.H, U32, P.rd(P.err_if(b, P.H{KM.MG{_}, a}), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %ea : {Pair.snd(P.H, U32, P.rd(P.err_if(b, P.H{KM.MG{LAT.fromT(U32, t0)}, _}), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, _}, j)) : U32}
  %Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), j)) :
    {Pair.snd(P.H, U32, P.rd(P.err_if(b, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}), j)) == _ : U32}
  err_k(b, t0, ta, d, j, hft, hd32, hj)

def Laws.err_keeps(w, a, d, b, j, hf, hd32, hj):
  err_keeps.go(w, a, d, b, j, hf, hd32, hj, LAT.mirror(U32, w), LAT.mirror(V.Val, a))
