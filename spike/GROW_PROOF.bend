# The store's growth's laws (spike/GROW_LAWS.bend). The arrays are taken
# erased, with mirrors (LAT.Mirror), so that a term names each once: the
# count matched first, then the mirrors destructured in the step (a match
# after a local statement is refused). Indices are U32 and their order
# Nat's; an index one on, i + 1, is 1 + i below 2^32, 2^32 kept abstract
# (as glam/proofgen/align/ALIGN.bend's add_mod4.k keeps it).

import Base
import ./GROW_LAWS.bend as Laws
import ./kmem_grow.bend as KM
import ./grow_model.bend as GM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/LAWS.bend as LA
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/PROOF.bend as LAP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD
import 0x96ab58f86121cb4f3fb48b3c8a045989/LAWS.bend as WL
import 0x96ab58f86121cb4f3fb48b3c8a045989/PROOF.bend as WLP
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MN
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB

# Nat's order, as the copy's indices need it
def lt_le_ne(a: Nat, b: Nat, +hle: {Nat.is_le(a, b) == True{} : Bool}, +hne: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, MB.false_ne_true()(Equal.sym(Bool, True{}, False{}, hne)))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, MB.false_ne_true()(hle))
    case 1n+p 1n+q:
      lt_le_ne(p, q, hle, hne)

def ne_lt(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, MB.false_ne_true()(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ne_lt(p, q, h)

def ne_flip(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(b, a), Nat.is_eq(a, b), MN.is_eq_comm(b, a)) : {_ == False{} : Bool}
  h

# a below a + 1 + p
def lt_add(+a: Nat, +p: Nat) -> {Nat.is_lt(a, Nat.add(a, 1n+p)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(a, 1n+p), 1n+Nat.add(a, p), MN.add_succ(a, p)) : {Nat.is_lt(a, _) == True{} : Bool}
  MN.lt_succ_of_le(a, Nat.add(a, p), MN.le_add_right(a, p))

# i + 1 one past i where i is below some word c: no wrap at 2^32, which
# c's own bound gives (WL.to_nat_lt), so that 2^32 is never compared with
# a power the checker would expand
def tn1.k(+m: Nat, +e: {Nat.pow(2n, 32n) == m : Nat}, +i: U32, +c: U32, +h: {Nat.is_lt(U32.to_nat(i), U32.to_nat(c)) == True{} : Bool}) -> {U32.to_nat(U32.add(i, 1)) == 1n+U32.to_nat(i) : Nat}:
  +e1 = ME.subst(Nat, q => {U32.to_nat(U32.add(i, 1)) == Nat.mod(Nat.add(U32.to_nat(i), U32.to_nat(1)), q) : Nat}, Nat.pow(2n, 32n), m, e, WL.to_nat_add(i, 1))
  +e1b = Equal.trans(Nat, Nat.add(U32.to_nat(i), U32.to_nat(1)), Nat.add(U32.to_nat(i), 1n), 1n+U32.to_nat(i), {==}, MN.add_comm(U32.to_nat(i), 1n))
  +hcm = ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(c), q) == True{} : Bool}, Nat.pow(2n, 32n), m, e, WL.to_nat_lt(c))
  +hl = MN.lt_of_le_of_lt(1n+U32.to_nat(i), U32.to_nat(c), m, MN.succ_le_of_lt(U32.to_nat(i), U32.to_nat(c), h), hcm)
  Equal.trans(Nat, U32.to_nat(U32.add(i, 1)), Nat.mod(Nat.add(U32.to_nat(i), U32.to_nat(1)), m), 1n+U32.to_nat(i), e1,
    Equal.trans(Nat, Nat.mod(Nat.add(U32.to_nat(i), U32.to_nat(1)), m), Nat.mod(1n+U32.to_nat(i), m), 1n+U32.to_nat(i), Equal.cong(Nat, Nat, z => Nat.mod(z, m), Nat.add(U32.to_nat(i), U32.to_nat(1)), 1n+U32.to_nat(i), e1b),
      WL.nat_mod_small(1n+U32.to_nat(i), m, hl)))

def tn1(+i: U32, +c: U32, +h: {Nat.is_lt(U32.to_nat(i), U32.to_nat(c)) == True{} : Bool}) -> {U32.to_nat((i + 1 : U32)) == 1n+U32.to_nat(i) : Nat}:
  tn1.k(Nat.pow(2n, 32n), {==}, i, c, h)

# two indices apart as numbers below 2^D are apart as slots
def sl_ne(+i: U32, +j: U32, +D: Nat, +hi: {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, D)) == True{} : Bool}, +hj: {Nat.is_lt(U32.to_nat(j), Nat.pow(2n, D)) == True{} : Bool}, +h: {Nat.is_eq(U32.to_nat(i), U32.to_nat(j)) == False{} : Bool}) ->
  {Nat.is_eq(AD.slot(i, D), AD.slot(j, D)) == False{} : Bool}:
  %Equal.sym(Nat, AD.slot(i, D), U32.to_nat(i), LA.slot_small(i, D, hi)) : {Nat.is_eq(_, AD.slot(j, D)) == False{} : Bool}
  %Equal.sym(Nat, AD.slot(j, D), U32.to_nat(j), LA.slot_small(j, D, hj)) : {Nat.is_eq(U32.to_nat(i), _) == False{} : Bool}
  h

# a copy keeps its destination full
def cfu(k: Nat, +i: U32, -src: Array<U32>, -dst: Array<U32>, +D: Nat, +hfd: {AD.full(U32, dst, D) == True{} : Bool}, ms: LAT.Mirror(U32, src), md: LAT.Mirror(U32, dst)) ->
  {AD.full(U32, KM.copy(k, i, KM.CP{src, dst}), D) == True{} : Bool}:
  match k:
    case 0n:
      hfd
    case 1n+p:
      (+ts, +es) = ms
      (+td, +ed) = md
      +hfd1 = LAP.full_t(U32, dst, td, D, ed, hfd)
      %es : {AD.full(U32, KM.copy(1n+p, i, KM.CP{_, dst}), D) == True{} : Bool}
      %ed : {AD.full(U32, KM.copy(1n+p, i, KM.CP{LAT.fromT(U32, ts), _}), D) == True{} : Bool}
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, ts), i), (LAT.fromT(U32, ts), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))), LA.get_pair(U32, LAT.fromT(U32, ts), i)) : {AD.full(U32, KM.copy(p, (i + 1 : U32), KM.cp.step(_, LAT.fromT(U32, td), i)), D) == True{} : Bool}
      cfu(p, (i + 1 : U32), LAT.fromT(U32, ts), Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))), D, LA.set_full(U32, LAT.fromT(U32, td), D, i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)), hfd1), LAT.mirror(U32, LAT.fromT(U32, ts)), LAT.mirror(U32, Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)))))

def Laws.copy_full(k, i, src, dst, dd, hfd):
  cfu(k, i, src, dst, dd, hfd, LAT.mirror(U32, src), LAT.mirror(U32, dst))

# an index below the copy's keeps the destination's word
def ca.lo(+k: Nat, +i: U32, -src: Array<U32>, -dst: Array<U32>, +j: U32, +D: Nat, +c: U32, +hfd: {AD.full(U32, dst, D) == True{} : Bool}, +hD: {Nat.is_lt(D, 32n) == True{} : Bool}, +hcD: {Nat.is_le(U32.to_nat(c), Nat.pow(2n, D)) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(U32.to_nat(i), k), U32.to_nat(c)) == True{} : Bool},
  +hjD: {Nat.is_lt(U32.to_nat(j), Nat.pow(2n, D)) == True{} : Bool}, +hlt: {Nat.is_lt(U32.to_nat(j), U32.to_nat(i)) == True{} : Bool}, ms: LAT.Mirror(U32, src), md: LAT.Mirror(U32, dst)) -> {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(k, i, KM.CP{src, dst}), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, dst, j)) : U32}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      (+ts, +es) = ms
      (+td, +ed) = md
      +hfd1 = LAP.full_t(U32, dst, td, D, ed, hfd)
      %es : {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(1n+p, i, KM.CP{_, dst}), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, dst, j)) : U32}
      %ed : {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(1n+p, i, KM.CP{LAT.fromT(U32, ts), _}), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, _, j)) : U32}
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, ts), i), (LAT.fromT(U32, ts), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))), LA.get_pair(U32, LAT.fromT(U32, ts), i)) : {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(p, (i + 1 : U32), KM.cp.step(_, LAT.fromT(U32, td), i)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, td), j)) : U32}
      +hiD = MN.lt_of_lt_of_le(U32.to_nat(i), Nat.add(U32.to_nat(i), 1n+p), U32.to_nat(c), lt_add(U32.to_nat(i), p), hr)
      +e1 = tn1(i, c, hiD)
      +hi2 = MN.lt_of_lt_of_le(U32.to_nat(i), U32.to_nat(c), Nat.pow(2n, D), hiD, hcD)
      +hr1 = ME.subst(Nat, q => {Nat.is_le(Nat.add(q, p), U32.to_nat(c)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), ME.subst(Nat, q => {Nat.is_le(q, U32.to_nat(c)) == True{} : Bool}, Nat.add(U32.to_nat(i), 1n+p), 1n+Nat.add(U32.to_nat(i), p), MN.add_succ(U32.to_nat(i), p), hr))
      +hlt1 = ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(j), q) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), MN.lt_of_lt_of_le(U32.to_nat(j), U32.to_nat(i), 1n+U32.to_nat(i), hlt, MN.le_succ(U32.to_nat(i))))
      +ih = ca.lo(p, (i + 1 : U32), LAT.fromT(U32, ts), Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))), j, D, c, LA.set_full(U32, LAT.fromT(U32, td), D, i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)), hfd1), hD, hcD, hr1, hjD, hlt1, LAT.mirror(U32, LAT.fromT(U32, ts)), LAT.mirror(U32, Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)))))
      Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(p, (i + 1 : U32), KM.CP{LAT.fromT(U32, ts), Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)))}), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, td), j)), ih,
        LA.get_set_other(U32, LAT.fromT(U32, td), D, i, j, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)), hfd1, hD, sl_ne(i, j, D, hi2, hjD, ne_flip(U32.to_nat(j), U32.to_nat(i), ne_lt(U32.to_nat(j), U32.to_nat(i), hlt)))))

# an index past the copy's keeps the destination's word
def ca.hi(+k: Nat, +i: U32, -src: Array<U32>, -dst: Array<U32>, +j: U32, +D: Nat, +c: U32, +hfd: {AD.full(U32, dst, D) == True{} : Bool}, +hD: {Nat.is_lt(D, 32n) == True{} : Bool}, +hcD: {Nat.is_le(U32.to_nat(c), Nat.pow(2n, D)) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(U32.to_nat(i), k), U32.to_nat(c)) == True{} : Bool},
  +hjD: {Nat.is_lt(U32.to_nat(j), Nat.pow(2n, D)) == True{} : Bool}, +hge: {Nat.is_le(Nat.add(U32.to_nat(i), k), U32.to_nat(j)) == True{} : Bool}, ms: LAT.Mirror(U32, src), md: LAT.Mirror(U32, dst)) -> {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(k, i, KM.CP{src, dst}), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, dst, j)) : U32}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      (+ts, +es) = ms
      (+td, +ed) = md
      +hfd1 = LAP.full_t(U32, dst, td, D, ed, hfd)
      %es : {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(1n+p, i, KM.CP{_, dst}), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, dst, j)) : U32}
      %ed : {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(1n+p, i, KM.CP{LAT.fromT(U32, ts), _}), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, _, j)) : U32}
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, ts), i), (LAT.fromT(U32, ts), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))), LA.get_pair(U32, LAT.fromT(U32, ts), i)) : {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(p, (i + 1 : U32), KM.cp.step(_, LAT.fromT(U32, td), i)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, td), j)) : U32}
      +hiD = MN.lt_of_lt_of_le(U32.to_nat(i), Nat.add(U32.to_nat(i), 1n+p), U32.to_nat(c), lt_add(U32.to_nat(i), p), hr)
      +e1 = tn1(i, c, hiD)
      +hi2 = MN.lt_of_lt_of_le(U32.to_nat(i), U32.to_nat(c), Nat.pow(2n, D), hiD, hcD)
      +hr1 = ME.subst(Nat, q => {Nat.is_le(Nat.add(q, p), U32.to_nat(c)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), ME.subst(Nat, q => {Nat.is_le(q, U32.to_nat(c)) == True{} : Bool}, Nat.add(U32.to_nat(i), 1n+p), 1n+Nat.add(U32.to_nat(i), p), MN.add_succ(U32.to_nat(i), p), hr))
      +hge1 = ME.subst(Nat, q => {Nat.is_le(Nat.add(q, p), U32.to_nat(j)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), ME.subst(Nat, q => {Nat.is_le(q, U32.to_nat(j)) == True{} : Bool}, Nat.add(U32.to_nat(i), 1n+p), 1n+Nat.add(U32.to_nat(i), p), MN.add_succ(U32.to_nat(i), p), hge))
      +hij = MN.lt_of_lt_of_le(U32.to_nat(i), Nat.add(U32.to_nat(i), 1n+p), U32.to_nat(j), lt_add(U32.to_nat(i), p), hge)
      +ih = ca.hi(p, (i + 1 : U32), LAT.fromT(U32, ts), Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))), j, D, c, LA.set_full(U32, LAT.fromT(U32, td), D, i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)), hfd1), hD, hcD, hr1, hjD, hge1, LAT.mirror(U32, LAT.fromT(U32, ts)), LAT.mirror(U32, Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)))))
      Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(p, (i + 1 : U32), KM.CP{LAT.fromT(U32, ts), Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)))}), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, td), j)), ih,
        LA.get_set_other(U32, LAT.fromT(U32, td), D, i, j, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)), hfd1, hD, sl_ne(i, j, D, hi2, hjD, ne_lt(U32.to_nat(i), U32.to_nat(j), hij))))

# within the copy's indices: the source's word. j the index taken now, or
# one taken later
def ca.s(+e: Bool, +i: U32, +j: U32, +ts: LAT.Tree<U32>, +td: LAT.Tree<U32>, +p: Nat, +D: Nat, +c: U32, +he: {Nat.is_eq(U32.to_nat(i), U32.to_nat(j)) == e : Bool},
  +hfd1: {AD.full(U32, LAT.fromT(U32, td), D) == True{} : Bool}, +hD: {Nat.is_lt(D, 32n) == True{} : Bool}, +hcD: {Nat.is_le(U32.to_nat(c), Nat.pow(2n, D)) == True{} : Bool},
  +hiD: {Nat.is_lt(U32.to_nat(i), U32.to_nat(c)) == True{} : Bool}, +e1: {U32.to_nat((i + 1 : U32)) == 1n+U32.to_nat(i) : Nat}, +hr1: {Nat.is_le(Nat.add(U32.to_nat((i + 1 : U32)), p), U32.to_nat(c)) == True{} : Bool}, +hlo: {Nat.is_le(U32.to_nat(i), U32.to_nat(j)) == True{} : Bool}, +hhi: {Nat.is_lt(U32.to_nat(j), Nat.add(U32.to_nat(i), 1n+p)) == True{} : Bool},
  ih: {Nat.is_le(U32.to_nat((i + 1 : U32)), U32.to_nat(j)) == True{} : Bool} -> {Nat.is_lt(U32.to_nat(j), Nat.add(U32.to_nat((i + 1 : U32)), p)) == True{} : Bool} -> {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(p, (i + 1 : U32), KM.CP{LAT.fromT(U32, ts), Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)))}), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), j)) : U32}) ->
  {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(p, (i + 1 : U32), KM.CP{LAT.fromT(U32, ts), Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)))}), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), j)) : U32}:
  match e:
    case True{}:
      +eij = WL.to_nat_inj(i, j, MN.eq_of_is_eq(U32.to_nat(i), U32.to_nat(j), he))
      +hi2 = MN.lt_of_lt_of_le(U32.to_nat(i), U32.to_nat(c), Nat.pow(2n, D), hiD, hcD)
      +hlt = ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(i), q) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), MN.lt_succ_of_le(U32.to_nat(i), U32.to_nat(i), MN.le_refl(U32.to_nat(i))))
      +hat = Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(p, (i + 1 : U32), KM.CP{LAT.fromT(U32, ts), Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)))}), i)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))), i)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)),
        ca.lo(p, (i + 1 : U32), LAT.fromT(U32, ts), Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))), i, D, c, LA.set_full(U32, LAT.fromT(U32, td), D, i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)), hfd1), hD, hcD, hr1, hi2, hlt, LAT.mirror(U32, LAT.fromT(U32, ts)), LAT.mirror(U32, Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))))),
        LA.get_set_same(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))))
      ME.subst(U32, z => {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(p, (i + 1 : U32), KM.CP{LAT.fromT(U32, ts), Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)))}), z)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), z)) : U32}, i, j, eij, hat)
    case False{}:
      +hlt = lt_le_ne(U32.to_nat(i), U32.to_nat(j), hlo, he)
      +hlo2 = ME.subst(Nat, q => {Nat.is_le(q, U32.to_nat(j)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), MN.succ_le_of_lt(U32.to_nat(i), U32.to_nat(j), hlt))
      +hhi2 = ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(j), Nat.add(q, p)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(j), q) == True{} : Bool}, Nat.add(U32.to_nat(i), 1n+p), 1n+Nat.add(U32.to_nat(i), p), MN.add_succ(U32.to_nat(i), p), hhi))
      ih(hlo2, hhi2)

def ca.in(+k: Nat, +i: U32, -src: Array<U32>, -dst: Array<U32>, +j: U32, +D: Nat, +c: U32, +hfd: {AD.full(U32, dst, D) == True{} : Bool}, +hD: {Nat.is_lt(D, 32n) == True{} : Bool}, +hcD: {Nat.is_le(U32.to_nat(c), Nat.pow(2n, D)) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(U32.to_nat(i), k), U32.to_nat(c)) == True{} : Bool},
  +hlo: {Nat.is_le(U32.to_nat(i), U32.to_nat(j)) == True{} : Bool}, +hhi: {Nat.is_lt(U32.to_nat(j), Nat.add(U32.to_nat(i), k)) == True{} : Bool}, ms: LAT.Mirror(U32, src), md: LAT.Mirror(U32, dst)) -> {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(k, i, KM.CP{src, dst}), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, src, j)) : U32}:
  match k:
    case 0n:
      +h0 = ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(j), q) == True{} : Bool}, Nat.add(U32.to_nat(i), 0n), U32.to_nat(i), MN.add_zero(U32.to_nat(i)), hhi)
      Empty.absurd({Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(0n, i, KM.CP{src, dst}), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, src, j)) : U32}, MN.lt_irrefl(U32.to_nat(i))(MN.lt_of_le_of_lt(U32.to_nat(i), U32.to_nat(j), U32.to_nat(i), hlo, h0)))
    case 1n+p:
      (+ts, +es) = ms
      (+td, +ed) = md
      +hfd1 = LAP.full_t(U32, dst, td, D, ed, hfd)
      %es : {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(1n+p, i, KM.CP{_, dst}), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, _, j)) : U32}
      %ed : {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(1n+p, i, KM.CP{LAT.fromT(U32, ts), _}), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), j)) : U32}
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, ts), i), (LAT.fromT(U32, ts), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))), LA.get_pair(U32, LAT.fromT(U32, ts), i)) : {Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(p, (i + 1 : U32), KM.cp.step(_, LAT.fromT(U32, td), i)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), j)) : U32}
      +hiD = MN.lt_of_lt_of_le(U32.to_nat(i), Nat.add(U32.to_nat(i), 1n+p), U32.to_nat(c), lt_add(U32.to_nat(i), p), hr)
      +e1 = tn1(i, c, hiD)
      +hi2 = MN.lt_of_lt_of_le(U32.to_nat(i), U32.to_nat(c), Nat.pow(2n, D), hiD, hcD)
      +hr1 = ME.subst(Nat, q => {Nat.is_le(Nat.add(q, p), U32.to_nat(c)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), ME.subst(Nat, q => {Nat.is_le(q, U32.to_nat(c)) == True{} : Bool}, Nat.add(U32.to_nat(i), 1n+p), 1n+Nat.add(U32.to_nat(i), p), MN.add_succ(U32.to_nat(i), p), hr))
      ca.s(Nat.is_eq(U32.to_nat(i), U32.to_nat(j)), i, j, ts, td, p, D, c, {==}, hfd1, hD, hcD, hiD, e1, hr1, hlo, hhi,
        h1 => h2 => ca.in(p, (i + 1 : U32), LAT.fromT(U32, ts), Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))), j, D, c, LA.set_full(U32, LAT.fromT(U32, td), D, i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i)), hfd1), hD, hcD, hr1, h1, h2, LAT.mirror(U32, LAT.fromT(U32, ts)), LAT.mirror(U32, Array.set(U32, LAT.fromT(U32, td), i, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ts), i))))))

# 0 below or at every number
def le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# the grown store as a copy into one level deeper: the depth's premise
# and Nat.add(d, 1n) as 1n+d
def gr.eq(-w: Array<U32>, +d: Nat, +cap: U32, +hdp: {KM.depth(32n, cap, 0n) == d : Nat}) -> {GM.arr(KM.grow(KM.MG{w}, cap)) == KM.copy(U32.to_nat(cap), 0, KM.CP{w, Array.new(U32, 1n+d, 0)}) : Array<U32>}:
  %Equal.sym(Nat, KM.depth(32n, cap, 0n), d, hdp) : {KM.copy(U32.to_nat(cap), 0, KM.CP{w, [0 : U32^Nat.add(_, 1n)]}) == KM.copy(U32.to_nat(cap), 0, KM.CP{w, Array.new(U32, 1n+d, 0)}) : Array<U32>}
  %Equal.sym(Nat, Nat.add(d, 1n), Nat.add(1n, d), MN.add_comm(d, 1n)) : {KM.copy(U32.to_nat(cap), 0, KM.CP{w, [0 : U32^_]}) == KM.copy(U32.to_nat(cap), 0, KM.CP{w, Array.new(U32, 1n+d, 0)}) : Array<U32>}
  {==}

def Laws.grow_full(w, d, cap, hdp):
  %Equal.sym(Array<U32>, GM.arr(KM.grow(KM.MG{w}, cap)), KM.copy(U32.to_nat(cap), 0, KM.CP{w, Array.new(U32, 1n+d, 0)}), gr.eq(w, d, cap, hdp)) : {AD.full(U32, _, 1n+d) == True{} : Bool}
  Laws.copy_full(U32.to_nat(cap), 0, w, Array.new(U32, 1n+d, 0), 1n+d, LA.new_full(U32, 1n+d, 0))

def Laws.grow_old(w, d, cap, j, hd, hc, hdp, hj):
  %Equal.sym(Array<U32>, GM.arr(KM.grow(KM.MG{w}, cap)), KM.copy(U32.to_nat(cap), 0, KM.CP{w, Array.new(U32, 1n+d, 0)}), gr.eq(w, d, cap, hdp)) : {Pair.snd(Array<U32>, U32, Array.get(U32, _, j)) == Pair.snd(Array<U32>, U32, Array.get(U32, w, j)) : U32}
  +hcD = ME.subst(Nat, q => {Nat.is_le(q, Nat.pow(2n, 1n+d)) == True{} : Bool}, Nat.pow(2n, d), U32.to_nat(cap), Equal.sym(Nat, U32.to_nat(cap), Nat.pow(2n, d), hc),
    MN.pow_le_pow_right(1n, d, 1n+d, MN.le_succ(d)))
  +hhi = ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(j), q) == True{} : Bool}, Nat.pow(2n, d), U32.to_nat(cap), Equal.sym(Nat, U32.to_nat(cap), Nat.pow(2n, d), hc), hj)
  ca.in(U32.to_nat(cap), 0, w, Array.new(U32, 1n+d, 0), j, 1n+d, cap, LA.new_full(U32, 1n+d, 0), hd, hcD, MN.le_refl(U32.to_nat(cap)), le0(U32.to_nat(j)), hhi, LAT.mirror(U32, w), LAT.mirror(U32, Array.new(U32, 1n+d, 0)))

def Laws.grow_new(w, d, cap, j, hd, hc, hdp, hj0, hj1):
  %Equal.sym(Array<U32>, GM.arr(KM.grow(KM.MG{w}, cap)), KM.copy(U32.to_nat(cap), 0, KM.CP{w, Array.new(U32, 1n+d, 0)}), gr.eq(w, d, cap, hdp)) : {Pair.snd(Array<U32>, U32, Array.get(U32, _, j)) == 0 : U32}
  +hcD = ME.subst(Nat, q => {Nat.is_le(q, Nat.pow(2n, 1n+d)) == True{} : Bool}, Nat.pow(2n, d), U32.to_nat(cap), Equal.sym(Nat, U32.to_nat(cap), Nat.pow(2n, d), hc),
    MN.pow_le_pow_right(1n, d, 1n+d, MN.le_succ(d)))
  +hge = ME.subst(Nat, q => {Nat.is_le(q, U32.to_nat(j)) == True{} : Bool}, Nat.pow(2n, d), U32.to_nat(cap), Equal.sym(Nat, U32.to_nat(cap), Nat.pow(2n, d), hc), hj0)
  Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KM.copy(U32.to_nat(cap), 0, KM.CP{w, Array.new(U32, 1n+d, 0)}), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.new(U32, 1n+d, 0), j)), 0,
    ca.hi(U32.to_nat(cap), 0, w, Array.new(U32, 1n+d, 0), j, 1n+d, cap, LA.new_full(U32, 1n+d, 0), hd, hcD, MN.le_refl(U32.to_nat(cap)), hj1, hge, LAT.mirror(U32, w), LAT.mirror(U32, Array.new(U32, 1n+d, 0))),
    LA.get_new(U32, 1n+d, 0, j))

# a store asked for room doubles once: the three tests decided by the
# premises, in the order m_ensure, decide and ens take them
def Laws.ensure_once(m, n, cap, maxd, h1, h2, h3):
  %Equal.sym(Bool, U32.is_le(n, cap), False{}, h1) : {KM.m_ensure.go(_, m, n, cap, maxd) == (KM.grow(m, cap), (cap * 2 : U32)) : KM.M & U32}
  %Equal.sym(Bool, Nat.is_ge(KM.depth(32n, cap, 0n), maxd), False{}, h2) : {KM.ens(32n, KM.decide(False{}, _, m, cap), n, maxd) == (KM.grow(m, cap), (cap * 2 : U32)) : KM.M & U32}
  %Equal.sym(Bool, U32.is_le(n, (cap * 2 : U32)), True{}, h3) :
    {KM.ens(31n, KM.decide(_, Nat.is_ge(KM.depth(32n, (cap * 2 : U32), 0n), maxd), KM.grow(m, cap), (cap * 2 : U32)), n, maxd) == (KM.grow(m, cap), (cap * 2 : U32)) : KM.M & U32}
  {==}
