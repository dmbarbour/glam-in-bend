# The store's growth's laws (spike/GROW_LAWS.bend). The arrays are taken
# erased, with mirrors (LAT.Mirror), so that a term names each once: the
# count matched first, then the mirrors destructured in the step (a match
# after a local statement is refused). Indices are U32 and their order
# Nat's; an index one on, i + 1, is 1 + i below 2^32, 2^32 kept abstract
# (as glam/proofgen/align/ALIGN.bend's add_mod4.k keeps it).

import Base
import ./GROW_LAWS.bend as Laws
import ./kmem_grow.bend as KM
import ./kprim.bend as P
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
  ca.in(U32.to_nat(cap), 0, w, Array.new(U32, 1n+d, 0), j, 1n+d, cap, LA.new_full(U32, 1n+d, 0), hd, hcD, MN.le_refl(U32.to_nat(cap)), MN.zero_le(U32.to_nat(j)), hhi, LAT.mirror(U32, w), LAT.mirror(U32, Array.new(U32, 1n+d, 0)))

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

# x + 1 below x + 2 + q
def lt2(+x: Nat, +q: Nat) -> {Nat.is_lt(1n+x, Nat.add(x, 2n+q)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(x, 2n+q), 1n+Nat.add(x, 1n+q), MN.add_succ(x, 1n+q)) : {Nat.is_lt(1n+x, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(x, 1n+q), 1n+Nat.add(x, q), MN.add_succ(x, q)) : {Nat.is_lt(1n+x, 1n+_) == True{} : Bool}
  MN.lt_succ_of_le(x, Nat.add(x, q), MN.le_add_right(x, q))

# x + (4 + q) as 4 + (x + q)
def add4(+x: Nat, +q: Nat) -> {Nat.add(x, 4n+q) == 4n+Nat.add(x, q) : Nat}:
  %Equal.sym(Nat, Nat.add(x, 1n+3n+q), 1n+Nat.add(x, 3n+q), MN.add_succ(x, 3n+q)) : {_ == 4n+Nat.add(x, q) : Nat}
  %Equal.sym(Nat, Nat.add(x, 1n+2n+q), 1n+Nat.add(x, 2n+q), MN.add_succ(x, 2n+q)) : {1n+_ == 4n+Nat.add(x, q) : Nat}
  %Equal.sym(Nat, Nat.add(x, 1n+1n+q), 1n+Nat.add(x, 1n+q), MN.add_succ(x, 1n+q)) : {2n+_ == 4n+Nat.add(x, q) : Nat}
  %Equal.sym(Nat, Nat.add(x, 1n+q), 1n+Nat.add(x, q), MN.add_succ(x, q)) : {3n+_ == 4n+Nat.add(x, q) : Nat}
  {==}

# n at most 4n
def le4(+n: Nat) -> {Nat.is_le(n, Nat.mul(n, 4n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      MN.le_trans(p, Nat.mul(p, 4n), 3n+Nat.mul(p, 4n), le4(p), MN.le_add_left(Nat.mul(p, 4n), 3n))

# node i's word 1, 4i + 1 as a number below the bound c; 2^32 abstract
# as m, put back only for the shift's premise
def w1n.k(+m: Nat, +e: {Nat.pow(2n, 32n) == m : Nat}, +i: U32, +c: U32, +h: {Nat.is_lt(Nat.mul(U32.to_nat(i), 4n), U32.to_nat(c)) == True{} : Bool}) -> {U32.to_nat(((i << 2n : U32) + 1 : U32)) == 1n+Nat.mul(U32.to_nat(i), 4n) : Nat}:
  +hp = ME.subst(Nat, q => {Nat.is_lt(q, U32.to_nat(c)) == True{} : Bool}, Nat.mul(U32.to_nat(i), 4n), Nat.mul(U32.to_nat(i), Nat.pow(2n, 2n)), {==}, h)
  +hcm = ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(c), q) == True{} : Bool}, Nat.pow(2n, 32n), m, e, WL.to_nat_lt(c))
  +hfm = MN.lt_of_lt_of_le(Nat.mul(U32.to_nat(i), Nat.pow(2n, 2n)), U32.to_nat(c), m, hp, MN.le_of_lt(U32.to_nat(c), m, hcm))
  +hf = ME.subst(Nat, q => {Nat.is_lt(Nat.mul(U32.to_nat(i), Nat.pow(2n, 2n)), q) == True{} : Bool}, m, Nat.pow(2n, 32n), Equal.sym(Nat, Nat.pow(2n, 32n), m, e), hfm)
  +es = WL.to_nat_shln_fits(i, 2n, hf)
  +hs = ME.subst(Nat, q => {Nat.is_lt(q, U32.to_nat(c)) == True{} : Bool}, Nat.mul(U32.to_nat(i), Nat.pow(2n, 2n)), U32.to_nat(U32.shln(i, 2n)), Equal.sym(Nat, U32.to_nat(U32.shln(i, 2n)), Nat.mul(U32.to_nat(i), Nat.pow(2n, 2n)), es), hp)
  Equal.trans(Nat, U32.to_nat(((i << 2n : U32) + 1 : U32)), 1n+U32.to_nat(U32.shln(i, 2n)), 1n+Nat.mul(U32.to_nat(i), 4n), tn1(U32.shln(i, 2n), c, hs), Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(U32.shln(i, 2n)), Nat.mul(U32.to_nat(i), 4n), es))

def w1n(+i: U32, +c: U32, +h: {Nat.is_lt(Nat.mul(U32.to_nat(i), 4n), U32.to_nat(c)) == True{} : Bool}) -> {U32.to_nat(((i << 2n : U32) + 1 : U32)) == 1n+Nat.mul(U32.to_nat(i), 4n) : Nat}:
  w1n.k(Nat.pow(2n, 32n), {==}, i, c, h)

def tb(+k: Nat, +i: U32, +to: U32, -a: Array<U32>, +j: U32, +D: Nat, +c: U32, +hf: {AD.full(U32, a, D) == True{} : Bool}, +hD: {Nat.is_lt(D, 32n) == True{} : Bool},
  +hc: {Nat.is_le(Nat.add(Nat.mul(U32.to_nat(i), 4n), Nat.mul(k, 4n)), U32.to_nat(c)) == True{} : Bool}, +hcD: {Nat.is_le(U32.to_nat(c), Nat.pow(2n, D)) == True{} : Bool}, +hj: {Nat.is_lt(U32.to_nat(j), Nat.mul(U32.to_nat(i), 4n)) == True{} : Bool}, ma: LAT.Mirror(U32, a)) ->
  {Pair.snd(Array<U32>, U32, Array.get(U32, GM.arr(P.thread(k, KM.MG{a}, i, to)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, a, j)) : U32}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      (+ta, +ea) = ma
      +hfa = LAP.full_t(U32, a, ta, D, ea, hf)
      %ea : {Pair.snd(Array<U32>, U32, Array.get(U32, GM.arr(P.thread(1n+p, KM.MG{_}, i, to)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, _, j)) : U32}
      +hW = MN.lt_of_lt_of_le(1n+Nat.mul(U32.to_nat(i), 4n), Nat.add(Nat.mul(U32.to_nat(i), 4n), 4n+Nat.mul(p, 4n)), U32.to_nat(c), lt2(Nat.mul(U32.to_nat(i), 4n), 2n+Nat.mul(p, 4n)), hc)
      +hMC = MN.lt_of_lt_of_le(Nat.mul(U32.to_nat(i), 4n), 1n+Nat.mul(U32.to_nat(i), 4n), U32.to_nat(c), MN.lt_succ_of_le(Nat.mul(U32.to_nat(i), 4n), Nat.mul(U32.to_nat(i), 4n), MN.le_refl(Nat.mul(U32.to_nat(i), 4n))), MN.le_of_lt(1n+Nat.mul(U32.to_nat(i), 4n), U32.to_nat(c), hW))
      +ew = w1n(i, c, hMC)
      +hWD = ME.subst(Nat, q => {Nat.is_lt(q, Nat.pow(2n, D)) == True{} : Bool}, 1n+Nat.mul(U32.to_nat(i), 4n), U32.to_nat(((i << 2n : U32) + 1 : U32)), Equal.sym(Nat, U32.to_nat(((i << 2n : U32) + 1 : U32)), 1n+Nat.mul(U32.to_nat(i), 4n), ew), MN.lt_of_lt_of_le(1n+Nat.mul(U32.to_nat(i), 4n), U32.to_nat(c), Nat.pow(2n, D), hW, hcD))
      +hjD = MN.lt_of_lt_of_le(U32.to_nat(j), U32.to_nat(c), Nat.pow(2n, D), MN.lt_of_lt_of_le(U32.to_nat(j), Nat.mul(U32.to_nat(i), 4n), U32.to_nat(c), hj, MN.le_of_lt(Nat.mul(U32.to_nat(i), 4n), U32.to_nat(c), hMC)), hcD)
      +hne = ME.subst(Nat, q => {Nat.is_eq(q, U32.to_nat(j)) == False{} : Bool}, 1n+Nat.mul(U32.to_nat(i), 4n), U32.to_nat(((i << 2n : U32) + 1 : U32)), Equal.sym(Nat, U32.to_nat(((i << 2n : U32) + 1 : U32)), 1n+Nat.mul(U32.to_nat(i), 4n), ew),
        ne_flip(U32.to_nat(j), 1n+Nat.mul(U32.to_nat(i), 4n), ne_lt(U32.to_nat(j), 1n+Nat.mul(U32.to_nat(i), 4n), MN.lt_of_lt_of_le(U32.to_nat(j), Nat.mul(U32.to_nat(i), 4n), 1n+Nat.mul(U32.to_nat(i), 4n), hj, MN.le_succ(Nat.mul(U32.to_nat(i), 4n))))))
      +hiC = MN.lt_of_le_of_lt(U32.to_nat(i), Nat.mul(U32.to_nat(i), 4n), U32.to_nat(c), le4(U32.to_nat(i)), hMC)
      +e1 = tn1(i, c, hiC)
      +hc1 = ME.subst(Nat, q => {Nat.is_le(Nat.add(Nat.mul(q, 4n), Nat.mul(p, 4n)), U32.to_nat(c)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1),
        ME.subst(Nat, q => {Nat.is_le(q, U32.to_nat(c)) == True{} : Bool}, Nat.add(Nat.mul(U32.to_nat(i), 4n), 4n+Nat.mul(p, 4n)), 4n+Nat.add(Nat.mul(U32.to_nat(i), 4n), Nat.mul(p, 4n)), add4(Nat.mul(U32.to_nat(i), 4n), Nat.mul(p, 4n)), hc))
      +hj1 = ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(j), Nat.mul(q, 4n)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1),
        MN.lt_of_lt_of_le(U32.to_nat(j), Nat.mul(U32.to_nat(i), 4n), 4n+Nat.mul(U32.to_nat(i), 4n), hj, MN.le_add_left(Nat.mul(U32.to_nat(i), 4n), 4n)))
      +ih = tb(p, (i + 1 : U32), to, Array.set(U32, LAT.fromT(U32, ta), ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32))), j, D, c, LA.set_full(U32, LAT.fromT(U32, ta), D, ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32)), hfa), hD, hc1, hcD, hj1, LAT.mirror(U32, Array.set(U32, LAT.fromT(U32, ta), ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32)))))
      Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, GM.arr(P.thread(p, KM.MG{Array.set(U32, LAT.fromT(U32, ta), ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32)))}, (i + 1 : U32), to)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, ta), ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, ta), j)), ih,
        LA.get_set_other(U32, LAT.fromT(U32, ta), D, ((i << 2n : U32) + 1 : U32), j, P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32)), hfa, hD, sl_ne(((i << 2n : U32) + 1 : U32), j, D, hWD, hjD, hne)))

def Laws.thread_below(k, i, to, a, j, D, c, hf, hD, hc, hcD, hj):
  tb(k, i, to, a, j, D, c, hf, hD, hc, hcD, hj, LAT.mirror(U32, a))

# the node just written, or one further on: n as i, its word written now
# and kept by the writes after (tb), or past it, by the induction
def tl.s(+e: Bool, +i: U32, +to: U32, +n: U32, +ta: LAT.Tree<U32>, +p: Nat, +D: Nat, +c: U32, +he: {Nat.is_eq(U32.to_nat(i), U32.to_nat(n)) == e : Bool},
  +hfa: {AD.full(U32, LAT.fromT(U32, ta), D) == True{} : Bool}, +hD: {Nat.is_lt(D, 32n) == True{} : Bool}, +hcD: {Nat.is_le(U32.to_nat(c), Nat.pow(2n, D)) == True{} : Bool},
  +hc1: {Nat.is_le(Nat.add(Nat.mul(U32.to_nat((i + 1 : U32)), 4n), Nat.mul(p, 4n)), U32.to_nat(c)) == True{} : Bool}, +e1: {U32.to_nat((i + 1 : U32)) == 1n+U32.to_nat(i) : Nat}, +ew: {U32.to_nat(((i << 2n : U32) + 1 : U32)) == 1n+Nat.mul(U32.to_nat(i), 4n) : Nat},
  +hlo: {Nat.is_le(U32.to_nat(i), U32.to_nat(n)) == True{} : Bool}, +hhi: {Nat.is_lt(U32.to_nat(n), Nat.add(U32.to_nat(i), 1n+p)) == True{} : Bool},
  ih: {Nat.is_le(U32.to_nat((i + 1 : U32)), U32.to_nat(n)) == True{} : Bool} -> {Nat.is_lt(U32.to_nat(n), Nat.add(U32.to_nat((i + 1 : U32)), p)) == True{} : Bool} -> {Pair.snd(Array<U32>, U32, Array.get(U32, GM.arr(P.thread(p, KM.MG{Array.set(U32, LAT.fromT(U32, ta), ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32)))}, (i + 1 : U32), to)), ((n << 2n : U32) + 1 : U32))) == P.link_of.go(U32.is_lt((n + 1 : U32), to), (n + 1 : U32)) : U32}) ->
  {Pair.snd(Array<U32>, U32, Array.get(U32, GM.arr(P.thread(p, KM.MG{Array.set(U32, LAT.fromT(U32, ta), ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32)))}, (i + 1 : U32), to)), ((n << 2n : U32) + 1 : U32))) == P.link_of.go(U32.is_lt((n + 1 : U32), to), (n + 1 : U32)) : U32}:
  match e:
    case True{}:
      +ein = WL.to_nat_inj(i, n, MN.eq_of_is_eq(U32.to_nat(i), U32.to_nat(n), he))
      +hj0 = MN.lt_succ_of_le(1n+Nat.mul(U32.to_nat(i), 4n), 3n+Nat.mul(U32.to_nat(i), 4n), MN.le_add_left(Nat.mul(U32.to_nat(i), 4n), 2n))
      +hj1 = ME.subst(Nat, q => {Nat.is_lt(q, Nat.mul(1n+U32.to_nat(i), 4n)) == True{} : Bool}, 1n+Nat.mul(U32.to_nat(i), 4n), U32.to_nat(((i << 2n : U32) + 1 : U32)), Equal.sym(Nat, U32.to_nat(((i << 2n : U32) + 1 : U32)), 1n+Nat.mul(U32.to_nat(i), 4n), ew), hj0)
      +hjW = ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(((i << 2n : U32) + 1 : U32)), Nat.mul(q, 4n)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), hj1)
      +hat = Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, GM.arr(P.thread(p, KM.MG{Array.set(U32, LAT.fromT(U32, ta), ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32)))}, (i + 1 : U32), to)), ((i << 2n : U32) + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, ta), ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32))), ((i << 2n : U32) + 1 : U32))), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32)),
        tb(p, (i + 1 : U32), to, Array.set(U32, LAT.fromT(U32, ta), ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32))), ((i << 2n : U32) + 1 : U32), D, c, LA.set_full(U32, LAT.fromT(U32, ta), D, ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32)), hfa), hD, hc1, hcD, hjW, LAT.mirror(U32, Array.set(U32, LAT.fromT(U32, ta), ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32))))),
        LA.get_set_same(U32, LAT.fromT(U32, ta), ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32))))
      ME.subst(U32, z => {Pair.snd(Array<U32>, U32, Array.get(U32, GM.arr(P.thread(p, KM.MG{Array.set(U32, LAT.fromT(U32, ta), ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32)))}, (i + 1 : U32), to)), ((z << 2n : U32) + 1 : U32))) == P.link_of.go(U32.is_lt((z + 1 : U32), to), (z + 1 : U32)) : U32}, i, n, ein, hat)
    case False{}:
      +hlt = lt_le_ne(U32.to_nat(i), U32.to_nat(n), hlo, he)
      +hlo2 = ME.subst(Nat, q => {Nat.is_le(q, U32.to_nat(n)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), MN.succ_le_of_lt(U32.to_nat(i), U32.to_nat(n), hlt))
      +hhi2 = ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(n), Nat.add(q, p)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1),
        ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(n), q) == True{} : Bool}, Nat.add(U32.to_nat(i), 1n+p), 1n+Nat.add(U32.to_nat(i), p), MN.add_succ(U32.to_nat(i), p), hhi))
      ih(hlo2, hhi2)

def tl(+k: Nat, +i: U32, +to: U32, -a: Array<U32>, +n: U32, +D: Nat, +c: U32, +hf: {AD.full(U32, a, D) == True{} : Bool}, +hD: {Nat.is_lt(D, 32n) == True{} : Bool},
  +hc: {Nat.is_le(Nat.add(Nat.mul(U32.to_nat(i), 4n), Nat.mul(k, 4n)), U32.to_nat(c)) == True{} : Bool}, +hcD: {Nat.is_le(U32.to_nat(c), Nat.pow(2n, D)) == True{} : Bool},
  +hlo: {Nat.is_le(U32.to_nat(i), U32.to_nat(n)) == True{} : Bool}, +hhi: {Nat.is_lt(U32.to_nat(n), Nat.add(U32.to_nat(i), k)) == True{} : Bool}, ma: LAT.Mirror(U32, a)) ->
  {Pair.snd(Array<U32>, U32, Array.get(U32, GM.arr(P.thread(k, KM.MG{a}, i, to)), ((n << 2n : U32) + 1 : U32))) == P.link_of.go(U32.is_lt((n + 1 : U32), to), (n + 1 : U32)) : U32}:
  match k:
    case 0n:
      +h0 = ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(n), q) == True{} : Bool}, Nat.add(U32.to_nat(i), 0n), U32.to_nat(i), MN.add_zero(U32.to_nat(i)), hhi)
      Empty.absurd({Pair.snd(Array<U32>, U32, Array.get(U32, GM.arr(P.thread(0n, KM.MG{a}, i, to)), ((n << 2n : U32) + 1 : U32))) == P.link_of.go(U32.is_lt((n + 1 : U32), to), (n + 1 : U32)) : U32}, MN.lt_irrefl(U32.to_nat(i))(MN.lt_of_le_of_lt(U32.to_nat(i), U32.to_nat(n), U32.to_nat(i), hlo, h0)))
    case 1n+p:
      (+ta, +ea) = ma
      +hfa = LAP.full_t(U32, a, ta, D, ea, hf)
      %ea : {Pair.snd(Array<U32>, U32, Array.get(U32, GM.arr(P.thread(1n+p, KM.MG{_}, i, to)), ((n << 2n : U32) + 1 : U32))) == P.link_of.go(U32.is_lt((n + 1 : U32), to), (n + 1 : U32)) : U32}
      +hW = MN.lt_of_lt_of_le(1n+Nat.mul(U32.to_nat(i), 4n), Nat.add(Nat.mul(U32.to_nat(i), 4n), 4n+Nat.mul(p, 4n)), U32.to_nat(c), lt2(Nat.mul(U32.to_nat(i), 4n), 2n+Nat.mul(p, 4n)), hc)
      +hMC = MN.lt_of_lt_of_le(Nat.mul(U32.to_nat(i), 4n), 1n+Nat.mul(U32.to_nat(i), 4n), U32.to_nat(c), MN.lt_succ_of_le(Nat.mul(U32.to_nat(i), 4n), Nat.mul(U32.to_nat(i), 4n), MN.le_refl(Nat.mul(U32.to_nat(i), 4n))), MN.le_of_lt(1n+Nat.mul(U32.to_nat(i), 4n), U32.to_nat(c), hW))
      +ew = w1n(i, c, hMC)
      +hiC = MN.lt_of_le_of_lt(U32.to_nat(i), Nat.mul(U32.to_nat(i), 4n), U32.to_nat(c), le4(U32.to_nat(i)), hMC)
      +e1 = tn1(i, c, hiC)
      +hc1 = ME.subst(Nat, q => {Nat.is_le(Nat.add(Nat.mul(q, 4n), Nat.mul(p, 4n)), U32.to_nat(c)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1),
        ME.subst(Nat, q => {Nat.is_le(q, U32.to_nat(c)) == True{} : Bool}, Nat.add(Nat.mul(U32.to_nat(i), 4n), 4n+Nat.mul(p, 4n)), 4n+Nat.add(Nat.mul(U32.to_nat(i), 4n), Nat.mul(p, 4n)), add4(Nat.mul(U32.to_nat(i), 4n), Nat.mul(p, 4n)), hc))
      tl.s(Nat.is_eq(U32.to_nat(i), U32.to_nat(n)), i, to, n, ta, p, D, c, {==}, hfa, hD, hcD, hc1, e1, ew, hlo, hhi,
        h1 => h2 => tl(p, (i + 1 : U32), to, Array.set(U32, LAT.fromT(U32, ta), ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32))), n, D, c, LA.set_full(U32, LAT.fromT(U32, ta), D, ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32)), hfa), hD, hc1, hcD, h1, h2, LAT.mirror(U32, Array.set(U32, LAT.fromT(U32, ta), ((i << 2n : U32) + 1 : U32), P.link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32))))))

def Laws.thread_link(k, i, to, a, n, D, c, hf, hD, hc, hcD, hlo, hhi):
  tl(k, i, to, a, n, D, c, hf, hD, hc, hcD, hlo, hhi, LAT.mirror(U32, a))

# a capacity of 2^j words halves j times to 1 within k > j steps: the
# depth a on by j. Each step's test decided from the capacity's number:
# 1 at j = 0, above 1 after, and its half 2^(j - 1)
def dp(+j: Nat, +k: Nat, +cap: U32, +a: Nat, +hc: {U32.to_nat(cap) == Nat.pow(2n, j) : Nat}, +hk: {Nat.is_lt(j, k) == True{} : Bool}) -> {KM.depth(k, cap, a) == Nat.add(j, a) : Nat}:
  match j:
    case 0n:
      match k:
        case 0n:
          Empty.absurd({KM.depth(0n, cap, a) == Nat.add(0n, a) : Nat}, MB.false_ne_true()(hk))
        case 1n+p:
          +e1 = WL.to_nat_inj(cap, 1, hc)
          ME.subst(U32, z => {KM.depth(1n+p, z, a) == a : Nat}, 1, cap, Equal.sym(U32, cap, 1, e1), {==})
    case 1n+q:
      match k:
        case 0n:
          Empty.absurd({KM.depth(0n, cap, a) == Nat.add(1n+q, a) : Nat}, MB.false_ne_true()(hk))
        case 1n+p:
          +hgt = ME.subst(Nat, z => {Nat.is_lt(1n, z) == True{} : Bool}, Nat.pow(2n, 1n+q), U32.to_nat(cap), Equal.sym(Nat, U32.to_nat(cap), Nat.pow(2n, 1n+q), hc), MN.pow_lt_pow_right(0n, 0n, 1n+q, {==}))
          +hne = Equal.trans(Bool, U32.is_eq(cap, 1), Nat.is_eq(U32.to_nat(cap), 1n), False{}, WL.is_eq_to_nat(cap, 1), ne_flip(1n, U32.to_nat(cap), ne_lt(1n, U32.to_nat(cap), hgt)))
          +hs = Equal.trans(Nat, U32.to_nat((cap >> 1n : U32)), Nat.div(U32.to_nat(cap), 2n), Nat.pow(2n, q), WL.to_nat_shr(cap),
            Equal.trans(Nat, Nat.div(U32.to_nat(cap), 2n), Nat.div(Nat.pow(2n, 1n+q), 2n), Nat.pow(2n, q), Equal.cong(Nat, Nat, z => Nat.div(z, 2n), U32.to_nat(cap), Nat.pow(2n, 1n+q), hc),
              MN.mul_div_cancel_left(Nat.pow(2n, q), 1n)))
          +ih = dp(q, p, (cap >> 1n : U32), 1n+a, hs, hk)
          %Equal.sym(Bool, U32.is_eq(cap, 1), False{}, hne) : {KM.depth.go(1n+p, _, cap, a) == Nat.add(1n+q, a) : Nat}
          Equal.trans(Nat, KM.depth(p, (cap >> 1n : U32), 1n+a), Nat.add(q, 1n+a), 1n+Nat.add(q, a), ih, MN.add_succ(q, a))

def Laws.depth_pow(cap, d, hc, hd):
  Equal.trans(Nat, KM.depth(32n, cap, 0n), Nat.add(d, 0n), d, dp(d, 32n, cap, 0n, hc, hd), MN.add_zero(d))
