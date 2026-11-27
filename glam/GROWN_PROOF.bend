# Proofs of glam/GROWN_LAWS.bend (cursor-laws.loop.shape.grow.copy.store
# .kept), kept by hand: the array-level laws of spike/GROW_PROOF.bend
# read through the views (LA.get_view on both sides), the store a tree's
# (a mirror), so that its terms are copyable.
#
# Lessons:
# - The header's words a splice writes (KMd.hdr_all) hold no capacity
#   word, which growth writes: a tracked node misses it through `past`
#   at words 0, 1 and 4 (ge4), its words then 4 or more.

import Base
import ./GROWN_LAWS.bend as Laws
import ../spike/GROW_LAWS.bend as GW
import ../spike/GROW_PROOF.bend as GP
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/kmodel.bend as KMd
import ./ring_model.bend as RG
import ./loop_model.bend as LM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/LAWS.bend as LA
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/PROOF.bend as LAP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_base.bend as AB
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD
import 0x96ab58f86121cb4f3fb48b3c8a045989/LAWS.bend as WL
import 0x96ab58f86121cb4f3fb48b3c8a045989/PROOF.bend as WLP
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MN
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB

# a negation true, its argument false
def nf(+x: Bool, +h: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  MB.not_inj(x, False{}, h)

# a word read alike as itself
def srefl(+x: U32) -> {LM.same(Some{x}, Some{x}) == True{} : Bool}:
  Equal.trans(Bool, U32.is_eq(x, x), Nat.is_eq(U32.to_nat(x), U32.to_nat(x)), True{}, WL.is_eq_to_nat(x, x), MN.is_eq_refl(U32.to_nat(x)))

# a word's sum with another within 2^j < 2^32 is their numbers' sum; 2^32
# abstract as m, put back only for the word law's premise
def tnb.k(+m: Nat, +em: {Nat.pow(2n, 32n) == m : Nat}, +i: U32, +b: U32, +j: Nat, +h: {Nat.is_lt(Nat.add(U32.to_nat(i), U32.to_nat(b)), Nat.pow(2n, j)) == True{} : Bool}, +hj: {Nat.is_lt(j, 32n) == True{} : Bool}) ->
  {U32.to_nat(U32.add(i, b)) == Nat.add(U32.to_nat(i), U32.to_nat(b)) : Nat}:
  +hpm = ME.subst(Nat, q => {Nat.is_lt(Nat.pow(2n, j), q) == True{} : Bool}, Nat.pow(2n, 32n), m, em, AB.pow_lt(j, 32n, hj))
  +hfm = MN.lt_of_lt_of_le(Nat.add(U32.to_nat(i), U32.to_nat(b)), Nat.pow(2n, j), m, h, MN.le_of_lt(Nat.pow(2n, j), m, hpm))
  +hf = ME.subst(Nat, q => {Nat.is_lt(Nat.add(U32.to_nat(i), U32.to_nat(b)), q) == True{} : Bool}, m, Nat.pow(2n, 32n), Equal.sym(Nat, Nat.pow(2n, 32n), m, em), hfm)
  WL.to_nat_add_fits(i, b, hf)

def tnb(+i: U32, +b: U32, +j: Nat, +h: {Nat.is_lt(Nat.add(U32.to_nat(i), U32.to_nat(b)), Nat.pow(2n, j)) == True{} : Bool}, +hj: {Nat.is_lt(j, 32n) == True{} : Bool}) ->
  {U32.to_nat(U32.add(i, b)) == Nat.add(U32.to_nat(i), U32.to_nat(b)) : Nat}:
  tnb.k(Nat.pow(2n, 32n), {==}, i, b, j, h, hj)

# a number off 0, 1, and 4 two and one on, is 4 or more
def ge4(+x: Nat, +h0: {Nat.is_eq(0n, x) == False{} : Bool}, +h1: {Nat.is_eq(1n, x) == False{} : Bool}, +h2: {Nat.is_eq(4n, Nat.add(x, 2n)) == False{} : Bool}, +h3: {Nat.is_eq(4n, Nat.add(x, 1n)) == False{} : Bool}) ->
  {Nat.is_le(4n, x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_le(4n, 0n) == True{} : Bool}, MB.false_ne_true()(Equal.sym(Bool, True{}, False{}, h0)))
    case 1n+p:
      match p:
        case 0n:
          Empty.absurd({Nat.is_le(4n, 1n) == True{} : Bool}, MB.false_ne_true()(Equal.sym(Bool, True{}, False{}, h1)))
        case 1n+q:
          match q:
            case 0n:
              Empty.absurd({Nat.is_le(4n, 2n) == True{} : Bool}, MB.false_ne_true()(Equal.sym(Bool, True{}, False{}, h2)))
            case 1n+r:
              match r:
                case 0n:
                  Empty.absurd({Nat.is_le(4n, 3n) == True{} : Bool}, MB.false_ne_true()(Equal.sym(Bool, True{}, False{}, h3)))
                case 1n+s:
                  MN.le_add_right(4n, s)

# word x of a node off the header's head, errors and table head words
# (one conjunct each of KMd.off.words over KMd.hdr_all)
def ow0(+e: Nat, +x: U32, +o: {KMd.off.words(KMd.hdr_all(), 2n+e, x) == True{} : Bool}) -> {Nat.is_eq(AD.slot(P.at_fh(), 2n+e), AD.slot(x, 2n+e)) == False{} : Bool}:
  nf(Nat.is_eq(AD.slot(P.at_fh(), 2n+e), AD.slot(x, 2n+e)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), 2n+e), AD.slot(x, 2n+e))), KMd.off.words(KMd.hdr_words(), 2n+e, x), o))

def ow1(+e: Nat, +x: U32, +o: {KMd.off.words(KMd.hdr_all(), 2n+e, x) == True{} : Bool}) -> {Nat.is_eq(AD.slot(P.at_errs(), 2n+e), AD.slot(x, 2n+e)) == False{} : Bool}:
  nf(Nat.is_eq(AD.slot(P.at_errs(), 2n+e), AD.slot(x, 2n+e)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), 2n+e), AD.slot(x, 2n+e))), KMd.off.words(KMd.tab_words(), 2n+e, x),
    MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), 2n+e), AD.slot(x, 2n+e))), KMd.off.words(KMd.hdr_words(), 2n+e, x), o)))

def ow4(+e: Nat, +x: U32, +o: {KMd.off.words(KMd.hdr_all(), 2n+e, x) == True{} : Bool}) -> {Nat.is_eq(AD.slot(P.at_tfh(), 2n+e), AD.slot(x, 2n+e)) == False{} : Bool}:
  nf(Nat.is_eq(AD.slot(P.at_tfh(), 2n+e), AD.slot(x, 2n+e)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_tfh(), 2n+e), AD.slot(x, 2n+e))), KMd.off.words([P.at_tn(), P.at_tcap(), P.at_td()], 2n+e, x),
    MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), 2n+e), AD.slot(x, 2n+e))), KMd.off.words(KMd.tab_words(), 2n+e, x),
      MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), 2n+e), AD.slot(x, 2n+e))), KMd.off.words(KMd.hdr_words(), 2n+e, x), o))))

# a slot below 2^(e + 2) as its number
def sn(+e: Nat, +x: U32, +h: {Nat.is_lt(U32.to_nat(x), Nat.pow(2n, 2n+e)) == True{} : Bool}) -> {AD.slot(x, 2n+e) == U32.to_nat(x) : Nat}:
  LA.slot_small(x, 2n+e, h)

# one word of the grown heap's view read alike, by more_old
def kw(+tw: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +hf: {AD.full(U32, LAT.fromT(U32, tw), 2n+e) == True{} : Bool}, +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tw), P.at_wcap())) == wc : U32}, +x: U32, +hj: {Nat.is_lt(U32.to_nat(x), Nat.pow(2n, 2n+e)) == True{} : Bool}, +hj0: {Nat.is_eq(U32.to_nat(x), U32.to_nat(P.at_fh())) == False{} : Bool}, +hj3: {Nat.is_eq(U32.to_nat(x), U32.to_nat(P.at_wcap())) == False{} : Bool}) ->
  {LM.kept.w(x, AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))) == True{} : Bool}:
  +eo = GW.more_old(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), wc, e, x, hf, hwc, hw, he3, he27, hj, hj0, hj3)
  +hf2 = GW.more_full(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), wc, e, hf, hwc, hw, he3, he27)
  %LA.get_view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))), 3n+e, x, hf2, MN.lt_of_lt_of_le(e, 28n, 29n, he27, {==})) : {LM.same(_, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tw)), AD.slot(x, 2n+e))) == True{} : Bool}
  %LA.get_view(U32, LAT.fromT(U32, tw), 2n+e, x, hf, MN.lt_of_lt_of_le(e, 28n, 30n, he27, {==})) : {LM.same(Some{Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))), x))}, _) == True{} : Bool}
  %Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))), x)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tw), x)), eo) : {LM.same(Some{_}, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tw), x))}) == True{} : Bool}
  srefl(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tw), x)))

# each tracked node's four words read alike: in range by RG.inr, off words
# 0 and 3 by past
def kn(+tw: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +hf: {AD.full(U32, LAT.fromT(U32, tw), 2n+e) == True{} : Bool}, +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tw), P.at_wcap())) == wc : U32}, N: List<&2, U32>, +hin: {RG.nodes.in(N, 2n+e) == True{} : Bool}, +hp: {KMd.past(N, 2n+e) == True{} : Bool}) ->
  {LM.kept(N, AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))) == True{} : Bool}:
  match N:
    case Nil{}:
      {==}
    case Con{+n, t}:
      +hr = MB.eq_true_of_and_left(RG.inr(n, 2n+e), RG.nodes.in(t, 2n+e), hin)
      +hrt = MB.eq_true_of_and_right(RG.inr(n, 2n+e), RG.nodes.in(t, 2n+e), hin)
      +hw4 = MB.eq_true_of_and_left(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), 2n+e), KMd.past(t, 2n+e), hp)
      +hpt = MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), 2n+e), KMd.past(t, 2n+e), hp)
      +o0 = MB.eq_true_of_and_left(KMd.off.words(KMd.hdr_all(), 2n+e, n), KMd.ws.off([(n + 1 : U32), (n + 2 : U32), (n + 3 : U32)], KMd.hdr_all(), 2n+e), hw4)
      +r1 = MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), 2n+e, n), KMd.ws.off([(n + 1 : U32), (n + 2 : U32), (n + 3 : U32)], KMd.hdr_all(), 2n+e), hw4)
      +o1 = MB.eq_true_of_and_left(KMd.off.words(KMd.hdr_all(), 2n+e, (n + 1 : U32)), KMd.ws.off([(n + 2 : U32), (n + 3 : U32)], KMd.hdr_all(), 2n+e), r1)
      +r2 = MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), 2n+e, (n + 1 : U32)), KMd.ws.off([(n + 2 : U32), (n + 3 : U32)], KMd.hdr_all(), 2n+e), r1)
      +o2 = MB.eq_true_of_and_left(KMd.off.words(KMd.hdr_all(), 2n+e, (n + 2 : U32)), KMd.ws.off([(n + 3 : U32)], KMd.hdr_all(), 2n+e), r2)
      +r3 = MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), 2n+e, (n + 2 : U32)), KMd.ws.off([(n + 3 : U32)], KMd.hdr_all(), 2n+e), r2)
      +o3 = MB.eq_true_of_and_left(KMd.off.words(KMd.hdr_all(), 2n+e, (n + 3 : U32)), True{}, r3)
      +hz0 = MN.pow_pos(2n+e, 1n)
      +h32 = GP.p32(e, he3)
      +hz1 = MN.lt_of_lt_of_le(1n, 32n, Nat.pow(2n, 2n+e), {==}, h32)
      +hz4 = MN.lt_of_lt_of_le(4n, 32n, Nat.pow(2n, 2n+e), {==}, h32)
      +r0n = MN.lt_of_le_of_lt(U32.to_nat(n), Nat.add(U32.to_nat(n), 3n), Nat.pow(2n, 2n+e), MN.le_add_right(U32.to_nat(n), 3n), hr)
      +q0 = r0n
      +s0 = sn(e, n, q0)
      +z0 = ME.subst(Nat, q => {Nat.is_eq(q, U32.to_nat(n)) == False{} : Bool}, AD.slot(P.at_fh(), 2n+e), 0n, sn(e, P.at_fh(), hz0), ME.subst(Nat, q => {Nat.is_eq(AD.slot(P.at_fh(), 2n+e), q) == False{} : Bool}, AD.slot(n, 2n+e), U32.to_nat(n), s0, ow0(e, n, o0)))
      +b1 = MN.lt_of_le_of_lt(Nat.add(U32.to_nat(n), 1n), Nat.add(U32.to_nat(n), 3n), Nat.pow(2n, 2n+e), MN.add_le_add_left(1n, 3n, U32.to_nat(n), {==}), hr)
      +e1 = tnb(n, 1, 2n+e, b1, MN.lt_of_lt_of_le(e, 28n, 30n, he27, {==}))
      +q1 = ME.subst(Nat, q => {Nat.is_lt(q, Nat.pow(2n, 2n+e)) == True{} : Bool}, Nat.add(U32.to_nat(n), 1n), U32.to_nat((n + 1 : U32)), Equal.sym(Nat, U32.to_nat((n + 1 : U32)), Nat.add(U32.to_nat(n), 1n), e1), b1)
      +s1 = sn(e, (n + 1 : U32), q1)
      +z1 = ME.subst(Nat, q => {Nat.is_eq(q, U32.to_nat((n + 1 : U32))) == False{} : Bool}, AD.slot(P.at_fh(), 2n+e), 0n, sn(e, P.at_fh(), hz0), ME.subst(Nat, q => {Nat.is_eq(AD.slot(P.at_fh(), 2n+e), q) == False{} : Bool}, AD.slot((n + 1 : U32), 2n+e), U32.to_nat((n + 1 : U32)), s1, ow0(e, (n + 1 : U32), o1)))
      +b2 = MN.lt_of_le_of_lt(Nat.add(U32.to_nat(n), 2n), Nat.add(U32.to_nat(n), 3n), Nat.pow(2n, 2n+e), MN.add_le_add_left(2n, 3n, U32.to_nat(n), {==}), hr)
      +e2 = tnb(n, 2, 2n+e, b2, MN.lt_of_lt_of_le(e, 28n, 30n, he27, {==}))
      +q2 = ME.subst(Nat, q => {Nat.is_lt(q, Nat.pow(2n, 2n+e)) == True{} : Bool}, Nat.add(U32.to_nat(n), 2n), U32.to_nat((n + 2 : U32)), Equal.sym(Nat, U32.to_nat((n + 2 : U32)), Nat.add(U32.to_nat(n), 2n), e2), b2)
      +s2 = sn(e, (n + 2 : U32), q2)
      +z2 = ME.subst(Nat, q => {Nat.is_eq(q, U32.to_nat((n + 2 : U32))) == False{} : Bool}, AD.slot(P.at_fh(), 2n+e), 0n, sn(e, P.at_fh(), hz0), ME.subst(Nat, q => {Nat.is_eq(AD.slot(P.at_fh(), 2n+e), q) == False{} : Bool}, AD.slot((n + 2 : U32), 2n+e), U32.to_nat((n + 2 : U32)), s2, ow0(e, (n + 2 : U32), o2)))
      +b3 = MN.lt_of_le_of_lt(Nat.add(U32.to_nat(n), 3n), Nat.add(U32.to_nat(n), 3n), Nat.pow(2n, 2n+e), MN.add_le_add_left(3n, 3n, U32.to_nat(n), {==}), hr)
      +e3 = tnb(n, 3, 2n+e, b3, MN.lt_of_lt_of_le(e, 28n, 30n, he27, {==}))
      +q3 = ME.subst(Nat, q => {Nat.is_lt(q, Nat.pow(2n, 2n+e)) == True{} : Bool}, Nat.add(U32.to_nat(n), 3n), U32.to_nat((n + 3 : U32)), Equal.sym(Nat, U32.to_nat((n + 3 : U32)), Nat.add(U32.to_nat(n), 3n), e3), b3)
      +s3 = sn(e, (n + 3 : U32), q3)
      +z3 = ME.subst(Nat, q => {Nat.is_eq(q, U32.to_nat((n + 3 : U32))) == False{} : Bool}, AD.slot(P.at_fh(), 2n+e), 0n, sn(e, P.at_fh(), hz0), ME.subst(Nat, q => {Nat.is_eq(AD.slot(P.at_fh(), 2n+e), q) == False{} : Bool}, AD.slot((n + 3 : U32), 2n+e), U32.to_nat((n + 3 : U32)), s3, ow0(e, (n + 3 : U32), o3)))
      +y1 = ME.subst(Nat, q => {Nat.is_eq(q, U32.to_nat(n)) == False{} : Bool}, AD.slot(P.at_errs(), 2n+e), 1n, sn(e, P.at_errs(), hz1), ME.subst(Nat, q => {Nat.is_eq(AD.slot(P.at_errs(), 2n+e), q) == False{} : Bool}, AD.slot(n, 2n+e), U32.to_nat(n), s0, ow1(e, n, o0)))
      +y4a = ME.subst(Nat, q => {Nat.is_eq(q, Nat.add(U32.to_nat(n), 1n)) == False{} : Bool}, AD.slot(P.at_tfh(), 2n+e), 4n, sn(e, P.at_tfh(), hz4), ME.subst(Nat, q => {Nat.is_eq(AD.slot(P.at_tfh(), 2n+e), q) == False{} : Bool}, AD.slot((n + 1 : U32), 2n+e), Nat.add(U32.to_nat(n), 1n), Equal.trans(Nat, AD.slot((n + 1 : U32), 2n+e), U32.to_nat((n + 1 : U32)), Nat.add(U32.to_nat(n), 1n), s1, e1), ow4(e, (n + 1 : U32), o1)))
      +y4b = ME.subst(Nat, q => {Nat.is_eq(q, Nat.add(U32.to_nat(n), 2n)) == False{} : Bool}, AD.slot(P.at_tfh(), 2n+e), 4n, sn(e, P.at_tfh(), hz4), ME.subst(Nat, q => {Nat.is_eq(AD.slot(P.at_tfh(), 2n+e), q) == False{} : Bool}, AD.slot((n + 2 : U32), 2n+e), Nat.add(U32.to_nat(n), 2n), Equal.trans(Nat, AD.slot((n + 2 : U32), 2n+e), U32.to_nat((n + 2 : U32)), Nat.add(U32.to_nat(n), 2n), s2, e2), ow4(e, (n + 2 : U32), o2)))
      +g4 = ge4(U32.to_nat(n), z0, y1, y4b, y4a)
      +k0 = kw(tw, ta, wc, e, hw, he3, he27, hf, hwc, n, q0, GP.ne_flip(0n, U32.to_nat(n), z0), GP.ne_flip(3n, U32.to_nat(n), GP.ne_lt(3n, U32.to_nat(n), MN.lt_of_lt_of_le(3n, 4n, U32.to_nat(n), {==}, g4))))
      +k1 = kw(tw, ta, wc, e, hw, he3, he27, hf, hwc, (n + 1 : U32), q1, GP.ne_flip(0n, U32.to_nat((n + 1 : U32)), z1), GP.ne_flip(3n, U32.to_nat((n + 1 : U32)), GP.ne_lt(3n, U32.to_nat((n + 1 : U32)), ME.subst(Nat, q => {Nat.is_lt(3n, q) == True{} : Bool}, Nat.add(U32.to_nat(n), 1n), U32.to_nat((n + 1 : U32)), Equal.sym(Nat, U32.to_nat((n + 1 : U32)), Nat.add(U32.to_nat(n), 1n), e1), MN.lt_of_lt_of_le(3n, 4n, Nat.add(U32.to_nat(n), 1n), {==}, MN.le_trans(4n, U32.to_nat(n), Nat.add(U32.to_nat(n), 1n), g4, MN.le_add_right(U32.to_nat(n), 1n)))))))
      +k2 = kw(tw, ta, wc, e, hw, he3, he27, hf, hwc, (n + 2 : U32), q2, GP.ne_flip(0n, U32.to_nat((n + 2 : U32)), z2), GP.ne_flip(3n, U32.to_nat((n + 2 : U32)), GP.ne_lt(3n, U32.to_nat((n + 2 : U32)), ME.subst(Nat, q => {Nat.is_lt(3n, q) == True{} : Bool}, Nat.add(U32.to_nat(n), 2n), U32.to_nat((n + 2 : U32)), Equal.sym(Nat, U32.to_nat((n + 2 : U32)), Nat.add(U32.to_nat(n), 2n), e2), MN.lt_of_lt_of_le(3n, 4n, Nat.add(U32.to_nat(n), 2n), {==}, MN.le_trans(4n, U32.to_nat(n), Nat.add(U32.to_nat(n), 2n), g4, MN.le_add_right(U32.to_nat(n), 2n)))))))
      +k3 = kw(tw, ta, wc, e, hw, he3, he27, hf, hwc, (n + 3 : U32), q3, GP.ne_flip(0n, U32.to_nat((n + 3 : U32)), z3), GP.ne_flip(3n, U32.to_nat((n + 3 : U32)), GP.ne_lt(3n, U32.to_nat((n + 3 : U32)), ME.subst(Nat, q => {Nat.is_lt(3n, q) == True{} : Bool}, Nat.add(U32.to_nat(n), 3n), U32.to_nat((n + 3 : U32)), Equal.sym(Nat, U32.to_nat((n + 3 : U32)), Nat.add(U32.to_nat(n), 3n), e3), MN.lt_of_lt_of_le(3n, 4n, Nat.add(U32.to_nat(n), 3n), {==}, MN.le_trans(4n, U32.to_nat(n), Nat.add(U32.to_nat(n), 3n), g4, MN.le_add_right(U32.to_nat(n), 3n)))))))
      MB.and_eq_true(LM.kept.w(n, AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))), LM.kept.w((n + 1 : U32), AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))) && (LM.kept.w((n + 2 : U32), AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))) && (LM.kept.w((n + 3 : U32), AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))) && LM.kept(t, AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))))), k0,
        MB.and_eq_true(LM.kept.w((n + 1 : U32), AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))), LM.kept.w((n + 2 : U32), AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))) && (LM.kept.w((n + 3 : U32), AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))) && LM.kept(t, AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))))), k1,
          MB.and_eq_true(LM.kept.w((n + 2 : U32), AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))), LM.kept.w((n + 3 : U32), AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))) && LM.kept(t, AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))), k2,
            MB.and_eq_true(LM.kept.w((n + 3 : U32), AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))), LM.kept(t, AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))))), k3, kn(tw, ta, wc, e, hw, he3, he27, hf, hwc, t, hrt, hpt)))))

def kept.w(-w: Array<U32>, -a: Array<V.Val>, +wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, N: List<&2, U32>, +hf: {AD.full(U32, w, 2n+e) == True{} : Bool}, +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_wcap())) == wc : U32},
  +hin: {RG.nodes.in(N, 2n+e) == True{} : Bool}, +hp: {KMd.past(N, 2n+e) == True{} : Bool}, mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {LM.kept(N, AD.view(U32, w), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a}))))) == True{} : Bool}:
  (+tw, +ew) = mw
  (+ta, +ea) = ma
  +hf2 = LAP.full_t(U32, w, tw, 2n+e, ew, hf)
  +hwc2 = ME.subst(Array<U32>, z => {Pair.snd(Array<U32>, U32, Array.get(U32, z, P.at_wcap())) == wc : U32}, w, LAT.fromT(U32, tw), Equal.sym(Array<U32>, LAT.fromT(U32, tw), w, ew), hwc)
  %ew : {LM.kept(N, AD.view(U32, _), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{_}, a}))))) == True{} : Bool}
  %ea : {LM.kept(N, AD.view(U32, LAT.fromT(U32, tw)), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, _}))))) == True{} : Bool}
  kn(tw, ta, wc, e, hw, he3, he27, hf2, hwc2, N, hin, hp)

def Laws.grown_kept(w, a, wc, e, N, hf, hwc, hw, he3, he27, hin, hp):
  kept.w(w, a, wc, e, hw, he3, he27, N, hf, hwc, hin, hp, LAT.mirror(U32, w), LAT.mirror(V.Val, a))
