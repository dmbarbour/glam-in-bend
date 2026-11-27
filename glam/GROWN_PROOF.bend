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
import ../spike/grow_model.bend as GM
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/kmodel.bend as KMd
import ./ring_model.bend as RG
import ./loop_model.bend as LM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/LAWS.bend as LA
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/PROOF.bend as LAP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_base.bend as AB
import 0x96ab58f86121cb4f3fb48b3c8a045989/proof_nat.bend as WN
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD
import 0x96ab58f86121cb4f3fb48b3c8a045989/LAWS.bend as WL
import 0x96ab58f86121cb4f3fb48b3c8a045989/PROOF.bend as WLP
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MN
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB

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
  MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(P.at_fh(), 2n+e), AD.slot(x, 2n+e)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), 2n+e), AD.slot(x, 2n+e))), KMd.off.words(KMd.hdr_words(), 2n+e, x), o))

def ow1(+e: Nat, +x: U32, +o: {KMd.off.words(KMd.hdr_all(), 2n+e, x) == True{} : Bool}) -> {Nat.is_eq(AD.slot(P.at_errs(), 2n+e), AD.slot(x, 2n+e)) == False{} : Bool}:
  MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(P.at_errs(), 2n+e), AD.slot(x, 2n+e)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), 2n+e), AD.slot(x, 2n+e))), KMd.off.words(KMd.tab_words(), 2n+e, x),
    MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), 2n+e), AD.slot(x, 2n+e))), KMd.off.words(KMd.hdr_words(), 2n+e, x), o)))

def ow4(+e: Nat, +x: U32, +o: {KMd.off.words(KMd.hdr_all(), 2n+e, x) == True{} : Bool}) -> {Nat.is_eq(AD.slot(P.at_tfh(), 2n+e), AD.slot(x, 2n+e)) == False{} : Bool}:
  MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(P.at_tfh(), 2n+e), AD.slot(x, 2n+e)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_tfh(), 2n+e), AD.slot(x, 2n+e))), KMd.off.words([P.at_tn(), P.at_tcap(), P.at_td()], 2n+e, x),
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

# a word of the grown view, the grown heap's word
def wv(+tw: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +hf: {AD.full(U32, LAT.fromT(U32, tw), 2n+e) == True{} : Bool}, +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tw), P.at_wcap())) == wc : U32}, +j: U32) -> {KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, j) == Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))), j)) : U32}:
  +hf2 = GW.more_full(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), wc, e, hf, hwc, hw, he3, he27)
  %LA.get_view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))), 3n+e, j, hf2, MN.lt_of_lt_of_le(e, 28n, 29n, he27, {==})) : {KMd.word.m(_) == Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))), j)) : U32}
  {==}

# node i of the fresh range, i below 2wc: its successor's number, one on
def fi1(+wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +i: U32, +hi: {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, 1n+e)) == True{} : Bool}) -> {U32.to_nat((i + 1 : U32)) == 1n+U32.to_nat(i) : Nat}:
  +h = MN.lt_of_le_of_lt(Nat.add(U32.to_nat(i), 1n), Nat.pow(2n, 1n+e), Nat.pow(2n, 3n+e), ME.subst(Nat, q => {Nat.is_le(q, Nat.pow(2n, 1n+e)) == True{} : Bool}, 1n+U32.to_nat(i), Nat.add(U32.to_nat(i), 1n), MN.add_comm(1n, U32.to_nat(i)), MN.succ_le_of_lt(U32.to_nat(i), Nat.pow(2n, 1n+e), hi)), AB.pow_lt(1n+e, 3n+e, MN.lt_succ_of_le(1n+e, 2n+e, MN.le_succ(1n+e))))
  Equal.trans(Nat, U32.to_nat((i + 1 : U32)), Nat.add(U32.to_nat(i), 1n), 1n+U32.to_nat(i), tnb(i, 1, 3n+e, h, MN.lt_of_lt_of_le(e, 28n, 29n, he27, {==})), MN.add_comm(U32.to_nat(i), 1n))

# a link one on, less one, is the node again (KMd.at_idx)
def ai(+wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +i: U32, +hi: {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, 1n+e)) == True{} : Bool}) -> {U32.is_eq(KMd.at_idx((i + 1 : U32)), (i << 2n : U32)) == True{} : Bool}:
  +e1 = fi1(wc, e, hw, he3, he27, i, hi)
  +hle = Equal.trans(Bool, U32.is_le(1, (i + 1 : U32)), Nat.is_le(U32.to_nat(1), U32.to_nat((i + 1 : U32))), True{}, WL.is_le_to_nat(1, (i + 1 : U32)), ME.subst(Nat, q => {Nat.is_le(1n, q) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), MN.zero_le(U32.to_nat(i))))
  +es = Equal.trans(Nat, U32.to_nat(((i + 1 : U32) - 1 : U32)), Nat.sub(U32.to_nat((i + 1 : U32)), 1n), U32.to_nat(i), WL.to_nat_sub_le((i + 1 : U32), 1, hle), Equal.trans(Nat, Nat.sub(U32.to_nat((i + 1 : U32)), 1n), Nat.sub(Nat.add(U32.to_nat(i), 1n), 1n), U32.to_nat(i), Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), U32.to_nat((i + 1 : U32)), Nat.add(U32.to_nat(i), 1n), Equal.trans(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), Nat.add(U32.to_nat(i), 1n), e1, MN.add_comm(1n, U32.to_nat(i)))), MN.add_sub_cancel(U32.to_nat(i), 1n)))
  +eq = WL.to_nat_inj(((i + 1 : U32) - 1 : U32), i, es)
  ME.subst(U32, z => {U32.is_eq((z << 2n : U32), (i << 2n : U32)) == True{} : Bool}, i, ((i + 1 : U32) - 1 : U32), Equal.sym(U32, ((i + 1 : U32) - 1 : U32), i, eq), Equal.trans(Bool, U32.is_eq((i << 2n : U32), (i << 2n : U32)), Nat.is_eq(U32.to_nat((i << 2n : U32)), U32.to_nat((i << 2n : U32))), True{}, WL.is_eq_to_nat((i << 2n : U32), (i << 2n : U32)), MN.is_eq_refl(U32.to_nat((i << 2n : U32)))))

# a link one on is never 0
def nz(+wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +i: U32, +hi: {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, 1n+e)) == True{} : Bool}) -> {Bool.not(U32.is_eq((i + 1 : U32), 0)) == True{} : Bool}:
  +e1 = fi1(wc, e, hw, he3, he27, i, hi)
  +h0 = Equal.trans(Bool, U32.is_eq((i + 1 : U32), 0), Nat.is_eq(U32.to_nat((i + 1 : U32)), U32.to_nat(0)), False{}, WL.is_eq_to_nat((i + 1 : U32), 0), ME.subst(Nat, q => {Nat.is_eq(q, U32.to_nat(0)) == False{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), {==}))
  Equal.cong(Bool, Bool, z => Bool.not(z), U32.is_eq((i + 1 : U32), 0), False{}, h0)

def hik(+wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +p: Nat, +i: U32, +hk: {Nat.is_le(Nat.add(1n+p, U32.to_nat(i)), Nat.pow(2n, 1n+e)) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, 1n+e)) == True{} : Bool}:
  MN.lt_of_lt_of_le(U32.to_nat(i), Nat.add(1n+p, U32.to_nat(i)), Nat.pow(2n, 1n+e), MN.lt_of_lt_of_le(U32.to_nat(i), 1n+U32.to_nat(i), Nat.add(1n+p, U32.to_nat(i)), MN.lt_succ_of_le(U32.to_nat(i), U32.to_nat(i), MN.le_refl(U32.to_nat(i))), MN.le_add_left(U32.to_nat(i), p)), hk)

def kst(+wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +p: Nat, +i: U32, +hk: {Nat.is_le(Nat.add(1n+p, U32.to_nat(i)), Nat.pow(2n, 1n+e)) == True{} : Bool}, +e1: {U32.to_nat((i + 1 : U32)) == 1n+U32.to_nat(i) : Nat}) -> {Nat.is_le(Nat.add(p, U32.to_nat((i + 1 : U32))), Nat.pow(2n, 1n+e)) == True{} : Bool}:
  ME.subst(Nat, q => {Nat.is_le(Nat.add(p, q), Nat.pow(2n, 1n+e)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), ME.subst(Nat, q => {Nat.is_le(q, Nat.pow(2n, 1n+e)) == True{} : Bool}, 1n+Nat.add(p, U32.to_nat(i)), Nat.add(p, 1n+U32.to_nat(i)), Equal.sym(Nat, Nat.add(p, 1n+U32.to_nat(i)), 1n+Nat.add(p, U32.to_nat(i)), MN.add_succ(p, U32.to_nat(i))), hk))

def lo1(+wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +i: U32, +hlo: {Nat.is_le(U32.to_nat(wc), U32.to_nat(i)) == True{} : Bool}, +e1: {U32.to_nat((i + 1 : U32)) == 1n+U32.to_nat(i) : Nat}) -> {Nat.is_le(U32.to_nat(wc), U32.to_nat((i + 1 : U32))) == True{} : Bool}:
  ME.subst(Nat, q => {Nat.is_le(U32.to_nat(wc), q) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), MN.le_trans(U32.to_nat(wc), U32.to_nat(i), 1n+U32.to_nat(i), hlo, MN.le_succ(U32.to_nat(i))))

# wc nodes from wc fit below 2wc
def hkw(+wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}) -> {Nat.is_le(Nat.add(U32.to_nat(wc), U32.to_nat(wc)), Nat.pow(2n, 1n+e)) == True{} : Bool}:
  ME.subst(Nat, q => {Nat.is_le(Nat.add(q, q), Nat.pow(2n, 1n+e)) == True{} : Bool}, Nat.pow(2n, e), U32.to_nat(wc), Equal.sym(Nat, U32.to_nat(wc), Nat.pow(2n, e), hw), ME.subst(Nat, q => {Nat.is_le(Nat.add(Nat.pow(2n, e), q), Nat.pow(2n, 1n+e)) == True{} : Bool}, Nat.add(Nat.pow(2n, e), 0n), Nat.pow(2n, e), MN.add_zero(Nat.pow(2n, e)), MN.le_refl(Nat.pow(2n, 1n+e))))

# the fresh nodes i on, chained from node i's link: each links the next
# (more_link), the last's link not read
def ch.go(+tw: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +hf: {AD.full(U32, LAT.fromT(U32, tw), 2n+e) == True{} : Bool}, +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tw), P.at_wcap())) == wc : U32}, +p: Nat, +i: U32, +hlo: {Nat.is_le(U32.to_nat(wc), U32.to_nat(i)) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(1n+p, U32.to_nat(i)), Nat.pow(2n, 1n+e)) == True{} : Bool},
  ih: {Nat.is_le(U32.to_nat(wc), U32.to_nat((i + 1 : U32))) == True{} : Bool} -> {Nat.is_le(Nat.add(p, U32.to_nat((i + 1 : U32))), Nat.pow(2n, 1n+e)) == True{} : Bool} -> {KMd.chain(GM.fresh(p, (i + 1 : U32)), AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, ((i + 1 : U32) + 1 : U32)) == True{} : Bool}) ->
  {KMd.chain(GM.fresh(p, (i + 1 : U32)), AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, ((i << 2n : U32) + 1 : U32))) == True{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      +hi = hik(wc, e, hw, he3, he27, 1n+q, i, hk)
      +e1 = fi1(wc, e, hw, he3, he27, i, hi)
      +hhi = MN.lt_of_lt_of_le(1n+U32.to_nat(i), Nat.add(2n+q, U32.to_nat(i)), Nat.pow(2n, 1n+e), MN.lt_succ_of_le(U32.to_nat(i), Nat.add(q, U32.to_nat(i)), MN.le_add_left(U32.to_nat(i), q)), hk)
      +eL = Equal.trans(U32, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, ((i << 2n : U32) + 1 : U32)), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))), ((i << 2n : U32) + 1 : U32))), ((i + 1 : U32) + 1 : U32), wv(tw, ta, wc, e, hw, he3, he27, hf, hwc, ((i << 2n : U32) + 1 : U32)), GW.more_link(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), wc, e, hf, hwc, hw, he3, he27, i, hlo, hhi))
      %Equal.sym(U32, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, ((i << 2n : U32) + 1 : U32)), ((i + 1 : U32) + 1 : U32), eL) : {KMd.chain(GM.fresh(1n+q, (i + 1 : U32)), AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, _) == True{} : Bool}
      +hlo1 = lo1(wc, e, hw, he3, he27, i, hlo, e1)
      +hk1 = kst(wc, e, hw, he3, he27, 1n+q, i, hk, e1)
      ih(hlo1, hk1)

def ch(+tw: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +hf: {AD.full(U32, LAT.fromT(U32, tw), 2n+e) == True{} : Bool}, +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tw), P.at_wcap())) == wc : U32}, +k: Nat, +i: U32, +hlo: {Nat.is_le(U32.to_nat(wc), U32.to_nat(i)) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(k, U32.to_nat(i)), Nat.pow(2n, 1n+e)) == True{} : Bool}) -> {KMd.chain(GM.fresh(k, i), AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, (i + 1 : U32)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      +hi = hik(wc, e, hw, he3, he27, p, i, hk)
      MB.and_eq_true(Bool.not(U32.is_eq((i + 1 : U32), 0)), U32.is_eq(KMd.at_idx((i + 1 : U32)), (i << 2n : U32)) && KMd.chain(GM.fresh(p, (i + 1 : U32)), AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, ((i << 2n : U32) + 1 : U32))), nz(wc, e, hw, he3, he27, i, hi),
        MB.and_eq_true(U32.is_eq(KMd.at_idx((i + 1 : U32)), (i << 2n : U32)), KMd.chain(GM.fresh(p, (i + 1 : U32)), AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, ((i << 2n : U32) + 1 : U32))), ai(wc, e, hw, he3, he27, i, hi),
          ch.go(tw, ta, wc, e, hw, he3, he27, hf, hwc, p, i, hlo, hk, h1 => h2 => ch(tw, ta, wc, e, hw, he3, he27, hf, hwc, p, (i + 1 : U32), h1, h2))))

def gch(+tw: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +hf: {AD.full(U32, LAT.fromT(U32, tw), 2n+e) == True{} : Bool}, +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tw), P.at_wcap())) == wc : U32}) -> {KMd.chain(GM.fresh(U32.to_nat(wc), wc), AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, P.at_fh())) == True{} : Bool}:
  +eh = Equal.trans(U32, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}))), P.at_fh())), (wc + 1 : U32), wv(tw, ta, wc, e, hw, he3, he27, hf, hwc, P.at_fh()), GW.more_head(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), wc, e, hf, hwc, hw, he3, he27))
  %Equal.sym(U32, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, P.at_fh()), (wc + 1 : U32), eh) : {KMd.chain(GM.fresh(U32.to_nat(wc), wc), AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)})))), 3n+e, _) == True{} : Bool}
  +hk = ME.subst(Nat, q => {Nat.is_le(Nat.add(q, q), Nat.pow(2n, 1n+e)) == True{} : Bool}, Nat.pow(2n, e), U32.to_nat(wc), Equal.sym(Nat, U32.to_nat(wc), Nat.pow(2n, e), hw), ME.subst(Nat, q => {Nat.is_le(Nat.add(Nat.pow(2n, e), q), Nat.pow(2n, 1n+e)) == True{} : Bool}, Nat.add(Nat.pow(2n, e), 0n), Nat.pow(2n, e), MN.add_zero(Nat.pow(2n, e)), MN.le_refl(Nat.pow(2n, 1n+e))))
  ch(tw, ta, wc, e, hw, he3, he27, hf, hwc, U32.to_nat(wc), wc, MN.le_refl(U32.to_nat(wc)), hk)

def chain.w(-w: Array<U32>, -a: Array<V.Val>, +wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +hf: {AD.full(U32, w, 2n+e) == True{} : Bool}, +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_wcap())) == wc : U32}, mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {KMd.chain(GM.fresh(U32.to_nat(wc), wc), AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a})))), 3n+e, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a})))), 3n+e, P.at_fh())) == True{} : Bool}:
  (+tw, +ew) = mw
  (+ta, +ea) = ma
  +hf2 = LAP.full_t(U32, w, tw, 2n+e, ew, hf)
  +hwc2 = ME.subst(Array<U32>, z => {Pair.snd(Array<U32>, U32, Array.get(U32, z, P.at_wcap())) == wc : U32}, w, LAT.fromT(U32, tw), Equal.sym(Array<U32>, LAT.fromT(U32, tw), w, ew), hwc)
  %ew : {KMd.chain(GM.fresh(U32.to_nat(wc), wc), AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{_}, a})))), 3n+e, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{_}, a})))), 3n+e, P.at_fh())) == True{} : Bool}
  %ea : {KMd.chain(GM.fresh(U32.to_nat(wc), wc), AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, _})))), 3n+e, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{LAT.fromT(U32, tw)}, _})))), 3n+e, P.at_fh())) == True{} : Bool}
  gch(tw, ta, wc, e, hw, he3, he27, hf2, hwc2)

def Laws.grown_chain(w, a, wc, e, hf, hwc, hw, he3, he27):
  chain.w(w, a, wc, e, hw, he3, he27, hf, hwc, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# Bool.or of two falses
def orff(+x: Bool, +y: Bool, +hx: {x == False{} : Bool}, +hy: {y == False{} : Bool}) -> {Bool.or(x, y) == False{} : Bool}:
  %Equal.sym(Bool, x, False{}, hx) : {Bool.or(_, y) == False{} : Bool}
  hy

# no fresh node j on is node i's, i below j
def nh(+wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +p: Nat, +j: U32, +i: U32, +hij: {Nat.is_lt(U32.to_nat(i), U32.to_nat(j)) == True{} : Bool}, +hb: {Nat.is_le(Nat.add(p, U32.to_nat(j)), Nat.pow(2n, 1n+e)) == True{} : Bool}) ->
  {RG.has(GM.fresh(p, j), (i << 2n : U32)) == False{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      +hj = hik(wc, e, hw, he3, he27, q, j, hb)
      +hi = MN.lt_of_lt_of_le(U32.to_nat(i), U32.to_nat(j), Nat.pow(2n, 1n+e), hij, MN.le_of_lt(U32.to_nat(j), Nat.pow(2n, 1n+e), hj))
      +e1 = fi1(wc, e, hw, he3, he27, j, hj)
      +h4 = Equal.trans(Bool, Nat.is_eq(Nat.mul(U32.to_nat(j), 4n), Nat.mul(U32.to_nat(i), 4n)), Nat.is_eq(U32.to_nat(j), U32.to_nat(i)), False{}, GP.q4(U32.to_nat(j), U32.to_nat(i)), GP.ne_flip(U32.to_nat(i), U32.to_nat(j), GP.ne_lt(U32.to_nat(i), U32.to_nat(j), hij)))
      +h5 = ME.subst(Nat, q => {Nat.is_eq(q, U32.to_nat((i << 2n : U32))) == False{} : Bool}, Nat.mul(U32.to_nat(j), 4n), U32.to_nat((j << 2n : U32)), Equal.sym(Nat, U32.to_nat((j << 2n : U32)), Nat.mul(U32.to_nat(j), 4n), GP.eH(wc, e, hw, he3, he27, j, hj)), ME.subst(Nat, q => {Nat.is_eq(Nat.mul(U32.to_nat(j), 4n), q) == False{} : Bool}, Nat.mul(U32.to_nat(i), 4n), U32.to_nat((i << 2n : U32)), Equal.sym(Nat, U32.to_nat((i << 2n : U32)), Nat.mul(U32.to_nat(i), 4n), GP.eH(wc, e, hw, he3, he27, i, hi)), h4))
      +h6 = Equal.trans(Bool, U32.is_eq((j << 2n : U32), (i << 2n : U32)), Nat.is_eq(U32.to_nat((j << 2n : U32)), U32.to_nat((i << 2n : U32))), False{}, WL.is_eq_to_nat((j << 2n : U32), (i << 2n : U32)), h5)
      +hij1 = ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(i), q) == True{} : Bool}, 1n+U32.to_nat(j), U32.to_nat((j + 1 : U32)), Equal.sym(Nat, U32.to_nat((j + 1 : U32)), 1n+U32.to_nat(j), e1), MN.lt_of_lt_of_le(U32.to_nat(i), U32.to_nat(j), 1n+U32.to_nat(j), hij, MN.le_succ(U32.to_nat(j))))
      +hb2 = kst(wc, e, hw, he3, he27, q, j, hb, e1)
      orff(U32.is_eq((j << 2n : U32), (i << 2n : U32)), RG.has(GM.fresh(q, (j + 1 : U32)), (i << 2n : U32)), h6, nh(wc, e, hw, he3, he27, q, (j + 1 : U32), i, hij1, hb2))

def dst(+wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +k: Nat, +i: U32, +hk: {Nat.is_le(Nat.add(k, U32.to_nat(i)), Nat.pow(2n, 1n+e)) == True{} : Bool}) -> {RG.distinct(GM.fresh(k, i)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      +hi = hik(wc, e, hw, he3, he27, p, i, hk)
      +e1 = fi1(wc, e, hw, he3, he27, i, hi)
      +hij = ME.subst(Nat, q => {Nat.is_lt(U32.to_nat(i), q) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), e1), MN.lt_succ_of_le(U32.to_nat(i), U32.to_nat(i), MN.le_refl(U32.to_nat(i))))
      +hb = kst(wc, e, hw, he3, he27, p, i, hk, e1)
      MB.and_eq_true(Bool.not(RG.has(GM.fresh(p, (i + 1 : U32)), (i << 2n : U32))), RG.distinct(GM.fresh(p, (i + 1 : U32))), Equal.cong(Bool, Bool, z => Bool.not(z), RG.has(GM.fresh(p, (i + 1 : U32)), (i << 2n : U32)), False{}, nh(wc, e, hw, he3, he27, p, (i + 1 : U32), i, hij, hb)), dst(wc, e, hw, he3, he27, p, (i + 1 : U32), hb))

def Laws.grown_distinct(wc, e, hw, he3, he27):
  dst(wc, e, hw, he3, he27, U32.to_nat(wc), wc, hkw(wc, e, hw, he3, he27))

# no tracked node, in range at the old depth, is word x at 2^(e + 2) or past
def hn(+wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +N: List<&2, U32>, +x: U32, +hin: {RG.nodes.in(N, 2n+e) == True{} : Bool}, +hx: {Nat.is_le(Nat.pow(2n, 2n+e), U32.to_nat(x)) == True{} : Bool}) -> {RG.has(N, x) == False{} : Bool}:
  match N:
    case Nil{}:
      {==}
    case Con{+n, t}:
      +hr = MB.eq_true_of_and_left(RG.inr(n, 2n+e), RG.nodes.in(t, 2n+e), hin)
      +hrt = MB.eq_true_of_and_right(RG.inr(n, 2n+e), RG.nodes.in(t, 2n+e), hin)
      +hl = MN.lt_of_lt_of_le(U32.to_nat(n), Nat.pow(2n, 2n+e), U32.to_nat(x), MN.lt_of_le_of_lt(U32.to_nat(n), Nat.add(U32.to_nat(n), 3n), Nat.pow(2n, 2n+e), MN.le_add_right(U32.to_nat(n), 3n), hr), hx)
      +h0 = Equal.trans(Bool, U32.is_eq(n, x), Nat.is_eq(U32.to_nat(n), U32.to_nat(x)), False{}, WL.is_eq_to_nat(n, x), GP.ne_lt(U32.to_nat(n), U32.to_nat(x), hl))
      orff(U32.is_eq(n, x), RG.has(t, x), h0, hn(wc, e, hw, he3, he27, t, x, hrt, hx))

def nin(+wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +k: Nat, +i: U32, +N: List<&2, U32>, +hin: {RG.nodes.in(N, 2n+e) == True{} : Bool}, +hlo: {Nat.is_le(U32.to_nat(wc), U32.to_nat(i)) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(k, U32.to_nat(i)), Nat.pow(2n, 1n+e)) == True{} : Bool}) -> {RG.none.in(GM.fresh(k, i), N) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      +hi = hik(wc, e, hw, he3, he27, p, i, hk)
      +e1 = fi1(wc, e, hw, he3, he27, i, hi)
      +hx = ME.subst(Nat, q => {Nat.is_le(Nat.pow(2n, 2n+e), q) == True{} : Bool}, Nat.mul(U32.to_nat(i), 4n), U32.to_nat((i << 2n : U32)), Equal.sym(Nat, U32.to_nat((i << 2n : U32)), Nat.mul(U32.to_nat(i), 4n), GP.eH(wc, e, hw, he3, he27, i, hi)), GP.pm(wc, e, hw, he3, he27, i, hlo))
      MB.and_eq_true(Bool.not(RG.has(N, (i << 2n : U32))), RG.none.in(GM.fresh(p, (i + 1 : U32)), N), Equal.cong(Bool, Bool, z => Bool.not(z), RG.has(N, (i << 2n : U32)), False{}, hn(wc, e, hw, he3, he27, N, (i << 2n : U32), hin, hx)),
        nin(wc, e, hw, he3, he27, p, (i + 1 : U32), N, hin, lo1(wc, e, hw, he3, he27, i, hlo, e1), kst(wc, e, hw, he3, he27, p, i, hk, e1)))

def Laws.grown_none(wc, e, hw, he3, he27, N, hin):
  nin(wc, e, hw, he3, he27, U32.to_nat(wc), wc, N, hin, MN.le_refl(U32.to_nat(wc)), hkw(wc, e, hw, he3, he27))

def bs(+k: Nat, +i: U32) -> {RG.bases(GM.fresh(k, i)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      MB.and_eq_true(U32.is_eq(P.base((i << 2n : U32)), (i << 2n : U32)), RG.bases(GM.fresh(p, (i + 1 : U32))),
        ME.subst(U32, z => {U32.is_eq(z, (i << 2n : U32)) == True{} : Bool}, (i << 2n : U32), P.base((i << 2n : U32)), Equal.sym(U32, P.base((i << 2n : U32)), (i << 2n : U32), GW.base_shl(i)), Equal.trans(Bool, U32.is_eq((i << 2n : U32), (i << 2n : U32)), Nat.is_eq(U32.to_nat((i << 2n : U32)), U32.to_nat((i << 2n : U32))), True{}, WL.is_eq_to_nat((i << 2n : U32), (i << 2n : U32)), MN.is_eq_refl(U32.to_nat((i << 2n : U32))))), bs(p, (i + 1 : U32)))

def Laws.grown_bases(wc, e, hw, he3, he27):
  bs(U32.to_nat(wc), wc)

# a word at 8 or past it, within the grown store, off a header word below 8
def offh(+e: Nat, +h: U32, +j: U32, +hh: {Nat.is_lt(U32.to_nat(h), 8n) == True{} : Bool}, +hhd: {Nat.is_le(8n, Nat.pow(2n, 3n+e)) == True{} : Bool}, +h8: {Nat.is_le(8n, U32.to_nat(j)) == True{} : Bool}, +hD: {Nat.is_lt(U32.to_nat(j), Nat.pow(2n, 3n+e)) == True{} : Bool}) ->
  {Bool.not(Nat.is_eq(AD.slot(h, 3n+e), AD.slot(j, 3n+e))) == True{} : Bool}:
  +sh = LA.slot_small(h, 3n+e, MN.lt_of_lt_of_le(U32.to_nat(h), 8n, Nat.pow(2n, 3n+e), hh, hhd))
  +sj = LA.slot_small(j, 3n+e, hD)
  +ne = GP.ne_lt(U32.to_nat(h), U32.to_nat(j), MN.lt_of_lt_of_le(U32.to_nat(h), 8n, U32.to_nat(j), hh, h8))
  +ne2 = ME.subst(Nat, q => {Nat.is_eq(q, AD.slot(j, 3n+e)) == False{} : Bool}, U32.to_nat(h), AD.slot(h, 3n+e), Equal.sym(Nat, AD.slot(h, 3n+e), U32.to_nat(h), sh), ME.subst(Nat, q => {Nat.is_eq(U32.to_nat(h), q) == False{} : Bool}, U32.to_nat(j), AD.slot(j, 3n+e), Equal.sym(Nat, AD.slot(j, 3n+e), U32.to_nat(j), sj), ne))
  Equal.cong(Bool, Bool, z => Bool.not(z), Nat.is_eq(AD.slot(h, 3n+e), AD.slot(j, 3n+e)), False{}, ne2)

def off8(+e: Nat, +j: U32, +h8: {Nat.is_le(8n, U32.to_nat(j)) == True{} : Bool}, +hD: {Nat.is_lt(U32.to_nat(j), Nat.pow(2n, 3n+e)) == True{} : Bool}) -> {KMd.off.words(KMd.hdr_all(), 3n+e, j) == True{} : Bool}:
  +hhd = WN.pow_le(3n, 3n+e, MN.le_add_right(3n, e))
  MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), 3n+e), AD.slot(j, 3n+e))), KMd.off.words(KMd.hdr_words(), 3n+e, j), offh(e, P.at_fh(), j, {==}, hhd, h8, hD), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), 3n+e), AD.slot(j, 3n+e))), KMd.off.words(KMd.tab_words(), 3n+e, j), offh(e, P.at_errs(), j, {==}, hhd, h8, hD), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(P.at_tfh(), 3n+e), AD.slot(j, 3n+e))), KMd.off.words([P.at_tn(), P.at_tcap(), P.at_td()], 3n+e, j), offh(e, P.at_tfh(), j, {==}, hhd, h8, hD), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(P.at_tn(), 3n+e), AD.slot(j, 3n+e))), KMd.off.words([P.at_tcap(), P.at_td()], 3n+e, j), offh(e, P.at_tn(), j, {==}, hhd, h8, hD), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(P.at_tcap(), 3n+e), AD.slot(j, 3n+e))), KMd.off.words([P.at_td()], 3n+e, j), offh(e, P.at_tcap(), j, {==}, hhd, h8, hD), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(P.at_td(), 3n+e), AD.slot(j, 3n+e))), KMd.off.words(Nil{}, 3n+e, j), offh(e, P.at_td(), j, {==}, hhd, h8, hD), {==}))))))

def pst(+wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +k: Nat, +i: U32, +hlo: {Nat.is_le(U32.to_nat(wc), U32.to_nat(i)) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(k, U32.to_nat(i)), Nat.pow(2n, 1n+e)) == True{} : Bool}) -> {KMd.past(GM.fresh(k, i), 3n+e) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      +hi = hik(wc, e, hw, he3, he27, p, i, hk)
      +e1 = fi1(wc, e, hw, he3, he27, i, hi)
      +g3 = GP.g32(wc, e, hw, he3, he27, i, hlo)
      +mb = GP.m4b(wc, e, hw, he3, he27, i, hi)
      +n0 = ME.subst(Nat, q => {U32.to_nat((i << 2n : U32)) == q : Nat}, Nat.mul(U32.to_nat(i), 4n), Nat.mul(U32.to_nat(i), 4n), {==}, GP.eH(wc, e, hw, he3, he27, i, hi))
      +h80 = ME.subst(Nat, q => {Nat.is_le(8n, q) == True{} : Bool}, Nat.mul(U32.to_nat(i), 4n), U32.to_nat((i << 2n : U32)), Equal.sym(Nat, U32.to_nat((i << 2n : U32)), Nat.mul(U32.to_nat(i), 4n), n0), MN.le_trans(8n, 32n, Nat.mul(U32.to_nat(i), 4n), {==}, g3))
      +hD0 = ME.subst(Nat, q => {Nat.is_lt(q, Nat.pow(2n, 3n+e)) == True{} : Bool}, Nat.mul(U32.to_nat(i), 4n), U32.to_nat((i << 2n : U32)), Equal.sym(Nat, U32.to_nat((i << 2n : U32)), Nat.mul(U32.to_nat(i), 4n), n0), MN.lt_of_lt_of_le(Nat.mul(U32.to_nat(i), 4n), 4n+Nat.mul(U32.to_nat(i), 4n), Nat.pow(2n, 3n+e), MN.lt_succ_of_le(Nat.mul(U32.to_nat(i), 4n), 3n+Nat.mul(U32.to_nat(i), 4n), MN.le_add_left(Nat.mul(U32.to_nat(i), 4n), 3n)), mb))
      +bk1 = ME.subst(Nat, q => {Nat.is_lt(Nat.add(q, 1n), Nat.pow(2n, 3n+e)) == True{} : Bool}, Nat.mul(U32.to_nat(i), 4n), U32.to_nat((i << 2n : U32)), Equal.sym(Nat, U32.to_nat((i << 2n : U32)), Nat.mul(U32.to_nat(i), 4n), n0), MN.lt_of_lt_of_le(Nat.add(Nat.mul(U32.to_nat(i), 4n), 1n), 4n+Nat.mul(U32.to_nat(i), 4n), Nat.pow(2n, 3n+e), ME.subst(Nat, q => {Nat.is_lt(q, 4n+Nat.mul(U32.to_nat(i), 4n)) == True{} : Bool}, 1n+Nat.mul(U32.to_nat(i), 4n), Nat.add(Nat.mul(U32.to_nat(i), 4n), 1n), MN.add_comm(1n, Nat.mul(U32.to_nat(i), 4n)), MN.lt_succ_of_le(1n+Nat.mul(U32.to_nat(i), 4n), 3n+Nat.mul(U32.to_nat(i), 4n), MN.le_add_left(1n+Nat.mul(U32.to_nat(i), 4n), 2n))), mb))
      +n1 = tnb((i << 2n : U32), 1, 3n+e, bk1, MN.lt_of_lt_of_le(e, 28n, 29n, he27, {==}))
      +h81 = ME.subst(Nat, q => {Nat.is_le(8n, q) == True{} : Bool}, Nat.add(U32.to_nat((i << 2n : U32)), 1n), U32.to_nat(((i << 2n : U32) + 1 : U32)), Equal.sym(Nat, U32.to_nat(((i << 2n : U32) + 1 : U32)), Nat.add(U32.to_nat((i << 2n : U32)), 1n), n1), MN.le_trans(8n, U32.to_nat((i << 2n : U32)), Nat.add(U32.to_nat((i << 2n : U32)), 1n), h80, MN.le_add_right(U32.to_nat((i << 2n : U32)), 1n)))
      +hD1 = ME.subst(Nat, q => {Nat.is_lt(q, Nat.pow(2n, 3n+e)) == True{} : Bool}, Nat.add(U32.to_nat((i << 2n : U32)), 1n), U32.to_nat(((i << 2n : U32) + 1 : U32)), Equal.sym(Nat, U32.to_nat(((i << 2n : U32) + 1 : U32)), Nat.add(U32.to_nat((i << 2n : U32)), 1n), n1), bk1)
      +bk2 = ME.subst(Nat, q => {Nat.is_lt(Nat.add(q, 2n), Nat.pow(2n, 3n+e)) == True{} : Bool}, Nat.mul(U32.to_nat(i), 4n), U32.to_nat((i << 2n : U32)), Equal.sym(Nat, U32.to_nat((i << 2n : U32)), Nat.mul(U32.to_nat(i), 4n), n0), MN.lt_of_lt_of_le(Nat.add(Nat.mul(U32.to_nat(i), 4n), 2n), 4n+Nat.mul(U32.to_nat(i), 4n), Nat.pow(2n, 3n+e), ME.subst(Nat, q => {Nat.is_lt(q, 4n+Nat.mul(U32.to_nat(i), 4n)) == True{} : Bool}, 2n+Nat.mul(U32.to_nat(i), 4n), Nat.add(Nat.mul(U32.to_nat(i), 4n), 2n), MN.add_comm(2n, Nat.mul(U32.to_nat(i), 4n)), MN.lt_succ_of_le(2n+Nat.mul(U32.to_nat(i), 4n), 3n+Nat.mul(U32.to_nat(i), 4n), MN.le_add_left(2n+Nat.mul(U32.to_nat(i), 4n), 1n))), mb))
      +n2 = tnb((i << 2n : U32), 2, 3n+e, bk2, MN.lt_of_lt_of_le(e, 28n, 29n, he27, {==}))
      +h82 = ME.subst(Nat, q => {Nat.is_le(8n, q) == True{} : Bool}, Nat.add(U32.to_nat((i << 2n : U32)), 2n), U32.to_nat(((i << 2n : U32) + 2 : U32)), Equal.sym(Nat, U32.to_nat(((i << 2n : U32) + 2 : U32)), Nat.add(U32.to_nat((i << 2n : U32)), 2n), n2), MN.le_trans(8n, U32.to_nat((i << 2n : U32)), Nat.add(U32.to_nat((i << 2n : U32)), 2n), h80, MN.le_add_right(U32.to_nat((i << 2n : U32)), 2n)))
      +hD2 = ME.subst(Nat, q => {Nat.is_lt(q, Nat.pow(2n, 3n+e)) == True{} : Bool}, Nat.add(U32.to_nat((i << 2n : U32)), 2n), U32.to_nat(((i << 2n : U32) + 2 : U32)), Equal.sym(Nat, U32.to_nat(((i << 2n : U32) + 2 : U32)), Nat.add(U32.to_nat((i << 2n : U32)), 2n), n2), bk2)
      +bk3 = ME.subst(Nat, q => {Nat.is_lt(Nat.add(q, 3n), Nat.pow(2n, 3n+e)) == True{} : Bool}, Nat.mul(U32.to_nat(i), 4n), U32.to_nat((i << 2n : U32)), Equal.sym(Nat, U32.to_nat((i << 2n : U32)), Nat.mul(U32.to_nat(i), 4n), n0), MN.lt_of_lt_of_le(Nat.add(Nat.mul(U32.to_nat(i), 4n), 3n), 4n+Nat.mul(U32.to_nat(i), 4n), Nat.pow(2n, 3n+e), ME.subst(Nat, q => {Nat.is_lt(q, 4n+Nat.mul(U32.to_nat(i), 4n)) == True{} : Bool}, 3n+Nat.mul(U32.to_nat(i), 4n), Nat.add(Nat.mul(U32.to_nat(i), 4n), 3n), MN.add_comm(3n, Nat.mul(U32.to_nat(i), 4n)), MN.lt_succ_of_le(3n+Nat.mul(U32.to_nat(i), 4n), 3n+Nat.mul(U32.to_nat(i), 4n), MN.le_add_left(3n+Nat.mul(U32.to_nat(i), 4n), 0n))), mb))
      +n3 = tnb((i << 2n : U32), 3, 3n+e, bk3, MN.lt_of_lt_of_le(e, 28n, 29n, he27, {==}))
      +h83 = ME.subst(Nat, q => {Nat.is_le(8n, q) == True{} : Bool}, Nat.add(U32.to_nat((i << 2n : U32)), 3n), U32.to_nat(((i << 2n : U32) + 3 : U32)), Equal.sym(Nat, U32.to_nat(((i << 2n : U32) + 3 : U32)), Nat.add(U32.to_nat((i << 2n : U32)), 3n), n3), MN.le_trans(8n, U32.to_nat((i << 2n : U32)), Nat.add(U32.to_nat((i << 2n : U32)), 3n), h80, MN.le_add_right(U32.to_nat((i << 2n : U32)), 3n)))
      +hD3 = ME.subst(Nat, q => {Nat.is_lt(q, Nat.pow(2n, 3n+e)) == True{} : Bool}, Nat.add(U32.to_nat((i << 2n : U32)), 3n), U32.to_nat(((i << 2n : U32) + 3 : U32)), Equal.sym(Nat, U32.to_nat(((i << 2n : U32) + 3 : U32)), Nat.add(U32.to_nat((i << 2n : U32)), 3n), n3), bk3)
      MB.and_eq_true(KMd.ws.off(KMd.nw((i << 2n : U32)), KMd.hdr_all(), 3n+e), KMd.past(GM.fresh(p, (i + 1 : U32)), 3n+e), MB.and_eq_true(KMd.off.words(KMd.hdr_all(), 3n+e, (i << 2n : U32)), KMd.ws.off([((i << 2n : U32) + 1 : U32), ((i << 2n : U32) + 2 : U32), ((i << 2n : U32) + 3 : U32)], KMd.hdr_all(), 3n+e), off8(e, (i << 2n : U32), h80, hD0), MB.and_eq_true(KMd.off.words(KMd.hdr_all(), 3n+e, ((i << 2n : U32) + 1 : U32)), KMd.ws.off([((i << 2n : U32) + 2 : U32), ((i << 2n : U32) + 3 : U32)], KMd.hdr_all(), 3n+e), off8(e, ((i << 2n : U32) + 1 : U32), h81, hD1), MB.and_eq_true(KMd.off.words(KMd.hdr_all(), 3n+e, ((i << 2n : U32) + 2 : U32)), KMd.ws.off([((i << 2n : U32) + 3 : U32)], KMd.hdr_all(), 3n+e), off8(e, ((i << 2n : U32) + 2 : U32), h82, hD2), MB.and_eq_true(KMd.off.words(KMd.hdr_all(), 3n+e, ((i << 2n : U32) + 3 : U32)), KMd.ws.off(Nil{}, KMd.hdr_all(), 3n+e), off8(e, ((i << 2n : U32) + 3 : U32), h83, hD3), {==})))),
        pst(wc, e, hw, he3, he27, p, (i + 1 : U32), lo1(wc, e, hw, he3, he27, i, hlo, e1), kst(wc, e, hw, he3, he27, p, i, hk, e1)))

def Laws.grown_past(wc, e, hw, he3, he27):
  pst(wc, e, hw, he3, he27, U32.to_nat(wc), wc, MN.le_refl(U32.to_nat(wc)), hkw(wc, e, hw, he3, he27))

def gin(+wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +k: Nat, +i: U32, +hk: {Nat.is_le(Nat.add(k, U32.to_nat(i)), Nat.pow(2n, 1n+e)) == True{} : Bool}) -> {RG.nodes.in(GM.fresh(k, i), 3n+e) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      +hi = hik(wc, e, hw, he3, he27, p, i, hk)
      +e1 = fi1(wc, e, hw, he3, he27, i, hi)
      +mb = GP.m4b(wc, e, hw, he3, he27, i, hi)
      +l3 = ME.subst(Nat, q => {Nat.is_lt(q, Nat.pow(2n, 3n+e)) == True{} : Bool}, 3n+Nat.mul(U32.to_nat(i), 4n), Nat.add(Nat.mul(U32.to_nat(i), 4n), 3n), MN.add_comm(3n, Nat.mul(U32.to_nat(i), 4n)), MN.lt_of_lt_of_le(3n+Nat.mul(U32.to_nat(i), 4n), 4n+Nat.mul(U32.to_nat(i), 4n), Nat.pow(2n, 3n+e), MN.lt_succ_of_le(3n+Nat.mul(U32.to_nat(i), 4n), 3n+Nat.mul(U32.to_nat(i), 4n), MN.le_refl(3n+Nat.mul(U32.to_nat(i), 4n))), mb))
      +l4 = ME.subst(Nat, q => {Nat.is_lt(Nat.add(q, 3n), Nat.pow(2n, 3n+e)) == True{} : Bool}, Nat.mul(U32.to_nat(i), 4n), U32.to_nat((i << 2n : U32)), Equal.sym(Nat, U32.to_nat((i << 2n : U32)), Nat.mul(U32.to_nat(i), 4n), GP.eH(wc, e, hw, he3, he27, i, hi)), l3)
      MB.and_eq_true(RG.inr((i << 2n : U32), 3n+e), RG.nodes.in(GM.fresh(p, (i + 1 : U32)), 3n+e), l4, gin(wc, e, hw, he3, he27, p, (i + 1 : U32), kst(wc, e, hw, he3, he27, p, i, hk, e1)))

def Laws.grown_in(wc, e, hw, he3, he27):
  gin(wc, e, hw, he3, he27, U32.to_nat(wc), wc, hkw(wc, e, hw, he3, he27))

# the fresh nodes past the old store
def ab(+wc: U32, +e: Nat, +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}, +he3: {Nat.is_le(3n, e) == True{} : Bool}, +he27: {Nat.is_lt(e, 28n) == True{} : Bool}, +k: Nat, +i: U32, +hlo: {Nat.is_le(U32.to_nat(wc), U32.to_nat(i)) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(k, U32.to_nat(i)), Nat.pow(2n, 1n+e)) == True{} : Bool}) -> {GM.above(GM.fresh(k, i), 2n+e) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      +hi = hik(wc, e, hw, he3, he27, p, i, hk)
      +e1 = fi1(wc, e, hw, he3, he27, i, hi)
      +hx = ME.subst(Nat, q => {Nat.is_le(Nat.pow(2n, 2n+e), q) == True{} : Bool}, Nat.mul(U32.to_nat(i), 4n), U32.to_nat((i << 2n : U32)), Equal.sym(Nat, U32.to_nat((i << 2n : U32)), Nat.mul(U32.to_nat(i), 4n), GP.eH(wc, e, hw, he3, he27, i, hi)), GP.pm(wc, e, hw, he3, he27, i, hlo))
      MB.and_eq_true(Nat.is_le(Nat.pow(2n, 2n+e), U32.to_nat((i << 2n : U32))), GM.above(GM.fresh(p, (i + 1 : U32)), 2n+e), hx, ab(wc, e, hw, he3, he27, p, (i + 1 : U32), lo1(wc, e, hw, he3, he27, i, hlo, e1), kst(wc, e, hw, he3, he27, p, i, hk, e1)))

def Laws.grown_above(wc, e, hw, he3, he27):
  ab(wc, e, hw, he3, he27, U32.to_nat(wc), wc, MN.le_refl(U32.to_nat(wc)), hkw(wc, e, hw, he3, he27))

# two words read alike are one word
def sw(x: Maybe<&2, U32>, y: Maybe<&2, U32>, +h: {LM.same(x, y) == True{} : Bool}) -> {KMd.word.m(x) == KMd.word.m(y) : U32}:
  match x:
    case Some{+p}:
      match y:
        case Some{+q}:
          WL.to_nat_inj(p, q, MN.eq_of_is_eq(U32.to_nat(p), U32.to_nat(q), Equal.trans(Bool, Nat.is_eq(U32.to_nat(p), U32.to_nat(q)), U32.is_eq(p, q), True{}, Equal.sym(Bool, U32.is_eq(p, q), Nat.is_eq(U32.to_nat(p), U32.to_nat(q)), WL.is_eq_to_nat(p, q)), h)))
        case None{}:
          Empty.absurd({KMd.word.m(Some{p}) == KMd.word.m(None{}) : U32}, MB.false_ne_true()(h))
    case None{}:
      match y:
        case Some{+q}:
          Empty.absurd({KMd.word.m(None{}) == KMd.word.m(Some{q}) : U32}, MB.false_ne_true()(h))
        case None{}:
          {==}

# an or true by its right
def or_r(+a: Bool, +b: Bool, +hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  ME.subst(Bool, q => {Bool.or(a, q) == True{} : Bool}, True{}, b, Equal.sym(Bool, b, True{}, hb), MB.or_true(a))

# an or true, its left false: its right true
def or_l(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +h: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  ME.subst(Bool, q => {Bool.or(q, b) == True{} : Bool}, a, False{}, ha, h)

# a tracked node's link word read alike (LM.kept at the node's word 1)
def khas.t(+n: U32, +t: List<&2, U32>, +z: U32, +v: List<&2, U32>, +d: Nat, +v2: List<&2, U32>, +hk: {LM.kept(Con{n, t}, v, d, v2) == True{} : Bool}, +h: {U32.is_eq(n, z) == True{} : Bool}) -> {LM.kept.w((z + 1 : U32), v, d, v2) == True{} : Bool}:
  ME.subst(U32, q => {LM.kept.w((q + 1 : U32), v, d, v2) == True{} : Bool}, n, z, WL.to_nat_inj(n, z, MN.eq_of_is_eq(U32.to_nat(n), U32.to_nat(z), Equal.trans(Bool, Nat.is_eq(U32.to_nat(n), U32.to_nat(z)), U32.is_eq(n, z), True{}, Equal.sym(Bool, U32.is_eq(n, z), Nat.is_eq(U32.to_nat(n), U32.to_nat(z)), WL.is_eq_to_nat(n, z)), h))), MB.eq_true_of_and_left(LM.kept.w((n + 1 : U32), v, d, v2), LM.kept.w((n + 2 : U32), v, d, v2) && (LM.kept.w((n + 3 : U32), v, d, v2) && LM.kept(t, v, d, v2)), MB.eq_true_of_and_right(LM.kept.w(n, v, d, v2), LM.kept.w((n + 1 : U32), v, d, v2) && (LM.kept.w((n + 2 : U32), v, d, v2) && (LM.kept.w((n + 3 : U32), v, d, v2) && LM.kept(t, v, d, v2))), hk)))

def khas(+N: List<&2, U32>, +z: U32, +v: List<&2, U32>, +d: Nat, +v2: List<&2, U32>, +hk: {LM.kept(N, v, d, v2) == True{} : Bool}, +hz: {RG.has(N, z) == True{} : Bool}) -> {LM.kept.w((z + 1 : U32), v, d, v2) == True{} : Bool}:
  match N:
    case Nil{}:
      Empty.absurd({LM.kept.w((z + 1 : U32), v, d, v2) == True{} : Bool}, MB.false_ne_true()(hz))
    case Con{+n, t}:
      GP.bcase(U32.is_eq(n, z), {LM.kept.w((z + 1 : U32), v, d, v2) == True{} : Bool}, h => khas.t(n, t, z, v, d, v2, hk, h),
        h => khas(t, z, v, d, v2, MB.eq_true_of_and_right(LM.kept.w((n + 3 : U32), v, d, v2), LM.kept(t, v, d, v2), MB.eq_true_of_and_right(LM.kept.w((n + 2 : U32), v, d, v2), LM.kept.w((n + 3 : U32), v, d, v2) && LM.kept(t, v, d, v2), MB.eq_true_of_and_right(LM.kept.w((n + 1 : U32), v, d, v2), LM.kept.w((n + 2 : U32), v, d, v2) && (LM.kept.w((n + 3 : U32), v, d, v2) && LM.kept(t, v, d, v2)), MB.eq_true_of_and_right(LM.kept.w(n, v, d, v2), LM.kept.w((n + 1 : U32), v, d, v2) && (LM.kept.w((n + 2 : U32), v, d, v2) && (LM.kept.w((n + 3 : U32), v, d, v2) && LM.kept(t, v, d, v2))), hk)))), or_l(U32.is_eq(n, z), RG.has(t, z), h, hz)))

# the head a faced port keeps off (po.all's base)
def pob(+r: U32, +L: List<&2, U32>, +d: Nat, N: List<&2, U32>, +h: {RG.po.all(r, L, d, N) == True{} : Bool}) -> {KMd.off.port(d, r, P.at_fh()) == True{} : Bool}:
  match N:
    case Nil{}:
      h
    case Con{+n, t}:
      pob(r, L, d, t, MB.eq_true_of_and_right(RG.po.n(r, L, d, n), RG.po.all(r, L, d, t), h))

# a port whose link word lies below 2^d keeps off a word at or past 2^d,
# one level deeper; a static links none
def opj.k(+st: Bool, +r: U32, +d: Nat, +j: U32, +hst: {P.is_static(r) == st : Bool}, +hl: {LM.lw.in(KMd.lw(r), d) == True{} : Bool},
  +hj0: {Nat.is_le(Nat.pow(2n, d), U32.to_nat(j)) == True{} : Bool}, +hj1: {Nat.is_lt(U32.to_nat(j), Nat.pow(2n, 1n+d)) == True{} : Bool}) -> {KMd.off.port(1n+d, r, j) == True{} : Bool}:
  match st:
    case True{}:
      %Equal.sym(Bool, P.is_static(r), True{}, hst) : {KMd.off.lw(KMd.lw.k(_, r), 1n+d, j) == True{} : Bool}
      {==}
    case False{}:
      +hl2 = ME.subst(Bool, q => {LM.lw.in(KMd.lw.k(q, r), d) == True{} : Bool}, P.is_static(r), False{}, hst, hl)
      %Equal.sym(Bool, P.is_static(r), False{}, hst) : {KMd.off.lw(KMd.lw.k(_, r), 1n+d, j) == True{} : Bool}
      +hrD = MN.lt_of_lt_of_le(U32.to_nat((r + 1 : U32)), Nat.pow(2n, d), Nat.pow(2n, 1n+d), hl2, MN.le_of_lt(Nat.pow(2n, d), Nat.pow(2n, 1n+d), AB.pow_lt(d, 1n+d, MN.lt_succ_of_le(d, d, MN.le_refl(d)))))
      +sr = LA.slot_small((r + 1 : U32), 1n+d, hrD)
      +sj = LA.slot_small(j, 1n+d, hj1)
      +ne = GP.ne_lt(U32.to_nat((r + 1 : U32)), U32.to_nat(j), MN.lt_of_lt_of_le(U32.to_nat((r + 1 : U32)), Nat.pow(2n, d), U32.to_nat(j), hl2, hj0))
      +ne2 = ME.subst(Nat, q => {Nat.is_eq(q, AD.slot(j, 1n+d)) == False{} : Bool}, U32.to_nat((r + 1 : U32)), AD.slot((r + 1 : U32), 1n+d), Equal.sym(Nat, AD.slot((r + 1 : U32), 1n+d), U32.to_nat((r + 1 : U32)), sr), ME.subst(Nat, q => {Nat.is_eq(U32.to_nat((r + 1 : U32)), q) == False{} : Bool}, U32.to_nat(j), AD.slot(j, 1n+d), Equal.sym(Nat, AD.slot(j, 1n+d), U32.to_nat(j), sj), ne))
      Equal.cong(Bool, Bool, z => Bool.not(z), Nat.is_eq(AD.slot((r + 1 : U32), 1n+d), AD.slot(j, 1n+d)), False{}, ne2)

def opj(+r: U32, +d: Nat, +j: U32, +hl: {LM.lw.in(KMd.lw(r), d) == True{} : Bool}, +hj0: {Nat.is_le(Nat.pow(2n, d), U32.to_nat(j)) == True{} : Bool}, +hj1: {Nat.is_lt(U32.to_nat(j), Nat.pow(2n, 1n+d)) == True{} : Bool}) -> {KMd.off.port(1n+d, r, j) == True{} : Bool}:
  opj.k(P.is_static(r), r, d, j, {==}, hl, hj0, hj1)

# off the head at d, off it one level deeper: both words below 2^d, their
# slots their numbers at either depth
def opf.k(+st: Bool, +r: U32, +d: Nat, +hst: {P.is_static(r) == st : Bool}, +hl: {LM.lw.in(KMd.lw(r), d) == True{} : Bool}, +hb: {KMd.off.port(d, r, P.at_fh()) == True{} : Bool}) ->
  {KMd.off.port(1n+d, r, P.at_fh()) == True{} : Bool}:
  match st:
    case True{}:
      %Equal.sym(Bool, P.is_static(r), True{}, hst) : {KMd.off.lw(KMd.lw.k(_, r), 1n+d, P.at_fh()) == True{} : Bool}
      {==}
    case False{}:
      +hl2 = ME.subst(Bool, q => {LM.lw.in(KMd.lw.k(q, r), d) == True{} : Bool}, P.is_static(r), False{}, hst, hl)
      +hb2 = ME.subst(Bool, q => {KMd.off.lw(KMd.lw.k(q, r), d, P.at_fh()) == True{} : Bool}, P.is_static(r), False{}, hst, hb)
      %Equal.sym(Bool, P.is_static(r), False{}, hst) : {KMd.off.lw(KMd.lw.k(_, r), 1n+d, P.at_fh()) == True{} : Bool}
      +hrD = MN.lt_of_lt_of_le(U32.to_nat((r + 1 : U32)), Nat.pow(2n, d), Nat.pow(2n, 1n+d), hl2, MN.le_of_lt(Nat.pow(2n, d), Nat.pow(2n, 1n+d), AB.pow_lt(d, 1n+d, MN.lt_succ_of_le(d, d, MN.le_refl(d)))))
      +a1 = ME.subst(Nat, q => {Bool.not(Nat.is_eq(q, AD.slot(P.at_fh(), d))) == True{} : Bool}, AD.slot((r + 1 : U32), d), U32.to_nat((r + 1 : U32)), LA.slot_small((r + 1 : U32), d, hl2), hb2)
      +a2 = ME.subst(Nat, q => {Bool.not(Nat.is_eq(U32.to_nat((r + 1 : U32)), q)) == True{} : Bool}, AD.slot(P.at_fh(), d), U32.to_nat(P.at_fh()), LA.slot_small(P.at_fh(), d, MN.pow_pos(d, 1n)), a1)
      +a3 = ME.subst(Nat, q => {Bool.not(Nat.is_eq(q, U32.to_nat(P.at_fh()))) == True{} : Bool}, U32.to_nat((r + 1 : U32)), AD.slot((r + 1 : U32), 1n+d), Equal.sym(Nat, AD.slot((r + 1 : U32), 1n+d), U32.to_nat((r + 1 : U32)), LA.slot_small((r + 1 : U32), 1n+d, hrD)), a2)
      ME.subst(Nat, q => {Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), 1n+d), q)) == True{} : Bool}, U32.to_nat(P.at_fh()), AD.slot(P.at_fh(), 1n+d), Equal.sym(Nat, AD.slot(P.at_fh(), 1n+d), U32.to_nat(P.at_fh()), LA.slot_small(P.at_fh(), 1n+d, MN.pow_pos(1n+d, 1n))), a3)

def opf(+r: U32, +d: Nat, +hl: {LM.lw.in(KMd.lw(r), d) == True{} : Bool}, +hb: {KMd.off.port(d, r, P.at_fh()) == True{} : Bool}) -> {KMd.off.port(1n+d, r, P.at_fh()) == True{} : Bool}:
  opf.k(P.is_static(r), r, d, {==}, hl, hb)

# a faced port off each fresh node's four words and the head
def pa(+r: U32, +L: List<&2, U32>, +d: Nat, E: List<&2, U32>, +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +hl: {LM.lw.in(KMd.lw(r), d) == True{} : Bool}, +hb: {KMd.off.port(d, r, P.at_fh()) == True{} : Bool},
  +hab: {GM.above(E, d) == True{} : Bool}, +hin: {RG.nodes.in(E, 1n+d) == True{} : Bool}) -> {RG.po.all(r, L, 1n+d, E) == True{} : Bool}:
  match E:
    case Nil{}:
      opf(r, d, hl, hb)
    case Con{+n, t}:
      +hn0 = MB.eq_true_of_and_left(Nat.is_le(Nat.pow(2n, d), U32.to_nat(n)), GM.above(t, d), hab)
      +habt = MB.eq_true_of_and_right(Nat.is_le(Nat.pow(2n, d), U32.to_nat(n)), GM.above(t, d), hab)
      +hr = MB.eq_true_of_and_left(RG.inr(n, 1n+d), RG.nodes.in(t, 1n+d), hin)
      +hint = MB.eq_true_of_and_right(RG.inr(n, 1n+d), RG.nodes.in(t, 1n+d), hin)
      +o0 = opj(r, d, n, hl, hn0, MN.lt_of_le_of_lt(U32.to_nat(n), Nat.add(U32.to_nat(n), 3n), Nat.pow(2n, 1n+d), MN.le_add_right(U32.to_nat(n), 3n), hr))
      +b1 = MN.lt_of_le_of_lt(Nat.add(U32.to_nat(n), 1n), Nat.add(U32.to_nat(n), 3n), Nat.pow(2n, 1n+d), MN.add_le_add_left(1n, 3n, U32.to_nat(n), {==}), hr)
      +e1 = tnb(n, 1, 1n+d, b1, hd)
      +o1 = opj(r, d, (n + 1 : U32), hl, ME.subst(Nat, q => {Nat.is_le(Nat.pow(2n, d), q) == True{} : Bool}, Nat.add(U32.to_nat(n), 1n), U32.to_nat((n + 1 : U32)), Equal.sym(Nat, U32.to_nat((n + 1 : U32)), Nat.add(U32.to_nat(n), 1n), e1), MN.le_trans(Nat.pow(2n, d), U32.to_nat(n), Nat.add(U32.to_nat(n), 1n), hn0, MN.le_add_right(U32.to_nat(n), 1n))), ME.subst(Nat, q => {Nat.is_lt(q, Nat.pow(2n, 1n+d)) == True{} : Bool}, Nat.add(U32.to_nat(n), 1n), U32.to_nat((n + 1 : U32)), Equal.sym(Nat, U32.to_nat((n + 1 : U32)), Nat.add(U32.to_nat(n), 1n), e1), b1))
      +b2 = MN.lt_of_le_of_lt(Nat.add(U32.to_nat(n), 2n), Nat.add(U32.to_nat(n), 3n), Nat.pow(2n, 1n+d), MN.add_le_add_left(2n, 3n, U32.to_nat(n), {==}), hr)
      +e2 = tnb(n, 2, 1n+d, b2, hd)
      +o2 = opj(r, d, (n + 2 : U32), hl, ME.subst(Nat, q => {Nat.is_le(Nat.pow(2n, d), q) == True{} : Bool}, Nat.add(U32.to_nat(n), 2n), U32.to_nat((n + 2 : U32)), Equal.sym(Nat, U32.to_nat((n + 2 : U32)), Nat.add(U32.to_nat(n), 2n), e2), MN.le_trans(Nat.pow(2n, d), U32.to_nat(n), Nat.add(U32.to_nat(n), 2n), hn0, MN.le_add_right(U32.to_nat(n), 2n))), ME.subst(Nat, q => {Nat.is_lt(q, Nat.pow(2n, 1n+d)) == True{} : Bool}, Nat.add(U32.to_nat(n), 2n), U32.to_nat((n + 2 : U32)), Equal.sym(Nat, U32.to_nat((n + 2 : U32)), Nat.add(U32.to_nat(n), 2n), e2), b2))
      +b3 = MN.lt_of_le_of_lt(Nat.add(U32.to_nat(n), 3n), Nat.add(U32.to_nat(n), 3n), Nat.pow(2n, 1n+d), MN.add_le_add_left(3n, 3n, U32.to_nat(n), {==}), hr)
      +e3 = tnb(n, 3, 1n+d, b3, hd)
      +o3 = opj(r, d, (n + 3 : U32), hl, ME.subst(Nat, q => {Nat.is_le(Nat.pow(2n, d), q) == True{} : Bool}, Nat.add(U32.to_nat(n), 3n), U32.to_nat((n + 3 : U32)), Equal.sym(Nat, U32.to_nat((n + 3 : U32)), Nat.add(U32.to_nat(n), 3n), e3), MN.le_trans(Nat.pow(2n, d), U32.to_nat(n), Nat.add(U32.to_nat(n), 3n), hn0, MN.le_add_right(U32.to_nat(n), 3n))), ME.subst(Nat, q => {Nat.is_lt(q, Nat.pow(2n, 1n+d)) == True{} : Bool}, Nat.add(U32.to_nat(n), 3n), U32.to_nat((n + 3 : U32)), Equal.sym(Nat, U32.to_nat((n + 3 : U32)), Nat.add(U32.to_nat(n), 3n), e3), b3))
      +pn = MB.and_eq_true(KMd.off.port(1n+d, r, n), Bool.or(RG.has(L, n), KMd.off.port(1n+d, r, (n + 1 : U32)) && (KMd.off.port(1n+d, r, (n + 2 : U32)) && KMd.off.port(1n+d, r, (n + 3 : U32)))), o0,
        or_r(RG.has(L, n), KMd.off.port(1n+d, r, (n + 1 : U32)) && (KMd.off.port(1n+d, r, (n + 2 : U32)) && KMd.off.port(1n+d, r, (n + 3 : U32))), MB.and_eq_true(KMd.off.port(1n+d, r, (n + 1 : U32)), KMd.off.port(1n+d, r, (n + 2 : U32)) && KMd.off.port(1n+d, r, (n + 3 : U32)), o1, MB.and_eq_true(KMd.off.port(1n+d, r, (n + 2 : U32)), KMd.off.port(1n+d, r, (n + 3 : U32)), o2, o3))))
      MB.and_eq_true(RG.po.n(r, L, 1n+d, n), RG.po.all(r, L, 1n+d, t), pn, pa(r, L, d, t, hd, hl, hb, habt, hint))

# each cursor's faced port so, one by one
def pxo(ys: List<&2, U32>, +v: List<&2, U32>, +v2: List<&2, U32>, +d: Nat, +L: List<&2, U32>, +N: List<&2, U32>, +E: List<&2, U32>, +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool},
  +hs: {RG.sub(ys, N) == True{} : Bool}, +hk: {LM.kept(N, v, d, v2) == True{} : Bool}, +hfi: {LM.faced.in(ys, v, d) == True{} : Bool}, +hpo: {RG.px.off(ys, v, d, L, N) == True{} : Bool},
  +hab: {GM.above(E, d) == True{} : Bool}, +hin: {RG.nodes.in(E, 1n+d) == True{} : Bool}) -> {RG.px.off(ys, v2, 1n+d, L, E) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+z, t}:
      +hz = MB.eq_true_of_and_left(RG.has(N, z), RG.sub(t, N), hs)
      +hst = MB.eq_true_of_and_right(RG.has(N, z), RG.sub(t, N), hs)
      +hl = MB.eq_true_of_and_left(LM.lw.in(KMd.lw(KMd.word(v, d, (z + 1 : U32))), d), LM.faced.in(t, v, d), hfi)
      +hft = MB.eq_true_of_and_right(LM.lw.in(KMd.lw(KMd.word(v, d, (z + 1 : U32))), d), LM.faced.in(t, v, d), hfi)
      +hp = MB.eq_true_of_and_left(RG.po.all(KMd.word(v, d, (z + 1 : U32)), L, d, N), RG.px.off(t, v, d, L, N), hpo)
      +hpt = MB.eq_true_of_and_right(RG.po.all(KMd.word(v, d, (z + 1 : U32)), L, d, N), RG.px.off(t, v, d, L, N), hpo)
      +we = sw(List.get(&2, U32, v2, AD.slot((z + 1 : U32), 1n+d)), List.get(&2, U32, v, AD.slot((z + 1 : U32), d)), khas(N, z, v, d, v2, hk, hz))
      +pz = pa(KMd.word(v, d, (z + 1 : U32)), L, d, E, hd, hl, pob(KMd.word(v, d, (z + 1 : U32)), L, d, N, hp), hab, hin)
      +pz2 = ME.subst(U32, q => {RG.po.all(q, L, 1n+d, E) == True{} : Bool}, KMd.word(v, d, (z + 1 : U32)), KMd.word(v2, 1n+d, (z + 1 : U32)), Equal.sym(U32, KMd.word(v2, 1n+d, (z + 1 : U32)), KMd.word(v, d, (z + 1 : U32)), we), pz)
      MB.and_eq_true(RG.po.all(KMd.word(v2, 1n+d, (z + 1 : U32)), L, 1n+d, E), RG.px.off(t, v2, 1n+d, L, E), pz2, pxo(t, v, v2, d, L, N, E, hd, hst, hk, hft, hpt, hab, hin))

def Laws.grown_ports(v, v2, d, L, N, E, hd, hs, hk, hfi, hpo, hab, hin):
  pxo(L, v, v2, d, L, N, E, hd, hs, hk, hfi, hpo, hab, hin)

# a link word in range at d is in range one level deeper
def lwu.k(+st: Bool, +r: U32, +d: Nat, +hst: {P.is_static(r) == st : Bool}, +hl: {LM.lw.in(KMd.lw(r), d) == True{} : Bool}) -> {LM.lw.in(KMd.lw(r), 1n+d) == True{} : Bool}:
  match st:
    case True{}:
      %Equal.sym(Bool, P.is_static(r), True{}, hst) : {LM.lw.in(KMd.lw.k(_, r), 1n+d) == True{} : Bool}
      {==}
    case False{}:
      +hl2 = ME.subst(Bool, q => {LM.lw.in(KMd.lw.k(q, r), d) == True{} : Bool}, P.is_static(r), False{}, hst, hl)
      %Equal.sym(Bool, P.is_static(r), False{}, hst) : {LM.lw.in(KMd.lw.k(_, r), 1n+d) == True{} : Bool}
      MN.lt_of_lt_of_le(U32.to_nat((r + 1 : U32)), Nat.pow(2n, d), Nat.pow(2n, 1n+d), hl2, MN.le_of_lt(Nat.pow(2n, d), Nat.pow(2n, 1n+d), AB.pow_lt(d, 1n+d, MN.lt_succ_of_le(d, d, MN.le_refl(d)))))

def lwu(+r: U32, +d: Nat, +hl: {LM.lw.in(KMd.lw(r), d) == True{} : Bool}) -> {LM.lw.in(KMd.lw(r), 1n+d) == True{} : Bool}:
  lwu.k(P.is_static(r), r, d, {==}, hl)

def gfo(ys: List<&2, U32>, +v: List<&2, U32>, +v2: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +hs: {RG.sub(ys, N) == True{} : Bool}, +hk: {LM.kept(N, v, d, v2) == True{} : Bool},
  +hfi: {LM.faced.in(ys, v, d) == True{} : Bool}) -> {LM.faced.in(ys, v2, 1n+d) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+z, t}:
      +hz = MB.eq_true_of_and_left(RG.has(N, z), RG.sub(t, N), hs)
      +hst = MB.eq_true_of_and_right(RG.has(N, z), RG.sub(t, N), hs)
      +hl = MB.eq_true_of_and_left(LM.lw.in(KMd.lw(KMd.word(v, d, (z + 1 : U32))), d), LM.faced.in(t, v, d), hfi)
      +hft = MB.eq_true_of_and_right(LM.lw.in(KMd.lw(KMd.word(v, d, (z + 1 : U32))), d), LM.faced.in(t, v, d), hfi)
      +we = sw(List.get(&2, U32, v2, AD.slot((z + 1 : U32), 1n+d)), List.get(&2, U32, v, AD.slot((z + 1 : U32), d)), khas(N, z, v, d, v2, hk, hz))
      +lz = ME.subst(U32, q => {LM.lw.in(KMd.lw(q), 1n+d) == True{} : Bool}, KMd.word(v, d, (z + 1 : U32)), KMd.word(v2, 1n+d, (z + 1 : U32)), Equal.sym(U32, KMd.word(v2, 1n+d, (z + 1 : U32)), KMd.word(v, d, (z + 1 : U32)), we), lwu(KMd.word(v, d, (z + 1 : U32)), d, hl))
      MB.and_eq_true(LM.lw.in(KMd.lw(KMd.word(v2, 1n+d, (z + 1 : U32))), 1n+d), LM.faced.in(t, v2, 1n+d), lz, gfo(t, v, v2, d, N, hst, hk, hft))

def Laws.grown_faced(v, v2, d, L, N, hs, hk, hfi):
  gfo(L, v, v2, d, N, hs, hk, hfi)
