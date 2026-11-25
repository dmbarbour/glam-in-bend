# Proofs of glam/MATERIALIZE_LAWS.bend: the laws of positioned demand and
# of the index composed as laws, their proof files imported to fill them.
#
# Lessons:
# - A serve's end is reached by rewriting its inputs where the code reads
#   them, in the order it reads them: the find, the find's answer, the
#   check. Each motive is the goal with the read left a hole; the code
#   between reduces.
# - A verdict's cost is mostly its imports': materialize.bend's 85 s, the
#   hub's string.bend 75 s more (2026-11-24, Bend 2.0.39), which the
#   index's proofs took for u32_eq_of_is_eq alone, copied now
#   (vendor/bend-mathlib/u32_eq.bend). Time a file of the imports alone and one trivial
#   def before blaming the proofs.
# - The laws' arrays, named by several laws' arguments, are mirrored
#   (fj2.m, fj1.m): each premise over an array carried onto its tree's
#   array, the end carried back.

import Base
import ./MATERIALIZE_LAWS.bend as Laws
import ./POSITION_LAWS.bend as PL
import ./POSITION_PROOF.bend as PP
import ./INDEX_LAWS.bend as XL
import ./INDEX_PROOF.bend as XP
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/knet.bend as KN
import ../spike/krules.bend as KR
import ../spike/kmodel.bend as KMd
import ./position.bend as Q
import ./position_model.bend as QM
import ./ring.bend as R
import ./index.bend as X
import ./index_model.bend as IM
import ./materialize.bend as M
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_base.bend as LAB
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT

# the serve's end over the host's words as a mirror's tree
def fj2.k(w: Array<U32>, a: Array<V.Val>, +d: Nat, +hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hwd: {Pair.snd(P.H, Bool, KN.wired_ok(P.H{KM.MG{w}, a})) == True{} : Bool}, +j: U32, +p: U32, +hj: {U32.is_le(P.first(), j) == True{} : Bool}, hjc: {U32.is_lt(j, KMd.word(AD.view(U32, w), d, P.at_wcap())) == True{} : Bool}, hpa: {U32.is_lt(p, KR.kind_arity(P.rk(KMd.word(AD.view(U32, w), d, (j << 2n : U32))))) == True{} : Bool}, +pos: U32, +hpos: {pos == ((j << 2n : U32) + p : U32) : U32}, +hns: {P.is_static(pos) == False{} : Bool}, +q: U32, +n: U32, hfa: {QM.front.at(Q.PdFront{P.H{KM.MG{w}, a}, q, n}, pos) == True{} : Bool}, +th: LAT.Tree<U32>, ah: Array<V.Val>, +dh: Nat, hfh: {AD.full(U32, LAT.fromT(U32, th), dh) == True{} : Bool}, +hdh32: {Nat.is_lt(dh, 32n) == True{} : Bool}, +situ: U32, +I: IM.Ix, +hr: {IM.ix.real(AD.view(U32, LAT.fromT(U32, th)), dh, situ, I) == True{} : Bool}, hi: {IM.ix.inv(I) == True{} : Bool}, +nc: U32, +hn: {KMd.word(AD.view(U32, LAT.fromT(U32, th)), dh, (nc + 2 : U32)) == pos : U32}, +k: U32, +c: U32, +hc: {IM.ix.look(I, q) == Some{c} : Maybe<&2, U32>}) ->
  {M.sv.pd(Q.PdFront{P.H{KM.MG{w}, a}, q, n}, P.H{KM.MG{LAT.fromT(U32, th)}, ah}, situ, k, nc, pos) == M.SvOk{P.H{KM.MG{w}, a}, R.join(P.H{KM.MG{LAT.fromT(U32, th)}, ah}, nc, c), n, 1} : M.Sv}:
  +hne = PL.front_apart(w, a, d, hf, hd32, hwd, j, p, hj, hjc, hpa, pos, hpos, hns, q, n, hfa)
  +hca = XL.found_apart(AD.view(U32, LAT.fromT(U32, th)), dh, situ, I, q, pos, c, nc, hr, hc, hn, hne)
  +hft = XL.find_tree(LAT.fromT(U32, th), ah, dh, situ, I, q, hfh, hdh32, hr, hi)
  %Equal.sym(P.H & Maybe<&2, U32>, X.ix.find(P.H{KM.MG{LAT.fromT(U32, th)}, ah}, situ, q), (P.H{KM.MG{LAT.fromT(U32, th)}, ah}, IM.ix.look(I, q)), hft) : {M.sv.front.m(_, P.H{KM.MG{w}, a}, situ, k, nc, q, n) == M.SvOk{P.H{KM.MG{w}, a}, R.join(P.H{KM.MG{LAT.fromT(U32, th)}, ah}, nc, c), n, 1} : M.Sv}
  %Equal.sym(Maybe<&2, U32>, IM.ix.look(I, q), Some{c}, hc) : {M.sv.front.m((P.H{KM.MG{LAT.fromT(U32, th)}, ah}, _), P.H{KM.MG{w}, a}, situ, k, nc, q, n) == M.SvOk{P.H{KM.MG{w}, a}, R.join(P.H{KM.MG{LAT.fromT(U32, th)}, ah}, nc, c), n, 1} : M.Sv}
  %Equal.sym(Bool, U32.is_eq(c, nc), False{}, hca) : {M.sv.front.c(_, P.H{KM.MG{w}, a}, P.H{KM.MG{LAT.fromT(U32, th)}, ah}, nc, c, n) == M.SvOk{P.H{KM.MG{w}, a}, R.join(P.H{KM.MG{LAT.fromT(U32, th)}, ah}, nc, c), n, 1} : M.Sv}
  {==}

def fj2.m(w: Array<U32>, a: Array<V.Val>, +d: Nat, +hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hwd: {Pair.snd(P.H, Bool, KN.wired_ok(P.H{KM.MG{w}, a})) == True{} : Bool}, +j: U32, +p: U32, +hj: {U32.is_le(P.first(), j) == True{} : Bool}, hjc: {U32.is_lt(j, KMd.word(AD.view(U32, w), d, P.at_wcap())) == True{} : Bool}, hpa: {U32.is_lt(p, KR.kind_arity(P.rk(KMd.word(AD.view(U32, w), d, (j << 2n : U32))))) == True{} : Bool}, +pos: U32, +hpos: {pos == ((j << 2n : U32) + p : U32) : U32}, +hns: {P.is_static(pos) == False{} : Bool}, +q: U32, +n: U32, hfa: {QM.front.at(Q.PdFront{P.H{KM.MG{w}, a}, q, n}, pos) == True{} : Bool}, -wh: Array<U32>, ah: Array<V.Val>, +dh: Nat, hfh: {AD.full(U32, wh, dh) == True{} : Bool}, +hdh32: {Nat.is_lt(dh, 32n) == True{} : Bool}, +situ: U32, +I: IM.Ix, +hr: {IM.ix.real(AD.view(U32, wh), dh, situ, I) == True{} : Bool}, hi: {IM.ix.inv(I) == True{} : Bool}, +nc: U32, +hn: {KMd.word(AD.view(U32, wh), dh, (nc + 2 : U32)) == pos : U32}, +k: U32, +c: U32, +hc: {IM.ix.look(I, q) == Some{c} : Maybe<&2, U32>}, mh: LAT.Mirror(U32, wh)) ->
  {M.sv.pd(Q.PdFront{P.H{KM.MG{w}, a}, q, n}, P.H{KM.MG{wh}, ah}, situ, k, nc, pos) == M.SvOk{P.H{KM.MG{w}, a}, R.join(P.H{KM.MG{wh}, ah}, nc, c), n, 1} : M.Sv}:
  (+th, +eh) = mh
  +hfh2 = LAB.subst(Array<U32>, x => {AD.full(U32, x, dh) == True{} : Bool}, wh, LAT.fromT(U32, th), Equal.sym(Array<U32>, LAT.fromT(U32, th), wh, eh), hfh)
  +hr2 = LAB.subst(Array<U32>, x => {IM.ix.real(AD.view(U32, x), dh, situ, I) == True{} : Bool}, wh, LAT.fromT(U32, th), Equal.sym(Array<U32>, LAT.fromT(U32, th), wh, eh), hr)
  +hn2 = LAB.subst(Array<U32>, x => {KMd.word(AD.view(U32, x), dh, (nc + 2 : U32)) == pos : U32}, wh, LAT.fromT(U32, th), Equal.sym(Array<U32>, LAT.fromT(U32, th), wh, eh), hn)
  LAB.subst(Array<U32>, x => {M.sv.pd(Q.PdFront{P.H{KM.MG{w}, a}, q, n}, P.H{KM.MG{x}, ah}, situ, k, nc, pos) == M.SvOk{P.H{KM.MG{w}, a}, R.join(P.H{KM.MG{x}, ah}, nc, c), n, 1} : M.Sv}, LAT.fromT(U32, th), wh, eh, fj2.k(w, a, d, hf, hd32, hwd, j, p, hj, hjc, hpa, pos, hpos, hns, q, n, hfa, th, ah, dh, hfh2, hdh32, situ, I, hr2, hi, nc, hn2, k, c, hc))

def Laws.front_joins(w, a, d, hf, hd32, hwd, j, p, hj, hjc, hpa, pos, hpos, hns, q, n, hfa, wh, ah, dh, hfh, hdh32, situ, I, hr, hi, nc, hn, k, c, hc):
  fj2.m(w, a, d, hf, hd32, hwd, j, p, hj, hjc, hpa, pos, hpos, hns, q, n, hfa, wh, ah, dh, hfh, hdh32, situ, I, hr, hi, nc, hn, k, c, hc, LAT.mirror(U32, wh))

# the one-net serve's end over the words and values as mirrors' trees
def fj1.k(+th: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +hf: {AD.full(U32, LAT.fromT(U32, th), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hwd: {Pair.snd(P.H, Bool, KN.wired_ok(P.H{KM.MG{LAT.fromT(U32, th)}, LAT.fromT(V.Val, ta)})) == True{} : Bool}, +j: U32, +p: U32, +hj: {U32.is_le(P.first(), j) == True{} : Bool}, hjc: {U32.is_lt(j, KMd.word(AD.view(U32, LAT.fromT(U32, th)), d, P.at_wcap())) == True{} : Bool}, hpa: {U32.is_lt(p, KR.kind_arity(P.rk(KMd.word(AD.view(U32, LAT.fromT(U32, th)), d, (j << 2n : U32))))) == True{} : Bool}, +pos: U32, +hpos: {pos == ((j << 2n : U32) + p : U32) : U32}, +hns: {P.is_static(pos) == False{} : Bool}, +q: U32, +n: U32, hfa: {QM.front.at(Q.PdFront{P.H{KM.MG{LAT.fromT(U32, th)}, LAT.fromT(V.Val, ta)}, q, n}, pos) == True{} : Bool}, +situ: U32, +I: IM.Ix, +hr: {IM.ix.real(AD.view(U32, LAT.fromT(U32, th)), d, situ, I) == True{} : Bool}, hi: {IM.ix.inv(I) == True{} : Bool}, +nc: U32, +hn: {KMd.word(AD.view(U32, LAT.fromT(U32, th)), d, (nc + 2 : U32)) == pos : U32}, +k: U32, +c: U32, +hc: {IM.ix.look(I, q) == Some{c} : Maybe<&2, U32>}) ->
  {M.sv1.pd(Q.PdFront{P.H{KM.MG{LAT.fromT(U32, th)}, LAT.fromT(V.Val, ta)}, q, n}, situ, k, nc, pos) == M.S1Ok{R.join(P.H{KM.MG{LAT.fromT(U32, th)}, LAT.fromT(V.Val, ta)}, nc, c), n, 1} : M.Sv1}:
  +hne = PL.front_apart(LAT.fromT(U32, th), LAT.fromT(V.Val, ta), d, hf, hd32, hwd, j, p, hj, hjc, hpa, pos, hpos, hns, q, n, hfa)
  +hca = XL.found_apart(AD.view(U32, LAT.fromT(U32, th)), d, situ, I, q, pos, c, nc, hr, hc, hn, hne)
  +hft = XL.find_tree(LAT.fromT(U32, th), LAT.fromT(V.Val, ta), d, situ, I, q, hf, hd32, hr, hi)
  %Equal.sym(P.H & Maybe<&2, U32>, X.ix.find(P.H{KM.MG{LAT.fromT(U32, th)}, LAT.fromT(V.Val, ta)}, situ, q), (P.H{KM.MG{LAT.fromT(U32, th)}, LAT.fromT(V.Val, ta)}, IM.ix.look(I, q)), hft) : {M.sv1.front.m(_, situ, k, nc, q, n) == M.S1Ok{R.join(P.H{KM.MG{LAT.fromT(U32, th)}, LAT.fromT(V.Val, ta)}, nc, c), n, 1} : M.Sv1}
  %Equal.sym(Maybe<&2, U32>, IM.ix.look(I, q), Some{c}, hc) : {M.sv1.front.m((P.H{KM.MG{LAT.fromT(U32, th)}, LAT.fromT(V.Val, ta)}, _), situ, k, nc, q, n) == M.S1Ok{R.join(P.H{KM.MG{LAT.fromT(U32, th)}, LAT.fromT(V.Val, ta)}, nc, c), n, 1} : M.Sv1}
  %Equal.sym(Bool, U32.is_eq(c, nc), False{}, hca) : {M.sv1.front.c(_, P.H{KM.MG{LAT.fromT(U32, th)}, LAT.fromT(V.Val, ta)}, nc, c, n) == M.S1Ok{R.join(P.H{KM.MG{LAT.fromT(U32, th)}, LAT.fromT(V.Val, ta)}, nc, c), n, 1} : M.Sv1}
  {==}

def fj1.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hwd: {Pair.snd(P.H, Bool, KN.wired_ok(P.H{KM.MG{w}, a})) == True{} : Bool}, +j: U32, +p: U32, +hj: {U32.is_le(P.first(), j) == True{} : Bool}, hjc: {U32.is_lt(j, KMd.word(AD.view(U32, w), d, P.at_wcap())) == True{} : Bool}, hpa: {U32.is_lt(p, KR.kind_arity(P.rk(KMd.word(AD.view(U32, w), d, (j << 2n : U32))))) == True{} : Bool}, +pos: U32, +hpos: {pos == ((j << 2n : U32) + p : U32) : U32}, +hns: {P.is_static(pos) == False{} : Bool}, +q: U32, +n: U32, hfa: {QM.front.at(Q.PdFront{P.H{KM.MG{w}, a}, q, n}, pos) == True{} : Bool}, +situ: U32, +I: IM.Ix, +hr: {IM.ix.real(AD.view(U32, w), d, situ, I) == True{} : Bool}, hi: {IM.ix.inv(I) == True{} : Bool}, +nc: U32, +hn: {KMd.word(AD.view(U32, w), d, (nc + 2 : U32)) == pos : U32}, +k: U32, +c: U32, +hc: {IM.ix.look(I, q) == Some{c} : Maybe<&2, U32>}, m0: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {M.sv1.pd(Q.PdFront{P.H{KM.MG{w}, a}, q, n}, situ, k, nc, pos) == M.S1Ok{R.join(P.H{KM.MG{w}, a}, nc, c), n, 1} : M.Sv1}:
  (+th, +ew) = m0
  (+ta, +ea) = ma
  +hfw = LAB.subst(Array<U32>, x => {AD.full(U32, x, d) == True{} : Bool}, w, LAT.fromT(U32, th), Equal.sym(Array<U32>, LAT.fromT(U32, th), w, ew), hf)
  +hwdw = LAB.subst(Array<U32>, x => {Pair.snd(P.H, Bool, KN.wired_ok(P.H{KM.MG{x}, a})) == True{} : Bool}, w, LAT.fromT(U32, th), Equal.sym(Array<U32>, LAT.fromT(U32, th), w, ew), hwd)
  +hwda = LAB.subst(Array<V.Val>, x => {Pair.snd(P.H, Bool, KN.wired_ok(P.H{KM.MG{LAT.fromT(U32, th)}, x})) == True{} : Bool}, a, LAT.fromT(V.Val, ta), Equal.sym(Array<V.Val>, LAT.fromT(V.Val, ta), a, ea), hwdw)
  +hjcw = LAB.subst(Array<U32>, x => {U32.is_lt(j, KMd.word(AD.view(U32, x), d, P.at_wcap())) == True{} : Bool}, w, LAT.fromT(U32, th), Equal.sym(Array<U32>, LAT.fromT(U32, th), w, ew), hjc)
  +hpaw = LAB.subst(Array<U32>, x => {U32.is_lt(p, KR.kind_arity(P.rk(KMd.word(AD.view(U32, x), d, (j << 2n : U32))))) == True{} : Bool}, w, LAT.fromT(U32, th), Equal.sym(Array<U32>, LAT.fromT(U32, th), w, ew), hpa)
  +hfaw = LAB.subst(Array<U32>, x => {QM.front.at(Q.PdFront{P.H{KM.MG{x}, a}, q, n}, pos) == True{} : Bool}, w, LAT.fromT(U32, th), Equal.sym(Array<U32>, LAT.fromT(U32, th), w, ew), hfa)
  +hfaa = LAB.subst(Array<V.Val>, x => {QM.front.at(Q.PdFront{P.H{KM.MG{LAT.fromT(U32, th)}, x}, q, n}, pos) == True{} : Bool}, a, LAT.fromT(V.Val, ta), Equal.sym(Array<V.Val>, LAT.fromT(V.Val, ta), a, ea), hfaw)
  +hrw = LAB.subst(Array<U32>, x => {IM.ix.real(AD.view(U32, x), d, situ, I) == True{} : Bool}, w, LAT.fromT(U32, th), Equal.sym(Array<U32>, LAT.fromT(U32, th), w, ew), hr)
  +hnw = LAB.subst(Array<U32>, x => {KMd.word(AD.view(U32, x), d, (nc + 2 : U32)) == pos : U32}, w, LAT.fromT(U32, th), Equal.sym(Array<U32>, LAT.fromT(U32, th), w, ew), hn)
  +gt = fj1.k(th, ta, d, hfw, hd32, hwda, j, p, hj, hjcw, hpaw, pos, hpos, hns, q, n, hfaa, situ, I, hrw, hi, nc, hnw, k, c, hc)
  +ga = LAB.subst(Array<V.Val>, x => {M.sv1.pd(Q.PdFront{P.H{KM.MG{LAT.fromT(U32, th)}, x}, q, n}, situ, k, nc, pos) == M.S1Ok{R.join(P.H{KM.MG{LAT.fromT(U32, th)}, x}, nc, c), n, 1} : M.Sv1}, LAT.fromT(V.Val, ta), a, ea, gt)
  LAB.subst(Array<U32>, x => {M.sv1.pd(Q.PdFront{P.H{KM.MG{x}, a}, q, n}, situ, k, nc, pos) == M.S1Ok{R.join(P.H{KM.MG{x}, a}, nc, c), n, 1} : M.Sv1}, LAT.fromT(U32, th), w, ew, ga)

def Laws.front_joins1(w, a, d, hf, hd32, hwd, j, p, hj, hjc, hpa, pos, hpos, hns, q, n, hfa, situ, I, hr, hi, nc, hn, k, c, hc):
  fj1.m(w, a, d, hf, hd32, hwd, j, p, hj, hjc, hpa, pos, hpos, hns, q, n, hfa, situ, I, hr, hi, nc, hn, k, c, hc, LAT.mirror(U32, w), LAT.mirror(V.Val, a))
