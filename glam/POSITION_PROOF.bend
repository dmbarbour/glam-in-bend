# Proofs of glam/POSITION_LAWS.bend: positioned demand's frontier
# (cursor-laws.noself.frontier.faces).
#
# Lessons (docs/Proving.md has them too):
# - Both of a frontier's makers read it as the position's link word
#   (pd.peer), and the reads after hand the heap back, so the frontier
#   faces the position in its own heap whatever the walks did: no premise.
#   Each place a frontier is made mirrors its own heap (peer_front).
# - The loop's step is one lemma that walks pd.q's branches to the end
#   each makes, settling it there: a frontier by the reads, a stop or a
#   value at once, a read again by the induction, passed as a function
#   (ih) of the next heap. A lemma about pd.q's result and a match on it
#   would name the heap twice.
# - The induction is a lambda calling the lemma on the smaller count
#   (front_loop), which Bend accepts as decreasing.
# - The walk's state was matched on U32 literals (pd.ended.k), stuck in a
#   proof's default arm: tested now (pd.ended.b), measured unchanged.
# - The frontier apart from the position (front_apart) is front_faces' fact
#   and wired_port's check of the position's port: its link a static
#   eraser, which a port that is no static cannot be, or no port of its
#   own reference. It calls wired_port as a law, so the wiring's proof
#   file is imported to fill it.

import Base
import ./POSITION_LAWS.bend as Laws
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/knet.bend as KN
import ../spike/kdemand.bend as KD
import ../spike/kernel.bend as K
import ./position.bend as Q
import ./position_model.bend as QM
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MN
import 0x8ae61ec3a6615abd35f196c07232ad28/u32.bend as MU
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/LAWS.bend as LA
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/PROOF.bend as LAP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_base.bend as LAB
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME
import ../spike/WIRED_PROOF.bend as WIP
import ../spike/WIRED_LAWS.bend as WI
import ../spike/wired_model.bend as WR
import ../spike/kmodel.bend as KMd
import ../spike/krules.bend as KR

def hw(+t0: LAT.Tree<U32>, +x: U32) -> U32:
  Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), x))

def hp(+t0: LAT.Tree<U32>, a: Array<V.Val>) -> P.H:
  P.H{KM.MG{LAT.fromT(U32, t0)}, a}

def rd_back(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +i: U32) -> {P.rd(hp(t0, a), i) == (hp(t0, a), hw(t0, i)) : P.H & U32}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), i), (LAT.fromT(U32, t0), hw(t0, i)), LA.get_pair(U32, LAT.fromT(U32, t0), i)) :
    {P.rd.fin(KM.m_get.fin(_), a) == (hp(t0, a), hw(t0, i)) : P.H & U32}
  {==}

def u32_refl(+x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  Equal.trans(Bool, U32.is_eq(x, x), Nat.is_eq(U32.to_nat(x), U32.to_nat(x)), True{}, MU.u32_is_eq_to_nat(x, x), MN.is_eq_refl(U32.to_nat(x)))

# a frontier made from the position's link word faces it
def pf.k(+cur: Bool, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +pos: U32, +n: U32) -> {QM.front.at(Q.pd.f.k(cur, hp(t0, a), hw(t0, (pos + 1 : U32)), n), pos) == True{} : Bool}:
  match cur:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(P.H & U32, P.rd(hp(t0, a), (pos + 1 : U32)), (hp(t0, a), hw(t0, (pos + 1 : U32))), rd_back(t0, a, (pos + 1 : U32))) :
        {U32.is_eq(Pair.snd(P.H, U32, _), hw(t0, (pos + 1 : U32))) == True{} : Bool}
      u32_refl(hw(t0, (pos + 1 : U32)))

def pf.p(+pr: Bool, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +pos: U32, +n: U32) -> {QM.front.at(Q.pd.f.p(pr, hp(t0, a), hw(t0, (pos + 1 : U32)), n), pos) == True{} : Bool}:
  match pr:
    case True{}:
      %Equal.sym(P.H & U32, P.rd(hp(t0, a), P.base(hw(t0, (pos + 1 : U32)))), (hp(t0, a), hw(t0, P.base(hw(t0, (pos + 1 : U32))))), rd_back(t0, a, P.base(hw(t0, (pos + 1 : U32))))) :
        {QM.front.at(Q.pd.f.c(_, hw(t0, (pos + 1 : U32)), n), pos) == True{} : Bool}
      pf.k(U32.is_eq(P.rk(hw(t0, P.base(hw(t0, (pos + 1 : U32))))), 18), t0, a, pos, n)
    case False{}:
      pf.k(False{}, t0, a, pos, n)

def pf.t(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +pos: U32, +n: U32) -> {QM.front.at(Q.pd.peer.r(Q.pd.peer(hp(t0, a), pos), n), pos) == True{} : Bool}:
  %Equal.sym(P.H & U32, P.rd(hp(t0, a), (pos + 1 : U32)), (hp(t0, a), hw(t0, (pos + 1 : U32))), rd_back(t0, a, (pos + 1 : U32))) :
    {QM.front.at(Q.pd.peer.r(_, n), pos) == True{} : Bool}
  pf.p(Bool.not(P.is_static(hw(t0, (pos + 1 : U32)))) && U32.is_eq((hw(t0, (pos + 1 : U32)) .&. 3 : U32), 0), t0, a, pos, n)

def pf.m(-A: Array<U32>, -a: Array<V.Val>, +pos: U32, +n: U32, m: LAT.Mirror(U32, A)) -> {QM.front.at(Q.pd.peer.r(Q.pd.peer(P.H{KM.MG{A}, a}, pos), n), pos) == True{} : Bool}:
  (+t0, +e0) = m
  %e0 : {QM.front.at(Q.pd.peer.r(Q.pd.peer(P.H{KM.MG{_}, a}, pos), n), pos) == True{} : Bool}
  pf.t(t0, a, pos, n)

# any heap: a frontier read at the position faces it
def peer_front(h: P.H, +pos: U32, +n: U32) -> {QM.front.at(Q.pd.peer.r(Q.pd.peer(h, pos), n), pos) == True{} : Bool}:
  match h:
    case P.H{w, a}:
      match w:
        case KM.MG{A}:
          pf.m(A, a, pos, n, LAT.mirror(U32, A))

# the loop's step, each of its ends settled where it is made
def lp.b(+done: Bool, +front: Bool, d: KD.D, +pos: U32, +n: U32, +acc: U32, +k: Nat, +f: Nat, ih: @h2:P.H -> @a2:U32 -> {QM.front.at(Q.pd.loop(k, f, h2, pos, a2), pos) == True{} : Bool}) ->
  {QM.front.at(Q.pd.loop.r(Q.pd.ended.b(done, front, d, pos, n, acc), acc, h2 => a2 => Q.pd.loop(k, f, h2, pos, a2)), pos) == True{} : Bool}:
  match done:
    case True{}:
      ih(Q.pd.h(d), (acc + n : U32))
    case False{}:
      match front:
        case True{}:
          peer_front(Q.pd.h(d), pos, (acc + n : U32))
        case False{}:
          {==}

def lp.ended(d: KD.D, +pos: U32, +acc: U32, +k: Nat, +f: Nat, ih: @h2:P.H -> @a2:U32 -> {QM.front.at(Q.pd.loop(k, f, h2, pos, a2), pos) == True{} : Bool}) -> {QM.front.at(Q.pd.loop.r(Q.pd.ended(d, pos, acc), acc, h2 => a2 => Q.pd.loop(k, f, h2, pos, a2)), pos) == True{} : Bool}:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      lp.b(U32.is_eq(st, 1), U32.is_eq(st, 7), KD.D{h, path, top, depth, n, st}, pos, n, acc, k, f, ih)

def lp.climbed(c: Q.Cl, +b: U32, +pos: U32, +acc: U32, +k: Nat, +f: Nat, ih: @h2:P.H -> @a2:U32 -> {QM.front.at(Q.pd.loop(k, f, h2, pos, a2), pos) == True{} : Bool}) -> {QM.front.at(Q.pd.loop.r(Q.pd.climbed(c, b, pos, f, acc), acc, h2 => a2 => Q.pd.loop(k, f, h2, pos, a2)), pos) == True{} : Bool}:
  match c:
    case Q.Cl{h, +x, +hit, +go}:
      match hit:
        case True{}:
          peer_front(h, pos, acc)
        case False{}:
          lp.ended(Q.pd.walk(h, b, f), pos, acc, k, f, ih)

def lp.ve(+era: Bool, h: P.H, +q: U32, +pos: U32, +acc: U32, +k: Nat, +f: Nat) -> {QM.front.at(Q.pd.loop.r(Q.pd.v.e(era, h, q, acc), acc, h2 => a2 => Q.pd.loop(k, f, h2, pos, a2)), pos) == True{} : Bool}:
  match era:
    case True{}:
      {==}
    case False{}:
      {==}

def lp.vk(+cur: Bool, +era: Bool, h: P.H, +q: U32, +pos: U32, +acc: U32, +k: Nat, +f: Nat) -> {QM.front.at(Q.pd.loop.r(Q.pd.v.k(cur, era, h, q, acc), acc, h2 => a2 => Q.pd.loop(k, f, h2, pos, a2)), pos) == True{} : Bool}:
  match cur:
    case True{}:
      {==}
    case False{}:
      lp.ve(era, h, q, pos, acc, k, f)

def lp.v(r: P.H & U32, +q: U32, +pos: U32, +acc: U32, +k: Nat, +f: Nat) -> {QM.front.at(Q.pd.loop.r(Q.pd.v(r, q, acc), acc, h2 => a2 => Q.pd.loop(k, f, h2, pos, a2)), pos) == True{} : Bool}:
  match r:
    case (h, +hd):
      lp.vk(U32.is_eq(P.rk(hd), 18), U32.is_eq((P.rk(hd) .|. 1 : U32), 7), h, q, pos, acc, k, f)

def lp.qk(+st: Bool, +pr: Bool, h: P.H, +q: U32, +pos: U32, +acc: U32, +k: Nat, +f: Nat, ih: @h2:P.H -> @a2:U32 -> {QM.front.at(Q.pd.loop(k, f, h2, pos, a2), pos) == True{} : Bool}) -> {QM.front.at(Q.pd.loop.r(Q.pd.q.k(st, pr, h, q, pos, f, acc), acc, h2 => a2 => Q.pd.loop(k, f, h2, pos, a2)), pos) == True{} : Bool}:
  match st:
    case True{}:
      {==}
    case False{}:
      match pr:
        case True{}:
          lp.v(P.rd(h, P.base(q)), q, pos, acc, k, f)
        case False{}:
          lp.climbed(Q.cl.from(h, P.base(q)), P.base(q), pos, acc, k, f, ih)

def lp.q(r: P.H & U32, +pos: U32, +acc: U32, +k: Nat, +f: Nat, ih: @h2:P.H -> @a2:U32 -> {QM.front.at(Q.pd.loop(k, f, h2, pos, a2), pos) == True{} : Bool}) -> {QM.front.at(Q.pd.loop.r(Q.pd.q(r, pos, f, acc), acc, h2 => a2 => Q.pd.loop(k, f, h2, pos, a2)), pos) == True{} : Bool}:
  match r:
    case (h, +q):
      lp.qk(P.is_static(q), U32.is_eq((q .&. 3 : U32), 0), h, q, pos, acc, k, f, ih)

def front_loop(g: Nat, +f: Nat, h: P.H, +pos: U32, +acc: U32) -> {QM.front.at(Q.pd.loop(g, f, h, pos, acc), pos) == True{} : Bool}:
  match g:
    case 0n:
      {==}
    case 1n+(+k):
      lp.q(Q.pd.peer(h, pos), pos, acc, k, f, h2 => a2 => front_loop(k, f, h2, pos, a2))

def Laws.front_faces(h, pos, g, f):
  front_loop(g, f, h, pos, 0)

# going on from a walk: its end settled first, the loop after
def Laws.front_faces_from(d, pos, g, f):
  lp.ended(K.demand_ev(0, f, d), pos, 0, g, f, h2 => a2 => front_loop(g, f, h2, pos, a2))

# --- the frontier apart from the position (front_apart)

def ah.u32_eq(+a: U32, +b: U32, +h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  MU.u32_to_nat_inj(a, b, MN.eq_of_is_eq(U32.to_nat(a), U32.to_nat(b),
    Equal.trans(Bool, Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), U32.is_eq(a, b), True{}, Equal.sym(Bool, U32.is_eq(a, b), Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), MU.u32_is_eq_to_nat(a, b)), h)))

# a port's check passed: its link no port of its own reference, unless a
# static eraser, which a port that is no static cannot be
def at_ne(+inside: Bool, +v: List<&2, U32>, +d: Nat, +x: U32, +y: U32, +cap: U32, +hin: {(U32.is_ge((y >> 2n : U32), P.first()) && U32.is_lt((y >> 2n : U32), cap) && U32.is_ne(y, x)) == inside : Bool},
  +h: {WR.at(inside, v, d, x, y) == True{} : Bool}) -> {U32.is_eq(y, x) == False{} : Bool}:
  match inside:
    case True{}:
      +hne = MB.eq_true_of_and_right(U32.is_ge((y >> 2n : U32), P.first()) && U32.is_lt((y >> 2n : U32), cap), U32.is_ne(y, x), hin)
      MB.eq_false_of_not_eq_true(U32.is_eq(y, x), hne)
    case False{}:
      Empty.absurd({U32.is_eq(y, x) == False{} : Bool}, MB.false_ne_true()(h))

# the static eraser is a static: no port that is none
def ne_era.k(+e: Bool, +x: U32, +he: {U32.is_eq(P.era(), x) == e : Bool}, +hx: {P.is_static(x) == False{} : Bool}) -> {e == False{} : Bool}:
  match e:
    case True{}:
      +ex = ah.u32_eq(P.era(), x, he)
      Empty.absurd({True{} == False{} : Bool}, MB.true_ne_false()(ME.subst(U32, z => {P.is_static(z) == False{} : Bool}, x, P.era(), Equal.sym(U32, P.era(), x, ex), hx)))
    case False{}:
      {==}

def lk_ne(+st: Bool, +v: List<&2, U32>, +d: Nat, +x: U32, +y: U32, +cap: U32, +hx: {P.is_static(x) == False{} : Bool}, +h: {WR.lk(st, v, d, x, y, cap) == True{} : Bool}) ->
  {U32.is_eq(y, x) == False{} : Bool}:
  match st:
    case True{}:
      +ey = ah.u32_eq(y, P.era(), h)
      ME.subst(U32, z => {U32.is_eq(z, x) == False{} : Bool}, P.era(), y, Equal.sym(U32, y, P.era(), ey), ne_era.k(U32.is_eq(P.era(), x), x, {==}, hx))
    case False{}:
      at_ne(U32.is_ge((y >> 2n : U32), P.first()) && U32.is_lt((y >> 2n : U32), cap) && U32.is_ne(y, x), v, d, x, y, cap, {==}, h)

def ah.hw(+t0: LAT.Tree<U32>, +x: U32) -> U32:
  Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), x))

def ah.rd_back(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +i: U32) -> {P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, i) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, ah.hw(t0, i)) : P.H & U32}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), i), (LAT.fromT(U32, t0), ah.hw(t0, i)), LA.get_pair(U32, LAT.fromT(U32, t0), i)) :
    {P.rd.fin(KM.m_get.fin(_), a) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, ah.hw(t0, i)) : P.H & U32}
  {==}

def ah.wdv(+t0: LAT.Tree<U32>, +d: Nat, +i: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, i) == ah.hw(t0, i) : U32}:
  %LA.get_view(U32, LAT.fromT(U32, t0), d, i, hft, hd32) : {KMd.word.m(_) == ah.hw(t0, i) : U32}
  {==}

# on mirrors: the frontier's port, the position's link word, is not it
def ap.k(+t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +j: U32, +p: U32,
  +hwp: {WR.port.ok(AD.view(U32, LAT.fromT(U32, t0)), d, ((j << 2n : U32) + p : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_wcap())) == True{} : Bool}, +hns: {P.is_static(((j << 2n : U32) + p : U32)) == False{} : Bool},
  +q: U32, +n: U32, +hfa: {QM.front.at(Q.PdFront{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, q, n}, ((j << 2n : U32) + p : U32)) == True{} : Bool}) -> {U32.is_eq(q, ((j << 2n : U32) + p : U32)) == False{} : Bool}:
  +hne = lk_ne(P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (((j << 2n : U32) + p : U32) + 1 : U32))), AD.view(U32, LAT.fromT(U32, t0)), d, ((j << 2n : U32) + p : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (((j << 2n : U32) + p : U32) + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_wcap()), hns, hwp)
  +hq0 = ME.subst(P.H & U32, z => {U32.is_eq(Pair.snd(P.H, U32, z), q) == True{} : Bool}, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (((j << 2n : U32) + p : U32) + 1 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, ah.hw(t0, (((j << 2n : U32) + p : U32) + 1 : U32))), ah.rd_back(t0, LAT.fromT(V.Val, ta), (((j << 2n : U32) + p : U32) + 1 : U32)), hfa)
  +hq = ah.u32_eq(ah.hw(t0, (((j << 2n : U32) + p : U32) + 1 : U32)), q, hq0)
  +hy = Equal.trans(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (((j << 2n : U32) + p : U32) + 1 : U32)), ah.hw(t0, (((j << 2n : U32) + p : U32) + 1 : U32)), q, ah.wdv(t0, d, (((j << 2n : U32) + p : U32) + 1 : U32), hft, hd32), hq)
  ME.subst(U32, z => {U32.is_eq(z, ((j << 2n : U32) + p : U32)) == False{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (((j << 2n : U32) + p : U32) + 1 : U32)), q, hy, hne)

def ap.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hwd: {Pair.snd(P.H, Bool, KN.wired_ok(P.H{KM.MG{w}, a})) == True{} : Bool}, +j: U32, +p: U32, +hj: {U32.is_le(P.first(), j) == True{} : Bool},
  hjc: {U32.is_lt(j, KMd.word(AD.view(U32, w), d, P.at_wcap())) == True{} : Bool}, hpa: {U32.is_lt(p, KR.kind_arity(P.rk(KMd.word(AD.view(U32, w), d, (j << 2n : U32))))) == True{} : Bool},
  +pos: U32, +hpos: {pos == ((j << 2n : U32) + p : U32) : U32}, +hns: {P.is_static(pos) == False{} : Bool}, +q: U32, +n: U32,
  hfa: {QM.front.at(Q.PdFront{P.H{KM.MG{w}, a}, q, n}, pos) == True{} : Bool}, m0: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) -> {U32.is_eq(q, pos) == False{} : Bool}:
  (+t0, +e0) = m0
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t0, d, e0, hf)
  +hw1 = LAB.subst(Array<U32>, x => {Pair.snd(P.H, Bool, KN.wired_ok(P.H{KM.MG{x}, a})) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e0), hwd)
  +hw2 = LAB.subst(Array<V.Val>, x => {Pair.snd(P.H, Bool, KN.wired_ok(P.H{KM.MG{LAT.fromT(U32, t0)}, x})) == True{} : Bool}, a, LAT.fromT(V.Val, ta), Equal.sym(Array<V.Val>, LAT.fromT(V.Val, ta), a, ea), hw1)
  +hjc2 = LAB.subst(Array<U32>, x => {U32.is_lt(j, KMd.word(AD.view(U32, x), d, P.at_wcap())) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e0), hjc)
  +hpa2 = LAB.subst(Array<U32>, x => {U32.is_lt(p, KR.kind_arity(P.rk(KMd.word(AD.view(U32, x), d, (j << 2n : U32))))) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e0), hpa)
  +hwp = WI.wired_port(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), d, hft, hd32, hw2, j, p, hj, hjc2, hpa2)
  +hf1 = LAB.subst(Array<U32>, x => {QM.front.at(Q.PdFront{P.H{KM.MG{x}, a}, q, n}, pos) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e0), hfa)
  +hf2 = LAB.subst(Array<V.Val>, x => {QM.front.at(Q.PdFront{P.H{KM.MG{LAT.fromT(U32, t0)}, x}, q, n}, pos) == True{} : Bool}, a, LAT.fromT(V.Val, ta), Equal.sym(Array<V.Val>, LAT.fromT(V.Val, ta), a, ea), hf1)
  +hf3 = ME.subst(U32, z => {QM.front.at(Q.PdFront{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, q, n}, z) == True{} : Bool}, pos, ((j << 2n : U32) + p : U32), hpos, hf2)
  +hns2 = ME.subst(U32, z => {P.is_static(z) == False{} : Bool}, pos, ((j << 2n : U32) + p : U32), hpos, hns)
  ME.subst(U32, z => {U32.is_eq(q, z) == False{} : Bool}, ((j << 2n : U32) + p : U32), pos, Equal.sym(U32, pos, ((j << 2n : U32) + p : U32), hpos), ap.k(t0, ta, d, hft, hd32, j, p, hwp, hns2, q, n, hf3))

def Laws.front_apart(w, a, d, hf, hd32, hwd, j, p, hj, hjc, hpa, pos, hpos, hns, q, n, hfa):
  ap.m(w, a, d, hf, hd32, hwd, j, p, hj, hjc, hpa, pos, hpos, hns, q, n, hfa, LAT.mirror(U32, w), LAT.mirror(V.Val, a))
