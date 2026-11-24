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

import Base
import ./POSITION_LAWS.bend as Laws
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/knet.bend as KN
import ../spike/kdemand.bend as KD
import ./position.bend as Q
import ./position_model.bend as QM
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MN
import 0x8ae61ec3a6615abd35f196c07232ad28/u32.bend as MU
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/LAWS.bend as LA
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/PROOF.bend as LAP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT

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
