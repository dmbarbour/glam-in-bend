# glam's proofs of glam/LAWS.bend.
#
# Lessons, beside docs/Proving.md's: a walk that only reads (the ring's,
# M.rg.pred.go) keeps its heap by induction on its fuel, each step's two
# cases split by a step lemma taking the test's Bool and its equation, the
# induction hypotheses for both cases passed in (go_pair, go_step); a
# value the law computes from the heap and passes to a law's relevant
# argument (the predecessor, an index) needs the heap's parts all
# mirrored, the value table too, so that no erased part is used.

import Base
import ./LAWS.bend as Laws
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ./materialize.bend as M
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/LAWS.bend as LA
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/PROOF.bend as LAP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_base.bend as LAB
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# A read of a heap made the read of its words (as spike/PROOF.bend's)
def rd_get(w: Array<U32>, -a: Array<V.Val>, +j: U32) ->
  {Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) == Pair.snd(Array<U32>, U32, Array.get(U32, w, j)) : U32}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, w, j), (w, Pair.snd(Array<U32>, U32, Array.get(U32, w, j))), LA.get_pair(U32, w, j)) :
    {Pair.snd(P.H, U32, P.rd.fin(KM.m_get.fin(_), a)) == Pair.snd(Array<U32>, U32, Array.get(U32, w, j)) : U32}
  {==}

# The ring's walk keeps its heap: a step, its test split
def go_step(+t: LAT.Tree<U32>, -a: Array<V.Val>, +g: Nat,
  +n: U32, +p: U32, +found: Maybe<&2, U32>, +x: U32, +b: Bool, e: {U32.is_eq(n, x) == b : Bool},
  ih1: {M.rg.pred.w(M.rg.pred.go(g, M.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, Some{p}, True{}}, x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, M.rg.pred.w(M.rg.pred.go(g, M.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, Some{p}, True{}}, x)))) : P.H & U32},
  ih2: {M.rg.pred.w(M.rg.pred.go(g, M.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}}, x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, M.rg.pred.w(M.rg.pred.go(g, M.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}}, x)))) : P.H & U32}) ->
  {M.rg.pred.w(M.rg.pred.go(1n+g, M.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, False{}}, x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, M.rg.pred.w(M.rg.pred.go(1n+g, M.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, False{}}, x)))) : P.H & U32}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(n, x), True{}, e) :
        {M.rg.pred.w(M.rg.pred.go(g, M.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, M.rg.pred.w(M.rg.pred.go(g, M.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x)))) : P.H & U32}
      ih1
    case False{}:
      %Equal.sym(Bool, U32.is_eq(n, x), False{}, e) :
        {M.rg.pred.w(M.rg.pred.go(g, M.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, M.rg.pred.w(M.rg.pred.go(g, M.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x)))) : P.H & U32}
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (n + 3 : U32))) :
        {M.rg.pred.w(M.rg.pred.go(g, M.rw.on(P.rd.fin(KM.m_get.fin(_), a), n), x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, M.rg.pred.w(M.rg.pred.go(g, M.rw.on(P.rd.fin(KM.m_get.fin(_), a), n), x)))) : P.H & U32}
      ih2

def go_pair(f: Nat, +t: LAT.Tree<U32>, -a: Array<V.Val>, +n: U32, +p: U32, +found: Maybe<&2, U32>, +done: Bool, +x: U32) ->
  {M.rg.pred.w(M.rg.pred.go(f, M.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, done}, x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, M.rg.pred.w(M.rg.pred.go(f, M.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, done}, x)))) : P.H & U32}:
  match f:
    case 0n:
      {==}
    case 1n+(+g):
      match done:
        case True{}:
          {==}
        case False{}:
          go_step(t, a, g, n, p, found, x, U32.is_eq(n, x), {==},
            go_pair(g, t, a, n, p, Some{p}, True{}, x),
            go_pair(g, t, a, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}, x))

# so the predecessor's walk hands the heap back
def pred_pair(+t: LAT.Tree<U32>, -a: Array<V.Val>, +x: U32) ->
  {M.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, M.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x))) : P.H & U32}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 3 : U32))) :
    {M.rg.pred.w(M.rg.pred.go(1000000n, M.rw.on(P.rd.fin(KM.m_get.fin(_), a), x), x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, M.rg.pred.w(M.rg.pred.go(1000000n, M.rw.on(P.rd.fin(KM.m_get.fin(_), a), x), x)))) : P.H & U32}
  go_pair(1000000n, t, a, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), x, None{}, False{}, x)

def unlink_keeps.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +x: U32, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hj: {Nat.is_eq(AD.slot((Pair.snd(P.H, U32, M.rg.pred(P.H{KM.MG{w}, a}, x)) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {Pair.snd(P.H, U32, P.rd(M.rg.unlink(P.H{KM.MG{w}, a}, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hj1 = LAB.subst(Array<U32>, y => {Nat.is_eq(AD.slot((Pair.snd(P.H, U32, M.rg.pred(P.H{KM.MG{y}, a}, x)) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hj)
  +hj2 = LAB.subst(Array<V.Val>, y => {Nat.is_eq(AD.slot((Pair.snd(P.H, U32, M.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, y}, x)) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, a, LAT.fromT(V.Val, ta), Equal.sym(Array<V.Val>, LAT.fromT(V.Val, ta), a, ea), hj1)
  %e : {Pair.snd(P.H, U32, P.rd(M.rg.unlink(P.H{KM.MG{_}, a}, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %ea : {Pair.snd(P.H, U32, P.rd(M.rg.unlink(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, _}, j)) : U32}
  %Equal.sym(P.H & U32, M.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x), (P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(P.H, U32, M.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))), pred_pair(t, LAT.fromT(V.Val, ta), x)) :
    {Pair.snd(P.H, U32, P.rd(M.rg.unlink.p(_, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 3 : U32))) :
    {Pair.snd(P.H, U32, P.rd(M.rg.unlink.set(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(P.H, U32, M.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t), (Pair.snd(P.H, U32, M.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))))}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t), (Pair.snd(P.H, U32, M.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)),
    rd_get(Array.set(U32, LAT.fromT(U32, t), (Pair.snd(P.H, U32, M.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LAT.fromT(V.Val, ta), j),
    Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t), (Pair.snd(P.H, U32, M.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)),
      LA.get_set_other(U32, LAT.fromT(U32, t), d, (Pair.snd(P.H, U32, M.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), j, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), hft, hd32, hj2),
      Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), rd_get(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), j))))

def Laws.unlink_keeps(w, a, d, x, j, hf, hd32, hj):
  unlink_keeps.go(w, a, d, x, j, hf, hd32, hj, LAT.mirror(U32, w), LAT.mirror(V.Val, a))
