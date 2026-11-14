# glam's proofs of glam/LAWS.bend.
#
# Lessons, beside docs/Proving.md's: a walk that only reads (the ring's,
# R.rg.pred.go) keeps its heap by induction on its fuel, each step's two
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
import ./ring.bend as R
import ./ring_model.bend as RG
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import 0x8ae61ec3a6615abd35f196c07232ad28/string.bend as MS
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME
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
  ih1: {R.rg.pred.w(R.rg.pred.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, Some{p}, True{}}, x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, Some{p}, True{}}, x)))) : P.H & U32},
  ih2: {R.rg.pred.w(R.rg.pred.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}}, x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}}, x)))) : P.H & U32}) ->
  {R.rg.pred.w(R.rg.pred.go(1n+g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, False{}}, x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(1n+g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, False{}}, x)))) : P.H & U32}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(n, x), True{}, e) :
        {R.rg.pred.w(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x)))) : P.H & U32}
      ih1
    case False{}:
      %Equal.sym(Bool, U32.is_eq(n, x), False{}, e) :
        {R.rg.pred.w(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x)))) : P.H & U32}
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (n + 3 : U32))) :
        {R.rg.pred.w(R.rg.pred.go(g, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), n), x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), n), x)))) : P.H & U32}
      ih2

def go_pair(f: Nat, +t: LAT.Tree<U32>, -a: Array<V.Val>, +n: U32, +p: U32, +found: Maybe<&2, U32>, +done: Bool, +x: U32) ->
  {R.rg.pred.w(R.rg.pred.go(f, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, done}, x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(f, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, done}, x)))) : P.H & U32}:
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
  {R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x))) : P.H & U32}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 3 : U32))) :
    {R.rg.pred.w(R.rg.pred.go(1000000n, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), x), x)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(1000000n, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), x), x)))) : P.H & U32}
  go_pair(1000000n, t, a, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), x, None{}, False{}, x)

def unlink_keeps.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +x: U32, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hj: {Nat.is_eq(AD.slot((Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{w}, a}, x)) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {Pair.snd(P.H, U32, P.rd(R.rg.unlink(P.H{KM.MG{w}, a}, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hj1 = LAB.subst(Array<U32>, y => {Nat.is_eq(AD.slot((Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{y}, a}, x)) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hj)
  +hj2 = LAB.subst(Array<V.Val>, y => {Nat.is_eq(AD.slot((Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, y}, x)) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, a, LAT.fromT(V.Val, ta), Equal.sym(Array<V.Val>, LAT.fromT(V.Val, ta), a, ea), hj1)
  %e : {Pair.snd(P.H, U32, P.rd(R.rg.unlink(P.H{KM.MG{_}, a}, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %ea : {Pair.snd(P.H, U32, P.rd(R.rg.unlink(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, _}, j)) : U32}
  %Equal.sym(P.H & U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x), (P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))), pred_pair(t, LAT.fromT(V.Val, ta), x)) :
    {Pair.snd(P.H, U32, P.rd(R.rg.unlink.p(_, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 3 : U32))) :
    {Pair.snd(P.H, U32, P.rd(R.rg.unlink.set(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t), (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))))}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t), (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)),
    rd_get(Array.set(U32, LAT.fromT(U32, t), (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LAT.fromT(V.Val, ta), j),
    Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t), (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)),
      LA.get_set_other(U32, LAT.fromT(U32, t), d, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), j, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), hft, hd32, hj2),
      Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), rd_get(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), j))))

def Laws.unlink_keeps(w, a, d, x, j, hf, hd32, hj):
  unlink_keeps.go(w, a, d, x, j, hf, hd32, hj, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# Rings (glam/ring_model.bend)
# =====

# by cases on a disjunction, each case a function used once (as Blend's)
def or_cases(+a: Bool, +b: Bool, +c: Bool, h: {Bool.or(a, b) == True{} : Bool},
    fa: {a == True{} : Bool} -> {c == True{} : Bool}, fb: {b == True{} : Bool} -> {c == True{} : Bool}) -> {c == True{} : Bool}:
  match a:
    case True{}:
      fa({==})
    case False{}:
      fb(h)

# a member of a closed ring links a member, read as the view has it
def closed_at(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +xs: List<&2, U32>, +n: U32,
    +hc: {RG.closed.go(v, d, xs, ys) == True{} : Bool}, hn: {RG.has(ys, n) == True{} : Bool}) ->
    {RG.link.in(v, d, xs, n) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({RG.link.in(v, d, xs, n) == True{} : Bool}, MB.false_ne_true()(hn))
    case Con{+y, +t}:
      +hy = MB.eq_true_of_and_left(RG.link.in(v, d, xs, y), RG.closed.go(v, d, xs, t), hc)
      +ht = MB.eq_true_of_and_right(RG.link.in(v, d, xs, y), RG.closed.go(v, d, xs, t), hc)
      or_cases(U32.is_eq(y, n), RG.has(t, n), RG.link.in(v, d, xs, n), hn,
        e => ME.subst(U32, z => {RG.link.in(v, d, xs, z) == True{} : Bool}, y, n, MS.u32_eq_of_is_eq(y, n, e), hy),
        hh => closed_at(t, v, d, xs, n, ht, hh))

# so a member's word 3, as the words hold it, is a member
def link_mem(+t: LAT.Tree<U32>, +d: Nat, +xs: List<&2, U32>, +n: U32,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hc: {RG.closed(AD.view(U32, LAT.fromT(U32, t)), d, xs) == True{} : Bool}, hn: {RG.has(xs, n) == True{} : Bool}) ->
    {RG.has(xs, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32)))) == True{} : Bool}:
  LAB.subst(Maybe<&2, U32>, mm => {RG.link.in.m(mm, xs) == True{} : Bool},
    List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((n + 3 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32)))},
    Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((n + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (n + 3 : U32), hft, hd32)),
    closed_at(xs, AD.view(U32, LAT.fromT(U32, t)), d, xs, n, hc, hn))

# the walk round a closed ring from a member stays among its members: a
# step, its test split
def pm_step(+t: LAT.Tree<U32>, -a: Array<V.Val>, +g: Nat, +xs: List<&2, U32>,
  +n: U32, +p: U32, +found: Maybe<&2, U32>, +x: U32, +b: Bool, e: {U32.is_eq(n, x) == b : Bool},
  ih1: {RG.has(xs, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, Some{p}, True{}}, x)))) == True{} : Bool},
  ih2: {RG.has(xs, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}}, x)))) == True{} : Bool}) ->
  {RG.has(xs, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(1n+g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, False{}}, x)))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(n, x), True{}, e) :
        {RG.has(xs, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x)))) == True{} : Bool}
      ih1
    case False{}:
      %Equal.sym(Bool, U32.is_eq(n, x), False{}, e) :
        {RG.has(xs, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x)))) == True{} : Bool}
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (n + 3 : U32))) :
        {RG.has(xs, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), n), x)))) == True{} : Bool}
      ih2

def pred_mem(f: Nat, +t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +xs: List<&2, U32>,
  +n: U32, +p: U32, +found: Maybe<&2, U32>, +done: Bool, +x: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hc: {RG.closed(AD.view(U32, LAT.fromT(U32, t)), d, xs) == True{} : Bool},
  +hn: {RG.has(xs, n) == True{} : Bool}, +hp: {RG.has(xs, p) == True{} : Bool}) ->
  {RG.has(xs, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(f, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, done}, x)))) == True{} : Bool}:
  match f:
    case 0n:
      hp
    case 1n+(+g):
      match done:
        case True{}:
          hp
        case False{}:
          pm_step(t, a, g, xs, n, p, found, x, U32.is_eq(n, x), {==},
            pred_mem(g, t, a, d, xs, n, p, Some{p}, True{}, x, hft, hd32, hc, hn, hp),
            pred_mem(g, t, a, d, xs, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}, x, hft, hd32, hc, link_mem(t, d, xs, n, hft, hd32, hc, hn), hn))

def pred_in_ring.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +x: U32, +xs: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hc: {RG.closed(AD.view(U32, w), d, xs) == True{} : Bool}, +hx: {RG.has(xs, x) == True{} : Bool},
  m: LAT.Mirror(U32, w)) ->
  {RG.has(xs, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{w}, a}, x))) == True{} : Bool}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hct = LAB.subst(Array<U32>, y => {RG.closed(AD.view(U32, y), d, xs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hc)
  %e : {RG.has(xs, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{_}, a}, x))) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 3 : U32))) :
    {RG.has(xs, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(1000000n, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), x), x)))) == True{} : Bool}
  pred_mem(1000000n, t, a, d, xs, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), x, None{}, False{}, x, hft, hd32, hct, link_mem(t, d, xs, x, hft, hd32, hct, hx), hx)

def Laws.pred_in_ring(w, a, d, x, xs, hf, hd32, hc, hx):
  pred_in_ring.go(w, a, d, x, xs, hf, hd32, hc, hx, LAT.mirror(U32, w))

