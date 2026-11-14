# glam's proofs of glam/LAWS.bend.
#
# Lessons, beside docs/Proving.md's: a walk that only reads (the ring's,
# R.rg.pred.go) keeps its heap by induction on its fuel, each step's two
# cases split by a step lemma taking the test's Bool and its equation, the
# induction hypotheses for both cases passed in (go_pair, go_step); a
# value the law computes from the heap and passes to a law's relevant
# argument (the predecessor, an index) needs the heap's parts all
# mirrored, the value table too, so that no erased part is used. A write
# is followed on the words' view (AD.view, LA.set_view), each member's
# read split by whether the slot written is its own: a step lemma taking
# the slots' test and its equation, get_set_ne on one side and
# get_set_self on the other (cs_step, ci_step); slots kept apart are
# premises carried member by member (apart, apart_at). U32.is_eq(x, x)
# unfolds past a rewrite by MU.u32_is_eq_to_nat alone: chain it with
# MN.is_eq_refl first (has_self); and a premise stated a == b rewrites b,
# so a hypothesis `get == Some{q}` is passed through Equal.sym.

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
import 0x8ae61ec3a6615abd35f196c07232ad28/list.bend as ML
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MN
import 0x8ae61ec3a6615abd35f196c07232ad28/u32.bend as MU

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

# A word set in the view keeps a closed ring closed, the word a member
def map_in(m: Maybe<&2, U32>, +xs: List<&2, U32>, +l: U32,
    hm: {RG.link.in.m(m, xs) == True{} : Bool}, +hl: {RG.has(xs, l) == True{} : Bool}) ->
    {RG.link.in.m(Maybe.map(&2, U32, U32, y => l, m), xs) == True{} : Bool}:
  match m:
    case Some{+z}:
      hl
    case None{}:
      Empty.absurd({RG.link.in.m(Maybe.map(&2, U32, U32, y => l, None{}), xs) == True{} : Bool}, MB.false_ne_true()(hm))

def cs_step(+v: List<&2, U32>, +d: Nat, +xs: List<&2, U32>, +s: Nat, +l: U32, +y: U32,
    +b: Bool, e: {Nat.is_eq(s, AD.slot((y + 3 : U32), d)) == b : Bool},
    hy: {RG.link.in(v, d, xs, y) == True{} : Bool}, +hl: {RG.has(xs, l) == True{} : Bool}) ->
    {RG.link.in(List.set(&2, U32, v, s, l), d, xs, y) == True{} : Bool}:
  match b:
    case False{}:
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, s, l), AD.slot((y + 3 : U32), d)), List.get(&2, U32, v, AD.slot((y + 3 : U32), d)), LAB.get_set_ne(U32, v, s, AD.slot((y + 3 : U32), d), l, e)) :
        {RG.link.in.m(_, xs) == True{} : Bool}
      hy
    case True{}:
      +eq = MN.eq_of_is_eq(s, AD.slot((y + 3 : U32), d), e)
      %eq : {RG.link.in.m(List.get(&2, U32, List.set(&2, U32, v, s, l), _), xs) == True{} : Bool}
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, s, l), s), Maybe.map(&2, U32, U32, z => l, List.get(&2, U32, v, s)), ML.get_set_self(&2, U32, v, s, l)) :
        {RG.link.in.m(_, xs) == True{} : Bool}
      map_in(List.get(&2, U32, v, s), xs, l,
        LAB.subst(Nat, k => {RG.link.in.m(List.get(&2, U32, v, k), xs) == True{} : Bool}, AD.slot((y + 3 : U32), d), s, Equal.sym(Nat, s, AD.slot((y + 3 : U32), d), eq), hy), hl)

def closed_set(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +xs: List<&2, U32>, +s: Nat, +l: U32,
    +hc: {RG.closed.go(v, d, xs, ys) == True{} : Bool}, +hl: {RG.has(xs, l) == True{} : Bool}) ->
    {RG.closed.go(List.set(&2, U32, v, s, l), d, xs, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +hy = MB.eq_true_of_and_left(RG.link.in(v, d, xs, y), RG.closed.go(v, d, xs, t), hc)
      +ht = MB.eq_true_of_and_right(RG.link.in(v, d, xs, y), RG.closed.go(v, d, xs, t), hc)
      MB.and_eq_true(RG.link.in(List.set(&2, U32, v, s, l), d, xs, y), RG.closed.go(List.set(&2, U32, v, s, l), d, xs, t),
        cs_step(v, d, xs, s, l, y, Nat.is_eq(s, AD.slot((y + 3 : U32), d)), {==}, hy, hl),
        closed_set(t, v, d, xs, s, l, ht, hl))

def unlink_closed.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +x: U32, +xs: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hc: {RG.closed(AD.view(U32, w), d, xs) == True{} : Bool}, +hx: {RG.has(xs, x) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.closed(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{w}, a}, x))), d, xs) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hct = LAB.subst(Array<U32>, y => {RG.closed(AD.view(U32, y), d, xs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hc)
  %e : {RG.closed(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{_}, a}, x))), d, xs) == True{} : Bool}
  %ea : {RG.closed(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x))), d, xs) == True{} : Bool}
  %Equal.sym(P.H & U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x), (P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))), pred_pair(t, LAT.fromT(V.Val, ta), x)) :
    {RG.closed(AD.view(U32, RG.words(R.rg.unlink.p(_, x))), d, xs) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 3 : U32))) :
    {RG.closed(AD.view(U32, RG.words(R.rg.unlink.set(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))))), d, xs) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.set_view(U32, LAT.fromT(U32, t), d, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), hft, hd32)) :
    {RG.closed(_, d, xs) == True{} : Bool}
  closed_set(xs, AD.view(U32, LAT.fromT(U32, t)), d, xs, AD.slot((Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), hct, link_mem(t, d, xs, x, hft, hd32, hct, hx))

def Laws.unlink_closed(w, a, d, x, xs, hf, hd32, hc, hx):
  unlink_closed.go(w, a, d, x, xs, hf, hd32, hc, hx, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# Inserting a cursor apart from the ring: a member's link among more
# members; x's own membership
def has_cons(+x: U32, +xs: List<&2, U32>, +l: U32, hl: {RG.has(xs, l) == True{} : Bool}) ->
    {RG.has(Con{x, xs}, l) == True{} : Bool}:
  %Equal.sym(Bool, RG.has(xs, l), True{}, hl) : {Bool.or(U32.is_eq(x, l), _) == True{} : Bool}
  MB.or_true(U32.is_eq(x, l))

def has_self(+x: U32, +xs: List<&2, U32>) -> {RG.has(Con{x, xs}, x) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(x, x), True{}, Equal.trans(Bool, U32.is_eq(x, x), Nat.is_eq(U32.to_nat(x), U32.to_nat(x)), True{}, MU.u32_is_eq_to_nat(x, x), MN.is_eq_refl(U32.to_nat(x)))) : {Bool.or(_, RG.has(xs, x)) == True{} : Bool}
  {==}

def in_cons(m: Maybe<&2, U32>, +x: U32, +xs: List<&2, U32>, hm: {RG.link.in.m(m, xs) == True{} : Bool}) ->
    {RG.link.in.m(m, Con{x, xs}) == True{} : Bool}:
  match m:
    case Some{+l}:
      has_cons(x, xs, l, hm)
    case None{}:
      Empty.absurd({RG.link.in.m(None{}, Con{x, xs}) == True{} : Bool}, MB.false_ne_true()(hm))

# apart from the ring, x's word-3 slot is not a member's
def apart_at(ys: List<&2, U32>, +d: Nat, +x: U32, +y: U32,
    +hap: {RG.apart(ys, d, x) == True{} : Bool}, hy: {RG.has(ys, y) == True{} : Bool}) ->
    {Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d))) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d))) == True{} : Bool}, MB.false_ne_true()(hy))
    case Con{+z, +t}:
      +hz = MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((z + 3 : U32), d))), RG.apart(t, d, x), hap)
      +ht = MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((z + 3 : U32), d))), RG.apart(t, d, x), hap)
      or_cases(U32.is_eq(z, y), RG.has(t, y), Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d))), hy,
        e => ME.subst(U32, q => {Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((q + 3 : U32), d))) == True{} : Bool}, z, y, MS.u32_eq_of_is_eq(z, y, e), hz),
        hh => apart_at(t, d, x, y, ht, hh))

# a member y's link after x's word 3 and situ's are written: situ's slot,
# x itself; any other, as it was
def ci_step(+v: List<&2, U32>, +d: Nat, +xs: List<&2, U32>, +x: U32, +n: U32, +ss: Nat, +y: U32, +q: U32,
    +hq: {List.get(&2, U32, v, ss) == Some{q} : Maybe<&2, U32>},
    +hsx: {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d)) == False{} : Bool},
    +hsxss: {Nat.is_eq(AD.slot((x + 3 : U32), d), ss) == False{} : Bool},
    +b: Bool, e: {Nat.is_eq(ss, AD.slot((y + 3 : U32), d)) == b : Bool},
    hy: {RG.link.in(v, d, xs, y) == True{} : Bool}) ->
    {RG.link.in(List.set(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), ss, x), d, Con{x, xs}, y) == True{} : Bool}:
  match b:
    case False{}:
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), ss, x), AD.slot((y + 3 : U32), d)), List.get(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), AD.slot((y + 3 : U32), d)), LAB.get_set_ne(U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), ss, AD.slot((y + 3 : U32), d), x, e)) :
        {RG.link.in.m(_, Con{x, xs}) == True{} : Bool}
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), AD.slot((y + 3 : U32), d)), List.get(&2, U32, v, AD.slot((y + 3 : U32), d)), LAB.get_set_ne(U32, v, AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d), n, hsx)) :
        {RG.link.in.m(_, Con{x, xs}) == True{} : Bool}
      in_cons(List.get(&2, U32, v, AD.slot((y + 3 : U32), d)), x, xs, hy)
    case True{}:
      +eq = MN.eq_of_is_eq(ss, AD.slot((y + 3 : U32), d), e)
      %eq : {RG.link.in.m(List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), ss, x), _), Con{x, xs}) == True{} : Bool}
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), ss, x), ss), Maybe.map(&2, U32, U32, z => x, List.get(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), ss)), ML.get_set_self(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), ss, x)) :
        {RG.link.in.m(_, Con{x, xs}) == True{} : Bool}
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), ss), List.get(&2, U32, v, ss), LAB.get_set_ne(U32, v, AD.slot((x + 3 : U32), d), ss, n, hsxss)) :
        {RG.link.in.m(Maybe.map(&2, U32, U32, z => x, _), Con{x, xs}) == True{} : Bool}
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, v, ss), Some{q}, hq) : {RG.link.in.m(Maybe.map(&2, U32, U32, z => x, _), Con{x, xs}) == True{} : Bool}
      has_self(x, xs)

def closed_ins(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +xs: List<&2, U32>, +x: U32, +n: U32, +ss: Nat, +q: U32,
    +hq: {List.get(&2, U32, v, ss) == Some{q} : Maybe<&2, U32>},
    +hsxss: {Nat.is_eq(AD.slot((x + 3 : U32), d), ss) == False{} : Bool},
    +hc: {RG.closed.go(v, d, xs, ys) == True{} : Bool}, +hap: {RG.apart(ys, d, x) == True{} : Bool}) ->
    {RG.closed.go(List.set(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), ss, x), d, Con{x, xs}, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      +hy = MB.eq_true_of_and_left(RG.link.in(v, d, xs, y), RG.closed.go(v, d, xs, r), hc)
      +hr = MB.eq_true_of_and_right(RG.link.in(v, d, xs, y), RG.closed.go(v, d, xs, r), hc)
      +hsy = MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d))), RG.apart(r, d, x), hap))
      +hapr = MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d))), RG.apart(r, d, x), hap)
      MB.and_eq_true(RG.link.in(List.set(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), ss, x), d, Con{x, xs}, y), RG.closed.go(List.set(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), ss, x), d, Con{x, xs}, r),
        ci_step(v, d, xs, x, n, ss, y, q, hq, hsy, hsxss, Nat.is_eq(ss, AD.slot((y + 3 : U32), d)), {==}, hy),
        closed_ins(r, v, d, xs, x, n, ss, q, hq, hsxss, hr, hapr))

# x's own link: situ's next, a member
def ci_own(+v: List<&2, U32>, +d: Nat, +xs: List<&2, U32>, +x: U32, +n: U32, +ss: Nat, +q2: U32,
    +hq2: {List.get(&2, U32, v, AD.slot((x + 3 : U32), d)) == Some{q2} : Maybe<&2, U32>},
    +hssx: {Nat.is_eq(ss, AD.slot((x + 3 : U32), d)) == False{} : Bool}, +hn: {RG.has(xs, n) == True{} : Bool}) ->
    {RG.link.in(List.set(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), ss, x), d, Con{x, xs}, x) == True{} : Bool}:
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), ss, x), AD.slot((x + 3 : U32), d)), List.get(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), AD.slot((x + 3 : U32), d)), LAB.get_set_ne(U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), ss, AD.slot((x + 3 : U32), d), x, hssx)) :
    {RG.link.in.m(_, Con{x, xs}) == True{} : Bool}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, AD.slot((x + 3 : U32), d), n), AD.slot((x + 3 : U32), d)), Maybe.map(&2, U32, U32, z => n, List.get(&2, U32, v, AD.slot((x + 3 : U32), d))), ML.get_set_self(&2, U32, v, AD.slot((x + 3 : U32), d), n)) :
    {RG.link.in.m(_, Con{x, xs}) == True{} : Bool}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, v, AD.slot((x + 3 : U32), d)), Some{q2}, hq2) : {RG.link.in.m(Maybe.map(&2, U32, U32, z => n, _), Con{x, xs}) == True{} : Bool}
  has_cons(x, xs, n, hn)

def insert_closed.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +situ: U32, +x: U32, +xs: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hc: {RG.closed(AD.view(U32, w), d, xs) == True{} : Bool}, +hs: {RG.has(xs, situ) == True{} : Bool},
  +hx: {RG.apart(xs, d, x) == True{} : Bool}, m: LAT.Mirror(U32, w)) ->
  {RG.closed(AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{w}, a}, situ, x))), d, Con{x, xs}) == True{} : Bool}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hct = LAB.subst(Array<U32>, y => {RG.closed(AD.view(U32, y), d, xs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hc)
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32))), hft)
  +hsxss = MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((situ + 3 : U32), d)), apart_at(xs, d, x, situ, hx, hs))
  %e : {RG.closed(AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{_}, a}, situ, x))), d, Con{x, xs}) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (situ + 3 : U32))) :
    {RG.closed(AD.view(U32, RG.words(R.rg.insert.r(P.rd.fin(KM.m_get.fin(_), a), situ, x))), d, Con{x, xs}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32)))), (situ + 3 : U32), x)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32))))), AD.slot((situ + 3 : U32), d), x), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32)))), d, (situ + 3 : U32), x, hf1, hd32)) :
    {RG.closed(_, d, Con{x, xs}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32))))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32)))), LA.set_view(U32, LAT.fromT(U32, t), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32))), hft, hd32)) :
    {RG.closed(List.set(&2, U32, _, AD.slot((situ + 3 : U32), d), x), d, Con{x, xs}) == True{} : Bool}
  MB.and_eq_true(RG.link.in(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32)))), AD.slot((situ + 3 : U32), d), x), d, Con{x, xs}, x),
    RG.closed.go(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32)))), AD.slot((situ + 3 : U32), d), x), d, Con{x, xs}, xs),
    ci_own(AD.view(U32, LAT.fromT(U32, t)), d, xs, x, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32))), AD.slot((situ + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))),
      Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (x + 3 : U32), hft, hd32)),
      Equal.trans(Bool, Nat.is_eq(AD.slot((situ + 3 : U32), d), AD.slot((x + 3 : U32), d)), Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((situ + 3 : U32), d)), False{}, MN.is_eq_comm(AD.slot((situ + 3 : U32), d), AD.slot((x + 3 : U32), d)), hsxss),
      link_mem(t, d, xs, situ, hft, hd32, hct, hs)),
    closed_ins(xs, AD.view(U32, LAT.fromT(U32, t)), d, xs, x, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32))), AD.slot((situ + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32))),
      Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (situ + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((situ + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (situ + 3 : U32), hft, hd32)),
      hsxss, hct, hx))

def Laws.insert_closed(w, a, d, situ, x, xs, hf, hd32, hc, hs, hx):
  insert_closed.go(w, a, d, situ, x, xs, hf, hd32, hc, hs, hx, LAT.mirror(U32, w))

