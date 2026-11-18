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
# so a hypothesis `get == Some{q}` is passed through Equal.sym. A
# composed step (the join) restates each step's heap in its parts
# (lx_parts, ul_parts, fr_parts) and carries the next step's premises
# (perfect words, the ring closed) forward; a step with static tests is
# proved for any Bools, split four ways, and applied to the tests. The
# exact ring's walk (wk) is followed along the list it walks, matching
# the list and then the fuel, each step's test rewritten by the link the
# chain gives rather than split; a list split at a member is a premise
# (pre ++ x :: post), not an existential; and a match may not follow a
# let, so facts drawn from a premise on the matched list go in each
# branch (ch_keep). Laws stated by membership are proved through their
# split (lpre, lpost, split_of_has), the split forms kept as lemmas; a
# definition cannot match a computed Bool, so a list taken apart by a test
# selects with a helper matching its Bool parameter (RG.keep, RG.pick,
# pick_l). The hub's Bool lemmas take their Bools relevantly: a fact
# about the view of an erased array is first moved onto its mirror's
# array, the value table's too where a heap after a step is named
# (join_exact.m). A rewrite may not stand inside a lambda: there,
# ME.subst. A lambda's parameter is used once: a case split needing it
# twice is a step lemma over Bools and their equations, the induction
# hypothesis passed in as a function (lp_step). An invariant kept through
# a write is easier stated so that the write's value keeps it wherever it
# lands (faces_write) than by locating every member the write may hit. A
# definition may use only those above it: a lemma needed earlier moves
# up. A walk that may raise an error hands back P.err_if(not done, h):
# the heap is restated in its parts by cases on the flag (eif_parts), and
# where the walk is shown done (pdone_exact.go) the error is gone by
# computation (pred_pair_ok). A bound in the heap's size reaches 2^d by
# lawful-arrays' size_count, never through the shift's value and 2^32,
# which the checker cannot hold (docs/BendIssues.md, Big constants); the
# pigeonhole (ph) counts on a list of Nats, by induction on the bound.
# A predicate strengthened as a conjunction (RG.port.ok, the links and
# the positions) leaves a consumer of its old half to take it by the left
# projection; only the lemmas that rebuild it want the new half (fm_sub,
# fm_add, port_sub beside links_sub).

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
# a walk's done flag, and the predecessor's walk's, as the code runs it
def rwd(w: R.Rw) -> Bool:
  match w:
    case R.Rw{h, +n, +p, found, done}:
      done

def pdone.f(r: P.H & Nat, +x: U32) -> Bool:
  (h, f) = r
  rwd(R.rg.pred.go(f, R.rw.on(R.rg.next(h, x), x), x))

def pdone(h: P.H, +x: U32) -> Bool:
  pdone.f(R.rg.fuel(h), x)

def go_step(+t: LAT.Tree<U32>, -a: Array<V.Val>, +g: Nat,
  +n: U32, +p: U32, +found: Maybe<&2, U32>, +x: U32, +b: Bool, e: {U32.is_eq(n, x) == b : Bool},
  ih1: {R.rg.pred.w(R.rg.pred.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, Some{p}, True{}}, x)) == (P.err_if(Bool.not(rwd(R.rg.pred.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, Some{p}, True{}}, x))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, Some{p}, True{}}, x)))) : P.H & U32},
  ih2: {R.rg.pred.w(R.rg.pred.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}}, x)) == (P.err_if(Bool.not(rwd(R.rg.pred.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}}, x))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}}, x)))) : P.H & U32}) ->
  {R.rg.pred.w(R.rg.pred.go(1n+g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, False{}}, x)) == (P.err_if(Bool.not(rwd(R.rg.pred.go(1n+g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, False{}}, x))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(1n+g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, False{}}, x)))) : P.H & U32}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(n, x), True{}, e) :
        {R.rg.pred.w(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x)) == (P.err_if(Bool.not(rwd(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x)))) : P.H & U32}
      ih1
    case False{}:
      %Equal.sym(Bool, U32.is_eq(n, x), False{}, e) :
        {R.rg.pred.w(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x)) == (P.err_if(Bool.not(rwd(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p), x)))) : P.H & U32}
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (n + 3 : U32))) :
        {R.rg.pred.w(R.rg.pred.go(g, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), n), x)) == (P.err_if(Bool.not(rwd(R.rg.pred.go(g, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), n), x))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), n), x)))) : P.H & U32}
      ih2

def go_pair(f: Nat, +t: LAT.Tree<U32>, -a: Array<V.Val>, +n: U32, +p: U32, +found: Maybe<&2, U32>, +done: Bool, +x: U32) ->
  {R.rg.pred.w(R.rg.pred.go(f, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, done}, x)) == (P.err_if(Bool.not(rwd(R.rg.pred.go(f, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, done}, x))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(f, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, done}, x)))) : P.H & U32}:
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
def pred_pair(+t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +x: U32, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}) ->
  {R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x) == (P.err_if(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x)), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x))) : P.H & U32}:
  %Equal.sym(Array<U32> & U32, Array.size(U32, LAT.fromT(U32, t)), (LAT.fromT(U32, t), U32.shln(1, d)), LA.size_pair(U32, LAT.fromT(U32, t), d, hft)) :
    {R.rg.pred.f(R.rg.fuel.s(_, a), x) == (P.err_if(Bool.not(pdone.f(R.rg.fuel.s(_, a), x)), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, U32, R.rg.pred.f(R.rg.fuel.s(_, a), x))) : P.H & U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 3 : U32))) :
    {R.rg.pred.w(R.rg.pred.go(U32.to_nat(U32.shln(1, d)), R.rw.on(P.rd.fin(KM.m_get.fin(_), a), x), x)) == (P.err_if(Bool.not(rwd(R.rg.pred.go(U32.to_nat(U32.shln(1, d)), R.rw.on(P.rd.fin(KM.m_get.fin(_), a), x), x))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(U32.to_nat(U32.shln(1, d)), R.rw.on(P.rd.fin(KM.m_get.fin(_), a), x), x)))) : P.H & U32}
  go_pair(U32.to_nat(U32.shln(1, d)), t, a, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), x, None{}, False{}, x)

# and where the walk is done, the heap as it was
def pred_pair_ok(+t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +x: U32, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hdone: {pdone(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x) == True{} : Bool}) ->
  {R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x))) : P.H & U32}:
  ME.subst(Bool, q => {R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x) == (P.err_if(Bool.not(q), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x))) : P.H & U32},
    pdone(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x), True{}, hdone, pred_pair(t, a, d, x, hft))

# a raised error's heap: in its parts, its words perfect, every word but
# the error count's as it was, a closed ring kept where that word is no
# member's word 3
def eif_parts(+b: Bool, -w: Array<U32>, -a: Array<V.Val>, m: LAT.Mirror(U32, w)) ->
  {P.H{KM.MG{RG.words(P.err_if(b, P.H{KM.MG{w}, a}))}, a} == P.err_if(b, P.H{KM.MG{w}, a}) : P.H}:
  match b:
    case True{}:
      (+t, +e) = m
      %e : {P.H{KM.MG{RG.words(P.err_if(True{}, P.H{KM.MG{_}, a}))}, a} == P.err_if(True{}, P.H{KM.MG{_}, a}) : P.H}
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), P.at_errs()), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_errs()))), LA.get_pair(U32, LAT.fromT(U32, t), P.at_errs())) :
        {P.H{KM.MG{RG.words(P.h_err.n(KM.m_get.fin(_), a))}, a} == P.h_err.n(KM.m_get.fin(_), a) : P.H}
      {==}
    case False{}:
      {==}

def eif_full(+b: Bool, -w: Array<U32>, -a: Array<V.Val>, +d: Nat, hf: {AD.full(U32, w, d) == True{} : Bool}, m: LAT.Mirror(U32, w)) ->
  {AD.full(U32, RG.words(P.err_if(b, P.H{KM.MG{w}, a})), d) == True{} : Bool}:
  match b:
    case True{}:
      (+t, +e) = m
      +hft = LAP.full_t(U32, w, t, d, e, hf)
      %e : {AD.full(U32, RG.words(P.err_if(True{}, P.H{KM.MG{_}, a})), d) == True{} : Bool}
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), P.at_errs()), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_errs()))), LA.get_pair(U32, LAT.fromT(U32, t), P.at_errs())) :
        {AD.full(U32, RG.words(P.h_err.n(KM.m_get.fin(_), a)), d) == True{} : Bool}
      LA.set_full(U32, LAT.fromT(U32, t), d, P.at_errs(), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_errs())) + 1 : U32), hft)
    case False{}:
      hf

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
  %Equal.sym(Array<U32> & U32, Array.size(U32, LAT.fromT(U32, t)), (LAT.fromT(U32, t), U32.shln(1, d)), LA.size_pair(U32, LAT.fromT(U32, t), d, hft)) :
    {RG.has(xs, Pair.snd(P.H, U32, R.rg.pred.f(R.rg.fuel.s(_, a), x))) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 3 : U32))) :
    {RG.has(xs, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(U32.to_nat(U32.shln(1, d)), R.rw.on(P.rd.fin(KM.m_get.fin(_), a), x), x)))) == True{} : Bool}
  pred_mem(U32.to_nat(U32.shln(1, d)), t, a, d, xs, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), x, None{}, False{}, x, hft, hd32, hct, link_mem(t, d, xs, x, hft, hd32, hct, hx), hx)

def Laws.pred_in_ring(w, a, d, x, xs, hf, hd32, hc, hx):
  pred_in_ring.go(w, a, d, x, xs, hf, hd32, hc, hx, LAT.mirror(U32, w))

# a word off the ring's links is off each member's word 3
def links_at(ys: List<&2, U32>, +d: Nat, +i: U32, +m: U32,
    +ho: {RG.off.links(ys, d, i) == True{} : Bool}, hm: {RG.has(ys, m) == True{} : Bool}) ->
    {Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 3 : U32), d))) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 3 : U32), d))) == True{} : Bool}, MB.false_ne_true()(hm))
    case Con{+z, +t}:
      +hz = MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((z + 3 : U32), d))), RG.off.links(t, d, i), ho)
      +ht = MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((z + 3 : U32), d))), RG.off.links(t, d, i), ho)
      or_cases(U32.is_eq(z, m), RG.has(t, m), Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 3 : U32), d))), hm,
        e => ME.subst(U32, q => {Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((q + 3 : U32), d))) == True{} : Bool}, z, m, MS.u32_eq_of_is_eq(z, m, e), hz),
        hh => links_at(t, d, i, m, ht, hh))

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

# Joins (glam/ring.bend's join; cells-freeze.nested.host.join)

def off_w0(+d: Nat, +m: U32, +j: U32, +h: {RG.off.node(d, m, j) == True{} : Bool}) -> {Nat.is_eq(AD.slot(m, d), AD.slot(j, d)) == False{} : Bool}:
  MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(m, d), AD.slot(j, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))), (Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))) && (Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))) && Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d))))), h))

def off_w1(+d: Nat, +m: U32, +j: U32, +h: {RG.off.node(d, m, j) == True{} : Bool}) -> {Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}:
  MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), (Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))) && Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d)))), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))), (Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))) && (Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))) && Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d))))), h)))

# a link, its static tests split: the heap after it in its parts
def lx_parts(+sy: Bool, +sz: Bool, -w: Array<U32>, -a: Array<V.Val>, +y: U32, +z: U32) ->
    {P.H{KM.MG{RG.words(P.link.to(sz, P.link.to(sy, P.H{KM.MG{w}, a}, y, z), z, y))}, a} == P.link.to(sz, P.link.to(sy, P.H{KM.MG{w}, a}, y, z), z, y) : P.H}:
  match sy:
    case True{}:
      match sz:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match sz:
        case True{}:
          {==}
        case False{}:
          {==}

def lx_full(+sy: Bool, +sz: Bool, +t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +y: U32, +z: U32,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}) -> {AD.full(U32, RG.words(P.link.to(sz, P.link.to(sy, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, z), z, y)), d) == True{} : Bool}:
  match sy:
    case True{}:
      match sz:
        case True{}:
          hft
        case False{}:
          LA.set_full(U32, LAT.fromT(U32, t), d, (z + 1 : U32), y, hft)
    case False{}:
      match sz:
        case True{}:
          LA.set_full(U32, LAT.fromT(U32, t), d, (y + 1 : U32), z, hft)
        case False{}:
          LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), d, (z + 1 : U32), y, LA.set_full(U32, LAT.fromT(U32, t), d, (y + 1 : U32), z, hft))

def lx_keeps(+sy: Bool, +sz: Bool, +t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +y: U32, +z: U32, +j: U32,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hy: {Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hz: {Nat.is_eq(AD.slot((z + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}) ->
    {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.link.to(sz, P.link.to(sy, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, z), z, y)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)) : U32}:
  match sy:
    case True{}:
      match sz:
        case True{}:
          {==}
        case False{}:
          LA.get_set_other(U32, LAT.fromT(U32, t), d, (z + 1 : U32), j, y, hft, hd32, hz)
    case False{}:
      match sz:
        case True{}:
          LA.get_set_other(U32, LAT.fromT(U32, t), d, (y + 1 : U32), j, z, hft, hd32, hy)
        case False{}:
          Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), (z + 1 : U32), y), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), LA.get_set_other(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), d, (z + 1 : U32), j, y, LA.set_full(U32, LAT.fromT(U32, t), d, (y + 1 : U32), z, hft), hd32, hz), LA.get_set_other(U32, LAT.fromT(U32, t), d, (y + 1 : U32), j, z, hft, hd32, hy))

# an unlink: the heap after it in its parts, its words perfect, every
# word off the ring as it was
def ul_parts(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +x: U32, hf: {AD.full(U32, w, d) == True{} : Bool}, m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
    {P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{w}, a}, x))}, a} == R.rg.unlink(P.H{KM.MG{w}, a}, x) : P.H}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  %e : {P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{_}, a}, x))}, a} == R.rg.unlink(P.H{KM.MG{_}, a}, x) : P.H}
  %ea : {P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x))}, _} == R.rg.unlink(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x) : P.H}
  %Equal.sym(P.H & U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x), (P.err_if(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))), pred_pair(t, LAT.fromT(V.Val, ta), d, x, hft)) :
    {P.H{KM.MG{RG.words(R.rg.unlink.p(_, x))}, LAT.fromT(V.Val, ta)} == R.rg.unlink.p(_, x) : P.H}
  %eif_parts(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), LAT.mirror(U32, LAT.fromT(U32, t))) :
    {P.H{KM.MG{RG.words(R.rg.unlink.set(R.rg.next(_, x), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))))}, LAT.fromT(V.Val, ta)} == R.rg.unlink.set(R.rg.next(_, x), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))) : P.H}
  %Equal.sym(Array<U32> & U32, Array.get(U32, RG.words(P.err_if(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)})), (x + 3 : U32)), (RG.words(P.err_if(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)})), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.err_if(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)})), (x + 3 : U32)))), LA.get_pair(U32, RG.words(P.err_if(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)})), (x + 3 : U32))) :
    {P.H{KM.MG{RG.words(R.rg.unlink.set(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))))}, LAT.fromT(V.Val, ta)} == R.rg.unlink.set(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))) : P.H}
  {==}

def ul_full(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +x: U32, hf: {AD.full(U32, w, d) == True{} : Bool},
    m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) -> {AD.full(U32, RG.words(R.rg.unlink(P.H{KM.MG{w}, a}, x)), d) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  %e : {AD.full(U32, RG.words(R.rg.unlink(P.H{KM.MG{_}, a}, x)), d) == True{} : Bool}
  %ea : {AD.full(U32, RG.words(R.rg.unlink(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x)), d) == True{} : Bool}
  %Equal.sym(P.H & U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x), (P.err_if(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))), pred_pair(t, LAT.fromT(V.Val, ta), d, x, hft)) :
    {AD.full(U32, RG.words(R.rg.unlink.p(_, x)), d) == True{} : Bool}
  %eif_parts(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), LAT.mirror(U32, LAT.fromT(U32, t))) :
    {AD.full(U32, RG.words(R.rg.unlink.set(R.rg.next(_, x), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)))), d) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, RG.words(P.err_if(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)})), (x + 3 : U32)), (RG.words(P.err_if(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)})), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.err_if(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)})), (x + 3 : U32)))), LA.get_pair(U32, RG.words(P.err_if(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)})), (x + 3 : U32))) :
    {AD.full(U32, RG.words(R.rg.unlink.set(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)))), d) == True{} : Bool}
  LA.set_full(U32, RG.words(P.err_if(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)})), d, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.err_if(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)})), (x + 3 : U32))), eif_full(Bool.not(pdone(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, hft, LAT.mirror(U32, LAT.fromT(U32, t))))

# a free: the heap after it in its parts, its words perfect, every word
# off the node and the head as it was (as spike's free_keeps, on words)
def fr_parts(-w: Array<U32>, -a: Array<V.Val>, +r: U32, m: LAT.Mirror(U32, w)) ->
    {P.H{KM.MG{RG.words(P.free(P.H{KM.MG{w}, a}, r))}, a} == P.free(P.H{KM.MG{w}, a}, r) : P.H}:
  (+t, +e) = m
  %e : {P.H{KM.MG{RG.words(P.free(P.H{KM.MG{_}, a}, r))}, a} == P.free(P.H{KM.MG{_}, a}, r) : P.H}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), LA.get_pair(U32, LAT.fromT(U32, t), P.at_fh())) :
    {P.H{KM.MG{RG.words(P.free.fh(KM.m_get.fin(_), a, r))}, a} == P.free.fh(KM.m_get.fin(_), a, r) : P.H}
  {==}

def fr_full(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +r: U32, hf: {AD.full(U32, w, d) == True{} : Bool},
    m: LAT.Mirror(U32, w)) -> {AD.full(U32, RG.words(P.free(P.H{KM.MG{w}, a}, r)), d) == True{} : Bool}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  %e : {AD.full(U32, RG.words(P.free(P.H{KM.MG{_}, a}, r)), d) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), LA.get_pair(U32, LAT.fromT(U32, t), P.at_fh())) :
    {AD.full(U32, RG.words(P.free.fh(KM.m_get.fin(_), a, r)), d) == True{} : Bool}
  LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), d, P.at_fh(), ((r >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), d, (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t), d, P.base(r), 0, hft)))

def fr_keeps(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +r: U32, +j: U32,
    hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +h0: {Nat.is_eq(AD.slot(P.base(r), d), AD.slot(j, d)) == False{} : Bool}, +h1: {Nat.is_eq(AD.slot((P.base(r) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool},
    m: LAT.Mirror(U32, w)) ->
    {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{w}, a}, r)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, w, j)) : U32}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  %e : {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{_}, a}, r)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, _, j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), LA.get_pair(U32, LAT.fromT(U32, t), P.at_fh())) :
    {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free.fh(KM.m_get.fin(_), a, r)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)) : U32}
  Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), P.at_fh(), ((r >> 2n : U32) + 1 : U32)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), d, P.at_fh(), j, ((r >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), d, (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t), d, P.base(r), 0, hft)), hd32, hh), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), LA.get_set_other(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), d, (P.base(r) + 1 : U32), j, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t), d, P.base(r), 0, hft), hd32, h1), LA.get_set_other(U32, LAT.fromT(U32, t), d, P.base(r), j, 0, hft, hd32, h0)))

# The ring exact (cells-freeze.nested.host.ring.exact)

def sub_cons_r(ys: List<&2, U32>, +z: U32, +M: List<&2, U32>, +h: {RG.sub(ys, M) == True{} : Bool}) -> {RG.sub(ys, Con{z, M}) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      MB.and_eq_true(RG.has(Con{z, M}, y), RG.sub(r, Con{z, M}), has_cons(z, M, y, MB.eq_true_of_and_left(RG.has(M, y), RG.sub(r, M), h)), sub_cons_r(r, z, M, MB.eq_true_of_and_right(RG.has(M, y), RG.sub(r, M), h)))

def sub_refl(ys: List<&2, U32>) -> {RG.sub(ys, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      MB.and_eq_true(RG.has(Con{y, r}, y), RG.sub(r, Con{y, r}), has_self(y, r), sub_cons_r(r, y, r, sub_refl(r)))

def or_false_l(+a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MB.true_ne_false()(h))
    case False{}:
      {==}

def or_false_r(+a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, MB.true_ne_false()(h))
    case False{}:
      h

# a link that is n, n a member, is a member
def li_of_is(m: Maybe<&2, U32>, +b: U32, +M: List<&2, U32>, h: {RG.link.is.m(m, b) == True{} : Bool}, hb: {RG.has(M, b) == True{} : Bool}) ->
    {RG.link.in.m(m, M) == True{} : Bool}:
  match m:
    case Some{+l}:
      ME.subst(U32, q => {RG.has(M, q) == True{} : Bool}, b, l, Equal.sym(U32, l, b, MS.u32_eq_of_is_eq(l, b, h)), hb)
    case None{}:
      Empty.absurd({RG.link.in.m(None{}, M) == True{} : Bool}, MB.false_ne_true()(h))

# a chain among members: each of its links a member's
def cl_chain(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +M: List<&2, U32>, +a: U32, +b: U32,
    +hch: {RG.chain(v, d, ys, a, b) == True{} : Bool}, +hb: {RG.has(M, b) == True{} : Bool}, +hs: {RG.sub(ys, M) == True{} : Bool}) ->
    {Bool.and(RG.link.in(v, d, M, a), RG.closed.go(v, d, M, ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      MB.and_eq_true(RG.link.in(v, d, M, a), True{}, li_of_is(List.get(&2, U32, v, AD.slot((a + 3 : U32), d)), b, M, hch, hb), {==})
    case Con{+y, +r}:
      +hy = MB.eq_true_of_and_left(RG.has(M, y), RG.sub(r, M), hs)
      +ih = cl_chain(r, v, d, M, y, b, MB.eq_true_of_and_right(RG.link.is(v, d, a, y), RG.chain(v, d, r, y, b), hch), hb, MB.eq_true_of_and_right(RG.has(M, y), RG.sub(r, M), hs))
      MB.and_eq_true(RG.link.in(v, d, M, a), RG.closed.go(v, d, M, Con{y, r}), li_of_is(List.get(&2, U32, v, AD.slot((a + 3 : U32), d)), y, M, MB.eq_true_of_and_left(RG.link.is(v, d, a, y), RG.chain(v, d, r, y, b), hch), hy), ih)

# the exact ring is closed
def ring_closed(+v: List<&2, U32>, +d: Nat, +s: U32, +t: List<&2, U32>, +hr: {RG.ring(v, d, s, t) == True{} : Bool}) ->
    {RG.closed(v, d, Con{s, t}) == True{} : Bool}:
  cl_chain(t, v, d, Con{s, t}, s, s, MB.eq_true_of_and_left(RG.chain(v, d, t, s, s), RG.apart.all(Con{s, t}, d), hr), has_self(s, t), sub_cons_r(t, s, t, sub_refl(t)))

# a chain split at a member, and two joined
def ch_split(pre: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +x: U32, +post: List<&2, U32>, +a: U32, +b: U32,
    +h: {RG.chain(v, d, List.append(&2, U32, pre, Con{x, post}), a, b) == True{} : Bool}) ->
    {Bool.and(RG.chain(v, d, pre, a, x), RG.chain(v, d, post, x, b)) == True{} : Bool}:
  match pre:
    case Nil{}:
      h
    case Con{+y, +r}:
      +ih = ch_split(r, v, d, x, post, y, b, MB.eq_true_of_and_right(RG.link.is(v, d, a, y), RG.chain(v, d, List.append(&2, U32, r, Con{x, post}), y, b), h))
      MB.and_eq_true(Bool.and(RG.link.is(v, d, a, y), RG.chain(v, d, r, y, x)), RG.chain(v, d, post, x, b), MB.and_eq_true(RG.link.is(v, d, a, y), RG.chain(v, d, r, y, x), MB.eq_true_of_and_left(RG.link.is(v, d, a, y), RG.chain(v, d, List.append(&2, U32, r, Con{x, post}), y, b), h), MB.eq_true_of_and_left(RG.chain(v, d, r, y, x), RG.chain(v, d, post, x, b), ih)), MB.eq_true_of_and_right(RG.chain(v, d, r, y, x), RG.chain(v, d, post, x, b), ih))

def ch_join(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +a: U32, +m: U32, +zs: List<&2, U32>, +b: U32,
    +h1: {RG.chain(v, d, ys, a, m) == True{} : Bool}, +h2: {RG.chain(v, d, zs, m, b) == True{} : Bool}) -> {RG.chain(v, d, List.append(&2, U32, ys, Con{m, zs}), a, b) == True{} : Bool}:
  match ys:
    case Nil{}:
      MB.and_eq_true(RG.link.is(v, d, a, m), RG.chain(v, d, zs, m, b), h1, h2)
    case Con{+y, +r}:
      MB.and_eq_true(RG.link.is(v, d, a, y), RG.chain(v, d, List.append(&2, U32, r, Con{m, zs}), y, b), MB.eq_true_of_and_left(RG.link.is(v, d, a, y), RG.chain(v, d, r, y, m), h1), ch_join(r, v, d, y, m, zs, b, MB.eq_true_of_and_right(RG.link.is(v, d, a, y), RG.chain(v, d, r, y, m), h1), h2))

def last_app(post: List<&2, U32>, +s: U32, +pre: List<&2, U32>, +x: U32) ->
    {RG.last(List.append(&2, U32, post, Con{s, pre}), x) == RG.last(pre, s) : U32}:
  match post:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      last_app(r, s, pre, y)

def has_app_mid(A: List<&2, U32>, +x: U32, +B: List<&2, U32>) -> {RG.has(List.append(&2, U32, A, Con{x, B}), x) == True{} : Bool}:
  match A:
    case Nil{}:
      has_self(x, B)
    case Con{+e, +r}:
      has_cons(e, List.append(&2, U32, r, Con{x, B}), x, has_app_mid(r, x, B))

def apart_app(A: List<&2, U32>, +B: List<&2, U32>, +d: Nat, +x: U32, +ha: {RG.apart(A, d, x) == True{} : Bool}, +hb: {RG.apart(B, d, x) == True{} : Bool}) ->
    {RG.apart(List.append(&2, U32, A, B), d, x) == True{} : Bool}:
  match A:
    case Nil{}:
      hb
    case Con{+e, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((e + 3 : U32), d))), RG.apart(List.append(&2, U32, r, B), d, x), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((e + 3 : U32), d))), RG.apart(r, d, x), ha), apart_app(r, B, d, x, MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((e + 3 : U32), d))), RG.apart(r, d, x), ha), hb))

# in an apart list, a member listed before x is apart from x, and so is
# each after it
def ap_before(A: List<&2, U32>, +B: List<&2, U32>, +d: Nat, +x: U32, +h: {RG.apart.all(List.append(&2, U32, A, Con{x, B}), d) == True{} : Bool}) ->
    {Bool.and(RG.apart(A, d, x), RG.apart(B, d, x)) == True{} : Bool}:
  match A:
    case Nil{}:
      MB.eq_true_of_and_left(RG.apart(B, d, x), RG.apart.all(B, d), h)
    case Con{+e, +r}:
      +he = MB.eq_true_of_and_left(RG.apart(List.append(&2, U32, r, Con{x, B}), d, e), RG.apart.all(List.append(&2, U32, r, Con{x, B}), d), h)
      +ih = ap_before(r, B, d, x, MB.eq_true_of_and_right(RG.apart(List.append(&2, U32, r, Con{x, B}), d, e), RG.apart.all(List.append(&2, U32, r, Con{x, B}), d), h))
      +hex = ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((e + 3 : U32), d), AD.slot((x + 3 : U32), d)), Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((e + 3 : U32), d)),
        MN.is_eq_comm(AD.slot((e + 3 : U32), d), AD.slot((x + 3 : U32), d)), apart_at(List.append(&2, U32, r, Con{x, B}), d, e, x, he, has_app_mid(r, x, B)))
      MB.and_eq_true(RG.apart(Con{e, r}, d, x), RG.apart(B, d, x), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((e + 3 : U32), d))), RG.apart(r, d, x), hex, MB.eq_true_of_and_left(RG.apart(r, d, x), RG.apart(B, d, x), ih)), MB.eq_true_of_and_right(RG.apart(r, d, x), RG.apart(B, d, x), ih))

# apart from every member, so none of them
def an_step(+z: U32, +x: U32, +d: Nat, +r: List<&2, U32>, +b: Bool, e: {U32.is_eq(z, x) == b : Bool},
    hz: {Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((z + 3 : U32), d))) == True{} : Bool}, hr: {RG.has(r, x) == False{} : Bool}) -> {Bool.or(b, RG.has(r, x)) == False{} : Bool}:
  match b:
    case True{}:
      +hzz = ME.subst(U32, q => {Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((q + 3 : U32), d))) == True{} : Bool}, z, x, MS.u32_eq_of_is_eq(z, x, e), hz)
      +hff = Equal.trans(Bool, False{}, Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((x + 3 : U32), d))), True{},
        ME.subst(Bool, q => {False{} == Bool.not(q) : Bool}, True{}, Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((x + 3 : U32), d)),
          Equal.sym(Bool, Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((x + 3 : U32), d)), True{}, MN.is_eq_refl(AD.slot((x + 3 : U32), d))), {==}), hzz)
      Empty.absurd({Bool.or(True{}, RG.has(r, x)) == False{} : Bool}, MB.false_ne_true()(hff))
    case False{}:
      hr

def apart_notin(L: List<&2, U32>, +d: Nat, +x: U32, +h: {RG.apart(L, d, x) == True{} : Bool}) -> {RG.has(L, x) == False{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      an_step(z, x, d, r, U32.is_eq(z, x), {==}, MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((z + 3 : U32), d))), RG.apart(r, d, x), h),
        apart_notin(r, d, x, MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((z + 3 : U32), d))), RG.apart(r, d, x), h)))

# lengths: a list split at a member keeps its length rotated
def len_mid(A: List<&2, U32>, +x: U32, +B: List<&2, U32>) -> {List.length(&2, U32, List.append(&2, U32, A, Con{x, B})) == 1n+List.length(&2, U32, List.append(&2, U32, A, B)) : Nat}:
  match A:
    case Nil{}:
      {==}
    case Con{+e, +r}:
      %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, r, Con{x, B})), 1n+List.length(&2, U32, List.append(&2, U32, r, B)), len_mid(r, x, B)) : {1n+_ == 1n+1n+List.length(&2, U32, List.append(&2, U32, r, B)) : Nat}
      {==}

def len_comm(A: List<&2, U32>, +B: List<&2, U32>) -> {List.length(&2, U32, List.append(&2, U32, A, B)) == List.length(&2, U32, List.append(&2, U32, B, A)) : Nat}:
  match A:
    case Nil{}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, B, Nil{}), B, ML.append_nil(&2, U32, B)) : {List.length(&2, U32, B) == List.length(&2, U32, _) : Nat}
      {==}
    case Con{+e, +r}:
      %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, B, Con{e, r})), 1n+List.length(&2, U32, List.append(&2, U32, B, r)), len_mid(B, e, r)) : {1n+List.length(&2, U32, List.append(&2, U32, r, B)) == _ : Nat}
      %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, r, B)), List.length(&2, U32, List.append(&2, U32, B, r)), len_comm(r, B)) : {1n+_ == 1n+List.length(&2, U32, List.append(&2, U32, B, r)) : Nat}
      {==}

def len_rot(+pre: List<&2, U32>, +x: U32, +post: List<&2, U32>, +s: U32) ->
    {List.length(&2, U32, List.append(&2, U32, pre, Con{x, post})) == List.length(&2, U32, List.append(&2, U32, post, Con{s, pre})) : Nat}:
  %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, pre, Con{x, post})), 1n+List.length(&2, U32, List.append(&2, U32, pre, post)), len_mid(pre, x, post)) : {_ == List.length(&2, U32, List.append(&2, U32, post, Con{s, pre})) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, post, Con{s, pre})), 1n+List.length(&2, U32, List.append(&2, U32, post, pre)), len_mid(post, s, pre)) : {1n+List.length(&2, U32, List.append(&2, U32, pre, post)) == _ : Nat}
  %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, pre, post)), List.length(&2, U32, List.append(&2, U32, post, pre)), len_comm(pre, post)) : {1n+_ == 1n+List.length(&2, U32, List.append(&2, U32, post, pre)) : Nat}
  {==}

# a walk done stays as it is, its next step returning it
def done_stays(+g: Nat, -h: P.H, +n: U32, +p: U32, -found: Maybe<&2, U32>, +x: U32) ->
    {R.rg.pred.go(g, R.Rw{h, n, p, found, True{}}, x) == R.Rw{h, n, p, found, True{}} : R.Rw}:
  match g:
    case 0n:
      {==}
    case 1n+(+k):
      {==}

# the walk along a chain from p to x, x in none of it, with fuel enough,
# stops at its last
def wk(L: List<&2, U32>, f: Nat, +t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +p: U32, +x: U32,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hch: {RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, L, p, x) == True{} : Bool}, +hnot: {RG.has(L, x) == False{} : Bool}, +hfu: {Nat.is_lt(List.length(&2, U32, L), f) == True{} : Bool}) ->
    {Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(f, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, None{}, False{}}, x))) == RG.last(L, p) : U32}:
  match L:
    case Nil{}:
      match f:
        case 0n:
          Empty.absurd({Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(0n, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, None{}, False{}}, x))) == p : U32}, MB.false_ne_true()(hfu))
        case 1n+(+g):
          +hN = LAB.subst(Maybe<&2, U32>, mm => {RG.link.is.m(mm, x) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (p + 3 : U32), hft, hd32)), hch)
          %Equal.sym(Bool, U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), x), True{}, hN) :
            {Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p), x))) == p : U32}
          %Equal.sym(R.Rw, R.rg.pred.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, Some{p}, True{}}, x), R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, Some{p}, True{}}, done_stays(g, P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, Some{p}, x)) :
            {Pair.snd(P.H, U32, R.rg.pred.w(_)) == p : U32}
          {==}
    case Con{+y, +r}:
      match f:
        case 0n:
          Empty.absurd({Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(0n, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, None{}, False{}}, x))) == RG.last(r, y) : U32}, MB.false_ne_true()(hfu))
        case 1n+(+g):
          +hNy = LAB.subst(Maybe<&2, U32>, mm => {RG.link.is.m(mm, y) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (p + 3 : U32), hft, hd32)), MB.eq_true_of_and_left(RG.link.is(AD.view(U32, LAT.fromT(U32, t)), d, p, y), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, r, y, x), hch))
          +hyx = or_false_l(U32.is_eq(y, x), RG.has(r, x), hnot)
          %Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), y, MS.u32_eq_of_is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), y, hNy)) :
            {Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.rw.pred.k(U32.is_eq(_, x), P.H{KM.MG{LAT.fromT(U32, t)}, a}, _, p), x))) == RG.last(r, y) : U32}
          %Equal.sym(Bool, U32.is_eq(y, x), False{}, hyx) :
            {Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, p), x))) == RG.last(r, y) : U32}
          %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (y + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (y + 3 : U32))) :
            {Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(g, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), y), x))) == RG.last(r, y) : U32}
          wk(r, g, t, a, d, y, x, hft, hd32, MB.eq_true_of_and_right(RG.link.is(AD.view(U32, LAT.fromT(U32, t)), d, p, y), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, r, y, x), hch), or_false_r(U32.is_eq(y, x), RG.has(r, x), hnot), hfu)

# the walk from a cursor of an exact ring finds the one listed before it
def pred_exact.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +pre: List<&2, U32>, +x: U32, +post: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pre, Con{x, post})) == True{} : Bool}, hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pre, Con{x, post})), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  m: LAT.Mirror(U32, w)) ->
  {Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{w}, a}, x)) == RG.last(pre, s) : U32}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, List.append(&2, U32, pre, Con{x, post})) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hch = MB.eq_true_of_and_left(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, List.append(&2, U32, pre, Con{x, post}), s, s), RG.apart.all(Con{s, List.append(&2, U32, pre, Con{x, post})}, d), hrt)
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, List.append(&2, U32, pre, Con{x, post}), s, s), RG.apart.all(Con{s, List.append(&2, U32, pre, Con{x, post})}, d), hrt)
  +sp = ch_split(pre, AD.view(U32, LAT.fromT(U32, t)), d, x, post, s, s, hch)
  +hL = ch_join(post, AD.view(U32, LAT.fromT(U32, t)), d, x, s, pre, x, MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, pre, s, x), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, post, x, s), sp), MB.eq_true_of_and_left(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, pre, s, x), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, post, x, s), sp))
  +ab = ap_before(Con{s, pre}, post, d, x, hap)
  +hnot = apart_notin(List.append(&2, U32, post, Con{s, pre}), d, x, apart_app(post, Con{s, pre}, d, x, MB.eq_true_of_and_right(RG.apart(Con{s, pre}, d, x), RG.apart(post, d, x), ab), MB.eq_true_of_and_left(RG.apart(Con{s, pre}, d, x), RG.apart(post, d, x), ab)))
  +hfu = ME.subst(Nat, q => {Nat.is_lt(q, U32.to_nat(U32.shln(1, d))) == True{} : Bool}, List.length(&2, U32, List.append(&2, U32, pre, Con{x, post})), List.length(&2, U32, List.append(&2, U32, post, Con{s, pre})), len_rot(pre, x, post, s), hn)
  %e : {Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{_}, a}, x)) == RG.last(pre, s) : U32}
  %Equal.sym(Array<U32> & U32, Array.size(U32, LAT.fromT(U32, t)), (LAT.fromT(U32, t), U32.shln(1, d)), LA.size_pair(U32, LAT.fromT(U32, t), d, hft)) :
    {Pair.snd(P.H, U32, R.rg.pred.f(R.rg.fuel.s(_, a), x)) == RG.last(pre, s) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 3 : U32))) :
    {Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(U32.to_nat(U32.shln(1, d)), R.rw.on(P.rd.fin(KM.m_get.fin(_), a), x), x))) == RG.last(pre, s) : U32}
  Equal.trans(U32, Pair.snd(P.H, U32, R.rg.pred.w(R.rg.pred.go(U32.to_nat(U32.shln(1, d)), R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), x, None{}, False{}}, x))), RG.last(List.append(&2, U32, post, Con{s, pre}), x), RG.last(pre, s),
    wk(List.append(&2, U32, post, Con{s, pre}), U32.to_nat(U32.shln(1, d)), t, a, d, x, x, hft, hd32, hL, hnot, hfu), last_app(post, s, pre, x))

# the walk along an exact ring is done before its fuel runs out
def wk_done(L: List<&2, U32>, f: Nat, +t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +p: U32, +x: U32,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hch: {RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, L, p, x) == True{} : Bool}, +hnot: {RG.has(L, x) == False{} : Bool}, +hfu: {Nat.is_lt(List.length(&2, U32, L), f) == True{} : Bool}) ->
    {rwd(R.rg.pred.go(f, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, None{}, False{}}, x)) == True{} : Bool}:
  match L:
    case Nil{}:
      match f:
        case 0n:
          Empty.absurd({rwd(R.rg.pred.go(0n, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, None{}, False{}}, x)) == True{} : Bool}, MB.false_ne_true()(hfu))
        case 1n+(+g):
          +hN = LAB.subst(Maybe<&2, U32>, mm => {RG.link.is.m(mm, x) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (p + 3 : U32), hft, hd32)), hch)
          %Equal.sym(Bool, U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), x), True{}, hN) :
            {rwd(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p), x)) == True{} : Bool}
          %Equal.sym(R.Rw, R.rg.pred.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, Some{p}, True{}}, x), R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, Some{p}, True{}}, done_stays(g, P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, Some{p}, x)) :
            {rwd(_) == True{} : Bool}
          {==}
    case Con{+y, +r}:
      match f:
        case 0n:
          Empty.absurd({rwd(R.rg.pred.go(0n, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, None{}, False{}}, x)) == True{} : Bool}, MB.false_ne_true()(hfu))
        case 1n+(+g):
          +hNy = LAB.subst(Maybe<&2, U32>, mm => {RG.link.is.m(mm, y) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (p + 3 : U32), hft, hd32)), MB.eq_true_of_and_left(RG.link.is(AD.view(U32, LAT.fromT(U32, t)), d, p, y), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, r, y, x), hch))
          +hyx = or_false_l(U32.is_eq(y, x), RG.has(r, x), hnot)
          %Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), y, MS.u32_eq_of_is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), y, hNy)) :
            {rwd(R.rg.pred.go(g, R.rw.pred.k(U32.is_eq(_, x), P.H{KM.MG{LAT.fromT(U32, t)}, a}, _, p), x)) == True{} : Bool}
          %Equal.sym(Bool, U32.is_eq(y, x), False{}, hyx) :
            {rwd(R.rg.pred.go(g, R.rw.pred.k(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, p), x)) == True{} : Bool}
          %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (y + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (y + 3 : U32))) :
            {rwd(R.rg.pred.go(g, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), y), x)) == True{} : Bool}
          wk_done(r, g, t, a, d, y, x, hft, hd32, MB.eq_true_of_and_right(RG.link.is(AD.view(U32, LAT.fromT(U32, t)), d, p, y), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, r, y, x), hch), or_false_r(U32.is_eq(y, x), RG.has(r, x), hnot), hfu)

def pdone_exact.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +pre: List<&2, U32>, +x: U32, +post: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pre, Con{x, post})) == True{} : Bool}, hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pre, Con{x, post})), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  m: LAT.Mirror(U32, w)) -> {pdone(P.H{KM.MG{w}, a}, x) == True{} : Bool}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, List.append(&2, U32, pre, Con{x, post})) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hch = MB.eq_true_of_and_left(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, List.append(&2, U32, pre, Con{x, post}), s, s), RG.apart.all(Con{s, List.append(&2, U32, pre, Con{x, post})}, d), hrt)
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, List.append(&2, U32, pre, Con{x, post}), s, s), RG.apart.all(Con{s, List.append(&2, U32, pre, Con{x, post})}, d), hrt)
  +sp = ch_split(pre, AD.view(U32, LAT.fromT(U32, t)), d, x, post, s, s, hch)
  +hL = ch_join(post, AD.view(U32, LAT.fromT(U32, t)), d, x, s, pre, x, MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, pre, s, x), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, post, x, s), sp), MB.eq_true_of_and_left(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, pre, s, x), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, post, x, s), sp))
  +ab = ap_before(Con{s, pre}, post, d, x, hap)
  +hnot = apart_notin(List.append(&2, U32, post, Con{s, pre}), d, x, apart_app(post, Con{s, pre}, d, x, MB.eq_true_of_and_right(RG.apart(Con{s, pre}, d, x), RG.apart(post, d, x), ab), MB.eq_true_of_and_left(RG.apart(Con{s, pre}, d, x), RG.apart(post, d, x), ab)))
  +hfu = ME.subst(Nat, q => {Nat.is_lt(q, U32.to_nat(U32.shln(1, d))) == True{} : Bool}, List.length(&2, U32, List.append(&2, U32, pre, Con{x, post})), List.length(&2, U32, List.append(&2, U32, post, Con{s, pre})), len_rot(pre, x, post, s), hn)
  %e : {pdone(P.H{KM.MG{_}, a}, x) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.size(U32, LAT.fromT(U32, t)), (LAT.fromT(U32, t), U32.shln(1, d)), LA.size_pair(U32, LAT.fromT(U32, t), d, hft)) :
    {pdone.f(R.rg.fuel.s(_, a), x) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 3 : U32))) :
    {rwd(R.rg.pred.go(U32.to_nat(U32.shln(1, d)), R.rw.on(P.rd.fin(KM.m_get.fin(_), a), x), x)) == True{} : Bool}
  wk_done(List.append(&2, U32, post, Con{s, pre}), U32.to_nat(U32.shln(1, d)), t, a, d, x, x, hft, hd32, hL, hnot, hfu)

# The ring exact through an unlink and an insert

def not_t(+b: Bool, +h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

# apartness of a part of a list, and of a list with one taken out
def apart_prefix(A: List<&2, U32>, +B: List<&2, U32>, +d: Nat, +e: U32, +h: {RG.apart(List.append(&2, U32, A, B), d, e) == True{} : Bool}) -> {RG.apart(A, d, e) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((e + 3 : U32), d), AD.slot((y + 3 : U32), d))), RG.apart(r, d, e), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((e + 3 : U32), d), AD.slot((y + 3 : U32), d))), RG.apart(List.append(&2, U32, r, B), d, e), h), apart_prefix(r, B, d, e, MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((e + 3 : U32), d), AD.slot((y + 3 : U32), d))), RG.apart(List.append(&2, U32, r, B), d, e), h)))

def apart_suffix(A: List<&2, U32>, +B: List<&2, U32>, +d: Nat, +e: U32, +h: {RG.apart(List.append(&2, U32, A, B), d, e) == True{} : Bool}) -> {RG.apart(B, d, e) == True{} : Bool}:
  match A:
    case Nil{}:
      h
    case Con{+y, +r}:
      apart_suffix(r, B, d, e, MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((e + 3 : U32), d), AD.slot((y + 3 : U32), d))), RG.apart(List.append(&2, U32, r, B), d, e), h))

def apart_drop(A: List<&2, U32>, +x: U32, +B: List<&2, U32>, +d: Nat, +e: U32, +h: {RG.apart(List.append(&2, U32, A, Con{x, B}), d, e) == True{} : Bool}) -> {RG.apart(List.append(&2, U32, A, B), d, e) == True{} : Bool}:
  match A:
    case Nil{}:
      MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((e + 3 : U32), d), AD.slot((x + 3 : U32), d))), RG.apart(B, d, e), h)
    case Con{+y, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((e + 3 : U32), d), AD.slot((y + 3 : U32), d))), RG.apart(List.append(&2, U32, r, B), d, e), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((e + 3 : U32), d), AD.slot((y + 3 : U32), d))), RG.apart(List.append(&2, U32, r, Con{x, B}), d, e), h), apart_drop(r, x, B, d, e, MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((e + 3 : U32), d), AD.slot((y + 3 : U32), d))), RG.apart(List.append(&2, U32, r, Con{x, B}), d, e), h)))

def ap_prefix(A: List<&2, U32>, +B: List<&2, U32>, +d: Nat, +h: {RG.apart.all(List.append(&2, U32, A, B), d) == True{} : Bool}) -> {RG.apart.all(A, d) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      MB.and_eq_true(RG.apart(r, d, y), RG.apart.all(r, d), apart_prefix(r, B, d, y, MB.eq_true_of_and_left(RG.apart(List.append(&2, U32, r, B), d, y), RG.apart.all(List.append(&2, U32, r, B), d), h)), ap_prefix(r, B, d, MB.eq_true_of_and_right(RG.apart(List.append(&2, U32, r, B), d, y), RG.apart.all(List.append(&2, U32, r, B), d), h)))

def ap_remove(A: List<&2, U32>, +x: U32, +B: List<&2, U32>, +d: Nat, +h: {RG.apart.all(List.append(&2, U32, A, Con{x, B}), d) == True{} : Bool}) -> {RG.apart.all(List.append(&2, U32, A, B), d) == True{} : Bool}:
  match A:
    case Nil{}:
      MB.eq_true_of_and_right(RG.apart(B, d, x), RG.apart.all(B, d), h)
    case Con{+y, +r}:
      MB.and_eq_true(RG.apart(List.append(&2, U32, r, B), d, y), RG.apart.all(List.append(&2, U32, r, B), d), apart_drop(r, x, B, d, y, MB.eq_true_of_and_left(RG.apart(List.append(&2, U32, r, Con{x, B}), d, y), RG.apart.all(List.append(&2, U32, r, Con{x, B}), d), h)), ap_remove(r, x, B, d, MB.eq_true_of_and_right(RG.apart(List.append(&2, U32, r, Con{x, B}), d, y), RG.apart.all(List.append(&2, U32, r, Con{x, B}), d), h)))

# in an apart list, a member of its first part is apart from its second
def ap_cross(A: List<&2, U32>, +B: List<&2, U32>, +d: Nat, +e: U32, +h: {RG.apart.all(List.append(&2, U32, A, B), d) == True{} : Bool}, he: {RG.has(A, e) == True{} : Bool}) -> {RG.apart(B, d, e) == True{} : Bool}:
  match A:
    case Nil{}:
      Empty.absurd({RG.apart(B, d, e) == True{} : Bool}, MB.false_ne_true()(he))
    case Con{+y, +r}:
      or_cases(U32.is_eq(y, e), RG.has(r, e), RG.apart(B, d, e), he,
        q => ME.subst(U32, z => {RG.apart(B, d, z) == True{} : Bool}, y, e, MS.u32_eq_of_is_eq(y, e, q), apart_suffix(r, B, d, y, MB.eq_true_of_and_left(RG.apart(List.append(&2, U32, r, B), d, y), RG.apart.all(List.append(&2, U32, r, B), d), h))),
        hh => ap_cross(r, B, d, e, MB.eq_true_of_and_right(RG.apart(List.append(&2, U32, r, B), d, y), RG.apart.all(List.append(&2, U32, r, B), d), h), hh))

def apart_links(ys: List<&2, U32>, +d: Nat, +x: U32, +h: {RG.apart(ys, d, x) == True{} : Bool}) -> {RG.off.links(ys, d, (x + 3 : U32)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d))), RG.off.links(r, d, (x + 3 : U32)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d))), RG.apart(r, d, x), h), apart_links(r, d, x, MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d))), RG.apart(r, d, x), h)))

def last_mem(ys: List<&2, U32>, +a: U32) -> {RG.has(Con{a, ys}, RG.last(ys, a)) == True{} : Bool}:
  match ys:
    case Nil{}:
      has_self(a, Nil{})
    case Con{+y, +r}:
      has_cons(a, Con{y, r}, RG.last(r, y), last_mem(r, y))

# chains through a write: a link elsewhere kept; the last link given n
def map_link(m: Maybe<&2, U32>, +n: U32, +x: U32, +b: U32, hm: {RG.link.is.m(m, x) == True{} : Bool}, +hnb: {U32.is_eq(n, b) == True{} : Bool}) ->
    {RG.link.is.m(Maybe.map(&2, U32, U32, z => n, m), b) == True{} : Bool}:
  match m:
    case Some{+l}:
      hnb
    case None{}:
      Empty.absurd({RG.link.is.m(None{}, b) == True{} : Bool}, MB.false_ne_true()(hm))

def lk_keep(+v: List<&2, U32>, +d: Nat, +a: U32, +b: U32, +i: U32, +n: U32, hl: {RG.link.is(v, d, a, b) == True{} : Bool}, +hs: {Nat.is_eq(AD.slot(i, d), AD.slot((a + 3 : U32), d)) == False{} : Bool}) ->
    {RG.link.is(List.set(&2, U32, v, AD.slot(i, d), n), d, a, b) == True{} : Bool}:
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((a + 3 : U32), d)), List.get(&2, U32, v, AD.slot((a + 3 : U32), d)), LAB.get_set_ne(U32, v, AD.slot(i, d), AD.slot((a + 3 : U32), d), n, hs)) :
    {RG.link.is.m(_, b) == True{} : Bool}
  hl

def ch_keep(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +a: U32, +b: U32, +i: U32, +n: U32,
    +hch: {RG.chain(v, d, ys, a, b) == True{} : Bool}, +ho: {RG.off.links(Con{a, ys}, d, i) == True{} : Bool}) -> {RG.chain(List.set(&2, U32, v, AD.slot(i, d), n), d, ys, a, b) == True{} : Bool}:
  match ys:
    case Nil{}:
      lk_keep(v, d, a, b, i, n, hch, MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(i, d), AD.slot((a + 3 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((a + 3 : U32), d))), RG.off.links(Nil{}, d, i), ho)))
    case Con{+y, +r}:
      +hs = MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(i, d), AD.slot((a + 3 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((a + 3 : U32), d))), RG.off.links(Con{y, r}, d, i), ho))
      +hor = MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((a + 3 : U32), d))), RG.off.links(Con{y, r}, d, i), ho)
      MB.and_eq_true(RG.link.is(List.set(&2, U32, v, AD.slot(i, d), n), d, a, y), RG.chain(List.set(&2, U32, v, AD.slot(i, d), n), d, r, y, b), lk_keep(v, d, a, y, i, n, MB.eq_true_of_and_left(RG.link.is(v, d, a, y), RG.chain(v, d, r, y, b), hch), hs), ch_keep(r, v, d, y, b, i, n, MB.eq_true_of_and_right(RG.link.is(v, d, a, y), RG.chain(v, d, r, y, b), hch), hor))

def ch_retarget(pre: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +a: U32, +x: U32, +n: U32, +b: U32,
    +hch: {RG.chain(v, d, pre, a, x) == True{} : Bool}, +hnb: {U32.is_eq(n, b) == True{} : Bool}, +hap: {RG.apart.all(Con{a, pre}, d) == True{} : Bool}) ->
    {RG.chain(List.set(&2, U32, v, AD.slot((RG.last(pre, a) + 3 : U32), d), n), d, pre, a, b) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, AD.slot((a + 3 : U32), d), n), AD.slot((a + 3 : U32), d)), Maybe.map(&2, U32, U32, z => n, List.get(&2, U32, v, AD.slot((a + 3 : U32), d))), ML.get_set_self(&2, U32, v, AD.slot((a + 3 : U32), d), n)) :
        {RG.link.is.m(_, b) == True{} : Bool}
      map_link(List.get(&2, U32, v, AD.slot((a + 3 : U32), d)), n, x, b, hch, hnb)
    case Con{+y, +r}:
      +ne = apart_at(Con{y, r}, d, a, RG.last(r, y), MB.eq_true_of_and_left(RG.apart(Con{y, r}, d, a), RG.apart.all(Con{y, r}, d), hap), last_mem(r, y))
      +hs = Equal.trans(Bool, Nat.is_eq(AD.slot((RG.last(r, y) + 3 : U32), d), AD.slot((a + 3 : U32), d)), Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((RG.last(r, y) + 3 : U32), d)), False{}, MN.is_eq_comm(AD.slot((RG.last(r, y) + 3 : U32), d), AD.slot((a + 3 : U32), d)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((RG.last(r, y) + 3 : U32), d)), ne))
      MB.and_eq_true(RG.link.is(List.set(&2, U32, v, AD.slot((RG.last(r, y) + 3 : U32), d), n), d, a, y), RG.chain(List.set(&2, U32, v, AD.slot((RG.last(r, y) + 3 : U32), d), n), d, r, y, b), lk_keep(v, d, a, y, (RG.last(r, y) + 3 : U32), n, MB.eq_true_of_and_left(RG.link.is(v, d, a, y), RG.chain(v, d, r, y, x), hch), hs), ch_retarget(r, v, d, y, x, n, b, MB.eq_true_of_and_right(RG.link.is(v, d, a, y), RG.chain(v, d, r, y, x), hch), hnb, MB.eq_true_of_and_right(RG.apart(Con{y, r}, d, a), RG.apart.all(Con{y, r}, d), hap)))

# the chain after an unlink: the one before x retargeted, those after
# x kept
def ul_chain(post: List<&2, U32>, +t: LAT.Tree<U32>, +d: Nat, +s: U32, +pre: List<&2, U32>, +x: U32,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hpre: {RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, pre, s, x) == True{} : Bool}, +hpost: {RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, post, x, s) == True{} : Bool},
    +hapA: {RG.apart.all(Con{s, pre}, d) == True{} : Bool}, +hcross: {RG.apart.all(List.append(&2, U32, Con{s, pre}, post), d) == True{} : Bool}) ->
    {RG.chain(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((RG.last(pre, s) + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), d, List.append(&2, U32, pre, post), s, s) == True{} : Bool}:
  match post:
    case Nil{}:
      +hNs = LAB.subst(Maybe<&2, U32>, mm => {RG.link.is.m(mm, s) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (x + 3 : U32), hft, hd32)), hpost)
      %Equal.sym(List<&2, U32>, List.append(&2, U32, pre, Nil{}), pre, ML.append_nil(&2, U32, pre)) : {RG.chain(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((RG.last(pre, s) + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), d, _, s, s) == True{} : Bool}
      ch_retarget(pre, AD.view(U32, LAT.fromT(U32, t)), d, s, x, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), s, hpre, hNs, hapA)
    case Con{+z, +r}:
      +hNz = LAB.subst(Maybe<&2, U32>, mm => {RG.link.is.m(mm, z) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (x + 3 : U32), hft, hd32)), MB.eq_true_of_and_left(RG.link.is(AD.view(U32, LAT.fromT(U32, t)), d, x, z), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, r, z, s), hpost))
      ch_join(pre, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((RG.last(pre, s) + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), d, s, z, r, s, ch_retarget(pre, AD.view(U32, LAT.fromT(U32, t)), d, s, x, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), z, hpre, hNz, hapA),
        ch_keep(r, AD.view(U32, LAT.fromT(U32, t)), d, z, s, (RG.last(pre, s) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), MB.eq_true_of_and_right(RG.link.is(AD.view(U32, LAT.fromT(U32, t)), d, x, z), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, r, z, s), hpost),
          apart_links(Con{z, r}, d, RG.last(pre, s), ap_cross(Con{s, pre}, Con{z, r}, d, RG.last(pre, s), hcross, last_mem(pre, s)))))

def unlink_exact.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +pre: List<&2, U32>, +x: U32, +post: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pre, Con{x, post})) == True{} : Bool}, +hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pre, Con{x, post})), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.ring(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{w}, a}, x))), d, s, List.append(&2, U32, pre, post)) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, List.append(&2, U32, pre, Con{x, post})) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hch = MB.eq_true_of_and_left(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, List.append(&2, U32, pre, Con{x, post}), s, s), RG.apart.all(Con{s, List.append(&2, U32, pre, Con{x, post})}, d), hrt)
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, List.append(&2, U32, pre, Con{x, post}), s, s), RG.apart.all(Con{s, List.append(&2, U32, pre, Con{x, post})}, d), hrt)
  +sp = ch_split(pre, AD.view(U32, LAT.fromT(U32, t)), d, x, post, s, s, hch)
  +eqPQ = pred_exact.go(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, pre, x, post, hft, hd32, hrt, hn, LAT.mirror(U32, LAT.fromT(U32, t)))
  +hapA = ap_prefix(Con{s, pre}, Con{x, post}, d, hap)
  +hcross = ap_remove(Con{s, pre}, x, post, d, hap)
  %e : {RG.ring(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{_}, a}, x))), d, s, List.append(&2, U32, pre, post)) == True{} : Bool}
  %ea : {RG.ring(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x))), d, s, List.append(&2, U32, pre, post)) == True{} : Bool}
  %Equal.sym(P.H & U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x), (P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))), pred_pair_ok(t, LAT.fromT(V.Val, ta), d, x, hft, pdone_exact.go(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, pre, x, post, hft, hd32, hrt, hn, LAT.mirror(U32, LAT.fromT(U32, t))))) :
    {RG.ring(AD.view(U32, RG.words(R.rg.unlink.p(_, x))), d, s, List.append(&2, U32, pre, post)) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 3 : U32))) :
    {RG.ring(AD.view(U32, RG.words(R.rg.unlink.set(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))))), d, s, List.append(&2, U32, pre, post)) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.set_view(U32, LAT.fromT(U32, t), d, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), hft, hd32)) :
    {RG.ring(_, d, s, List.append(&2, U32, pre, post)) == True{} : Bool}
  %Equal.sym(U32, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)), RG.last(pre, s), eqPQ) :
    {RG.ring(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((_ + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), d, s, List.append(&2, U32, pre, post)) == True{} : Bool}
  MB.and_eq_true(RG.chain(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((RG.last(pre, s) + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), d, List.append(&2, U32, pre, post), s, s), RG.apart.all(Con{s, List.append(&2, U32, pre, post)}, d), ul_chain(post, t, d, s, pre, x, hft, hd32, MB.eq_true_of_and_left(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, pre, s, x), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, post, x, s), sp), MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, pre, s, x), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, post, x, s), sp), hapA, hcross), hcross)

# an insert after s: s links x, x links what s did, the rest kept
def ins_link_s(+t: LAT.Tree<U32>, +d: Nat, +s: U32, +x: U32,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hsx: {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((s + 3 : U32), d)) == False{} : Bool}) -> {RG.link.is(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), d, s, x) == True{} : Bool}:
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), AD.slot((s + 3 : U32), d)), Maybe.map(&2, U32, U32, z => x, List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((s + 3 : U32), d))), ML.get_set_self(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x)) :
    {RG.link.is.m(_, x) == True{} : Bool}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((s + 3 : U32), d)), List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((s + 3 : U32), d)), LAB.get_set_ne(U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), AD.slot((s + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), hsx)) :
    {RG.link.is.m(Maybe.map(&2, U32, U32, z => x, _), x) == True{} : Bool}
  %LA.get_view(U32, LAT.fromT(U32, t), d, (s + 3 : U32), hft, hd32) :
    {RG.link.is.m(Maybe.map(&2, U32, U32, z => x, _), x) == True{} : Bool}
  Equal.trans(Bool, U32.is_eq(x, x), Nat.is_eq(U32.to_nat(x), U32.to_nat(x)), True{}, MU.u32_is_eq_to_nat(x, x), MN.is_eq_refl(U32.to_nat(x)))

def ins_link_x(+t: LAT.Tree<U32>, +d: Nat, +s: U32, +x: U32, +b: U32,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hssx: {Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((x + 3 : U32), d)) == False{} : Bool}, +hNb: {U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), b) == True{} : Bool}) -> {RG.link.is(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), d, x, b) == True{} : Bool}:
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d)), List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((x + 3 : U32), d)), LAB.get_set_ne(U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), AD.slot((x + 3 : U32), d), x, hssx)) :
    {RG.link.is.m(_, b) == True{} : Bool}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((x + 3 : U32), d)), Maybe.map(&2, U32, U32, z => Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d))), ML.get_set_self(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))))) :
    {RG.link.is.m(_, b) == True{} : Bool}
  %LA.get_view(U32, LAT.fromT(U32, t), d, (x + 3 : U32), hft, hd32) :
    {RG.link.is.m(Maybe.map(&2, U32, U32, z => Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), _), b) == True{} : Bool}
  hNb

def ins_chain(cs: List<&2, U32>, +t: LAT.Tree<U32>, +d: Nat, +s: U32, +x: U32,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hssx: {Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((x + 3 : U32), d)) == False{} : Bool},
    +hchs: {RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s) == True{} : Bool}, +hapx: {RG.apart(cs, d, x) == True{} : Bool}, +haps: {RG.apart(cs, d, s) == True{} : Bool}) ->
    {RG.chain(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), d, cs, x, s) == True{} : Bool}:
  match cs:
    case Nil{}:
      ins_link_x(t, d, s, x, s, hft, hd32, hssx, LAB.subst(Maybe<&2, U32>, mm => {RG.link.is.m(mm, s) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((s + 3 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((s + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (s + 3 : U32), hft, hd32)), hchs))
    case Con{+z, +r}:
      MB.and_eq_true(RG.link.is(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), d, x, z), RG.chain(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), d, r, z, s), ins_link_x(t, d, s, x, z, hft, hd32, hssx, LAB.subst(Maybe<&2, U32>, mm => {RG.link.is.m(mm, z) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((s + 3 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((s + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (s + 3 : U32), hft, hd32)), MB.eq_true_of_and_left(RG.link.is(AD.view(U32, LAT.fromT(U32, t)), d, s, z), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, r, z, s), hchs))), ch_keep(r, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), d, z, s, (s + 3 : U32), x, ch_keep(r, AD.view(U32, LAT.fromT(U32, t)), d, z, s, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), MB.eq_true_of_and_right(RG.link.is(AD.view(U32, LAT.fromT(U32, t)), d, s, z), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, r, z, s), hchs), apart_links(Con{z, r}, d, x, hapx)), apart_links(Con{z, r}, d, s, haps)))

def insert_exact.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {RG.ring(AD.view(U32, w), d, s, cs) == True{} : Bool}, +hx: {RG.apart(Con{s, cs}, d, x) == True{} : Bool}, m: LAT.Mirror(U32, w)) ->
  {RG.ring(AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{w}, a}, s, x))), d, s, Con{x, cs}) == True{} : Bool}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hchs = MB.eq_true_of_and_left(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hrt)
  +hapr = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hrt)
  +hsx = MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((s + 3 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((s + 3 : U32), d))), RG.apart(cs, d, x), hx))
  +hssx = Equal.trans(Bool, Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((x + 3 : U32), d)), Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((s + 3 : U32), d)), False{}, MN.is_eq_comm(AD.slot((s + 3 : U32), d), AD.slot((x + 3 : U32), d)), hsx)
  +hapx = MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((s + 3 : U32), d))), RG.apart(cs, d, x), hx)
  +haps = MB.eq_true_of_and_left(RG.apart(cs, d, s), RG.apart.all(cs, d), hapr)
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), hft)
  %e : {RG.ring(AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{_}, a}, s, x))), d, s, Con{x, cs}) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (s + 3 : U32))) :
    {RG.ring(AD.view(U32, RG.words(R.rg.insert.r(P.rd.fin(KM.m_get.fin(_), a), s, x))), d, s, Con{x, cs}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), (s + 3 : U32), x)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))))), AD.slot((s + 3 : U32), d), x), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), d, (s + 3 : U32), x, hf1, hd32)) :
    {RG.ring(_, d, s, Con{x, cs}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), LA.set_view(U32, LAT.fromT(U32, t), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), hft, hd32)) :
    {RG.ring(List.set(&2, U32, _, AD.slot((s + 3 : U32), d), x), d, s, Con{x, cs}) == True{} : Bool}
  MB.and_eq_true(RG.chain(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), d, Con{x, cs}, s, s), RG.apart.all(Con{s, Con{x, cs}}, d), MB.and_eq_true(RG.link.is(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), d, s, x), RG.chain(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), d, cs, x, s), ins_link_s(t, d, s, x, hft, hd32, hsx), ins_chain(cs, t, d, s, x, hft, hd32, hssx, hchs, hapx, haps)), MB.and_eq_true(RG.apart(Con{x, cs}, d, s), RG.apart.all(Con{x, cs}, d), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((x + 3 : U32), d))), RG.apart(cs, d, s), not_t(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((x + 3 : U32), d)), hssx), haps), MB.and_eq_true(RG.apart(cs, d, x), RG.apart.all(cs, d), hapx, MB.eq_true_of_and_right(RG.apart(cs, d, s), RG.apart.all(cs, d), hapr))))

def Laws.insert_exact(w, a, d, s, t, x, hf, hd32, hr, hx):
  insert_exact.go(w, a, d, s, t, x, hf, hd32, hr, hx, LAT.mirror(U32, w))

# The ring exact through a join

# a link off every member's word 3 keeps the ring exact
def lx_ring(+sy: Bool, +sz: Bool, +t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +y: U32, +z: U32, +s: U32, +cs: List<&2, U32>,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hr: {RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs) == True{} : Bool},
    +hoy: {RG.off.links(Con{s, cs}, d, (y + 1 : U32)) == True{} : Bool}, +hoz: {RG.off.links(Con{s, cs}, d, (z + 1 : U32)) == True{} : Bool}) ->
    {RG.ring(AD.view(U32, RG.words(P.link.to(sz, P.link.to(sy, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, z), z, y))), d, s, cs) == True{} : Bool}:
  match sy:
    case True{}:
      match sz:
        case True{}:
          hr
        case False{}:
          %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (z + 1 : U32), y)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((z + 1 : U32), d), y), LA.set_view(U32, LAT.fromT(U32, t), d, (z + 1 : U32), y, hft, hd32)) :
            {RG.ring(_, d, s, cs) == True{} : Bool}
          MB.and_eq_true(RG.chain(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((z + 1 : U32), d), y), d, cs, s, s), RG.apart.all(Con{s, cs}, d), ch_keep(cs, AD.view(U32, LAT.fromT(U32, t)), d, s, s, (z + 1 : U32), y, MB.eq_true_of_and_left(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hr), hoz), MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hr))
    case False{}:
      match sz:
        case True{}:
          %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d), z), LA.set_view(U32, LAT.fromT(U32, t), d, (y + 1 : U32), z, hft, hd32)) :
            {RG.ring(_, d, s, cs) == True{} : Bool}
          MB.and_eq_true(RG.chain(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d), z), d, cs, s, s), RG.apart.all(Con{s, cs}, d), ch_keep(cs, AD.view(U32, LAT.fromT(U32, t)), d, s, s, (y + 1 : U32), z, MB.eq_true_of_and_left(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hr), hoy), MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hr))
        case False{}:
          %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), (z + 1 : U32), y)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z)), AD.slot((z + 1 : U32), d), y), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), d, (z + 1 : U32), y, LA.set_full(U32, LAT.fromT(U32, t), d, (y + 1 : U32), z, hft), hd32)) :
            {RG.ring(_, d, s, cs) == True{} : Bool}
          %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d), z), LA.set_view(U32, LAT.fromT(U32, t), d, (y + 1 : U32), z, hft, hd32)) :
            {RG.ring(List.set(&2, U32, _, AD.slot((z + 1 : U32), d), y), d, s, cs) == True{} : Bool}
          MB.and_eq_true(RG.chain(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d), z), AD.slot((z + 1 : U32), d), y), d, cs, s, s), RG.apart.all(Con{s, cs}, d), ch_keep(cs, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d), z), d, s, s, (z + 1 : U32), y, ch_keep(cs, AD.view(U32, LAT.fromT(U32, t)), d, s, s, (y + 1 : U32), z, MB.eq_true_of_and_left(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hr), hoy), hoz), MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hr))

# a free whose writes are off every member's word 3 keeps the ring exact
def fr_ring(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +r: U32, +s: U32, +cs: List<&2, U32>,
    hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {RG.ring(AD.view(U32, w), d, s, cs) == True{} : Bool},
    +h0: {RG.off.links(Con{s, cs}, d, P.base(r)) == True{} : Bool}, +h1: {RG.off.links(Con{s, cs}, d, (P.base(r) + 1 : U32)) == True{} : Bool}, +hh: {RG.off.links(Con{s, cs}, d, P.at_fh()) == True{} : Bool}, m: LAT.Mirror(U32, w)) ->
    {RG.ring(AD.view(U32, RG.words(P.free(P.H{KM.MG{w}, a}, r))), d, s, cs) == True{} : Bool}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  %e : {RG.ring(AD.view(U32, RG.words(P.free(P.H{KM.MG{_}, a}, r))), d, s, cs) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), LA.get_pair(U32, LAT.fromT(U32, t), P.at_fh())) :
    {RG.ring(AD.view(U32, RG.words(P.free.fh(KM.m_get.fin(_), a, r))), d, s, cs) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), P.at_fh(), ((r >> 2n : U32) + 1 : U32))), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())))), AD.slot(P.at_fh(), d), ((r >> 2n : U32) + 1 : U32)), LA.set_view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), d, P.at_fh(), ((r >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), d, (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t), d, P.base(r), 0, hft)), hd32)) :
    {RG.ring(_, d, s, cs) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())))), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0)), AD.slot((P.base(r) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), d, (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t), d, P.base(r), 0, hft), hd32)) :
    {RG.ring(List.set(&2, U32, _, AD.slot(P.at_fh(), d), ((r >> 2n : U32) + 1 : U32)), d, s, cs) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(P.base(r), d), 0), LA.set_view(U32, LAT.fromT(U32, t), d, P.base(r), 0, hft, hd32)) :
    {RG.ring(List.set(&2, U32, List.set(&2, U32, _, AD.slot((P.base(r) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), AD.slot(P.at_fh(), d), ((r >> 2n : U32) + 1 : U32)), d, s, cs) == True{} : Bool}
  MB.and_eq_true(RG.chain(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(P.base(r), d), 0), AD.slot((P.base(r) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), AD.slot(P.at_fh(), d), ((r >> 2n : U32) + 1 : U32)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), ch_keep(cs, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(P.base(r), d), 0), AD.slot((P.base(r) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), d, s, s, P.at_fh(), ((r >> 2n : U32) + 1 : U32), ch_keep(cs, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(P.base(r), d), 0), d, s, s, (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), ch_keep(cs, AD.view(U32, LAT.fromT(U32, t)), d, s, s, P.base(r), 0, MB.eq_true_of_and_left(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hrt), h0), h1), hh), MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hrt))

# the join: the link off the ring's links, the two exact unlinks, the
# two frees off the ring left
def join_exact.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +pa: List<&2, U32>, +x: U32, +pb: List<&2, U32>,
  +pc: List<&2, U32>, +y: U32, +pd: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pa, Con{x, pb})) == True{} : Bool}, +hsp: {List.append(&2, U32, pa, pb) == List.append(&2, U32, pc, Con{y, pd}) : List<&2, U32>}, +hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pa, Con{x, pb})), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  +hbx: {P.base(x) == x : U32}, +hby: {P.base(y) == y : U32},
  hu: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{x, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, hw: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{x, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32)) == True{} : Bool},
  +hx0: {RG.off.links(Con{s, List.append(&2, U32, pc, pd)}, d, x) == True{} : Bool}, +hx1: {RG.off.links(Con{s, List.append(&2, U32, pc, pd)}, d, (x + 1 : U32)) == True{} : Bool}, +hy0: {RG.off.links(Con{s, List.append(&2, U32, pc, pd)}, d, y) == True{} : Bool}, +hy1: {RG.off.links(Con{s, List.append(&2, U32, pc, pd)}, d, (y + 1 : U32)) == True{} : Bool},
  +hh: {RG.off.links(Con{s, List.append(&2, U32, pc, pd)}, d, P.at_fh()) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.ring(AD.view(U32, RG.words(R.join(P.H{KM.MG{w}, a}, x, y))), d, s, List.append(&2, U32, pc, pd)) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, List.append(&2, U32, pa, Con{x, pb})) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hut = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{x, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hu)
  +hwt = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{x, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (y + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hw)
  +hr1 = lx_ring(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), s, List.append(&2, U32, pa, Con{x, pb}), hft, hd32, hrt, hut, hwt)
  +hf1 = lx_full(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), hft)
  +hr2 = unlink_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, s, pa, x, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf2 = ul_full(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, x, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hr2c = ME.subst(List<&2, U32>, q => {RG.ring(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))), d, s, q) == True{} : Bool}, List.append(&2, U32, pa, pb), List.append(&2, U32, pc, Con{y, pd}), hsp, hr2)
  +hn1 = ME.subst(Nat, q => {Nat.is_lt(q, U32.to_nat(U32.shln(1, d))) == True{} : Bool}, List.length(&2, U32, List.append(&2, U32, pa, Con{x, pb})), 1n+List.length(&2, U32, List.append(&2, U32, pa, pb)), len_mid(pa, x, pb), hn)
  +hn2 = ME.subst(List<&2, U32>, q => {Nat.is_lt(List.length(&2, U32, q), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, List.append(&2, U32, pa, pb), List.append(&2, U32, pc, Con{y, pd}), hsp,
    MN.lt_trans(List.length(&2, U32, List.append(&2, U32, pa, pb)), 1n+List.length(&2, U32, List.append(&2, U32, pa, pb)), U32.to_nat(U32.shln(1, d)), MN.lt_succ_self(List.length(&2, U32, List.append(&2, U32, pa, pb))), hn1))
  +hr3 = unlink_exact.go(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, s, pc, y, pd, hf2, hd32, hr2c, hn2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf3 = ul_full(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, y, hf2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hr4 = fr_ring(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), d, x, s, List.append(&2, U32, pc, pd), hf3, hd32, hr3, ME.subst(U32, q => {RG.off.links(Con{s, List.append(&2, U32, pc, pd)}, d, q) == True{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), hx0), ME.subst(U32, q => {RG.off.links(Con{s, List.append(&2, U32, pc, pd)}, d, (q + 1 : U32)) == True{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), hx1), hh, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))))
  +hf4 = fr_full(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), d, x, hf3, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))))
  +hr5 = fr_ring(RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, y, s, List.append(&2, U32, pc, pd), hf4, hd32, hr4, ME.subst(U32, q => {RG.off.links(Con{s, List.append(&2, U32, pc, pd)}, d, q) == True{} : Bool}, y, P.base(y), Equal.sym(U32, P.base(y), y, hby), hy0), ME.subst(U32, q => {RG.off.links(Con{s, List.append(&2, U32, pc, pd)}, d, (q + 1 : U32)) == True{} : Bool}, y, P.base(y), Equal.sym(U32, P.base(y), y, hby), hy1), hh, LAT.mirror(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))))
  %e : {RG.ring(AD.view(U32, RG.words(R.join(P.H{KM.MG{_}, a}, x, y))), d, s, List.append(&2, U32, pc, pd)) == True{} : Bool}
  %ea : {RG.ring(AD.view(U32, RG.words(R.join(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x, y))), d, s, List.append(&2, U32, pc, pd)) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 1 : U32))) :
    {RG.ring(AD.view(U32, RG.words(R.jn.u(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), x, y))), d, s, List.append(&2, U32, pc, pd)) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (y + 1 : U32))) :
    {RG.ring(AD.view(U32, RG.words(R.jn.w(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), x, y))), d, s, List.append(&2, U32, pc, pd)) == True{} : Bool}
  %lx_parts(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))) :
    {RG.ring(AD.view(U32, RG.words(P.free(P.free(R.rg.unlink(R.rg.unlink(_, x), y), x), y))), d, s, List.append(&2, U32, pc, pd)) == True{} : Bool}
  %ul_parts(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, x, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {RG.ring(AD.view(U32, RG.words(P.free(P.free(R.rg.unlink(_, y), x), y))), d, s, List.append(&2, U32, pc, pd)) == True{} : Bool}
  %ul_parts(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, y, hf2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {RG.ring(AD.view(U32, RG.words(P.free(P.free(_, x), y))), d, s, List.append(&2, U32, pc, pd)) == True{} : Bool}
  %fr_parts(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), x, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)))) :
    {RG.ring(AD.view(U32, RG.words(P.free(_, y))), d, s, List.append(&2, U32, pc, pd)) == True{} : Bool}
  %fr_parts(RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), y, LAT.mirror(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)))) :
    {RG.ring(AD.view(U32, RG.words(_)), d, s, List.append(&2, U32, pc, pd)) == True{} : Bool}
  hr5

# The ring exact stated by membership

# Bools: two falses
def or_ff(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ha) : {Bool.or(_, b) == False{} : Bool}
  hb

# The pigeonhole: numbers all distinct and below n number at most n; an
# exact ring's members' word-3 slots are so, below 2^d, the heap's words
def memN(ns: List<&2, Nat>, +n: Nat) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Nat.is_eq(h, n) || memN(t, n)

def nodupN(ns: List<&2, Nat>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Bool.not(memN(t, h)) && nodupN(t)

def allLt(ns: List<&2, Nat>, +n: Nat) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Nat.is_lt(h, n) && allLt(t, n)

def pickN(+b: Bool, l1: List<&2, Nat>, l2: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      l1
    case False{}:
      l2

def removeN(ns: List<&2, Nat>, +n: Nat) -> List<&2, Nat>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      pickN(Nat.is_eq(h, n), removeN(t, n), Con{h, removeN(t, n)})

def lt0(h: Nat) -> {Nat.is_lt(h, 0n) == False{} : Bool}:
  match h:
    case 0n:
      {==}
    case 1n+g:
      {==}

def lt_ne(h: Nat, m: Nat, +h1: {Nat.is_lt(h, 1n+m) == True{} : Bool}, +h2: {Nat.is_eq(h, m) == False{} : Bool}) -> {Nat.is_lt(h, m) == True{} : Bool}:
  match h:
    case 0n:
      match m:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, MB.true_ne_false()(h2))
        case 1n+k:
          {==}
    case 1n+g:
      match m:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+g, 0n) == True{} : Bool}, MB.true_ne_false()(Equal.trans(Bool, True{}, Nat.is_lt(g, 0n), False{}, Equal.sym(Bool, Nat.is_lt(g, 0n), True{}, h1), lt0(g))))
        case 1n+k:
          lt_ne(g, k, h1, h2)

def rm_notin(ns: List<&2, Nat>, +m: Nat, +h: {memN(ns, m) == False{} : Bool}) -> {removeN(ns, m) == ns : List<&2, Nat>}:
  match ns:
    case Nil{}:
      {==}
    case Con{+e, +r}:
      %Equal.sym(Bool, Nat.is_eq(e, m), False{}, or_false_l(Nat.is_eq(e, m), memN(r, m), h)) :
        {pickN(_, removeN(r, m), Con{e, removeN(r, m)}) == Con{e, r} : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, removeN(r, m), r, rm_notin(r, m, or_false_r(Nat.is_eq(e, m), memN(r, m), h))) :
        {Con{e, _} == Con{e, r} : List<&2, Nat>}
      {==}

def rl_go(+e: Nat, +r: List<&2, Nat>, +m: Nat, +b: Bool, +eb: {Nat.is_eq(e, m) == b : Bool}, +hnot: {memN(r, e) == False{} : Bool},
    +ih: {Nat.is_le(List.length(&2, Nat, r), 1n+List.length(&2, Nat, removeN(r, m))) == True{} : Bool}) ->
    {Nat.is_le(1n+List.length(&2, Nat, r), 1n+List.length(&2, Nat, pickN(b, removeN(r, m), Con{e, removeN(r, m)}))) == True{} : Bool}:
  match b:
    case True{}:
      +hm = ME.subst(Nat, q => {memN(r, q) == False{} : Bool}, e, m, MN.eq_of_is_eq(e, m, eb), hnot)
      %Equal.sym(List<&2, Nat>, removeN(r, m), r, rm_notin(r, m, hm)) :
        {Nat.is_le(1n+List.length(&2, Nat, r), 1n+List.length(&2, Nat, _)) == True{} : Bool}
      MN.le_refl(1n+List.length(&2, Nat, r))
    case False{}:
      ih

def rm_len(ns: List<&2, Nat>, +m: Nat, +h: {nodupN(ns) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Nat, ns), 1n+List.length(&2, Nat, removeN(ns, m))) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+e, +r}:
      rl_go(e, r, m, Nat.is_eq(e, m), {==}, MB.eq_false_of_not_eq_true(memN(r, e), MB.eq_true_of_and_left(Bool.not(memN(r, e)), nodupN(r), h)),
        rm_len(r, m, MB.eq_true_of_and_right(Bool.not(memN(r, e)), nodupN(r), h)))

def mr_go(+e: Nat, +r: List<&2, Nat>, +m: Nat, +x: Nat, +b: Bool, +hex: {Nat.is_eq(e, x) == False{} : Bool}, +ih: {memN(removeN(r, m), x) == False{} : Bool}) ->
    {memN(pickN(b, removeN(r, m), Con{e, removeN(r, m)}), x) == False{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      or_ff(Nat.is_eq(e, x), memN(removeN(r, m), x), hex, ih)

def mem_rm(ns: List<&2, Nat>, +m: Nat, +x: Nat, +h: {memN(ns, x) == False{} : Bool}) -> {memN(removeN(ns, m), x) == False{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+e, +r}:
      mr_go(e, r, m, x, Nat.is_eq(e, m), or_false_l(Nat.is_eq(e, x), memN(r, x), h), mem_rm(r, m, x, or_false_r(Nat.is_eq(e, x), memN(r, x), h)))

def rn_go(+e: Nat, +r: List<&2, Nat>, +m: Nat, +b: Bool, +hnot: {memN(r, e) == False{} : Bool}, +ih: {nodupN(removeN(r, m)) == True{} : Bool}) ->
    {nodupN(pickN(b, removeN(r, m), Con{e, removeN(r, m)})) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      MB.and_eq_true(Bool.not(memN(removeN(r, m), e)), nodupN(removeN(r, m)), not_t(memN(removeN(r, m), e), mem_rm(r, m, e, hnot)), ih)

def rm_nodup(ns: List<&2, Nat>, +m: Nat, +h: {nodupN(ns) == True{} : Bool}) -> {nodupN(removeN(ns, m)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+e, +r}:
      rn_go(e, r, m, Nat.is_eq(e, m), MB.eq_false_of_not_eq_true(memN(r, e), MB.eq_true_of_and_left(Bool.not(memN(r, e)), nodupN(r), h)),
        rm_nodup(r, m, MB.eq_true_of_and_right(Bool.not(memN(r, e)), nodupN(r), h)))

def rlt_go(+e: Nat, +r: List<&2, Nat>, +m: Nat, +b: Bool, +eb: {Nat.is_eq(e, m) == b : Bool}, +he: {Nat.is_lt(e, 1n+m) == True{} : Bool}, +ih: {allLt(removeN(r, m), m) == True{} : Bool}) ->
    {allLt(pickN(b, removeN(r, m), Con{e, removeN(r, m)}), m) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      MB.and_eq_true(Nat.is_lt(e, m), allLt(removeN(r, m), m), lt_ne(e, m, he, eb), ih)

def rm_lt(ns: List<&2, Nat>, +m: Nat, +h: {allLt(ns, 1n+m) == True{} : Bool}) -> {allLt(removeN(ns, m), m) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+e, +r}:
      rlt_go(e, r, m, Nat.is_eq(e, m), {==}, MB.eq_true_of_and_left(Nat.is_lt(e, 1n+m), allLt(r, 1n+m), h), rm_lt(r, m, MB.eq_true_of_and_right(Nat.is_lt(e, 1n+m), allLt(r, 1n+m), h)))

def ph0(ns: List<&2, Nat>, +hlt: {allLt(ns, 0n) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Nat, ns), 0n) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Empty.absurd({Nat.is_le(List.length(&2, Nat, Con{h, t}), 0n) == True{} : Bool}, MB.true_ne_false()(Equal.trans(Bool, True{}, Nat.is_lt(h, 0n), False{},
        Equal.sym(Bool, Nat.is_lt(h, 0n), True{}, MB.eq_true_of_and_left(Nat.is_lt(h, 0n), allLt(t, 0n), hlt)), lt0(h))))

def ph(n: Nat, +ns: List<&2, Nat>, +hnd: {nodupN(ns) == True{} : Bool}, +hlt: {allLt(ns, n) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Nat, ns), n) == True{} : Bool}:
  match n:
    case 0n:
      ph0(ns, hlt)
    case 1n+(+k):
      MN.le_trans(List.length(&2, Nat, ns), 1n+List.length(&2, Nat, removeN(ns, k)), 1n+k, rm_len(ns, k, hnd),
        ph(k, removeN(ns, k), rm_nodup(ns, k, hnd), rm_lt(ns, k, hlt)))

# slots of the members' word 3
def slots(ys: List<&2, U32>, +d: Nat) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{+y, t}:
      Con{AD.slot((y + 3 : U32), d), slots(t, d)}

def len_slots(ys: List<&2, U32>, +d: Nat) -> {List.length(&2, Nat, slots(ys, d)) == List.length(&2, U32, ys) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %Equal.sym(Nat, List.length(&2, Nat, slots(t, d)), List.length(&2, U32, t), len_slots(t, d)) : {1n+_ == 1n+List.length(&2, U32, t) : Nat}
      {==}

def ap_mem(ys: List<&2, U32>, +d: Nat, +y: U32, +h: {RG.apart(ys, d, y) == True{} : Bool}) -> {memN(slots(ys, d), AD.slot((y + 3 : U32), d)) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      or_ff(Nat.is_eq(AD.slot((z + 3 : U32), d), AD.slot((y + 3 : U32), d)), memN(slots(r, d), AD.slot((y + 3 : U32), d)),
        Equal.trans(Bool, Nat.is_eq(AD.slot((z + 3 : U32), d), AD.slot((y + 3 : U32), d)), Nat.is_eq(AD.slot((y + 3 : U32), d), AD.slot((z + 3 : U32), d)), False{}, MN.is_eq_comm(AD.slot((z + 3 : U32), d), AD.slot((y + 3 : U32), d)),
          MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((y + 3 : U32), d), AD.slot((z + 3 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((y + 3 : U32), d), AD.slot((z + 3 : U32), d))), RG.apart(r, d, y), h))),
        ap_mem(r, d, y, MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((y + 3 : U32), d), AD.slot((z + 3 : U32), d))), RG.apart(r, d, y), h)))

def nd_slots(ys: List<&2, U32>, +d: Nat, +h: {RG.apart.all(ys, d) == True{} : Bool}) -> {nodupN(slots(ys, d)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      MB.and_eq_true(Bool.not(memN(slots(t, d), AD.slot((y + 3 : U32), d))), nodupN(slots(t, d)), not_t(memN(slots(t, d), AD.slot((y + 3 : U32), d)), ap_mem(t, d, y, MB.eq_true_of_and_left(RG.apart(t, d, y), RG.apart.all(t, d), h))), nd_slots(t, d, MB.eq_true_of_and_right(RG.apart(t, d, y), RG.apart.all(t, d), h)))

def lt_slots(ys: List<&2, U32>, +d: Nat) -> {allLt(slots(ys, d), Nat.pow(2n, d)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      MB.and_eq_true(Nat.is_lt(AD.slot((y + 3 : U32), d), Nat.pow(2n, d)), allLt(slots(t, d), Nat.pow(2n, d)), LA.slot_lt((y + 3 : U32), d), lt_slots(t, d))

# so an exact ring has fewer cursors than the heap has words, the fuel of
# its walks: the length premise retired
def len_ok(+t: LAT.Tree<U32>, +d: Nat, +s: U32, +cs: List<&2, U32>, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hap: {RG.apart.all(Con{s, cs}, d) == True{} : Bool}) -> {Nat.is_lt(List.length(&2, U32, cs), U32.to_nat(U32.shln(1, d))) == True{} : Bool}:
  +le1 = ph(Nat.pow(2n, d), slots(Con{s, cs}, d), nd_slots(Con{s, cs}, d, hap), lt_slots(Con{s, cs}, d))
  +le2 = ME.subst(Nat, q => {Nat.is_le(q, Nat.pow(2n, d)) == True{} : Bool}, List.length(&2, Nat, slots(Con{s, cs}, d)), 1n+List.length(&2, U32, cs), len_slots(Con{s, cs}, d), le1)
  +lt1 = Equal.trans(Bool, Nat.is_lt(List.length(&2, U32, cs), Nat.pow(2n, d)), Nat.is_le(1n+List.length(&2, U32, cs), Nat.pow(2n, d)), True{}, MN.is_lt_eq_succ_le(List.length(&2, U32, cs), Nat.pow(2n, d)), le2)
  +feq = ME.subst(Array<U32> & U32, q => {U32.to_nat(Pair.snd(Array<U32>, U32, q)) == Nat.pow(2n, d) : Nat}, Array.size(U32, LAT.fromT(U32, t)), (LAT.fromT(U32, t), U32.shln(1, d)),
    LA.size_pair(U32, LAT.fromT(U32, t), d, hft), LA.size_count(U32, LAT.fromT(U32, t), d, hft, hd32))
  ME.subst(Nat, q => {Nat.is_lt(List.length(&2, U32, cs), q) == True{} : Bool}, Nat.pow(2n, d), U32.to_nat(U32.shln(1, d)), Equal.sym(Nat, U32.to_nat(U32.shln(1, d)), Nat.pow(2n, d), feq), lt1)

def pick_l(+b: Bool, l1: List<&2, U32>, l2: List<&2, U32>) -> List<&2, U32>:
  match b:
    case True{}:
      l1
    case False{}:
      l2

# those listed before x's first place, and after it
def lpre(ys: List<&2, U32>, +x: U32) -> List<&2, U32>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{+y, t}:
      pick_l(U32.is_eq(y, x), Nil{}, Con{y, lpre(t, x)})

def lpost(ys: List<&2, U32>, +x: U32) -> List<&2, U32>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{+y, +t}:
      pick_l(U32.is_eq(y, x), t, lpost(t, x))

# a member's list is those before it, it, those after
def sp_go(+t: List<&2, U32>, +y: U32, +x: U32, +b: Bool, e: {U32.is_eq(y, x) == b : Bool},
    h: {Bool.or(b, RG.has(t, x)) == True{} : Bool}, ih: {RG.has(t, x) == True{} : Bool} -> {List.append(&2, U32, lpre(t, x), Con{x, lpost(t, x)}) == t : List<&2, U32>}) ->
    {List.append(&2, U32, pick_l(b, Nil{}, Con{y, lpre(t, x)}), Con{x, pick_l(b, t, lpost(t, x))}) == Con{y, t} : List<&2, U32>}:
  match b:
    case True{}:
      ME.subst(U32, q => {Con{q, t} == Con{y, t} : List<&2, U32>}, y, x, MS.u32_eq_of_is_eq(y, x, e), {==})
    case False{}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(t, x), Con{x, lpost(t, x)}), t, ih(h)) : {Con{y, _} == Con{y, t} : List<&2, U32>}
      {==}

def split_of_has(ys: List<&2, U32>, +x: U32, h: {RG.has(ys, x) == True{} : Bool}) -> {List.append(&2, U32, lpre(ys, x), Con{x, lpost(ys, x)}) == ys : List<&2, U32>}:
  match ys:
    case Nil{}:
      Empty.absurd({List.append(&2, U32, Nil{}, Con{x, Nil{}}) == Nil{} : List<&2, U32>}, MB.false_ne_true()(h))
    case Con{+y, +t}:
      sp_go(t, y, x, U32.is_eq(y, x), {==}, h, hh => split_of_has(t, x, hh))

# the member before x is the last of a and those before x
def bl_go(+t: List<&2, U32>, +y: U32, +a: U32, +x: U32, +b: Bool, ih: {RG.before(t, y, x) == RG.last(lpre(t, x), y) : U32}) ->
    {RG.pick(b, a, RG.before(t, y, x)) == RG.last(pick_l(b, Nil{}, Con{y, lpre(t, x)}), a) : U32}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def before_last(ys: List<&2, U32>, +a: U32, +x: U32) -> {RG.before(ys, a, x) == RG.last(lpre(ys, x), a) : U32}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      bl_go(t, y, a, x, U32.is_eq(y, x), before_last(t, y, x))

# taking out what is not there changes nothing; taking out x from its
# split leaves the two parts
def without_notin(ys: List<&2, U32>, +x: U32, +h: {RG.has(ys, x) == False{} : Bool}) -> {RG.without(ys, x) == ys : List<&2, U32>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %Equal.sym(Bool, U32.is_eq(y, x), False{}, or_false_l(U32.is_eq(y, x), RG.has(t, x), h)) :
        {List.append(&2, U32, RG.keep(_, y), RG.without(t, x)) == Con{y, t} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, RG.without(t, x), t, without_notin(t, x, or_false_r(U32.is_eq(y, x), RG.has(t, x), h))) :
        {Con{y, _} == Con{y, t} : List<&2, U32>}
      {==}

def without_split(A: List<&2, U32>, +x: U32, +B: List<&2, U32>, +ha: {RG.has(A, x) == False{} : Bool}, +hb: {RG.has(B, x) == False{} : Bool}) ->
    {RG.without(List.append(&2, U32, A, Con{x, B}), x) == List.append(&2, U32, A, B) : List<&2, U32>}:
  match A:
    case Nil{}:
      %Equal.sym(Bool, U32.is_eq(x, x), True{}, Equal.trans(Bool, U32.is_eq(x, x), Nat.is_eq(U32.to_nat(x), U32.to_nat(x)), True{}, MU.u32_is_eq_to_nat(x, x), MN.is_eq_refl(U32.to_nat(x)))) :
        {List.append(&2, U32, RG.keep(_, x), RG.without(B, x)) == B : List<&2, U32>}
      without_notin(B, x, hb)
    case Con{+e, +r}:
      %Equal.sym(Bool, U32.is_eq(e, x), False{}, or_false_l(U32.is_eq(e, x), RG.has(r, x), ha)) :
        {List.append(&2, U32, RG.keep(_, e), RG.without(List.append(&2, U32, r, Con{x, B}), x)) == Con{e, List.append(&2, U32, r, B)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, RG.without(List.append(&2, U32, r, Con{x, B}), x), List.append(&2, U32, r, B), without_split(r, x, B, or_false_r(U32.is_eq(e, x), RG.has(r, x), ha), hb)) :
        {Con{e, _} == Con{e, List.append(&2, U32, r, B)} : List<&2, U32>}
      {==}

# a member other than x stays a member without x
def hw_go(+r: List<&2, U32>, +z: U32, +x: U32, +y: U32, +b: Bool, e: {U32.is_eq(z, x) == b : Bool},
    +hxy: {U32.is_eq(x, y) == False{} : Bool}, hy: {Bool.or(U32.is_eq(z, y), RG.has(r, y)) == True{} : Bool},
    ih: {RG.has(r, y) == True{} : Bool} -> {RG.has(RG.without(r, x), y) == True{} : Bool}) ->
    {RG.has(List.append(&2, U32, RG.keep(b, z), RG.without(r, x)), y) == True{} : Bool}:
  match b:
    case True{}:
      or_cases(U32.is_eq(z, y), RG.has(r, y), RG.has(RG.without(r, x), y), hy,
        q => Empty.absurd({RG.has(RG.without(r, x), y) == True{} : Bool},
          MB.true_ne_false()(Equal.trans(Bool, True{}, U32.is_eq(x, y), False{},
            ME.subst(U32, k => {True{} == U32.is_eq(k, y) : Bool}, z, x, MS.u32_eq_of_is_eq(z, x, e), Equal.sym(Bool, U32.is_eq(z, y), True{}, q)), hxy))),
        hh => ih(hh))
    case False{}:
      or_cases(U32.is_eq(z, y), RG.has(r, y), Bool.or(U32.is_eq(z, y), RG.has(RG.without(r, x), y)), hy,
        q => ME.subst(Bool, k => {Bool.or(k, RG.has(RG.without(r, x), y)) == True{} : Bool}, True{}, U32.is_eq(z, y), Equal.sym(Bool, U32.is_eq(z, y), True{}, q), {==}),
        hh => has_cons(z, RG.without(r, x), y, ih(hh)))

def has_without(ys: List<&2, U32>, +x: U32, +y: U32, +hxy: {U32.is_eq(x, y) == False{} : Bool}, h: {RG.has(ys, y) == True{} : Bool}) ->
    {RG.has(RG.without(ys, x), y) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({RG.has(Nil{}, y) == True{} : Bool}, MB.false_ne_true()(h))
    case Con{+z, +r}:
      hw_go(r, z, x, y, U32.is_eq(z, x), {==}, hxy, h, hh => has_without(r, x, y, hxy, hh))
# sublists: members of a list taken out stay members of it; what holds
# of every member, or of every member's word 3, holds of a sublist
def sub_has(B: List<&2, U32>, +C: List<&2, U32>, +a: U32, +hbc: {RG.sub(B, C) == True{} : Bool}, hb: {RG.has(B, a) == True{} : Bool}) -> {RG.has(C, a) == True{} : Bool}:
  match B:
    case Nil{}:
      Empty.absurd({RG.has(C, a) == True{} : Bool}, MB.false_ne_true()(hb))
    case Con{+y, +r}:
      or_cases(U32.is_eq(y, a), RG.has(r, a), RG.has(C, a), hb,
        q => ME.subst(U32, k => {RG.has(C, k) == True{} : Bool}, y, a, MS.u32_eq_of_is_eq(y, a, q), MB.eq_true_of_and_left(RG.has(C, y), RG.sub(r, C), hbc)),
        hh => sub_has(r, C, a, MB.eq_true_of_and_right(RG.has(C, y), RG.sub(r, C), hbc), hh))

def sub_trans(A: List<&2, U32>, +B: List<&2, U32>, +C: List<&2, U32>, +hab: {RG.sub(A, B) == True{} : Bool}, +hbc: {RG.sub(B, C) == True{} : Bool}) -> {RG.sub(A, C) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      MB.and_eq_true(RG.has(C, y), RG.sub(r, C), sub_has(B, C, y, hbc, MB.eq_true_of_and_left(RG.has(B, y), RG.sub(r, B), hab)), sub_trans(r, B, C, MB.eq_true_of_and_right(RG.has(B, y), RG.sub(r, B), hab), hbc))

def sw_go(+r: List<&2, U32>, +z: U32, +x: U32, +b: Bool, +ih: {RG.sub(RG.without(r, x), r) == True{} : Bool}) ->
    {RG.sub(List.append(&2, U32, RG.keep(b, z), RG.without(r, x)), Con{z, r}) == True{} : Bool}:
  match b:
    case True{}:
      sub_cons_r(RG.without(r, x), z, r, ih)
    case False{}:
      MB.and_eq_true(RG.has(Con{z, r}, z), RG.sub(RG.without(r, x), Con{z, r}), has_self(z, r), sub_cons_r(RG.without(r, x), z, r, ih))

def sub_without(ys: List<&2, U32>, +x: U32) -> {RG.sub(RG.without(ys, x), ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      sw_go(r, z, x, U32.is_eq(z, x), sub_without(r, x))

def links_sub(L: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +i: U32, +hs: {RG.sub(L, M) == True{} : Bool}, +h: {RG.off.links(M, d, i) == True{} : Bool}) -> {RG.off.links(L, d, i) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 3 : U32), d))), RG.off.links(r, d, i), links_at(M, d, i, m, h, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hs)), links_sub(r, M, d, i, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hs), h))

# the positions kept off as the links are
def pos_at(ys: List<&2, U32>, +d: Nat, +i: U32, +m: U32,
    +ho: {RG.off.pos(ys, d, i) == True{} : Bool}, hm: {RG.has(ys, m) == True{} : Bool}) ->
    {Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 2 : U32), d))) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 2 : U32), d))) == True{} : Bool}, MB.false_ne_true()(hm))
    case Con{+z, +t}:
      +hz = MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((z + 2 : U32), d))), RG.off.pos(t, d, i), ho)
      +ht = MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((z + 2 : U32), d))), RG.off.pos(t, d, i), ho)
      or_cases(U32.is_eq(z, m), RG.has(t, m), Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 2 : U32), d))), hm,
        e => ME.subst(U32, q => {Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((q + 2 : U32), d))) == True{} : Bool}, z, m, MS.u32_eq_of_is_eq(z, m, e), hz),
        hh => pos_at(t, d, i, m, ht, hh))

def pos_sub(L: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +i: U32, +hs: {RG.sub(L, M) == True{} : Bool}, +h: {RG.off.pos(M, d, i) == True{} : Bool}) -> {RG.off.pos(L, d, i) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 2 : U32), d))), RG.off.pos(r, d, i), pos_at(M, d, i, m, h, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hs)), pos_sub(r, M, d, i, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hs), h))

# a port faceable by a list, by any of its parts
def port_sub(+L: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +r: U32, +hs: {RG.sub(L, M) == True{} : Bool}, +h: {RG.port.ok(M, d, r) == True{} : Bool}) -> {RG.port.ok(L, d, r) == True{} : Bool}:
  MB.and_eq_true(RG.off.links(L, d, (r + 1 : U32)), RG.off.pos(L, d, (r + 1 : U32)), links_sub(L, M, d, (r + 1 : U32), hs, MB.eq_true_of_and_left(RG.off.links(M, d, (r + 1 : U32)), RG.off.pos(M, d, (r + 1 : U32)), h)), pos_sub(L, M, d, (r + 1 : U32), hs, MB.eq_true_of_and_right(RG.off.links(M, d, (r + 1 : U32)), RG.off.pos(M, d, (r + 1 : U32)), h)))

def bases_at(K: List<&2, U32>, +m: U32, +h: {RG.bases(K) == True{} : Bool}, hm: {RG.has(K, m) == True{} : Bool}) -> {U32.is_eq(P.base(m), m) == True{} : Bool}:
  match K:
    case Nil{}:
      Empty.absurd({U32.is_eq(P.base(m), m) == True{} : Bool}, MB.false_ne_true()(hm))
    case Con{+k, +r}:
      or_cases(U32.is_eq(k, m), RG.has(r, m), U32.is_eq(P.base(m), m), hm,
        q => ME.subst(U32, z => {U32.is_eq(P.base(z), z) == True{} : Bool}, k, m, MS.u32_eq_of_is_eq(k, m, q), MB.eq_true_of_and_left(U32.is_eq(P.base(k), k), RG.bases(r), h)),
        hh => bases_at(r, m, MB.eq_true_of_and_right(U32.is_eq(P.base(k), k), RG.bases(r), h), hh))

def bases_sub(L: List<&2, U32>, +M: List<&2, U32>, +hs: {RG.sub(L, M) == True{} : Bool}, +h: {RG.bases(M) == True{} : Bool}) -> {RG.bases(L) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(U32.is_eq(P.base(m), m), RG.bases(r), bases_at(M, m, h, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hs)), bases_sub(r, M, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hs), h))

# a member's split of an exact ring: it, and x in neither part
def ring_split(-v: List<&2, U32>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32,
    +hr: {RG.ring(v, d, s, cs) == True{} : Bool}, +hx: {RG.has(cs, x) == True{} : Bool}) -> {RG.ring(v, d, s, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)})) == True{} : Bool}:
  ME.subst(List<&2, U32>, q => {RG.ring(v, d, s, q) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), cs, split_of_has(cs, x, hx)), hr)

def ring_parts_notin(+d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32,
    +hap: {RG.apart.all(Con{s, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)})}, d) == True{} : Bool}) -> {Bool.and(Bool.not(RG.has(lpre(cs, x), x)), Bool.not(RG.has(lpost(cs, x), x))) == True{} : Bool}:
  +ab = ap_before(Con{s, lpre(cs, x)}, lpost(cs, x), d, x, hap)
  MB.and_eq_true(Bool.not(RG.has(lpre(cs, x), x)), Bool.not(RG.has(lpost(cs, x), x)), not_t(RG.has(lpre(cs, x), x), apart_notin(lpre(cs, x), d, x, MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((s + 3 : U32), d))), RG.apart(lpre(cs, x), d, x), MB.eq_true_of_and_left(RG.apart(Con{s, lpre(cs, x)}, d, x), RG.apart(lpost(cs, x), d, x), ab)))), not_t(RG.has(lpost(cs, x), x), apart_notin(lpost(cs, x), d, x, MB.eq_true_of_and_right(RG.apart(Con{s, lpre(cs, x)}, d, x), RG.apart(lpost(cs, x), d, x), ab))))

def notin_l(+A: List<&2, U32>, +B: List<&2, U32>, +x: U32, +h: {Bool.and(Bool.not(RG.has(A, x)), Bool.not(RG.has(B, x))) == True{} : Bool}) -> {RG.has(A, x) == False{} : Bool}:
  MB.eq_false_of_not_eq_true(RG.has(A, x), MB.eq_true_of_and_left(Bool.not(RG.has(A, x)), Bool.not(RG.has(B, x)), h))

def notin_r(+A: List<&2, U32>, +B: List<&2, U32>, +x: U32, +h: {Bool.and(Bool.not(RG.has(A, x)), Bool.not(RG.has(B, x))) == True{} : Bool}) -> {RG.has(B, x) == False{} : Bool}:
  MB.eq_false_of_not_eq_true(RG.has(B, x), MB.eq_true_of_and_right(Bool.not(RG.has(A, x)), Bool.not(RG.has(B, x)), h))

# without x is the two parts of x's split
def without_eq(+d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32,
    +hap: {RG.apart.all(Con{s, cs}, d) == True{} : Bool}, +hx: {RG.has(cs, x) == True{} : Bool}) -> {RG.without(cs, x) == List.append(&2, U32, lpre(cs, x), lpost(cs, x)) : List<&2, U32>}:
  +nn = ring_parts_notin(d, s, cs, x, ME.subst(List<&2, U32>, q => {RG.apart.all(Con{s, q}, d) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), cs, split_of_has(cs, x, hx)), hap))
  ME.subst(List<&2, U32>, q => {RG.without(q, x) == List.append(&2, U32, lpre(cs, x), lpost(cs, x)) : List<&2, U32>}, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), cs, split_of_has(cs, x, hx),
    without_split(lpre(cs, x), x, lpost(cs, x), notin_l(lpre(cs, x), lpost(cs, x), x, nn), notin_r(lpre(cs, x), lpost(cs, x), x, nn)))

def pred_exact.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hr: {RG.ring(AD.view(U32, w), d, s, cs) == True{} : Bool}, +hx: {RG.has(cs, x) == True{} : Bool},
  m: LAT.Mirror(U32, w)) ->
  {Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{w}, a}, x)) == RG.before(cs, s, x) : U32}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hn = len_ok(t, d, s, cs, hft, hd32, MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hrt))
  %e : {Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{_}, a}, x)) == RG.before(cs, s, x) : U32}
  Equal.trans(U32, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x)), RG.last(lpre(cs, x), s), RG.before(cs, s, x),
    pred_exact.go(LAT.fromT(U32, t), a, d, s, lpre(cs, x), x, lpost(cs, x), hft, hd32, ring_split(AD.view(U32, LAT.fromT(U32, t)), d, s, cs, x, hrt, hx),
      ME.subst(List<&2, U32>, q => {Nat.is_lt(List.length(&2, U32, q), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), cs, split_of_has(cs, x, hx)), hn), LAT.mirror(U32, LAT.fromT(U32, t))),
    Equal.sym(U32, RG.before(cs, s, x), RG.last(lpre(cs, x), s), before_last(cs, s, x)))

def Laws.pred_exact(w, a, d, s, t, x, hf, hd32, hr, hx):
  pred_exact.m(w, a, d, s, t, x, hf, hd32, hr, hx, LAT.mirror(U32, w))

def unlink_exact.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hr: {RG.ring(AD.view(U32, w), d, s, cs) == True{} : Bool}, +hx: {RG.has(cs, x) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.ring(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{w}, a}, x))), d, s, RG.without(cs, x)) == True{} : Bool}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hn = len_ok(t, d, s, cs, hft, hd32, MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hrt))
  %e : {RG.ring(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{_}, a}, x))), d, s, RG.without(cs, x)) == True{} : Bool}
  ME.subst(List<&2, U32>, q => {RG.ring(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{LAT.fromT(U32, t)}, a}, x))), d, s, q) == True{} : Bool}, List.append(&2, U32, lpre(cs, x), lpost(cs, x)), RG.without(cs, x),
    Equal.sym(List<&2, U32>, RG.without(cs, x), List.append(&2, U32, lpre(cs, x), lpost(cs, x)), without_eq(d, s, cs, x, MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hrt), hx)),
    unlink_exact.go(LAT.fromT(U32, t), a, d, s, lpre(cs, x), x, lpost(cs, x), hft, hd32, ring_split(AD.view(U32, LAT.fromT(U32, t)), d, s, cs, x, hrt, hx),
      ME.subst(List<&2, U32>, q => {Nat.is_lt(List.length(&2, U32, q), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), cs, split_of_has(cs, x, hx)), hn), LAT.mirror(U32, LAT.fromT(U32, t)), ma))

def Laws.unlink_exact(w, a, d, s, t, x, hf, hd32, hr, hx):
  unlink_exact.m(w, a, d, s, t, x, hf, hd32, hr, hx, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# The ring's layout

# two nodes apart, either way round
def disj4_sym(+d: Nat, +a: U32, +b: U32, +h: {RG.disj4(d, a, b) == True{} : Bool}) -> {RG.disj4(d, b, a) == True{} : Bool}:
  MB.and_eq_true(RG.off(RG.nw(a), d, b), (RG.off(RG.nw(a), d, (b + 1 : U32)) && (RG.off(RG.nw(a), d, (b + 2 : U32)) && RG.off(RG.nw(a), d, (b + 3 : U32)))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(a, d), AD.slot(b, d))), RG.off(Con{(a + 1 : U32), Con{(a + 2 : U32), Con{(a + 3 : U32), Nil{}}}}, d, b), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot(b, d), AD.slot(a, d)), Nat.is_eq(AD.slot(a, d), AD.slot(b, d)), MN.is_eq_comm(AD.slot(b, d), AD.slot(a, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot(a, d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, a), MB.eq_true_of_and_left(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot(b, d))), RG.off(Con{(a + 2 : U32), Con{(a + 3 : U32), Nil{}}}, d, b), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot(b, d), AD.slot((a + 1 : U32), d)), Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot(b, d)), MN.is_eq_comm(AD.slot(b, d), AD.slot((a + 1 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 1 : U32), d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, (a + 1 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(b), d, (a + 1 : U32)), (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h)))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot(b, d))), RG.off(Con{(a + 3 : U32), Nil{}}, d, b), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot(b, d), AD.slot((a + 2 : U32), d)), Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot(b, d)), MN.is_eq_comm(AD.slot(b, d), AD.slot((a + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 2 : U32), d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, (a + 2 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(b), d, (a + 2 : U32)), RG.off(RG.nw(b), d, (a + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, (a + 1 : U32)), (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h))))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot(b, d))), RG.off(Nil{}, d, b), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot(b, d), AD.slot((a + 3 : U32), d)), Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot(b, d)), MN.is_eq_comm(AD.slot(b, d), AD.slot((a + 3 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 3 : U32), d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, (a + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, (a + 2 : U32)), RG.off(RG.nw(b), d, (a + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, (a + 1 : U32)), (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h))))), {==})))), MB.and_eq_true(RG.off(RG.nw(a), d, (b + 1 : U32)), (RG.off(RG.nw(a), d, (b + 2 : U32)) && RG.off(RG.nw(a), d, (b + 3 : U32))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(a, d), AD.slot((b + 1 : U32), d))), RG.off(Con{(a + 1 : U32), Con{(a + 2 : U32), Con{(a + 3 : U32), Nil{}}}}, d, (b + 1 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(a, d)), Nat.is_eq(AD.slot(a, d), AD.slot((b + 1 : U32), d)), MN.is_eq_comm(AD.slot((b + 1 : U32), d), AD.slot(a, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(a, d))), RG.off(Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}, d, a), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot(a, d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, a), MB.eq_true_of_and_left(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h)))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 1 : U32), d))), RG.off(Con{(a + 2 : U32), Con{(a + 3 : U32), Nil{}}}, d, (b + 1 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d)), Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 1 : U32), d)), MN.is_eq_comm(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d))), RG.off(Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}, d, (a + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 1 : U32), d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, (a + 1 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(b), d, (a + 1 : U32)), (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h))))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 1 : U32), d))), RG.off(Con{(a + 3 : U32), Nil{}}, d, (b + 1 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 2 : U32), d)), Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 1 : U32), d)), MN.is_eq_comm(AD.slot((b + 1 : U32), d), AD.slot((a + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 2 : U32), d))), RG.off(Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}, d, (a + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 2 : U32), d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, (a + 2 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(b), d, (a + 2 : U32)), RG.off(RG.nw(b), d, (a + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, (a + 1 : U32)), (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h)))))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 1 : U32), d))), RG.off(Nil{}, d, (b + 1 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 3 : U32), d)), Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 1 : U32), d)), MN.is_eq_comm(AD.slot((b + 1 : U32), d), AD.slot((a + 3 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 3 : U32), d))), RG.off(Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}, d, (a + 3 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 3 : U32), d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, (a + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, (a + 2 : U32)), RG.off(RG.nw(b), d, (a + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, (a + 1 : U32)), (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h)))))), {==})))), MB.and_eq_true(RG.off(RG.nw(a), d, (b + 2 : U32)), RG.off(RG.nw(a), d, (b + 3 : U32)), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(a, d), AD.slot((b + 2 : U32), d))), RG.off(Con{(a + 1 : U32), Con{(a + 2 : U32), Con{(a + 3 : U32), Nil{}}}}, d, (b + 2 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(a, d)), Nat.is_eq(AD.slot(a, d), AD.slot((b + 2 : U32), d)), MN.is_eq_comm(AD.slot((b + 2 : U32), d), AD.slot(a, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(a, d))), RG.off(Con{(b + 3 : U32), Nil{}}, d, a), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(a, d))), RG.off(Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}, d, a), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot(a, d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, a), MB.eq_true_of_and_left(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h))))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 2 : U32), d))), RG.off(Con{(a + 2 : U32), Con{(a + 3 : U32), Nil{}}}, d, (b + 2 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d)), Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 2 : U32), d)), MN.is_eq_comm(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d))), RG.off(Con{(b + 3 : U32), Nil{}}, d, (a + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d))), RG.off(Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}, d, (a + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 1 : U32), d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, (a + 1 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(b), d, (a + 1 : U32)), (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h)))))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 2 : U32), d))), RG.off(Con{(a + 3 : U32), Nil{}}, d, (b + 2 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d)), Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 2 : U32), d)), MN.is_eq_comm(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d))), RG.off(Con{(b + 3 : U32), Nil{}}, d, (a + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 2 : U32), d))), RG.off(Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}, d, (a + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 2 : U32), d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, (a + 2 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(b), d, (a + 2 : U32)), RG.off(RG.nw(b), d, (a + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, (a + 1 : U32)), (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h))))))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 2 : U32), d))), RG.off(Nil{}, d, (b + 2 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d)), Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 2 : U32), d)), MN.is_eq_comm(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d))), RG.off(Con{(b + 3 : U32), Nil{}}, d, (a + 3 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 3 : U32), d))), RG.off(Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}, d, (a + 3 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 3 : U32), d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, (a + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, (a + 2 : U32)), RG.off(RG.nw(b), d, (a + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, (a + 1 : U32)), (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h))))))), {==})))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(a, d), AD.slot((b + 3 : U32), d))), RG.off(Con{(a + 1 : U32), Con{(a + 2 : U32), Con{(a + 3 : U32), Nil{}}}}, d, (b + 3 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(a, d)), Nat.is_eq(AD.slot(a, d), AD.slot((b + 3 : U32), d)), MN.is_eq_comm(AD.slot((b + 3 : U32), d), AD.slot(a, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(a, d))), RG.off(Nil{}, d, a), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(a, d))), RG.off(Con{(b + 3 : U32), Nil{}}, d, a), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(a, d))), RG.off(Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}, d, a), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot(a, d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, a), MB.eq_true_of_and_left(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h)))))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 3 : U32), d))), RG.off(Con{(a + 2 : U32), Con{(a + 3 : U32), Nil{}}}, d, (b + 3 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d)), Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 3 : U32), d)), MN.is_eq_comm(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d))), RG.off(Nil{}, d, (a + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d))), RG.off(Con{(b + 3 : U32), Nil{}}, d, (a + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d))), RG.off(Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}, d, (a + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 1 : U32), d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, (a + 1 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(b), d, (a + 1 : U32)), (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h))))))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 3 : U32), d))), RG.off(Con{(a + 3 : U32), Nil{}}, d, (b + 3 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d)), Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 3 : U32), d)), MN.is_eq_comm(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d))), RG.off(Nil{}, d, (a + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d))), RG.off(Con{(b + 3 : U32), Nil{}}, d, (a + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 2 : U32), d))), RG.off(Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}, d, (a + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 2 : U32), d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, (a + 2 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(b), d, (a + 2 : U32)), RG.off(RG.nw(b), d, (a + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, (a + 1 : U32)), (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h)))))))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 3 : U32), d))), RG.off(Nil{}, d, (b + 3 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d)), Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 3 : U32), d)), MN.is_eq_comm(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d))), RG.off(Nil{}, d, (a + 3 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d))), RG.off(Con{(b + 3 : U32), Nil{}}, d, (a + 3 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 3 : U32), d))), RG.off(Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}, d, (a + 3 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 3 : U32), d))), RG.off(Con{(b + 1 : U32), Con{(b + 2 : U32), Con{(b + 3 : U32), Nil{}}}}, d, (a + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, (a + 2 : U32)), RG.off(RG.nw(b), d, (a + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, (a + 1 : U32)), (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(b), d, a), (RG.off(RG.nw(b), d, (a + 1 : U32)) && (RG.off(RG.nw(b), d, (a + 2 : U32)) && RG.off(RG.nw(b), d, (a + 3 : U32)))), h)))))))), {==})))))))

def cross_at(ys: List<&2, U32>, +d: Nat, +a: U32, +b: U32, +h: {RG.cross(ys, d, a) == True{} : Bool}, hb: {RG.has(ys, b) == True{} : Bool}) -> {RG.disj4(d, a, b) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({RG.disj4(d, a, b) == True{} : Bool}, MB.false_ne_true()(hb))
    case Con{+c, +r}:
      or_cases(U32.is_eq(c, b), RG.has(r, b), RG.disj4(d, a, b), hb,
        q => ME.subst(U32, k => {RG.disj4(d, a, k) == True{} : Bool}, c, b, MS.u32_eq_of_is_eq(c, b, q), MB.eq_true_of_and_left(RG.disj4(d, a, c), RG.cross(r, d, a), h)),
        hh => cross_at(r, d, a, b, MB.eq_true_of_and_right(RG.disj4(d, a, c), RG.cross(r, d, a), h), hh))

def cross_sub(L: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +a: U32, +hs: {RG.sub(L, M) == True{} : Bool}, +h: {RG.cross(M, d, a) == True{} : Bool}) -> {RG.cross(L, d, a) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+b, +r}:
      MB.and_eq_true(RG.disj4(d, a, b), RG.cross(r, d, a), cross_at(M, d, a, b, h, MB.eq_true_of_and_left(RG.has(M, b), RG.sub(r, M), hs)), cross_sub(r, M, d, a, MB.eq_true_of_and_right(RG.has(M, b), RG.sub(r, M), hs), h))

# taking a member out keeps the layout
def lw_go(+t: List<&2, U32>, +a: U32, +d: Nat, +x: U32, +b: Bool, +hl: {RG.layout(Con{a, t}, d) == True{} : Bool}, +ih: {RG.layout(RG.without(t, x), d) == True{} : Bool}) ->
    {RG.layout(List.append(&2, U32, RG.keep(b, a), RG.without(t, x)), d) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      MB.and_eq_true(RG.apartw(RG.nw(a), d), Bool.and(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(RG.without(t, x), d, a), RG.layout(RG.without(t, x), d))), MB.eq_true_of_and_left(RG.apartw(RG.nw(a), d), Bool.and(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(t, d, a), RG.layout(t, d))), hl), MB.and_eq_true(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(RG.without(t, x), d, a), RG.layout(RG.without(t, x), d)), MB.eq_true_of_and_left(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(t, d, a), RG.layout(t, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(a), d), Bool.and(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(t, d, a), RG.layout(t, d))), hl)), MB.and_eq_true(RG.cross(RG.without(t, x), d, a), RG.layout(RG.without(t, x), d), cross_sub(RG.without(t, x), t, d, a, sub_without(t, x), MB.eq_true_of_and_left(RG.cross(t, d, a), RG.layout(t, d), MB.eq_true_of_and_right(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(t, d, a), RG.layout(t, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(a), d), Bool.and(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(t, d, a), RG.layout(t, d))), hl)))), ih)))

def lay_without(ys: List<&2, U32>, +d: Nat, +x: U32, +h: {RG.layout(ys, d) == True{} : Bool}) -> {RG.layout(RG.without(ys, x), d) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      lw_go(t, a, d, x, U32.is_eq(a, x), h, lay_without(t, d, x, MB.eq_true_of_and_right(RG.cross(t, d, a), RG.layout(t, d), MB.eq_true_of_and_right(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(t, d, a), RG.layout(t, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(a), d), Bool.and(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(t, d, a), RG.layout(t, d))), h)))))

# two distinct members of a layout are apart: the first listed apart from
# every later one, either way round
def lp_step(+c: U32, +r: List<&2, U32>, +d: Nat, +a: U32, +b: U32, +ba: Bool, +ea: {U32.is_eq(c, a) == ba : Bool},
    +bb: Bool, +eb: {U32.is_eq(c, b) == bb : Bool}, +h: {RG.layout(Con{c, r}, d) == True{} : Bool},
    +ha: {Bool.or(ba, RG.has(r, a)) == True{} : Bool}, +hb: {Bool.or(bb, RG.has(r, b)) == True{} : Bool}, +hne: {U32.is_eq(a, b) == False{} : Bool},
    ih: {RG.has(r, a) == True{} : Bool} -> {RG.has(r, b) == True{} : Bool} -> {RG.disj4(d, a, b) == True{} : Bool}) -> {RG.disj4(d, a, b) == True{} : Bool}:
  match ba:
    case True{}:
      match bb:
        case True{}:
          Empty.absurd({RG.disj4(d, a, b) == True{} : Bool}, MB.true_ne_false()(Equal.trans(Bool, True{}, U32.is_eq(a, b), False{},
            ME.subst(U32, k => {True{} == U32.is_eq(k, b) : Bool}, c, a, MS.u32_eq_of_is_eq(c, a, ea), Equal.sym(Bool, U32.is_eq(c, b), True{}, eb)), hne)))
        case False{}:
          ME.subst(U32, k => {RG.disj4(d, k, b) == True{} : Bool}, c, a, MS.u32_eq_of_is_eq(c, a, ea), cross_at(r, d, c, b, MB.eq_true_of_and_left(RG.cross(r, d, c), RG.layout(r, d), MB.eq_true_of_and_right(RG.off(RG.nw(c), d, P.at_fh()), Bool.and(RG.cross(r, d, c), RG.layout(r, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(c), d), Bool.and(RG.off(RG.nw(c), d, P.at_fh()), Bool.and(RG.cross(r, d, c), RG.layout(r, d))), h))), hb))
    case False{}:
      match bb:
        case True{}:
          ME.subst(U32, k => {RG.disj4(d, a, k) == True{} : Bool}, c, b, MS.u32_eq_of_is_eq(c, b, eb), disj4_sym(d, c, a, cross_at(r, d, c, a, MB.eq_true_of_and_left(RG.cross(r, d, c), RG.layout(r, d), MB.eq_true_of_and_right(RG.off(RG.nw(c), d, P.at_fh()), Bool.and(RG.cross(r, d, c), RG.layout(r, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(c), d), Bool.and(RG.off(RG.nw(c), d, P.at_fh()), Bool.and(RG.cross(r, d, c), RG.layout(r, d))), h))), ha)))
        case False{}:
          ih(ha)(hb)

def lay_pair(M: List<&2, U32>, +d: Nat, +a: U32, +b: U32, +h: {RG.layout(M, d) == True{} : Bool}, +ha: {RG.has(M, a) == True{} : Bool}, +hb: {RG.has(M, b) == True{} : Bool},
    +hne: {U32.is_eq(a, b) == False{} : Bool}) -> {RG.disj4(d, a, b) == True{} : Bool}:
  match M:
    case Nil{}:
      Empty.absurd({RG.disj4(d, a, b) == True{} : Bool}, MB.false_ne_true()(ha))
    case Con{+c, +r}:
      lp_step(c, r, d, a, b, U32.is_eq(c, a), {==}, U32.is_eq(c, b), {==}, h, ha, hb, hne,
        pa => pb => lay_pair(r, d, a, b, MB.eq_true_of_and_right(RG.cross(r, d, c), RG.layout(r, d), MB.eq_true_of_and_right(RG.off(RG.nw(c), d, P.at_fh()), Bool.and(RG.cross(r, d, c), RG.layout(r, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(c), d), Bool.and(RG.off(RG.nw(c), d, P.at_fh()), Bool.and(RG.cross(r, d, c), RG.layout(r, d))), h))), pa, pb, hne))

# a member's own words apart
def lay_self(M: List<&2, U32>, +d: Nat, +m: U32, +h: {RG.layout(M, d) == True{} : Bool}, hm: {RG.has(M, m) == True{} : Bool}) -> {RG.apartw(RG.nw(m), d) == True{} : Bool}:
  match M:
    case Nil{}:
      Empty.absurd({RG.apartw(RG.nw(m), d) == True{} : Bool}, MB.false_ne_true()(hm))
    case Con{+c, +r}:
      or_cases(U32.is_eq(c, m), RG.has(r, m), RG.apartw(RG.nw(m), d), hm,
        q => ME.subst(U32, k => {RG.apartw(RG.nw(k), d) == True{} : Bool}, c, m, MS.u32_eq_of_is_eq(c, m, q), MB.eq_true_of_and_left(RG.apartw(RG.nw(c), d), Bool.and(RG.off(RG.nw(c), d, P.at_fh()), Bool.and(RG.cross(r, d, c), RG.layout(r, d))), h)),
        hh => lay_self(r, d, m, MB.eq_true_of_and_right(RG.cross(r, d, c), RG.layout(r, d), MB.eq_true_of_and_right(RG.off(RG.nw(c), d, P.at_fh()), Bool.and(RG.cross(r, d, c), RG.layout(r, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(c), d), Bool.and(RG.off(RG.nw(c), d, P.at_fh()), Bool.and(RG.cross(r, d, c), RG.layout(r, d))), h))), hh))

# no member's word 3 on the head's word
def head_links(M: List<&2, U32>, +d: Nat, +h: {RG.layout(M, d) == True{} : Bool}) -> {RG.off.links(M, d, P.at_fh()) == True{} : Bool}:
  match M:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((a + 3 : U32), d))), RG.off.links(t, d, P.at_fh()), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot(P.at_fh(), d)), Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((a + 3 : U32), d)), MN.is_eq_comm(AD.slot((a + 3 : U32), d), AD.slot(P.at_fh(), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot(P.at_fh(), d))), RG.off(Nil{}, d, P.at_fh()), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot(P.at_fh(), d))), RG.off(Con{(a + 3 : U32), Nil{}}, d, P.at_fh()), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot(P.at_fh(), d))), RG.off(Con{(a + 2 : U32), Con{(a + 3 : U32), Nil{}}}, d, P.at_fh()), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(a, d), AD.slot(P.at_fh(), d))), RG.off(Con{(a + 1 : U32), Con{(a + 2 : U32), Con{(a + 3 : U32), Nil{}}}}, d, P.at_fh()), MB.eq_true_of_and_left(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(t, d, a), RG.layout(t, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(a), d), Bool.and(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(t, d, a), RG.layout(t, d))), h))))))), head_links(t, d, MB.eq_true_of_and_right(RG.cross(t, d, a), RG.layout(t, d), MB.eq_true_of_and_right(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(t, d, a), RG.layout(t, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(a), d), Bool.and(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(t, d, a), RG.layout(t, d))), h)))))

def lol_step0(+m: U32, +p: U32, +d: Nat, +M: List<&2, U32>, +b: Bool, e: {U32.is_eq(m, p) == b : Bool},
    +h: {RG.layout(M, d) == True{} : Bool}, +hm: {RG.has(M, m) == True{} : Bool}, +hp: {RG.has(M, p) == True{} : Bool}) -> {Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot((p + 3 : U32), d))) == True{} : Bool}:
  match b:
    case True{}:
      ME.subst(U32, q => {Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot((q + 3 : U32), d))) == True{} : Bool}, m, p, MS.u32_eq_of_is_eq(m, p, e), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(m, d)), Nat.is_eq(AD.slot(m, d), AD.slot((m + 3 : U32), d)), MN.is_eq_comm(AD.slot((m + 3 : U32), d), AD.slot(m, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(m, d))), RG.off(Nil{}, d, m), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(m, d))), RG.off(Con{(m + 3 : U32), Nil{}}, d, m), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(m, d))), RG.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, m), MB.eq_true_of_and_left(RG.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, m), RG.apartw(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d), lay_self(M, d, m, h, hm)))))))
    case False{}:
      ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((p + 3 : U32), d), AD.slot(m, d)), Nat.is_eq(AD.slot(m, d), AD.slot((p + 3 : U32), d)), MN.is_eq_comm(AD.slot((p + 3 : U32), d), AD.slot(m, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((p + 3 : U32), d), AD.slot(m, d))), RG.off(Nil{}, d, m), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((p + 2 : U32), d), AD.slot(m, d))), RG.off(Con{(p + 3 : U32), Nil{}}, d, m), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((p + 1 : U32), d), AD.slot(m, d))), RG.off(Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}, d, m), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(p, d), AD.slot(m, d))), RG.off(Con{(p + 1 : U32), Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}}, d, m), MB.eq_true_of_and_left(RG.off(RG.nw(p), d, m), (RG.off(RG.nw(p), d, (m + 1 : U32)) && (RG.off(RG.nw(p), d, (m + 2 : U32)) && RG.off(RG.nw(p), d, (m + 3 : U32)))), lay_pair(M, d, m, p, h, hm, hp, e)))))))

def lol_build0(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +m: U32, +hk: {RG.sub(K, M) == True{} : Bool}, +h: {RG.layout(M, d) == True{} : Bool}, +hm: {RG.has(M, m) == True{} : Bool}) ->
    {RG.off.links(K, d, m) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+q, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot((q + 3 : U32), d))), RG.off.links(r, d, m), lol_step0(m, q, d, M, U32.is_eq(m, q), {==}, h, hm, MB.eq_true_of_and_left(RG.has(M, q), RG.sub(r, M), hk)), lol_build0(r, M, d, m, MB.eq_true_of_and_right(RG.has(M, q), RG.sub(r, M), hk), h, hm))

def lol_step1(+m: U32, +p: U32, +d: Nat, +M: List<&2, U32>, +b: Bool, e: {U32.is_eq(m, p) == b : Bool},
    +h: {RG.layout(M, d) == True{} : Bool}, +hm: {RG.has(M, m) == True{} : Bool}, +hp: {RG.has(M, p) == True{} : Bool}) -> {Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot((p + 3 : U32), d))) == True{} : Bool}:
  match b:
    case True{}:
      ME.subst(U32, q => {Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot((q + 3 : U32), d))) == True{} : Bool}, m, p, MS.u32_eq_of_is_eq(m, p, e), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot((m + 1 : U32), d)), Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot((m + 3 : U32), d)), MN.is_eq_comm(AD.slot((m + 3 : U32), d), AD.slot((m + 1 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot((m + 1 : U32), d))), RG.off(Nil{}, d, (m + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot((m + 1 : U32), d))), RG.off(Con{(m + 3 : U32), Nil{}}, d, (m + 1 : U32)), MB.eq_true_of_and_left(RG.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, (m + 1 : U32)), RG.apartw(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d), MB.eq_true_of_and_right(RG.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, m), RG.apartw(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d), lay_self(M, d, m, h, hm)))))))
    case False{}:
      ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((p + 3 : U32), d), AD.slot((m + 1 : U32), d)), Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot((p + 3 : U32), d)), MN.is_eq_comm(AD.slot((p + 3 : U32), d), AD.slot((m + 1 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((p + 3 : U32), d), AD.slot((m + 1 : U32), d))), RG.off(Nil{}, d, (m + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((p + 2 : U32), d), AD.slot((m + 1 : U32), d))), RG.off(Con{(p + 3 : U32), Nil{}}, d, (m + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((p + 1 : U32), d), AD.slot((m + 1 : U32), d))), RG.off(Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}, d, (m + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(p, d), AD.slot((m + 1 : U32), d))), RG.off(Con{(p + 1 : U32), Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}}, d, (m + 1 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(p), d, (m + 1 : U32)), (RG.off(RG.nw(p), d, (m + 2 : U32)) && RG.off(RG.nw(p), d, (m + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(p), d, m), (RG.off(RG.nw(p), d, (m + 1 : U32)) && (RG.off(RG.nw(p), d, (m + 2 : U32)) && RG.off(RG.nw(p), d, (m + 3 : U32)))), lay_pair(M, d, m, p, h, hm, hp, e))))))))

def lol_build1(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +m: U32, +hk: {RG.sub(K, M) == True{} : Bool}, +h: {RG.layout(M, d) == True{} : Bool}, +hm: {RG.has(M, m) == True{} : Bool}) ->
    {RG.off.links(K, d, (m + 1 : U32)) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+q, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot((q + 3 : U32), d))), RG.off.links(r, d, (m + 1 : U32)), lol_step1(m, q, d, M, U32.is_eq(m, q), {==}, h, hm, MB.eq_true_of_and_left(RG.has(M, q), RG.sub(r, M), hk)), lol_build1(r, M, d, m, MB.eq_true_of_and_right(RG.has(M, q), RG.sub(r, M), hk), h, hm))

# What the ring's members face

# word i's slot no member's word 1
def ones(ys: List<&2, U32>, +d: Nat, +i: U32) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+m, t}:
      Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d))) && ones(t, d, i)

def fm_sub(mm: Maybe<&2, U32>, +d: Nat, +M: List<&2, U32>, +N: List<&2, U32>, +hs: {RG.sub(N, M) == True{} : Bool}, +h: {RG.faces.m(mm, d, M) == True{} : Bool}) -> {RG.faces.m(mm, d, N) == True{} : Bool}:
  match mm:
    case Some{+r}:
      MB.and_eq_true(RG.off.links(N, d, (r + 1 : U32)), RG.off.pos(N, d, (r + 1 : U32)), links_sub(N, M, d, (r + 1 : U32), hs, MB.eq_true_of_and_left(RG.off.links(M, d, (r + 1 : U32)), RG.off.pos(M, d, (r + 1 : U32)), h)), pos_sub(N, M, d, (r + 1 : U32), hs, MB.eq_true_of_and_right(RG.off.links(M, d, (r + 1 : U32)), RG.off.pos(M, d, (r + 1 : U32)), h)))
    case None{}:
      Empty.absurd({RG.faces.m(None{}, d, N) == True{} : Bool}, MB.false_ne_true()(h))

def fm_map(mm: Maybe<&2, U32>, +n: U32, +d: Nat, +N: List<&2, U32>, h: {RG.faces.m(mm, d, N) == True{} : Bool}, +hn: {RG.port.ok(N, d, n) == True{} : Bool}) ->
    {RG.faces.m(Maybe.map(&2, U32, U32, z => n, mm), d, N) == True{} : Bool}:
  match mm:
    case Some{+r}:
      hn
    case None{}:
      Empty.absurd({RG.faces.m(None{}, d, N) == True{} : Bool}, MB.false_ne_true()(h))

# a member's face kept by a write elsewhere, or by a write of a port
# whose link word is off the links
def fm_keep(+v: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +i: U32, +n: U32, +m: U32, h: {RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, N) == True{} : Bool},
    +hs: {Nat.is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d)) == False{} : Bool}) -> {RG.faces.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((m + 1 : U32), d)), d, N) == True{} : Bool}:
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((m + 1 : U32), d)), List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), LAB.get_set_ne(U32, v, AD.slot(i, d), AD.slot((m + 1 : U32), d), n, hs)) :
    {RG.faces.m(_, d, N) == True{} : Bool}
  h

def fm_write(+v: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +i: U32, +n: U32, +m: U32, +b: Bool, e: {Nat.is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d)) == b : Bool},
    +h: {RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, N) == True{} : Bool}, +hn: {RG.port.ok(N, d, n) == True{} : Bool}) -> {RG.faces.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((m + 1 : U32), d)), d, N) == True{} : Bool}:
  match b:
    case True{}:
      +eq = MN.eq_of_is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d), e)
      +h2 = ME.subst(Nat, q => {RG.faces.m(List.get(&2, U32, v, q), d, N) == True{} : Bool}, AD.slot((m + 1 : U32), d), AD.slot(i, d), Equal.sym(Nat, AD.slot(i, d), AD.slot((m + 1 : U32), d), eq), h)
      %eq : {RG.faces.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), _), d, N) == True{} : Bool}
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot(i, d)), Maybe.map(&2, U32, U32, z => n, List.get(&2, U32, v, AD.slot(i, d))), ML.get_set_self(&2, U32, v, AD.slot(i, d), n)) :
        {RG.faces.m(_, d, N) == True{} : Bool}
      fm_map(List.get(&2, U32, v, AD.slot(i, d)), n, d, N, h2, hn)
    case False{}:
      fm_keep(v, d, N, i, n, m, h, e)

def faces_keep(K: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +i: U32, +n: U32,
    +h: {RG.faces(K, v, d, N) == True{} : Bool}, +ho: {ones(K, d, i) == True{} : Bool}) -> {RG.faces(K, List.set(&2, U32, v, AD.slot(i, d), n), d, N) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(RG.faces.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((m + 1 : U32), d)), d, N), RG.faces(r, List.set(&2, U32, v, AD.slot(i, d), n), d, N), fm_keep(v, d, N, i, n, m, MB.eq_true_of_and_left(RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, N), RG.faces(r, v, d, N), h), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d))), ones(r, d, i), ho))), faces_keep(r, v, d, N, i, n, MB.eq_true_of_and_right(RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, N), RG.faces(r, v, d, N), h), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d))), ones(r, d, i), ho)))

def faces_write(K: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +i: U32, +n: U32,
    +h: {RG.faces(K, v, d, N) == True{} : Bool}, +hn: {RG.port.ok(N, d, n) == True{} : Bool}) -> {RG.faces(K, List.set(&2, U32, v, AD.slot(i, d), n), d, N) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(RG.faces.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((m + 1 : U32), d)), d, N), RG.faces(r, List.set(&2, U32, v, AD.slot(i, d), n), d, N), fm_write(v, d, N, i, n, m, Nat.is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d)), {==}, MB.eq_true_of_and_left(RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, N), RG.faces(r, v, d, N), h), hn), faces_write(r, v, d, N, i, n, MB.eq_true_of_and_right(RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, N), RG.faces(r, v, d, N), h), hn))

# faces over fewer members, against fewer
def faces_at(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +M: List<&2, U32>, +m: U32, +h: {RG.faces(ys, v, d, M) == True{} : Bool}, hm: {RG.has(ys, m) == True{} : Bool}) ->
    {RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, M) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, M) == True{} : Bool}, MB.false_ne_true()(hm))
    case Con{+c, +r}:
      or_cases(U32.is_eq(c, m), RG.has(r, m), RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, M), hm,
        q => ME.subst(U32, k => {RG.faces.m(List.get(&2, U32, v, AD.slot((k + 1 : U32), d)), d, M) == True{} : Bool}, c, m, MS.u32_eq_of_is_eq(c, m, q), MB.eq_true_of_and_left(RG.faces.m(List.get(&2, U32, v, AD.slot((c + 1 : U32), d)), d, M), RG.faces(r, v, d, M), h)),
        hh => faces_at(r, v, d, M, m, MB.eq_true_of_and_right(RG.faces.m(List.get(&2, U32, v, AD.slot((c + 1 : U32), d)), d, M), RG.faces(r, v, d, M), h), hh))

def faces_sub(L: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +M: List<&2, U32>, +N: List<&2, U32>, +hl: {RG.sub(L, M) == True{} : Bool}, +hn: {RG.sub(N, M) == True{} : Bool},
    +h: {RG.faces(M, v, d, M) == True{} : Bool}) -> {RG.faces(L, v, d, N) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, N), RG.faces(r, v, d, N), fm_sub(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, M, N, hn, faces_at(M, v, d, M, m, h, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hl))), faces_sub(r, v, d, M, N, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hl), hn, h))

# a member's words off the head's
def lay_head(M: List<&2, U32>, +d: Nat, +m: U32, +h: {RG.layout(M, d) == True{} : Bool}, hm: {RG.has(M, m) == True{} : Bool}) -> {RG.off(RG.nw(m), d, P.at_fh()) == True{} : Bool}:
  match M:
    case Nil{}:
      Empty.absurd({RG.off(RG.nw(m), d, P.at_fh()) == True{} : Bool}, MB.false_ne_true()(hm))
    case Con{+c, +r}:
      or_cases(U32.is_eq(c, m), RG.has(r, m), RG.off(RG.nw(m), d, P.at_fh()), hm,
        q => ME.subst(U32, k => {RG.off(RG.nw(k), d, P.at_fh()) == True{} : Bool}, c, m, MS.u32_eq_of_is_eq(c, m, q), MB.eq_true_of_and_left(RG.off(RG.nw(c), d, P.at_fh()), Bool.and(RG.cross(r, d, c), RG.layout(r, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(c), d), Bool.and(RG.off(RG.nw(c), d, P.at_fh()), Bool.and(RG.cross(r, d, c), RG.layout(r, d))), h))),
        hh => lay_head(r, d, m, MB.eq_true_of_and_right(RG.cross(r, d, c), RG.layout(r, d), MB.eq_true_of_and_right(RG.off(RG.nw(c), d, P.at_fh()), Bool.and(RG.cross(r, d, c), RG.layout(r, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(c), d), Bool.and(RG.off(RG.nw(c), d, P.at_fh()), Bool.and(RG.cross(r, d, c), RG.layout(r, d))), h))), hh))

# the words a free writes off every other member's word 1

def ones_z0(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +z: U32, +hk: {RG.sub(K, M) == True{} : Bool}, +h: {RG.layout(M, d) == True{} : Bool},
    +hz: {RG.has(M, z) == True{} : Bool}, +hnz: {RG.has(K, z) == False{} : Bool}) -> {ones(K, d, z) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(z, d), AD.slot((m + 1 : U32), d))), ones(r, d, z), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(z, d), AD.slot((m + 1 : U32), d))), RG.off(Con{(z + 1 : U32), Con{(z + 2 : U32), Con{(z + 3 : U32), Nil{}}}}, d, (m + 1 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(z), d, (m + 1 : U32)), (RG.off(RG.nw(z), d, (m + 2 : U32)) && RG.off(RG.nw(z), d, (m + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(z), d, m), (RG.off(RG.nw(z), d, (m + 1 : U32)) && (RG.off(RG.nw(z), d, (m + 2 : U32)) && RG.off(RG.nw(z), d, (m + 3 : U32)))), lay_pair(M, d, m, z, h, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hk), hz, or_false_l(U32.is_eq(m, z), RG.has(r, z), hnz))))), ones_z0(r, M, d, z, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hk), h, hz, or_false_r(U32.is_eq(m, z), RG.has(r, z), hnz)))

def ones_z1(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +z: U32, +hk: {RG.sub(K, M) == True{} : Bool}, +h: {RG.layout(M, d) == True{} : Bool},
    +hz: {RG.has(M, z) == True{} : Bool}, +hnz: {RG.has(K, z) == False{} : Bool}) -> {ones(K, d, (z + 1 : U32)) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((z + 1 : U32), d), AD.slot((m + 1 : U32), d))), ones(r, d, (z + 1 : U32)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((z + 1 : U32), d), AD.slot((m + 1 : U32), d))), RG.off(Con{(z + 2 : U32), Con{(z + 3 : U32), Nil{}}}, d, (m + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(z, d), AD.slot((m + 1 : U32), d))), RG.off(Con{(z + 1 : U32), Con{(z + 2 : U32), Con{(z + 3 : U32), Nil{}}}}, d, (m + 1 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(z), d, (m + 1 : U32)), (RG.off(RG.nw(z), d, (m + 2 : U32)) && RG.off(RG.nw(z), d, (m + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(z), d, m), (RG.off(RG.nw(z), d, (m + 1 : U32)) && (RG.off(RG.nw(z), d, (m + 2 : U32)) && RG.off(RG.nw(z), d, (m + 3 : U32)))), lay_pair(M, d, m, z, h, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hk), hz, or_false_l(U32.is_eq(m, z), RG.has(r, z), hnz)))))), ones_z1(r, M, d, z, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hk), h, hz, or_false_r(U32.is_eq(m, z), RG.has(r, z), hnz)))

def o3_step(+m: U32, +p: U32, +d: Nat, +M: List<&2, U32>, +b: Bool, e: {U32.is_eq(m, p) == b : Bool},
    +h: {RG.layout(M, d) == True{} : Bool}, +hm: {RG.has(M, m) == True{} : Bool}, +hp: {RG.has(M, p) == True{} : Bool}) -> {Bool.not(Nat.is_eq(AD.slot((p + 3 : U32), d), AD.slot((m + 1 : U32), d))) == True{} : Bool}:
  match b:
    case True{}:
      ME.subst(U32, q => {Bool.not(Nat.is_eq(AD.slot((p + 3 : U32), d), AD.slot((q + 1 : U32), d))) == True{} : Bool}, p, m, Equal.sym(U32, m, p, MS.u32_eq_of_is_eq(m, p, e)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((p + 3 : U32), d), AD.slot((p + 1 : U32), d))), RG.off(Nil{}, d, (p + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((p + 2 : U32), d), AD.slot((p + 1 : U32), d))), RG.off(Con{(p + 3 : U32), Nil{}}, d, (p + 1 : U32)), MB.eq_true_of_and_left(RG.off(Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}, d, (p + 1 : U32)), RG.apartw(Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}, d), MB.eq_true_of_and_right(RG.off(Con{(p + 1 : U32), Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}}, d, p), RG.apartw(Con{(p + 1 : U32), Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}}, d), lay_self(M, d, p, h, hp))))))
    case False{}:
      MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((p + 3 : U32), d), AD.slot((m + 1 : U32), d))), RG.off(Nil{}, d, (m + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((p + 2 : U32), d), AD.slot((m + 1 : U32), d))), RG.off(Con{(p + 3 : U32), Nil{}}, d, (m + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((p + 1 : U32), d), AD.slot((m + 1 : U32), d))), RG.off(Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}, d, (m + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(p, d), AD.slot((m + 1 : U32), d))), RG.off(Con{(p + 1 : U32), Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}}, d, (m + 1 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(p), d, (m + 1 : U32)), (RG.off(RG.nw(p), d, (m + 2 : U32)) && RG.off(RG.nw(p), d, (m + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(p), d, m), (RG.off(RG.nw(p), d, (m + 1 : U32)) && (RG.off(RG.nw(p), d, (m + 2 : U32)) && RG.off(RG.nw(p), d, (m + 3 : U32)))), lay_pair(M, d, m, p, h, hm, hp, e)))))))

def ones_p3(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +p: U32, +hk: {RG.sub(K, M) == True{} : Bool}, +h: {RG.layout(M, d) == True{} : Bool}, +hp: {RG.has(M, p) == True{} : Bool}) ->
    {ones(K, d, (p + 3 : U32)) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((p + 3 : U32), d), AD.slot((m + 1 : U32), d))), ones(r, d, (p + 3 : U32)), o3_step(m, p, d, M, U32.is_eq(m, p), {==}, h, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hk), hp), ones_p3(r, M, d, p, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hk), h, hp))

def ones_head(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +hk: {RG.sub(K, M) == True{} : Bool}, +h: {RG.layout(M, d) == True{} : Bool}) -> {ones(K, d, P.at_fh()) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((m + 1 : U32), d))), ones(r, d, P.at_fh()), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(P.at_fh(), d)), Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((m + 1 : U32), d)), MN.is_eq_comm(AD.slot((m + 1 : U32), d), AD.slot(P.at_fh(), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(P.at_fh(), d))), RG.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, P.at_fh()), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(P.at_fh(), d))), RG.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, P.at_fh()), lay_head(M, d, m, h, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hk))))), ones_head(r, M, d, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hk), h))

# a link of two ports, each's link word off the links: every face kept
def lx_faces(+sy: Bool, +sz: Bool, +t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +y: U32, +z: U32, +K: List<&2, U32>, +N: List<&2, U32>,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hK: {RG.faces(K, AD.view(U32, LAT.fromT(U32, t)), d, N) == True{} : Bool},
    +hy: {RG.port.ok(N, d, y) == True{} : Bool}, +hz: {RG.port.ok(N, d, z) == True{} : Bool}) -> {RG.faces(K, AD.view(U32, RG.words(P.link.to(sz, P.link.to(sy, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, z), z, y))), d, N) == True{} : Bool}:
  match sy:
    case True{}:
      match sz:
        case True{}:
          hK
        case False{}:
          %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (z + 1 : U32), y)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((z + 1 : U32), d), y), LA.set_view(U32, LAT.fromT(U32, t), d, (z + 1 : U32), y, hft, hd32)) :
            {RG.faces(K, _, d, N) == True{} : Bool}
          faces_write(K, AD.view(U32, LAT.fromT(U32, t)), d, N, (z + 1 : U32), y, hK, hy)
    case False{}:
      match sz:
        case True{}:
          %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d), z), LA.set_view(U32, LAT.fromT(U32, t), d, (y + 1 : U32), z, hft, hd32)) :
            {RG.faces(K, _, d, N) == True{} : Bool}
          faces_write(K, AD.view(U32, LAT.fromT(U32, t)), d, N, (y + 1 : U32), z, hK, hz)
        case False{}:
          %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), (z + 1 : U32), y)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z)), AD.slot((z + 1 : U32), d), y), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), d, (z + 1 : U32), y, LA.set_full(U32, LAT.fromT(U32, t), d, (y + 1 : U32), z, hft), hd32)) :
            {RG.faces(K, _, d, N) == True{} : Bool}
          %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d), z), LA.set_view(U32, LAT.fromT(U32, t), d, (y + 1 : U32), z, hft, hd32)) :
            {RG.faces(K, List.set(&2, U32, _, AD.slot((z + 1 : U32), d), y), d, N) == True{} : Bool}
          faces_write(K, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d), z), d, N, (z + 1 : U32), y, faces_write(K, AD.view(U32, LAT.fromT(U32, t)), d, N, (y + 1 : U32), z, hK, hz), hy)

def ul_faces(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +x: U32, +K: List<&2, U32>, +N: List<&2, U32>,
    hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hK: {RG.faces(K, AD.view(U32, w), d, N) == True{} : Bool},
    ho: {ones(K, d, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{w}, a}, x)) + 3 : U32)) == True{} : Bool}, hdone: {pdone(P.H{KM.MG{w}, a}, x) == True{} : Bool},
    m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
    {RG.faces(K, AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{w}, a}, x))), d, N) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hKt = LAB.subst(Array<U32>, q => {RG.faces(K, AD.view(U32, q), d, N) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hK)
  +ho1 = LAB.subst(Array<U32>, q => {ones(K, d, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{q}, a}, x)) + 3 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), ho)
  +hot = LAB.subst(Array<V.Val>, q => {ones(K, d, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, q}, x)) + 3 : U32)) == True{} : Bool}, a, LAT.fromT(V.Val, ta), Equal.sym(Array<V.Val>, LAT.fromT(V.Val, ta), a, ea), ho1)
  +hd1 = LAB.subst(Array<U32>, q => {pdone(P.H{KM.MG{q}, a}, x) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hdone)
  +hdt = LAB.subst(Array<V.Val>, q => {pdone(P.H{KM.MG{LAT.fromT(U32, t)}, q}, x) == True{} : Bool}, a, LAT.fromT(V.Val, ta), Equal.sym(Array<V.Val>, LAT.fromT(V.Val, ta), a, ea), hd1)
  %e : {RG.faces(K, AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{_}, a}, x))), d, N) == True{} : Bool}
  %ea : {RG.faces(K, AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x))), d, N) == True{} : Bool}
  %Equal.sym(P.H & U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x), (P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))), pred_pair_ok(t, LAT.fromT(V.Val, ta), d, x, hft, hdt)) :
    {RG.faces(K, AD.view(U32, RG.words(R.rg.unlink.p(_, x))), d, N) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 3 : U32))) :
    {RG.faces(K, AD.view(U32, RG.words(R.rg.unlink.set(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))))), d, N) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.set_view(U32, LAT.fromT(U32, t), d, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), hft, hd32)) :
    {RG.faces(K, _, d, N) == True{} : Bool}
  faces_keep(K, AD.view(U32, LAT.fromT(U32, t)), d, N, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), hKt, hot)

def fr_faces(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +r: U32, +K: List<&2, U32>, +N: List<&2, U32>,
    hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hK: {RG.faces(K, AD.view(U32, w), d, N) == True{} : Bool},
    +h0: {ones(K, d, P.base(r)) == True{} : Bool}, +h1: {ones(K, d, (P.base(r) + 1 : U32)) == True{} : Bool}, +hh: {ones(K, d, P.at_fh()) == True{} : Bool}, m: LAT.Mirror(U32, w)) ->
    {RG.faces(K, AD.view(U32, RG.words(P.free(P.H{KM.MG{w}, a}, r))), d, N) == True{} : Bool}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hKt = LAB.subst(Array<U32>, q => {RG.faces(K, AD.view(U32, q), d, N) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hK)
  %e : {RG.faces(K, AD.view(U32, RG.words(P.free(P.H{KM.MG{_}, a}, r))), d, N) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), LA.get_pair(U32, LAT.fromT(U32, t), P.at_fh())) :
    {RG.faces(K, AD.view(U32, RG.words(P.free.fh(KM.m_get.fin(_), a, r))), d, N) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), P.at_fh(), ((r >> 2n : U32) + 1 : U32))), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())))), AD.slot(P.at_fh(), d), ((r >> 2n : U32) + 1 : U32)), LA.set_view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), d, P.at_fh(), ((r >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), d, (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t), d, P.base(r), 0, hft)), hd32)) :
    {RG.faces(K, _, d, N) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())))), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0)), AD.slot((P.base(r) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), d, (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t), d, P.base(r), 0, hft), hd32)) :
    {RG.faces(K, List.set(&2, U32, _, AD.slot(P.at_fh(), d), ((r >> 2n : U32) + 1 : U32)), d, N) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(P.base(r), d), 0), LA.set_view(U32, LAT.fromT(U32, t), d, P.base(r), 0, hft, hd32)) :
    {RG.faces(K, List.set(&2, U32, List.set(&2, U32, _, AD.slot((P.base(r) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), AD.slot(P.at_fh(), d), ((r >> 2n : U32) + 1 : U32)), d, N) == True{} : Bool}
  faces_keep(K, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(P.base(r), d), 0), AD.slot((P.base(r) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), d, N, P.at_fh(), ((r >> 2n : U32) + 1 : U32), faces_keep(K, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(P.base(r), d), 0), d, N, (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), faces_keep(K, AD.view(U32, LAT.fromT(U32, t)), d, N, P.base(r), 0, hKt, h0), h1), hh)

# The join exact, its faces kept

# lists: those before x a part of the list; what was taken out not there
def slp_go(+t: List<&2, U32>, +y: U32, +x: U32, +b: Bool, +ih: {RG.sub(lpre(t, x), t) == True{} : Bool}) ->
    {RG.sub(pick_l(b, Nil{}, Con{y, lpre(t, x)}), Con{y, t}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      MB.and_eq_true(RG.has(Con{y, t}, y), RG.sub(lpre(t, x), Con{y, t}), has_self(y, t), sub_cons_r(lpre(t, x), y, t, ih))

def sub_lpre(ys: List<&2, U32>, +x: U32) -> {RG.sub(lpre(ys, x), ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      slp_go(t, y, x, U32.is_eq(y, x), sub_lpre(t, x))

def nw_go(+t: List<&2, U32>, +y: U32, +x: U32, +b: Bool, +e: {U32.is_eq(y, x) == b : Bool}, +ih: {RG.has(RG.without(t, x), x) == False{} : Bool}) ->
    {RG.has(List.append(&2, U32, RG.keep(b, y), RG.without(t, x)), x) == False{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      or_ff(U32.is_eq(y, x), RG.has(RG.without(t, x), x), e, ih)

def notin_without(ys: List<&2, U32>, +x: U32) -> {RG.has(RG.without(ys, x), x) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      nw_go(t, y, x, U32.is_eq(y, x), {==}, notin_without(t, x))

def ns_go(+L: List<&2, U32>, +M: List<&2, U32>, +x: U32, +b: Bool, +e: {RG.has(L, x) == b : Bool}, +hs: {RG.sub(L, M) == True{} : Bool}, +h: {RG.has(M, x) == False{} : Bool}) ->
    {RG.has(L, x) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({RG.has(L, x) == False{} : Bool}, MB.true_ne_false()(Equal.trans(Bool, True{}, RG.has(M, x), False{}, Equal.sym(Bool, RG.has(M, x), True{}, sub_has(L, M, x, hs, e)), h)))
    case False{}:
      e

def notin_sub(+L: List<&2, U32>, +M: List<&2, U32>, +x: U32, +hs: {RG.sub(L, M) == True{} : Bool}, +h: {RG.has(M, x) == False{} : Bool}) -> {RG.has(L, x) == False{} : Bool}:
  ns_go(L, M, x, RG.has(L, x), {==}, hs, h)

def ne_go(+cs: List<&2, U32>, +s: U32, +x: U32, +b: Bool, +e: {U32.is_eq(s, x) == b : Bool}, +hs: {RG.has(cs, s) == False{} : Bool}, +hx: {RG.has(cs, x) == True{} : Bool}) ->
    {U32.is_eq(s, x) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({U32.is_eq(s, x) == False{} : Bool}, MB.true_ne_false()(Equal.trans(Bool, True{}, RG.has(cs, s), False{},
        ME.subst(U32, k => {True{} == RG.has(cs, k) : Bool}, x, s, Equal.sym(U32, s, x, MS.u32_eq_of_is_eq(s, x, e)), Equal.sym(Bool, RG.has(cs, x), True{}, hx)), hs)))
    case False{}:
      e

# the faces through the join's steps: the link writes ports off the
# links, the unlinks and frees write off every member's word 1
def join_faces.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +pa: List<&2, U32>, +x: U32, +pb: List<&2, U32>,
  +pc: List<&2, U32>, +y: U32, +pd: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pa, Con{x, pb})) == True{} : Bool}, +hsp: {List.append(&2, U32, pa, pb) == List.append(&2, U32, pc, Con{y, pd}) : List<&2, U32>}, +hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pa, Con{x, pb})), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  hu: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{x, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, hw: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{x, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32)) == True{} : Bool},
  +K: List<&2, U32>, +N: List<&2, U32>, hK: {RG.faces(K, AD.view(U32, w), d, N) == True{} : Bool},
  hU: {RG.port.ok(N, d, Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32)))) == True{} : Bool}, hW: {RG.port.ok(N, d, Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32)))) == True{} : Bool},
  +o1: {ones(K, d, (RG.last(pa, s) + 3 : U32)) == True{} : Bool}, +o2: {ones(K, d, (RG.last(pc, s) + 3 : U32)) == True{} : Bool},
  +ox0: {ones(K, d, P.base(x)) == True{} : Bool}, +ox1: {ones(K, d, (P.base(x) + 1 : U32)) == True{} : Bool}, +oy0: {ones(K, d, P.base(y)) == True{} : Bool}, +oy1: {ones(K, d, (P.base(y) + 1 : U32)) == True{} : Bool},
  +oh: {ones(K, d, P.at_fh()) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.faces(K, AD.view(U32, RG.words(R.join(P.H{KM.MG{w}, a}, x, y))), d, N) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, List.append(&2, U32, pa, Con{x, pb})) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hut = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{x, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hu)
  +hwt = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{x, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (y + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hw)
  +hKt = LAB.subst(Array<U32>, q => {RG.faces(K, AD.view(U32, q), d, N) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hK)
  +hUt = LAB.subst(Array<U32>, q => {RG.port.ok(N, d, Pair.snd(Array<U32>, U32, Array.get(U32, q, (x + 1 : U32)))) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hU)
  +hWt = LAB.subst(Array<U32>, q => {RG.port.ok(N, d, Pair.snd(Array<U32>, U32, Array.get(U32, q, (y + 1 : U32)))) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hW)
  +hr1 = lx_ring(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), s, List.append(&2, U32, pa, Con{x, pb}), hft, hd32, hrt, hut, hwt)
  +hf1 = lx_full(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), hft)
  +kf1 = lx_faces(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), K, N, hft, hd32, hKt, hUt, hWt)
  +pe1 = pred_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, s, pa, x, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))))
  +kf2 = ul_faces(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, x, K, N, hf1, hd32, kf1,
    ME.subst(U32, q => {ones(K, d, (q + 3 : U32)) == True{} : Bool}, RG.last(pa, s), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), Equal.sym(U32, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), RG.last(pa, s), pe1), o1),
    pdone_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, s, pa, x, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))))), LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hr2 = unlink_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, s, pa, x, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf2 = ul_full(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, x, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hr2c = ME.subst(List<&2, U32>, q => {RG.ring(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))), d, s, q) == True{} : Bool}, List.append(&2, U32, pa, pb), List.append(&2, U32, pc, Con{y, pd}), hsp, hr2)
  +hn1 = ME.subst(Nat, q => {Nat.is_lt(q, U32.to_nat(U32.shln(1, d))) == True{} : Bool}, List.length(&2, U32, List.append(&2, U32, pa, Con{x, pb})), 1n+List.length(&2, U32, List.append(&2, U32, pa, pb)), len_mid(pa, x, pb), hn)
  +hn2 = ME.subst(List<&2, U32>, q => {Nat.is_lt(List.length(&2, U32, q), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, List.append(&2, U32, pa, pb), List.append(&2, U32, pc, Con{y, pd}), hsp,
    MN.lt_trans(List.length(&2, U32, List.append(&2, U32, pa, pb)), 1n+List.length(&2, U32, List.append(&2, U32, pa, pb)), U32.to_nat(U32.shln(1, d)), MN.lt_succ_self(List.length(&2, U32, List.append(&2, U32, pa, pb))), hn1))
  +pe2 = pred_exact.go(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, s, pc, y, pd, hf2, hd32, hr2c, hn2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))))
  +kf3 = ul_faces(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, y, K, N, hf2, hd32, kf2,
    ME.subst(U32, q => {ones(K, d, (q + 3 : U32)) == True{} : Bool}, RG.last(pc, s), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), Equal.sym(U32, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), RG.last(pc, s), pe2), o2),
    pdone_exact.go(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, s, pc, y, pd, hf2, hd32, hr2c, hn2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)))), LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf3 = ul_full(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, y, hf2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +kf4 = fr_faces(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), d, x, K, N, hf3, hd32, kf3, ox0, ox1, oh, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))))
  +hf4 = fr_full(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), d, x, hf3, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))))
  %e : {RG.faces(K, AD.view(U32, RG.words(R.join(P.H{KM.MG{_}, a}, x, y))), d, N) == True{} : Bool}
  %ea : {RG.faces(K, AD.view(U32, RG.words(R.join(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x, y))), d, N) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 1 : U32))) :
    {RG.faces(K, AD.view(U32, RG.words(R.jn.u(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), x, y))), d, N) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (y + 1 : U32))) :
    {RG.faces(K, AD.view(U32, RG.words(R.jn.w(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), x, y))), d, N) == True{} : Bool}
  %lx_parts(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))) :
    {RG.faces(K, AD.view(U32, RG.words(P.free(P.free(R.rg.unlink(R.rg.unlink(_, x), y), x), y))), d, N) == True{} : Bool}
  %ul_parts(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, x, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {RG.faces(K, AD.view(U32, RG.words(P.free(P.free(R.rg.unlink(_, y), x), y))), d, N) == True{} : Bool}
  %ul_parts(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, y, hf2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {RG.faces(K, AD.view(U32, RG.words(P.free(P.free(_, x), y))), d, N) == True{} : Bool}
  %fr_parts(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), x, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)))) :
    {RG.faces(K, AD.view(U32, RG.words(P.free(_, y))), d, N) == True{} : Bool}
  fr_faces(RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, y, K, N, hf4, hd32, kf4, oy0, oy1, oh, LAT.mirror(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))))

# the join by membership: x's split, then y's in the ring without x;
# the list's own facts kept by taking members out, the faces by the steps
def join_exact.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32, +y: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {RG.ring.ok(AD.view(U32, w), d, s, cs) == True{} : Bool},
  +hx: {RG.has(cs, x) == True{} : Bool}, +hy: {RG.has(cs, y) == True{} : Bool}, +hxy: {U32.is_eq(x, y) == False{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.ring.ok(AD.view(U32, RG.words(R.join(P.H{KM.MG{w}, a}, x, y))), d, s, RG.without(RG.without(cs, x), y)) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring.ok(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  %e : {RG.ring.ok(AD.view(U32, RG.words(R.join(P.H{KM.MG{_}, a}, x, y))), d, s, RG.without(RG.without(cs, x), y)) == True{} : Bool}
  %ea : {RG.ring.ok(AD.view(U32, RG.words(R.join(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x, y))), d, s, RG.without(RG.without(cs, x), y)) == True{} : Bool}
  +hring = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)
  +hlay = MB.eq_true_of_and_left(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt))
  +hbases = MB.eq_true_of_and_left(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hfaces = MB.eq_true_of_and_right(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hut = LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, Con{s, cs}) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (x + 1 : U32), hft, hd32)), faces_at(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}, x, hfaces, has_cons(s, cs, x, hx)))
  +hwt = LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, Con{s, cs}) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (y + 1 : U32), hft, hd32)), faces_at(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}, y, hfaces, has_cons(s, cs, y, hy)))
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hring)
  +hnt = len_ok(t, d, s, cs, hft, hd32, hap)
  +eqWX = without_eq(d, s, cs, x, hap, hx)
  +hyW = has_without(cs, x, y, hxy, hy)
  +hapX = ME.subst(List<&2, U32>, q => {RG.apart.all(Con{s, q}, d) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), cs, split_of_has(cs, x, hx)), hap)
  +hapWX = ME.subst(List<&2, U32>, q => {RG.apart.all(Con{s, q}, d) == True{} : Bool}, List.append(&2, U32, lpre(cs, x), lpost(cs, x)), RG.without(cs, x), Equal.sym(List<&2, U32>, RG.without(cs, x), List.append(&2, U32, lpre(cs, x), lpost(cs, x)), eqWX), ap_remove(Con{s, lpre(cs, x)}, x, lpost(cs, x), d, hapX))
  +eqWXY = without_eq(d, s, RG.without(cs, x), y, hapWX, hyW)
  +hsp = Equal.trans(List<&2, U32>, List.append(&2, U32, lpre(cs, x), lpost(cs, x)), RG.without(cs, x), List.append(&2, U32, lpre(RG.without(cs, x), y), Con{y, lpost(RG.without(cs, x), y)}), Equal.sym(List<&2, U32>, RG.without(cs, x), List.append(&2, U32, lpre(cs, x), lpost(cs, x)), eqWX), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(RG.without(cs, x), y), Con{y, lpost(RG.without(cs, x), y)}), RG.without(cs, x), split_of_has(RG.without(cs, x), y, hyW)))
  +subw = sub_trans(RG.without(RG.without(cs, x), y), RG.without(cs, x), cs, sub_without(RG.without(cs, x), y), sub_without(cs, x))
  +subr = MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(RG.without(RG.without(cs, x), y), Con{s, cs}), has_self(s, cs), sub_cons_r(RG.without(RG.without(cs, x), y), s, cs, subw))
  +hbx = MS.u32_eq_of_is_eq(P.base(x), x, bases_at(Con{s, cs}, x, hbases, has_cons(s, cs, x, hx)))
  +hby = MS.u32_eq_of_is_eq(P.base(y), y, bases_at(Con{s, cs}, y, hbases, has_cons(s, cs, y, hy)))
  +hrs = ring_split(AD.view(U32, LAT.fromT(U32, t)), d, s, cs, x, hring, hx)
  +hnx = ME.subst(List<&2, U32>, q => {Nat.is_lt(List.length(&2, U32, q), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), cs, split_of_has(cs, x, hx)), hnt)
  +hus = ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), cs, split_of_has(cs, x, hx)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), hut))
  +hws = ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), cs, split_of_has(cs, x, hx)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32)), hwt))
  +hns = apart_notin(cs, d, s, MB.eq_true_of_and_left(RG.apart(cs, d, s), RG.apart.all(cs, d), hap))
  +nx = or_ff(U32.is_eq(s, x), RG.has(RG.without(RG.without(cs, x), y), x), ne_go(cs, s, x, U32.is_eq(s, x), {==}, hns, hx), notin_sub(RG.without(RG.without(cs, x), y), RG.without(cs, x), x, sub_without(RG.without(cs, x), y), notin_without(cs, x)))
  +ny = or_ff(U32.is_eq(s, y), RG.has(RG.without(RG.without(cs, x), y), y), ne_go(cs, s, y, U32.is_eq(s, y), {==}, hns, hy), notin_without(RG.without(cs, x), y))
  +r = join_exact.go(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, lpre(cs, x), x, lpost(cs, x), lpre(RG.without(cs, x), y), y, lpost(RG.without(cs, x), y), hft, hd32, hrs, hsp, hnx, hbx, hby, hus, hws,
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, x) == True{} : Bool}, RG.without(RG.without(cs, x), y), List.append(&2, U32, lpre(RG.without(cs, x), y), lpost(RG.without(cs, x), y)), eqWXY, links_sub(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, d, x, subr, lol_build0(Con{s, cs}, Con{s, cs}, d, x, sub_refl(Con{s, cs}), hlay, has_cons(s, cs, x, hx)))),
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (x + 1 : U32)) == True{} : Bool}, RG.without(RG.without(cs, x), y), List.append(&2, U32, lpre(RG.without(cs, x), y), lpost(RG.without(cs, x), y)), eqWXY, links_sub(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, d, (x + 1 : U32), subr, lol_build1(Con{s, cs}, Con{s, cs}, d, x, sub_refl(Con{s, cs}), hlay, has_cons(s, cs, x, hx)))),
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, y) == True{} : Bool}, RG.without(RG.without(cs, x), y), List.append(&2, U32, lpre(RG.without(cs, x), y), lpost(RG.without(cs, x), y)), eqWXY, links_sub(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, d, y, subr, lol_build0(Con{s, cs}, Con{s, cs}, d, y, sub_refl(Con{s, cs}), hlay, has_cons(s, cs, y, hy)))),
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (y + 1 : U32)) == True{} : Bool}, RG.without(RG.without(cs, x), y), List.append(&2, U32, lpre(RG.without(cs, x), y), lpost(RG.without(cs, x), y)), eqWXY, links_sub(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, d, (y + 1 : U32), subr, lol_build1(Con{s, cs}, Con{s, cs}, d, y, sub_refl(Con{s, cs}), hlay, has_cons(s, cs, y, hy)))),
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, P.at_fh()) == True{} : Bool}, RG.without(RG.without(cs, x), y), List.append(&2, U32, lpre(RG.without(cs, x), y), lpost(RG.without(cs, x), y)), eqWXY, links_sub(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, d, P.at_fh(), subr, head_links(Con{s, cs}, d, hlay))), LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +fj = join_faces.go(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, lpre(cs, x), x, lpost(cs, x), lpre(RG.without(cs, x), y), y, lpost(RG.without(cs, x), y), hft, hd32, hrs, hsp, hnx, hus, hws,
    Con{s, RG.without(RG.without(cs, x), y)}, Con{s, RG.without(RG.without(cs, x), y)}, faces_sub(Con{s, RG.without(RG.without(cs, x), y)}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}, Con{s, RG.without(RG.without(cs, x), y)}, subr, subr, hfaces),
    port_sub(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), subr, hut), port_sub(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), subr, hwt),
    ones_p3(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, d, RG.last(lpre(cs, x), s), subr, hlay,
      sub_has(Con{s, lpre(cs, x)}, Con{s, cs}, RG.last(lpre(cs, x), s), MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(lpre(cs, x), Con{s, cs}), has_self(s, cs), sub_cons_r(lpre(cs, x), s, cs, sub_lpre(cs, x))), last_mem(lpre(cs, x), s))),
    ones_p3(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, d, RG.last(lpre(RG.without(cs, x), y), s), subr, hlay,
      sub_has(Con{s, lpre(RG.without(cs, x), y)}, Con{s, cs}, RG.last(lpre(RG.without(cs, x), y), s), MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(lpre(RG.without(cs, x), y), Con{s, cs}), has_self(s, cs), sub_cons_r(lpre(RG.without(cs, x), y), s, cs, sub_trans(lpre(RG.without(cs, x), y), RG.without(cs, x), cs, sub_lpre(RG.without(cs, x), y), sub_without(cs, x)))), last_mem(lpre(RG.without(cs, x), y), s))),
    ME.subst(U32, q => {ones(Con{s, RG.without(RG.without(cs, x), y)}, d, q) == True{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), ones_z0(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, d, x, subr, hlay, has_cons(s, cs, x, hx), nx)),
    ME.subst(U32, q => {ones(Con{s, RG.without(RG.without(cs, x), y)}, d, (q + 1 : U32)) == True{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), ones_z1(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, d, x, subr, hlay, has_cons(s, cs, x, hx), nx)),
    ME.subst(U32, q => {ones(Con{s, RG.without(RG.without(cs, x), y)}, d, q) == True{} : Bool}, y, P.base(y), Equal.sym(U32, P.base(y), y, hby), ones_z0(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, d, y, subr, hlay, has_cons(s, cs, y, hy), ny)),
    ME.subst(U32, q => {ones(Con{s, RG.without(RG.without(cs, x), y)}, d, (q + 1 : U32)) == True{} : Bool}, y, P.base(y), Equal.sym(U32, P.base(y), y, hby), ones_z1(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, d, y, subr, hlay, has_cons(s, cs, y, hy), ny)),
    ones_head(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, d, subr, hlay), LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  MB.and_eq_true(RG.ring(AD.view(U32, RG.words(R.join(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))), d, s, RG.without(RG.without(cs, x), y)), Bool.and(RG.layout(Con{s, RG.without(RG.without(cs, x), y)}, d), Bool.and(RG.bases(Con{s, RG.without(RG.without(cs, x), y)}), RG.faces(Con{s, RG.without(RG.without(cs, x), y)}, AD.view(U32, RG.words(R.join(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))), d, Con{s, RG.without(RG.without(cs, x), y)}))), ME.subst(List<&2, U32>, q => {RG.ring(AD.view(U32, RG.words(R.join(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))), d, s, q) == True{} : Bool}, List.append(&2, U32, lpre(RG.without(cs, x), y), lpost(RG.without(cs, x), y)), RG.without(RG.without(cs, x), y), Equal.sym(List<&2, U32>, RG.without(RG.without(cs, x), y), List.append(&2, U32, lpre(RG.without(cs, x), y), lpost(RG.without(cs, x), y)), eqWXY), r), MB.and_eq_true(RG.layout(Con{s, RG.without(RG.without(cs, x), y)}, d), Bool.and(RG.bases(Con{s, RG.without(RG.without(cs, x), y)}), RG.faces(Con{s, RG.without(RG.without(cs, x), y)}, AD.view(U32, RG.words(R.join(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))), d, Con{s, RG.without(RG.without(cs, x), y)})), MB.and_eq_true(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(RG.without(RG.without(cs, x), y), d, s), RG.layout(RG.without(RG.without(cs, x), y), d))), MB.eq_true_of_and_left(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d))), hlay), MB.and_eq_true(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(RG.without(RG.without(cs, x), y), d, s), RG.layout(RG.without(RG.without(cs, x), y), d)), MB.eq_true_of_and_left(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d))), hlay)), MB.and_eq_true(RG.cross(RG.without(RG.without(cs, x), y), d, s), RG.layout(RG.without(RG.without(cs, x), y), d), cross_sub(RG.without(RG.without(cs, x), y), cs, d, s, subw, MB.eq_true_of_and_left(RG.cross(cs, d, s), RG.layout(cs, d), MB.eq_true_of_and_right(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d))), hlay)))), lay_without(RG.without(cs, x), d, y, lay_without(cs, d, x, MB.eq_true_of_and_right(RG.cross(cs, d, s), RG.layout(cs, d), MB.eq_true_of_and_right(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d))), hlay)))))))), MB.and_eq_true(RG.bases(Con{s, RG.without(RG.without(cs, x), y)}), RG.faces(Con{s, RG.without(RG.without(cs, x), y)}, AD.view(U32, RG.words(R.join(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))), d, Con{s, RG.without(RG.without(cs, x), y)}), bases_sub(Con{s, RG.without(RG.without(cs, x), y)}, Con{s, cs}, subr, hbases), fj)))

def Laws.join_exact(w, a, d, s, t, x, y, hf, hd32, hr, hx, hy, hxy):
  join_exact.m(w, a, d, s, t, x, y, hf, hd32, hr, hx, hy, hxy, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# A placeholder joined, a cursor leaving

def ones_out0(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +z: U32, +hk: {RG.sub(K, M) == True{} : Bool}, +hc: {RG.cross(M, d, z) == True{} : Bool}) ->
    {ones(K, d, z) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(z, d), AD.slot((m + 1 : U32), d))), ones(r, d, z), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(z, d)), Nat.is_eq(AD.slot(z, d), AD.slot((m + 1 : U32), d)), MN.is_eq_comm(AD.slot((m + 1 : U32), d), AD.slot(z, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(z, d))), RG.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, z), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(z, d))), RG.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, z), MB.eq_true_of_and_left(RG.off(RG.nw(m), d, z), (RG.off(RG.nw(m), d, (z + 1 : U32)) && (RG.off(RG.nw(m), d, (z + 2 : U32)) && RG.off(RG.nw(m), d, (z + 3 : U32)))), cross_at(M, d, z, m, hc, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hk)))))), ones_out0(r, M, d, z, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hk), hc))

def links_out0(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +z: U32, +hk: {RG.sub(K, M) == True{} : Bool}, +hc: {RG.cross(M, d, z) == True{} : Bool}) ->
    {RG.off.links(K, d, z) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(z, d), AD.slot((m + 3 : U32), d))), RG.off.links(r, d, z), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(z, d)), Nat.is_eq(AD.slot(z, d), AD.slot((m + 3 : U32), d)), MN.is_eq_comm(AD.slot((m + 3 : U32), d), AD.slot(z, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(z, d))), RG.off(Nil{}, d, z), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(z, d))), RG.off(Con{(m + 3 : U32), Nil{}}, d, z), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(z, d))), RG.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, z), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(z, d))), RG.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, z), MB.eq_true_of_and_left(RG.off(RG.nw(m), d, z), (RG.off(RG.nw(m), d, (z + 1 : U32)) && (RG.off(RG.nw(m), d, (z + 2 : U32)) && RG.off(RG.nw(m), d, (z + 3 : U32)))), cross_at(M, d, z, m, hc, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hk)))))))), links_out0(r, M, d, z, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hk), hc))

def ones_out1(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +z: U32, +hk: {RG.sub(K, M) == True{} : Bool}, +hc: {RG.cross(M, d, z) == True{} : Bool}) ->
    {ones(K, d, (z + 1 : U32)) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((z + 1 : U32), d), AD.slot((m + 1 : U32), d))), ones(r, d, (z + 1 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot((z + 1 : U32), d)), Nat.is_eq(AD.slot((z + 1 : U32), d), AD.slot((m + 1 : U32), d)), MN.is_eq_comm(AD.slot((m + 1 : U32), d), AD.slot((z + 1 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot((z + 1 : U32), d))), RG.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, (z + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot((z + 1 : U32), d))), RG.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, (z + 1 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(m), d, (z + 1 : U32)), (RG.off(RG.nw(m), d, (z + 2 : U32)) && RG.off(RG.nw(m), d, (z + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(m), d, z), (RG.off(RG.nw(m), d, (z + 1 : U32)) && (RG.off(RG.nw(m), d, (z + 2 : U32)) && RG.off(RG.nw(m), d, (z + 3 : U32)))), cross_at(M, d, z, m, hc, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hk))))))), ones_out1(r, M, d, z, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hk), hc))

def links_out1(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +z: U32, +hk: {RG.sub(K, M) == True{} : Bool}, +hc: {RG.cross(M, d, z) == True{} : Bool}) ->
    {RG.off.links(K, d, (z + 1 : U32)) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((z + 1 : U32), d), AD.slot((m + 3 : U32), d))), RG.off.links(r, d, (z + 1 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot((z + 1 : U32), d)), Nat.is_eq(AD.slot((z + 1 : U32), d), AD.slot((m + 3 : U32), d)), MN.is_eq_comm(AD.slot((m + 3 : U32), d), AD.slot((z + 1 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot((z + 1 : U32), d))), RG.off(Nil{}, d, (z + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot((z + 1 : U32), d))), RG.off(Con{(m + 3 : U32), Nil{}}, d, (z + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot((z + 1 : U32), d))), RG.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, (z + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot((z + 1 : U32), d))), RG.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, (z + 1 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(m), d, (z + 1 : U32)), (RG.off(RG.nw(m), d, (z + 2 : U32)) && RG.off(RG.nw(m), d, (z + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(m), d, z), (RG.off(RG.nw(m), d, (z + 1 : U32)) && (RG.off(RG.nw(m), d, (z + 2 : U32)) && RG.off(RG.nw(m), d, (z + 3 : U32)))), cross_at(M, d, z, m, hc, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hk))))))))), links_out1(r, M, d, z, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hk), hc))

# join1: its ring exact without the member that leaves
def join1_exact.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +pa: List<&2, U32>, +x: U32, +m0: U32, +pb: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pa, Con{m0, pb})) == True{} : Bool}, +hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pa, Con{m0, pb})), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  hu: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, hw: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (m0 + 1 : U32))) + 1 : U32)) == True{} : Bool},
  +h00: {RG.off.links(Con{s, List.append(&2, U32, pa, pb)}, d, P.base(x)) == True{} : Bool}, +h10: {RG.off.links(Con{s, List.append(&2, U32, pa, pb)}, d, (P.base(x) + 1 : U32)) == True{} : Bool}, +h01: {RG.off.links(Con{s, List.append(&2, U32, pa, pb)}, d, P.base(m0)) == True{} : Bool}, +h11: {RG.off.links(Con{s, List.append(&2, U32, pa, pb)}, d, (P.base(m0) + 1 : U32)) == True{} : Bool}, +hh: {RG.off.links(Con{s, List.append(&2, U32, pa, pb)}, d, P.at_fh()) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.ring(AD.view(U32, RG.words(R.join1(P.H{KM.MG{w}, a}, x, m0))), d, s, List.append(&2, U32, pa, pb)) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, List.append(&2, U32, pa, Con{m0, pb})) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hut = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hu)
  +hwt = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (m0 + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hw)
  +hr1 = lx_ring(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), s, List.append(&2, U32, pa, Con{m0, pb}), hft, hd32, hrt, hut, hwt)
  +hf1 = lx_full(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), hft)
  +hr2 = unlink_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, s, pa, m0, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf2 = ul_full(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, m0, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hr3 = fr_ring(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)), LAT.fromT(V.Val, ta), d, x, s, List.append(&2, U32, pa, pb), hf2, hd32, hr2, h00, h10, hh, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0))))
  +hf3 = fr_full(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)), LAT.fromT(V.Val, ta), d, x, hf2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0))))
  +hr4 = fr_ring(RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, m0, s, List.append(&2, U32, pa, pb), hf3, hd32, hr3, h01, h11, hh, LAT.mirror(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0))}, LAT.fromT(V.Val, ta)}, x))))
  %e : {RG.ring(AD.view(U32, RG.words(R.join1(P.H{KM.MG{_}, a}, x, m0))), d, s, List.append(&2, U32, pa, pb)) == True{} : Bool}
  %ea : {RG.ring(AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x, m0))), d, s, List.append(&2, U32, pa, pb)) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 1 : U32))) :
    {RG.ring(AD.view(U32, RG.words(R.jn1.u(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), x, m0))), d, s, List.append(&2, U32, pa, pb)) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) :
    {RG.ring(AD.view(U32, RG.words(R.jn1.w(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), x, m0))), d, s, List.append(&2, U32, pa, pb)) == True{} : Bool}
  %lx_parts(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))) :
    {RG.ring(AD.view(U32, RG.words(P.free(P.free(R.rg.unlink(_, m0), x), m0))), d, s, List.append(&2, U32, pa, pb)) == True{} : Bool}
  %ul_parts(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, m0, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {RG.ring(AD.view(U32, RG.words(P.free(P.free(_, x), m0))), d, s, List.append(&2, U32, pa, pb)) == True{} : Bool}
  %fr_parts(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)), LAT.fromT(V.Val, ta), x, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)))) :
    {RG.ring(AD.view(U32, RG.words(P.free(_, m0))), d, s, List.append(&2, U32, pa, pb)) == True{} : Bool}
  hr4

def join1_faces.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +pa: List<&2, U32>, +x: U32, +m0: U32, +pb: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pa, Con{m0, pb})) == True{} : Bool}, +hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pa, Con{m0, pb})), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  hu: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, hw: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (m0 + 1 : U32))) + 1 : U32)) == True{} : Bool},
  +K: List<&2, U32>, +N: List<&2, U32>, hK: {RG.faces(K, AD.view(U32, w), d, N) == True{} : Bool},
  hU: {RG.port.ok(N, d, Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32)))) == True{} : Bool}, hW: {RG.port.ok(N, d, Pair.snd(Array<U32>, U32, Array.get(U32, w, (m0 + 1 : U32)))) == True{} : Bool},
  +om: {ones(K, d, (RG.last(pa, s) + 3 : U32)) == True{} : Bool}, +o00: {ones(K, d, P.base(x)) == True{} : Bool}, +o10: {ones(K, d, (P.base(x) + 1 : U32)) == True{} : Bool}, +o01: {ones(K, d, P.base(m0)) == True{} : Bool}, +o11: {ones(K, d, (P.base(m0) + 1 : U32)) == True{} : Bool}, +oh: {ones(K, d, P.at_fh()) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.faces(K, AD.view(U32, RG.words(R.join1(P.H{KM.MG{w}, a}, x, m0))), d, N) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, List.append(&2, U32, pa, Con{m0, pb})) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hut = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hu)
  +hwt = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (m0 + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hw)
  +hKt = LAB.subst(Array<U32>, q => {RG.faces(K, AD.view(U32, q), d, N) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hK)
  +hUt = LAB.subst(Array<U32>, q => {RG.port.ok(N, d, Pair.snd(Array<U32>, U32, Array.get(U32, q, (x + 1 : U32)))) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hU)
  +hWt = LAB.subst(Array<U32>, q => {RG.port.ok(N, d, Pair.snd(Array<U32>, U32, Array.get(U32, q, (m0 + 1 : U32)))) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hW)
  +hr1 = lx_ring(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), s, List.append(&2, U32, pa, Con{m0, pb}), hft, hd32, hrt, hut, hwt)
  +hf1 = lx_full(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), hft)
  +kf1 = lx_faces(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), K, N, hft, hd32, hKt, hUt, hWt)
  +pe = pred_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, s, pa, m0, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))))
  +kf2 = ul_faces(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, m0, K, N, hf1, hd32, kf1,
    ME.subst(U32, q => {ones(K, d, (q + 3 : U32)) == True{} : Bool}, RG.last(pa, s), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)), Equal.sym(U32, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)), RG.last(pa, s), pe), om),
    pdone_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, s, pa, m0, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))))), LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf2 = ul_full(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, m0, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf3 = fr_full(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)), LAT.fromT(V.Val, ta), d, x, hf2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0))))
  +kf3 = fr_faces(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)), LAT.fromT(V.Val, ta), d, x, K, N, hf2, hd32, kf2, o00, o10, oh, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0))))
  %e : {RG.faces(K, AD.view(U32, RG.words(R.join1(P.H{KM.MG{_}, a}, x, m0))), d, N) == True{} : Bool}
  %ea : {RG.faces(K, AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x, m0))), d, N) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 1 : U32))) :
    {RG.faces(K, AD.view(U32, RG.words(R.jn1.u(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), x, m0))), d, N) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) :
    {RG.faces(K, AD.view(U32, RG.words(R.jn1.w(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), x, m0))), d, N) == True{} : Bool}
  %lx_parts(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))) :
    {RG.faces(K, AD.view(U32, RG.words(P.free(P.free(R.rg.unlink(_, m0), x), m0))), d, N) == True{} : Bool}
  %ul_parts(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, m0, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {RG.faces(K, AD.view(U32, RG.words(P.free(P.free(_, x), m0))), d, N) == True{} : Bool}
  %fr_parts(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)), LAT.fromT(V.Val, ta), x, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)))) :
    {RG.faces(K, AD.view(U32, RG.words(P.free(_, m0))), d, N) == True{} : Bool}
  fr_faces(RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, m0, K, N, hf3, hd32, kf3, o01, o11, oh, LAT.mirror(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0))}, LAT.fromT(V.Val, ta)}, x))))

# leave: its ring exact without the member that leaves
def leave_exact.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +pa: List<&2, U32>, +pp: U32, +m0: U32, +pb: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pa, Con{m0, pb})) == True{} : Bool}, +hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pa, Con{m0, pb})), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  hu: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (pp + 1 : U32)) == True{} : Bool}, hw: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (m0 + 1 : U32))) + 1 : U32)) == True{} : Bool},
  +h00: {RG.off.links(Con{s, List.append(&2, U32, pa, pb)}, d, P.base(m0)) == True{} : Bool}, +h10: {RG.off.links(Con{s, List.append(&2, U32, pa, pb)}, d, (P.base(m0) + 1 : U32)) == True{} : Bool}, +hh: {RG.off.links(Con{s, List.append(&2, U32, pa, pb)}, d, P.at_fh()) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.ring(AD.view(U32, RG.words(R.leave(P.H{KM.MG{w}, a}, pp, m0))), d, s, List.append(&2, U32, pa, pb)) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, List.append(&2, U32, pa, Con{m0, pb})) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hut = hu
  +hwt = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (m0 + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hw)
  +hr1 = lx_ring(P.is_static(pp), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), s, List.append(&2, U32, pa, Con{m0, pb}), hft, hd32, hrt, hut, hwt)
  +hf1 = lx_full(P.is_static(pp), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), hft)
  +hr2 = unlink_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp)), LAT.fromT(V.Val, ta), d, s, pa, m0, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf2 = ul_full(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp)), LAT.fromT(V.Val, ta), d, m0, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hr3 = fr_ring(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, m0)), LAT.fromT(V.Val, ta), d, m0, s, List.append(&2, U32, pa, pb), hf2, hd32, hr2, h00, h10, hh, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, m0))))
  %e : {RG.ring(AD.view(U32, RG.words(R.leave(P.H{KM.MG{_}, a}, pp, m0))), d, s, List.append(&2, U32, pa, pb)) == True{} : Bool}
  %ea : {RG.ring(AD.view(U32, RG.words(R.leave(P.H{KM.MG{LAT.fromT(U32, t)}, _}, pp, m0))), d, s, List.append(&2, U32, pa, pb)) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) :
    {RG.ring(AD.view(U32, RG.words(R.lv.w(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), pp, m0))), d, s, List.append(&2, U32, pa, pb)) == True{} : Bool}
  %lx_parts(P.is_static(pp), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))) :
    {RG.ring(AD.view(U32, RG.words(P.free(R.rg.unlink(_, m0), m0))), d, s, List.append(&2, U32, pa, pb)) == True{} : Bool}
  %ul_parts(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp)), LAT.fromT(V.Val, ta), d, m0, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {RG.ring(AD.view(U32, RG.words(P.free(_, m0))), d, s, List.append(&2, U32, pa, pb)) == True{} : Bool}
  hr3

def leave_faces.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +pa: List<&2, U32>, +pp: U32, +m0: U32, +pb: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pa, Con{m0, pb})) == True{} : Bool}, +hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pa, Con{m0, pb})), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  hu: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (pp + 1 : U32)) == True{} : Bool}, hw: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (m0 + 1 : U32))) + 1 : U32)) == True{} : Bool},
  +K: List<&2, U32>, +N: List<&2, U32>, hK: {RG.faces(K, AD.view(U32, w), d, N) == True{} : Bool},
  hU: {RG.port.ok(N, d, pp) == True{} : Bool}, hW: {RG.port.ok(N, d, Pair.snd(Array<U32>, U32, Array.get(U32, w, (m0 + 1 : U32)))) == True{} : Bool},
  +om: {ones(K, d, (RG.last(pa, s) + 3 : U32)) == True{} : Bool}, +o00: {ones(K, d, P.base(m0)) == True{} : Bool}, +o10: {ones(K, d, (P.base(m0) + 1 : U32)) == True{} : Bool}, +oh: {ones(K, d, P.at_fh()) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.faces(K, AD.view(U32, RG.words(R.leave(P.H{KM.MG{w}, a}, pp, m0))), d, N) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, List.append(&2, U32, pa, Con{m0, pb})) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hut = hu
  +hwt = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (m0 + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hw)
  +hKt = LAB.subst(Array<U32>, q => {RG.faces(K, AD.view(U32, q), d, N) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hK)
  +hUt = hU
  +hWt = LAB.subst(Array<U32>, q => {RG.port.ok(N, d, Pair.snd(Array<U32>, U32, Array.get(U32, q, (m0 + 1 : U32)))) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hW)
  +hr1 = lx_ring(P.is_static(pp), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), s, List.append(&2, U32, pa, Con{m0, pb}), hft, hd32, hrt, hut, hwt)
  +hf1 = lx_full(P.is_static(pp), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), hft)
  +kf1 = lx_faces(P.is_static(pp), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), K, N, hft, hd32, hKt, hUt, hWt)
  +pe = pred_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp)), LAT.fromT(V.Val, ta), d, s, pa, m0, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp))))
  +kf2 = ul_faces(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp)), LAT.fromT(V.Val, ta), d, m0, K, N, hf1, hd32, kf1,
    ME.subst(U32, q => {ones(K, d, (q + 3 : U32)) == True{} : Bool}, RG.last(pa, s), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, m0)), Equal.sym(U32, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, m0)), RG.last(pa, s), pe), om),
    pdone_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp)), LAT.fromT(V.Val, ta), d, s, pa, m0, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp)))), LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf2 = ul_full(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp)), LAT.fromT(V.Val, ta), d, m0, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))

  %e : {RG.faces(K, AD.view(U32, RG.words(R.leave(P.H{KM.MG{_}, a}, pp, m0))), d, N) == True{} : Bool}
  %ea : {RG.faces(K, AD.view(U32, RG.words(R.leave(P.H{KM.MG{LAT.fromT(U32, t)}, _}, pp, m0))), d, N) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) :
    {RG.faces(K, AD.view(U32, RG.words(R.lv.w(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), pp, m0))), d, N) == True{} : Bool}
  %lx_parts(P.is_static(pp), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))) :
    {RG.faces(K, AD.view(U32, RG.words(P.free(R.rg.unlink(_, m0), m0))), d, N) == True{} : Bool}
  %ul_parts(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp)), LAT.fromT(V.Val, ta), d, m0, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {RG.faces(K, AD.view(U32, RG.words(P.free(_, m0))), d, N) == True{} : Bool}
  fr_faces(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, m0)), LAT.fromT(V.Val, ta), d, m0, K, N, hf2, hd32, kf2, o00, o10, oh, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, m0))))

# join1 by membership
def join1_exact.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32, +m0: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {RG.ring.ok(AD.view(U32, w), d, s, cs) == True{} : Bool},
  hx: {RG.node.ok(AD.view(U32, w), d, Con{s, cs}, x) == True{} : Bool}, +hm: {RG.has(cs, m0) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.ring.ok(AD.view(U32, RG.words(R.join1(P.H{KM.MG{w}, a}, x, m0))), d, s, RG.without(cs, m0)) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring.ok(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hxt = LAB.subst(Array<U32>, q => {RG.node.ok(AD.view(U32, q), d, Con{s, cs}, x) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hx)
  +hring = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)
  +hlay = MB.eq_true_of_and_left(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt))
  +hbases = MB.eq_true_of_and_left(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hfaces = MB.eq_true_of_and_right(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hring)
  +hn = len_ok(t, d, s, cs, hft, hd32, hap)
  +eqW = without_eq(d, s, cs, m0, hap, hm)
  +subr = MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(RG.without(cs, m0), Con{s, cs}), has_self(s, cs), sub_cons_r(RG.without(cs, m0), s, cs, sub_without(cs, m0)))
  +hbm = MS.u32_eq_of_is_eq(P.base(m0), m0, bases_at(Con{s, cs}, m0, hbases, has_cons(s, cs, m0, hm)))
  +hrs = ring_split(AD.view(U32, LAT.fromT(U32, t)), d, s, cs, m0, hring, hm)
  +hnm = ME.subst(List<&2, U32>, q => {Nat.is_lt(List.length(&2, U32, q), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), cs, split_of_has(cs, m0, hm)), hn)
  +hwt = LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, Con{s, cs}) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m0 + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m0 + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (m0 + 1 : U32), hft, hd32)), faces_at(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}, m0, hfaces, has_cons(s, cs, m0, hm)))
  +hws = ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), cs, split_of_has(cs, m0, hm)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) + 1 : U32)), hwt))
  +hns = apart_notin(cs, d, s, MB.eq_true_of_and_left(RG.apart(cs, d, s), RG.apart.all(cs, d), hap))
  +nm = or_ff(U32.is_eq(s, m0), RG.has(RG.without(cs, m0), m0), ne_go(cs, s, m0, U32.is_eq(s, m0), {==}, hns, hm), notin_without(cs, m0))
  +om = ones_p3(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, RG.last(lpre(cs, m0), s), subr, hlay,
    sub_has(Con{s, lpre(cs, m0)}, Con{s, cs}, RG.last(lpre(cs, m0), s), MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(lpre(cs, m0), Con{s, cs}), has_self(s, cs), sub_cons_r(lpre(cs, m0), s, cs, sub_lpre(cs, m0))), last_mem(lpre(cs, m0), s)))
  +hcx = MB.eq_true_of_and_left(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs})), hxt)
  +hbx = MS.u32_eq_of_is_eq(P.base(x), x, MB.eq_true_of_and_left(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs})), hxt)))
  +hut = LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, Con{s, cs}) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))},
    Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (x + 1 : U32), hft, hd32)), MB.eq_true_of_and_right(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs})), hxt)))
  %e : {RG.ring.ok(AD.view(U32, RG.words(R.join1(P.H{KM.MG{_}, a}, x, m0))), d, s, RG.without(cs, m0)) == True{} : Bool}
  %ea : {RG.ring.ok(AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x, m0))), d, s, RG.without(cs, m0)) == True{} : Bool}
  +r = join1_exact.go(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, lpre(cs, m0), x, m0, lpost(cs, m0), hft, hd32, hrs, hnm, ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), cs, split_of_has(cs, m0, hm)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), hut)), hws,
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, P.base(x)) == True{} : Bool}, RG.without(cs, m0), List.append(&2, U32, lpre(cs, m0), lpost(cs, m0)), eqW, ME.subst(U32, q => {RG.off.links(Con{s, RG.without(cs, m0)}, d, q) == True{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), links_out0(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, x, subr, hcx))),
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (P.base(x) + 1 : U32)) == True{} : Bool}, RG.without(cs, m0), List.append(&2, U32, lpre(cs, m0), lpost(cs, m0)), eqW, ME.subst(U32, q => {RG.off.links(Con{s, RG.without(cs, m0)}, d, (q + 1 : U32)) == True{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), links_out1(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, x, subr, hcx))),
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, P.base(m0)) == True{} : Bool}, RG.without(cs, m0), List.append(&2, U32, lpre(cs, m0), lpost(cs, m0)), eqW, ME.subst(U32, q => {RG.off.links(Con{s, RG.without(cs, m0)}, d, q) == True{} : Bool}, m0, P.base(m0), Equal.sym(U32, P.base(m0), m0, hbm), lol_build0(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, m0, subr, hlay, has_cons(s, cs, m0, hm)))),
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (P.base(m0) + 1 : U32)) == True{} : Bool}, RG.without(cs, m0), List.append(&2, U32, lpre(cs, m0), lpost(cs, m0)), eqW, ME.subst(U32, q => {RG.off.links(Con{s, RG.without(cs, m0)}, d, (q + 1 : U32)) == True{} : Bool}, m0, P.base(m0), Equal.sym(U32, P.base(m0), m0, hbm), lol_build1(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, m0, subr, hlay, has_cons(s, cs, m0, hm)))),
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, P.at_fh()) == True{} : Bool}, RG.without(cs, m0), List.append(&2, U32, lpre(cs, m0), lpost(cs, m0)), eqW, links_sub(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, P.at_fh(), subr, head_links(Con{s, cs}, d, hlay))), LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +fj = join1_faces.go(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, lpre(cs, m0), x, m0, lpost(cs, m0), hft, hd32, hrs, hnm, ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), cs, split_of_has(cs, m0, hm)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), hut)), hws,
    Con{s, RG.without(cs, m0)}, Con{s, RG.without(cs, m0)}, faces_sub(Con{s, RG.without(cs, m0)}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}, Con{s, RG.without(cs, m0)}, subr, subr, hfaces),
    port_sub(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), subr, hut), port_sub(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), subr, hwt), om,
    ME.subst(U32, q => {ones(Con{s, RG.without(cs, m0)}, d, q) == True{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), ones_out0(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, x, subr, hcx)),
    ME.subst(U32, q => {ones(Con{s, RG.without(cs, m0)}, d, (q + 1 : U32)) == True{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), ones_out1(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, x, subr, hcx)),
    ME.subst(U32, q => {ones(Con{s, RG.without(cs, m0)}, d, q) == True{} : Bool}, m0, P.base(m0), Equal.sym(U32, P.base(m0), m0, hbm), ones_z0(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, m0, subr, hlay, has_cons(s, cs, m0, hm), nm)),
    ME.subst(U32, q => {ones(Con{s, RG.without(cs, m0)}, d, (q + 1 : U32)) == True{} : Bool}, m0, P.base(m0), Equal.sym(U32, P.base(m0), m0, hbm), ones_z1(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, m0, subr, hlay, has_cons(s, cs, m0, hm), nm)),
    ones_head(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, subr, hlay), LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  MB.and_eq_true(RG.ring(AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, s, RG.without(cs, m0)), Bool.and(RG.layout(Con{s, RG.without(cs, m0)}, d), Bool.and(RG.bases(Con{s, RG.without(cs, m0)}), RG.faces(Con{s, RG.without(cs, m0)}, AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, Con{s, RG.without(cs, m0)}))), ME.subst(List<&2, U32>, q => {RG.ring(AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, s, q) == True{} : Bool}, List.append(&2, U32, lpre(cs, m0), lpost(cs, m0)), RG.without(cs, m0), Equal.sym(List<&2, U32>, RG.without(cs, m0), List.append(&2, U32, lpre(cs, m0), lpost(cs, m0)), eqW), r), MB.and_eq_true(RG.layout(Con{s, RG.without(cs, m0)}, d), Bool.and(RG.bases(Con{s, RG.without(cs, m0)}), RG.faces(Con{s, RG.without(cs, m0)}, AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, Con{s, RG.without(cs, m0)})), MB.and_eq_true(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(RG.without(cs, m0), d, s), RG.layout(RG.without(cs, m0), d))), MB.eq_true_of_and_left(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d))), hlay), MB.and_eq_true(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(RG.without(cs, m0), d, s), RG.layout(RG.without(cs, m0), d)), MB.eq_true_of_and_left(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d))), hlay)), MB.and_eq_true(RG.cross(RG.without(cs, m0), d, s), RG.layout(RG.without(cs, m0), d), cross_sub(RG.without(cs, m0), cs, d, s, sub_without(cs, m0), MB.eq_true_of_and_left(RG.cross(cs, d, s), RG.layout(cs, d), MB.eq_true_of_and_right(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d))), hlay)))), lay_without(cs, d, m0, MB.eq_true_of_and_right(RG.cross(cs, d, s), RG.layout(cs, d), MB.eq_true_of_and_right(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d))), hlay))))))), MB.and_eq_true(RG.bases(Con{s, RG.without(cs, m0)}), RG.faces(Con{s, RG.without(cs, m0)}, AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, Con{s, RG.without(cs, m0)}), bases_sub(Con{s, RG.without(cs, m0)}, Con{s, cs}, subr, hbases), fj)))

def Laws.join1_exact(w, a, d, s, t, x, y, hf, hd32, hr, hx, hy):
  join1_exact.m(w, a, d, s, t, x, y, hf, hd32, hr, hx, hy, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# leave by membership
def leave_exact.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +pp: U32, +m0: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {RG.ring.ok(AD.view(U32, w), d, s, cs) == True{} : Bool},
  +hm: {RG.has(cs, m0) == True{} : Bool}, +hp: {RG.port.ok(Con{s, cs}, d, pp) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.ring.ok(AD.view(U32, RG.words(R.leave(P.H{KM.MG{w}, a}, pp, m0))), d, s, RG.without(cs, m0)) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring.ok(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hring = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)
  +hlay = MB.eq_true_of_and_left(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt))
  +hbases = MB.eq_true_of_and_left(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hfaces = MB.eq_true_of_and_right(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hring)
  +hn = len_ok(t, d, s, cs, hft, hd32, hap)
  +eqW = without_eq(d, s, cs, m0, hap, hm)
  +subr = MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(RG.without(cs, m0), Con{s, cs}), has_self(s, cs), sub_cons_r(RG.without(cs, m0), s, cs, sub_without(cs, m0)))
  +hbm = MS.u32_eq_of_is_eq(P.base(m0), m0, bases_at(Con{s, cs}, m0, hbases, has_cons(s, cs, m0, hm)))
  +hrs = ring_split(AD.view(U32, LAT.fromT(U32, t)), d, s, cs, m0, hring, hm)
  +hnm = ME.subst(List<&2, U32>, q => {Nat.is_lt(List.length(&2, U32, q), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), cs, split_of_has(cs, m0, hm)), hn)
  +hwt = LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, Con{s, cs}) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m0 + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m0 + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (m0 + 1 : U32), hft, hd32)), faces_at(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}, m0, hfaces, has_cons(s, cs, m0, hm)))
  +hws = ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), cs, split_of_has(cs, m0, hm)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) + 1 : U32)), hwt))
  +hns = apart_notin(cs, d, s, MB.eq_true_of_and_left(RG.apart(cs, d, s), RG.apart.all(cs, d), hap))
  +nm = or_ff(U32.is_eq(s, m0), RG.has(RG.without(cs, m0), m0), ne_go(cs, s, m0, U32.is_eq(s, m0), {==}, hns, hm), notin_without(cs, m0))
  +om = ones_p3(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, RG.last(lpre(cs, m0), s), subr, hlay,
    sub_has(Con{s, lpre(cs, m0)}, Con{s, cs}, RG.last(lpre(cs, m0), s), MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(lpre(cs, m0), Con{s, cs}), has_self(s, cs), sub_cons_r(lpre(cs, m0), s, cs, sub_lpre(cs, m0))), last_mem(lpre(cs, m0), s)))
  %e : {RG.ring.ok(AD.view(U32, RG.words(R.leave(P.H{KM.MG{_}, a}, pp, m0))), d, s, RG.without(cs, m0)) == True{} : Bool}
  %ea : {RG.ring.ok(AD.view(U32, RG.words(R.leave(P.H{KM.MG{LAT.fromT(U32, t)}, _}, pp, m0))), d, s, RG.without(cs, m0)) == True{} : Bool}
  +r = leave_exact.go(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, lpre(cs, m0), pp, m0, lpost(cs, m0), hft, hd32, hrs, hnm, ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (pp + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), cs, split_of_has(cs, m0, hm)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (pp + 1 : U32)), RG.off.pos(Con{s, cs}, d, (pp + 1 : U32)), hp)), hws,
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, P.base(m0)) == True{} : Bool}, RG.without(cs, m0), List.append(&2, U32, lpre(cs, m0), lpost(cs, m0)), eqW, ME.subst(U32, q => {RG.off.links(Con{s, RG.without(cs, m0)}, d, q) == True{} : Bool}, m0, P.base(m0), Equal.sym(U32, P.base(m0), m0, hbm), lol_build0(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, m0, subr, hlay, has_cons(s, cs, m0, hm)))),
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (P.base(m0) + 1 : U32)) == True{} : Bool}, RG.without(cs, m0), List.append(&2, U32, lpre(cs, m0), lpost(cs, m0)), eqW, ME.subst(U32, q => {RG.off.links(Con{s, RG.without(cs, m0)}, d, (q + 1 : U32)) == True{} : Bool}, m0, P.base(m0), Equal.sym(U32, P.base(m0), m0, hbm), lol_build1(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, m0, subr, hlay, has_cons(s, cs, m0, hm)))),
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, P.at_fh()) == True{} : Bool}, RG.without(cs, m0), List.append(&2, U32, lpre(cs, m0), lpost(cs, m0)), eqW, links_sub(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, P.at_fh(), subr, head_links(Con{s, cs}, d, hlay))), LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +fj = leave_faces.go(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, lpre(cs, m0), pp, m0, lpost(cs, m0), hft, hd32, hrs, hnm, ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (pp + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), cs, split_of_has(cs, m0, hm)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (pp + 1 : U32)), RG.off.pos(Con{s, cs}, d, (pp + 1 : U32)), hp)), hws,
    Con{s, RG.without(cs, m0)}, Con{s, RG.without(cs, m0)}, faces_sub(Con{s, RG.without(cs, m0)}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}, Con{s, RG.without(cs, m0)}, subr, subr, hfaces),
    port_sub(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, pp, subr, hp), port_sub(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), subr, hwt), om,
    ME.subst(U32, q => {ones(Con{s, RG.without(cs, m0)}, d, q) == True{} : Bool}, m0, P.base(m0), Equal.sym(U32, P.base(m0), m0, hbm), ones_z0(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, m0, subr, hlay, has_cons(s, cs, m0, hm), nm)),
    ME.subst(U32, q => {ones(Con{s, RG.without(cs, m0)}, d, (q + 1 : U32)) == True{} : Bool}, m0, P.base(m0), Equal.sym(U32, P.base(m0), m0, hbm), ones_z1(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, m0, subr, hlay, has_cons(s, cs, m0, hm), nm)),
    ones_head(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, subr, hlay), LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  MB.and_eq_true(RG.ring(AD.view(U32, RG.words(R.leave(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, m0))), d, s, RG.without(cs, m0)), Bool.and(RG.layout(Con{s, RG.without(cs, m0)}, d), Bool.and(RG.bases(Con{s, RG.without(cs, m0)}), RG.faces(Con{s, RG.without(cs, m0)}, AD.view(U32, RG.words(R.leave(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, m0))), d, Con{s, RG.without(cs, m0)}))), ME.subst(List<&2, U32>, q => {RG.ring(AD.view(U32, RG.words(R.leave(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, m0))), d, s, q) == True{} : Bool}, List.append(&2, U32, lpre(cs, m0), lpost(cs, m0)), RG.without(cs, m0), Equal.sym(List<&2, U32>, RG.without(cs, m0), List.append(&2, U32, lpre(cs, m0), lpost(cs, m0)), eqW), r), MB.and_eq_true(RG.layout(Con{s, RG.without(cs, m0)}, d), Bool.and(RG.bases(Con{s, RG.without(cs, m0)}), RG.faces(Con{s, RG.without(cs, m0)}, AD.view(U32, RG.words(R.leave(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, m0))), d, Con{s, RG.without(cs, m0)})), MB.and_eq_true(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(RG.without(cs, m0), d, s), RG.layout(RG.without(cs, m0), d))), MB.eq_true_of_and_left(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d))), hlay), MB.and_eq_true(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(RG.without(cs, m0), d, s), RG.layout(RG.without(cs, m0), d)), MB.eq_true_of_and_left(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d))), hlay)), MB.and_eq_true(RG.cross(RG.without(cs, m0), d, s), RG.layout(RG.without(cs, m0), d), cross_sub(RG.without(cs, m0), cs, d, s, sub_without(cs, m0), MB.eq_true_of_and_left(RG.cross(cs, d, s), RG.layout(cs, d), MB.eq_true_of_and_right(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d))), hlay)))), lay_without(cs, d, m0, MB.eq_true_of_and_right(RG.cross(cs, d, s), RG.layout(cs, d), MB.eq_true_of_and_right(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d)), MB.eq_true_of_and_right(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d))), hlay))))))), MB.and_eq_true(RG.bases(Con{s, RG.without(cs, m0)}), RG.faces(Con{s, RG.without(cs, m0)}, AD.view(U32, RG.words(R.leave(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, m0))), d, Con{s, RG.without(cs, m0)}), bases_sub(Con{s, RG.without(cs, m0)}, Con{s, cs}, subr, hbases), fj)))

def Laws.leave_exact(w, a, d, s, t, p, c, hf, hd32, hr, hc, hp):
  leave_exact.m(w, a, d, s, t, p, c, hf, hd32, hr, hc, hp, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# The ring exact with its nodes through an insert

# a node apart from each of ys has its word 3 apart from theirs
def apart_of_cross(ys: List<&2, U32>, +d: Nat, +x: U32, +h: {RG.cross(ys, d, x) == True{} : Bool}) -> {RG.apart(ys, d, x) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      +hd = MB.eq_true_of_and_left(RG.disj4(d, x, y), RG.cross(r, d, x), h)
      +o3 = MB.eq_true_of_and_right(RG.off(RG.nw(y), d, (x + 2 : U32)), RG.off(RG.nw(y), d, (x + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(y), d, (x + 1 : U32)), Bool.and(RG.off(RG.nw(y), d, (x + 2 : U32)), RG.off(RG.nw(y), d, (x + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(y), d, x), Bool.and(RG.off(RG.nw(y), d, (x + 1 : U32)), Bool.and(RG.off(RG.nw(y), d, (x + 2 : U32)), RG.off(RG.nw(y), d, (x + 3 : U32)))), hd)))
      +n3 = MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((y + 3 : U32), d), AD.slot((x + 3 : U32), d))), RG.off(Nil{}, d, (x + 3 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((y + 2 : U32), d), AD.slot((x + 3 : U32), d))), RG.off(Con{(y + 3 : U32), Nil{}}, d, (x + 3 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot((x + 3 : U32), d))), RG.off(Con{(y + 2 : U32), Con{(y + 3 : U32), Nil{}}}, d, (x + 3 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(y, d), AD.slot((x + 3 : U32), d))), RG.off(Con{(y + 1 : U32), Con{(y + 2 : U32), Con{(y + 3 : U32), Nil{}}}}, d, (x + 3 : U32)), o3))))
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d))), RG.apart(r, d, x), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((y + 3 : U32), d), AD.slot((x + 3 : U32), d)), Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d)), MN.is_eq_comm(AD.slot((y + 3 : U32), d), AD.slot((x + 3 : U32), d)), n3), apart_of_cross(r, d, x, MB.eq_true_of_and_right(RG.disj4(d, x, y), RG.cross(r, d, x), h)))

# a face off the links of Con{s, t} and off x's word 3 is off those of
# Con{s, Con{x, t}}
def fm_add(m: Maybe<&2, U32>, +d: Nat, +s: U32, +t: List<&2, U32>, +x: U32, +h: {RG.faces.m(m, d, Con{s, t}) == True{} : Bool}, +hx: {RG.faces.m(m, d, Con{x, Nil{}}) == True{} : Bool}) ->
    {RG.faces.m(m, d, Con{s, Con{x, t}}) == True{} : Bool}:
  match m:
    case Some{+r}:
      MB.and_eq_true(RG.off.links(Con{s, Con{x, t}}, d, (r + 1 : U32)), RG.off.pos(Con{s, Con{x, t}}, d, (r + 1 : U32)), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((s + 3 : U32), d))), RG.off.links(Con{x, t}, d, (r + 1 : U32)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((s + 3 : U32), d))), RG.off.links(t, d, (r + 1 : U32)), MB.eq_true_of_and_left(RG.off.links(Con{s, t}, d, (r + 1 : U32)), RG.off.pos(Con{s, t}, d, (r + 1 : U32)), h)), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((x + 3 : U32), d))), RG.off.links(t, d, (r + 1 : U32)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((x + 3 : U32), d))), RG.off.links(Nil{}, d, (r + 1 : U32)), MB.eq_true_of_and_left(RG.off.links(Con{x, Nil{}}, d, (r + 1 : U32)), RG.off.pos(Con{x, Nil{}}, d, (r + 1 : U32)), hx)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((s + 3 : U32), d))), RG.off.links(t, d, (r + 1 : U32)), MB.eq_true_of_and_left(RG.off.links(Con{s, t}, d, (r + 1 : U32)), RG.off.pos(Con{s, t}, d, (r + 1 : U32)), h)))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((s + 2 : U32), d))), RG.off.pos(Con{x, t}, d, (r + 1 : U32)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((s + 2 : U32), d))), RG.off.pos(t, d, (r + 1 : U32)), MB.eq_true_of_and_right(RG.off.links(Con{s, t}, d, (r + 1 : U32)), RG.off.pos(Con{s, t}, d, (r + 1 : U32)), h)), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((x + 2 : U32), d))), RG.off.pos(t, d, (r + 1 : U32)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((x + 2 : U32), d))), RG.off.pos(Nil{}, d, (r + 1 : U32)), MB.eq_true_of_and_right(RG.off.links(Con{x, Nil{}}, d, (r + 1 : U32)), RG.off.pos(Con{x, Nil{}}, d, (r + 1 : U32)), hx)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((s + 2 : U32), d))), RG.off.pos(t, d, (r + 1 : U32)), MB.eq_true_of_and_right(RG.off.links(Con{s, t}, d, (r + 1 : U32)), RG.off.pos(Con{s, t}, d, (r + 1 : U32)), h)))))
    case None{}:
      h

def faces_add(K: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +s: U32, +t: List<&2, U32>, +x: U32,
    +h: {RG.faces(K, v, d, Con{s, t}) == True{} : Bool}, +hx: {RG.faces(K, v, d, Con{x, Nil{}}) == True{} : Bool}) -> {RG.faces(K, v, d, Con{s, Con{x, t}}) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, Con{s, Con{x, t}}), RG.faces(r, v, d, Con{s, Con{x, t}}), fm_add(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, s, t, x, MB.eq_true_of_and_left(RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, Con{s, t}), RG.faces(r, v, d, Con{s, t}), h), MB.eq_true_of_and_left(RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, Con{x, Nil{}}), RG.faces(r, v, d, Con{x, Nil{}}), hx)), faces_add(r, v, d, s, t, x, MB.eq_true_of_and_right(RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, Con{s, t}), RG.faces(r, v, d, Con{s, t}), h), MB.eq_true_of_and_right(RG.faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, Con{x, Nil{}}), RG.faces(r, v, d, Con{x, Nil{}}), hx)))

# an insert writes two words 3, off every member's word 1: every face kept
def ins_faces(+t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +K: List<&2, U32>, +M: List<&2, U32>,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +h: {RG.faces(K, AD.view(U32, LAT.fromT(U32, t)), d, M) == True{} : Bool}, +hox: {ones(K, d, (x + 3 : U32)) == True{} : Bool}, +hos: {ones(K, d, (s + 3 : U32)) == True{} : Bool}) ->
    {RG.faces(K, AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{LAT.fromT(U32, t)}, a}, s, x))), d, M) == True{} : Bool}:
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), hft)
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (s + 3 : U32))) :
    {RG.faces(K, AD.view(U32, RG.words(R.rg.insert.r(P.rd.fin(KM.m_get.fin(_), a), s, x))), d, M) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), (s + 3 : U32), x)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))))), AD.slot((s + 3 : U32), d), x), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), d, (s + 3 : U32), x, hf1, hd32)) :
    {RG.faces(K, _, d, M) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), LA.set_view(U32, LAT.fromT(U32, t), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), hft, hd32)) :
    {RG.faces(K, List.set(&2, U32, _, AD.slot((s + 3 : U32), d), x), d, M) == True{} : Bool}
  faces_keep(K, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), d, M, (s + 3 : U32), x, faces_keep(K, AD.view(U32, LAT.fromT(U32, t)), d, M, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), h, hox), hos)

def insert_ok.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {RG.ring.ok(AD.view(U32, w), d, s, cs) == True{} : Bool},
  hx: {RG.enter.ok(AD.view(U32, w), d, s, cs, x) == True{} : Bool}, m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.ring.ok(AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{w}, a}, s, x))), d, s, Con{x, cs}) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring.ok(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hxt = LAB.subst(Array<U32>, q => {RG.enter.ok(AD.view(U32, q), d, s, cs, x) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hx)
  +hring = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)
  +hk = MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)
  +hlay = MB.eq_true_of_and_left(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), hk)
  +hbf = MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), hk)
  +hbases = MB.eq_true_of_and_left(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), hbf)
  +hfaces = MB.eq_true_of_and_right(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), hbf)
  +he0 = MB.eq_true_of_and_left(RG.apartw(RG.nw(x), d), Bool.and(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))))), hxt)
  +hx1 = MB.eq_true_of_and_right(RG.apartw(RG.nw(x), d), Bool.and(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))))), hxt)
  +he1 = MB.eq_true_of_and_left(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}})))), hx1)
  +hx2 = MB.eq_true_of_and_right(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}})))), hx1)
  +he2 = MB.eq_true_of_and_left(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))), hx2)
  +hx3 = MB.eq_true_of_and_right(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))), hx2)
  +he3 = MB.eq_true_of_and_left(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}})), hx3)
  +hx4 = MB.eq_true_of_and_right(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}})), hx3)
  +he4 = MB.eq_true_of_and_left(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}), hx4)
  +he5 = MB.eq_true_of_and_right(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}), hx4)
  +hl0 = MB.eq_true_of_and_left(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d))), hlay)
  +hm1 = MB.eq_true_of_and_right(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d))), hlay)
  +hl1 = MB.eq_true_of_and_left(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d)), hm1)
  +hm2 = MB.eq_true_of_and_right(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(cs, d, s), RG.layout(cs, d)), hm1)
  +hl2 = MB.eq_true_of_and_left(RG.cross(cs, d, s), RG.layout(cs, d), hm2)
  +hm3 = MB.eq_true_of_and_right(RG.cross(cs, d, s), RG.layout(cs, d), hm2)
  +hdxs = MB.eq_true_of_and_left(RG.disj4(d, x, s), RG.cross(cs, d, x), he2)
  +hcx = MB.eq_true_of_and_right(RG.disj4(d, x, s), RG.cross(cs, d, x), he2)
  +hlayL = MB.and_eq_true(RG.apartw(RG.nw(s), d), Bool.and(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(Con{x, cs}, d, s), RG.layout(Con{x, cs}, d))), hl0, MB.and_eq_true(RG.off(RG.nw(s), d, P.at_fh()), Bool.and(RG.cross(Con{x, cs}, d, s), RG.layout(Con{x, cs}, d)), hl1, MB.and_eq_true(RG.cross(Con{x, cs}, d, s), RG.layout(Con{x, cs}, d), MB.and_eq_true(RG.disj4(d, s, x), RG.cross(cs, d, s), disj4_sym(d, x, s, hdxs), hl2), MB.and_eq_true(RG.apartw(RG.nw(x), d), Bool.and(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(cs, d, x), RG.layout(cs, d))), he0, MB.and_eq_true(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(cs, d, x), RG.layout(cs, d)), he1, MB.and_eq_true(RG.cross(cs, d, x), RG.layout(cs, d), hcx, hm3))))))
  +hbasesL = MB.and_eq_true(U32.is_eq(P.base(s), s), RG.bases(Con{x, cs}), MB.eq_true_of_and_left(U32.is_eq(P.base(s), s), RG.bases(cs), hbases), MB.and_eq_true(U32.is_eq(P.base(x), x), RG.bases(cs), he3, MB.eq_true_of_and_right(U32.is_eq(P.base(s), s), RG.bases(cs), hbases)))
  +hfa = faces_add(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, s, cs, x, hfaces, he5)
  +hfacesL = MB.and_eq_true(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((s + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{x, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, Con{x, cs}}), MB.eq_true_of_and_left(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((s + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(cs, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, Con{x, cs}}), hfa), MB.and_eq_true(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(cs, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, Con{x, cs}}), he4, MB.eq_true_of_and_right(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((s + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(cs, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, Con{x, cs}}), hfa)))
  +hox = ones_p3(Con{s, Con{x, cs}}, Con{s, Con{x, cs}}, d, x, sub_refl(Con{s, Con{x, cs}}), hlayL, has_cons(s, Con{x, cs}, x, has_self(x, cs)))
  +hos = ones_p3(Con{s, Con{x, cs}}, Con{s, Con{x, cs}}, d, s, sub_refl(Con{s, Con{x, cs}}), hlayL, has_self(s, Con{x, cs}))
  +hr1 = insert_exact.go(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, x, hft, hd32, hring, apart_of_cross(Con{s, cs}, d, x, he2), LAT.mirror(U32, LAT.fromT(U32, t)))
  +hF = ins_faces(t, LAT.fromT(V.Val, ta), d, s, x, Con{s, Con{x, cs}}, Con{s, Con{x, cs}}, hft, hd32, hfacesL, hox, hos)
  %e : {RG.ring.ok(AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{_}, a}, s, x))), d, s, Con{x, cs}) == True{} : Bool}
  %ea : {RG.ring.ok(AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{LAT.fromT(U32, t)}, _}, s, x))), d, s, Con{x, cs}) == True{} : Bool}
  MB.and_eq_true(RG.ring(AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x))), d, s, Con{x, cs}), Bool.and(RG.layout(Con{s, Con{x, cs}}, d), Bool.and(RG.bases(Con{s, Con{x, cs}}), RG.faces(Con{s, Con{x, cs}}, AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x))), d, Con{s, Con{x, cs}}))), hr1, MB.and_eq_true(RG.layout(Con{s, Con{x, cs}}, d), Bool.and(RG.bases(Con{s, Con{x, cs}}), RG.faces(Con{s, Con{x, cs}}, AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x))), d, Con{s, Con{x, cs}})), hlayL, MB.and_eq_true(RG.bases(Con{s, Con{x, cs}}), RG.faces(Con{s, Con{x, cs}}, AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x))), d, Con{s, Con{x, cs}}), hbasesL, hF)))

def Laws.insert_ok(w, a, d, s, t, x, hf, hd32, hr, hx):
  insert_ok.m(w, a, d, s, t, x, hf, hd32, hr, hx, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# The cursor made: its two words, then the insert

# a word of a node apart from the members, off their words 1 and 3
def ones_out2(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +z: U32, +hk: {RG.sub(K, M) == True{} : Bool}, +hc: {RG.cross(M, d, z) == True{} : Bool}) ->
    {ones(K, d, (z + 2 : U32)) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((z + 2 : U32), d), AD.slot((m + 1 : U32), d))), ones(r, d, (z + 2 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot((z + 2 : U32), d)), Nat.is_eq(AD.slot((z + 2 : U32), d), AD.slot((m + 1 : U32), d)), MN.is_eq_comm(AD.slot((m + 1 : U32), d), AD.slot((z + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot((z + 2 : U32), d))), RG.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, (z + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot((z + 2 : U32), d))), RG.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, (z + 2 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(m), d, (z + 2 : U32)), RG.off(RG.nw(m), d, (z + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(m), d, (z + 1 : U32)), Bool.and(RG.off(RG.nw(m), d, (z + 2 : U32)), RG.off(RG.nw(m), d, (z + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(m), d, z), Bool.and(RG.off(RG.nw(m), d, (z + 1 : U32)), Bool.and(RG.off(RG.nw(m), d, (z + 2 : U32)), RG.off(RG.nw(m), d, (z + 3 : U32)))), cross_at(M, d, z, m, hc, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hk)))))))), ones_out2(r, M, d, z, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hk), hc))

def links_out2(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +z: U32, +hk: {RG.sub(K, M) == True{} : Bool}, +hc: {RG.cross(M, d, z) == True{} : Bool}) ->
    {RG.off.links(K, d, (z + 2 : U32)) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((z + 2 : U32), d), AD.slot((m + 3 : U32), d))), RG.off.links(r, d, (z + 2 : U32)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot((z + 2 : U32), d)), Nat.is_eq(AD.slot((z + 2 : U32), d), AD.slot((m + 3 : U32), d)), MN.is_eq_comm(AD.slot((m + 3 : U32), d), AD.slot((z + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot((z + 2 : U32), d))), RG.off(Nil{}, d, (z + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot((z + 2 : U32), d))), RG.off(Con{(m + 3 : U32), Nil{}}, d, (z + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot((z + 2 : U32), d))), RG.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, (z + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot((z + 2 : U32), d))), RG.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, (z + 2 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(m), d, (z + 2 : U32)), RG.off(RG.nw(m), d, (z + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(m), d, (z + 1 : U32)), Bool.and(RG.off(RG.nw(m), d, (z + 2 : U32)), RG.off(RG.nw(m), d, (z + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(m), d, z), Bool.and(RG.off(RG.nw(m), d, (z + 1 : U32)), Bool.and(RG.off(RG.nw(m), d, (z + 2 : U32)), RG.off(RG.nw(m), d, (z + 3 : U32)))), cross_at(M, d, z, m, hc, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hk)))))))))), links_out2(r, M, d, z, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hk), hc))

# a write off the members' words 1 and 3 keeps the ring exact with its nodes
def wr_ring(+v: List<&2, U32>, +d: Nat, +s: U32, +cs: List<&2, U32>, +i: U32, +n: U32, +hr: {RG.ring.ok(v, d, s, cs) == True{} : Bool},
    +hl: {RG.off.links(Con{s, cs}, d, i) == True{} : Bool}, +ho: {ones(Con{s, cs}, d, i) == True{} : Bool}) -> {RG.ring.ok(List.set(&2, U32, v, AD.slot(i, d), n), d, s, cs) == True{} : Bool}:
  +hring = MB.eq_true_of_and_left(RG.ring(v, d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, v, d, Con{s, cs}))), hr)
  +hk = MB.eq_true_of_and_right(RG.ring(v, d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, v, d, Con{s, cs}))), hr)
  +hlay = MB.eq_true_of_and_left(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, v, d, Con{s, cs})), hk)
  +hbf = MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, v, d, Con{s, cs})), hk)
  +hb = MB.eq_true_of_and_left(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, v, d, Con{s, cs}), hbf)
  +hfc = MB.eq_true_of_and_right(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, v, d, Con{s, cs}), hbf)
  MB.and_eq_true(RG.ring(List.set(&2, U32, v, AD.slot(i, d), n), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, List.set(&2, U32, v, AD.slot(i, d), n), d, Con{s, cs}))), MB.and_eq_true(RG.chain(List.set(&2, U32, v, AD.slot(i, d), n), d, cs, s, s), RG.apart.all(Con{s, cs}, d), ch_keep(cs, v, d, s, s, i, n, MB.eq_true_of_and_left(RG.chain(v, d, cs, s, s), RG.apart.all(Con{s, cs}, d), hring), hl), MB.eq_true_of_and_right(RG.chain(v, d, cs, s, s), RG.apart.all(Con{s, cs}, d), hring)), MB.and_eq_true(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, List.set(&2, U32, v, AD.slot(i, d), n), d, Con{s, cs})), hlay, MB.and_eq_true(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, List.set(&2, U32, v, AD.slot(i, d), n), d, Con{s, cs}), hb, faces_keep(Con{s, cs}, v, d, Con{s, cs}, i, n, hfc, ho))))

# and keeps x ready to enter it, the write off x's word 1
def wr_enter(+v: List<&2, U32>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32, +i: U32, +n: U32, +hx: {RG.enter.ok(v, d, s, cs, x) == True{} : Bool},
    +ho: {ones(Con{s, cs}, d, i) == True{} : Bool}, +hi: {Nat.is_eq(AD.slot(i, d), AD.slot((x + 1 : U32), d)) == False{} : Bool}) -> {RG.enter.ok(List.set(&2, U32, v, AD.slot(i, d), n), d, s, cs, x) == True{} : Bool}:
  +he0 = MB.eq_true_of_and_left(RG.apartw(RG.nw(x), d), Bool.and(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, v, AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, v, d, Con{x, Nil{}}))))), hx)
  +hx1 = MB.eq_true_of_and_right(RG.apartw(RG.nw(x), d), Bool.and(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, v, AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, v, d, Con{x, Nil{}}))))), hx)
  +he1 = MB.eq_true_of_and_left(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, v, AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, v, d, Con{x, Nil{}})))), hx1)
  +hx2 = MB.eq_true_of_and_right(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, v, AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, v, d, Con{x, Nil{}})))), hx1)
  +he2 = MB.eq_true_of_and_left(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, v, AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, v, d, Con{x, Nil{}}))), hx2)
  +hx3 = MB.eq_true_of_and_right(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, v, AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, v, d, Con{x, Nil{}}))), hx2)
  +he3 = MB.eq_true_of_and_left(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, v, AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, v, d, Con{x, Nil{}})), hx3)
  +hx4 = MB.eq_true_of_and_right(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, v, AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, v, d, Con{x, Nil{}})), hx3)
  +he4 = MB.eq_true_of_and_left(RG.faces.m(List.get(&2, U32, v, AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, v, d, Con{x, Nil{}}), hx4)
  +he5 = MB.eq_true_of_and_right(RG.faces.m(List.get(&2, U32, v, AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, v, d, Con{x, Nil{}}), hx4)
  MB.and_eq_true(RG.apartw(RG.nw(x), d), Bool.and(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, List.set(&2, U32, v, AD.slot(i, d), n), d, Con{x, Nil{}}))))), he0, MB.and_eq_true(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, List.set(&2, U32, v, AD.slot(i, d), n), d, Con{x, Nil{}})))), he1, MB.and_eq_true(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, List.set(&2, U32, v, AD.slot(i, d), n), d, Con{x, Nil{}}))), he2, MB.and_eq_true(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, List.set(&2, U32, v, AD.slot(i, d), n), d, Con{x, Nil{}})), he3, MB.and_eq_true(RG.faces.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, List.set(&2, U32, v, AD.slot(i, d), n), d, Con{x, Nil{}}), fm_keep(v, d, Con{s, Con{x, cs}}, i, n, x, he4, hi), faces_keep(Con{s, cs}, v, d, Con{x, Nil{}}, i, n, he5, ho))))))

def cursor_ok.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32, +src: U32, +neg: Bool,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {RG.ring.ok(AD.view(U32, w), d, s, cs) == True{} : Bool},
  hx: {RG.enter.ok(AD.view(U32, w), d, s, cs, x) == True{} : Bool}, m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.ring.ok(AD.view(U32, RG.words(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg))), d, s, Con{x, cs}) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring.ok(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hxt = LAB.subst(Array<U32>, q => {RG.enter.ok(AD.view(U32, q), d, s, cs, x) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hx)
  +he0 = MB.eq_true_of_and_left(RG.apartw(RG.nw(x), d), Bool.and(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))))), hxt)
  +he2 = MB.eq_true_of_and_left(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))), MB.eq_true_of_and_right(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}})))), MB.eq_true_of_and_right(RG.apartw(RG.nw(x), d), Bool.and(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))))), hxt)))
  +hi0 = Equal.trans(Bool, Nat.is_eq(AD.slot(x, d), AD.slot((x + 1 : U32), d)), Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(x, d)), False{}, MN.is_eq_comm(AD.slot(x, d), AD.slot((x + 1 : U32), d)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(x, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(x, d))), RG.off(Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}, d, x), MB.eq_true_of_and_left(RG.off(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d, x), RG.apartw(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d), he0))))
  +hi2 = MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot((x + 1 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot((x + 1 : U32), d))), RG.off(Con{(x + 3 : U32), Nil{}}, d, (x + 1 : U32)), MB.eq_true_of_and_left(RG.off(Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}, d, (x + 1 : U32)), RG.apartw(Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}, d), MB.eq_true_of_and_right(RG.off(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d, x), RG.apartw(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d), he0))))
  +hl0 = links_out0(Con{s, cs}, Con{s, cs}, d, x, sub_refl(Con{s, cs}), he2)
  +hl2 = links_out2(Con{s, cs}, Con{s, cs}, d, x, sub_refl(Con{s, cs}), he2)
  +ho0 = ones_out0(Con{s, cs}, Con{s, cs}, d, x, sub_refl(Con{s, cs}), he2)
  +ho2 = ones_out2(Con{s, cs}, Con{s, cs}, d, x, sub_refl(Con{s, cs}), he2)
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t), d, x, P.hd2(18, R.cur.form(neg), 0), hft)
  +hf2 = LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), src, hf1)
  +hr2 = wr_ring(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), d, s, cs, (x + 2 : U32), src, wr_ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs, x, P.hd2(18, R.cur.form(neg), 0), hrt, hl0, ho0), hl2, ho2)
  +hx2 = wr_enter(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), d, s, cs, x, (x + 2 : U32), src, wr_enter(AD.view(U32, LAT.fromT(U32, t)), d, s, cs, x, x, P.hd2(18, R.cur.form(neg), 0), hxt, ho0, hi0), ho2, hi2)
  +hr3 = LAB.subst(List<&2, U32>, q => {RG.ring.ok(List.set(&2, U32, q, AD.slot((x + 2 : U32), d), src), d, s, cs) == True{} : Bool}, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), LA.set_view(U32, LAT.fromT(U32, t), d, x, P.hd2(18, R.cur.form(neg), 0), hft, hd32)), hr2)
  +hr4 = LAB.subst(List<&2, U32>, q => {RG.ring.ok(q, d, s, cs) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), AD.slot((x + 2 : U32), d), src), AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), AD.slot((x + 2 : U32), d), src), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), src, hf1, hd32)), hr3)
  +hx3 = LAB.subst(List<&2, U32>, q => {RG.enter.ok(List.set(&2, U32, q, AD.slot((x + 2 : U32), d), src), d, s, cs, x) == True{} : Bool}, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), LA.set_view(U32, LAT.fromT(U32, t), d, x, P.hd2(18, R.cur.form(neg), 0), hft, hd32)), hx2)
  +hx4 = LAB.subst(List<&2, U32>, q => {RG.enter.ok(q, d, s, cs, x) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), AD.slot((x + 2 : U32), d), src), AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), AD.slot((x + 2 : U32), d), src), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), src, hf1, hd32)), hx3)
  %e : {RG.ring.ok(AD.view(U32, RG.words(R.cursor(P.H{KM.MG{_}, a}, s, x, src, neg))), d, s, Con{x, cs}) == True{} : Bool}
  %ea : {RG.ring.ok(AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, _}, s, x, src, neg))), d, s, Con{x, cs}) == True{} : Bool}
  insert_ok.m(Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), LAT.fromT(V.Val, ta), d, s, cs, x, hf2, hd32, hr4, hx4, LAT.mirror(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))

def Laws.cursor_ok(w, a, d, s, t, x, src, neg, hf, hd32, hr, hx):
  cursor_ok.m(w, a, d, s, t, x, src, neg, hf, hd32, hr, hx, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# The cursor made: its words

def cursor_head.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32, +src: U32, +neg: Bool,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hx: {RG.enter.ok(AD.view(U32, w), d, s, cs, x) == True{} : Bool}, m: LAT.Mirror(U32, w)) ->
  {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg)), x)) == P.hd2(18, R.cur.form(neg), 0) : U32}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hxt = LAB.subst(Array<U32>, q => {RG.enter.ok(AD.view(U32, q), d, s, cs, x) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hx)
  +haw = MB.eq_true_of_and_left(RG.apartw(RG.nw(x), d), Bool.and(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))))), hxt)
  +hcr = MB.eq_true_of_and_left(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))), MB.eq_true_of_and_right(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}})))), MB.eq_true_of_and_right(RG.apartw(RG.nw(x), d), Bool.and(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))))), hxt)))
  +hds = MB.eq_true_of_and_left(RG.disj4(d, x, s), RG.cross(cs, d, x), hcr)
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t), d, x, P.hd2(18, R.cur.form(neg), 0), hft)
  +hf2 = LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), src, hf1)
  +hf3 = LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))), hf2)
  +hsj = MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(x, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(x, d))), RG.off(Nil{}, d, x), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((s + 2 : U32), d), AD.slot(x, d))), RG.off(Con{(s + 3 : U32), Nil{}}, d, x), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((s + 1 : U32), d), AD.slot(x, d))), RG.off(Con{(s + 2 : U32), Con{(s + 3 : U32), Nil{}}}, d, x), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(s, d), AD.slot(x, d))), RG.off(Con{(s + 1 : U32), Con{(s + 2 : U32), Con{(s + 3 : U32), Nil{}}}}, d, x), MB.eq_true_of_and_left(RG.off(RG.nw(s), d, x), Bool.and(RG.off(RG.nw(s), d, (x + 1 : U32)), Bool.and(RG.off(RG.nw(s), d, (x + 2 : U32)), RG.off(RG.nw(s), d, (x + 3 : U32)))), hds))))))
  +hxj = MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(x, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(x, d))), RG.off(Nil{}, d, x), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(x, d))), RG.off(Con{(x + 3 : U32), Nil{}}, d, x), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(x, d))), RG.off(Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}, d, x), MB.eq_true_of_and_left(RG.off(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d, x), RG.apartw(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d), haw)))))
  +hxj2 = MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(x, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(x, d))), RG.off(Con{(x + 3 : U32), Nil{}}, d, x), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(x, d))), RG.off(Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}, d, x), MB.eq_true_of_and_left(RG.off(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d, x), RG.apartw(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d), haw))))
  %e : {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.cursor(P.H{KM.MG{_}, a}, s, x, src, neg)), x)) == P.hd2(18, R.cur.form(neg), 0) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)), (Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), LA.get_pair(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))) :
    {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.insert.r(P.rd.fin(KM.m_get.fin(_), a), s, x)), x)) == P.hd2(18, R.cur.form(neg), 0) : U32}
  Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), (s + 3 : U32), x), x)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), x)), P.hd2(18, R.cur.form(neg), 0), LA.get_set_other(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), d, (s + 3 : U32), x, x, hf3, hd32, hsj), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), x)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), x)), P.hd2(18, R.cur.form(neg), 0), LA.get_set_other(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), d, (x + 3 : U32), x, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))), hf2, hd32, hxj), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), x)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), x)), P.hd2(18, R.cur.form(neg), 0), LA.get_set_other(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), x, src, hf1, hd32, hxj2), LA.get_set_same(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)))))

def Laws.cursor_head(w, a, d, s, t, x, src, neg, hf, hd32, hx):
  cursor_head.m(w, a, d, s, t, x, src, neg, hf, hd32, hx, LAT.mirror(U32, w))

def cursor_pos.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32, +src: U32, +neg: Bool,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hx: {RG.enter.ok(AD.view(U32, w), d, s, cs, x) == True{} : Bool}, m: LAT.Mirror(U32, w)) ->
  {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg)), (x + 2 : U32))) == src : U32}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hxt = LAB.subst(Array<U32>, q => {RG.enter.ok(AD.view(U32, q), d, s, cs, x) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hx)
  +haw = MB.eq_true_of_and_left(RG.apartw(RG.nw(x), d), Bool.and(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))))), hxt)
  +hcr = MB.eq_true_of_and_left(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))), MB.eq_true_of_and_right(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}})))), MB.eq_true_of_and_right(RG.apartw(RG.nw(x), d), Bool.and(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))))), hxt)))
  +hds = MB.eq_true_of_and_left(RG.disj4(d, x, s), RG.cross(cs, d, x), hcr)
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t), d, x, P.hd2(18, R.cur.form(neg), 0), hft)
  +hf2 = LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), src, hf1)
  +hf3 = LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))), hf2)
  +hsj = MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((x + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((x + 2 : U32), d))), RG.off(Nil{}, d, (x + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((s + 2 : U32), d), AD.slot((x + 2 : U32), d))), RG.off(Con{(s + 3 : U32), Nil{}}, d, (x + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((s + 1 : U32), d), AD.slot((x + 2 : U32), d))), RG.off(Con{(s + 2 : U32), Con{(s + 3 : U32), Nil{}}}, d, (x + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(s, d), AD.slot((x + 2 : U32), d))), RG.off(Con{(s + 1 : U32), Con{(s + 2 : U32), Con{(s + 3 : U32), Nil{}}}}, d, (x + 2 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(s), d, (x + 2 : U32)), RG.off(RG.nw(s), d, (x + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(s), d, (x + 1 : U32)), Bool.and(RG.off(RG.nw(s), d, (x + 2 : U32)), RG.off(RG.nw(s), d, (x + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(s), d, x), Bool.and(RG.off(RG.nw(s), d, (x + 1 : U32)), Bool.and(RG.off(RG.nw(s), d, (x + 2 : U32)), RG.off(RG.nw(s), d, (x + 3 : U32)))), hds))))))))
  +hxj = MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((x + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((x + 2 : U32), d))), RG.off(Nil{}, d, (x + 2 : U32)), MB.eq_true_of_and_left(RG.off(Con{(x + 3 : U32), Nil{}}, d, (x + 2 : U32)), RG.apartw(Con{(x + 3 : U32), Nil{}}, d), MB.eq_true_of_and_right(RG.off(Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}, d, (x + 1 : U32)), RG.apartw(Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}, d), MB.eq_true_of_and_right(RG.off(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d, x), RG.apartw(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d), haw)))))
  %e : {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.cursor(P.H{KM.MG{_}, a}, s, x, src, neg)), (x + 2 : U32))) == src : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)), (Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), LA.get_pair(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))) :
    {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.insert.r(P.rd.fin(KM.m_get.fin(_), a), s, x)), (x + 2 : U32))) == src : U32}
  Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), (s + 3 : U32), x), (x + 2 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), (x + 2 : U32))), src, LA.get_set_other(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), d, (s + 3 : U32), (x + 2 : U32), x, hf3, hd32, hsj), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), (x + 2 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 2 : U32))), src, LA.get_set_other(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), d, (x + 3 : U32), (x + 2 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))), hf2, hd32, hxj), LA.get_set_same(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)))

def Laws.cursor_pos(w, a, d, s, t, x, src, neg, hf, hd32, hx):
  cursor_pos.m(w, a, d, s, t, x, src, neg, hf, hd32, hx, LAT.mirror(U32, w))

# The find on an exact ring

# A find hands back the heap it walked, an error raised only where its
# fuel ran out (fgo_pair), and on an exact ring finds what RG.first says
# (fwk) before its fuel runs out (fwk_done), each walk followed along the
# chain as the predecessor's is (wk, wk_done)

def fd_stays(+g: Nat, -h: P.H, +n: U32, +p: U32, -found: Maybe<&2, U32>, +s: U32, +far: U32) ->
    {R.rg.find.go(g, R.Rw{h, n, p, found, True{}}, s, far) == R.Rw{h, n, p, found, True{}} : R.Rw}:
  match g:
    case 0n:
      {==}
    case 1n+(+k):
      {==}

def fgo_hit(+t: LAT.Tree<U32>, -a: Array<V.Val>, +g: Nat, +n: U32, +s: U32, +far: U32, +c: Bool,
  ih2: {R.rg.found(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, n, Some{n}, True{}}, s, far)) == (P.err_if(Bool.not(rwd(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, n, Some{n}, True{}}, s, far))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, n, Some{n}, True{}}, s, far)))) : P.H & Maybe<&2, U32>},
  ih3: {R.rg.found(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}}, s, far)) == (P.err_if(Bool.not(rwd(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}}, s, far))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}}, s, far)))) : P.H & Maybe<&2, U32>}) ->
  {R.rg.found(R.rg.find.go(g, R.rw.find.k(c, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n), s, far)) == (P.err_if(Bool.not(rwd(R.rg.find.go(g, R.rw.find.k(c, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n), s, far))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.rw.find.k(c, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n), s, far)))) : P.H & Maybe<&2, U32>}:
  match c:
    case True{}:
      ih2
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (n + 3 : U32))) :
        {R.rg.found(R.rg.find.go(g, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), n), s, far)) == (P.err_if(Bool.not(rwd(R.rg.find.go(g, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), n), s, far))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), n), s, far)))) : P.H & Maybe<&2, U32>}
      ih3

def fgo_step(+t: LAT.Tree<U32>, -a: Array<V.Val>, +g: Nat, +n: U32, +p: U32, +found: Maybe<&2, U32>, +s: U32, +far: U32, +b: Bool, e: {U32.is_eq(n, s) == b : Bool},
  ih1: {R.rg.found(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, n, None{}, True{}}, s, far)) == (P.err_if(Bool.not(rwd(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, n, None{}, True{}}, s, far))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, n, None{}, True{}}, s, far)))) : P.H & Maybe<&2, U32>},
  ih2: {R.rg.found(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, n, Some{n}, True{}}, s, far)) == (P.err_if(Bool.not(rwd(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, n, Some{n}, True{}}, s, far))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, n, Some{n}, True{}}, s, far)))) : P.H & Maybe<&2, U32>},
  ih3: {R.rg.found(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}}, s, far)) == (P.err_if(Bool.not(rwd(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}}, s, far))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}}, s, far)))) : P.H & Maybe<&2, U32>}) ->
  {R.rg.found(R.rg.find.go(1n+g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, False{}}, s, far)) == (P.err_if(Bool.not(rwd(R.rg.find.go(1n+g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, False{}}, s, far))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(1n+g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, False{}}, s, far)))) : P.H & Maybe<&2, U32>}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(n, s), True{}, e) :
        {R.rg.found(R.rg.find.go(g, R.rw.find.s(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, far), s, far)) == (P.err_if(Bool.not(rwd(R.rg.find.go(g, R.rw.find.s(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, far), s, far))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.rw.find.s(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, far), s, far)))) : P.H & Maybe<&2, U32>}
      ih1
    case False{}:
      %Equal.sym(Bool, U32.is_eq(n, s), False{}, e) :
        {R.rg.found(R.rg.find.go(g, R.rw.find.s(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, far), s, far)) == (P.err_if(Bool.not(rwd(R.rg.find.go(g, R.rw.find.s(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, far), s, far))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.rw.find.s(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, far), s, far)))) : P.H & Maybe<&2, U32>}
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (n + 2 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 2 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (n + 2 : U32))) :
        {R.rg.found(R.rg.find.go(g, R.rw.find.p(P.rd.fin(KM.m_get.fin(_), a), n, far), s, far)) == (P.err_if(Bool.not(rwd(R.rg.find.go(g, R.rw.find.p(P.rd.fin(KM.m_get.fin(_), a), n, far), s, far))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.rw.find.p(P.rd.fin(KM.m_get.fin(_), a), n, far), s, far)))) : P.H & Maybe<&2, U32>}
      fgo_hit(t, a, g, n, s, far, U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 2 : U32))), far), ih2, ih3)

def fgo_pair(f: Nat, +t: LAT.Tree<U32>, -a: Array<V.Val>, +n: U32, +p: U32, +found: Maybe<&2, U32>, +done: Bool, +s: U32, +far: U32) ->
  {R.rg.found(R.rg.find.go(f, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, done}, s, far)) == (P.err_if(Bool.not(rwd(R.rg.find.go(f, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, done}, s, far))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(f, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, n, p, found, done}, s, far)))) : P.H & Maybe<&2, U32>}:
  match f:
    case 0n:
      {==}
    case 1n+(+g):
      match done:
        case True{}:
          {==}
        case False{}:
          fgo_step(t, a, g, n, p, found, s, far, U32.is_eq(n, s), {==},
            fgo_pair(g, t, a, n, n, None{}, True{}, s, far),
            fgo_pair(g, t, a, n, n, Some{n}, True{}, s, far),
            fgo_pair(g, t, a, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (n + 3 : U32))), n, None{}, False{}, s, far))

def fwk_hit(+t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +g: Nat, +y: U32, +s: U32, +far: U32, +r: Maybe<&2, U32>, +c: Bool,
  ih: {Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 3 : U32))), y, None{}, False{}}, s, far))) == r : Maybe<&2, U32>}) ->
  {Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.rw.find.k(c, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y), s, far))) == RG.first.k(c, y, r) : Maybe<&2, U32>}:
  match c:
    case True{}:
      %Equal.sym(R.Rw, R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, y, Some{y}, True{}}, s, far), R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, y, Some{y}, True{}}, fd_stays(g, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, y, Some{y}, s, far)) :
        {Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(_)) == Some{y} : Maybe<&2, U32>}
      {==}
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (y + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (y + 3 : U32))) :
        {Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), y), s, far))) == r : Maybe<&2, U32>}
      ih

def fwk(Lst: List<&2, U32>, f: Nat, +t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +p: U32, +s: U32, +far: U32, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hch: {RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, Lst, p, s) == True{} : Bool}, +hnot: {RG.has(Lst, s) == False{} : Bool}, +hfu: {Nat.is_lt(List.length(&2, U32, Lst), f) == True{} : Bool}) ->
    {Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(f, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, None{}, False{}}, s, far))) == RG.first(Lst, AD.view(U32, LAT.fromT(U32, t)), d, far) : Maybe<&2, U32>}:
  match Lst:
    case Nil{}:
      match f:
        case 0n:
          Empty.absurd({Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(0n, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, None{}, False{}}, s, far))) == RG.first(Nil{}, AD.view(U32, LAT.fromT(U32, t)), d, far) : Maybe<&2, U32>}, MB.false_ne_true()(hfu))
        case 1n+(+g):
          +hN = LAB.subst(Maybe<&2, U32>, mm => {RG.link.is.m(mm, s) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (p + 3 : U32), hft, hd32)), hch)
          %Equal.sym(Bool, U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), s), True{}, hN) :
            {Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.rw.find.s(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), far), s, far))) == RG.first(Nil{}, AD.view(U32, LAT.fromT(U32, t)), d, far) : Maybe<&2, U32>}
          %Equal.sym(R.Rw, R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), None{}, True{}}, s, far), R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), None{}, True{}}, fd_stays(g, P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), None{}, s, far)) :
            {Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(_)) == RG.first(Nil{}, AD.view(U32, LAT.fromT(U32, t)), d, far) : Maybe<&2, U32>}
          {==}
    case Con{+y, +r}:
      match f:
        case 0n:
          Empty.absurd({Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(0n, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, None{}, False{}}, s, far))) == RG.first(Con{y, r}, AD.view(U32, LAT.fromT(U32, t)), d, far) : Maybe<&2, U32>}, MB.false_ne_true()(hfu))
        case 1n+(+g):
          +hNy = LAB.subst(Maybe<&2, U32>, mm => {RG.link.is.m(mm, y) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (p + 3 : U32), hft, hd32)), MB.eq_true_of_and_left(RG.link.is(AD.view(U32, LAT.fromT(U32, t)), d, p, y), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, r, y, s), hch))
          +hys = or_false_l(U32.is_eq(y, s), RG.has(r, s), hnot)
          %Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), y, MS.u32_eq_of_is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), y, hNy)) :
            {Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.rw.find.s(U32.is_eq(_, s), P.H{KM.MG{LAT.fromT(U32, t)}, a}, _, far), s, far))) == RG.first(Con{y, r}, AD.view(U32, LAT.fromT(U32, t)), d, far) : Maybe<&2, U32>}
          %Equal.sym(Bool, U32.is_eq(y, s), False{}, hys) :
            {Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.rw.find.s(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, far), s, far))) == RG.first(Con{y, r}, AD.view(U32, LAT.fromT(U32, t)), d, far) : Maybe<&2, U32>}
          %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (y + 2 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 2 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (y + 2 : U32))) :
            {Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.rw.find.p(P.rd.fin(KM.m_get.fin(_), a), y, far), s, far))) == RG.first(Con{y, r}, AD.view(U32, LAT.fromT(U32, t)), d, far) : Maybe<&2, U32>}
          %LA.get_view(U32, LAT.fromT(U32, t), d, (y + 2 : U32), hft, hd32) :
            {Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(g, R.rw.find.k(U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 2 : U32))), far), P.H{KM.MG{LAT.fromT(U32, t)}, a}, y), s, far))) == RG.first.k(RG.pos.is.m(_, far), y, RG.first(r, AD.view(U32, LAT.fromT(U32, t)), d, far)) : Maybe<&2, U32>}
          fwk_hit(t, a, d, g, y, s, far, RG.first(r, AD.view(U32, LAT.fromT(U32, t)), d, far), U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 2 : U32))), far),
            fwk(r, g, t, a, d, y, s, far, hft, hd32, MB.eq_true_of_and_right(RG.link.is(AD.view(U32, LAT.fromT(U32, t)), d, p, y), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, r, y, s), hch), or_false_r(U32.is_eq(y, s), RG.has(r, s), hnot), hfu))

def fwkd_hit(+t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +g: Nat, +y: U32, +s: U32, +far: U32, +r: Maybe<&2, U32>, +c: Bool,
  ih: {rwd(R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 3 : U32))), y, None{}, False{}}, s, far)) == True{} : Bool}) ->
  {rwd(R.rg.find.go(g, R.rw.find.k(c, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y), s, far)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(R.Rw, R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, y, Some{y}, True{}}, s, far), R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, y, Some{y}, True{}}, fd_stays(g, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, y, Some{y}, s, far)) :
        {rwd(_) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (y + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (y + 3 : U32))) :
        {rwd(R.rg.find.go(g, R.rw.on(P.rd.fin(KM.m_get.fin(_), a), y), s, far)) == True{} : Bool}
      ih

def fwk_done(Lst: List<&2, U32>, f: Nat, +t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +p: U32, +s: U32, +far: U32, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hch: {RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, Lst, p, s) == True{} : Bool}, +hnot: {RG.has(Lst, s) == False{} : Bool}, +hfu: {Nat.is_lt(List.length(&2, U32, Lst), f) == True{} : Bool}) ->
    {rwd(R.rg.find.go(f, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, None{}, False{}}, s, far)) == True{} : Bool}:
  match Lst:
    case Nil{}:
      match f:
        case 0n:
          Empty.absurd({rwd(R.rg.find.go(0n, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, None{}, False{}}, s, far)) == True{} : Bool}, MB.false_ne_true()(hfu))
        case 1n+(+g):
          +hN = LAB.subst(Maybe<&2, U32>, mm => {RG.link.is.m(mm, s) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (p + 3 : U32), hft, hd32)), hch)
          %Equal.sym(Bool, U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), s), True{}, hN) :
            {rwd(R.rg.find.go(g, R.rw.find.s(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), far), s, far)) == True{} : Bool}
          %Equal.sym(R.Rw, R.rg.find.go(g, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), None{}, True{}}, s, far), R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), None{}, True{}}, fd_stays(g, P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), None{}, s, far)) :
            {rwd(_) == True{} : Bool}
          {==}
    case Con{+y, +r}:
      match f:
        case 0n:
          Empty.absurd({rwd(R.rg.find.go(0n, R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), p, None{}, False{}}, s, far)) == True{} : Bool}, MB.false_ne_true()(hfu))
        case 1n+(+g):
          +hNy = LAB.subst(Maybe<&2, U32>, mm => {RG.link.is.m(mm, y) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (p + 3 : U32), hft, hd32)), MB.eq_true_of_and_left(RG.link.is(AD.view(U32, LAT.fromT(U32, t)), d, p, y), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, r, y, s), hch))
          +hys = or_false_l(U32.is_eq(y, s), RG.has(r, s), hnot)
          %Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), y, MS.u32_eq_of_is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (p + 3 : U32))), y, hNy)) :
            {rwd(R.rg.find.go(g, R.rw.find.s(U32.is_eq(_, s), P.H{KM.MG{LAT.fromT(U32, t)}, a}, _, far), s, far)) == True{} : Bool}
          %Equal.sym(Bool, U32.is_eq(y, s), False{}, hys) :
            {rwd(R.rg.find.go(g, R.rw.find.s(_, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, far), s, far)) == True{} : Bool}
          %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (y + 2 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 2 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (y + 2 : U32))) :
            {rwd(R.rg.find.go(g, R.rw.find.p(P.rd.fin(KM.m_get.fin(_), a), y, far), s, far)) == True{} : Bool}
          %LA.get_view(U32, LAT.fromT(U32, t), d, (y + 2 : U32), hft, hd32) :
            {rwd(R.rg.find.go(g, R.rw.find.k(U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 2 : U32))), far), P.H{KM.MG{LAT.fromT(U32, t)}, a}, y), s, far)) == True{} : Bool}
          fwkd_hit(t, a, d, g, y, s, far, RG.first(r, AD.view(U32, LAT.fromT(U32, t)), d, far), U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 2 : U32))), far),
            fwk_done(r, g, t, a, d, y, s, far, hft, hd32, MB.eq_true_of_and_right(RG.link.is(AD.view(U32, LAT.fromT(U32, t)), d, p, y), RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, r, y, s), hch), or_false_r(U32.is_eq(y, s), RG.has(r, s), hnot), hfu))

def find_exact.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +far: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {RG.ring(AD.view(U32, w), d, s, cs) == True{} : Bool}, m: LAT.Mirror(U32, w)) ->
  {R.rg.find(P.H{KM.MG{w}, a}, s, far) == (P.H{KM.MG{w}, a}, RG.first(cs, AD.view(U32, w), d, far)) : P.H & Maybe<&2, U32>}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hch = MB.eq_true_of_and_left(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hrt)
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hrt)
  +hnot = apart_notin(cs, d, s, MB.eq_true_of_and_left(RG.apart(cs, d, s), RG.apart.all(cs, d), hap))
  +hfu = len_ok(t, d, s, cs, hft, hd32, hap)
  +hfound = fwk(cs, U32.to_nat(U32.shln(1, d)), t, a, d, s, s, far, hft, hd32, hch, hnot, hfu)
  +hdone = fwk_done(cs, U32.to_nat(U32.shln(1, d)), t, a, d, s, s, far, hft, hd32, hch, hnot, hfu)
  %e : {R.rg.find(P.H{KM.MG{_}, a}, s, far) == (P.H{KM.MG{_}, a}, RG.first(cs, AD.view(U32, _), d, far)) : P.H & Maybe<&2, U32>}
  %Equal.sym(Array<U32> & U32, Array.size(U32, LAT.fromT(U32, t)), (LAT.fromT(U32, t), U32.shln(1, d)), LA.size_pair(U32, LAT.fromT(U32, t), d, hft)) :
    {R.rg.find.f(R.rg.fuel.s(_, a), s, far) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far)) : P.H & Maybe<&2, U32>}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (s + 3 : U32))) :
    {R.rg.found(R.rg.find.go(U32.to_nat(U32.shln(1, d)), R.rw.on(P.rd.fin(KM.m_get.fin(_), a), s), s, far)) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far)) : P.H & Maybe<&2, U32>}
  %Equal.sym(P.H & Maybe<&2, U32>, R.rg.found(R.rg.find.go(U32.to_nat(U32.shln(1, d)), R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), s, None{}, False{}}, s, far)), (P.err_if(Bool.not(rwd(R.rg.find.go(U32.to_nat(U32.shln(1, d)), R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), s, None{}, False{}}, s, far))), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(U32.to_nat(U32.shln(1, d)), R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), s, None{}, False{}}, s, far)))), fgo_pair(U32.to_nat(U32.shln(1, d)), t, a, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), s, None{}, False{}, s, far)) :
    {_ == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far)) : P.H & Maybe<&2, U32>}
  %Equal.sym(Bool, rwd(R.rg.find.go(U32.to_nat(U32.shln(1, d)), R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), s, None{}, False{}}, s, far)), True{}, hdone) :
    {(P.err_if(Bool.not(_), P.H{KM.MG{LAT.fromT(U32, t)}, a}), Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(U32.to_nat(U32.shln(1, d)), R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), s, None{}, False{}}, s, far)))) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far)) : P.H & Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, Pair.snd(P.H, Maybe<&2, U32>, R.rg.found(R.rg.find.go(U32.to_nat(U32.shln(1, d)), R.Rw{P.H{KM.MG{LAT.fromT(U32, t)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), s, None{}, False{}}, s, far))), RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far), hfound) :
    {(P.H{KM.MG{LAT.fromT(U32, t)}, a}, _) == (P.H{KM.MG{LAT.fromT(U32, t)}, a}, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far)) : P.H & Maybe<&2, U32>}
  {==}

def Laws.find_exact(w, a, d, s, t, far, hf, hd32, hr):
  find_exact.m(w, a, d, s, t, far, hf, hd32, hr, LAT.mirror(U32, w))

# The pending placeholders: lists and layouts

# U32.is_eq turned round
def ueq_comm(+a: U32, +b: U32) -> {U32.is_eq(a, b) == U32.is_eq(b, a) : Bool}:
  Equal.trans(Bool, U32.is_eq(a, b), Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), U32.is_eq(b, a), MU.u32_is_eq_to_nat(a, b),
    Equal.trans(Bool, Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), Nat.is_eq(U32.to_nat(b), U32.to_nat(a)), U32.is_eq(b, a), MN.is_eq_comm(U32.to_nat(a), U32.to_nat(b)),
      Equal.sym(Bool, U32.is_eq(b, a), Nat.is_eq(U32.to_nat(b), U32.to_nat(a)), MU.u32_is_eq_to_nat(b, a))))

def ueq_ne(+a: U32, +b: U32, +h: {U32.is_eq(a, b) == False{} : Bool}) -> {U32.is_eq(b, a) == False{} : Bool}:
  Equal.trans(Bool, U32.is_eq(b, a), U32.is_eq(a, b), False{}, ueq_comm(b, a), h)

# a node of M outside K apart from each of K's nodes, M laid out
def cross_of(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +a: U32, +hs: {RG.sub(K, M) == True{} : Bool}, +hl: {RG.layout(M, d) == True{} : Bool},
    +ha: {RG.has(M, a) == True{} : Bool}, +hn: {RG.has(K, a) == False{} : Bool}) -> {RG.cross(K, d, a) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+b, +r}:
      MB.and_eq_true(RG.disj4(d, a, b), RG.cross(r, d, a), lay_pair(M, d, a, b, hl, ha, MB.eq_true_of_and_left(RG.has(M, b), RG.sub(r, M), hs), ueq_ne(b, a, or_false_l(U32.is_eq(b, a), RG.has(r, a), hn))), cross_of(r, M, d, a, MB.eq_true_of_and_right(RG.has(M, b), RG.sub(r, M), hs), hl, ha, or_false_r(U32.is_eq(b, a), RG.has(r, a), hn)))

# a part of a laid-out list, its nodes listed once, laid out
def lay_sub(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +hs: {RG.sub(K, M) == True{} : Bool}, +hl: {RG.layout(M, d) == True{} : Bool},
    +hap: {RG.apart.all(K, d) == True{} : Bool}) -> {RG.layout(K, d) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+a, +r}:
      +ha = MB.eq_true_of_and_left(RG.has(M, a), RG.sub(r, M), hs)
      +hsr = MB.eq_true_of_and_right(RG.has(M, a), RG.sub(r, M), hs)
      +hna = apart_notin(r, d, a, MB.eq_true_of_and_left(RG.apart(r, d, a), RG.apart.all(r, d), hap))
      MB.and_eq_true(RG.apartw(RG.nw(a), d), Bool.and(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(r, d, a), RG.layout(r, d))), lay_self(M, d, a, hl, ha), MB.and_eq_true(RG.off(RG.nw(a), d, P.at_fh()), Bool.and(RG.cross(r, d, a), RG.layout(r, d)), lay_head(M, d, a, hl, ha), MB.and_eq_true(RG.cross(r, d, a), RG.layout(r, d), cross_of(r, M, d, a, hsr, hl, ha, hna), lay_sub(r, M, d, hsr, hl, MB.eq_true_of_and_right(RG.apart(r, d, a), RG.apart.all(r, d), hap)))))

def o0_step(+m: U32, +p: U32, +d: Nat, +M: List<&2, U32>, +b: Bool, e: {U32.is_eq(m, p) == b : Bool},
    +h: {RG.layout(M, d) == True{} : Bool}, +hm: {RG.has(M, m) == True{} : Bool}, +hp: {RG.has(M, p) == True{} : Bool}) -> {Bool.not(Nat.is_eq(AD.slot(p, d), AD.slot((m + 1 : U32), d))) == True{} : Bool}:
  match b:
    case True{}:
      ME.subst(U32, q => {Bool.not(Nat.is_eq(AD.slot(p, d), AD.slot((q + 1 : U32), d))) == True{} : Bool}, p, m, Equal.sym(U32, m, p, MS.u32_eq_of_is_eq(m, p, e)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((p + 1 : U32), d), AD.slot(p, d)), Nat.is_eq(AD.slot(p, d), AD.slot((p + 1 : U32), d)), MN.is_eq_comm(AD.slot((p + 1 : U32), d), AD.slot(p, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((p + 1 : U32), d), AD.slot(p, d))), RG.off(Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}, d, p), MB.eq_true_of_and_left(RG.off(Con{(p + 1 : U32), Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}}, d, p), RG.apartw(Con{(p + 1 : U32), Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}}, d), lay_self(M, d, p, h, hp)))))
    case False{}:
      MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(p, d), AD.slot((m + 1 : U32), d))), RG.off(Con{(p + 1 : U32), Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}}, d, (m + 1 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(p), d, (m + 1 : U32)), Bool.and(RG.off(RG.nw(p), d, (m + 2 : U32)), RG.off(RG.nw(p), d, (m + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(p), d, m), Bool.and(RG.off(RG.nw(p), d, (m + 1 : U32)), Bool.and(RG.off(RG.nw(p), d, (m + 2 : U32)), RG.off(RG.nw(p), d, (m + 3 : U32)))), lay_pair(M, d, m, p, h, hm, hp, e))))

def ones_p0(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +p: U32, +hk: {RG.sub(K, M) == True{} : Bool}, +h: {RG.layout(M, d) == True{} : Bool}, +hp: {RG.has(M, p) == True{} : Bool}) ->
    {ones(K, d, p) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(p, d), AD.slot((m + 1 : U32), d))), ones(r, d, p), o0_step(m, p, d, M, U32.is_eq(m, p), {==}, h, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hk), hp), ones_p0(r, M, d, p, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hk), h, hp))

def o2_step(+m: U32, +p: U32, +d: Nat, +M: List<&2, U32>, +b: Bool, e: {U32.is_eq(m, p) == b : Bool},
    +h: {RG.layout(M, d) == True{} : Bool}, +hm: {RG.has(M, m) == True{} : Bool}, +hp: {RG.has(M, p) == True{} : Bool}) -> {Bool.not(Nat.is_eq(AD.slot((p + 2 : U32), d), AD.slot((m + 1 : U32), d))) == True{} : Bool}:
  match b:
    case True{}:
      ME.subst(U32, q => {Bool.not(Nat.is_eq(AD.slot((p + 2 : U32), d), AD.slot((q + 1 : U32), d))) == True{} : Bool}, p, m, Equal.sym(U32, m, p, MS.u32_eq_of_is_eq(m, p, e)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((p + 2 : U32), d), AD.slot((p + 1 : U32), d))), RG.off(Con{(p + 3 : U32), Nil{}}, d, (p + 1 : U32)), MB.eq_true_of_and_left(RG.off(Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}, d, (p + 1 : U32)), RG.apartw(Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}, d), MB.eq_true_of_and_right(RG.off(Con{(p + 1 : U32), Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}}, d, p), RG.apartw(Con{(p + 1 : U32), Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}}, d), lay_self(M, d, p, h, hp)))))
    case False{}:
      MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((p + 2 : U32), d), AD.slot((m + 1 : U32), d))), RG.off(Con{(p + 3 : U32), Nil{}}, d, (m + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((p + 1 : U32), d), AD.slot((m + 1 : U32), d))), RG.off(Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}, d, (m + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(p, d), AD.slot((m + 1 : U32), d))), RG.off(Con{(p + 1 : U32), Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}}, d, (m + 1 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(p), d, (m + 1 : U32)), Bool.and(RG.off(RG.nw(p), d, (m + 2 : U32)), RG.off(RG.nw(p), d, (m + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(p), d, m), Bool.and(RG.off(RG.nw(p), d, (m + 1 : U32)), Bool.and(RG.off(RG.nw(p), d, (m + 2 : U32)), RG.off(RG.nw(p), d, (m + 3 : U32)))), lay_pair(M, d, m, p, h, hm, hp, e))))))

def ones_p2(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +p: U32, +hk: {RG.sub(K, M) == True{} : Bool}, +h: {RG.layout(M, d) == True{} : Bool}, +hp: {RG.has(M, p) == True{} : Bool}) ->
    {ones(K, d, (p + 2 : U32)) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((p + 2 : U32), d), AD.slot((m + 1 : U32), d))), ones(r, d, (p + 2 : U32)), o2_step(m, p, d, M, U32.is_eq(m, p), {==}, h, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hk), hp), ones_p2(r, M, d, p, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hk), h, hp))

# the pending none of a list's: one listed there none of them, a part
# of it, and a node none of them added
def none_has(ps: List<&2, U32>, +M: List<&2, U32>, +y: U32, +hn: {RG.none.in(ps, M) == True{} : Bool}, +hy: {RG.has(M, y) == True{} : Bool}) -> {RG.has(ps, y) == False{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +r}:
      or_ff(U32.is_eq(q, y), RG.has(r, y), ne_go(M, q, y, U32.is_eq(q, y), {==}, MB.eq_false_of_not_eq_true(RG.has(M, q), MB.eq_true_of_and_left(Bool.not(RG.has(M, q)), RG.none.in(r, M), hn)), hy),
        none_has(r, M, y, MB.eq_true_of_and_right(Bool.not(RG.has(M, q)), RG.none.in(r, M), hn), hy))

def none_sub(ps: List<&2, U32>, +M: List<&2, U32>, +N: List<&2, U32>, +hn: {RG.none.in(ps, M) == True{} : Bool}, +hs: {RG.sub(N, M) == True{} : Bool}) -> {RG.none.in(ps, N) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +r}:
      MB.and_eq_true(Bool.not(RG.has(N, q)), RG.none.in(r, N), not_t(RG.has(N, q), notin_sub(N, M, q, hs, MB.eq_false_of_not_eq_true(RG.has(M, q), MB.eq_true_of_and_left(Bool.not(RG.has(M, q)), RG.none.in(r, M), hn)))), none_sub(r, M, N, MB.eq_true_of_and_right(Bool.not(RG.has(M, q)), RG.none.in(r, M), hn), hs))

def none_ins(ps: List<&2, U32>, +s: U32, +cs: List<&2, U32>, +x: U32, +hn: {RG.none.in(ps, Con{s, cs}) == True{} : Bool}, +hx: {RG.has(ps, x) == False{} : Bool}) ->
    {RG.none.in(ps, Con{s, Con{x, cs}}) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +r}:
      +hq = MB.eq_false_of_not_eq_true(RG.has(Con{s, cs}, q), MB.eq_true_of_and_left(Bool.not(RG.has(Con{s, cs}, q)), RG.none.in(r, Con{s, cs}), hn))
      MB.and_eq_true(Bool.not(RG.has(Con{s, Con{x, cs}}, q)), RG.none.in(r, Con{s, Con{x, cs}}), not_t(RG.has(Con{s, Con{x, cs}}, q), or_ff(U32.is_eq(s, q), RG.has(Con{x, cs}, q), or_false_l(U32.is_eq(s, q), RG.has(cs, q), hq), or_ff(U32.is_eq(x, q), RG.has(cs, q), ueq_ne(q, x, or_false_l(U32.is_eq(q, x), RG.has(r, x), hx)), or_false_r(U32.is_eq(s, q), RG.has(cs, q), hq)))), none_ins(r, s, cs, x, MB.eq_true_of_and_right(Bool.not(RG.has(Con{s, cs}, q)), RG.none.in(r, Con{s, cs}), hn), or_false_r(U32.is_eq(q, x), RG.has(r, x), hx)))

# a part of L with neither x nor y a part of L without both
def sub_w2(K: List<&2, U32>, +L: List<&2, U32>, +x: U32, +y: U32, +hs: {RG.sub(K, L) == True{} : Bool}, +hx: {RG.has(K, x) == False{} : Bool}, +hy: {RG.has(K, y) == False{} : Bool}) ->
    {RG.sub(K, RG.without(RG.without(L, x), y)) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(RG.has(RG.without(RG.without(L, x), y), m), RG.sub(r, RG.without(RG.without(L, x), y)), has_without(RG.without(L, x), y, m, ueq_ne(m, y, or_false_l(U32.is_eq(m, y), RG.has(r, y), hy)), has_without(L, x, m, ueq_ne(m, x, or_false_l(U32.is_eq(m, x), RG.has(r, x), hx)), MB.eq_true_of_and_left(RG.has(L, m), RG.sub(r, L), hs))), sub_w2(r, L, x, y, MB.eq_true_of_and_right(RG.has(L, m), RG.sub(r, L), hs), or_false_r(U32.is_eq(m, x), RG.has(r, x), hx), or_false_r(U32.is_eq(m, y), RG.has(r, y), hy)))

# The pending placeholders: the steps

# the faces of L kept through an insert after the cursor's own two writes
def cur_faces(-w2: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +L: List<&2, U32>, hf2: {AD.full(U32, w2, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    hF: {RG.faces(L, AD.view(U32, w2), d, L) == True{} : Bool}, m2: LAT.Mirror(U32, w2), +hox: {ones(L, d, (x + 3 : U32)) == True{} : Bool}, +hos: {ones(L, d, (s + 3 : U32)) == True{} : Bool}) ->
    {RG.faces(L, AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{w2}, a}, s, x))), d, L) == True{} : Bool}:
  (+t2, +e2) = m2
  +hft2 = LAP.full_t(U32, w2, t2, d, e2, hf2)
  +hFt = LAB.subst(Array<U32>, q => {RG.faces(L, AD.view(U32, q), d, L) == True{} : Bool}, w2, LAT.fromT(U32, t2), Equal.sym(Array<U32>, LAT.fromT(U32, t2), w2, e2), hF)
  %e2 : {RG.faces(L, AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{_}, a}, s, x))), d, L) == True{} : Bool}
  ins_faces(t2, a, d, s, x, L, L, hft2, hd32, hFt, hox, hos)

# a placeholder made a cursor: the invariant kept, the ring's part by
# cursor_ok on what the invariant gives, the faces of all of L through
# the cursor's four writes
def cursor_pend.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +ps: List<&2, U32>, +L: List<&2, U32>, +x: U32, +src: U32, +neg: Bool,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hp: {RG.pend.ok(AD.view(U32, w), d, s, cs, Con{x, ps}, L) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.pend.ok(AD.view(U32, RG.words(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg))), d, s, Con{x, cs}, ps, L) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hpt = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, q), d, s, cs, Con{x, ps}, L) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hp)
  +hp0 = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt)
  +hpr0 = MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt)
  +hp1 = MB.eq_true_of_and_left(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))))), hpr0)
  +hpr1 = MB.eq_true_of_and_right(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))))), hpr0)
  +hp2 = MB.eq_true_of_and_left(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))), hpr1)
  +hpr2 = MB.eq_true_of_and_right(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))), hpr1)
  +hp3 = MB.eq_true_of_and_left(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))), hpr2)
  +hpr3 = MB.eq_true_of_and_right(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))), hpr2)
  +hp4 = MB.eq_true_of_and_left(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))), hpr3)
  +hpr4 = MB.eq_true_of_and_right(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))), hpr3)
  +hp5 = MB.eq_true_of_and_left(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)), hpr4)
  +hpr5 = MB.eq_true_of_and_right(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)), hpr4)
  +hp6 = MB.eq_true_of_and_left(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L), hpr5)
  +hp7 = MB.eq_true_of_and_right(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L), hpr5)
  +hsL = MB.eq_true_of_and_left(RG.has(L, s), RG.sub(cs, L), hp1)
  +hcsL = MB.eq_true_of_and_right(RG.has(L, s), RG.sub(cs, L), hp1)
  +hxL = MB.eq_true_of_and_left(RG.has(L, x), RG.sub(ps, L), hp2)
  +hpsL = MB.eq_true_of_and_right(RG.has(L, x), RG.sub(ps, L), hp2)
  +hxout = MB.eq_false_of_not_eq_true(RG.has(Con{s, cs}, x), MB.eq_true_of_and_left(Bool.not(RG.has(Con{s, cs}, x)), RG.none.in(ps, Con{s, cs}), hp3))
  +hpsout = MB.eq_true_of_and_right(Bool.not(RG.has(Con{s, cs}, x)), RG.none.in(ps, Con{s, cs}), hp3)
  +hxps = MB.eq_false_of_not_eq_true(RG.has(ps, x), MB.eq_true_of_and_left(Bool.not(RG.has(ps, x)), RG.distinct(ps), hp4))
  +hdps = MB.eq_true_of_and_right(Bool.not(RG.has(ps, x)), RG.distinct(ps), hp4)
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hp0)
  +hsubx = MB.and_eq_true(RG.has(L, s), RG.sub(Con{x, cs}, L), hsL, MB.and_eq_true(RG.has(L, x), RG.sub(cs, L), hxL, hcsL))
  +hr0 = MB.and_eq_true(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hp0, MB.and_eq_true(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), lay_sub(Con{s, cs}, L, d, hp1, hp5, hap), MB.and_eq_true(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), bases_sub(Con{s, cs}, L, hp1, hp6), faces_sub(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, L, Con{s, cs}, hp1, hp1, hp7))))
  +hx0 = MB.and_eq_true(RG.apartw(RG.nw(x), d), Bool.and(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))))), lay_self(L, d, x, hp5, hxL), MB.and_eq_true(RG.off(RG.nw(x), d, P.at_fh()), Bool.and(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}})))), lay_head(L, d, x, hp5, hxL), MB.and_eq_true(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}))), cross_of(Con{s, cs}, L, d, x, hp1, hp5, hxL, hxout), MB.and_eq_true(U32.is_eq(P.base(x), x), Bool.and(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}})), bases_at(L, x, hp6, hxL), MB.and_eq_true(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, cs}}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{x, Nil{}}), fm_sub(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, L, Con{s, Con{x, cs}}, hsubx, faces_at(L, AD.view(U32, LAT.fromT(U32, t)), d, L, x, hp7, hxL)), faces_sub(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, L, Con{x, Nil{}}, hp1, MB.and_eq_true(RG.has(L, x), RG.sub(Nil{}, L), hxL, {==}), hp7))))))
  +hrok = cursor_ok.m(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, x, src, neg, hft, hd32, hr0, hx0, LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hringP = MB.eq_true_of_and_left(RG.ring(AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), d, s, Con{x, cs}), Bool.and(RG.layout(Con{s, Con{x, cs}}, d), Bool.and(RG.bases(Con{s, Con{x, cs}}), RG.faces(Con{s, Con{x, cs}}, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), d, Con{s, Con{x, cs}}))), hrok)
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t), d, x, P.hd2(18, R.cur.form(neg), 0), hft)
  +hf2 = LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), src, hf1)
  +hF2 = faces_keep(L, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), d, L, (x + 2 : U32), src, faces_keep(L, AD.view(U32, LAT.fromT(U32, t)), d, L, x, P.hd2(18, R.cur.form(neg), 0), hp7, ones_p0(L, L, d, x, sub_refl(L), hp5, hxL)), ones_p2(L, L, d, x, sub_refl(L), hp5, hxL))
  +hF3 = LAB.subst(List<&2, U32>, q => {RG.faces(L, List.set(&2, U32, q, AD.slot((x + 2 : U32), d), src), d, L) == True{} : Bool}, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), LA.set_view(U32, LAT.fromT(U32, t), d, x, P.hd2(18, R.cur.form(neg), 0), hft, hd32)), hF2)
  +hF4 = LAB.subst(List<&2, U32>, q => {RG.faces(L, q, d, L) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), AD.slot((x + 2 : U32), d), src), AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), AD.slot((x + 2 : U32), d), src), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), src, hf1, hd32)), hF3)
  +hFP = cur_faces(Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), LAT.fromT(V.Val, ta), d, s, x, L, hf2, hd32, hF4, LAT.mirror(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), ones_p3(L, L, d, x, sub_refl(L), hp5, hxL), ones_p3(L, L, d, s, sub_refl(L), hp5, hsL))
  %e : {RG.pend.ok(AD.view(U32, RG.words(R.cursor(P.H{KM.MG{_}, a}, s, x, src, neg))), d, s, Con{x, cs}, ps, L) == True{} : Bool}
  %ea : {RG.pend.ok(AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, _}, s, x, src, neg))), d, s, Con{x, cs}, ps, L) == True{} : Bool}
  MB.and_eq_true(RG.ring(AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), d, s, Con{x, cs}), Bool.and(RG.sub(Con{s, Con{x, cs}}, L), Bool.and(RG.sub(ps, L), Bool.and(RG.none.in(ps, Con{s, Con{x, cs}}), Bool.and(RG.distinct(ps), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), d, L))))))), hringP, MB.and_eq_true(RG.sub(Con{s, Con{x, cs}}, L), Bool.and(RG.sub(ps, L), Bool.and(RG.none.in(ps, Con{s, Con{x, cs}}), Bool.and(RG.distinct(ps), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), d, L)))))), hsubx, MB.and_eq_true(RG.sub(ps, L), Bool.and(RG.none.in(ps, Con{s, Con{x, cs}}), Bool.and(RG.distinct(ps), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), d, L))))), hpsL, MB.and_eq_true(RG.none.in(ps, Con{s, Con{x, cs}}), Bool.and(RG.distinct(ps), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), d, L)))), none_ins(ps, s, cs, x, hpsout, hxps), MB.and_eq_true(RG.distinct(ps), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), d, L))), hdps, MB.and_eq_true(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), d, L)), hp5, MB.and_eq_true(RG.bases(L), RG.faces(L, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), d, L), hp6, hFP)))))))

def Laws.cursor_pend(w, a, d, s, t, ps, L, x, src, neg, hf, hd32, hp):
  cursor_pend.m(w, a, d, s, t, ps, L, x, src, neg, hf, hd32, hp, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# The pending placeholders: a join

# a placeholder joined to a cursor: the invariant kept, the ring's part
# by join1_exact on what the invariant gives, the faces of all of L but
# the two through join1_faces.go over that list, with join1_exact.m's own
# derivations of its premises
def join1_pend.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +ps: List<&2, U32>, +L: List<&2, U32>, +x: U32, +m0: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hp: {RG.pend.ok(AD.view(U32, w), d, s, cs, Con{x, ps}, L) == True{} : Bool},
  +hm: {RG.has(cs, m0) == True{} : Bool}, m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.pend.ok(AD.view(U32, RG.words(R.join1(P.H{KM.MG{w}, a}, x, m0))), d, s, RG.without(cs, m0), ps, RG.without(RG.without(L, x), m0)) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hpt = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, q), d, s, cs, Con{x, ps}, L) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hp)
  +hp0 = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt)
  +hpr0 = MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt)
  +hp1 = MB.eq_true_of_and_left(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))))), hpr0)
  +hpr1 = MB.eq_true_of_and_right(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))))), hpr0)
  +hp2 = MB.eq_true_of_and_left(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))), hpr1)
  +hpr2 = MB.eq_true_of_and_right(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))), hpr1)
  +hp3 = MB.eq_true_of_and_left(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))), hpr2)
  +hpr3 = MB.eq_true_of_and_right(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))), hpr2)
  +hp4 = MB.eq_true_of_and_left(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))), hpr3)
  +hpr4 = MB.eq_true_of_and_right(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))), hpr3)
  +hp5 = MB.eq_true_of_and_left(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)), hpr4)
  +hpr5 = MB.eq_true_of_and_right(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)), hpr4)
  +hp6 = MB.eq_true_of_and_left(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L), hpr5)
  +hp7 = MB.eq_true_of_and_right(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L), hpr5)
  +hxL = MB.eq_true_of_and_left(RG.has(L, x), RG.sub(ps, L), hp2)
  +hpsL = MB.eq_true_of_and_right(RG.has(L, x), RG.sub(ps, L), hp2)
  +hxout = MB.eq_false_of_not_eq_true(RG.has(Con{s, cs}, x), MB.eq_true_of_and_left(Bool.not(RG.has(Con{s, cs}, x)), RG.none.in(ps, Con{s, cs}), hp3))
  +hpsout = MB.eq_true_of_and_right(Bool.not(RG.has(Con{s, cs}, x)), RG.none.in(ps, Con{s, cs}), hp3)
  +hxps = MB.eq_false_of_not_eq_true(RG.has(ps, x), MB.eq_true_of_and_left(Bool.not(RG.has(ps, x)), RG.distinct(ps), hp4))
  +hdps = MB.eq_true_of_and_right(Bool.not(RG.has(ps, x)), RG.distinct(ps), hp4)
  +hap0 = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hp0)
  +hm0L = sub_has(Con{s, cs}, L, m0, hp1, has_cons(s, cs, m0, hm))
  +hsLW = sub_trans(RG.without(RG.without(L, x), m0), RG.without(L, x), L, sub_without(RG.without(L, x), m0), sub_without(L, x))
  +hxLW = notin_sub(RG.without(RG.without(L, x), m0), RG.without(L, x), x, sub_without(RG.without(L, x), m0), notin_without(L, x))
  +hmLW = notin_without(RG.without(L, x), m0)
  +hr0 = MB.and_eq_true(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hp0, MB.and_eq_true(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), lay_sub(Con{s, cs}, L, d, hp1, hp5, hap0), MB.and_eq_true(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), bases_sub(Con{s, cs}, L, hp1, hp6), faces_sub(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, L, Con{s, cs}, hp1, hp1, hp7))))
  +hx0 = MB.and_eq_true(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs})), cross_of(Con{s, cs}, L, d, x, hp1, hp5, hxL, hxout), MB.and_eq_true(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs}), bases_at(L, x, hp6, hxL), fm_sub(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, L, Con{s, cs}, hp1, faces_at(L, AD.view(U32, LAT.fromT(U32, t)), d, L, x, hp7, hxL))))
  +hrt = hr0
  +hxt = hx0
  +hring = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)
  +hlay = MB.eq_true_of_and_left(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt))
  +hbases = MB.eq_true_of_and_left(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hfaces = MB.eq_true_of_and_right(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hring)
  +hn = len_ok(t, d, s, cs, hft, hd32, hap)
  +eqW = without_eq(d, s, cs, m0, hap, hm)
  +subr = MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(RG.without(cs, m0), Con{s, cs}), has_self(s, cs), sub_cons_r(RG.without(cs, m0), s, cs, sub_without(cs, m0)))
  +hbm = MS.u32_eq_of_is_eq(P.base(m0), m0, bases_at(Con{s, cs}, m0, hbases, has_cons(s, cs, m0, hm)))
  +hrs = ring_split(AD.view(U32, LAT.fromT(U32, t)), d, s, cs, m0, hring, hm)
  +hnm = ME.subst(List<&2, U32>, q => {Nat.is_lt(List.length(&2, U32, q), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), cs, split_of_has(cs, m0, hm)), hn)
  +hwt = LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, Con{s, cs}) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m0 + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m0 + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (m0 + 1 : U32), hft, hd32)), faces_at(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}, m0, hfaces, has_cons(s, cs, m0, hm)))
  +hws = ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), cs, split_of_has(cs, m0, hm)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) + 1 : U32)), hwt))
  +hns = apart_notin(cs, d, s, MB.eq_true_of_and_left(RG.apart(cs, d, s), RG.apart.all(cs, d), hap))
  +nm = or_ff(U32.is_eq(s, m0), RG.has(RG.without(cs, m0), m0), ne_go(cs, s, m0, U32.is_eq(s, m0), {==}, hns, hm), notin_without(cs, m0))
  +om = ones_p3(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, RG.last(lpre(cs, m0), s), subr, hlay,
    sub_has(Con{s, lpre(cs, m0)}, Con{s, cs}, RG.last(lpre(cs, m0), s), MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(lpre(cs, m0), Con{s, cs}), has_self(s, cs), sub_cons_r(lpre(cs, m0), s, cs, sub_lpre(cs, m0))), last_mem(lpre(cs, m0), s)))
  +hcx = MB.eq_true_of_and_left(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs})), hxt)
  +hbx = MS.u32_eq_of_is_eq(P.base(x), x, MB.eq_true_of_and_left(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs})), hxt)))
  +hut = LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, Con{s, cs}) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))},
    Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (x + 1 : U32), hft, hd32)), MB.eq_true_of_and_right(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs})), hxt)))
  +hrok = join1_exact.m(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, x, m0, hft, hd32, hr0, hx0, hm, LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +fjL = join1_faces.go(LAT.fromT(U32, t),
    LAT.fromT(V.Val, ta),
    d,
    s,
    lpre(cs, m0),
    x,
    m0,
    lpost(cs, m0),
    hft,
    hd32,
    hrs,
    hnm,
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), cs, split_of_has(cs, m0, hm)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), hut)),
    hws,
    RG.without(RG.without(L, x), m0),
    RG.without(RG.without(L, x), m0),
    faces_sub(RG.without(RG.without(L, x), m0), AD.view(U32, LAT.fromT(U32, t)), d, L, RG.without(RG.without(L, x), m0), hsLW, hsLW, hp7),
    port_sub(RG.without(RG.without(L, x), m0), L, d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), hsLW, LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, L) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (x + 1 : U32), hft, hd32)), faces_at(L, AD.view(U32, LAT.fromT(U32, t)), d, L, x, hp7, hxL))),
    port_sub(RG.without(RG.without(L, x), m0), L, d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), hsLW, LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, L) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m0 + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m0 + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (m0 + 1 : U32), hft, hd32)), faces_at(L, AD.view(U32, LAT.fromT(U32, t)), d, L, m0, hp7, hm0L))),
    ones_p3(RG.without(RG.without(L, x), m0), L, d, RG.last(lpre(cs, m0), s), hsLW, hp5, sub_has(Con{s, cs}, L, RG.last(lpre(cs, m0), s), hp1, sub_has(Con{s, lpre(cs, m0)}, Con{s, cs}, RG.last(lpre(cs, m0), s), MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(lpre(cs, m0), Con{s, cs}), has_self(s, cs), sub_cons_r(lpre(cs, m0), s, cs, sub_lpre(cs, m0))), last_mem(lpre(cs, m0), s)))),
    ME.subst(U32, q => {ones(RG.without(RG.without(L, x), m0), d, q) == True{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), ones_z0(RG.without(RG.without(L, x), m0), L, d, x, hsLW, hp5, hxL, hxLW)),
    ME.subst(U32, q => {ones(RG.without(RG.without(L, x), m0), d, (q + 1 : U32)) == True{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), ones_z1(RG.without(RG.without(L, x), m0), L, d, x, hsLW, hp5, hxL, hxLW)),
    ME.subst(U32, q => {ones(RG.without(RG.without(L, x), m0), d, q) == True{} : Bool}, m0, P.base(m0), Equal.sym(U32, P.base(m0), m0, hbm), ones_z0(RG.without(RG.without(L, x), m0), L, d, m0, hsLW, hp5, hm0L, hmLW)),
    ME.subst(U32, q => {ones(RG.without(RG.without(L, x), m0), d, (q + 1 : U32)) == True{} : Bool}, m0, P.base(m0), Equal.sym(U32, P.base(m0), m0, hbm), ones_z1(RG.without(RG.without(L, x), m0), L, d, m0, hsLW, hp5, hm0L, hmLW)),
    ones_head(RG.without(RG.without(L, x), m0), L, d, hsLW, hp5),
    LAT.mirror(U32, LAT.fromT(U32, t)),
    LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  %e : {RG.pend.ok(AD.view(U32, RG.words(R.join1(P.H{KM.MG{_}, a}, x, m0))), d, s, RG.without(cs, m0), ps, RG.without(RG.without(L, x), m0)) == True{} : Bool}
  %ea : {RG.pend.ok(AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x, m0))), d, s, RG.without(cs, m0), ps, RG.without(RG.without(L, x), m0)) == True{} : Bool}
  MB.and_eq_true(RG.ring(AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, s, RG.without(cs, m0)), Bool.and(RG.sub(Con{s, RG.without(cs, m0)}, RG.without(RG.without(L, x), m0)), Bool.and(RG.sub(ps, RG.without(RG.without(L, x), m0)), Bool.and(RG.none.in(ps, Con{s, RG.without(cs, m0)}), Bool.and(RG.distinct(ps), Bool.and(RG.layout(RG.without(RG.without(L, x), m0), d), Bool.and(RG.bases(RG.without(RG.without(L, x), m0)), RG.faces(RG.without(RG.without(L, x), m0), AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, RG.without(RG.without(L, x), m0)))))))), MB.eq_true_of_and_left(RG.ring(AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, s, RG.without(cs, m0)), Bool.and(RG.layout(Con{s, RG.without(cs, m0)}, d), Bool.and(RG.bases(Con{s, RG.without(cs, m0)}), RG.faces(Con{s, RG.without(cs, m0)}, AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, Con{s, RG.without(cs, m0)}))), hrok), MB.and_eq_true(RG.sub(Con{s, RG.without(cs, m0)}, RG.without(RG.without(L, x), m0)), Bool.and(RG.sub(ps, RG.without(RG.without(L, x), m0)), Bool.and(RG.none.in(ps, Con{s, RG.without(cs, m0)}), Bool.and(RG.distinct(ps), Bool.and(RG.layout(RG.without(RG.without(L, x), m0), d), Bool.and(RG.bases(RG.without(RG.without(L, x), m0)), RG.faces(RG.without(RG.without(L, x), m0), AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, RG.without(RG.without(L, x), m0))))))), sub_w2(Con{s, RG.without(cs, m0)}, L, x, m0, sub_trans(Con{s, RG.without(cs, m0)}, Con{s, cs}, L, subr, hp1), notin_sub(Con{s, RG.without(cs, m0)}, Con{s, cs}, x, subr, hxout), nm), MB.and_eq_true(RG.sub(ps, RG.without(RG.without(L, x), m0)), Bool.and(RG.none.in(ps, Con{s, RG.without(cs, m0)}), Bool.and(RG.distinct(ps), Bool.and(RG.layout(RG.without(RG.without(L, x), m0), d), Bool.and(RG.bases(RG.without(RG.without(L, x), m0)), RG.faces(RG.without(RG.without(L, x), m0), AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, RG.without(RG.without(L, x), m0)))))), sub_w2(ps, L, x, m0, hpsL, hxps, none_has(ps, Con{s, cs}, m0, hpsout, has_cons(s, cs, m0, hm))), MB.and_eq_true(RG.none.in(ps, Con{s, RG.without(cs, m0)}), Bool.and(RG.distinct(ps), Bool.and(RG.layout(RG.without(RG.without(L, x), m0), d), Bool.and(RG.bases(RG.without(RG.without(L, x), m0)), RG.faces(RG.without(RG.without(L, x), m0), AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, RG.without(RG.without(L, x), m0))))), none_sub(ps, Con{s, cs}, Con{s, RG.without(cs, m0)}, hpsout, subr), MB.and_eq_true(RG.distinct(ps), Bool.and(RG.layout(RG.without(RG.without(L, x), m0), d), Bool.and(RG.bases(RG.without(RG.without(L, x), m0)), RG.faces(RG.without(RG.without(L, x), m0), AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, RG.without(RG.without(L, x), m0)))), hdps, MB.and_eq_true(RG.layout(RG.without(RG.without(L, x), m0), d), Bool.and(RG.bases(RG.without(RG.without(L, x), m0)), RG.faces(RG.without(RG.without(L, x), m0), AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, RG.without(RG.without(L, x), m0))), lay_without(RG.without(L, x), d, m0, lay_without(L, d, x, hp5)), MB.and_eq_true(RG.bases(RG.without(RG.without(L, x), m0)), RG.faces(RG.without(RG.without(L, x), m0), AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, m0))), d, RG.without(RG.without(L, x), m0)), bases_sub(RG.without(RG.without(L, x), m0), L, hsLW, hp6), fjL)))))))

def Laws.join1_pend(w, a, d, s, t, ps, L, x, y, hf, hd32, hp, hy):
  join1_pend.m(w, a, d, s, t, ps, L, x, y, hf, hd32, hp, hy, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# The join frames over the exact ring

def ulx_keeps(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +x: U32, +j: U32, hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    hdone: {pdone(P.H{KM.MG{w}, a}, x) == True{} : Bool}, hp: {Nat.is_eq(AD.slot((Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{w}, a}, x)) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
    {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.unlink(P.H{KM.MG{w}, a}, x)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, w, j)) : U32}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hd1 = LAB.subst(Array<U32>, q => {pdone(P.H{KM.MG{q}, a}, x) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hdone)
  +hdt = LAB.subst(Array<V.Val>, q => {pdone(P.H{KM.MG{LAT.fromT(U32, t)}, q}, x) == True{} : Bool}, a, LAT.fromT(V.Val, ta), Equal.sym(Array<V.Val>, LAT.fromT(V.Val, ta), a, ea), hd1)
  +hp1 = LAB.subst(Array<U32>, q => {Nat.is_eq(AD.slot((Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{q}, a}, x)) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hp)
  +hpt = LAB.subst(Array<V.Val>, q => {Nat.is_eq(AD.slot((Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, q}, x)) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, a, LAT.fromT(V.Val, ta), Equal.sym(Array<V.Val>, LAT.fromT(V.Val, ta), a, ea), hp1)
  %e : {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.unlink(P.H{KM.MG{_}, a}, x)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, _, j)) : U32}
  %ea : {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.unlink(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)) : U32}
  %Equal.sym(P.H & U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x), (P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))), pred_pair_ok(t, LAT.fromT(V.Val, ta), d, x, hft, hdt)) :
    {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.unlink.p(_, x)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 3 : U32))) :
    {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.unlink.set(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)))), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)) : U32}
  LA.get_set_other(U32, LAT.fromT(U32, t), d, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), j, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), hft, hd32, hpt)

# join's frame, split forms: the word j followed through each step
def join_keeps.x(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +pa: List<&2, U32>, +x: U32, +pb: List<&2, U32>, +pc: List<&2, U32>, +y: U32, +pd: List<&2, U32>, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pa, Con{x, pb})) == True{} : Bool}, +hsp: {List.append(&2, U32, pa, pb) == List.append(&2, U32, pc, Con{y, pd}) : List<&2, U32>}, +hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pa, Con{x, pb})), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  hu: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{x, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, hw: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{x, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32)) == True{} : Bool},
  hju: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, hjw: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hp1: {Nat.is_eq(AD.slot((RG.last(pa, s) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hp2: {Nat.is_eq(AD.slot((RG.last(pc, s) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, 
  +h0x: {Nat.is_eq(AD.slot(P.base(x), d), AD.slot(j, d)) == False{} : Bool}, +h1x: {Nat.is_eq(AD.slot((P.base(x) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, +h0y: {Nat.is_eq(AD.slot(P.base(y), d), AD.slot(j, d)) == False{} : Bool}, +h1y: {Nat.is_eq(AD.slot((P.base(y) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {Pair.snd(P.H, U32, P.rd(R.join(P.H{KM.MG{w}, a}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, List.append(&2, U32, pa, Con{x, pb})) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hut = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{x, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hu)
  +hwt = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{x, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (y + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hw)
  +hjut = LAB.subst(Array<U32>, q => {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, q, (x + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hju)
  +hjwt = LAB.subst(Array<U32>, q => {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, q, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hjw)
  +hr1 = lx_ring(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), s, List.append(&2, U32, pa, Con{x, pb}), hft, hd32, hrt, hut, hwt)
  +hf1 = lx_full(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), hft)
  +k1 = lx_keeps(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), j, hft, hd32, hjut, hjwt)
  +pe1 = pred_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, s, pa, x, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))))
  +k2 = ulx_keeps(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, x, j, hf1, hd32, pdone_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, s, pa, x, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))))),
    ME.subst(U32, q => {Nat.is_eq(AD.slot((q + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, RG.last(pa, s), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), Equal.sym(U32, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), RG.last(pa, s), pe1), hp1), LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf2 = ul_full(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, x, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hr2 = unlink_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, s, pa, x, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hr2c = ME.subst(List<&2, U32>, q => {RG.ring(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))), d, s, q) == True{} : Bool}, List.append(&2, U32, pa, pb), List.append(&2, U32, pc, Con{y, pd}), hsp, hr2)
  +hn1 = ME.subst(Nat, q => {Nat.is_lt(q, U32.to_nat(U32.shln(1, d))) == True{} : Bool}, List.length(&2, U32, List.append(&2, U32, pa, Con{x, pb})), 1n+List.length(&2, U32, List.append(&2, U32, pa, pb)), len_mid(pa, x, pb), hn)
  +hn2 = ME.subst(List<&2, U32>, q => {Nat.is_lt(List.length(&2, U32, q), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, List.append(&2, U32, pa, pb), List.append(&2, U32, pc, Con{y, pd}), hsp, MN.lt_trans(List.length(&2, U32, List.append(&2, U32, pa, pb)), 1n+List.length(&2, U32, List.append(&2, U32, pa, pb)), U32.to_nat(U32.shln(1, d)), MN.lt_succ_self(List.length(&2, U32, List.append(&2, U32, pa, pb))), hn1))
  +pe2 = pred_exact.go(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, s, pc, y, pd, hf2, hd32, hr2c, hn2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))))
  +k3 = ulx_keeps(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, y, j, hf2, hd32, pdone_exact.go(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, s, pc, y, pd, hf2, hd32, hr2c, hn2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)))),
    ME.subst(U32, q => {Nat.is_eq(AD.slot((q + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, RG.last(pc, s), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), Equal.sym(U32, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), RG.last(pc, s), pe2), hp2), LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf3 = ul_full(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, y, hf2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +k4 = fr_keeps(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), d, x, j, hf3, hd32, h0x, h1x, hjh, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))))
  +hf4 = fr_full(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), d, x, hf3, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))))
  +k5 = fr_keeps(RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, y, j, hf4, hd32, h0y, h1y, hjh, LAT.mirror(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))))
  %e : {Pair.snd(P.H, U32, P.rd(R.join(P.H{KM.MG{_}, a}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %ea : {Pair.snd(P.H, U32, P.rd(R.join(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, _}, j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 1 : U32))) :
    {Pair.snd(P.H, U32, P.rd(R.jn.u(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (y + 1 : U32))) :
    {Pair.snd(P.H, U32, P.rd(R.jn.w(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %lx_parts(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))) :
    {Pair.snd(P.H, U32, P.rd(P.free(P.free(R.rg.unlink(R.rg.unlink(_, x), y), x), y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %ul_parts(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, x, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {Pair.snd(P.H, U32, P.rd(P.free(P.free(R.rg.unlink(_, y), x), y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %ul_parts(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, y, hf2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {Pair.snd(P.H, U32, P.rd(P.free(P.free(_, x), y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %fr_parts(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), x, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)))) :
    {Pair.snd(P.H, U32, P.rd(P.free(_, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %fr_parts(RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), y, LAT.mirror(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)))) :
    {Pair.snd(P.H, U32, P.rd(_, j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{RG.words(P.free(P.H{KM.MG{RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)), rd_get(RG.words(P.free(P.H{KM.MG{RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), j), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), k5, Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), k4, Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), k3, Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, x)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), k2, k1)))), Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), rd_get(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), j))))

# join1's frame, split forms: the word j followed through each step
def join1_keeps.x(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +pa: List<&2, U32>, +x: U32, +y: U32, +pb: List<&2, U32>, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pa, Con{y, pb})) == True{} : Bool}, +hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pa, Con{y, pb})), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  hu: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{y, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, hw: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{y, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32)) == True{} : Bool},
  hju: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, hjw: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hp1: {Nat.is_eq(AD.slot((RG.last(pa, s) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, 
  +h0x: {Nat.is_eq(AD.slot(P.base(x), d), AD.slot(j, d)) == False{} : Bool}, +h1x: {Nat.is_eq(AD.slot((P.base(x) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, +h0y: {Nat.is_eq(AD.slot(P.base(y), d), AD.slot(j, d)) == False{} : Bool}, +h1y: {Nat.is_eq(AD.slot((P.base(y) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {Pair.snd(P.H, U32, P.rd(R.join1(P.H{KM.MG{w}, a}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, List.append(&2, U32, pa, Con{y, pb})) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hut = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{y, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hu)
  +hwt = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{y, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (y + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hw)
  +hjut = LAB.subst(Array<U32>, q => {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, q, (x + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hju)
  +hjwt = LAB.subst(Array<U32>, q => {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, q, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hjw)
  +hr1 = lx_ring(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), s, List.append(&2, U32, pa, Con{y, pb}), hft, hd32, hrt, hut, hwt)
  +hf1 = lx_full(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), hft)
  +k1 = lx_keeps(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), j, hft, hd32, hjut, hjwt)
  +pe1 = pred_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, s, pa, y, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))))
  +k2 = ulx_keeps(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, y, j, hf1, hd32, pdone_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, s, pa, y, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))))),
    ME.subst(U32, q => {Nat.is_eq(AD.slot((q + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, RG.last(pa, s), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y)), Equal.sym(U32, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y)), RG.last(pa, s), pe1), hp1), LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf2 = ul_full(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, y, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +k3 = fr_keeps(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), d, x, j, hf2, hd32, h0x, h1x, hjh, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))))
  +hf3 = fr_full(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), d, x, hf2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))))
  +k4 = fr_keeps(RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, y, j, hf3, hd32, h0y, h1y, hjh, LAT.mirror(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))))
  %e : {Pair.snd(P.H, U32, P.rd(R.join1(P.H{KM.MG{_}, a}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %ea : {Pair.snd(P.H, U32, P.rd(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, _}, j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 1 : U32))) :
    {Pair.snd(P.H, U32, P.rd(R.jn1.u(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (y + 1 : U32))) :
    {Pair.snd(P.H, U32, P.rd(R.jn1.w(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %lx_parts(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))) :
    {Pair.snd(P.H, U32, P.rd(P.free(P.free(R.rg.unlink(_, y), x), y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %ul_parts(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, y, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {Pair.snd(P.H, U32, P.rd(P.free(P.free(_, x), y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %fr_parts(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), x, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y)))) :
    {Pair.snd(P.H, U32, P.rd(P.free(_, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %fr_parts(RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), y, LAT.mirror(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)))) :
    {Pair.snd(P.H, U32, P.rd(_, j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{RG.words(P.free(P.H{KM.MG{RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)), rd_get(RG.words(P.free(P.H{KM.MG{RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), j), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), k4, Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), k3, Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), k2, k1))), Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), rd_get(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), j))))

def join_keeps.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32, +y: U32, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {RG.ring.ok(AD.view(U32, w), d, s, cs) == True{} : Bool},
  +hx: {RG.has(cs, x) == True{} : Bool}, +hy: {RG.has(cs, y) == True{} : Bool}, +hxy: {U32.is_eq(x, y) == False{} : Bool},
  +hj: {RG.off.links(Con{s, cs}, d, j) == True{} : Bool}, +hjx: {RG.off.node(d, x, j) == True{} : Bool}, +hjy: {RG.off.node(d, y, j) == True{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool},
  hju: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, hjw: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {Pair.snd(P.H, U32, P.rd(R.join(P.H{KM.MG{w}, a}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring.ok(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hring = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)
  +hbases = MB.eq_true_of_and_left(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hfaces = MB.eq_true_of_and_right(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hring)
  +hn = len_ok(t, d, s, cs, hft, hd32, hap)
  +hjut = LAB.subst(Array<U32>, q => {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, q, (x + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hju)
  +hjwt = LAB.subst(Array<U32>, q => {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, q, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hjw)
  %e : {Pair.snd(P.H, U32, P.rd(R.join(P.H{KM.MG{_}, a}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %ea : {Pair.snd(P.H, U32, P.rd(R.join(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, _}, j)) : U32}
  +eqWX = without_eq(d, s, cs, x, hap, hx)
  +hyW = has_without(cs, x, y, hxy, hy)
  +hsp = Equal.trans(List<&2, U32>, List.append(&2, U32, lpre(cs, x), lpost(cs, x)), RG.without(cs, x), List.append(&2, U32, lpre(RG.without(cs, x), y), Con{y, lpost(RG.without(cs, x), y)}), Equal.sym(List<&2, U32>, RG.without(cs, x), List.append(&2, U32, lpre(cs, x), lpost(cs, x)), eqWX), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(RG.without(cs, x), y), Con{y, lpost(RG.without(cs, x), y)}), RG.without(cs, x), split_of_has(RG.without(cs, x), y, hyW)))
  +hbx = MS.u32_eq_of_is_eq(P.base(x), x, bases_at(Con{s, cs}, x, hbases, has_cons(s, cs, x, hx)))
  +hby = MS.u32_eq_of_is_eq(P.base(y), y, bases_at(Con{s, cs}, y, hbases, has_cons(s, cs, y, hy)))
  join_keeps.x(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, lpre(cs, x), x, lpost(cs, x), lpre(RG.without(cs, x), y), y, lpost(RG.without(cs, x), y), j, hft, hd32, ring_split(AD.view(U32, LAT.fromT(U32, t)), d, s, cs, x, hring, hx), hsp,
    ME.subst(List<&2, U32>, q => {Nat.is_lt(List.length(&2, U32, q), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), cs, split_of_has(cs, x, hx)), hn),
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), cs, split_of_has(cs, x, hx)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, Con{s, cs}) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (x + 1 : U32), hft, hd32)), faces_at(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}, x, hfaces, has_cons(s, cs, x, hx))))), ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, x), Con{x, lpost(cs, x)}), cs, split_of_has(cs, x, hx)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32)), LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, Con{s, cs}) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (y + 1 : U32), hft, hd32)), faces_at(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}, y, hfaces, has_cons(s, cs, y, hy))))), hjut, hjwt,
    Equal.trans(Bool, Nat.is_eq(AD.slot((RG.last(lpre(cs, x), s) + 3 : U32), d), AD.slot(j, d)), Nat.is_eq(AD.slot(j, d), AD.slot((RG.last(lpre(cs, x), s) + 3 : U32), d)), False{}, MN.is_eq_comm(AD.slot((RG.last(lpre(cs, x), s) + 3 : U32), d), AD.slot(j, d)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(j, d), AD.slot((RG.last(lpre(cs, x), s) + 3 : U32), d)), links_at(Con{s, cs}, d, j, RG.last(lpre(cs, x), s), hj, sub_has(Con{s, lpre(cs, x)}, Con{s, cs}, RG.last(lpre(cs, x), s), MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(lpre(cs, x), Con{s, cs}), has_self(s, cs), sub_cons_r(lpre(cs, x), s, cs, sub_lpre(cs, x))), last_mem(lpre(cs, x), s))))),
    Equal.trans(Bool, Nat.is_eq(AD.slot((RG.last(lpre(RG.without(cs, x), y), s) + 3 : U32), d), AD.slot(j, d)), Nat.is_eq(AD.slot(j, d), AD.slot((RG.last(lpre(RG.without(cs, x), y), s) + 3 : U32), d)), False{}, MN.is_eq_comm(AD.slot((RG.last(lpre(RG.without(cs, x), y), s) + 3 : U32), d), AD.slot(j, d)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(j, d), AD.slot((RG.last(lpre(RG.without(cs, x), y), s) + 3 : U32), d)), links_at(Con{s, cs}, d, j, RG.last(lpre(RG.without(cs, x), y), s), hj, sub_has(Con{s, lpre(RG.without(cs, x), y)}, Con{s, cs}, RG.last(lpre(RG.without(cs, x), y), s), MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(lpre(RG.without(cs, x), y), Con{s, cs}), has_self(s, cs), sub_cons_r(lpre(RG.without(cs, x), y), s, cs, sub_trans(lpre(RG.without(cs, x), y), RG.without(cs, x), cs, sub_lpre(RG.without(cs, x), y), sub_without(cs, x)))), last_mem(lpre(RG.without(cs, x), y), s))))),
    ME.subst(U32, q => {Nat.is_eq(AD.slot(q, d), AD.slot(j, d)) == False{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), off_w0(d, x, j, hjx)), ME.subst(U32, q => {Nat.is_eq(AD.slot((q + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), off_w1(d, x, j, hjx)),
    ME.subst(U32, q => {Nat.is_eq(AD.slot(q, d), AD.slot(j, d)) == False{} : Bool}, y, P.base(y), Equal.sym(U32, P.base(y), y, hby), off_w0(d, y, j, hjy)), ME.subst(U32, q => {Nat.is_eq(AD.slot((q + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, y, P.base(y), Equal.sym(U32, P.base(y), y, hby), off_w1(d, y, j, hjy)), hjh,
    LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))

def Laws.join_keeps(w, a, d, s, t, x, y, j, hf, hd32, hr, hx, hy, hxy, hj, hjx, hjy, hjh, hju, hjw):
  join_keeps.m(w, a, d, s, t, x, y, j, hf, hd32, hr, hx, hy, hxy, hj, hjx, hjy, hjh, hju, hjw, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

def join1_keeps.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32, +y: U32, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {RG.ring.ok(AD.view(U32, w), d, s, cs) == True{} : Bool},
  hx: {RG.node.ok(AD.view(U32, w), d, Con{s, cs}, x) == True{} : Bool}, +hy: {RG.has(cs, y) == True{} : Bool},
  +hj: {RG.off.links(Con{s, cs}, d, j) == True{} : Bool}, +hjx: {RG.off.node(d, x, j) == True{} : Bool}, +hjy: {RG.off.node(d, y, j) == True{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool},
  hju: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, hjw: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {Pair.snd(P.H, U32, P.rd(R.join1(P.H{KM.MG{w}, a}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring.ok(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hring = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)
  +hbases = MB.eq_true_of_and_left(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hfaces = MB.eq_true_of_and_right(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hring)
  +hn = len_ok(t, d, s, cs, hft, hd32, hap)
  +hxt = LAB.subst(Array<U32>, q => {RG.node.ok(AD.view(U32, q), d, Con{s, cs}, x) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hx)
  +hjut = LAB.subst(Array<U32>, q => {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, q, (x + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hju)
  +hjwt = LAB.subst(Array<U32>, q => {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, q, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hjw)
  %e : {Pair.snd(P.H, U32, P.rd(R.join1(P.H{KM.MG{_}, a}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %ea : {Pair.snd(P.H, U32, P.rd(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, _}, j)) : U32}
  +hbx = MS.u32_eq_of_is_eq(P.base(x), x, MB.eq_true_of_and_left(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs})), hxt)))
  +hby = MS.u32_eq_of_is_eq(P.base(y), y, bases_at(Con{s, cs}, y, hbases, has_cons(s, cs, y, hy)))
  +hut = LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, Con{s, cs}) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))},
    Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (x + 1 : U32), hft, hd32)), MB.eq_true_of_and_right(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs})), hxt)))
  join1_keeps.x(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, lpre(cs, y), x, y, lpost(cs, y), j, hft, hd32, ring_split(AD.view(U32, LAT.fromT(U32, t)), d, s, cs, y, hring, hy),
    ME.subst(List<&2, U32>, q => {Nat.is_lt(List.length(&2, U32, q), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, y), Con{y, lpost(cs, y)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, y), Con{y, lpost(cs, y)}), cs, split_of_has(cs, y, hy)), hn),
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, y), Con{y, lpost(cs, y)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, y), Con{y, lpost(cs, y)}), cs, split_of_has(cs, y, hy)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), hut)), ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, y), Con{y, lpost(cs, y)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, y), Con{y, lpost(cs, y)}), cs, split_of_has(cs, y, hy)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32)), LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, Con{s, cs}) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (y + 1 : U32), hft, hd32)), faces_at(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}, y, hfaces, has_cons(s, cs, y, hy))))), hjut, hjwt,
    Equal.trans(Bool, Nat.is_eq(AD.slot((RG.last(lpre(cs, y), s) + 3 : U32), d), AD.slot(j, d)), Nat.is_eq(AD.slot(j, d), AD.slot((RG.last(lpre(cs, y), s) + 3 : U32), d)), False{}, MN.is_eq_comm(AD.slot((RG.last(lpre(cs, y), s) + 3 : U32), d), AD.slot(j, d)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(j, d), AD.slot((RG.last(lpre(cs, y), s) + 3 : U32), d)), links_at(Con{s, cs}, d, j, RG.last(lpre(cs, y), s), hj, sub_has(Con{s, lpre(cs, y)}, Con{s, cs}, RG.last(lpre(cs, y), s), MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(lpre(cs, y), Con{s, cs}), has_self(s, cs), sub_cons_r(lpre(cs, y), s, cs, sub_lpre(cs, y))), last_mem(lpre(cs, y), s))))),
    ME.subst(U32, q => {Nat.is_eq(AD.slot(q, d), AD.slot(j, d)) == False{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), off_w0(d, x, j, hjx)), ME.subst(U32, q => {Nat.is_eq(AD.slot((q + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), off_w1(d, x, j, hjx)),
    ME.subst(U32, q => {Nat.is_eq(AD.slot(q, d), AD.slot(j, d)) == False{} : Bool}, y, P.base(y), Equal.sym(U32, P.base(y), y, hby), off_w0(d, y, j, hjy)), ME.subst(U32, q => {Nat.is_eq(AD.slot((q + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, y, P.base(y), Equal.sym(U32, P.base(y), y, hby), off_w1(d, y, j, hjy)), hjh,
    LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))

def Laws.join1_keeps(w, a, d, s, t, x, y, j, hf, hd32, hr, hx, hy, hj, hjx, hjy, hjh, hju, hjw):
  join1_keeps.m(w, a, d, s, t, x, y, j, hf, hd32, hr, hx, hy, hj, hjx, hjy, hjh, hju, hjw, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# A leave keeps every word but its own: its predecessor's word 3, its own node, the
# head, the two ports' link words; join1_keeps's steps with the port given
# and one free
def leave_keeps.x(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +pa: List<&2, U32>, +pp: U32, +y: U32, +pb: List<&2, U32>, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pa, Con{y, pb})) == True{} : Bool}, +hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pa, Con{y, pb})), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  +hu: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{y, pb})}, d, (pp + 1 : U32)) == True{} : Bool}, hw: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{y, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32)) == True{} : Bool},
  +hjp: {Nat.is_eq(AD.slot((pp + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, hjw: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hp1: {Nat.is_eq(AD.slot((RG.last(pa, s) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool},
  +h0y: {Nat.is_eq(AD.slot(P.base(y), d), AD.slot(j, d)) == False{} : Bool}, +h1y: {Nat.is_eq(AD.slot((P.base(y) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {Pair.snd(P.H, U32, P.rd(R.leave(P.H{KM.MG{w}, a}, pp, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, List.append(&2, U32, pa, Con{y, pb})) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hwt = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{y, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (y + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hw)
  +hjwt = LAB.subst(Array<U32>, q => {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, q, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hjw)
  +hr1 = lx_ring(P.is_static(pp), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), s, List.append(&2, U32, pa, Con{y, pb}), hft, hd32, hrt, hu, hwt)
  +hf1 = lx_full(P.is_static(pp), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), hft)
  +k1 = lx_keeps(P.is_static(pp), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), j, hft, hd32, hjp, hjwt)
  +pe1 = pred_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp)), LAT.fromT(V.Val, ta), d, s, pa, y, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))))
  +k2 = ulx_keeps(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp)), LAT.fromT(V.Val, ta), d, y, j, hf1, hd32, pdone_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp)), LAT.fromT(V.Val, ta), d, s, pa, y, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp)))),
    ME.subst(U32, q => {Nat.is_eq(AD.slot((q + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, RG.last(pa, s), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, y)), Equal.sym(U32, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, y)), RG.last(pa, s), pe1), hp1), LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf2 = ul_full(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp)), LAT.fromT(V.Val, ta), d, y, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +k3 = fr_keeps(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), d, y, j, hf2, hd32, h0y, h1y, hjh, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, y))))
  %e : {Pair.snd(P.H, U32, P.rd(R.leave(P.H{KM.MG{_}, a}, pp, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %ea : {Pair.snd(P.H, U32, P.rd(R.leave(P.H{KM.MG{LAT.fromT(U32, t)}, _}, pp, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, _}, j)) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (y + 1 : U32))) :
    {Pair.snd(P.H, U32, P.rd(R.lv.w(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), pp, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %lx_parts(P.is_static(pp), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))) :
    {Pair.snd(P.H, U32, P.rd(P.free(R.rg.unlink(_, y), y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %ul_parts(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp)), LAT.fromT(V.Val, ta), d, y, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {Pair.snd(P.H, U32, P.rd(P.free(_, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %fr_parts(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), y, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, y)))) :
    {Pair.snd(P.H, U32, P.rd(_, j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)), rd_get(RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), j),
    Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)),
      Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), k3, Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp))}, LAT.fromT(V.Val, ta)}, y)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(pp), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, pp, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), pp)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), k2, k1)),
      Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), rd_get(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), j))))

def leave_keeps.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +pp: U32, +y: U32, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {RG.ring.ok(AD.view(U32, w), d, s, cs) == True{} : Bool},
  +hy: {RG.has(cs, y) == True{} : Bool}, +hp: {RG.port.ok(Con{s, cs}, d, pp) == True{} : Bool},
  +hj: {RG.off.links(Con{s, cs}, d, j) == True{} : Bool}, +hjy: {RG.off.node(d, y, j) == True{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool},
  +hjp: {Nat.is_eq(AD.slot((pp + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, hjw: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {Pair.snd(P.H, U32, P.rd(R.leave(P.H{KM.MG{w}, a}, pp, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring.ok(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hring = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)
  +hbases = MB.eq_true_of_and_left(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hfaces = MB.eq_true_of_and_right(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hring)
  +hn = len_ok(t, d, s, cs, hft, hd32, hap)
  +hjwt = LAB.subst(Array<U32>, q => {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, q, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hjw)
  %e : {Pair.snd(P.H, U32, P.rd(R.leave(P.H{KM.MG{_}, a}, pp, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %ea : {Pair.snd(P.H, U32, P.rd(R.leave(P.H{KM.MG{LAT.fromT(U32, t)}, _}, pp, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, _}, j)) : U32}
  +hby = MS.u32_eq_of_is_eq(P.base(y), y, bases_at(Con{s, cs}, y, hbases, has_cons(s, cs, y, hy)))
  leave_keeps.x(LAT.fromT(U32, t),
    LAT.fromT(V.Val, ta),
    d,
    s,
    lpre(cs, y),
    pp,
    y,
    lpost(cs, y),
    j,
    hft,
    hd32,
    ring_split(AD.view(U32, LAT.fromT(U32, t)), d, s, cs, y, hring, hy),
    ME.subst(List<&2, U32>, q => {Nat.is_lt(List.length(&2, U32, q), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, y), Con{y, lpost(cs, y)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, y), Con{y, lpost(cs, y)}), cs, split_of_has(cs, y, hy)), hn),
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (pp + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, y), Con{y, lpost(cs, y)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, y), Con{y, lpost(cs, y)}), cs, split_of_has(cs, y, hy)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (pp + 1 : U32)), RG.off.pos(Con{s, cs}, d, (pp + 1 : U32)), hp)),
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, y), Con{y, lpost(cs, y)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, y), Con{y, lpost(cs, y)}), cs, split_of_has(cs, y, hy)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32)), LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, Con{s, cs}) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (y + 1 : U32), hft, hd32)), faces_at(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}, y, hfaces, has_cons(s, cs, y, hy))))),
    hjp,
    hjwt,
    Equal.trans(Bool, Nat.is_eq(AD.slot((RG.last(lpre(cs, y), s) + 3 : U32), d), AD.slot(j, d)), Nat.is_eq(AD.slot(j, d), AD.slot((RG.last(lpre(cs, y), s) + 3 : U32), d)), False{}, MN.is_eq_comm(AD.slot((RG.last(lpre(cs, y), s) + 3 : U32), d), AD.slot(j, d)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(j, d), AD.slot((RG.last(lpre(cs, y), s) + 3 : U32), d)), links_at(Con{s, cs}, d, j, RG.last(lpre(cs, y), s), hj, sub_has(Con{s, lpre(cs, y)}, Con{s, cs}, RG.last(lpre(cs, y), s), MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(lpre(cs, y), Con{s, cs}), has_self(s, cs), sub_cons_r(lpre(cs, y), s, cs, sub_lpre(cs, y))), last_mem(lpre(cs, y), s))))),
    ME.subst(U32, q => {Nat.is_eq(AD.slot(q, d), AD.slot(j, d)) == False{} : Bool}, y, P.base(y), Equal.sym(U32, P.base(y), y, hby), off_w0(d, y, j, hjy)),
    ME.subst(U32, q => {Nat.is_eq(AD.slot((q + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, y, P.base(y), Equal.sym(U32, P.base(y), y, hby), off_w1(d, y, j, hjy)),
    hjh,
    LAT.mirror(U32, LAT.fromT(U32, t)),
    LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))

def Laws.leave_keeps(w, a, d, s, t, p, c, j, hf, hd32, hr, hc, hp, hj, hjc, hjh, hjp, hjw):
  leave_keeps.m(w, a, d, s, t, p, c, j, hf, hd32, hr, hc, hp, hj, hjc, hjh, hjp, hjw, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# A crossing: the find, then a join or a cursor

# a Maybe's value, or z where there is none, and whether there is one
def mval(m: Maybe<&2, U32>, +z: U32) -> U32:
  match m:
    case Some{+q}:
      q
    case None{}:
      z

def issome(m: Maybe<&2, U32>) -> Bool:
  match m:
    case Some{+q}:
      True{}
    case None{}:
      False{}

# the find's model names a member of the list it walked
def fh_step(+z: U32, +r: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +far: U32, +y: U32, +b: Bool,
    h: {RG.first.k(b, z, RG.first(r, v, d, far)) == Some{y} : Maybe<&2, U32>},
    ih: {RG.first(r, v, d, far) == Some{y} : Maybe<&2, U32>} -> {RG.has(r, y) == True{} : Bool}) -> {RG.has(Con{z, r}, y) == True{} : Bool}:
  match b:
    case True{}:
      ME.subst(U32, k => {RG.has(Con{z, r}, k) == True{} : Bool}, z, y, ME.subst(Maybe<&2, U32>, mm => {z == mval(mm, z) : U32}, Some{z}, Some{y}, h, {==}), has_self(z, r))
    case False{}:
      has_cons(z, r, y, ih(h))

def first_has(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +far: U32, +y: U32, h: {RG.first(ys, v, d, far) == Some{y} : Maybe<&2, U32>}) -> {RG.has(ys, y) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({RG.has(Nil{}, y) == True{} : Bool}, MB.false_ne_true()(ME.subst(Maybe<&2, U32>, mm => {False{} == issome(mm) : Bool}, None{}, Some{y}, h, {==})))
    case Con{+z, +r}:
      fh_step(z, r, v, d, far, y, RG.pos.is(v, d, z, far), h, q => first_has(r, v, d, far, y, q))

# a crossing by what its find found: a join, or a cursor made
def cross_step(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +ps: List<&2, U32>, +L: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +far: U32,
  m: Maybe<&2, U32>, e: {RG.first(cs, AD.view(U32, w), d, far) == m : Maybe<&2, U32>},
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hp: {RG.pend.ok(AD.view(U32, w), d, s, cs, Con{x, ps}, L) == True{} : Bool},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.pend.ok(AD.view(U32, RG.words(R.cross.k((P.H{KM.MG{w}, a}, m), s, x, src, neg))), d, s, RG.cross.t(m, x, cs), ps, RG.cross.L(m, x, L)) == True{} : Bool}:
  match m:
    case Some{+y}:
      (+t, +et) = mw
      (+ta, +eta) = ma
      +hft = LAP.full_t(U32, w, t, d, et, hf)
      +hpt = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, q), d, s, cs, Con{x, ps}, L) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, et), hp)
      +eyt = LAB.subst(Array<U32>, q => {RG.first(cs, AD.view(U32, q), d, far) == Some{y} : Maybe<&2, U32>}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, et), e)
      %et : {RG.pend.ok(AD.view(U32, RG.words(R.cross.k((P.H{KM.MG{_}, a}, Some{y}), s, x, src, neg))), d, s, RG.cross.t(Some{y}, x, cs), ps, RG.cross.L(Some{y}, x, L)) == True{} : Bool}
      %eta : {RG.pend.ok(AD.view(U32, RG.words(R.cross.k((P.H{KM.MG{LAT.fromT(U32, t)}, _}, Some{y}), s, x, src, neg))), d, s, RG.cross.t(Some{y}, x, cs), ps, RG.cross.L(Some{y}, x, L)) == True{} : Bool}
      join1_pend.m(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, ps, L, x, y, hft, hd32, hpt, first_has(cs, AD.view(U32, LAT.fromT(U32, t)), d, far, y, eyt), LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
    case None{}:
      cursor_pend.m(w, a, d, s, cs, ps, L, x, src, neg, hf, hd32, hp, mw, ma)

def cross_pend.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +ps: List<&2, U32>, +L: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +far: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hp: {RG.pend.ok(AD.view(U32, w), d, s, cs, Con{x, ps}, L) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {RG.pend.ok(AD.view(U32, RG.words(R.cross(P.H{KM.MG{w}, a}, s, x, src, neg, far))), d, s, RG.cross.t(RG.first(cs, AD.view(U32, w), d, far), x, cs), ps, RG.cross.L(RG.first(cs, AD.view(U32, w), d, far), x, L)) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hpt = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, q), d, s, cs, Con{x, ps}, L) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hp)
  +hr0 = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt)
  %e : {RG.pend.ok(AD.view(U32, RG.words(R.cross(P.H{KM.MG{_}, a}, s, x, src, neg, far))), d, s, RG.cross.t(RG.first(cs, AD.view(U32, _), d, far), x, cs), ps, RG.cross.L(RG.first(cs, AD.view(U32, _), d, far), x, L)) == True{} : Bool}
  %ea : {RG.pend.ok(AD.view(U32, RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, t)}, _}, s, x, src, neg, far))), d, s, RG.cross.t(RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far), x, cs), ps, RG.cross.L(RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far), x, L)) == True{} : Bool}
  %Equal.sym(P.H & Maybe<&2, U32>, R.rg.find(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, far), (P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far)), find_exact.m(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, far, hft, hd32, hr0, LAT.mirror(U32, LAT.fromT(U32, t)))) :
    {RG.pend.ok(AD.view(U32, RG.words(R.cross.k(_, s, x, src, neg))), d, s, RG.cross.t(RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far), x, cs), ps, RG.cross.L(RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far), x, L)) == True{} : Bool}
  cross_step(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, ps, L, x, src, neg, far, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far), {==}, hft, hd32, hpt, LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))

def Laws.cross_pend(w, a, d, s, t, ps, L, x, src, neg, far, hf, hd32, hp):
  cross_pend.m(w, a, d, s, t, ps, L, x, src, neg, far, hf, hd32, hp, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# A copy's crossings: the find on agreeing views

# two words read alike give a position test alike
def meq_pos(a: Maybe<&2, U32>, b: Maybe<&2, U32>, +far: U32, h: {RG.meq(a, b) == True{} : Bool}) -> {RG.pos.is.m(a, far) == RG.pos.is.m(b, far) : Bool}:
  match a:
    case Some{+x}:
      match b:
        case Some{+y}:
          ME.subst(U32, k => {U32.is_eq(x, far) == U32.is_eq(k, far) : Bool}, x, y, MS.u32_eq_of_is_eq(x, y, h), {==})
        case None{}:
          Empty.absurd({RG.pos.is.m(Some{x}, far) == RG.pos.is.m(None{}, far) : Bool}, MB.false_ne_true()(h))
    case None{}:
      match b:
        case Some{+y}:
          Empty.absurd({RG.pos.is.m(None{}, far) == RG.pos.is.m(Some{y}, far) : Bool}, MB.false_ne_true()(h))
        case None{}:
          {==}

# a find's model the same on two views agreeing at the members' words 2:
# the model of a copy's crossings shares none of the code's finds
def first_agree(ys: List<&2, U32>, +v1: List<&2, U32>, +v2: List<&2, U32>, +d: Nat, +far: U32, +h: {RG.agree(ys, v1, v2, d) == True{} : Bool}) ->
    {RG.first(ys, v1, d, far) == RG.first(ys, v2, d, far) : Maybe<&2, U32>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      +ep = meq_pos(List.get(&2, U32, v1, AD.slot((m + 2 : U32), d)), List.get(&2, U32, v2, AD.slot((m + 2 : U32), d)), far, MB.eq_true_of_and_left(RG.meq(List.get(&2, U32, v1, AD.slot((m + 2 : U32), d)), List.get(&2, U32, v2, AD.slot((m + 2 : U32), d))), RG.agree(r, v1, v2, d), h))
      +ih = first_agree(r, v1, v2, d, far, MB.eq_true_of_and_right(RG.meq(List.get(&2, U32, v1, AD.slot((m + 2 : U32), d)), List.get(&2, U32, v2, AD.slot((m + 2 : U32), d))), RG.agree(r, v1, v2, d), h))
      %ep : {RG.first.k(RG.pos.is.m(List.get(&2, U32, v1, AD.slot((m + 2 : U32), d)), far), m, RG.first(r, v1, d, far)) == RG.first.k(_, m, RG.first(r, v2, d, far)) : Maybe<&2, U32>}
      %ih : {RG.first.k(RG.pos.is.m(List.get(&2, U32, v1, AD.slot((m + 2 : U32), d)), far), m, RG.first(r, v1, d, far)) == RG.first.k(RG.pos.is.m(List.get(&2, U32, v1, AD.slot((m + 2 : U32), d)), far), m, _) : Maybe<&2, U32>}
      {==}

# A copy's crossings: a crossing's heap in its parts and full

def join1_parts(+t: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +x: U32, +y: U32, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}) -> {P.H{KM.MG{RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))}, LAT.fromT(V.Val, ta)} == R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y) : P.H}:
  +hf1 = lx_full(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), hft)
  +hf2 = ul_full(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, y, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 1 : U32))) :
    {P.H{KM.MG{RG.words(R.jn1.u(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), x, y))}, LAT.fromT(V.Val, ta)} == R.jn1.u(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), x, y) : P.H}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (y + 1 : U32))) :
    {P.H{KM.MG{RG.words(R.jn1.w(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), x, y))}, LAT.fromT(V.Val, ta)} == R.jn1.w(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), x, y) : P.H}
  %lx_parts(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))) :
    {P.H{KM.MG{RG.words(P.free(P.free(R.rg.unlink(_, y), x), y))}, LAT.fromT(V.Val, ta)} == P.free(P.free(R.rg.unlink(_, y), x), y) : P.H}
  %ul_parts(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, y, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {P.H{KM.MG{RG.words(P.free(P.free(_, x), y))}, LAT.fromT(V.Val, ta)} == P.free(P.free(_, x), y) : P.H}
  %fr_parts(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), x, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y)))) :
    {P.H{KM.MG{RG.words(P.free(_, y))}, LAT.fromT(V.Val, ta)} == P.free(_, y) : P.H}
  fr_parts(RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), y, LAT.mirror(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))))

def join1_full(+t: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +x: U32, +y: U32, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}) -> {AD.full(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y)), d) == True{} : Bool}:
  +hf1 = lx_full(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), hft)
  +hf2 = ul_full(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, y, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 1 : U32))) :
    {AD.full(U32, RG.words(R.jn1.u(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), x, y)), d) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (y + 1 : U32))) :
    {AD.full(U32, RG.words(R.jn1.w(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), x, y)), d) == True{} : Bool}
  %lx_parts(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))) :
    {AD.full(U32, RG.words(P.free(P.free(R.rg.unlink(_, y), x), y)), d) == True{} : Bool}
  %ul_parts(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, y, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {AD.full(U32, RG.words(P.free(P.free(_, x), y)), d) == True{} : Bool}
  %fr_parts(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), x, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y)))) :
    {AD.full(U32, RG.words(P.free(_, y)), d) == True{} : Bool}
  fr_full(RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, y, fr_full(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y)), LAT.fromT(V.Val, ta), d, x, hf2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y)))), LAT.mirror(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, y))}, LAT.fromT(V.Val, ta)}, x))))

def cursor_parts(+t: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +x: U32, +src: U32, +neg: Bool) -> {P.H{KM.MG{RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))}, LAT.fromT(V.Val, ta)} == R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg) : P.H}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)), (Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), LA.get_pair(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))) :
    {P.H{KM.MG{RG.words(R.rg.insert.r(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), s, x))}, LAT.fromT(V.Val, ta)} == R.rg.insert.r(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), s, x) : P.H}
  {==}

def cursor_full(+t: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +x: U32, +src: U32, +neg: Bool, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}) -> {AD.full(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg)), d) == True{} : Bool}:
  +hf3 = LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), src, LA.set_full(U32, LAT.fromT(U32, t), d, x, P.hd2(18, R.cur.form(neg), 0), hft)))
  %Equal.sym(Array<U32> & U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)), (Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), LA.get_pair(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))) :
    {AD.full(U32, RG.words(R.rg.insert.r(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), s, x)), d) == True{} : Bool}
  LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), d, (s + 3 : U32), x, hf3)

def cross_kp(+t: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +x: U32, +src: U32, +neg: Bool, m: Maybe<&2, U32>, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}) -> {P.H{KM.MG{RG.words(R.cross.k((P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, m), s, x, src, neg))}, LAT.fromT(V.Val, ta)} == R.cross.k((P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, m), s, x, src, neg) : P.H}:
  match m:
    case Some{+y}:
      join1_parts(t, ta, d, x, y, hft)
    case None{}:
      cursor_parts(t, ta, d, s, x, src, neg)

def cross_kf(+t: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +x: U32, +src: U32, +neg: Bool, m: Maybe<&2, U32>, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}) -> {AD.full(U32, RG.words(R.cross.k((P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, m), s, x, src, neg)), d) == True{} : Bool}:
  match m:
    case Some{+y}:
      join1_full(t, ta, d, x, y, hft)
    case None{}:
      cursor_full(t, ta, d, s, x, src, neg, hft)

def cross_parts.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +far: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {RG.ring(AD.view(U32, w), d, s, cs) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) -> {P.H{KM.MG{RG.words(R.cross(P.H{KM.MG{w}, a}, s, x, src, neg, far))}, a} == R.cross(P.H{KM.MG{w}, a}, s, x, src, neg, far) : P.H}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  %e : {P.H{KM.MG{RG.words(R.cross(P.H{KM.MG{_}, a}, s, x, src, neg, far))}, a} == R.cross(P.H{KM.MG{_}, a}, s, x, src, neg, far) : P.H}
  %ea : {P.H{KM.MG{RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, t)}, _}, s, x, src, neg, far))}, _} == R.cross(P.H{KM.MG{LAT.fromT(U32, t)}, _}, s, x, src, neg, far) : P.H}
  %Equal.sym(P.H & Maybe<&2, U32>, R.rg.find(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, far), (P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far)), find_exact.m(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, far, hft, hd32, hrt, LAT.mirror(U32, LAT.fromT(U32, t)))) :
    {P.H{KM.MG{RG.words(R.cross.k(_, s, x, src, neg))}, LAT.fromT(V.Val, ta)} == R.cross.k(_, s, x, src, neg) : P.H}
  cross_kp(t, ta, d, s, x, src, neg, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far), hft)

def cross_full.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +far: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {RG.ring(AD.view(U32, w), d, s, cs) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) -> {AD.full(U32, RG.words(R.cross(P.H{KM.MG{w}, a}, s, x, src, neg, far)), d) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, cs) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  %e : {AD.full(U32, RG.words(R.cross(P.H{KM.MG{_}, a}, s, x, src, neg, far)), d) == True{} : Bool}
  %ea : {AD.full(U32, RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, t)}, _}, s, x, src, neg, far)), d) == True{} : Bool}
  %Equal.sym(P.H & Maybe<&2, U32>, R.rg.find(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, far), (P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far)), find_exact.m(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, far, hft, hd32, hrt, LAT.mirror(U32, LAT.fromT(U32, t)))) :
    {AD.full(U32, RG.words(R.cross.k(_, s, x, src, neg)), d) == True{} : Bool}
  cross_kf(t, ta, d, s, x, src, neg, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far), hft)

# A copy's crossings: the positions

# every pending placeholder's word 2 read in the view of the positions:
# the view's setting of a new cursor's position then gives it
def pdef(ps: List<&2, U32>, +pv: List<&2, U32>, +d: Nat) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+p, r}:
      issome(List.get(&2, U32, pv, AD.slot((p + 2 : U32), d))) && pdef(r, pv, d)

def issome_map(m: Maybe<&2, U32>, +v: U32) -> {issome(Maybe.map(&2, U32, U32, z => v, m)) == issome(m) : Bool}:
  match m:
    case Some{+q}:
      {==}
    case None{}:
      {==}

def map_some(m: Maybe<&2, U32>, +v: U32, h: {issome(m) == True{} : Bool}) -> {Maybe.map(&2, U32, U32, z => v, m) == Some{v} : Maybe<&2, U32>}:
  match m:
    case Some{+q}:
      {==}
    case None{}:
      Empty.absurd({Maybe.map(&2, U32, U32, z => v, None{}) == Some{v} : Maybe<&2, U32>}, MB.false_ne_true()(h))

def pd_step(+p: U32, +pv: List<&2, U32>, +d: Nat, +i: Nat, +v: U32, +b: Bool, e: {Nat.is_eq(i, AD.slot((p + 2 : U32), d)) == b : Bool}, +h: {issome(List.get(&2, U32, pv, AD.slot((p + 2 : U32), d))) == True{} : Bool}) ->
    {issome(List.get(&2, U32, List.set(&2, U32, pv, i, v), AD.slot((p + 2 : U32), d))) == True{} : Bool}:
  match b:
    case True{}:
      +eq = MN.eq_of_is_eq(i, AD.slot((p + 2 : U32), d), e)
      %Equal.sym(Nat, i, AD.slot((p + 2 : U32), d), eq) :
        {issome(List.get(&2, U32, List.set(&2, U32, pv, _, v), AD.slot((p + 2 : U32), d))) == True{} : Bool}
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, pv, AD.slot((p + 2 : U32), d), v), AD.slot((p + 2 : U32), d)), Maybe.map(&2, U32, U32, z => v, List.get(&2, U32, pv, AD.slot((p + 2 : U32), d))), ML.get_set_self(&2, U32, pv, AD.slot((p + 2 : U32), d), v)) :
        {issome(_) == True{} : Bool}
      Equal.trans(Bool, issome(Maybe.map(&2, U32, U32, z => v, List.get(&2, U32, pv, AD.slot((p + 2 : U32), d)))), issome(List.get(&2, U32, pv, AD.slot((p + 2 : U32), d))), True{}, issome_map(List.get(&2, U32, pv, AD.slot((p + 2 : U32), d)), v), h)
    case False{}:
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, pv, i, v), AD.slot((p + 2 : U32), d)), List.get(&2, U32, pv, AD.slot((p + 2 : U32), d)), LAB.get_set_ne(U32, pv, i, AD.slot((p + 2 : U32), d), v, e)) :
        {issome(_) == True{} : Bool}
      h

def pdef_set(ps: List<&2, U32>, +pv: List<&2, U32>, +d: Nat, +i: Nat, +v: U32, +h: {pdef(ps, pv, d) == True{} : Bool}) -> {pdef(ps, List.set(&2, U32, pv, i, v), d) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +r}:
      MB.and_eq_true(issome(List.get(&2, U32, List.set(&2, U32, pv, i, v), AD.slot((p + 2 : U32), d))), pdef(r, List.set(&2, U32, pv, i, v), d), pd_step(p, pv, d, i, v, Nat.is_eq(i, AD.slot((p + 2 : U32), d)), {==}, MB.eq_true_of_and_left(issome(List.get(&2, U32, pv, AD.slot((p + 2 : U32), d))), pdef(r, pv, d), h)), pdef_set(r, pv, d, i, v, MB.eq_true_of_and_right(issome(List.get(&2, U32, pv, AD.slot((p + 2 : U32), d))), pdef(r, pv, d), h)))

def pv_one(+p: U32, +t: LAT.Tree<U32>, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
    {issome(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 2 : U32), d))) == True{} : Bool}:
  %LA.get_view(U32, LAT.fromT(U32, t), d, (p + 2 : U32), hft, hd32) :
    {issome(_) == True{} : Bool}
  {==}

def pdef_view(ps: List<&2, U32>, +t: LAT.Tree<U32>, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
    {pdef(ps, AD.view(U32, LAT.fromT(U32, t)), d) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +r}:
      MB.and_eq_true(issome(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((p + 2 : U32), d))), pdef(r, AD.view(U32, LAT.fromT(U32, t)), d), pv_one(p, t, d, hft, hd32), pdef_view(r, t, d, hft, hd32))

# agreement at a member, over a part, and carried over equal reads
def agree_at(M: List<&2, U32>, +v1: List<&2, U32>, +v2: List<&2, U32>, +d: Nat, +m: U32, +h: {RG.agree(M, v1, v2, d) == True{} : Bool}, hm: {RG.has(M, m) == True{} : Bool}) ->
    {RG.meq(List.get(&2, U32, v1, AD.slot((m + 2 : U32), d)), List.get(&2, U32, v2, AD.slot((m + 2 : U32), d))) == True{} : Bool}:
  match M:
    case Nil{}:
      Empty.absurd({RG.meq(List.get(&2, U32, v1, AD.slot((m + 2 : U32), d)), List.get(&2, U32, v2, AD.slot((m + 2 : U32), d))) == True{} : Bool}, MB.false_ne_true()(hm))
    case Con{+c, +r}:
      or_cases(U32.is_eq(c, m), RG.has(r, m), RG.meq(List.get(&2, U32, v1, AD.slot((m + 2 : U32), d)), List.get(&2, U32, v2, AD.slot((m + 2 : U32), d))), hm,
        q => ME.subst(U32, k => {RG.meq(List.get(&2, U32, v1, AD.slot((k + 2 : U32), d)), List.get(&2, U32, v2, AD.slot((k + 2 : U32), d))) == True{} : Bool}, c, m, MS.u32_eq_of_is_eq(c, m, q), MB.eq_true_of_and_left(RG.meq(List.get(&2, U32, v1, AD.slot((c + 2 : U32), d)), List.get(&2, U32, v2, AD.slot((c + 2 : U32), d))), RG.agree(r, v1, v2, d), h)),
        hh => agree_at(r, v1, v2, d, m, MB.eq_true_of_and_right(RG.meq(List.get(&2, U32, v1, AD.slot((c + 2 : U32), d)), List.get(&2, U32, v2, AD.slot((c + 2 : U32), d))), RG.agree(r, v1, v2, d), h), hh))

def agree_sub(K: List<&2, U32>, +M: List<&2, U32>, +v1: List<&2, U32>, +v2: List<&2, U32>, +d: Nat, +hs: {RG.sub(K, M) == True{} : Bool}, +h: {RG.agree(M, v1, v2, d) == True{} : Bool}) ->
    {RG.agree(K, v1, v2, d) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(RG.meq(List.get(&2, U32, v1, AD.slot((m + 2 : U32), d)), List.get(&2, U32, v2, AD.slot((m + 2 : U32), d))), RG.agree(r, v1, v2, d), agree_at(M, v1, v2, d, m, h, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hs)), agree_sub(r, M, v1, v2, d, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hs), h))

def meq_tr2(+a1: Maybe<&2, U32>, +a2: Maybe<&2, U32>, +b1: Maybe<&2, U32>, +b2: Maybe<&2, U32>, +ea: {a1 == a2 : Maybe<&2, U32>}, +eb: {b1 == b2 : Maybe<&2, U32>}, +h: {RG.meq(a2, b2) == True{} : Bool}) -> {RG.meq(a1, b1) == True{} : Bool}:
  ME.subst(Maybe<&2, U32>, q => {RG.meq(a1, q) == True{} : Bool}, b2, b1, Equal.sym(Maybe<&2, U32>, b1, b2, eb), ME.subst(Maybe<&2, U32>, q => {RG.meq(q, b2) == True{} : Bool}, a2, a1, Equal.sym(Maybe<&2, U32>, a1, a2, ea), h))

# a node's four words off j, as a law states it, from its layout's form
def off_node_of(+d: Nat, +m: U32, +j: U32, +h: {RG.off(RG.nw(m), d, j) == True{} : Bool}) -> {RG.off.node(d, m, j) == True{} : Bool}:
  MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))), Bool.and(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), Bool.and(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d))))), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))), RG.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, j), h), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), Bool.and(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d)))), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), RG.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))), RG.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, j), h)), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d))), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), RG.off(Con{(m + 3 : U32), Nil{}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), RG.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))), RG.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, j), h))), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d))), RG.off(Nil{}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), RG.off(Con{(m + 3 : U32), Nil{}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), RG.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))), RG.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, j), h)))))))

# a node's word 2 off every listed node's word 3, the list laid out
def l2_step(+m: U32, +p: U32, +d: Nat, +M: List<&2, U32>, +b: Bool, e: {U32.is_eq(m, p) == b : Bool},
    +h: {RG.layout(M, d) == True{} : Bool}, +hm: {RG.has(M, m) == True{} : Bool}, +hp: {RG.has(M, p) == True{} : Bool}) -> {Bool.not(Nat.is_eq(AD.slot((p + 2 : U32), d), AD.slot((m + 3 : U32), d))) == True{} : Bool}:
  match b:
    case True{}:
      ME.subst(U32, q => {Bool.not(Nat.is_eq(AD.slot((p + 2 : U32), d), AD.slot((q + 3 : U32), d))) == True{} : Bool}, p, m, Equal.sym(U32, m, p, MS.u32_eq_of_is_eq(m, p, e)), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((p + 3 : U32), d), AD.slot((p + 2 : U32), d)), Nat.is_eq(AD.slot((p + 2 : U32), d), AD.slot((p + 3 : U32), d)), MN.is_eq_comm(AD.slot((p + 3 : U32), d), AD.slot((p + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((p + 3 : U32), d), AD.slot((p + 2 : U32), d))), RG.off(Nil{}, d, (p + 2 : U32)), MB.eq_true_of_and_left(RG.off(Con{(p + 3 : U32), Nil{}}, d, (p + 2 : U32)), RG.apartw(Con{(p + 3 : U32), Nil{}}, d), MB.eq_true_of_and_right(RG.off(Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}, d, (p + 1 : U32)), RG.apartw(Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}, d), MB.eq_true_of_and_right(RG.off(Con{(p + 1 : U32), Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}}, d, p), RG.apartw(Con{(p + 1 : U32), Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}}, d), lay_self(M, d, p, h, hp)))))))
    case False{}:
      MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((p + 2 : U32), d), AD.slot((m + 3 : U32), d))), RG.off(Con{(p + 3 : U32), Nil{}}, d, (m + 3 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((p + 1 : U32), d), AD.slot((m + 3 : U32), d))), RG.off(Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}, d, (m + 3 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(p, d), AD.slot((m + 3 : U32), d))), RG.off(Con{(p + 1 : U32), Con{(p + 2 : U32), Con{(p + 3 : U32), Nil{}}}}, d, (m + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(p), d, (m + 2 : U32)), RG.off(RG.nw(p), d, (m + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(p), d, (m + 1 : U32)), Bool.and(RG.off(RG.nw(p), d, (m + 2 : U32)), RG.off(RG.nw(p), d, (m + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(p), d, m), Bool.and(RG.off(RG.nw(p), d, (m + 1 : U32)), Bool.and(RG.off(RG.nw(p), d, (m + 2 : U32)), RG.off(RG.nw(p), d, (m + 3 : U32)))), lay_pair(M, d, m, p, h, hm, hp, e)))))))

def links_p2(K: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +p: U32, +hk: {RG.sub(K, M) == True{} : Bool}, +h: {RG.layout(M, d) == True{} : Bool}, +hp: {RG.has(M, p) == True{} : Bool}) ->
    {RG.off.links(K, d, (p + 2 : U32)) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((p + 2 : U32), d), AD.slot((m + 3 : U32), d))), RG.off.links(r, d, (p + 2 : U32)), l2_step(m, p, d, M, U32.is_eq(m, p), {==}, h, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hk), hp), links_p2(r, M, d, p, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hk), h, hp))

# A copy's crossings: the positions through a crossing

# the cursor's four writes leave every other word
def cur_get(+t: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +x: U32, +src: U32, +neg: Bool, +j: U32, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +h0: {Nat.is_eq(AD.slot(x, d), AD.slot(j, d)) == False{} : Bool}, +h2: {Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(j, d)) == False{} : Bool}, +h3: {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hs3: {Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}) ->
    {List.get(&2, U32, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), AD.slot(j, d)) == List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(j, d)) : Maybe<&2, U32>}:
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t), d, x, P.hd2(18, R.cur.form(neg), 0), hft)
  +hf2 = LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), src, hf1)
  +hf3 = LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))), hf2)
  %Equal.sym(Array<U32> & U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)), (Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), LA.get_pair(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))) :
    {List.get(&2, U32, AD.view(U32, RG.words(R.rg.insert.r(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), s, x))), AD.slot(j, d)) == List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(j, d)) : Maybe<&2, U32>}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), (s + 3 : U32), x)), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))))), AD.slot((s + 3 : U32), d), x), LA.set_view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), d, (s + 3 : U32), x, hf3, hd32)) :
    {List.get(&2, U32, _, AD.slot(j, d)) == List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(j, d)) : Maybe<&2, U32>}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))))), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), LA.set_view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))), hf2, hd32)) :
    {List.get(&2, U32, List.set(&2, U32, _, AD.slot((s + 3 : U32), d), x), AD.slot(j, d)) == List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(j, d)) : Maybe<&2, U32>}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), AD.slot((x + 2 : U32), d), src), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), src, hf1, hd32)) :
    {List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, _, AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), AD.slot(j, d)) == List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(j, d)) : Maybe<&2, U32>}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), LA.set_view(U32, LAT.fromT(U32, t), d, x, P.hd2(18, R.cur.form(neg), 0), hft, hd32)) :
    {List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, _, AD.slot((x + 2 : U32), d), src), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), AD.slot(j, d)) == List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(j, d)) : Maybe<&2, U32>}
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), AD.slot(j, d)), List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), AD.slot(j, d)), List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(j, d)), LAB.get_set_ne(U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), AD.slot(j, d), x, hs3),
    Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), AD.slot(j, d)), List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src), AD.slot(j, d)), List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(j, d)), LAB.get_set_ne(U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src), AD.slot((x + 3 : U32), d), AD.slot(j, d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))), h3),
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src), AD.slot(j, d)), List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot(j, d)), List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(j, d)), LAB.get_set_ne(U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), AD.slot(j, d), src, h2), LAB.get_set_ne(U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), AD.slot(j, d), P.hd2(18, R.cur.form(neg), 0), h0))))

# and the cursor reads its position at its word 2
def cur_x(+t: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +x: U32, +src: U32, +neg: Bool, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hxx: {Nat.is_eq(AD.slot(x, d), AD.slot((x + 2 : U32), d)) == False{} : Bool}, +h3x: {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((x + 2 : U32), d)) == False{} : Bool}, +hsx: {Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((x + 2 : U32), d)) == False{} : Bool}) ->
    {List.get(&2, U32, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), AD.slot((x + 2 : U32), d)) == Some{src} : Maybe<&2, U32>}:
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t), d, x, P.hd2(18, R.cur.form(neg), 0), hft)
  +hf2 = LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), src, hf1)
  +hf3 = LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))), hf2)
  %Equal.sym(Array<U32> & U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)), (Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), LA.get_pair(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))) :
    {List.get(&2, U32, AD.view(U32, RG.words(R.rg.insert.r(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), s, x))), AD.slot((x + 2 : U32), d)) == Some{src} : Maybe<&2, U32>}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), (s + 3 : U32), x)), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))))), AD.slot((s + 3 : U32), d), x), LA.set_view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), d, (s + 3 : U32), x, hf3, hd32)) :
    {List.get(&2, U32, _, AD.slot((x + 2 : U32), d)) == Some{src} : Maybe<&2, U32>}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))))), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), LA.set_view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))), hf2, hd32)) :
    {List.get(&2, U32, List.set(&2, U32, _, AD.slot((s + 3 : U32), d), x), AD.slot((x + 2 : U32), d)) == Some{src} : Maybe<&2, U32>}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), AD.slot((x + 2 : U32), d), src), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), src, hf1, hd32)) :
    {List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, _, AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), AD.slot((x + 2 : U32), d)) == Some{src} : Maybe<&2, U32>}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), LA.set_view(U32, LAT.fromT(U32, t), d, x, P.hd2(18, R.cur.form(neg), 0), hft, hd32)) :
    {List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, _, AD.slot((x + 2 : U32), d), src), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), AD.slot((x + 2 : U32), d)) == Some{src} : Maybe<&2, U32>}
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), x), AD.slot((x + 2 : U32), d)), List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), AD.slot((x + 2 : U32), d)), Some{src}, LAB.get_set_ne(U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), AD.slot((s + 3 : U32), d), AD.slot((x + 2 : U32), d), x, hsx),
    Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32)))), AD.slot((x + 2 : U32), d)), List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src), AD.slot((x + 2 : U32), d)), Some{src}, LAB.get_set_ne(U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src), AD.slot((x + 3 : U32), d), AD.slot((x + 2 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), (s + 3 : U32))), h3x),
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src), AD.slot((x + 2 : U32), d)), Maybe.map(&2, U32, U32, z => src, List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d))), Some{src}, ML.get_set_self(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d), src),
        ME.subst(Maybe<&2, U32>, qq => {Maybe.map(&2, U32, U32, z => src, qq) == Some{src} : Maybe<&2, U32>}, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 2 : U32)))}, List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d)), Equal.trans(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 2 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 2 : U32), d)), List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (x + 2 : U32), hft, hd32), Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.slot((x + 2 : U32), d)), List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 2 : U32), d)), LAB.get_set_ne(U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), AD.slot((x + 2 : U32), d), P.hd2(18, R.cur.form(neg), 0), hxx))), {==}))))

def meq_self(+v: U32) -> {RG.meq(Some{v}, Some{v}) == True{} : Bool}:
  Equal.trans(Bool, U32.is_eq(v, v), Nat.is_eq(U32.to_nat(v), U32.to_nat(v)), True{}, MU.u32_is_eq_to_nat(v, v), MN.is_eq_refl(U32.to_nat(v)))

# the members' positions agreeing through a cursor made, the view of
# the positions given the cursor's
def agree_cur(K: List<&2, U32>, +L: List<&2, U32>, +t: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +x: U32, +src: U32, +neg: Bool, +pv: List<&2, U32>, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hl: {RG.layout(L, d) == True{} : Bool}, +hsK: {RG.sub(K, L) == True{} : Bool}, +hsL: {RG.has(L, s) == True{} : Bool}, +hxL: {RG.has(L, x) == True{} : Bool},
    +hKx: {RG.has(K, x) == False{} : Bool}, +hKs: {RG.has(K, s) == False{} : Bool}, +hag: {RG.agree(K, AD.view(U32, LAT.fromT(U32, t)), pv, d) == True{} : Bool}) ->
    {RG.agree(K, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), List.set(&2, U32, pv, AD.slot((x + 2 : U32), d), src), d) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      +hm = MB.eq_true_of_and_left(RG.has(L, m), RG.sub(r, L), hsK)
      +ox = MB.eq_true_of_and_left(RG.off(RG.nw(x), d, (m + 2 : U32)), RG.off(RG.nw(x), d, (m + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(x), d, (m + 1 : U32)), Bool.and(RG.off(RG.nw(x), d, (m + 2 : U32)), RG.off(RG.nw(x), d, (m + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(x), d, m), Bool.and(RG.off(RG.nw(x), d, (m + 1 : U32)), Bool.and(RG.off(RG.nw(x), d, (m + 2 : U32)), RG.off(RG.nw(x), d, (m + 3 : U32)))), lay_pair(L, d, m, x, hl, hm, hxL, or_false_l(U32.is_eq(m, x), RG.has(r, x), hKx)))))
      +os = MB.eq_true_of_and_left(RG.off(RG.nw(s), d, (m + 2 : U32)), RG.off(RG.nw(s), d, (m + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(s), d, (m + 1 : U32)), Bool.and(RG.off(RG.nw(s), d, (m + 2 : U32)), RG.off(RG.nw(s), d, (m + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(s), d, m), Bool.and(RG.off(RG.nw(s), d, (m + 1 : U32)), Bool.and(RG.off(RG.nw(s), d, (m + 2 : U32)), RG.off(RG.nw(s), d, (m + 3 : U32)))), lay_pair(L, d, m, s, hl, hm, hsL, or_false_l(U32.is_eq(m, s), RG.has(r, s), hKs)))))
      +eV = cur_get(t, ta, d, s, x, src, neg, (m + 2 : U32), hft, hd32, MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(x, d), AD.slot((m + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(x, d), AD.slot((m + 2 : U32), d))), RG.off(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d, (m + 2 : U32)), ox)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot((m + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot((m + 2 : U32), d))), RG.off(Con{(x + 3 : U32), Nil{}}, d, (m + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot((m + 2 : U32), d))), RG.off(Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}, d, (m + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(x, d), AD.slot((m + 2 : U32), d))), RG.off(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d, (m + 2 : U32)), ox)))), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((m + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((m + 2 : U32), d))), RG.off(Nil{}, d, (m + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot((m + 2 : U32), d))), RG.off(Con{(x + 3 : U32), Nil{}}, d, (m + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot((m + 2 : U32), d))), RG.off(Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}, d, (m + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(x, d), AD.slot((m + 2 : U32), d))), RG.off(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d, (m + 2 : U32)), ox))))), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((m + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((m + 2 : U32), d))), RG.off(Nil{}, d, (m + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((s + 2 : U32), d), AD.slot((m + 2 : U32), d))), RG.off(Con{(s + 3 : U32), Nil{}}, d, (m + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((s + 1 : U32), d), AD.slot((m + 2 : U32), d))), RG.off(Con{(s + 2 : U32), Con{(s + 3 : U32), Nil{}}}, d, (m + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(s, d), AD.slot((m + 2 : U32), d))), RG.off(Con{(s + 1 : U32), Con{(s + 2 : U32), Con{(s + 3 : U32), Nil{}}}}, d, (m + 2 : U32)), os))))))
      +eP = LAB.get_set_ne(U32, pv, AD.slot((x + 2 : U32), d), AD.slot((m + 2 : U32), d), src, MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot((m + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot((m + 2 : U32), d))), RG.off(Con{(x + 3 : U32), Nil{}}, d, (m + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot((m + 2 : U32), d))), RG.off(Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}, d, (m + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(x, d), AD.slot((m + 2 : U32), d))), RG.off(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d, (m + 2 : U32)), ox)))))
      MB.and_eq_true(RG.meq(List.get(&2, U32, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), AD.slot((m + 2 : U32), d)), List.get(&2, U32, List.set(&2, U32, pv, AD.slot((x + 2 : U32), d), src), AD.slot((m + 2 : U32), d))), RG.agree(r, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), List.set(&2, U32, pv, AD.slot((x + 2 : U32), d), src), d), meq_tr2(List.get(&2, U32, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), AD.slot((m + 2 : U32), d)), List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m + 2 : U32), d)), List.get(&2, U32, List.set(&2, U32, pv, AD.slot((x + 2 : U32), d), src), AD.slot((m + 2 : U32), d)), List.get(&2, U32, pv, AD.slot((m + 2 : U32), d)), eV, eP, MB.eq_true_of_and_left(RG.meq(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m + 2 : U32), d)), List.get(&2, U32, pv, AD.slot((m + 2 : U32), d))), RG.agree(r, AD.view(U32, LAT.fromT(U32, t)), pv, d), hag)), agree_cur(r, L, t, ta, d, s, x, src, neg, pv, hft, hd32, hl, MB.eq_true_of_and_right(RG.has(L, m), RG.sub(r, L), hsK), hsL, hxL, or_false_r(U32.is_eq(m, x), RG.has(r, x), hKx), or_false_r(U32.is_eq(m, s), RG.has(r, s), hKs), MB.eq_true_of_and_right(RG.meq(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m + 2 : U32), d)), List.get(&2, U32, pv, AD.slot((m + 2 : U32), d))), RG.agree(r, AD.view(U32, LAT.fromT(U32, t)), pv, d), hag)))

# the members' positions agreeing through a join, each member's word 2
# kept by join1_keeps, its premises on the faced ports from port.ok
def agree_join(K: List<&2, U32>, +L: List<&2, U32>, +t: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +x: U32, +y: U32, +pv: List<&2, U32>, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hr0: {RG.ring.ok(AD.view(U32, LAT.fromT(U32, t)), d, s, cs) == True{} : Bool}, +hx0: {RG.node.ok(AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}, x) == True{} : Bool}, +hy: {RG.has(cs, y) == True{} : Bool},
    +hl: {RG.layout(L, d) == True{} : Bool}, +hsK: {RG.sub(K, L) == True{} : Bool}, +hsC: {RG.sub(Con{s, cs}, L) == True{} : Bool}, +hxL: {RG.has(L, x) == True{} : Bool}, +hyL: {RG.has(L, y) == True{} : Bool},
    +hKx: {RG.has(K, x) == False{} : Bool}, +hKy: {RG.has(K, y) == False{} : Bool},
    +hpu: {RG.port.ok(L, d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))) == True{} : Bool}, +hpw: {RG.port.ok(L, d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32)))) == True{} : Bool}, +hag: {RG.agree(K, AD.view(U32, LAT.fromT(U32, t)), pv, d) == True{} : Bool}) ->
    {RG.agree(K, AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))), pv, d) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      +hm = MB.eq_true_of_and_left(RG.has(L, m), RG.sub(r, L), hsK)
      +hmx = or_false_l(U32.is_eq(m, x), RG.has(r, x), hKx)
      +hmy = or_false_l(U32.is_eq(m, y), RG.has(r, y), hKy)
      +hj = links_p2(Con{s, cs}, L, d, m, hsC, hl, hm)
      +hjx = off_node_of(d, x, (m + 2 : U32), MB.eq_true_of_and_left(RG.off(RG.nw(x), d, (m + 2 : U32)), RG.off(RG.nw(x), d, (m + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(x), d, (m + 1 : U32)), Bool.and(RG.off(RG.nw(x), d, (m + 2 : U32)), RG.off(RG.nw(x), d, (m + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(x), d, m), Bool.and(RG.off(RG.nw(x), d, (m + 1 : U32)), Bool.and(RG.off(RG.nw(x), d, (m + 2 : U32)), RG.off(RG.nw(x), d, (m + 3 : U32)))), lay_pair(L, d, m, x, hl, hm, hxL, hmx)))))
      +hjy = off_node_of(d, y, (m + 2 : U32), MB.eq_true_of_and_left(RG.off(RG.nw(y), d, (m + 2 : U32)), RG.off(RG.nw(y), d, (m + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(y), d, (m + 1 : U32)), Bool.and(RG.off(RG.nw(y), d, (m + 2 : U32)), RG.off(RG.nw(y), d, (m + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(y), d, m), Bool.and(RG.off(RG.nw(y), d, (m + 1 : U32)), Bool.and(RG.off(RG.nw(y), d, (m + 2 : U32)), RG.off(RG.nw(y), d, (m + 3 : U32)))), lay_pair(L, d, m, y, hl, hm, hyL, hmy)))))
      +hjh = Equal.trans(Bool, Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((m + 2 : U32), d)), Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(P.at_fh(), d)), False{}, MN.is_eq_comm(AD.slot(P.at_fh(), d), AD.slot((m + 2 : U32), d)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(P.at_fh(), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(P.at_fh(), d))), RG.off(Con{(m + 3 : U32), Nil{}}, d, P.at_fh()), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(P.at_fh(), d))), RG.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, P.at_fh()), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(P.at_fh(), d))), RG.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, P.at_fh()), lay_head(L, d, m, hl, hm))))))
      +hju = MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32), d), AD.slot((m + 2 : U32), d)), pos_at(L, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32), m, MB.eq_true_of_and_right(RG.off.links(L, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), RG.off.pos(L, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), hpu), hm))
      +hjw = MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32), d), AD.slot((m + 2 : U32), d)), pos_at(L, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32), m, MB.eq_true_of_and_right(RG.off.links(L, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32)), RG.off.pos(L, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (y + 1 : U32))) + 1 : U32)), hpw), hm))
      +keep = join1_keeps.m(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, x, y, (m + 2 : U32), hft, hd32, hr0, hx0, hy, hj, hjx, hjy, hjh, hju, hjw, LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
      +hfJ = join1_full(t, ta, d, x, y, hft)
      +eb = Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y)), (m + 2 : U32))), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))}, LAT.fromT(V.Val, ta)}, (m + 2 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m + 2 : U32))), Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))}, LAT.fromT(V.Val, ta)}, (m + 2 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y)), (m + 2 : U32))), rd_get(RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y)), LAT.fromT(V.Val, ta), (m + 2 : U32))),
        Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))}, LAT.fromT(V.Val, ta)}, (m + 2 : U32))), Pair.snd(P.H, U32, P.rd(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y), (m + 2 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m + 2 : U32))), ME.subst(P.H, hh => {Pair.snd(P.H, U32, P.rd(P.H{KM.MG{RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))}, LAT.fromT(V.Val, ta)}, (m + 2 : U32))) == Pair.snd(P.H, U32, P.rd(hh, (m + 2 : U32))) : U32}, P.H{KM.MG{RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))}, LAT.fromT(V.Val, ta)}, R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y), join1_parts(t, ta, d, x, y, hft), {==}),
          Equal.trans(U32, Pair.snd(P.H, U32, P.rd(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y), (m + 2 : U32))), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, (m + 2 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m + 2 : U32))), keep, rd_get(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), (m + 2 : U32)))))
      +eV = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))), AD.slot((m + 2 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y)), (m + 2 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m + 2 : U32), d)), Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y)), (m + 2 : U32)))}, List.get(&2, U32, AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))), AD.slot((m + 2 : U32), d)), LA.get_view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y)), d, (m + 2 : U32), hfJ, hd32)),
        Equal.trans(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y)), (m + 2 : U32)))}, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m + 2 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m + 2 : U32), d)), ME.subst(U32, k => {Some{Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y)), (m + 2 : U32)))} == Some{k} : Maybe<&2, U32>}, Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y)), (m + 2 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m + 2 : U32))), eb, {==}), LA.get_view(U32, LAT.fromT(U32, t), d, (m + 2 : U32), hft, hd32)))
      MB.and_eq_true(RG.meq(List.get(&2, U32, AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))), AD.slot((m + 2 : U32), d)), List.get(&2, U32, pv, AD.slot((m + 2 : U32), d))), RG.agree(r, AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))), pv, d), meq_tr2(List.get(&2, U32, AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x, y))), AD.slot((m + 2 : U32), d)), List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m + 2 : U32), d)), List.get(&2, U32, pv, AD.slot((m + 2 : U32), d)), List.get(&2, U32, pv, AD.slot((m + 2 : U32), d)), eV, {==}, MB.eq_true_of_and_left(RG.meq(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m + 2 : U32), d)), List.get(&2, U32, pv, AD.slot((m + 2 : U32), d))), RG.agree(r, AD.view(U32, LAT.fromT(U32, t)), pv, d), hag)), agree_join(r, L, t, ta, d, s, cs, x, y, pv, hft, hd32, hr0, hx0, hy, hl, MB.eq_true_of_and_right(RG.has(L, m), RG.sub(r, L), hsK), hsC, hxL, hyL, or_false_r(U32.is_eq(m, x), RG.has(r, x), hKx), or_false_r(U32.is_eq(m, y), RG.has(r, y), hKy), hpu, hpw, MB.eq_true_of_and_right(RG.meq(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m + 2 : U32), d)), List.get(&2, U32, pv, AD.slot((m + 2 : U32), d))), RG.agree(r, AD.view(U32, LAT.fromT(U32, t)), pv, d), hag)))

# A copy's crossings: the fold

# the agreement after a crossing, by what the find's model found
def crs_agree.k(+tw: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +rt: List<&2, U32>, +L: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +far: U32, +pv: List<&2, U32>,
    m: Maybe<&2, U32>, e: {RG.first(rt, AD.view(U32, LAT.fromT(U32, tw)), d, far) == m : Maybe<&2, U32>}, +hft: {AD.full(U32, LAT.fromT(U32, tw), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hp5: {RG.layout(L, d) == True{} : Bool}, +hp1: {RG.sub(Con{s, rt}, L) == True{} : Bool}, +hp7: {RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L) == True{} : Bool}, +hsL: {RG.has(L, s) == True{} : Bool}, +hcsL: {RG.sub(rt, L) == True{} : Bool}, +hxL: {RG.has(L, x) == True{} : Bool}, +hxout: {RG.has(Con{s, rt}, x) == False{} : Bool}, +hns: {RG.has(rt, s) == False{} : Bool}, +hxrt: {RG.has(rt, x) == False{} : Bool}, +hr0: {RG.ring.ok(AD.view(U32, LAT.fromT(U32, tw)), d, s, rt) == True{} : Bool}, +hx0: {RG.node.ok(AD.view(U32, LAT.fromT(U32, tw)), d, Con{s, rt}, x) == True{} : Bool}, +hpu: {RG.port.ok(L, d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tw), (x + 1 : U32)))) == True{} : Bool},
    +hag: {RG.agree(rt, AD.view(U32, LAT.fromT(U32, tw)), pv, d) == True{} : Bool}, +hpd0: {issome(List.get(&2, U32, pv, AD.slot((x + 2 : U32), d))) == True{} : Bool}) ->
    {RG.agree(RG.cross.t(m, x, rt), AD.view(U32, RG.words(R.cross.k((P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, m), s, x, src, neg))), RG.cr.pv(m, x, src, pv, d), d) == True{} : Bool}:
  match m:
    case Some{+y}:
      +hy = first_has(rt, AD.view(U32, LAT.fromT(U32, tw)), d, far, y, e)
      +hyL = sub_has(Con{s, rt}, L, y, hp1, has_cons(s, rt, y, hy))
      +hpw = LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, L) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tw)), AD.slot((y + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tw), (y + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tw), (y + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tw)), AD.slot((y + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, tw), d, (y + 1 : U32), hft, hd32)), faces_at(L, AD.view(U32, LAT.fromT(U32, tw)), d, L, y, hp7, hyL))
      agree_join(RG.without(rt, y), L, tw, ta, d, s, rt, x, y, pv, hft, hd32, hr0, hx0, hy, hp5, sub_trans(RG.without(rt, y), rt, L, sub_without(rt, y), hcsL), hp1, hxL, hyL,
        notin_sub(RG.without(rt, y), rt, x, sub_without(rt, y), hxrt), notin_without(rt, y), hpu, hpw, agree_sub(RG.without(rt, y), rt, AD.view(U32, LAT.fromT(U32, tw)), pv, d, sub_without(rt, y), hag))
    case None{}:
      +ex = cur_x(tw, ta, d, s, x, src, neg, hft, hd32, Equal.trans(Bool, Nat.is_eq(AD.slot(x, d), AD.slot((x + 2 : U32), d)), Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(x, d)), False{}, MN.is_eq_comm(AD.slot(x, d), AD.slot((x + 2 : U32), d)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(x, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(x, d))), RG.off(Con{(x + 3 : U32), Nil{}}, d, x), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(x, d))), RG.off(Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}, d, x), MB.eq_true_of_and_left(RG.off(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d, x), RG.apartw(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d), lay_self(L, d, x, hp5, hxL)))))), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((x + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((x + 2 : U32), d))), RG.off(Nil{}, d, (x + 2 : U32)), MB.eq_true_of_and_left(RG.off(Con{(x + 3 : U32), Nil{}}, d, (x + 2 : U32)), RG.apartw(Con{(x + 3 : U32), Nil{}}, d), MB.eq_true_of_and_right(RG.off(Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}, d, (x + 1 : U32)), RG.apartw(Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}, d), MB.eq_true_of_and_right(RG.off(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d, x), RG.apartw(Con{(x + 1 : U32), Con{(x + 2 : U32), Con{(x + 3 : U32), Nil{}}}}, d), lay_self(L, d, x, hp5, hxL)))))), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((x + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((x + 2 : U32), d))), RG.off(Nil{}, d, (x + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((s + 2 : U32), d), AD.slot((x + 2 : U32), d))), RG.off(Con{(s + 3 : U32), Nil{}}, d, (x + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((s + 1 : U32), d), AD.slot((x + 2 : U32), d))), RG.off(Con{(s + 2 : U32), Con{(s + 3 : U32), Nil{}}}, d, (x + 2 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(s, d), AD.slot((x + 2 : U32), d))), RG.off(Con{(s + 1 : U32), Con{(s + 2 : U32), Con{(s + 3 : U32), Nil{}}}}, d, (x + 2 : U32)), MB.eq_true_of_and_left(RG.off(RG.nw(s), d, (x + 2 : U32)), RG.off(RG.nw(s), d, (x + 3 : U32)), MB.eq_true_of_and_right(RG.off(RG.nw(s), d, (x + 1 : U32)), Bool.and(RG.off(RG.nw(s), d, (x + 2 : U32)), RG.off(RG.nw(s), d, (x + 3 : U32))), MB.eq_true_of_and_right(RG.off(RG.nw(s), d, x), Bool.and(RG.off(RG.nw(s), d, (x + 1 : U32)), Bool.and(RG.off(RG.nw(s), d, (x + 2 : U32)), RG.off(RG.nw(s), d, (x + 3 : U32)))), lay_pair(L, d, x, s, hp5, hxL, hsL, ueq_ne(s, x, or_false_l(U32.is_eq(s, x), RG.has(rt, x), hxout))))))))))))
      +ep = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, pv, AD.slot((x + 2 : U32), d), src), AD.slot((x + 2 : U32), d)), Maybe.map(&2, U32, U32, z => src, List.get(&2, U32, pv, AD.slot((x + 2 : U32), d))), Some{src}, ML.get_set_self(&2, U32, pv, AD.slot((x + 2 : U32), d), src), map_some(List.get(&2, U32, pv, AD.slot((x + 2 : U32), d)), src, hpd0))
      MB.and_eq_true(RG.meq(List.get(&2, U32, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), AD.slot((x + 2 : U32), d)), List.get(&2, U32, List.set(&2, U32, pv, AD.slot((x + 2 : U32), d), src), AD.slot((x + 2 : U32), d))), RG.agree(rt, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), List.set(&2, U32, pv, AD.slot((x + 2 : U32), d), src), d), meq_tr2(List.get(&2, U32, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), AD.slot((x + 2 : U32), d)), Some{src}, List.get(&2, U32, List.set(&2, U32, pv, AD.slot((x + 2 : U32), d), src), AD.slot((x + 2 : U32), d)), Some{src}, ex, ep, meq_self(src)), agree_cur(rt, L, tw, ta, d, s, x, src, neg, pv, hft, hd32, hp5, hcsL, hsL, hxL, hxrt, hns, hag))

def crs_agree(+tw: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +rt: List<&2, U32>, +ps: List<&2, U32>, +L: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +far: U32, +pv: List<&2, U32>,
    +m: Maybe<&2, U32>, +e: {RG.first(rt, AD.view(U32, LAT.fromT(U32, tw)), d, far) == m : Maybe<&2, U32>}, +hft: {AD.full(U32, LAT.fromT(U32, tw), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hp2: {RG.pend.ok(AD.view(U32, LAT.fromT(U32, tw)), d, s, rt, Con{x, ps}, L) == True{} : Bool},
    +hag: {RG.agree(rt, AD.view(U32, LAT.fromT(U32, tw)), pv, d) == True{} : Bool}, +hpd0: {issome(List.get(&2, U32, pv, AD.slot((x + 2 : U32), d))) == True{} : Bool}) ->
    {RG.agree(RG.cross.t(m, x, rt), AD.view(U32, RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, x, src, neg, far))), RG.cr.pv(m, x, src, pv, d), d) == True{} : Bool}:
  +hp0 = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, tw)), d, s, rt), Bool.and(RG.sub(Con{s, rt}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, rt}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L))))))), hp2)
  +hpr0 = MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, tw)), d, s, rt), Bool.and(RG.sub(Con{s, rt}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, rt}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L))))))), hp2)
  +hp1 = MB.eq_true_of_and_left(RG.sub(Con{s, rt}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, rt}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L)))))), hpr0)
  +hpr1 = MB.eq_true_of_and_right(RG.sub(Con{s, rt}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, rt}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L)))))), hpr0)
  +hp2 = MB.eq_true_of_and_left(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, rt}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L))))), hpr1)
  +hpr2 = MB.eq_true_of_and_right(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, rt}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L))))), hpr1)
  +hp3 = MB.eq_true_of_and_left(RG.none.in(Con{x, ps}, Con{s, rt}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L)))), hpr2)
  +hpr3 = MB.eq_true_of_and_right(RG.none.in(Con{x, ps}, Con{s, rt}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L)))), hpr2)
  +hp4 = MB.eq_true_of_and_left(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L))), hpr3)
  +hpr4 = MB.eq_true_of_and_right(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L))), hpr3)
  +hp5 = MB.eq_true_of_and_left(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L)), hpr4)
  +hpr5 = MB.eq_true_of_and_right(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L)), hpr4)
  +hp6 = MB.eq_true_of_and_left(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L), hpr5)
  +hp7 = MB.eq_true_of_and_right(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L), hpr5)
  +hsL = MB.eq_true_of_and_left(RG.has(L, s), RG.sub(rt, L), hp1)
  +hcsL = MB.eq_true_of_and_right(RG.has(L, s), RG.sub(rt, L), hp1)
  +hxL = MB.eq_true_of_and_left(RG.has(L, x), RG.sub(ps, L), hp2)
  +hxout = MB.eq_false_of_not_eq_true(RG.has(Con{s, rt}, x), MB.eq_true_of_and_left(Bool.not(RG.has(Con{s, rt}, x)), RG.none.in(ps, Con{s, rt}), hp3))
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, tw)), d, rt, s, s), RG.apart.all(Con{s, rt}, d), hp0)
  +hns = apart_notin(rt, d, s, MB.eq_true_of_and_left(RG.apart(rt, d, s), RG.apart.all(rt, d), hap))
  +hxrt = or_false_r(U32.is_eq(s, x), RG.has(rt, x), hxout)
  +hr0 = MB.and_eq_true(RG.ring(AD.view(U32, LAT.fromT(U32, tw)), d, s, rt), Bool.and(RG.layout(Con{s, rt}, d), Bool.and(RG.bases(Con{s, rt}), RG.faces(Con{s, rt}, AD.view(U32, LAT.fromT(U32, tw)), d, Con{s, rt}))), hp0, MB.and_eq_true(RG.layout(Con{s, rt}, d), Bool.and(RG.bases(Con{s, rt}), RG.faces(Con{s, rt}, AD.view(U32, LAT.fromT(U32, tw)), d, Con{s, rt})), lay_sub(Con{s, rt}, L, d, hp1, hp5, hap), MB.and_eq_true(RG.bases(Con{s, rt}), RG.faces(Con{s, rt}, AD.view(U32, LAT.fromT(U32, tw)), d, Con{s, rt}), bases_sub(Con{s, rt}, L, hp1, hp6), faces_sub(Con{s, rt}, AD.view(U32, LAT.fromT(U32, tw)), d, L, Con{s, rt}, hp1, hp1, hp7))))
  +hx0 = MB.and_eq_true(RG.cross(Con{s, rt}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tw)), AD.slot((x + 1 : U32), d)), d, Con{s, rt})), cross_of(Con{s, rt}, L, d, x, hp1, hp5, hxL, hxout), MB.and_eq_true(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tw)), AD.slot((x + 1 : U32), d)), d, Con{s, rt}), bases_at(L, x, hp6, hxL), fm_sub(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tw)), AD.slot((x + 1 : U32), d)), d, L, Con{s, rt}, hp1, faces_at(L, AD.view(U32, LAT.fromT(U32, tw)), d, L, x, hp7, hxL))))
  +hpu = LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, L) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tw)), AD.slot((x + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tw), (x + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tw), (x + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tw)), AD.slot((x + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, tw), d, (x + 1 : U32), hft, hd32)), faces_at(L, AD.view(U32, LAT.fromT(U32, tw)), d, L, x, hp7, hxL))
  %Equal.sym(P.H & Maybe<&2, U32>, R.rg.find(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, far), (P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, RG.first(rt, AD.view(U32, LAT.fromT(U32, tw)), d, far)), find_exact.m(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), d, s, rt, far, hft, hd32, hp0, LAT.mirror(U32, LAT.fromT(U32, tw)))) :
    {RG.agree(RG.cross.t(m, x, rt), AD.view(U32, RG.words(R.cross.k(_, s, x, src, neg))), RG.cr.pv(m, x, src, pv, d), d) == True{} : Bool}
  %Equal.sym(Maybe<&2, U32>, RG.first(rt, AD.view(U32, LAT.fromT(U32, tw)), d, far), m, e) :
    {RG.agree(RG.cross.t(m, x, rt), AD.view(U32, RG.words(R.cross.k((P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, _), s, x, src, neg))), RG.cr.pv(m, x, src, pv, d), d) == True{} : Bool}
  crs_agree.k(tw, ta, d, s, rt, L, x, src, neg, far, pv, m, e, hft, hd32, hp5, hp1, hp7, hsL, hcsL, hxL, hxout, hns, hxrt, hr0, hx0, hpu, hag, hpd0)

# the pending ones' words 2 read in the view after a crossing
def crs_pdef(m: Maybe<&2, U32>, +x: U32, +src: U32, +pv: List<&2, U32>, +d: Nat, +ps: List<&2, U32>, +h: {pdef(ps, pv, d) == True{} : Bool}) ->
    {pdef(ps, RG.cr.pv(m, x, src, pv, d), d) == True{} : Bool}:
  match m:
    case Some{+y}:
      h
    case None{}:
      pdef_set(ps, pv, d, AD.slot((x + 2 : U32), d), src, h)

def meq_refl(m: Maybe<&2, U32>) -> {RG.meq(m, m) == True{} : Bool}:
  match m:
    case Some{+v}:
      meq_self(v)
    case None{}:
      {==}

def agree_refl(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat) -> {RG.agree(ys, v, v, d) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(RG.meq(List.get(&2, U32, v, AD.slot((m + 2 : U32), d)), List.get(&2, U32, v, AD.slot((m + 2 : U32), d))), RG.agree(r, v, v, d), meq_refl(List.get(&2, U32, v, AD.slot((m + 2 : U32), d))), agree_refl(r, v, d))

# the fold, the ring's members agreeing with the view of the positions
# and the pending ones' words 2 read in it, by induction on the crossings
def crs.go(cl: List<&2, R.FzC>, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +s: U32, +rt: List<&2, U32>, +L: List<&2, U32>, +pv: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hfm: {AD.full(U32, map, dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
  hp: {RG.pend.ok(AD.view(U32, w), d, s, rt, RG.pls(cl, AD.view(U32, map), dm), L) == True{} : Bool}, +hag: {RG.agree(rt, AD.view(U32, w), pv, d) == True{} : Bool}, +hpd: {pdef(RG.pls(cl, AD.view(U32, map), dm), pv, d) == True{} : Bool},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {RG.pend.ok(AD.view(U32, RG.words(Pair.snd(Array<U32>, P.H, R.crossings(cl, (map, P.H{KM.MG{w}, a}), s)))), d, s, Pair.fst(List<&2, U32>, List<&2, U32>, RG.cr(cl, AD.view(U32, map), dm, pv, d, rt, L)), Nil{}, Pair.snd(List<&2, U32>, List<&2, U32>, RG.cr(cl, AD.view(U32, map), dm, pv, d, rt, L))) == True{} : Bool}:
  match cl:
    case Nil{}:
      hp
    case Con{c, +rest}:
      match c:
        case R.FzC{+at, +src, +neg, +far}:
          (+tw, +ew) = mw
          (+ta, +ea) = ma
          (+tm, +em) = mm
          +hft = LAP.full_t(U32, w, tw, d, ew, hf)
          +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
          +ePL = ME.subst(Maybe<&2, U32>, q => {RG.pl.of(q) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)) : U32}, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm)), LA.get_view(U32, LAT.fromT(U32, tm), dm, at, hfmt, hdm), {==})
          +hpa = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, q), d, s, rt, Con{RG.pl.of(List.get(&2, U32, AD.view(U32, map), AD.slot(at, dm))), RG.pls(rest, AD.view(U32, map), dm)}, L) == True{} : Bool}, w, LAT.fromT(U32, tw), Equal.sym(Array<U32>, LAT.fromT(U32, tw), w, ew), hp)
          +hpb = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, LAT.fromT(U32, tw)), d, s, rt, Con{RG.pl.of(List.get(&2, U32, AD.view(U32, q), AD.slot(at, dm))), RG.pls(rest, AD.view(U32, q), dm)}, L) == True{} : Bool}, map, LAT.fromT(U32, tm), Equal.sym(Array<U32>, LAT.fromT(U32, tm), map, em), hpa)
          +hp3 = ME.subst(U32, q => {RG.pend.ok(AD.view(U32, LAT.fromT(U32, tw)), d, s, rt, Con{q, RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm)}, L) == True{} : Bool}, RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), ePL, hpb)
          +hagt = LAB.subst(Array<U32>, q => {RG.agree(rt, AD.view(U32, q), pv, d) == True{} : Bool}, w, LAT.fromT(U32, tw), Equal.sym(Array<U32>, LAT.fromT(U32, tw), w, ew), hag)
          +hpd1 = LAB.subst(Array<U32>, q => {pdef(Con{RG.pl.of(List.get(&2, U32, AD.view(U32, q), AD.slot(at, dm))), RG.pls(rest, AD.view(U32, q), dm)}, pv, d) == True{} : Bool}, map, LAT.fromT(U32, tm), Equal.sym(Array<U32>, LAT.fromT(U32, tm), map, em), hpd)
          +hpd2 = ME.subst(U32, q => {pdef(Con{q, RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm)}, pv, d) == True{} : Bool}, RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), ePL, hpd1)
          +hpd0 = MB.eq_true_of_and_left(issome(List.get(&2, U32, pv, AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)) + 2 : U32), d))), pdef(RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm), pv, d), hpd2)
          +hpdr = MB.eq_true_of_and_right(issome(List.get(&2, U32, pv, AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)) + 2 : U32), d))), pdef(RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm), pv, d), hpd2)
          +eF = first_agree(rt, AD.view(U32, LAT.fromT(U32, tw)), pv, d, far, hagt)
          +hr0 = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, tw)), d, s, rt), Bool.and(RG.sub(Con{s, rt}, L), Bool.and(RG.sub(Con{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm)}, L), Bool.and(RG.none.in(Con{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm)}, Con{s, rt}), Bool.and(RG.distinct(Con{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm)}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L))))))), hp3)
          +hpx = cross_pend.m(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), d, s, rt, RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm), L, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far, hft, hd32, hp3, LAT.mirror(U32, LAT.fromT(U32, tw)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
          +hpn = ME.subst(Maybe<&2, U32>, q => {RG.pend.ok(AD.view(U32, RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far))), d, s, RG.cross.t(q, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), rt), RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm), RG.cross.L(q, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), L)) == True{} : Bool}, RG.first(rt, AD.view(U32, LAT.fromT(U32, tw)), d, far), RG.first(rt, pv, d, far), eF, hpx)
          +hagn = crs_agree(tw, ta, d, s, rt, RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm), L, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far, pv, RG.first(rt, pv, d, far), eF, hft, hd32, hp3, hagt, hpd0)
          +hpdn = crs_pdef(RG.first(rt, pv, d, far), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, pv, d, RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm), hpdr)
          +hfx = cross_full.m(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), d, s, rt, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far, hft, hd32, hr0, LAT.mirror(U32, LAT.fromT(U32, tw)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
          %ew : {RG.pend.ok(AD.view(U32, RG.words(Pair.snd(Array<U32>, P.H, R.crossings(Con{R.FzC{at, src, neg, far}, rest}, (map, P.H{KM.MG{_}, a}), s)))), d, s, Pair.fst(List<&2, U32>, List<&2, U32>, RG.cr(Con{R.FzC{at, src, neg, far}, rest}, AD.view(U32, map), dm, pv, d, rt, L)), Nil{}, Pair.snd(List<&2, U32>, List<&2, U32>, RG.cr(Con{R.FzC{at, src, neg, far}, rest}, AD.view(U32, map), dm, pv, d, rt, L))) == True{} : Bool}
          %ea : {RG.pend.ok(AD.view(U32, RG.words(Pair.snd(Array<U32>, P.H, R.crossings(Con{R.FzC{at, src, neg, far}, rest}, (map, P.H{KM.MG{LAT.fromT(U32, tw)}, _}), s)))), d, s, Pair.fst(List<&2, U32>, List<&2, U32>, RG.cr(Con{R.FzC{at, src, neg, far}, rest}, AD.view(U32, map), dm, pv, d, rt, L)), Nil{}, Pair.snd(List<&2, U32>, List<&2, U32>, RG.cr(Con{R.FzC{at, src, neg, far}, rest}, AD.view(U32, map), dm, pv, d, rt, L))) == True{} : Bool}
          %em : {RG.pend.ok(AD.view(U32, RG.words(Pair.snd(Array<U32>, P.H, R.crossings(Con{R.FzC{at, src, neg, far}, rest}, (_, P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}), s)))), d, s, Pair.fst(List<&2, U32>, List<&2, U32>, RG.cr(Con{R.FzC{at, src, neg, far}, rest}, AD.view(U32, _), dm, pv, d, rt, L)), Nil{}, Pair.snd(List<&2, U32>, List<&2, U32>, RG.cr(Con{R.FzC{at, src, neg, far}, rest}, AD.view(U32, _), dm, pv, d, rt, L))) == True{} : Bool}
          %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, tm), at), (LAT.fromT(U32, tm), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at))), LA.get_pair(U32, LAT.fromT(U32, tm), at)) :
            {RG.pend.ok(AD.view(U32, RG.words(Pair.snd(Array<U32>, P.H, R.crossings(rest, R.crossing.pl(_, P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, src, neg, far), s)))), d, s, Pair.fst(List<&2, U32>, List<&2, U32>, RG.cr(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, RG.cr.pv(RG.first(rt, pv, d, far), RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), src, pv, d), d, RG.cross.t(RG.first(rt, pv, d, far), RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), rt), RG.cross.L(RG.first(rt, pv, d, far), RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), L))), Nil{}, Pair.snd(List<&2, U32>, List<&2, U32>, RG.cr(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, RG.cr.pv(RG.first(rt, pv, d, far), RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), src, pv, d), d, RG.cross.t(RG.first(rt, pv, d, far), RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), rt), RG.cross.L(RG.first(rt, pv, d, far), RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), L)))) == True{} : Bool}
          %cross_parts.m(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), d, s, rt, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far, hft, hd32, hr0, LAT.mirror(U32, LAT.fromT(U32, tw)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
            {RG.pend.ok(AD.view(U32, RG.words(Pair.snd(Array<U32>, P.H, R.crossings(rest, (LAT.fromT(U32, tm), _), s)))), d, s, Pair.fst(List<&2, U32>, List<&2, U32>, RG.cr(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, RG.cr.pv(RG.first(rt, pv, d, far), RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), src, pv, d), d, RG.cross.t(RG.first(rt, pv, d, far), RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), rt), RG.cross.L(RG.first(rt, pv, d, far), RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), L))), Nil{}, Pair.snd(List<&2, U32>, List<&2, U32>, RG.cr(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, RG.cr.pv(RG.first(rt, pv, d, far), RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), src, pv, d), d, RG.cross.t(RG.first(rt, pv, d, far), RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), rt), RG.cross.L(RG.first(rt, pv, d, far), RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), L)))) == True{} : Bool}
          %Equal.sym(U32, RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), ePL) :
            {RG.pend.ok(AD.view(U32, RG.words(Pair.snd(Array<U32>, P.H, R.crossings(rest, (LAT.fromT(U32, tm), P.H{KM.MG{RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far))}, LAT.fromT(V.Val, ta)}), s)))), d, s, Pair.fst(List<&2, U32>, List<&2, U32>, RG.cr(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, RG.cr.pv(RG.first(rt, pv, d, far), _, src, pv, d), d, RG.cross.t(RG.first(rt, pv, d, far), _, rt), RG.cross.L(RG.first(rt, pv, d, far), _, L))), Nil{}, Pair.snd(List<&2, U32>, List<&2, U32>, RG.cr(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, RG.cr.pv(RG.first(rt, pv, d, far), _, src, pv, d), d, RG.cross.t(RG.first(rt, pv, d, far), _, rt), RG.cross.L(RG.first(rt, pv, d, far), _, L)))) == True{} : Bool}
          crs.go(rest, RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far)), LAT.fromT(V.Val, ta), LAT.fromT(U32, tm), d, dm, s, RG.cross.t(RG.first(rt, pv, d, far), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), rt), RG.cross.L(RG.first(rt, pv, d, far), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), L), RG.cr.pv(RG.first(rt, pv, d, far), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, pv, d), hfx, hd32, hfmt, hdm, hpn, hagn, hpdn, LAT.mirror(U32, RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)), LAT.mirror(U32, LAT.fromT(U32, tm)))

def crossings_pend.m(-w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +s: U32, +rt: List<&2, U32>, +L: List<&2, U32>, +cs: List<&2, R.FzC>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hfm: {AD.full(U32, map, dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
  hp: {RG.pend.ok(AD.view(U32, w), d, s, rt, RG.pls(cs, AD.view(U32, map), dm), L) == True{} : Bool},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {RG.pend.ok(AD.view(U32, RG.words(Pair.snd(Array<U32>, P.H, R.crossings(cs, (map, P.H{KM.MG{w}, a}), s)))), d, s, Pair.fst(List<&2, U32>, List<&2, U32>, RG.cr(cs, AD.view(U32, map), dm, AD.view(U32, w), d, rt, L)), Nil{}, Pair.snd(List<&2, U32>, List<&2, U32>, RG.cr(cs, AD.view(U32, map), dm, AD.view(U32, w), d, rt, L))) == True{} : Bool}:
  (+tw, +ew) = mw
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, w, tw, d, ew, hf)
  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
  +hpa = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, q), d, s, rt, RG.pls(cs, AD.view(U32, map), dm), L) == True{} : Bool}, w, LAT.fromT(U32, tw), Equal.sym(Array<U32>, LAT.fromT(U32, tw), w, ew), hp)
  +hpb = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, LAT.fromT(U32, tw)), d, s, rt, RG.pls(cs, AD.view(U32, q), dm), L) == True{} : Bool}, map, LAT.fromT(U32, tm), Equal.sym(Array<U32>, LAT.fromT(U32, tm), map, em), hpa)
  %ew : {RG.pend.ok(AD.view(U32, RG.words(Pair.snd(Array<U32>, P.H, R.crossings(cs, (map, P.H{KM.MG{_}, a}), s)))), d, s, Pair.fst(List<&2, U32>, List<&2, U32>, RG.cr(cs, AD.view(U32, map), dm, AD.view(U32, _), d, rt, L)), Nil{}, Pair.snd(List<&2, U32>, List<&2, U32>, RG.cr(cs, AD.view(U32, map), dm, AD.view(U32, _), d, rt, L))) == True{} : Bool}
  %em : {RG.pend.ok(AD.view(U32, RG.words(Pair.snd(Array<U32>, P.H, R.crossings(cs, (_, P.H{KM.MG{LAT.fromT(U32, tw)}, a}), s)))), d, s, Pair.fst(List<&2, U32>, List<&2, U32>, RG.cr(cs, AD.view(U32, _), dm, AD.view(U32, LAT.fromT(U32, tw)), d, rt, L)), Nil{}, Pair.snd(List<&2, U32>, List<&2, U32>, RG.cr(cs, AD.view(U32, _), dm, AD.view(U32, LAT.fromT(U32, tw)), d, rt, L))) == True{} : Bool}
  crs.go(cs, LAT.fromT(U32, tw), a, LAT.fromT(U32, tm), d, dm, s, rt, L, AD.view(U32, LAT.fromT(U32, tw)), hft, hd32, hfmt, hdm, hpb, agree_refl(rt, AD.view(U32, LAT.fromT(U32, tw)), d), pdef_view(RG.pls(cs, AD.view(U32, LAT.fromT(U32, tm)), dm), tw, d, hft, hd32), LAT.mirror(U32, LAT.fromT(U32, tw)), ma, LAT.mirror(U32, LAT.fromT(U32, tm)))

def Laws.crossings_pend(w, a, map, d, dm, s, t, L, cs, hf, hd32, hfm, hdm, hp):
  crossings_pend.m(w, a, map, d, dm, s, t, L, cs, hf, hd32, hfm, hdm, hp, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))

# A copy's crossings: the ports faced, kept among the first ones

# what a node faces, by its word 1: a port among those of N, so that the
# crossings write only the link words of the ports faced at the start
def fin.m(m: Maybe<&2, U32>, +d: Nat, +N: List<&2, U32>) -> Bool:
  match m:
    case Some{+r}:
      RG.has(N, r)
    case None{}:
      False{}

def faced.in(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +N: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+m, t}:
      fin.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, N) && faced.in(t, v, d, N)

# faces' lemmas, their twins: the port faced among N's, kept as a face
# is (faces_keep, faces_write, and the steps' lx_faces, ul_faces, fr_faces)

def fn_map(mm: Maybe<&2, U32>, +n: U32, +d: Nat, +N: List<&2, U32>, h: {fin.m(mm, d, N) == True{} : Bool}, +hn: {RG.has(N, n) == True{} : Bool}) ->
    {fin.m(Maybe.map(&2, U32, U32, z => n, mm), d, N) == True{} : Bool}:
  match mm:
    case Some{+r}:
      hn
    case None{}:
      Empty.absurd({fin.m(None{}, d, N) == True{} : Bool}, MB.false_ne_true()(h))

def fn_keep(+v: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +i: U32, +n: U32, +m: U32, h: {fin.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, N) == True{} : Bool},
    +hs: {Nat.is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d)) == False{} : Bool}) -> {fin.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((m + 1 : U32), d)), d, N) == True{} : Bool}:
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((m + 1 : U32), d)), List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), LAB.get_set_ne(U32, v, AD.slot(i, d), AD.slot((m + 1 : U32), d), n, hs)) :
    {fin.m(_, d, N) == True{} : Bool}
  h

def fn_write(+v: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +i: U32, +n: U32, +m: U32, +b: Bool, e: {Nat.is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d)) == b : Bool},
    +h: {fin.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, N) == True{} : Bool}, +hn: {RG.has(N, n) == True{} : Bool}) -> {fin.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((m + 1 : U32), d)), d, N) == True{} : Bool}:
  match b:
    case True{}:
      +eq = MN.eq_of_is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d), e)
      +h2 = ME.subst(Nat, q => {fin.m(List.get(&2, U32, v, q), d, N) == True{} : Bool}, AD.slot((m + 1 : U32), d), AD.slot(i, d), Equal.sym(Nat, AD.slot(i, d), AD.slot((m + 1 : U32), d), eq), h)
      %eq : {fin.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), _), d, N) == True{} : Bool}
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot(i, d)), Maybe.map(&2, U32, U32, z => n, List.get(&2, U32, v, AD.slot(i, d))), ML.get_set_self(&2, U32, v, AD.slot(i, d), n)) :
        {fin.m(_, d, N) == True{} : Bool}
      fn_map(List.get(&2, U32, v, AD.slot(i, d)), n, d, N, h2, hn)
    case False{}:
      fn_keep(v, d, N, i, n, m, h, e)

def faced_keep(K: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +i: U32, +n: U32,
    +h: {faced.in(K, v, d, N) == True{} : Bool}, +ho: {ones(K, d, i) == True{} : Bool}) -> {faced.in(K, List.set(&2, U32, v, AD.slot(i, d), n), d, N) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(fin.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((m + 1 : U32), d)), d, N), faced.in(r, List.set(&2, U32, v, AD.slot(i, d), n), d, N), fn_keep(v, d, N, i, n, m, MB.eq_true_of_and_left(fin.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, N), faced.in(r, v, d, N), h), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d))), ones(r, d, i), ho))), faced_keep(r, v, d, N, i, n, MB.eq_true_of_and_right(fin.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, N), faced.in(r, v, d, N), h), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d))), ones(r, d, i), ho)))

def faced_write(K: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +i: U32, +n: U32,
    +h: {faced.in(K, v, d, N) == True{} : Bool}, +hn: {RG.has(N, n) == True{} : Bool}) -> {faced.in(K, List.set(&2, U32, v, AD.slot(i, d), n), d, N) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(fin.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot(i, d), n), AD.slot((m + 1 : U32), d)), d, N), faced.in(r, List.set(&2, U32, v, AD.slot(i, d), n), d, N), fn_write(v, d, N, i, n, m, Nat.is_eq(AD.slot(i, d), AD.slot((m + 1 : U32), d)), {==}, MB.eq_true_of_and_left(fin.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, N), faced.in(r, v, d, N), h), hn), faced_write(r, v, d, N, i, n, MB.eq_true_of_and_right(fin.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, N), faced.in(r, v, d, N), h), hn))

def faced_at(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +M: List<&2, U32>, +m: U32, +h: {faced.in(ys, v, d, M) == True{} : Bool}, hm: {RG.has(ys, m) == True{} : Bool}) ->
    {fin.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, M) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({fin.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, M) == True{} : Bool}, MB.false_ne_true()(hm))
    case Con{+c, +r}:
      or_cases(U32.is_eq(c, m), RG.has(r, m), fin.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, M), hm,
        q => ME.subst(U32, k => {fin.m(List.get(&2, U32, v, AD.slot((k + 1 : U32), d)), d, M) == True{} : Bool}, c, m, MS.u32_eq_of_is_eq(c, m, q), MB.eq_true_of_and_left(fin.m(List.get(&2, U32, v, AD.slot((c + 1 : U32), d)), d, M), faced.in(r, v, d, M), h)),
        hh => faced_at(r, v, d, M, m, MB.eq_true_of_and_right(fin.m(List.get(&2, U32, v, AD.slot((c + 1 : U32), d)), d, M), faced.in(r, v, d, M), h), hh))

def lx_faced(+sy: Bool, +sz: Bool, +t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +y: U32, +z: U32, +K: List<&2, U32>, +N: List<&2, U32>,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hK: {faced.in(K, AD.view(U32, LAT.fromT(U32, t)), d, N) == True{} : Bool},
    +hy: {RG.has(N, y) == True{} : Bool}, +hz: {RG.has(N, z) == True{} : Bool}) -> {faced.in(K, AD.view(U32, RG.words(P.link.to(sz, P.link.to(sy, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, z), z, y))), d, N) == True{} : Bool}:
  match sy:
    case True{}:
      match sz:
        case True{}:
          hK
        case False{}:
          %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (z + 1 : U32), y)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((z + 1 : U32), d), y), LA.set_view(U32, LAT.fromT(U32, t), d, (z + 1 : U32), y, hft, hd32)) :
            {faced.in(K, _, d, N) == True{} : Bool}
          faced_write(K, AD.view(U32, LAT.fromT(U32, t)), d, N, (z + 1 : U32), y, hK, hy)
    case False{}:
      match sz:
        case True{}:
          %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d), z), LA.set_view(U32, LAT.fromT(U32, t), d, (y + 1 : U32), z, hft, hd32)) :
            {faced.in(K, _, d, N) == True{} : Bool}
          faced_write(K, AD.view(U32, LAT.fromT(U32, t)), d, N, (y + 1 : U32), z, hK, hz)
        case False{}:
          %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), (z + 1 : U32), y)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z)), AD.slot((z + 1 : U32), d), y), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z), d, (z + 1 : U32), y, LA.set_full(U32, LAT.fromT(U32, t), d, (y + 1 : U32), z, hft), hd32)) :
            {faced.in(K, _, d, N) == True{} : Bool}
          %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (y + 1 : U32), z)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d), z), LA.set_view(U32, LAT.fromT(U32, t), d, (y + 1 : U32), z, hft, hd32)) :
            {faced.in(K, List.set(&2, U32, _, AD.slot((z + 1 : U32), d), y), d, N) == True{} : Bool}
          faced_write(K, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((y + 1 : U32), d), z), d, N, (z + 1 : U32), y, faced_write(K, AD.view(U32, LAT.fromT(U32, t)), d, N, (y + 1 : U32), z, hK, hz), hy)

def ul_faced(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +x: U32, +K: List<&2, U32>, +N: List<&2, U32>,
    hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hK: {faced.in(K, AD.view(U32, w), d, N) == True{} : Bool},
    ho: {ones(K, d, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{w}, a}, x)) + 3 : U32)) == True{} : Bool}, hdone: {pdone(P.H{KM.MG{w}, a}, x) == True{} : Bool},
    m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
    {faced.in(K, AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{w}, a}, x))), d, N) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hKt = LAB.subst(Array<U32>, q => {faced.in(K, AD.view(U32, q), d, N) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hK)
  +ho1 = LAB.subst(Array<U32>, q => {ones(K, d, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{q}, a}, x)) + 3 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), ho)
  +hot = LAB.subst(Array<V.Val>, q => {ones(K, d, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, q}, x)) + 3 : U32)) == True{} : Bool}, a, LAT.fromT(V.Val, ta), Equal.sym(Array<V.Val>, LAT.fromT(V.Val, ta), a, ea), ho1)
  +hd1 = LAB.subst(Array<U32>, q => {pdone(P.H{KM.MG{q}, a}, x) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hdone)
  +hdt = LAB.subst(Array<V.Val>, q => {pdone(P.H{KM.MG{LAT.fromT(U32, t)}, q}, x) == True{} : Bool}, a, LAT.fromT(V.Val, ta), Equal.sym(Array<V.Val>, LAT.fromT(V.Val, ta), a, ea), hd1)
  %e : {faced.in(K, AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{_}, a}, x))), d, N) == True{} : Bool}
  %ea : {faced.in(K, AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x))), d, N) == True{} : Bool}
  %Equal.sym(P.H & U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x), (P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))), pred_pair_ok(t, LAT.fromT(V.Val, ta), d, x, hft, hdt)) :
    {faced.in(K, AD.view(U32, RG.words(R.rg.unlink.p(_, x))), d, N) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 3 : U32))) :
    {faced.in(K, AD.view(U32, RG.words(R.rg.unlink.set(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x))))), d, N) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32)))), LA.set_view(U32, LAT.fromT(U32, t), d, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), hft, hd32)) :
    {faced.in(K, _, d, N) == True{} : Bool}
  faced_keep(K, AD.view(U32, LAT.fromT(U32, t)), d, N, (Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, x)) + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 3 : U32))), hKt, hot)

def fr_faced(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +r: U32, +K: List<&2, U32>, +N: List<&2, U32>,
    hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hK: {faced.in(K, AD.view(U32, w), d, N) == True{} : Bool},
    +h0: {ones(K, d, P.base(r)) == True{} : Bool}, +h1: {ones(K, d, (P.base(r) + 1 : U32)) == True{} : Bool}, +hh: {ones(K, d, P.at_fh()) == True{} : Bool}, m: LAT.Mirror(U32, w)) ->
    {faced.in(K, AD.view(U32, RG.words(P.free(P.H{KM.MG{w}, a}, r))), d, N) == True{} : Bool}:
  (+t, +e) = m
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hKt = LAB.subst(Array<U32>, q => {faced.in(K, AD.view(U32, q), d, N) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hK)
  %e : {faced.in(K, AD.view(U32, RG.words(P.free(P.H{KM.MG{_}, a}, r))), d, N) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), LA.get_pair(U32, LAT.fromT(U32, t), P.at_fh())) :
    {faced.in(K, AD.view(U32, RG.words(P.free.fh(KM.m_get.fin(_), a, r))), d, N) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), P.at_fh(), ((r >> 2n : U32) + 1 : U32))), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())))), AD.slot(P.at_fh(), d), ((r >> 2n : U32) + 1 : U32)), LA.set_view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), d, P.at_fh(), ((r >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), d, (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t), d, P.base(r), 0, hft)), hd32)) :
    {faced.in(K, _, d, N) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())))), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0)), AD.slot((P.base(r) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0), d, (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t), d, P.base(r), 0, hft), hd32)) :
    {faced.in(K, List.set(&2, U32, _, AD.slot(P.at_fh(), d), ((r >> 2n : U32) + 1 : U32)), d, N) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), P.base(r), 0)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(P.base(r), d), 0), LA.set_view(U32, LAT.fromT(U32, t), d, P.base(r), 0, hft, hd32)) :
    {faced.in(K, List.set(&2, U32, List.set(&2, U32, _, AD.slot((P.base(r) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), AD.slot(P.at_fh(), d), ((r >> 2n : U32) + 1 : U32)), d, N) == True{} : Bool}
  faced_keep(K, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(P.base(r), d), 0), AD.slot((P.base(r) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh()))), d, N, P.at_fh(), ((r >> 2n : U32) + 1 : U32), faced_keep(K, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(P.base(r), d), 0), d, N, (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), P.at_fh())), faced_keep(K, AD.view(U32, LAT.fromT(U32, t)), d, N, P.base(r), 0, hKt, h0), h1), hh)

def ins_faced(+t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +K: List<&2, U32>, +M: List<&2, U32>,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +h: {faced.in(K, AD.view(U32, LAT.fromT(U32, t)), d, M) == True{} : Bool}, +hox: {ones(K, d, (x + 3 : U32)) == True{} : Bool}, +hos: {ones(K, d, (s + 3 : U32)) == True{} : Bool}) ->
    {faced.in(K, AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{LAT.fromT(U32, t)}, a}, s, x))), d, M) == True{} : Bool}:
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), hft)
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (s + 3 : U32))) :
    {faced.in(K, AD.view(U32, RG.words(R.rg.insert.r(P.rd.fin(KM.m_get.fin(_), a), s, x))), d, M) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), (s + 3 : U32), x)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))))), AD.slot((s + 3 : U32), d), x), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), d, (s + 3 : U32), x, hf1, hd32)) :
    {faced.in(K, _, d, M) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), LA.set_view(U32, LAT.fromT(U32, t), d, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), hft, hd32)) :
    {faced.in(K, List.set(&2, U32, _, AD.slot((s + 3 : U32), d), x), d, M) == True{} : Bool}
  faced_keep(K, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 3 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32)))), d, M, (s + 3 : U32), x, faced_keep(K, AD.view(U32, LAT.fromT(U32, t)), d, M, (x + 3 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (s + 3 : U32))), h, hox), hos)

def join1_faced.go(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +pa: List<&2, U32>, +x: U32, +m0: U32, +pb: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pa, Con{m0, pb})) == True{} : Bool}, +hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pa, Con{m0, pb})), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  hu: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, hw: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (m0 + 1 : U32))) + 1 : U32)) == True{} : Bool},
  +K: List<&2, U32>, +N: List<&2, U32>, hK: {faced.in(K, AD.view(U32, w), d, N) == True{} : Bool},
  hU: {RG.has(N, Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32)))) == True{} : Bool}, hW: {RG.has(N, Pair.snd(Array<U32>, U32, Array.get(U32, w, (m0 + 1 : U32)))) == True{} : Bool},
  +om: {ones(K, d, (RG.last(pa, s) + 3 : U32)) == True{} : Bool}, +o00: {ones(K, d, P.base(x)) == True{} : Bool}, +o10: {ones(K, d, (P.base(x) + 1 : U32)) == True{} : Bool}, +o01: {ones(K, d, P.base(m0)) == True{} : Bool}, +o11: {ones(K, d, (P.base(m0) + 1 : U32)) == True{} : Bool}, +oh: {ones(K, d, P.at_fh()) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {faced.in(K, AD.view(U32, RG.words(R.join1(P.H{KM.MG{w}, a}, x, m0))), d, N) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {RG.ring(AD.view(U32, q), d, s, List.append(&2, U32, pa, Con{m0, pb})) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hr)
  +hut = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hu)
  +hwt = LAB.subst(Array<U32>, q => {RG.off.links(Con{s, List.append(&2, U32, pa, Con{m0, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, q, (m0 + 1 : U32))) + 1 : U32)) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hw)
  +hKt = LAB.subst(Array<U32>, q => {faced.in(K, AD.view(U32, q), d, N) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hK)
  +hUt = LAB.subst(Array<U32>, q => {RG.has(N, Pair.snd(Array<U32>, U32, Array.get(U32, q, (x + 1 : U32)))) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hU)
  +hWt = LAB.subst(Array<U32>, q => {RG.has(N, Pair.snd(Array<U32>, U32, Array.get(U32, q, (m0 + 1 : U32)))) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hW)
  +hr1 = lx_ring(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), s, List.append(&2, U32, pa, Con{m0, pb}), hft, hd32, hrt, hut, hwt)
  +hf1 = lx_full(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), hft)
  +kf1 = lx_faced(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), t, LAT.fromT(V.Val, ta), d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), K, N, hft, hd32, hKt, hUt, hWt)
  +pe = pred_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, s, pa, m0, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))))
  +kf2 = ul_faced(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, m0, K, N, hf1, hd32, kf1,
    ME.subst(U32, q => {ones(K, d, (q + 3 : U32)) == True{} : Bool}, RG.last(pa, s), Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)), Equal.sym(U32, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)), RG.last(pa, s), pe), om),
    pdone_exact.go(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, s, pa, m0, pb, hf1, hd32, hr1, hn, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))))), LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf2 = ul_full(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, m0, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
  +hf3 = fr_full(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)), LAT.fromT(V.Val, ta), d, x, hf2, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0))))
  +kf3 = fr_faced(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)), LAT.fromT(V.Val, ta), d, x, K, N, hf2, hd32, kf2, o00, o10, oh, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0))))
  %e : {faced.in(K, AD.view(U32, RG.words(R.join1(P.H{KM.MG{_}, a}, x, m0))), d, N) == True{} : Bool}
  %ea : {faced.in(K, AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x, m0))), d, N) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (x + 1 : U32))) :
    {faced.in(K, AD.view(U32, RG.words(R.jn1.u(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), x, m0))), d, N) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)), (LAT.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) :
    {faced.in(K, AD.view(U32, RG.words(R.jn1.w(P.rd.fin(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), x, m0))), d, N) == True{} : Bool}
  %lx_parts(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), LAT.fromT(U32, t), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))) :
    {faced.in(K, AD.view(U32, RG.words(P.free(P.free(R.rg.unlink(_, m0), x), m0))), d, N) == True{} : Bool}
  %ul_parts(RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))))), LAT.fromT(V.Val, ta), d, m0, hf1, LAT.mirror(U32, RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
    {faced.in(K, AD.view(U32, RG.words(P.free(P.free(_, x), m0))), d, N) == True{} : Bool}
  %fr_parts(RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)), LAT.fromT(V.Val, ta), x, LAT.mirror(U32, RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0)))) :
    {faced.in(K, AD.view(U32, RG.words(P.free(_, m0))), d, N) == True{} : Bool}
  fr_faced(RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0))}, LAT.fromT(V.Val, ta)}, x)), LAT.fromT(V.Val, ta), d, m0, K, N, hf3, hd32, kf3, o01, o11, oh, LAT.mirror(U32, RG.words(P.free(P.H{KM.MG{RG.words(R.rg.unlink(P.H{KM.MG{RG.words(P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), P.link.to(P.is_static(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))), P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))))}, LAT.fromT(V.Val, ta)}, m0))}, LAT.fromT(V.Val, ta)}, x))))

# A copy's crossings: the region, its lemmas

def nodes_at(L: List<&2, U32>, +d: Nat, +j: U32, +m: U32, +h: {RG.off.nodes(L, d, j) == True{} : Bool}, hm: {RG.has(L, m) == True{} : Bool}) -> {RG.off.node(d, m, j) == True{} : Bool}:
  match L:
    case Nil{}:
      Empty.absurd({RG.off.node(d, m, j) == True{} : Bool}, MB.false_ne_true()(hm))
    case Con{+c, +r}:
      or_cases(U32.is_eq(c, m), RG.has(r, m), RG.off.node(d, m, j), hm,
        q => ME.subst(U32, k => {RG.off.node(d, k, j) == True{} : Bool}, c, m, MS.u32_eq_of_is_eq(c, m, q), MB.eq_true_of_and_left(RG.off.node(d, c, j), RG.off.nodes(r, d, j), h)),
        hh => nodes_at(r, d, j, m, MB.eq_true_of_and_right(RG.off.node(d, c, j), RG.off.nodes(r, d, j), h), hh))

def ports_at(F: List<&2, U32>, +d: Nat, +j: U32, +f: U32, +h: {RG.off.ports(F, d, j) == True{} : Bool}, hf: {RG.has(F, f) == True{} : Bool}) -> {Bool.not(Nat.is_eq(AD.slot((f + 1 : U32), d), AD.slot(j, d))) == True{} : Bool}:
  match F:
    case Nil{}:
      Empty.absurd({Bool.not(Nat.is_eq(AD.slot((f + 1 : U32), d), AD.slot(j, d))) == True{} : Bool}, MB.false_ne_true()(hf))
    case Con{+c, +r}:
      or_cases(U32.is_eq(c, f), RG.has(r, f), Bool.not(Nat.is_eq(AD.slot((f + 1 : U32), d), AD.slot(j, d))), hf,
        q => ME.subst(U32, k => {Bool.not(Nat.is_eq(AD.slot((k + 1 : U32), d), AD.slot(j, d))) == True{} : Bool}, c, f, MS.u32_eq_of_is_eq(c, f, q), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((c + 1 : U32), d), AD.slot(j, d))), RG.off.ports(r, d, j), h)),
        hh => ports_at(r, d, j, f, MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((c + 1 : U32), d), AD.slot(j, d))), RG.off.ports(r, d, j), h), hh))

def off_nodes_sub(K: List<&2, U32>, +L: List<&2, U32>, +d: Nat, +j: U32, +hs: {RG.sub(K, L) == True{} : Bool}, +h: {RG.off.nodes(L, d, j) == True{} : Bool}) -> {RG.off.nodes(K, d, j) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(RG.off.node(d, m, j), RG.off.nodes(r, d, j), nodes_at(L, d, j, m, h, MB.eq_true_of_and_left(RG.has(L, m), RG.sub(r, L), hs)), off_nodes_sub(r, L, d, j, MB.eq_true_of_and_right(RG.has(L, m), RG.sub(r, L), hs), h))

# the ring's links off a word no node of L holds
def links_of_nodes(K: List<&2, U32>, +L: List<&2, U32>, +d: Nat, +j: U32, +hs: {RG.sub(K, L) == True{} : Bool}, +h: {RG.off.nodes(L, d, j) == True{} : Bool}) -> {RG.off.links(K, d, j) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      +hn = nodes_at(L, d, j, m, h, MB.eq_true_of_and_left(RG.has(L, m), RG.sub(r, L), hs))
      +n3 = MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d))), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), Bool.and(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d)))), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))), Bool.and(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), Bool.and(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d))))), hn)))
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(j, d), AD.slot((m + 3 : U32), d))), RG.off.links(r, d, j), ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d)), Nat.is_eq(AD.slot(j, d), AD.slot((m + 3 : U32), d)), MN.is_eq_comm(AD.slot((m + 3 : U32), d), AD.slot(j, d)), n3), links_of_nodes(r, L, d, j, MB.eq_true_of_and_right(RG.has(L, m), RG.sub(r, L), hs), h))

# the faced ports' invariant over a part, and where it starts
def faced_sub(K: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +M: List<&2, U32>, +F: List<&2, U32>, +hs: {RG.sub(K, M) == True{} : Bool}, +h: {faced.in(M, v, d, F) == True{} : Bool}) -> {faced.in(K, v, d, F) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(fin.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, F), faced.in(r, v, d, F), faced_at(M, v, d, F, m, h, MB.eq_true_of_and_left(RG.has(M, m), RG.sub(r, M), hs)), faced_sub(r, v, d, M, F, MB.eq_true_of_and_right(RG.has(M, m), RG.sub(r, M), hs), h))

def faced_has(L: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +m: U32, hm: {RG.has(L, m) == True{} : Bool}) -> {RG.has(RG.faced(L, v, d), RG.pl.of(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)))) == True{} : Bool}:
  match L:
    case Nil{}:
      Empty.absurd({RG.has(RG.faced(Nil{}, v, d), RG.pl.of(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)))) == True{} : Bool}, MB.false_ne_true()(hm))
    case Con{+c, +r}:
      or_cases(U32.is_eq(c, m), RG.has(r, m), RG.has(RG.faced(Con{c, r}, v, d), RG.pl.of(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)))), hm,
        q => ME.subst(U32, k => {RG.has(RG.faced(Con{c, r}, v, d), RG.pl.of(List.get(&2, U32, v, AD.slot((k + 1 : U32), d)))) == True{} : Bool}, c, m, MS.u32_eq_of_is_eq(c, m, q), has_self(RG.pl.of(List.get(&2, U32, v, AD.slot((c + 1 : U32), d))), RG.faced(r, v, d))),
        hh => has_cons(RG.pl.of(List.get(&2, U32, v, AD.slot((c + 1 : U32), d))), RG.faced(r, v, d), RG.pl.of(List.get(&2, U32, v, AD.slot((m + 1 : U32), d))), faced_has(r, v, d, m, hh)))

def fi_one(+m: U32, +L: List<&2, U32>, +t: LAT.Tree<U32>, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hm: {RG.has(L, m) == True{} : Bool}) ->
    {fin.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m + 1 : U32), d)), d, RG.faced(L, AD.view(U32, LAT.fromT(U32, t)), d)) == True{} : Bool}:
  +q = Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m + 1 : U32)))
  +hq = ME.subst(Maybe<&2, U32>, qq => {RG.has(RG.faced(L, AD.view(U32, LAT.fromT(U32, t)), d), RG.pl.of(qq)) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m + 1 : U32), d)), Some{q}, Equal.sym(Maybe<&2, U32>, Some{q}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (m + 1 : U32), hft, hd32)), faced_has(L, AD.view(U32, LAT.fromT(U32, t)), d, m, hm))
  %LA.get_view(U32, LAT.fromT(U32, t), d, (m + 1 : U32), hft, hd32) :
    {fin.m(_, d, RG.faced(L, AD.view(U32, LAT.fromT(U32, t)), d)) == True{} : Bool}
  hq

def faced_init(K: List<&2, U32>, +L: List<&2, U32>, +t: LAT.Tree<U32>, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {RG.sub(K, L) == True{} : Bool}) ->
    {faced.in(K, AD.view(U32, LAT.fromT(U32, t)), d, RG.faced(L, AD.view(U32, LAT.fromT(U32, t)), d)) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(fin.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m + 1 : U32), d)), d, RG.faced(L, AD.view(U32, LAT.fromT(U32, t)), d)), faced.in(r, AD.view(U32, LAT.fromT(U32, t)), d, RG.faced(L, AD.view(U32, LAT.fromT(U32, t)), d)), fi_one(m, L, t, d, hft, hd32, MB.eq_true_of_and_left(RG.has(L, m), RG.sub(r, L), hs)), faced_init(r, L, t, d, hft, hd32, MB.eq_true_of_and_right(RG.has(L, m), RG.sub(r, L), hs)))

# A cursor made keeps every word but its node's and the situating node's
# word 3 (cursor_keeps): cur_get's frame on the view, read back by P.rd
def off_w2(+d: Nat, +m: U32, +j: U32, +h: {RG.off.node(d, m, j) == True{} : Bool}) -> {Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d)) == False{} : Bool}:
  MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d))), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), Bool.and(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d)))), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))), Bool.and(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), Bool.and(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d))))), h))))

def off_w3(+d: Nat, +m: U32, +j: U32, +h: {RG.off.node(d, m, j) == True{} : Bool}) -> {Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}:
  MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d))), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), Bool.and(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d)))), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))), Bool.and(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), Bool.and(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d))))), h))))

def some_inj(+a: U32, +b: U32, e: {Some{a} == Some{b} : Maybe<&2, U32>}) -> {a == b : U32}:
  ME.subst(Maybe<&2, U32>, q => {a == Maybe.default(&2, U32, q, a) : U32}, Some{a}, Some{b}, e, {==})

def cursor_keeps.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +src: U32, +neg: Bool, +j: U32,
    hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hjx: {RG.off.node(d, x, j) == True{} : Bool}, +hjs: {Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d)) == False{} : Bool},
    m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
    {Pair.snd(P.H, U32, P.rd(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  %e : {Pair.snd(P.H, U32, P.rd(R.cursor(P.H{KM.MG{_}, a}, s, x, src, neg), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %ea : {Pair.snd(P.H, U32, P.rd(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, _}, s, x, src, neg), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, _}, j)) : U32}
  %cursor_parts(t, ta, d, s, x, src, neg) :
    {Pair.snd(P.H, U32, P.rd(_, j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  ME.trans3(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)), rd_get(RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg)), LAT.fromT(V.Val, ta), j), some_inj(Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), ME.trans3(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg)), j))}, List.get(&2, U32, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg))), AD.slot(j, d)), List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(j, d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j))}, LA.get_view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, x, src, neg)), d, j, cursor_full(t, ta, d, s, x, src, neg, hft), hd32), cur_get(t, ta, d, s, x, src, neg, j, hft, hd32, off_w0(d, x, j, hjx), off_w2(d, x, j, hjx), off_w3(d, x, j, hjx), hjs), Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(j, d)), LA.get_view(U32, LAT.fromT(U32, t), d, j, hft, hd32)))), Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), rd_get(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), j)))

def Laws.cursor_keeps(w, a, d, s, x, src, neg, j, hf, hd32, hjx, hjs):
  cursor_keeps.m(w, a, d, s, x, src, neg, j, hf, hd32, hjx, hjs, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# A copy's crossings: the region kept, step by step (crossings_keeps)
def fport(K: List<&2, U32>, +t: LAT.Tree<U32>, +d: Nat, +F: List<&2, U32>, +x: U32, +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hfi: {faced.in(K, AD.view(U32, LAT.fromT(U32, t)), d, F) == True{} : Bool}, hx: {RG.has(K, x) == True{} : Bool}) -> {RG.has(F, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))) == True{} : Bool}:
  ME.subst(Maybe<&2, U32>, q => {fin.m(q, d, F) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))},
    Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (x + 1 : U32), hft, hd32)), faced_at(K, AD.view(U32, LAT.fromT(U32, t)), d, F, x, hfi, hx))

# the cursor's word 3 and the situating node's, off every word 1
def cur_faced(-w2: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +L: List<&2, U32>, +F: List<&2, U32>, hf2: {AD.full(U32, w2, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    hF: {faced.in(L, AD.view(U32, w2), d, F) == True{} : Bool}, m2: LAT.Mirror(U32, w2), +hox: {ones(L, d, (x + 3 : U32)) == True{} : Bool}, +hos: {ones(L, d, (s + 3 : U32)) == True{} : Bool}) ->
    {faced.in(L, AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{w2}, a}, s, x))), d, F) == True{} : Bool}:
  (+t2, +e2) = m2
  +hft2 = LAP.full_t(U32, w2, t2, d, e2, hf2)
  +hFt = LAB.subst(Array<U32>, q => {faced.in(L, AD.view(U32, q), d, F) == True{} : Bool}, w2, LAT.fromT(U32, t2), Equal.sym(Array<U32>, LAT.fromT(U32, t2), w2, e2), hF)
  %e2 : {faced.in(L, AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{_}, a}, s, x))), d, F) == True{} : Bool}
  ins_faced(t2, a, d, s, x, L, F, hft2, hd32, hFt, hox, hos)

# a cursor made: the ports faced kept among F
def cur_faced.p(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +ps: List<&2, U32>, +L: List<&2, U32>, +x: U32, +src: U32, +neg: Bool,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hp: {RG.pend.ok(AD.view(U32, w), d, s, cs, Con{x, ps}, L) == True{} : Bool},
  +F: List<&2, U32>, hfi: {faced.in(L, AD.view(U32, w), d, F) == True{} : Bool}, m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {faced.in(L, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg))), d, F) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hfit = LAB.subst(Array<U32>, q => {faced.in(L, AD.view(U32, q), d, F) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hfi)
  +hpt = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, q), d, s, cs, Con{x, ps}, L) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hp)
  +hp0 = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt)
  +hpr0 = MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt)
  +hp1 = MB.eq_true_of_and_left(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))))), hpr0)
  +hpr1 = MB.eq_true_of_and_right(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))))), hpr0)
  +hp2 = MB.eq_true_of_and_left(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))), hpr1)
  +hpr2 = MB.eq_true_of_and_right(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))), hpr1)
  +hp3 = MB.eq_true_of_and_left(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))), hpr2)
  +hpr3 = MB.eq_true_of_and_right(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))), hpr2)
  +hp4 = MB.eq_true_of_and_left(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))), hpr3)
  +hpr4 = MB.eq_true_of_and_right(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))), hpr3)
  +hp5 = MB.eq_true_of_and_left(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)), hpr4)
  +hpr5 = MB.eq_true_of_and_right(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)), hpr4)
  +hp6 = MB.eq_true_of_and_left(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L), hpr5)
  +hp7 = MB.eq_true_of_and_right(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L), hpr5)
  +hsL = MB.eq_true_of_and_left(RG.has(L, s), RG.sub(cs, L), hp1)
  +hcsL = MB.eq_true_of_and_right(RG.has(L, s), RG.sub(cs, L), hp1)
  +hxL = MB.eq_true_of_and_left(RG.has(L, x), RG.sub(ps, L), hp2)
  +hpsL = MB.eq_true_of_and_right(RG.has(L, x), RG.sub(ps, L), hp2)
  +hxout = MB.eq_false_of_not_eq_true(RG.has(Con{s, cs}, x), MB.eq_true_of_and_left(Bool.not(RG.has(Con{s, cs}, x)), RG.none.in(ps, Con{s, cs}), hp3))
  +hpsout = MB.eq_true_of_and_right(Bool.not(RG.has(Con{s, cs}, x)), RG.none.in(ps, Con{s, cs}), hp3)
  +hxps = MB.eq_false_of_not_eq_true(RG.has(ps, x), MB.eq_true_of_and_left(Bool.not(RG.has(ps, x)), RG.distinct(ps), hp4))
  +hdps = MB.eq_true_of_and_right(Bool.not(RG.has(ps, x)), RG.distinct(ps), hp4)
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hp0)
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t), d, x, P.hd2(18, R.cur.form(neg), 0), hft)
  +hf2 = LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), src, hf1)
  +hF2 = faced_keep(L, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), d, F, (x + 2 : U32), src, faced_keep(L, AD.view(U32, LAT.fromT(U32, t)), d, F, x, P.hd2(18, R.cur.form(neg), 0), hfit, ones_p0(L, L, d, x, sub_refl(L), hp5, hxL)), ones_p2(L, L, d, x, sub_refl(L), hp5, hxL))
  +hF3 = LAB.subst(List<&2, U32>, q => {faced.in(L, List.set(&2, U32, q, AD.slot((x + 2 : U32), d), src), d, F) == True{} : Bool}, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(x, d), P.hd2(18, R.cur.form(neg), 0)), LA.set_view(U32, LAT.fromT(U32, t), d, x, P.hd2(18, R.cur.form(neg), 0), hft, hd32)), hF2)
  +hF4 = LAB.subst(List<&2, U32>, q => {faced.in(L, q, d, F) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), AD.slot((x + 2 : U32), d), src), AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0))), AD.slot((x + 2 : U32), d), src), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), d, (x + 2 : U32), src, hf1, hd32)), hF3)
  +hFP = cur_faced(Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src), LAT.fromT(V.Val, ta), d, s, x, L, F, hf2, hd32, hF4, LAT.mirror(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t), x, P.hd2(18, R.cur.form(neg), 0)), (x + 2 : U32), src)), ones_p3(L, L, d, x, sub_refl(L), hp5, hxL), ones_p3(L, L, d, s, sub_refl(L), hp5, hsL))
  %e : {faced.in(L, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{_}, a}, s, x, src, neg))), d, F) == True{} : Bool}
  %ea : {faced.in(L, AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t)}, _}, s, x, src, neg))), d, F) == True{} : Bool}
  hFP

# a join: the frame, on what the invariant and the faced ports give
def j1_keeps.p(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +ps: List<&2, U32>, +L: List<&2, U32>, +x: U32, +m0: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hp: {RG.pend.ok(AD.view(U32, w), d, s, cs, Con{x, ps}, L) == True{} : Bool},
  +hm: {RG.has(cs, m0) == True{} : Bool}, +F: List<&2, U32>, +j: U32, hfi: {faced.in(L, AD.view(U32, w), d, F) == True{} : Bool}, +hj: {RG.off.nodes(L, d, j) == True{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}, +hjf: {RG.off.ports(F, d, j) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {Pair.snd(P.H, U32, P.rd(R.join1(P.H{KM.MG{w}, a}, x, m0), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hfit = LAB.subst(Array<U32>, q => {faced.in(L, AD.view(U32, q), d, F) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hfi)
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hpt = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, q), d, s, cs, Con{x, ps}, L) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hp)
  +hp0 = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt)
  +hpr0 = MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt)
  +hp1 = MB.eq_true_of_and_left(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))))), hpr0)
  +hpr1 = MB.eq_true_of_and_right(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))))), hpr0)
  +hp2 = MB.eq_true_of_and_left(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))), hpr1)
  +hpr2 = MB.eq_true_of_and_right(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))), hpr1)
  +hp3 = MB.eq_true_of_and_left(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))), hpr2)
  +hpr3 = MB.eq_true_of_and_right(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))), hpr2)
  +hp4 = MB.eq_true_of_and_left(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))), hpr3)
  +hpr4 = MB.eq_true_of_and_right(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))), hpr3)
  +hp5 = MB.eq_true_of_and_left(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)), hpr4)
  +hpr5 = MB.eq_true_of_and_right(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)), hpr4)
  +hp6 = MB.eq_true_of_and_left(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L), hpr5)
  +hp7 = MB.eq_true_of_and_right(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L), hpr5)
  +hxL = MB.eq_true_of_and_left(RG.has(L, x), RG.sub(ps, L), hp2)
  +hpsL = MB.eq_true_of_and_right(RG.has(L, x), RG.sub(ps, L), hp2)
  +hxout = MB.eq_false_of_not_eq_true(RG.has(Con{s, cs}, x), MB.eq_true_of_and_left(Bool.not(RG.has(Con{s, cs}, x)), RG.none.in(ps, Con{s, cs}), hp3))
  +hpsout = MB.eq_true_of_and_right(Bool.not(RG.has(Con{s, cs}, x)), RG.none.in(ps, Con{s, cs}), hp3)
  +hxps = MB.eq_false_of_not_eq_true(RG.has(ps, x), MB.eq_true_of_and_left(Bool.not(RG.has(ps, x)), RG.distinct(ps), hp4))
  +hdps = MB.eq_true_of_and_right(Bool.not(RG.has(ps, x)), RG.distinct(ps), hp4)
  +hap0 = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hp0)
  +hm0L = sub_has(Con{s, cs}, L, m0, hp1, has_cons(s, cs, m0, hm))
  +hsLW = sub_trans(RG.without(RG.without(L, x), m0), RG.without(L, x), L, sub_without(RG.without(L, x), m0), sub_without(L, x))
  +hxLW = notin_sub(RG.without(RG.without(L, x), m0), RG.without(L, x), x, sub_without(RG.without(L, x), m0), notin_without(L, x))
  +hmLW = notin_without(RG.without(L, x), m0)
  +hr0 = MB.and_eq_true(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hp0, MB.and_eq_true(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), lay_sub(Con{s, cs}, L, d, hp1, hp5, hap0), MB.and_eq_true(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), bases_sub(Con{s, cs}, L, hp1, hp6), faces_sub(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, L, Con{s, cs}, hp1, hp1, hp7))))
  +hx0 = MB.and_eq_true(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs})), cross_of(Con{s, cs}, L, d, x, hp1, hp5, hxL, hxout), MB.and_eq_true(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs}), bases_at(L, x, hp6, hxL), fm_sub(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, L, Con{s, cs}, hp1, faces_at(L, AD.view(U32, LAT.fromT(U32, t)), d, L, x, hp7, hxL))))
  %e : {Pair.snd(P.H, U32, P.rd(R.join1(P.H{KM.MG{_}, a}, x, m0), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %ea : {Pair.snd(P.H, U32, P.rd(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x, m0), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, _}, j)) : U32}
  join1_keeps.m(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, x, m0, j, hft, hd32, hr0, hx0, hm, links_of_nodes(Con{s, cs}, L, d, j, hp1, hj), nodes_at(L, d, j, x, hj, hxL), nodes_at(L, d, j, m0, hj, hm0L), hjh,
    MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32), d), AD.slot(j, d)), ports_at(F, d, j, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))), hjf, fport(L, t, d, F, x, hft, hd32, hfit, hxL))),
    MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) + 1 : U32), d), AD.slot(j, d)), ports_at(F, d, j, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))), hjf, fport(L, t, d, F, m0, hft, hd32, hfit, hm0L))),
    LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))

# and the ports faced kept among F
def j1_faced.p(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +ps: List<&2, U32>, +L: List<&2, U32>, +x: U32, +m0: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hp: {RG.pend.ok(AD.view(U32, w), d, s, cs, Con{x, ps}, L) == True{} : Bool},
  +hm: {RG.has(cs, m0) == True{} : Bool}, +F: List<&2, U32>, hfi: {faced.in(L, AD.view(U32, w), d, F) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {faced.in(RG.without(RG.without(L, x), m0), AD.view(U32, RG.words(R.join1(P.H{KM.MG{w}, a}, x, m0))), d, F) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hfit = LAB.subst(Array<U32>, q => {faced.in(L, AD.view(U32, q), d, F) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hfi)
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hpt = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, q), d, s, cs, Con{x, ps}, L) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hp)
  +hp0 = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt)
  +hpr0 = MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt)
  +hp1 = MB.eq_true_of_and_left(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))))), hpr0)
  +hpr1 = MB.eq_true_of_and_right(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))))), hpr0)
  +hp2 = MB.eq_true_of_and_left(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))), hpr1)
  +hpr2 = MB.eq_true_of_and_right(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))), hpr1)
  +hp3 = MB.eq_true_of_and_left(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))), hpr2)
  +hpr3 = MB.eq_true_of_and_right(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))), hpr2)
  +hp4 = MB.eq_true_of_and_left(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))), hpr3)
  +hpr4 = MB.eq_true_of_and_right(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))), hpr3)
  +hp5 = MB.eq_true_of_and_left(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)), hpr4)
  +hpr5 = MB.eq_true_of_and_right(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)), hpr4)
  +hp6 = MB.eq_true_of_and_left(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L), hpr5)
  +hp7 = MB.eq_true_of_and_right(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L), hpr5)
  +hxL = MB.eq_true_of_and_left(RG.has(L, x), RG.sub(ps, L), hp2)
  +hpsL = MB.eq_true_of_and_right(RG.has(L, x), RG.sub(ps, L), hp2)
  +hxout = MB.eq_false_of_not_eq_true(RG.has(Con{s, cs}, x), MB.eq_true_of_and_left(Bool.not(RG.has(Con{s, cs}, x)), RG.none.in(ps, Con{s, cs}), hp3))
  +hpsout = MB.eq_true_of_and_right(Bool.not(RG.has(Con{s, cs}, x)), RG.none.in(ps, Con{s, cs}), hp3)
  +hxps = MB.eq_false_of_not_eq_true(RG.has(ps, x), MB.eq_true_of_and_left(Bool.not(RG.has(ps, x)), RG.distinct(ps), hp4))
  +hdps = MB.eq_true_of_and_right(Bool.not(RG.has(ps, x)), RG.distinct(ps), hp4)
  +hap0 = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hp0)
  +hm0L = sub_has(Con{s, cs}, L, m0, hp1, has_cons(s, cs, m0, hm))
  +hsLW = sub_trans(RG.without(RG.without(L, x), m0), RG.without(L, x), L, sub_without(RG.without(L, x), m0), sub_without(L, x))
  +hxLW = notin_sub(RG.without(RG.without(L, x), m0), RG.without(L, x), x, sub_without(RG.without(L, x), m0), notin_without(L, x))
  +hmLW = notin_without(RG.without(L, x), m0)
  +hr0 = MB.and_eq_true(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hp0, MB.and_eq_true(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), lay_sub(Con{s, cs}, L, d, hp1, hp5, hap0), MB.and_eq_true(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), bases_sub(Con{s, cs}, L, hp1, hp6), faces_sub(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, L, Con{s, cs}, hp1, hp1, hp7))))
  +hx0 = MB.and_eq_true(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs})), cross_of(Con{s, cs}, L, d, x, hp1, hp5, hxL, hxout), MB.and_eq_true(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs}), bases_at(L, x, hp6, hxL), fm_sub(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, L, Con{s, cs}, hp1, faces_at(L, AD.view(U32, LAT.fromT(U32, t)), d, L, x, hp7, hxL))))
  +hrt = hr0
  +hxt = hx0
  +hring = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)
  +hlay = MB.eq_true_of_and_left(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt))
  +hbases = MB.eq_true_of_and_left(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hfaces = MB.eq_true_of_and_right(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs})), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.layout(Con{s, cs}, d), Bool.and(RG.bases(Con{s, cs}), RG.faces(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}))), hrt)))
  +hap = MB.eq_true_of_and_right(RG.chain(AD.view(U32, LAT.fromT(U32, t)), d, cs, s, s), RG.apart.all(Con{s, cs}, d), hring)
  +hn = len_ok(t, d, s, cs, hft, hd32, hap)
  +eqW = without_eq(d, s, cs, m0, hap, hm)
  +subr = MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(RG.without(cs, m0), Con{s, cs}), has_self(s, cs), sub_cons_r(RG.without(cs, m0), s, cs, sub_without(cs, m0)))
  +hbm = MS.u32_eq_of_is_eq(P.base(m0), m0, bases_at(Con{s, cs}, m0, hbases, has_cons(s, cs, m0, hm)))
  +hrs = ring_split(AD.view(U32, LAT.fromT(U32, t)), d, s, cs, m0, hring, hm)
  +hnm = ME.subst(List<&2, U32>, q => {Nat.is_lt(List.length(&2, U32, q), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), cs, split_of_has(cs, m0, hm)), hn)
  +hwt = LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, Con{s, cs}) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m0 + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((m0 + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (m0 + 1 : U32), hft, hd32)), faces_at(Con{s, cs}, AD.view(U32, LAT.fromT(U32, t)), d, Con{s, cs}, m0, hfaces, has_cons(s, cs, m0, hm)))
  +hws = ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), cs, split_of_has(cs, m0, hm)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (m0 + 1 : U32))) + 1 : U32)), hwt))
  +hns = apart_notin(cs, d, s, MB.eq_true_of_and_left(RG.apart(cs, d, s), RG.apart.all(cs, d), hap))
  +nm = or_ff(U32.is_eq(s, m0), RG.has(RG.without(cs, m0), m0), ne_go(cs, s, m0, U32.is_eq(s, m0), {==}, hns, hm), notin_without(cs, m0))
  +om = ones_p3(Con{s, RG.without(cs, m0)}, Con{s, cs}, d, RG.last(lpre(cs, m0), s), subr, hlay,
    sub_has(Con{s, lpre(cs, m0)}, Con{s, cs}, RG.last(lpre(cs, m0), s), MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(lpre(cs, m0), Con{s, cs}), has_self(s, cs), sub_cons_r(lpre(cs, m0), s, cs, sub_lpre(cs, m0))), last_mem(lpre(cs, m0), s)))
  +hcx = MB.eq_true_of_and_left(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs})), hxt)
  +hbx = MS.u32_eq_of_is_eq(P.base(x), x, MB.eq_true_of_and_left(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs})), hxt)))
  +hut = LAB.subst(Maybe<&2, U32>, mm => {RG.faces.m(mm, d, Con{s, cs}) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))},
    Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t), d, (x + 1 : U32), hft, hd32)), MB.eq_true_of_and_right(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs}), MB.eq_true_of_and_right(RG.cross(Con{s, cs}, d, x), Bool.and(U32.is_eq(P.base(x), x), RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((x + 1 : U32), d)), d, Con{s, cs})), hxt)))
  %e : {faced.in(RG.without(RG.without(L, x), m0), AD.view(U32, RG.words(R.join1(P.H{KM.MG{_}, a}, x, m0))), d, F) == True{} : Bool}
  %ea : {faced.in(RG.without(RG.without(L, x), m0), AD.view(U32, RG.words(R.join1(P.H{KM.MG{LAT.fromT(U32, t)}, _}, x, m0))), d, F) == True{} : Bool}
  join1_faced.go(LAT.fromT(U32, t),
    LAT.fromT(V.Val, ta),
    d,
    s,
    lpre(cs, m0),
    x,
    m0,
    lpost(cs, m0),
    hft,
    hd32,
    hrs,
    hnm,
    ME.subst(List<&2, U32>, q => {RG.off.links(Con{s, q}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)) == True{} : Bool}, cs, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), Equal.sym(List<&2, U32>, List.append(&2, U32, lpre(cs, m0), Con{m0, lpost(cs, m0)}), cs, split_of_has(cs, m0, hm)), MB.eq_true_of_and_left(RG.off.links(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), RG.off.pos(Con{s, cs}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (x + 1 : U32))) + 1 : U32)), hut)),
    hws,
    RG.without(RG.without(L, x), m0),
    F,
    faced_sub(RG.without(RG.without(L, x), m0), AD.view(U32, LAT.fromT(U32, t)), d, L, F, hsLW, hfit),
    fport(L, t, d, F, x, hft, hd32, hfit, hxL),
    fport(L, t, d, F, m0, hft, hd32, hfit, hm0L),
    ones_p3(RG.without(RG.without(L, x), m0), L, d, RG.last(lpre(cs, m0), s), hsLW, hp5, sub_has(Con{s, cs}, L, RG.last(lpre(cs, m0), s), hp1, sub_has(Con{s, lpre(cs, m0)}, Con{s, cs}, RG.last(lpre(cs, m0), s), MB.and_eq_true(RG.has(Con{s, cs}, s), RG.sub(lpre(cs, m0), Con{s, cs}), has_self(s, cs), sub_cons_r(lpre(cs, m0), s, cs, sub_lpre(cs, m0))), last_mem(lpre(cs, m0), s)))),
    ME.subst(U32, q => {ones(RG.without(RG.without(L, x), m0), d, q) == True{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), ones_z0(RG.without(RG.without(L, x), m0), L, d, x, hsLW, hp5, hxL, hxLW)),
    ME.subst(U32, q => {ones(RG.without(RG.without(L, x), m0), d, (q + 1 : U32)) == True{} : Bool}, x, P.base(x), Equal.sym(U32, P.base(x), x, hbx), ones_z1(RG.without(RG.without(L, x), m0), L, d, x, hsLW, hp5, hxL, hxLW)),
    ME.subst(U32, q => {ones(RG.without(RG.without(L, x), m0), d, q) == True{} : Bool}, m0, P.base(m0), Equal.sym(U32, P.base(m0), m0, hbm), ones_z0(RG.without(RG.without(L, x), m0), L, d, m0, hsLW, hp5, hm0L, hmLW)),
    ME.subst(U32, q => {ones(RG.without(RG.without(L, x), m0), d, (q + 1 : U32)) == True{} : Bool}, m0, P.base(m0), Equal.sym(U32, P.base(m0), m0, hbm), ones_z1(RG.without(RG.without(L, x), m0), L, d, m0, hsLW, hp5, hm0L, hmLW)),
    ones_head(RG.without(RG.without(L, x), m0), L, d, hsLW, hp5),
    LAT.mirror(U32, LAT.fromT(U32, t)),
    LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))

def crossL_sub(m: Maybe<&2, U32>, +x: U32, +L: List<&2, U32>) -> {RG.sub(RG.cross.L(m, x, L), L) == True{} : Bool}:
  match m:
    case Some{+y}:
      sub_trans(RG.without(RG.without(L, x), y), RG.without(L, x), L, sub_without(RG.without(L, x), y), sub_without(L, x))
    case None{}:
      sub_refl(L)

def crk_step(+t: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +ps: List<&2, U32>, +L: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +far: U32, +F: List<&2, U32>, +j: U32, m: Maybe<&2, U32>, e: {RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far) == m : Maybe<&2, U32>},
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hpt: {RG.pend.ok(AD.view(U32, LAT.fromT(U32, t)), d, s, cs, Con{x, ps}, L) == True{} : Bool}, +hfit: {faced.in(L, AD.view(U32, LAT.fromT(U32, t)), d, F) == True{} : Bool},
    +hj: {RG.off.nodes(L, d, j) == True{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}, +hjf: {RG.off.ports(F, d, j) == True{} : Bool}) ->
    {Pair.snd(P.H, U32, P.rd(R.cross.k((P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, m), s, x, src, neg), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}:
  match m:
    case Some{+y}:
      j1_keeps.p(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, ps, L, x, y, hft, hd32, hpt, first_has(cs, AD.view(U32, LAT.fromT(U32, t)), d, far, y, e), F, j, hfit, hj, hjh, hjf, LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
    case None{}:
      cursor_keeps.m(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, x, src, neg, j, hft, hd32, nodes_at(L, d, j, x, hj, MB.eq_true_of_and_left(RG.has(L, x), RG.sub(ps, L), MB.eq_true_of_and_left(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))), MB.eq_true_of_and_right(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))))), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt))))), off_w3(d, s, j, nodes_at(L, d, j, s, hj, MB.eq_true_of_and_left(RG.has(L, s), RG.sub(cs, L), MB.eq_true_of_and_left(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L)))))), MB.eq_true_of_and_right(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt))))), LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))

def crf_step(+t: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +ps: List<&2, U32>, +L: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +far: U32, +F: List<&2, U32>, m: Maybe<&2, U32>, e: {RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far) == m : Maybe<&2, U32>},
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hpt: {RG.pend.ok(AD.view(U32, LAT.fromT(U32, t)), d, s, cs, Con{x, ps}, L) == True{} : Bool}, +hfit: {faced.in(L, AD.view(U32, LAT.fromT(U32, t)), d, F) == True{} : Bool}) ->
    {faced.in(RG.cross.L(m, x, L), AD.view(U32, RG.words(R.cross.k((P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, m), s, x, src, neg))), d, F) == True{} : Bool}:
  match m:
    case Some{+y}:
      j1_faced.p(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, ps, L, x, y, hft, hd32, hpt, first_has(cs, AD.view(U32, LAT.fromT(U32, t)), d, far, y, e), F, hfit, LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
    case None{}:
      cur_faced.p(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, ps, L, x, src, neg, hft, hd32, hpt, F, hfit, LAT.mirror(U32, LAT.fromT(U32, t)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))

def crk.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +ps: List<&2, U32>, +L: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +far: U32, +F: List<&2, U32>, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hp: {RG.pend.ok(AD.view(U32, w), d, s, cs, Con{x, ps}, L) == True{} : Bool}, hfi: {faced.in(L, AD.view(U32, w), d, F) == True{} : Bool}, +hj: {RG.off.nodes(L, d, j) == True{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}, +hjf: {RG.off.ports(F, d, j) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {Pair.snd(P.H, U32, P.rd(R.cross(P.H{KM.MG{w}, a}, s, x, src, neg, far), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hpt = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, q), d, s, cs, Con{x, ps}, L) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hp)
  +hfit = LAB.subst(Array<U32>, q => {faced.in(L, AD.view(U32, q), d, F) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hfi)
  +hr0 = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt)
  %e : {Pair.snd(P.H, U32, P.rd(R.cross(P.H{KM.MG{_}, a}, s, x, src, neg, far), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %ea : {Pair.snd(P.H, U32, P.rd(R.cross(P.H{KM.MG{LAT.fromT(U32, t)}, _}, s, x, src, neg, far), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, _}, j)) : U32}
  %Equal.sym(P.H & Maybe<&2, U32>, R.rg.find(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, far), (P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far)), find_exact.m(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, far, hft, hd32, hr0, LAT.mirror(U32, LAT.fromT(U32, t)))) :
    {Pair.snd(P.H, U32, P.rd(R.cross.k(_, s, x, src, neg), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  crk_step(t, ta, d, s, cs, ps, L, x, src, neg, far, F, j, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far), {==}, hft, hd32, hpt, hfit, hj, hjh, hjf)

def crf.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +cs: List<&2, U32>, +ps: List<&2, U32>, +L: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +far: U32, +F: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hp: {RG.pend.ok(AD.view(U32, w), d, s, cs, Con{x, ps}, L) == True{} : Bool}, hfi: {faced.in(L, AD.view(U32, w), d, F) == True{} : Bool},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {faced.in(RG.cross.L(RG.first(cs, AD.view(U32, w), d, far), x, L), AD.view(U32, RG.words(R.cross(P.H{KM.MG{w}, a}, s, x, src, neg, far))), d, F) == True{} : Bool}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  +hpt = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, q), d, s, cs, Con{x, ps}, L) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hp)
  +hfit = LAB.subst(Array<U32>, q => {faced.in(L, AD.view(U32, q), d, F) == True{} : Bool}, w, LAT.fromT(U32, t), Equal.sym(Array<U32>, LAT.fromT(U32, t), w, e), hfi)
  +hr0 = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, t)), d, s, cs), Bool.and(RG.sub(Con{s, cs}, L), Bool.and(RG.sub(Con{x, ps}, L), Bool.and(RG.none.in(Con{x, ps}, Con{s, cs}), Bool.and(RG.distinct(Con{x, ps}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, t)), d, L))))))), hpt)
  %e : {faced.in(RG.cross.L(RG.first(cs, AD.view(U32, _), d, far), x, L), AD.view(U32, RG.words(R.cross(P.H{KM.MG{_}, a}, s, x, src, neg, far))), d, F) == True{} : Bool}
  %ea : {faced.in(RG.cross.L(RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far), x, L), AD.view(U32, RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, t)}, _}, s, x, src, neg, far))), d, F) == True{} : Bool}
  %Equal.sym(P.H & Maybe<&2, U32>, R.rg.find(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, s, far), (P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far)), find_exact.m(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, s, cs, far, hft, hd32, hr0, LAT.mirror(U32, LAT.fromT(U32, t)))) :
    {faced.in(RG.cross.L(RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far), x, L), AD.view(U32, RG.words(R.cross.k(_, s, x, src, neg))), d, F) == True{} : Bool}
  crf_step(t, ta, d, s, cs, ps, L, x, src, neg, far, F, RG.first(cs, AD.view(U32, LAT.fromT(U32, t)), d, far), {==}, hft, hd32, hpt, hfit)

# the crossings in turn: each one's frame, the ports faced kept among
# the first ones, by induction on the crossings, the find the code's own
def crk.go(cl: List<&2, R.FzC>, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +s: U32, +rt: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hfm: {AD.full(U32, map, dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
  hp: {RG.pend.ok(AD.view(U32, w), d, s, rt, RG.pls(cl, AD.view(U32, map), dm), L) == True{} : Bool}, hfi: {faced.in(L, AD.view(U32, w), d, F) == True{} : Bool},
  +hj: {RG.off.nodes(L, d, j) == True{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}, +hjf: {RG.off.ports(F, d, j) == True{} : Bool},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {Pair.snd(P.H, U32, P.rd(Pair.snd(Array<U32>, P.H, R.crossings(cl, (map, P.H{KM.MG{w}, a}), s)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  match cl:
    case Nil{}:
      {==}
    case Con{c, +rest}:
      match c:
        case R.FzC{+at, +src, +neg, +far}:
          (+tw, +ew) = mw
          (+ta, +ea) = ma
          (+tm, +em) = mm
          +hft = LAP.full_t(U32, w, tw, d, ew, hf)
          +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
          +ePL = ME.subst(Maybe<&2, U32>, q => {RG.pl.of(q) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)) : U32}, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm)), LA.get_view(U32, LAT.fromT(U32, tm), dm, at, hfmt, hdm), {==})
          +hpa = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, q), d, s, rt, Con{RG.pl.of(List.get(&2, U32, AD.view(U32, map), AD.slot(at, dm))), RG.pls(rest, AD.view(U32, map), dm)}, L) == True{} : Bool}, w, LAT.fromT(U32, tw), Equal.sym(Array<U32>, LAT.fromT(U32, tw), w, ew), hp)
          +hpb = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, LAT.fromT(U32, tw)), d, s, rt, Con{RG.pl.of(List.get(&2, U32, AD.view(U32, q), AD.slot(at, dm))), RG.pls(rest, AD.view(U32, q), dm)}, L) == True{} : Bool}, map, LAT.fromT(U32, tm), Equal.sym(Array<U32>, LAT.fromT(U32, tm), map, em), hpa)
          +hp3 = ME.subst(U32, q => {RG.pend.ok(AD.view(U32, LAT.fromT(U32, tw)), d, s, rt, Con{q, RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm)}, L) == True{} : Bool}, RG.pl.of(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(at, dm))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), ePL, hpb)
          +hr0 = MB.eq_true_of_and_left(RG.ring(AD.view(U32, LAT.fromT(U32, tw)), d, s, rt), Bool.and(RG.sub(Con{s, rt}, L), Bool.and(RG.sub(Con{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm)}, L), Bool.and(RG.none.in(Con{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm)}, Con{s, rt}), Bool.and(RG.distinct(Con{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm)}), Bool.and(RG.layout(L, d), Bool.and(RG.bases(L), RG.faces(L, AD.view(U32, LAT.fromT(U32, tw)), d, L))))))), hp3)
          +hfx = cross_full.m(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), d, s, rt, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far, hft, hd32, hr0, LAT.mirror(U32, LAT.fromT(U32, tw)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
          +hfit = LAB.subst(Array<U32>, q => {faced.in(L, AD.view(U32, q), d, F) == True{} : Bool}, w, LAT.fromT(U32, tw), Equal.sym(Array<U32>, LAT.fromT(U32, tw), w, ew), hfi)
          +hpx = cross_pend.m(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), d, s, rt, RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm), L, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far, hft, hd32, hp3, LAT.mirror(U32, LAT.fromT(U32, tw)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
          +hfin = crf.m(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), d, s, rt, RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm), L, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far, F, hft, hd32, hp3, hfit, LAT.mirror(U32, LAT.fromT(U32, tw)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
          +kst = crk.m(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), d, s, rt, RG.pls(rest, AD.view(U32, LAT.fromT(U32, tm)), dm), L, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far, F, j, hft, hd32, hp3, hfit, hj, hjh, hjf, LAT.mirror(U32, LAT.fromT(U32, tw)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))
          %ew : {Pair.snd(P.H, U32, P.rd(Pair.snd(Array<U32>, P.H, R.crossings(Con{R.FzC{at, src, neg, far}, rest}, (map, P.H{KM.MG{_}, a}), s)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
          %ea : {Pair.snd(P.H, U32, P.rd(Pair.snd(Array<U32>, P.H, R.crossings(Con{R.FzC{at, src, neg, far}, rest}, (map, P.H{KM.MG{LAT.fromT(U32, tw)}, _}), s)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, tw)}, _}, j)) : U32}
          %em : {Pair.snd(P.H, U32, P.rd(Pair.snd(Array<U32>, P.H, R.crossings(Con{R.FzC{at, src, neg, far}, rest}, (_, P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}), s)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, j)) : U32}
          %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, tm), at), (LAT.fromT(U32, tm), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at))), LA.get_pair(U32, LAT.fromT(U32, tm), at)) :
            {Pair.snd(P.H, U32, P.rd(Pair.snd(Array<U32>, P.H, R.crossings(rest, R.crossing.pl(_, P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, src, neg, far), s)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, j)) : U32}
          %cross_parts.m(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), d, s, rt, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far, hft, hd32, hr0, LAT.mirror(U32, LAT.fromT(U32, tw)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))) :
            {Pair.snd(P.H, U32, P.rd(Pair.snd(Array<U32>, P.H, R.crossings(rest, (LAT.fromT(U32, tm), _), s)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, j)) : U32}
          Equal.trans(U32, Pair.snd(P.H, U32, P.rd(Pair.snd(Array<U32>, P.H, R.crossings(rest, (LAT.fromT(U32, tm), P.H{KM.MG{RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far))}, LAT.fromT(V.Val, ta)}), s)), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far))}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, j)),
            crk.go(rest, RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far)), LAT.fromT(V.Val, ta), LAT.fromT(U32, tm), d, dm, s, RG.cross.t(RG.first(rt, AD.view(U32, LAT.fromT(U32, tw)), d, far), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), rt), RG.cross.L(RG.first(rt, AD.view(U32, LAT.fromT(U32, tw)), d, far), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), L), F, j, hfx, hd32, hfmt, hdm, hpx, hfin,
              off_nodes_sub(RG.cross.L(RG.first(rt, AD.view(U32, LAT.fromT(U32, tw)), d, far), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), L), L, d, j, crossL_sub(RG.first(rt, AD.view(U32, LAT.fromT(U32, tw)), d, far), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), L), hj), hjh, hjf,
              LAT.mirror(U32, RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far))), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)), LAT.mirror(U32, LAT.fromT(U32, tm))),
            ME.subst(P.H, q => {Pair.snd(P.H, U32, P.rd(q, j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, j)) : U32}, R.cross(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far), P.H{KM.MG{RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far))}, LAT.fromT(V.Val, ta)}, Equal.sym(P.H, P.H{KM.MG{RG.words(R.cross(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far))}, LAT.fromT(V.Val, ta)}, R.cross(P.H{KM.MG{LAT.fromT(U32, tw)}, LAT.fromT(V.Val, ta)}, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far), cross_parts.m(LAT.fromT(U32, tw), LAT.fromT(V.Val, ta), d, s, rt, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), at)), src, neg, far, hft, hd32, hr0, LAT.mirror(U32, LAT.fromT(U32, tw)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)))), kst))

def crossings_keeps.m(-w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +s: U32, +rt: List<&2, U32>, +L: List<&2, U32>, +cs: List<&2, R.FzC>, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hfm: {AD.full(U32, map, dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
  hp: {RG.pend.ok(AD.view(U32, w), d, s, rt, RG.pls(cs, AD.view(U32, map), dm), L) == True{} : Bool},
  +hj: {RG.off.nodes(L, d, j) == True{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}, hjf: {RG.off.ports(RG.faced(L, AD.view(U32, w), d), d, j) == True{} : Bool},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {Pair.snd(P.H, U32, P.rd(Pair.snd(Array<U32>, P.H, R.crossings(cs, (map, P.H{KM.MG{w}, a}), s)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+tw, +ew) = mw
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, w, tw, d, ew, hf)
  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
  +hpa = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, q), d, s, rt, RG.pls(cs, AD.view(U32, map), dm), L) == True{} : Bool}, w, LAT.fromT(U32, tw), Equal.sym(Array<U32>, LAT.fromT(U32, tw), w, ew), hp)
  +hpb = LAB.subst(Array<U32>, q => {RG.pend.ok(AD.view(U32, LAT.fromT(U32, tw)), d, s, rt, RG.pls(cs, AD.view(U32, q), dm), L) == True{} : Bool}, map, LAT.fromT(U32, tm), Equal.sym(Array<U32>, LAT.fromT(U32, tm), map, em), hpa)
  +hjft = LAB.subst(Array<U32>, q => {RG.off.ports(RG.faced(L, AD.view(U32, q), d), d, j) == True{} : Bool}, w, LAT.fromT(U32, tw), Equal.sym(Array<U32>, LAT.fromT(U32, tw), w, ew), hjf)
  %ew : {Pair.snd(P.H, U32, P.rd(Pair.snd(Array<U32>, P.H, R.crossings(cs, (map, P.H{KM.MG{_}, a}), s)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %em : {Pair.snd(P.H, U32, P.rd(Pair.snd(Array<U32>, P.H, R.crossings(cs, (_, P.H{KM.MG{LAT.fromT(U32, tw)}, a}), s)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, tw)}, a}, j)) : U32}
  crk.go(cs, LAT.fromT(U32, tw), a, LAT.fromT(U32, tm), d, dm, s, rt, L, RG.faced(L, AD.view(U32, LAT.fromT(U32, tw)), d), j, hft, hd32, hfmt, hdm, hpb, faced_init(L, L, tw, d, hft, hd32, sub_refl(L)), hj, hjh, hjft, LAT.mirror(U32, LAT.fromT(U32, tw)), ma, LAT.mirror(U32, LAT.fromT(U32, tm)))

def Laws.crossings_keeps(w, a, map, d, dm, s, t, L, cs, j, hf, hd32, hfm, hdm, hp, hj, hjh, hjf):
  crossings_keeps.m(w, a, map, d, dm, s, t, L, cs, j, hf, hd32, hfm, hdm, hp, hj, hjh, hjf, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))
