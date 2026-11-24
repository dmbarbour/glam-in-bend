# The splice's proofs (glam/SPLICE_LAWS.bend; cells-freeze.nested.host.splice).
# The splice's state threaded step by step, each heap restated in its
# parts by one lemma over a heap variable (heta) rather than one per
# operation; the spike's frame laws cited through spike/LAWS.bend.

import Base
import ./SPLICE_LAWS.bend as Laws
import ../spike/HEAP_LAWS.bend as SL
import ../spike/HEAP_PROOF.bend as SP
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/tpl.bend as T
import ../spike/rules.bend as R
import ../spike/net.bend as N
import ../spike/kmodel.bend as KMd
import ./splice_copy.bend as S
import ./splice_model.bend as SM
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import 0x8ae61ec3a6615abd35f196c07232ad28/string.bend as MS
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MN
import 0x8ae61ec3a6615abd35f196c07232ad28/list.bend as ML
import 0x8ae61ec3a6615abd35f196c07232ad28/u32.bend as MU
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/LAWS.bend as LA
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/PROOF.bend as LAP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_base.bend as LAB
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD
import 0x96ab58f86121cb4f3fb48b3c8a045989/LAWS.bend as WL
import 0x96ab58f86121cb4f3fb48b3c8a045989/PROOF.bend as WP

# any heap in its parts
def heta(h: P.H) -> {P.H{KM.MG{KMd.words(h)}, KMd.vals(h)} == h : P.H}:
  match h:
    case P.H{w, a}:
      match w:
        case KM.MG{x}:
          {==}

# the word a view of full words holds, the array's own
def word_get(w: Array<U32>, +d: Nat, +i: U32, hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
  {KMd.word(AD.view(U32, w), d, i) == Pair.snd(Array<U32>, U32, Array.get(U32, w, i)) : U32}:
  %LA.get_view(U32, w, d, i, hf, hd32) : {KMd.word.m(_) == Pair.snd(Array<U32>, U32, Array.get(U32, w, i)) : U32}
  {==}

# a node taken keeps the words full
def node_full(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +fh: U32, +hd: U32, +p: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, hfh: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_fh())) == fh : U32}, hne: {U32.is_eq(fh, 0) == False{} : Bool}, m: LAT.Mirror(U32, w)) ->
  {AD.full(U32, KMd.words(Pair.fst(P.H, U32, P.node(P.H{KM.MG{w}, a}, hd, p))), d) == True{} : Bool}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +hfht = LAB.subst(Array<U32>, q => {Pair.snd(Array<U32>, U32, Array.get(U32, q, P.at_fh())) == fh : U32}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e), hfh)
  %e : {AD.full(U32, KMd.words(Pair.fst(P.H, U32, P.node(P.H{KM.MG{_}, a}, hd, p))), d) == True{} : Bool}
  %Equal.sym(P.H & U32, P.alloc(P.H{KM.MG{LAT.fromT(U32, t0)}, a}), (P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))))}, a}, ((fh - 1 : U32) << 2n : U32)), SP.alloc_pop(t0, a, fh, hfht, hne)) :
    {AD.full(U32, KMd.words(Pair.fst(P.H, U32, P.node.fin(_, hd, p))), d) == True{} : Bool}
  LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), ((fh - 1 : U32) << 2n : U32), hd), d, (((fh - 1 : U32) << 2n : U32) + P.node.word(hd) : U32), p, LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32)))), d, ((fh - 1 : U32) << 2n : U32), hd, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ((((fh - 1 : U32) << 2n : U32)) + 1 : U32))), hft)))

# an error counted, or none, keeps the words full
def err_full(b: Bool, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}) ->
  {AD.full(U32, KMd.words(P.err_if(b, P.H{KM.MG{LAT.fromT(U32, t0)}, a})), d) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), P.at_errs()), (LAT.fromT(U32, t0), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_errs()))), LA.get_pair(U32, LAT.fromT(U32, t0), P.at_errs())) :
        {AD.full(U32, KMd.words(P.h_err.n(KM.m_get.fin(_), a)), d) == True{} : Bool}
      LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_errs(), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_errs())) + 1 : U32), hft)
    case False{}:
      hft

# the value table's put keeps the words full, whatever it computed
def dtb_full(+t0: LAT.Tree<U32>, tb: P.DT, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}) ->
  {AD.full(U32, KMd.words(P.dt_back(KM.MG{LAT.fromT(U32, t0)}, tb)), d) == True{} : Bool}:
  match tb:
    case P.DT{a2, +fh, +n, +cap, +dd}:
      LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), P.at_tn(), n), P.at_tcap(), cap), d, P.at_td(), U32.from_nat(dd), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), P.at_tn(), n), d, P.at_tcap(), cap, LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_tfh(), fh), d, P.at_tn(), n, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_tfh(), fh, hft))))

def dto_full(+t0: LAT.Tree<U32>, r: P.DT & U32, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}) ->
  {AD.full(U32, KMd.words(Pair.fst(P.H, U32, P.dt_op.fin(r, KM.MG{LAT.fromT(U32, t0)}))), d) == True{} : Bool}:
  match r:
    case (tb, +i):
      dtb_full(t0, tb, d, hft)

def tab_full(+t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +x: V.Val, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}) ->
  {AD.full(U32, KMd.words(Pair.fst(P.H, U32, P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, x))), d) == True{} : Bool}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tfh()), (LAT.fromT(U32, t0), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tfh()))), LA.get_pair(U32, LAT.fromT(U32, t0), P.at_tfh())) :
    {AD.full(U32, KMd.words(Pair.fst(P.H, U32, P.tab_put.t(P.dt.fh(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), x))), d) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tn()), (LAT.fromT(U32, t0), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tn()))), LA.get_pair(U32, LAT.fromT(U32, t0), P.at_tn())) :
    {AD.full(U32, KMd.words(Pair.fst(P.H, U32, P.tab_put.t(P.dt.n(KM.m_get.fin(_), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tfh()))), x))), d) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tcap()), (LAT.fromT(U32, t0), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tcap()))), LA.get_pair(U32, LAT.fromT(U32, t0), P.at_tcap())) :
    {AD.full(U32, KMd.words(Pair.fst(P.H, U32, P.tab_put.t(P.dt.cap(KM.m_get.fin(_), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tfh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tn()))), x))), d) == True{} : Bool}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), P.at_td()), (LAT.fromT(U32, t0), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_td()))), LA.get_pair(U32, LAT.fromT(U32, t0), P.at_td())) :
    {AD.full(U32, KMd.words(Pair.fst(P.H, U32, P.tab_put.t(P.dt.d(KM.m_get.fin(_), LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tfh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tn())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tcap()))), x))), d) == True{} : Bool}
  dto_full(t0, P.dt_put(P.DT{LAT.fromT(V.Val, ta), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tfh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tn())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_tcap())), U32.to_nat(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_td())))}, x), d, hft)

def pwt_full(r: P.H & U32, +f: U32, +d: Nat, h: {AD.full(U32, KMd.words(Pair.fst(P.H, U32, r)), d) == True{} : Bool}) ->
  {AD.full(U32, KMd.words(Pair.fst(P.H, P.PW, P.pw.tab(r, f))), d) == True{} : Bool}:
  match r:
    case (h2, +i):
      h

# a value put keeps the words full, P.put's cases as it takes them
def put2_f(t: List<&2, V.Val>, +op: U32, +need: U32, +a: U32, +v: V.Val, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}) ->
    {AD.full(U32, KMd.words(Pair.fst(P.H, P.PW, P.put.two(t, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, op, need, a, v))), d) == True{} : Bool}:
  match t:
    case Nil{}:
      pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
    case Con{x, +u}:
      match x:
        case V.VNum{+b}:
          match u:
            case Nil{}:
              pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, V.VP2{op, need, a, b}), P.benc(op, need), d, tab_full(t0, ta, V.VP2{op, need, a, b}, d, hft))
            case Con{+y, +z}:
              pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VUnit{}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VLazy{+h}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VFun{+op2, +need2, +args2}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VList{+xs}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VDict{+es}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VErr{+e}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VFree{+next}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VP2{+op2, +need2, +a2, +b2}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))

def putgo_f(args: List<&2, V.Val>, +op: U32, +need: U32, +v: V.Val, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}) ->
    {AD.full(U32, KMd.words(Pair.fst(P.H, P.PW, P.put.fun.go(args, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, op, need, v))), d) == True{} : Bool}:
  match args:
    case Nil{}:
      hft
    case Con{x, +t}:
      match x:
        case V.VNum{+n}:
          match t:
            case Nil{}:
              hft
            case Con{+y, +z}:
              put2_f(Con{y, z}, op, need, n, v, t0, ta, d, hft)
        case V.VUnit{}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VLazy{+h}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VFun{+op2, +need2, +args2}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VList{+xs}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VDict{+es}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VErr{+e}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VFree{+next}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))
        case V.VP2{+op2, +need2, +a2, +b2}:
          pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), P.benc(op, need), d, tab_full(t0, ta, v, d, hft))

def putfun_f(fits: Bool, args: List<&2, V.Val>, +op: U32, +need: U32, +v: V.Val, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}) ->
    {AD.full(U32, KMd.words(Pair.fst(P.H, P.PW, P.put.fun(fits, args, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, op, need, v))), d) == True{} : Bool}:
  match fits:
    case True{}:
      putgo_f(args, op, need, v, t0, ta, d, hft)
    case False{}:
      pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), 0, d, tab_full(t0, ta, v, d, hft))

def put_f(v: V.Val, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}) ->
    {AD.full(U32, KMd.words(Pair.fst(P.H, P.PW, P.put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v))), d) == True{} : Bool}:
  match v:
    case V.VNum{+n}:
      hft
    case V.VFun{+op, +need, +args}:
      putfun_f(P.bfits(op, need), args, op, need, V.VFun{op, need, args}, t0, ta, d, hft)
    case V.VP2{+op, +need, +a, +b}:
      putfun_f(P.bfits(op, need), [V.VNum{a}, V.VNum{b}], op, need, V.VP2{op, need, a, b}, t0, ta, d, hft)
      case V.VUnit{}:
        pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, V.VUnit{}), 0, d, tab_full(t0, ta, V.VUnit{}, d, hft))
      case V.VLazy{+h}:
        pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, V.VLazy{h}), 0, d, tab_full(t0, ta, V.VLazy{h}, d, hft))
      case V.VList{+xs}:
        pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, V.VList{xs}), 0, d, tab_full(t0, ta, V.VList{xs}, d, hft))
      case V.VDict{+es}:
        pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, V.VDict{es}), 0, d, tab_full(t0, ta, V.VDict{es}, d, hft))
      case V.VErr{+e}:
        pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, V.VErr{e}), 0, d, tab_full(t0, ta, V.VErr{e}, d, hft))
      case V.VFree{+next}:
        pwt_full(P.tab_put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, V.VFree{next}), 0, d, tab_full(t0, ta, V.VFree{next}, d, hft))

# The step: each template node a pop after what comes before it (nothing,
# an error counted, or a value put), in one form
def pwm(pw: P.PW) -> U32:
  match pw:
    case P.PW{+m, +f, +w}:
      m

def pwf(pw: P.PW) -> U32:
  match pw:
    case P.PW{+m, +f, +w}:
      f

def pww(pw: P.PW) -> U32:
  match pw:
    case P.PW{+m, +f, +w}:
      w

def newpw(r: P.H & P.PW, +k: U32) ->
  {S.sp.new_pw(r, k) == P.node(Pair.fst(P.H, P.PW, r), P.hd2(k, pwm(Pair.snd(P.H, P.PW, r)), pwf(Pair.snd(P.H, P.PW, r))), pww(Pair.snd(P.H, P.PW, r))) : P.H & U32}:
  match r:
    case (h, pw):
      match pw:
        case P.PW{+m, +f, +w}:
          {==}

def pre.p(pp: V.Pay, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>) -> P.H:
  match pp:
    case V.PVal{+v}:
      Pair.fst(P.H, P.PW, P.put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v))
    case V.PLvl{+l}:
      P.err_if(P.too_big(l), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)})
    case V.PLift{+i, +up, +amt}:
      P.err_if(P.too_big(i) || U32.is_ge(amt, 2147483648), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)})
    case V.PNone{}:
      P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}
    case V.PFan{+f}:
      P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}

def hd.p(pp: V.Pay, +k: R.NodeKind, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>) -> U32:
  match pp:
    case V.PVal{+v}:
      P.hd2(N.kcode(k), pwm(Pair.snd(P.H, P.PW, P.put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v))), pwf(Pair.snd(P.H, P.PW, P.put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v))))
    case V.PLvl{+l}:
      P.hd(N.kcode(k), l)
    case V.PLift{+i, +up, +amt}:
      P.hd(N.kcode(k), i)
    case V.PNone{}:
      P.bare_hd(N.kcode(k))
    case V.PFan{+f}:
      P.bare_hd(N.kcode(k))

def pl.p(pp: V.Pay, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>) -> U32:
  match pp:
    case V.PVal{+v}:
      pww(Pair.snd(P.H, P.PW, P.put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v)))
    case V.PLvl{+l}:
      0
    case V.PLift{+i, +up, +amt}:
      P.lift_word(up, amt)
    case V.PNone{}:
      0
    case V.PFan{+f}:
      0

def pre(t: T.TNode, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +by: U32) -> P.H:
  match t:
    case T.TF{+k, +site, +lvl}:
      P.err_if(P.fan_too_big(U32.is_eq(V.raise_lvl(by, lvl), V.nolvl()), site, V.raise_lvl(by, lvl)), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)})
    case T.TN{+k, +p}:
      pre.p(V.raise_pay(by, p), t0, ta)

def hdf(t: T.TNode, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +by: U32) -> U32:
  match t:
    case T.TF{+k, +site, +lvl}:
      P.fan_hd(N.kcode(k), site, V.raise_lvl(by, lvl))
    case T.TN{+k, +p}:
      hd.p(V.raise_pay(by, p), k, t0, ta)

def plf(t: T.TNode, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +by: U32) -> U32:
  match t:
    case T.TF{+k, +site, +lvl}:
      0
    case T.TN{+k, +p}:
      pl.p(V.raise_pay(by, p), t0, ta)

def nf.p(pp: V.Pay, +k: R.NodeKind, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>) ->
  {S.sp.tn(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, k, pp) == P.node(pre.p(pp, t0, ta), hd.p(pp, k, t0, ta), pl.p(pp, t0, ta)) : P.H & U32}:
  match pp:
    case V.PVal{+v}:
      newpw(P.put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v), N.kcode(k))
    case V.PLvl{+l}:
      {==}
    case V.PLift{+i, +up, +amt}:
      {==}
    case V.PNone{}:
      {==}
    case V.PFan{+f}:
      {==}

def nf(t: T.TNode, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +by: U32) ->
  {S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by) == P.node(pre(t, t0, ta, by), hdf(t, t0, ta, by), plf(t, t0, ta, by)) : P.H & U32}:
  match t:
    case T.TF{+k, +site, +lvl}:
      {==}
    case T.TN{+k, +p}:
      nf.p(V.raise_pay(by, p), k, t0, ta)

# What comes before each pop writes only the header's words a splice
# writes, and keeps the words full
def spput(q: P.H & U32, -map: Array<U32>, +i: U32) ->
  {S.sp.put(q, map, i) == S.Sp{Pair.fst(P.H, U32, q), Array.set(U32, map, i, Pair.snd(P.H, U32, q))} : S.Sp}:
  match q:
    case (h, +r):
      {==}

def pre_rd.p(pp: V.Pay, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +ix: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {KMd.off.words(KMd.hdr_words(), d, ix) == True{} : Bool}) ->
  {Pair.snd(P.H, U32, P.rd(pre.p(pp, t0, ta), ix)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ix)) : U32}:
  match pp:
    case V.PVal{+v}:
      Equal.trans(U32, Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, P.PW, P.put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v)), ix)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, ix)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ix)), SL.put_keeps(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), d, v, ix, hft, hd32, MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(ix, d))), KMd.off.words(KMd.tab_words(), d, ix), hi)), SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), ix))
    case V.PLvl{+l}:
      Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.err_if(P.too_big(l), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}), ix)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, ix)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ix)), SL.err_keeps(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), d, P.too_big(l), ix, hft, hd32, MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(ix, d))), KMd.off.words(Nil{}, d, ix), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(ix, d))), KMd.off.words(KMd.tab_words(), d, ix), hi), {==})), SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), ix))
    case V.PLift{+i2, +up, +amt}:
      Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.err_if(P.too_big(i2) || U32.is_ge(amt, 2147483648), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}), ix)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, ix)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ix)), SL.err_keeps(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), d, P.too_big(i2) || U32.is_ge(amt, 2147483648), ix, hft, hd32, MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(ix, d))), KMd.off.words(Nil{}, d, ix), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(ix, d))), KMd.off.words(KMd.tab_words(), d, ix), hi), {==})), SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), ix))
    case V.PNone{}:
      SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), ix)
    case V.PFan{+f}:
      SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), ix)

def pre_rd(t: T.TNode, +by: U32, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +ix: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {KMd.off.words(KMd.hdr_words(), d, ix) == True{} : Bool}) ->
  {Pair.snd(P.H, U32, P.rd(pre(t, t0, ta, by), ix)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ix)) : U32}:
  match t:
    case T.TF{+k, +site, +lvl}:
      Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.err_if(P.fan_too_big(U32.is_eq(V.raise_lvl(by, lvl), V.nolvl()), site, V.raise_lvl(by, lvl)), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}), ix)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, ix)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ix)), SL.err_keeps(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), d, P.fan_too_big(U32.is_eq(V.raise_lvl(by, lvl), V.nolvl()), site, V.raise_lvl(by, lvl)), ix, hft, hd32, MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(ix, d))), KMd.off.words(Nil{}, d, ix), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(ix, d))), KMd.off.words(KMd.tab_words(), d, ix), hi), {==})), SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), ix))
    case T.TN{+k, +p}:
      pre_rd.p(V.raise_pay(by, p), t0, ta, d, ix, hft, hd32, hi)

def pre_get(+t: T.TNode, +by: U32, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +ix: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {KMd.off.words(KMd.hdr_words(), d, ix) == True{} : Bool}) ->
  {Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), ix)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ix)) : U32}:
  ME.trans3(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), ix)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, ix)), Pair.snd(P.H, U32, P.rd(pre(t, t0, ta, by), ix)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ix)), Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, ix)), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), ix)), SP.rd_get(KMd.words(pre(t, t0, ta, by)), KMd.vals(pre(t, t0, ta, by)), ix)), ME.subst(P.H, x => {Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, ix)) == Pair.snd(P.H, U32, P.rd(x, ix)) : U32}, P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, pre(t, t0, ta, by), heta(pre(t, t0, ta, by)), {==}), pre_rd(t, by, t0, ta, d, ix, hft, hd32, hi))

def pre_full.p(pp: V.Pay, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}) ->
  {AD.full(U32, KMd.words(pre.p(pp, t0, ta)), d) == True{} : Bool}:
  match pp:
    case V.PVal{+v}:
      put_f(v, t0, ta, d, hft)
    case V.PLvl{+l}:
      err_full(P.too_big(l), t0, LAT.fromT(V.Val, ta), d, hft)
    case V.PLift{+i2, +up, +amt}:
      err_full(P.too_big(i2) || U32.is_ge(amt, 2147483648), t0, LAT.fromT(V.Val, ta), d, hft)
    case V.PNone{}:
      hft
    case V.PFan{+f}:
      hft

def pre_full(t: T.TNode, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +by: U32, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}) ->
  {AD.full(U32, KMd.words(pre(t, t0, ta, by)), d) == True{} : Bool}:
  match t:
    case T.TF{+k, +site, +lvl}:
      err_full(P.fan_too_big(U32.is_eq(V.raise_lvl(by, lvl), V.nolvl()), site, V.raise_lvl(by, lvl)), t0, LAT.fromT(V.Val, ta), d, hft)
    case T.TN{+k, +p}:
      pre_full.p(V.raise_pay(by, p), t0, ta, d, hft)

# A step: the frame of a pop after what comes before it
def sf(+t: T.TNode, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +by: U32, +d: Nat, +n: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hne: {U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), 0) == False{} : Bool}, +hidx: {KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) == n : U32}, +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}, +j: U32, +hjn: {KMd.off.words(KMd.nw(n), d, j) == True{} : Bool}, +hjh: {KMd.off.words(KMd.hdr_all(), d, j) == True{} : Bool}) ->
  {Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}:
  %Equal.sym(P.H & U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), P.node(pre(t, t0, ta, by), hdf(t, t0, ta, by), plf(t, t0, ta, by)), nf(t, t0, ta, by)) :
    {Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, _)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}
  %heta(pre(t, t0, ta, by)) :
    {Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, P.node(_, hdf(t, t0, ta, by), plf(t, t0, ta, by)))), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}
  %SP.rd_get(KMd.words(Pair.fst(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by)))), KMd.vals(Pair.fst(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by)))), j) : {_ == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}
  %Equal.sym(P.H, P.H{KM.MG{KMd.words(Pair.fst(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by))))}, KMd.vals(Pair.fst(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by))))}, Pair.fst(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by))), heta(Pair.fst(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by))))) : {Pair.snd(P.H, U32, P.rd(_, j)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)) : U32}
  ME.trans3(U32, Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by))), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, j)), Pair.snd(P.H, U32, P.rd(pre(t, t0, ta, by), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), SL.node_keeps(KMd.words(pre(t, t0, ta, by)), KMd.vals(pre(t, t0, ta, by)), d, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), hdf(t, t0, ta, by), plf(t, t0, ta, by), j, pre_full(t, t0, ta, by, d, hft), hd32, {==}, ME.subst(U32, x => {U32.is_eq(x, 0) == False{} : Bool}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), pre_get(t, by, t0, ta, d, P.at_fh(), hft, hd32, hhd)), hne), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d))), KMd.off.words(Con{P.at_errs(), Con{P.at_tfh(), Con{P.at_tn(), Con{P.at_tcap(), Con{P.at_td(), Nil{}}}}}}, d, j), hjh)), ME.subst(U32, x => {Nat.is_eq(AD.slot(x, d), AD.slot(j, d)) == False{} : Bool}, n, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), Equal.sym(U32, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), n, ME.subst(U32, x => {KMd.at_idx(x) == n : U32}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), pre_get(t, by, t0, ta, d, P.at_fh(), hft, hd32, hhd)), hidx)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(n, d), AD.slot(j, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(n, d), AD.slot(j, d))), KMd.off.words(Con{(n + 1 : U32), Con{(n + 2 : U32), Con{(n + 3 : U32), Nil{}}}}, d, j), hjn))), ME.subst(U32, x => {Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, n, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), Equal.sym(U32, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), n, ME.subst(U32, x => {KMd.at_idx(x) == n : U32}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), pre_get(t, by, t0, ta, d, P.at_fh(), hft, hd32, hhd)), hidx)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((n + 1 : U32), d), AD.slot(j, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((n + 1 : U32), d), AD.slot(j, d))), KMd.off.words(Con{(n + 2 : U32), Con{(n + 3 : U32), Nil{}}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(n, d), AD.slot(j, d))), KMd.off.words(Con{(n + 1 : U32), Con{(n + 2 : U32), Con{(n + 3 : U32), Nil{}}}}, d, j), hjn)))), ME.subst(U32, x => {Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(j, d)) == False{} : Bool}, n, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), Equal.sym(U32, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), n, ME.subst(U32, x => {KMd.at_idx(x) == n : U32}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), pre_get(t, by, t0, ta, d, P.at_fh(), hft, hd32, hhd)), hidx)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((n + 2 : U32), d), AD.slot(j, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((n + 2 : U32), d), AD.slot(j, d))), KMd.off.words(Con{(n + 3 : U32), Nil{}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((n + 1 : U32), d), AD.slot(j, d))), KMd.off.words(Con{(n + 2 : U32), Con{(n + 3 : U32), Nil{}}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(n, d), AD.slot(j, d))), KMd.off.words(Con{(n + 1 : U32), Con{(n + 2 : U32), Con{(n + 3 : U32), Nil{}}}}, d, j), hjn))))), ME.subst(U32, x => {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, n, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), Equal.sym(U32, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), n, ME.subst(U32, x => {KMd.at_idx(x) == n : U32}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), pre_get(t, by, t0, ta, d, P.at_fh(), hft, hd32, hhd)), hidx)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot((n + 3 : U32), d), AD.slot(j, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((n + 3 : U32), d), AD.slot(j, d))), KMd.off.words(Nil{}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((n + 2 : U32), d), AD.slot(j, d))), KMd.off.words(Con{(n + 3 : U32), Nil{}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((n + 1 : U32), d), AD.slot(j, d))), KMd.off.words(Con{(n + 2 : U32), Con{(n + 3 : U32), Nil{}}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(n, d), AD.slot(j, d))), KMd.off.words(Con{(n + 1 : U32), Con{(n + 2 : U32), Con{(n + 3 : U32), Nil{}}}}, d, j), hjn))))))), ME.subst(P.H, x => {Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, j)) == Pair.snd(P.H, U32, P.rd(x, j)) : U32}, P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, pre(t, t0, ta, by), heta(pre(t, t0, ta, by)), {==}), pre_rd(t, by, t0, ta, d, j, hft, hd32, MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d))), KMd.off.words(KMd.hdr_words(), d, j), hjh)))

# and the head it leaves: the next node's link
def sn(+t: T.TNode, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +by: U32, +d: Nat, +n: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hne: {U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), 0) == False{} : Bool}, +hidx: {KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) == n : U32}, +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}, +hpn: {KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d) == True{} : Bool}) ->
  {Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))) : U32}:
  %Equal.sym(P.H & U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), P.node(pre(t, t0, ta, by), hdf(t, t0, ta, by), plf(t, t0, ta, by)), nf(t, t0, ta, by)) :
    {Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, _)), P.at_fh())) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))) : U32}
  %heta(pre(t, t0, ta, by)) :
    {Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, P.node(_, hdf(t, t0, ta, by), plf(t, t0, ta, by)))), P.at_fh())) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))) : U32}
  %SP.rd_get(KMd.words(Pair.fst(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by)))), KMd.vals(Pair.fst(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by)))), P.at_fh()) : {_ == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))) : U32}
  %Equal.sym(P.H, P.H{KM.MG{KMd.words(Pair.fst(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by))))}, KMd.vals(Pair.fst(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by))))}, Pair.fst(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by))), heta(Pair.fst(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by))))) : {Pair.snd(P.H, U32, P.rd(_, P.at_fh())) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))) : U32}
  ME.trans3(U32, Pair.snd(P.H, U32, P.rd(Pair.fst(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by))), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), ((((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32)) + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), (n + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))), SL.node_next(KMd.words(pre(t, t0, ta, by)), KMd.vals(pre(t, t0, ta, by)), d, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), hdf(t, t0, ta, by), plf(t, t0, ta, by), pre_full(t, t0, ta, by, d, hft), hd32, {==}, ME.subst(U32, x => {U32.is_eq(x, 0) == False{} : Bool}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), pre_get(t, by, t0, ta, d, P.at_fh(), hft, hd32, hhd)), hne), ME.subst(U32, x => {Nat.is_eq(AD.slot(x, d), AD.slot(P.at_fh(), d)) == False{} : Bool}, n, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), Equal.sym(U32, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), n, ME.subst(U32, x => {KMd.at_idx(x) == n : U32}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), pre_get(t, by, t0, ta, d, P.at_fh(), hft, hd32, hhd)), hidx)), Equal.trans(Bool, Nat.is_eq(AD.slot(n, d), AD.slot(P.at_fh(), d)), Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(n, d)), False{}, MN.is_eq_comm(AD.slot(n, d), AD.slot(P.at_fh(), d)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(n, d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(n, d))), KMd.off.words(Con{P.at_errs(), Con{P.at_tfh(), Con{P.at_tn(), Con{P.at_tcap(), Con{P.at_td(), Nil{}}}}}}, d, n), MB.eq_true_of_and_left(KMd.off.words(KMd.hdr_all(), d, n), KMd.ws.off(Con{(n + 1 : U32), Con{(n + 2 : U32), Con{(n + 3 : U32), Nil{}}}}, KMd.hdr_all(), d), hpn))))), SP.word_ne(hdf(t, t0, ta, by), ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), d, P.at_fh(), U32.is_eq((hdf(t, t0, ta, by) .&. 63 : U32), 5), {==}, ME.subst(U32, x => {Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(P.at_fh(), d)) == False{} : Bool}, n, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), Equal.sym(U32, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), n, ME.subst(U32, x => {KMd.at_idx(x) == n : U32}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), pre_get(t, by, t0, ta, d, P.at_fh(), hft, hd32, hhd)), hidx)), Equal.trans(Bool, Nat.is_eq(AD.slot((n + 2 : U32), d), AD.slot(P.at_fh(), d)), Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((n + 2 : U32), d)), False{}, MN.is_eq_comm(AD.slot((n + 2 : U32), d), AD.slot(P.at_fh(), d)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((n + 2 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((n + 2 : U32), d))), KMd.off.words(Con{P.at_errs(), Con{P.at_tfh(), Con{P.at_tn(), Con{P.at_tcap(), Con{P.at_td(), Nil{}}}}}}, d, (n + 2 : U32)), MB.eq_true_of_and_left(KMd.off.words(KMd.hdr_all(), d, (n + 2 : U32)), KMd.ws.off(Con{(n + 3 : U32), Nil{}}, KMd.hdr_all(), d), MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), d, (n + 1 : U32)), KMd.ws.off(Con{(n + 2 : U32), Con{(n + 3 : U32), Nil{}}}, KMd.hdr_all(), d), MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), d, n), KMd.ws.off(Con{(n + 1 : U32), Con{(n + 2 : U32), Con{(n + 3 : U32), Nil{}}}}, KMd.hdr_all(), d), hpn))))))), ME.subst(U32, x => {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(P.at_fh(), d)) == False{} : Bool}, n, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), Equal.sym(U32, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), n, ME.subst(U32, x => {KMd.at_idx(x) == n : U32}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), pre_get(t, by, t0, ta, d, P.at_fh(), hft, hd32, hhd)), hidx)), Equal.trans(Bool, Nat.is_eq(AD.slot((n + 3 : U32), d), AD.slot(P.at_fh(), d)), Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((n + 3 : U32), d)), False{}, MN.is_eq_comm(AD.slot((n + 3 : U32), d), AD.slot(P.at_fh(), d)), MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((n + 3 : U32), d)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((n + 3 : U32), d))), KMd.off.words(Con{P.at_errs(), Con{P.at_tfh(), Con{P.at_tn(), Con{P.at_tcap(), Con{P.at_td(), Nil{}}}}}}, d, (n + 3 : U32)), MB.eq_true_of_and_left(KMd.off.words(KMd.hdr_all(), d, (n + 3 : U32)), KMd.ws.off(Nil{}, KMd.hdr_all(), d), MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), d, (n + 2 : U32)), KMd.ws.off(Con{(n + 3 : U32), Nil{}}, KMd.hdr_all(), d), MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), d, (n + 1 : U32)), KMd.ws.off(Con{(n + 2 : U32), Con{(n + 3 : U32), Nil{}}}, KMd.hdr_all(), d), MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), d, n), KMd.ws.off(Con{(n + 1 : U32), Con{(n + 2 : U32), Con{(n + 3 : U32), Nil{}}}}, KMd.hdr_all(), d), hpn)))))))))), ME.subst(U32, x => {Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), ((((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32)) + 1 : U32))) == Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), (x + 1 : U32))) : U32}, ((Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())) - 1 : U32) << 2n : U32), n, ME.subst(U32, x => {KMd.at_idx(x) == n : U32}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), pre_get(t, by, t0, ta, d, P.at_fh(), hft, hd32, hhd)), hidx), {==}), pre_get(t, by, t0, ta, d, (n + 1 : U32), hft, hd32, MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((n + 1 : U32), d))), KMd.off.words(KMd.hdr_words(), d, (n + 1 : U32)), MB.eq_true_of_and_left(KMd.off.words(KMd.hdr_all(), d, (n + 1 : U32)), KMd.ws.off(Con{(n + 2 : U32), Con{(n + 3 : U32), Nil{}}}, KMd.hdr_all(), d), MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), d, n), KMd.ws.off(Con{(n + 1 : U32), Con{(n + 2 : U32), Con{(n + 3 : U32), Nil{}}}}, KMd.hdr_all(), d), hpn)))))

# and the words still full
def sfull(+t: T.TNode, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +by: U32, +d: Nat, +n: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hne: {U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), 0) == False{} : Bool}, +hidx: {KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) == n : U32}, +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}) ->
  {AD.full(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), d) == True{} : Bool}:
  %Equal.sym(P.H & U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), P.node(pre(t, t0, ta, by), hdf(t, t0, ta, by), plf(t, t0, ta, by)), nf(t, t0, ta, by)) :
    {AD.full(U32, KMd.words(Pair.fst(P.H, U32, _)), d) == True{} : Bool}
  %heta(pre(t, t0, ta, by)) :
    {AD.full(U32, KMd.words(Pair.fst(P.H, U32, P.node(_, hdf(t, t0, ta, by), plf(t, t0, ta, by)))), d) == True{} : Bool}
  node_full(KMd.words(pre(t, t0, ta, by)), KMd.vals(pre(t, t0, ta, by)), d, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), hdf(t, t0, ta, by), plf(t, t0, ta, by), pre_full(t, t0, ta, by, d, hft), {==}, ME.subst(U32, x => {U32.is_eq(x, 0) == False{} : Bool}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(pre(t, t0, ta, by)), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), pre_get(t, by, t0, ta, d, P.at_fh(), hft, hd32, hhd)), hne), LAT.mirror(U32, KMd.words(pre(t, t0, ta, by))))

# the free list's later links, read alike after the step: its frame at
# each later node's word 1, which is off the node taken and the header
def ctr(rn: List<&2, U32>, +t: T.TNode, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +by: U32, +d: Nat, +n: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hne: {U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), 0) == False{} : Bool}, +hidx: {KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) == n : U32}, +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}, +h: U32, +hfW: {AD.full(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), d) == True{} : Bool},
  +ha: {KMd.apart.n(n, rn, d) == True{} : Bool}, +hp: {KMd.past(rn, d) == True{} : Bool}, +hc: {KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, h) == True{} : Bool}) ->
  {KMd.chain(rn, AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, h) == True{} : Bool}:
  match rn:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(Bool.not(U32.is_eq(h, 0)), Bool.and(U32.is_eq(KMd.at_idx(h), m), KMd.chain(r, AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, (m + 1 : U32)))), MB.eq_true_of_and_left(Bool.not(U32.is_eq(h, 0)), Bool.and(U32.is_eq(KMd.at_idx(h), m), KMd.chain(r, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (m + 1 : U32)))), hc), MB.and_eq_true(U32.is_eq(KMd.at_idx(h), m), KMd.chain(r, AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, (m + 1 : U32))), MB.eq_true_of_and_left(U32.is_eq(KMd.at_idx(h), m), KMd.chain(r, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (m + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(h, 0)), Bool.and(U32.is_eq(KMd.at_idx(h), m), KMd.chain(r, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (m + 1 : U32)))), hc)), ME.subst(U32, x => {KMd.chain(r, AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, x) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (m + 1 : U32)), KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, (m + 1 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, (m + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (m + 1 : U32)), ME.trans3(U32, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, (m + 1 : U32)), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), (m + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (m + 1 : U32))), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (m + 1 : U32)), word_get(KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), d, (m + 1 : U32), hfW, hd32), sf(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd, (m + 1 : U32), MB.eq_true_of_and_left(KMd.off.words(KMd.nw(n), d, (m + 1 : U32)), KMd.ws.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, KMd.nw(n), d), MB.eq_true_of_and_right(KMd.off.words(KMd.nw(n), d, m), KMd.ws.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, KMd.nw(n), d), MB.eq_true_of_and_left(KMd.ws.off(KMd.nw(m), KMd.nw(n), d), KMd.apart.n(n, r, d), ha))), MB.eq_true_of_and_left(KMd.off.words(KMd.hdr_all(), d, (m + 1 : U32)), KMd.ws.off(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, KMd.hdr_all(), d), MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), d, m), KMd.ws.off(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, KMd.hdr_all(), d), MB.eq_true_of_and_left(KMd.ws.off(KMd.nw(m), KMd.hdr_all(), d), KMd.past(r, d), hp)))), Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (m + 1 : U32)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (m + 1 : U32))), word_get(LAT.fromT(U32, t0), d, (m + 1 : U32), hft, hd32)))), ctr(r, t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (m + 1 : U32)), hfW, MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(m), KMd.nw(n), d), KMd.apart.n(n, r, d), ha), MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(m), KMd.hdr_all(), d), KMd.past(r, d), hp), MB.eq_true_of_and_right(U32.is_eq(KMd.at_idx(h), m), KMd.chain(r, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (m + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(h, 0)), Bool.and(U32.is_eq(KMd.at_idx(h), m), KMd.chain(r, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (m + 1 : U32)))), hc))))))

# two lists of one length, their tails too
def npred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def npred_eq(+x: Nat, +y: Nat, e: {1n+x == 1n+y : Nat}) -> {x == y : Nat}:
  ME.subst(Nat, q => {x == npred(q) : Nat}, 1n+x, 1n+y, e, {==})

# the first node's eraser test, the node pass's split (S.sp.node_at)
def hd_era(ts: List<&2, T.TNode>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{+t, +rest}:
      S.sp.is_era(t)

# the node pass, by induction on the template's nodes, the free list's
# nodes beside them, each step's facts above; an eraser, matched on its
# test e as a parameter (no step lemma), makes no node, the static put
# in the map
def nodes_go(ts: List<&2, T.TNode>, +e: Bool, +he: {e == hd_era(ts) : Bool}, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +i: U32, +by: U32, ns: List<&2, U32>, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool},
  hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}, +hap: {KMd.apart(ns, d) == True{} : Bool}, +hpa: {KMd.past(ns, d) == True{} : Bool},
  +hj: {KMd.nodes.off(ns, d, j) == True{} : Bool}, +hjh: {KMd.off.words(KMd.hdr_all(), d, j) == True{} : Bool}, +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(ts, i, S.Sp{P.H{KM.MG{w}, a}, map}, by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +rt}:
      match e:
        case True{}:
          +hl2 = ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == List.length(&2, U32, ns) : Nat}, S.sp.is_era(t), True{}, Equal.sym(Bool, True{}, S.sp.is_era(t), he), hl)
          %he : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.sp.node_k(_, S.Sp{P.H{KM.MG{w}, a}, map}, t, i, by), by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}
          nodes_go(rt, hd_era(rt), {==}, w, a, Array.set(U32, map, i, P.era()), d, (i + 1 : U32), by, ns, j, hf, hd32, hc, hl2, hap, hpa, hj, hjh, hhd, mw, ma)
        case False{}:
          match ns:
            case Nil{}:
              Empty.absurd({Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{w}, a}, map}, by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}, MB.false_ne_true()(Equal.sym(Bool, True{}, False{}, ME.subst(Nat, q => {Nat.is_eq(q, 0n) == False{} : Bool}, SM.made.k(False{}, SM.made(rt)), 0n, ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == 0n : Nat}, S.sp.is_era(t), False{}, Equal.sym(Bool, False{}, S.sp.is_era(t), he), hl), {==}))))
            case Con{+n, +rn}:
              (+t0, +ew) = mw
              (+ta, +ea) = ma
              +hft = LAP.full_t(U32, w, t0, d, ew, hf)
              +hct = LAB.subst(Array<U32>, q => {KMd.chain(Con{n, rn}, AD.view(U32, q), d, KMd.word(AD.view(U32, q), d, P.at_fh())) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, ew), hc)
              +hne = ME.subst(U32, x => {U32.is_eq(x, 0) == False{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), word_get(LAT.fromT(U32, t0), d, P.at_fh(), hft, hd32), MB.eq_false_of_not_eq_true(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0), MB.eq_true_of_and_left(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct)))
              +hidx = ME.subst(U32, x => {KMd.at_idx(x) == n : U32}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), word_get(LAT.fromT(U32, t0), d, P.at_fh(), hft, hd32), MS.u32_eq_of_is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n, MB.eq_true_of_and_left(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct))))
              %ew : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{_}, a}, map}, by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
              %ea : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map}, by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, _}, j)) : U32}
              %he : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.sp.node_k(_, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, map}, t, i, by), by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)) : U32}
              %Equal.sym(S.Sp, S.sp.put(S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), map, i), S.Sp{Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)), Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, spput(S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), map, i)) :
                {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(rt, (i + 1 : U32), _, by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)) : U32}
              %heta(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))) :
                {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.Sp{_, Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)) : U32}
              ME.trans3(U32, Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.Sp{P.H{KM.MG{KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, by)), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)), nodes_go(rt, hd_era(rt), {==}, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), d, (i + 1 : U32), by, rn, j, sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), hd32, ME.subst(U32, x => {KMd.chain(rn, AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, x) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), ME.trans3(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), word_get(LAT.fromT(U32, t0), d, (n + 1 : U32), hft, hd32), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))), sn(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd, MB.eq_true_of_and_left(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(rn, d), hpa))), Equal.sym(U32, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), word_get(KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), d, P.at_fh(), sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), hd32))), ctr(rn, t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), MB.eq_true_of_and_left(KMd.apart.n(n, rn, d), KMd.apart(rn, d), hap), MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(rn, d), hpa), MB.eq_true_of_and_right(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct)))), npred_eq(SM.made(rt), List.length(&2, U32, rn), ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == List.length(&2, U32, Con{n, rn}) : Nat}, S.sp.is_era(t), False{}, Equal.sym(Bool, False{}, S.sp.is_era(t), he), hl)),
              MB.eq_true_of_and_right(KMd.apart.n(n, rn, d), KMd.apart(rn, d), hap), MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(rn, d), hpa), MB.eq_true_of_and_right(KMd.off.words(KMd.nw(n), d, j), KMd.nodes.off(rn, d, j), hj), hjh, hhd,
              LAT.mirror(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), LAT.mirror(V.Val, KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))))), Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), SP.rd_get(KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), j), sf(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd, j, MB.eq_true_of_and_left(KMd.off.words(KMd.nw(n), d, j), KMd.nodes.off(rn, d, j), hj), hjh)), Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), j)))

def Laws.nodes_keeps(w, a, map, d, ts, i, by, ns, j, hf, hd32, hc, hl, hap, hpa, hj, hjh, hhd):
  nodes_go(ts, hd_era(ts), {==}, w, a, map, d, i, by, ns, j, hf, hd32, hc, hl, hap, hpa, hj, hjh, hhd, LAT.mirror(U32, w), LAT.mirror(V.Val, a))

# The links pass. 32-bit addition associates (a link word, (base + port)
# + 1, is a node's word base + (port + 1)), proved over the modulus as a
# variable, never 2^32 computed (docs/Proving.md, big constants)
def mod_add_l(+x: Nat, +y: Nat, +m: Nat) -> {Nat.mod(Nat.add(Nat.mod(x, m), y), m) == Nat.mod(Nat.add(x, y), m) : Nat}:
  ME.trans3(Nat, Nat.mod(Nat.add(Nat.mod(x, m), y), m), Nat.mod(Nat.add(Nat.add(Nat.mod(x, m), y), Nat.mul(m, Nat.div(x, m))), m), Nat.mod(Nat.add(Nat.add(Nat.mod(x, m), Nat.mul(m, Nat.div(x, m))), y), m), Nat.mod(Nat.add(x, y), m), Equal.sym(Nat, Nat.mod(Nat.add(Nat.add(Nat.mod(x, m), y), Nat.mul(m, Nat.div(x, m))), m), Nat.mod(Nat.add(Nat.mod(x, m), y), m), MN.add_mul_mod_self_left(Nat.add(Nat.mod(x, m), y), m, Nat.div(x, m))), ME.subst(Nat, z => {Nat.mod(Nat.add(Nat.add(Nat.mod(x, m), y), Nat.mul(m, Nat.div(x, m))), m) == Nat.mod(z, m) : Nat}, Nat.add(Nat.add(Nat.mod(x, m), y), Nat.mul(m, Nat.div(x, m))), Nat.add(Nat.add(Nat.mod(x, m), Nat.mul(m, Nat.div(x, m))), y), ME.trans3(Nat, Nat.add(Nat.add(Nat.mod(x, m), y), Nat.mul(m, Nat.div(x, m))), Nat.add(Nat.mod(x, m), Nat.add(y, Nat.mul(m, Nat.div(x, m)))), Nat.add(Nat.mod(x, m), Nat.add(Nat.mul(m, Nat.div(x, m)), y)), Nat.add(Nat.add(Nat.mod(x, m), Nat.mul(m, Nat.div(x, m))), y), MN.add_assoc(Nat.mod(x, m), y, Nat.mul(m, Nat.div(x, m))), ME.subst(Nat, z => {Nat.add(Nat.mod(x, m), Nat.add(y, Nat.mul(m, Nat.div(x, m)))) == Nat.add(Nat.mod(x, m), z) : Nat}, Nat.add(y, Nat.mul(m, Nat.div(x, m))), Nat.add(Nat.mul(m, Nat.div(x, m)), y), MN.add_comm(y, Nat.mul(m, Nat.div(x, m))), {==}), Equal.sym(Nat, Nat.add(Nat.add(Nat.mod(x, m), Nat.mul(m, Nat.div(x, m))), y), Nat.add(Nat.mod(x, m), Nat.add(Nat.mul(m, Nat.div(x, m)), y)), MN.add_assoc(Nat.mod(x, m), Nat.mul(m, Nat.div(x, m)), y))), {==}), ME.subst(Nat, z => {Nat.mod(Nat.add(Nat.add(Nat.mod(x, m), Nat.mul(m, Nat.div(x, m))), y), m) == Nat.mod(Nat.add(z, y), m) : Nat}, Nat.add(Nat.mod(x, m), Nat.mul(m, Nat.div(x, m))), x, MN.mod_add_div(x, m), {==}))

def mod_add_r(+x: Nat, +y: Nat, +m: Nat) -> {Nat.mod(Nat.add(x, Nat.mod(y, m)), m) == Nat.mod(Nat.add(x, y), m) : Nat}:
  ME.trans3(Nat, Nat.mod(Nat.add(x, Nat.mod(y, m)), m), Nat.mod(Nat.add(Nat.mod(y, m), x), m), Nat.mod(Nat.add(y, x), m), Nat.mod(Nat.add(x, y), m), ME.subst(Nat, z => {Nat.mod(Nat.add(x, Nat.mod(y, m)), m) == Nat.mod(z, m) : Nat}, Nat.add(x, Nat.mod(y, m)), Nat.add(Nat.mod(y, m), x), MN.add_comm(x, Nat.mod(y, m)), {==}), mod_add_l(y, x, m), ME.subst(Nat, z => {Nat.mod(Nat.add(y, x), m) == Nat.mod(z, m) : Nat}, Nat.add(y, x), Nat.add(x, y), MN.add_comm(y, x), {==}))

def assoc_m(+m: Nat, +a: U32, +b: U32, +c: U32, +e: {Nat.pow(2n, 32n) == m : Nat}) ->
  {U32.to_nat(U32.add(U32.add(a, b), c)) == U32.to_nat(U32.add(a, U32.add(b, c))) : Nat}:
  Equal.trans(Nat, U32.to_nat(U32.add(U32.add(a, b), c)), Nat.mod(Nat.add(U32.to_nat(U32.add(a, b)), U32.to_nat(c)), m), U32.to_nat(U32.add(a, U32.add(b, c))), ME.subst(Nat, k => {U32.to_nat(U32.add(U32.add(a, b), c)) == Nat.mod(Nat.add(U32.to_nat(U32.add(a, b)), U32.to_nat(c)), k) : Nat}, Nat.pow(2n, 32n), m, e, MU.u32_add_wrap(U32.add(a, b), c)), Equal.trans(Nat, Nat.mod(Nat.add(U32.to_nat(U32.add(a, b)), U32.to_nat(c)), m), Nat.mod(Nat.add(Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), m), U32.to_nat(c)), m), U32.to_nat(U32.add(a, U32.add(b, c))), ME.subst(Nat, z => {Nat.mod(Nat.add(U32.to_nat(U32.add(a, b)), U32.to_nat(c)), m) == Nat.mod(Nat.add(z, U32.to_nat(c)), m) : Nat}, U32.to_nat(U32.add(a, b)), Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), m), ME.subst(Nat, k => {U32.to_nat(U32.add(a, b)) == Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), k) : Nat}, Nat.pow(2n, 32n), m, e, MU.u32_add_wrap(a, b)), {==}), Equal.trans(Nat, Nat.mod(Nat.add(Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), m), U32.to_nat(c)), m), Nat.mod(Nat.add(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c)), m), U32.to_nat(U32.add(a, U32.add(b, c))), mod_add_l(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c), m), Equal.trans(Nat, Nat.mod(Nat.add(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c)), m), Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), m), U32.to_nat(U32.add(a, U32.add(b, c))), ME.subst(Nat, z => {Nat.mod(Nat.add(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c)), m) == Nat.mod(z, m) : Nat}, Nat.add(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c)), Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), MN.add_assoc(U32.to_nat(a), U32.to_nat(b), U32.to_nat(c)), {==}), Equal.trans(Nat, Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), m), Nat.mod(Nat.add(U32.to_nat(a), Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), m)), m), U32.to_nat(U32.add(a, U32.add(b, c))), Equal.sym(Nat, Nat.mod(Nat.add(U32.to_nat(a), Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), m)), m), Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), m), mod_add_r(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c)), m)), Equal.trans(Nat, Nat.mod(Nat.add(U32.to_nat(a), Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), m)), m), Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(U32.add(b, c))), m), U32.to_nat(U32.add(a, U32.add(b, c))), ME.subst(Nat, z => {Nat.mod(Nat.add(U32.to_nat(a), Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), m)), m) == Nat.mod(Nat.add(U32.to_nat(a), z), m) : Nat}, Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), m), U32.to_nat(U32.add(b, c)), Equal.sym(Nat, U32.to_nat(U32.add(b, c)), Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), m), ME.subst(Nat, k => {U32.to_nat(U32.add(b, c)) == Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), k) : Nat}, Nat.pow(2n, 32n), m, e, MU.u32_add_wrap(b, c))), {==}), Equal.sym(Nat, U32.to_nat(U32.add(a, U32.add(b, c))), Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(U32.add(b, c))), m), ME.subst(Nat, k => {U32.to_nat(U32.add(a, U32.add(b, c))) == Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(U32.add(b, c))), k) : Nat}, Nat.pow(2n, 32n), m, e, MU.u32_add_wrap(a, U32.add(b, c))))))))))

def u32_assoc(+a: U32, +b: U32, +c: U32) -> {U32.add(U32.add(a, b), c) == U32.add(a, U32.add(b, c)) : U32}:
  MU.u32_to_nat_inj(U32.add(U32.add(a, b), c), U32.add(a, U32.add(b, c)), assoc_m(Nat.pow(2n, 32n), a, b, c, {==}))

def or_cases(+a: Bool, +b: Bool, +c: Bool, h: {Bool.or(a, b) == True{} : Bool},
    fa: {a == True{} : Bool} -> {c == True{} : Bool}, fb: {b == True{} : Bool} -> {c == True{} : Bool}) -> {c == True{} : Bool}:
  match a:
    case True{}:
      fa({==})
    case False{}:
      fb(h)

# a fresh node's words, off word j, read from the nodes' frame premise
def knodes_at(ns: List<&2, U32>, +d: Nat, +j: U32, +m: U32, +h: {KMd.nodes.off(ns, d, j) == True{} : Bool}, hm: {KMd.has(ns, m) == True{} : Bool}) ->
  {KMd.off.words(KMd.nw(m), d, j) == True{} : Bool}:
  match ns:
    case Nil{}:
      Empty.absurd({KMd.off.words(KMd.nw(m), d, j) == True{} : Bool}, MB.false_ne_true()(hm))
    case Con{+c, +r}:
      or_cases(U32.is_eq(c, m), KMd.has(r, m), KMd.off.words(KMd.nw(m), d, j), hm,
        q => ME.subst(U32, k => {KMd.off.words(KMd.nw(k), d, j) == True{} : Bool}, c, m, MS.u32_eq_of_is_eq(c, m, q), MB.eq_true_of_and_left(KMd.off.words(KMd.nw(c), d, j), KMd.nodes.off(r, d, j), h)),
        hh => knodes_at(r, d, j, m, MB.eq_true_of_and_right(KMd.off.words(KMd.nw(c), d, j), KMd.nodes.off(r, d, j), h), hh))

# a link word a link writes, (base + port) + 1, a fresh node's word 1, 2
# or 3, off word j
def lwoff(+ns: List<&2, U32>, +m: U32, +p: U32, +d: Nat, +j: U32, +hm: {KMd.has(ns, m) == True{} : Bool}, hp: {SM.port3(p) == True{} : Bool},
    +hj: {KMd.nodes.off(ns, d, j) == True{} : Bool}) -> {Nat.is_eq(AD.slot(((m + p : U32) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}:
  +hnw = knodes_at(ns, d, j, m, hj, hm)
  MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(((m + p : U32) + 1 : U32), d), AD.slot(j, d)),
    or_cases(U32.is_eq(p, 0), Bool.or(U32.is_eq(p, 1), U32.is_eq(p, 2)), Bool.not(Nat.is_eq(AD.slot(((m + p : U32) + 1 : U32), d), AD.slot(j, d))), hp, q0 => ME.subst(U32, x => {Bool.not(Nat.is_eq(AD.slot(((m + x : U32) + 1 : U32), d), AD.slot(j, d))) == True{} : Bool}, 0, p, Equal.sym(U32, p, 0, MS.u32_eq_of_is_eq(p, 0, q0)), ME.subst(U32, x => {Bool.not(Nat.is_eq(AD.slot(x, d), AD.slot(j, d))) == True{} : Bool}, (m + 1 : U32), ((m + 0 : U32) + 1 : U32), Equal.sym(U32, ((m + 0 : U32) + 1 : U32), (m + 1 : U32), u32_assoc(m, 0, 1)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), KMd.off.words(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))), KMd.off.words(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, j), hnw)))),
      q12 => or_cases(U32.is_eq(p, 1), U32.is_eq(p, 2), Bool.not(Nat.is_eq(AD.slot(((m + p : U32) + 1 : U32), d), AD.slot(j, d))), q12, q1 => ME.subst(U32, x => {Bool.not(Nat.is_eq(AD.slot(((m + x : U32) + 1 : U32), d), AD.slot(j, d))) == True{} : Bool}, 1, p, Equal.sym(U32, p, 1, MS.u32_eq_of_is_eq(p, 1, q1)), ME.subst(U32, x => {Bool.not(Nat.is_eq(AD.slot(x, d), AD.slot(j, d))) == True{} : Bool}, (m + 2 : U32), ((m + 1 : U32) + 1 : U32), Equal.sym(U32, ((m + 1 : U32) + 1 : U32), (m + 2 : U32), u32_assoc(m, 1, 1)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), KMd.off.words(Con{(m + 3 : U32), Nil{}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), KMd.off.words(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))), KMd.off.words(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, j), hnw))))), q2 => ME.subst(U32, x => {Bool.not(Nat.is_eq(AD.slot(((m + x : U32) + 1 : U32), d), AD.slot(j, d))) == True{} : Bool}, 2, p, Equal.sym(U32, p, 2, MS.u32_eq_of_is_eq(p, 2, q2)), ME.subst(U32, x => {Bool.not(Nat.is_eq(AD.slot(x, d), AD.slot(j, d))) == True{} : Bool}, (m + 3 : U32), ((m + 2 : U32) + 1 : U32), Equal.sym(U32, ((m + 2 : U32) + 1 : U32), (m + 3 : U32), u32_assoc(m, 2, 1)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d))), KMd.off.words(Nil{}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))), KMd.off.words(Con{(m + 3 : U32), Nil{}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))), KMd.off.words(Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}, d, j), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))), KMd.off.words(Con{(m + 1 : U32), Con{(m + 2 : U32), Con{(m + 3 : U32), Nil{}}}}, d, j), hnw)))))))))

# link_xx keeps the words full (glam/PROOF.bend's lx_full, over the
# splice's model of the heap)
def lxf(+sy: Bool, +sz: Bool, +t: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +y: U32, +z: U32,
    +hft: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}) -> {AD.full(U32, KMd.words(P.link.to(sz, P.link.to(sy, P.H{KM.MG{LAT.fromT(U32, t)}, a}, y, z), z, y)), d) == True{} : Bool}:
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

# a word off port r's link word, if r has one (glam/PROOF.bend's
# off_port_of.k)
def opk(+st: Bool, +d: Nat, +r: U32, +j: U32, +h: {Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}) ->
    {KMd.off.lw(KMd.lw.k(st, r), d, j) == True{} : Bool}:
  match st:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(j, d)), False{}, h) : {Bool.not(_) == True{} : Bool}
      {==}

# a fresh node's port: word j off its link word
def end_fresh(+ns: List<&2, U32>, +m: U32, +p: U32, +d: Nat, +j: U32, +q: {Bool.and(KMd.has(ns, m), SM.port3(p)) == True{} : Bool},
    +hj: {KMd.nodes.off(ns, d, j) == True{} : Bool}) -> {KMd.off.port(d, (m + p : U32), j) == True{} : Bool}:
  opk(P.is_static((m + p : U32)), d, (m + p : U32), j, lwoff(ns, m, p, d, j, MB.eq_true_of_and_left(KMd.has(ns, m), SM.port3(p), q), MB.eq_true_of_and_right(KMd.has(ns, m), SM.port3(p), q), hj))

# an end a link names, static or a fresh node's port: word j off its
# link word, if it has one
def end_off(+ns: List<&2, U32>, +m: U32, +p: U32, +d: Nat, +j: U32, h: {Bool.or(P.is_static((m + p : U32)), Bool.and(KMd.has(ns, m), SM.port3(p))) == True{} : Bool},
    +hj: {KMd.nodes.off(ns, d, j) == True{} : Bool}) -> {KMd.off.port(d, (m + p : U32), j) == True{} : Bool}:
  or_cases(P.is_static((m + p : U32)), Bool.and(KMd.has(ns, m), SM.port3(p)), KMd.off.port(d, (m + p : U32), j), h,
    q => ME.subst(Bool, s => {KMd.off.lw(KMd.lw.k(s, (m + p : U32)), d, j) == True{} : Bool}, True{}, P.is_static((m + p : U32)), Equal.sym(Bool, P.is_static((m + p : U32)), True{}, q), {==}),
    q => end_fresh(ns, m, p, d, j, q, hj))

# the links pass, by induction on the links: each writes at most its two
# ends' link words (link_xx; spike's link_keeps), a static's none, the
# others words of fresh nodes
def links_go(ls: List<&2, T.TLink>, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +ns: List<&2, U32>, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hfm: {AD.full(U32, map, dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
  he: {SM.ends.ok(ls, AD.view(U32, map), dm, ns) == True{} : Bool}, +hj: {KMd.nodes.off(ns, d, j) == True{} : Bool},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{w}, a}, map})), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, +rest}:
      match l:
        case T.TL{e1, e2}:
          match e1:
            case T.TE{+n1, +p1}:
              match e2:
                case T.TE{+n2, +p2}:
                  (+t0, +ew) = mw
                  (+ta, +eav) = ma
                  (+tm, +em) = mm
                  +hft = LAP.full_t(U32, w, t0, d, ew, hf)
                  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
                  +het = LAB.subst(Array<U32>, q => {SM.ends.ok(Con{T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, rest}, AD.view(U32, q), dm, ns) == True{} : Bool}, map, LAT.fromT(U32, tm), Equal.sym(Array<U32>, LAT.fromT(U32, tm), map, em), he)
                  %ew : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(Con{T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, rest}, S.Sp{P.H{KM.MG{_}, a}, map})), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
                  %eav : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(Con{T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, rest}, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map})), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, _}, j)) : U32}
                  %em : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(Con{T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, rest}, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, _})), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)) : U32}
                  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, tm), n1), (LAT.fromT(U32, tm), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1))), LA.get_pair(U32, LAT.fromT(U32, tm), n1)) :
                    {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(rest, S.sp.link1(S.sp.ref(_, p1), T.TE{n2, p2}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}))), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)) : U32}
                  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, tm), n2), (LAT.fromT(U32, tm), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2))), LA.get_pair(U32, LAT.fromT(U32, tm), n2)) :
                    {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(rest, S.sp.link2(S.sp.ref(_, p2), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}))), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)) : U32}
                  %heta(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32))) :
                    {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(rest, S.Sp{_, LAT.fromT(U32, tm)})), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)) : U32}
                  ME.trans3(U32, Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(rest, S.Sp{P.H{KM.MG{KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, LAT.fromT(U32, tm)})), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, j)), Pair.snd(P.H, U32, P.rd(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)), links_go(rest, KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32))), KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32))), LAT.fromT(U32, tm), d, dm, ns, j, lxf(P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32)), P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)), t0, LAT.fromT(V.Val, ta), d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32), hft), hd32, hfmt, hdm, MB.eq_true_of_and_right(SM.link.ok(T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, AD.view(U32, LAT.fromT(U32, tm)), dm, ns), SM.ends.ok(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, ns), het), hj, LAT.mirror(U32, KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))), LAT.mirror(V.Val, KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))), LAT.mirror(U32, LAT.fromT(U32, tm))), ME.subst(P.H, q => {Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, j)) == Pair.snd(P.H, U32, P.rd(q, j)) : U32}, P.H{KM.MG{KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)), heta(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32))), {==}), SL.link_keeps(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32), j, hft, hd32, end_off(ns, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)), p1, d, j, ME.subst(U32, x => {Bool.or(P.is_static((x + p1 : U32)), Bool.and(KMd.has(ns, x), SM.port3(p1))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n1), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)), word_get(LAT.fromT(U32, tm), dm, n1, hfmt, hdm), MB.eq_true_of_and_left(SM.end.ok(T.TE{n1, p1}, AD.view(U32, LAT.fromT(U32, tm)), dm, ns), SM.end.ok(T.TE{n2, p2}, AD.view(U32, LAT.fromT(U32, tm)), dm, ns), MB.eq_true_of_and_left(SM.link.ok(T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, AD.view(U32, LAT.fromT(U32, tm)), dm, ns), SM.ends.ok(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, ns), het))), hj), end_off(ns, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)), p2, d, j, ME.subst(U32, x => {Bool.or(P.is_static((x + p2 : U32)), Bool.and(KMd.has(ns, x), SM.port3(p2))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n2), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)), word_get(LAT.fromT(U32, tm), dm, n2, hfmt, hdm), MB.eq_true_of_and_right(SM.end.ok(T.TE{n1, p1}, AD.view(U32, LAT.fromT(U32, tm)), dm, ns), SM.end.ok(T.TE{n2, p2}, AD.view(U32, LAT.fromT(U32, tm)), dm, ns), MB.eq_true_of_and_left(SM.link.ok(T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, AD.view(U32, LAT.fromT(U32, tm)), dm, ns), SM.ends.ok(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, ns), het))), hj)))

def Laws.links_keeps(w, a, map, d, dm, ls, ns, j, hf, hd32, hfm, hdm, he, hj):
  links_go(ls, w, a, map, d, dm, ns, j, hf, hd32, hfm, hdm, he, hj, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))

# The node pass's map. A map word after a set: the value at the set's
# slot, the word before elsewhere
def some_inj(+a: U32, +b: U32, e: {Some{a} == Some{b} : Maybe<&2, U32>}) -> {a == b : U32}:
  ME.subst(Maybe<&2, U32>, q => {a == Maybe.default(&2, U32, q, a) : U32}, Some{a}, Some{b}, e, {==})

def get_slot_eq(+t0: LAT.Tree<U32>, +d: Nat, +i: U32, +j: U32, +v: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    hij: {Nat.is_eq(AD.slot(i, d), AD.slot(j, d)) == True{} : Bool}) -> {Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), i, v), j)) == v : U32}:
  some_inj(Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), i, v), j)), v, Equal.trans(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), i, v), j))}, List.get(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), i, v)), AD.slot(j, d)), Maybe.map(&2, U32, U32, z => v, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), i))}), LA.get_view(U32, Array.set(U32, LAT.fromT(U32, t0), i, v), d, j, LA.set_full(U32, LAT.fromT(U32, t0), d, i, v, hft), hd32), Equal.trans(Maybe<&2, U32>, List.get(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), i, v)), AD.slot(j, d)), List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(i, d), v), AD.slot(j, d)), Maybe.map(&2, U32, U32, z => v, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), i))}), ME.subst(List<&2, U32>, xs => {List.get(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), i, v)), AD.slot(j, d)) == List.get(&2, U32, xs, AD.slot(j, d)) : Maybe<&2, U32>}, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), i, v)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(i, d), v), LA.set_view(U32, LAT.fromT(U32, t0), d, i, v, hft, hd32), {==}), Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(i, d), v), AD.slot(j, d)), List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(i, d), v), AD.slot(i, d)), Maybe.map(&2, U32, U32, z => v, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), i))}), ME.subst(Nat, k => {List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(i, d), v), AD.slot(j, d)) == List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(i, d), v), k) : Maybe<&2, U32>}, AD.slot(j, d), AD.slot(i, d), Equal.sym(Nat, AD.slot(i, d), AD.slot(j, d), MN.eq_of_is_eq(AD.slot(i, d), AD.slot(j, d), hij)), {==}), Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(i, d), v), AD.slot(i, d)), Maybe.map(&2, U32, U32, z => v, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(i, d))), Maybe.map(&2, U32, U32, z => v, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), i))}), ML.get_set_self(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(i, d), v), ME.subst(Maybe<&2, U32>, mm => {Maybe.map(&2, U32, U32, z => v, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(i, d))) == Maybe.map(&2, U32, U32, z => v, mm) : Maybe<&2, U32>}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(i, d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), i))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), i))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(i, d)), LA.get_view(U32, LAT.fromT(U32, t0), d, i, hft, hd32)), {==}))))))

def wset.k(+b: Bool, +t0: LAT.Tree<U32>, +dm: Nat, +i: U32, +ix: U32, +v: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
    +hb: {Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)) == b : Bool}) -> {KMd.word(AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), i, v)), dm, ix) == SM.pick(b, v, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), dm, ix)) : U32}:
  match b:
    case True{}:
      Equal.trans(U32, KMd.word(AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), i, v)), dm, ix), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), i, v), ix)), v, word_get(Array.set(U32, LAT.fromT(U32, t0), i, v), dm, ix, LA.set_full(U32, LAT.fromT(U32, t0), dm, i, v, hft), hdm), get_slot_eq(t0, dm, i, ix, v, hft, hdm, hb))
    case False{}:
      ME.trans3(U32, KMd.word(AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), i, v)), dm, ix), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), i, v), ix)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ix)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), dm, ix), word_get(Array.set(U32, LAT.fromT(U32, t0), i, v), dm, ix, LA.set_full(U32, LAT.fromT(U32, t0), dm, i, v, hft), hdm), LA.get_set_other(U32, LAT.fromT(U32, t0), dm, i, ix, v, hft, hdm, hb), Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), dm, ix), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ix)), word_get(LAT.fromT(U32, t0), dm, ix, hft, hdm)))

def wset(+t0: LAT.Tree<U32>, +dm: Nat, +i: U32, +ix: U32, +v: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}) ->
    {KMd.word(AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), i, v)), dm, ix) == SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), v, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), dm, ix)) : U32}:
  wset.k(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), t0, dm, i, ix, v, hft, hdm, {==})

# the node a step pops is the chain's head: P.node's result (spike's
# node_index) after the step's value and error writes, which leave the
# head word
def node_val(+t: T.TNode, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +by: U32, +d: Nat, +n: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hne: {U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), 0) == False{} : Bool}, +hidx: {KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) == n : U32}, +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}) -> {Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)) == n : U32}:
  %Equal.sym(P.H & U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), P.node(pre(t, t0, ta, by), hdf(t, t0, ta, by), plf(t, t0, ta, by)), nf(t, t0, ta, by)) : {Pair.snd(P.H, U32, _) == n : U32}
  %heta(pre(t, t0, ta, by)) : {Pair.snd(P.H, U32, P.node(_, hdf(t, t0, ta, by), plf(t, t0, ta, by))) == n : U32}
  Equal.trans(U32, Pair.snd(P.H, U32, P.node(P.H{KM.MG{KMd.words(pre(t, t0, ta, by))}, KMd.vals(pre(t, t0, ta, by))}, hdf(t, t0, ta, by), plf(t, t0, ta, by))), ((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())) - 1 : U32) << 2n : U32), n, SL.node_index(KMd.words(pre(t, t0, ta, by)), KMd.vals(pre(t, t0, ta, by)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), hdf(t, t0, ta, by), plf(t, t0, ta, by), pre_get(t, by, t0, ta, d, P.at_fh(), hft, hd32, hhd), hne), hidx)

# the node pass's map, by induction as the node pass's frame: an eraser
# sets its slot to the static, a node to the chain's head
def maps_go(ts: List<&2, T.TNode>, +e: Bool, +he: {e == hd_era(ts) : Bool}, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +i: U32, +by: U32, ns: List<&2, U32>, +ix: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hfm: {AD.full(U32, map, dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
  hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}, hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat},
  +hap: {KMd.apart(ns, d) == True{} : Bool}, +hpa: {KMd.past(ns, d) == True{} : Bool}, +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {KMd.word(AD.view(U32, SM.map(S.sp.nodes(ts, i, S.Sp{P.H{KM.MG{w}, a}, map}, by))), dm, ix) == SM.ent(ts, ns, i, dm, ix, KMd.word(AD.view(U32, map), dm, ix)) : U32}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +rt}:
      match e:
        case True{}:
          (+tm, +em) = mm
          +hl2 = ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == List.length(&2, U32, ns) : Nat}, S.sp.is_era(t), True{}, Equal.sym(Bool, True{}, S.sp.is_era(t), he), hl)
          +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
          %em : {KMd.word(AD.view(U32, SM.map(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{w}, a}, _}, by))), dm, ix) == SM.ent(Con{t, rt}, ns, i, dm, ix, KMd.word(AD.view(U32, _), dm, ix)) : U32}
          %he : {KMd.word(AD.view(U32, SM.map(S.sp.nodes(rt, (i + 1 : U32), S.sp.node_k(_, S.Sp{P.H{KM.MG{w}, a}, LAT.fromT(U32, tm)}, t, i, by), by))), dm, ix) == SM.ent(rt, SM.ent.ns(_, ns), (i + 1 : U32), dm, ix, SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), SM.ent.w(_, ns), KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, ix))) : U32}
          ME.subst(U32, z => {KMd.word(AD.view(U32, SM.map(S.sp.nodes(rt, (i + 1 : U32), S.Sp{P.H{KM.MG{w}, a}, Array.set(U32, LAT.fromT(U32, tm), i, P.era())}, by))), dm, ix) == SM.ent(rt, ns, (i + 1 : U32), dm, ix, z) : U32}, KMd.word(AD.view(U32, Array.set(U32, LAT.fromT(U32, tm), i, P.era())), dm, ix), SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), P.era(), KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, ix)), wset(tm, dm, i, ix, P.era(), hfmt, hdm), maps_go(rt, hd_era(rt), {==}, w, a, Array.set(U32, LAT.fromT(U32, tm), i, P.era()), d, dm, (i + 1 : U32), by, ns, ix, hf, hd32, LA.set_full(U32, LAT.fromT(U32, tm), dm, i, P.era(), hfmt), hdm, hc, hl2, hap, hpa, hhd, mw, ma, LAT.mirror(U32, Array.set(U32, LAT.fromT(U32, tm), i, P.era()))))
        case False{}:
          match ns:
            case Nil{}:
              Empty.absurd({KMd.word(AD.view(U32, SM.map(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{w}, a}, map}, by))), dm, ix) == SM.ent(Con{t, rt}, Nil{}, i, dm, ix, KMd.word(AD.view(U32, map), dm, ix)) : U32}, MB.false_ne_true()(Equal.sym(Bool, True{}, False{}, ME.subst(Nat, q => {Nat.is_eq(q, 0n) == False{} : Bool}, SM.made.k(False{}, SM.made(rt)), 0n, ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == 0n : Nat}, S.sp.is_era(t), False{}, Equal.sym(Bool, False{}, S.sp.is_era(t), he), hl), {==}))))
            case Con{+n, +rn}:
              (+t0, +ew) = mw
              (+ta, +ea) = ma
              (+tm, +em) = mm
              +hft = LAP.full_t(U32, w, t0, d, ew, hf)
              +hct = LAB.subst(Array<U32>, q => {KMd.chain(Con{n, rn}, AD.view(U32, q), d, KMd.word(AD.view(U32, q), d, P.at_fh())) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, ew), hc)
              +hne = ME.subst(U32, x => {U32.is_eq(x, 0) == False{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), word_get(LAT.fromT(U32, t0), d, P.at_fh(), hft, hd32), MB.eq_false_of_not_eq_true(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0), MB.eq_true_of_and_left(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct)))
              +hidx = ME.subst(U32, x => {KMd.at_idx(x) == n : U32}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), word_get(LAT.fromT(U32, t0), d, P.at_fh(), hft, hd32), MS.u32_eq_of_is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n, MB.eq_true_of_and_left(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct))))
              +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
              %ew : {KMd.word(AD.view(U32, SM.map(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{_}, a}, map}, by))), dm, ix) == SM.ent(Con{t, rt}, Con{n, rn}, i, dm, ix, KMd.word(AD.view(U32, map), dm, ix)) : U32}
              %ea : {KMd.word(AD.view(U32, SM.map(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map}, by))), dm, ix) == SM.ent(Con{t, rt}, Con{n, rn}, i, dm, ix, KMd.word(AD.view(U32, map), dm, ix)) : U32}
              %em : {KMd.word(AD.view(U32, SM.map(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, _}, by))), dm, ix) == SM.ent(Con{t, rt}, Con{n, rn}, i, dm, ix, KMd.word(AD.view(U32, _), dm, ix)) : U32}
              %he : {KMd.word(AD.view(U32, SM.map(S.sp.nodes(rt, (i + 1 : U32), S.sp.node_k(_, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, t, i, by), by))), dm, ix) == SM.ent(rt, SM.ent.ns(_, Con{n, rn}), (i + 1 : U32), dm, ix, SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), SM.ent.w(_, Con{n, rn}), KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, ix))) : U32}
              %Equal.sym(S.Sp, S.sp.put(S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), LAT.fromT(U32, tm), i), S.Sp{Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)), Array.set(U32, LAT.fromT(U32, tm), i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, spput(S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), LAT.fromT(U32, tm), i)) :
                {KMd.word(AD.view(U32, SM.map(S.sp.nodes(rt, (i + 1 : U32), _, by))), dm, ix) == SM.ent(rt, rn, (i + 1 : U32), dm, ix, SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), n, KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, ix))) : U32}
              %Equal.sym(U32, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)), n, node_val(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd)) :
                {KMd.word(AD.view(U32, SM.map(S.sp.nodes(rt, (i + 1 : U32), S.Sp{Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)), Array.set(U32, LAT.fromT(U32, tm), i, _)}, by))), dm, ix) == SM.ent(rt, rn, (i + 1 : U32), dm, ix, SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), n, KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, ix))) : U32}
              %heta(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))) :
                {KMd.word(AD.view(U32, SM.map(S.sp.nodes(rt, (i + 1 : U32), S.Sp{_, Array.set(U32, LAT.fromT(U32, tm), i, n)}, by))), dm, ix) == SM.ent(rt, rn, (i + 1 : U32), dm, ix, SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), n, KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, ix))) : U32}
              ME.subst(U32, z => {KMd.word(AD.view(U32, SM.map(S.sp.nodes(rt, (i + 1 : U32), S.Sp{P.H{KM.MG{KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, Array.set(U32, LAT.fromT(U32, tm), i, n)}, by))), dm, ix) == SM.ent(rt, rn, (i + 1 : U32), dm, ix, z) : U32}, KMd.word(AD.view(U32, Array.set(U32, LAT.fromT(U32, tm), i, n)), dm, ix), SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), n, KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, ix)), wset(tm, dm, i, ix, n, hfmt, hdm), maps_go(rt, hd_era(rt), {==}, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), Array.set(U32, LAT.fromT(U32, tm), i, n), d, dm, (i + 1 : U32), by, rn, ix, sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), hd32, LA.set_full(U32, LAT.fromT(U32, tm), dm, i, n, hfmt), hdm, ME.subst(U32, x => {KMd.chain(rn, AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, x) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), ME.trans3(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), word_get(LAT.fromT(U32, t0), d, (n + 1 : U32), hft, hd32), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))), sn(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd, MB.eq_true_of_and_left(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(rn, d), hpa))), Equal.sym(U32, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), word_get(KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), d, P.at_fh(), sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), hd32))), ctr(rn, t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), MB.eq_true_of_and_left(KMd.apart.n(n, rn, d), KMd.apart(rn, d), hap), MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(rn, d), hpa), MB.eq_true_of_and_right(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct)))), npred_eq(SM.made(rt), List.length(&2, U32, rn), ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == List.length(&2, U32, Con{n, rn}) : Nat}, S.sp.is_era(t), False{}, Equal.sym(Bool, False{}, S.sp.is_era(t), he), hl)),
                MB.eq_true_of_and_right(KMd.apart.n(n, rn, d), KMd.apart(rn, d), hap), MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(rn, d), hpa), hhd,
                LAT.mirror(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), LAT.mirror(V.Val, KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), LAT.mirror(U32, Array.set(U32, LAT.fromT(U32, tm), i, n))))

def Laws.nodes_maps(w, a, map, d, dm, ts, i, by, ns, ix, hf, hd32, hfm, hdm, hc, hl, hap, hpa, hhd):
  maps_go(ts, hd_era(ts), {==}, w, a, map, d, dm, i, by, ns, ix, hf, hd32, hfm, hdm, hc, hl, hap, hpa, hhd, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))

# The copy's two passes. The node pass keeps the words full
def full_go(ts: List<&2, T.TNode>, +e: Bool, +he: {e == hd_era(ts) : Bool}, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +i: U32, +by: U32, ns: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}, hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat},
  +hap: {KMd.apart(ns, d) == True{} : Bool}, +hpa: {KMd.past(ns, d) == True{} : Bool}, +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {AD.full(U32, KMd.words(SM.heap(S.sp.nodes(ts, i, S.Sp{P.H{KM.MG{w}, a}, map}, by))), d) == True{} : Bool}:
  match ts:
    case Nil{}:
      hf
    case Con{+t, +rt}:
      match e:
        case True{}:
          +hl2 = ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == List.length(&2, U32, ns) : Nat}, S.sp.is_era(t), True{}, Equal.sym(Bool, True{}, S.sp.is_era(t), he), hl)
          %he : {AD.full(U32, KMd.words(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.sp.node_k(_, S.Sp{P.H{KM.MG{w}, a}, map}, t, i, by), by))), d) == True{} : Bool}
          full_go(rt, hd_era(rt), {==}, w, a, Array.set(U32, map, i, P.era()), d, (i + 1 : U32), by, ns, hf, hd32, hc, hl2, hap, hpa, hhd, mw, ma)
        case False{}:
          match ns:
            case Nil{}:
              Empty.absurd({AD.full(U32, KMd.words(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{w}, a}, map}, by))), d) == True{} : Bool}, MB.false_ne_true()(Equal.sym(Bool, True{}, False{}, ME.subst(Nat, q => {Nat.is_eq(q, 0n) == False{} : Bool}, SM.made.k(False{}, SM.made(rt)), 0n, ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == 0n : Nat}, S.sp.is_era(t), False{}, Equal.sym(Bool, False{}, S.sp.is_era(t), he), hl), {==}))))
            case Con{+n, +rn}:
              (+t0, +ew) = mw
              (+ta, +ea) = ma
              +hft = LAP.full_t(U32, w, t0, d, ew, hf)
              +hct = LAB.subst(Array<U32>, q => {KMd.chain(Con{n, rn}, AD.view(U32, q), d, KMd.word(AD.view(U32, q), d, P.at_fh())) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, ew), hc)
              +hne = ME.subst(U32, x => {U32.is_eq(x, 0) == False{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), word_get(LAT.fromT(U32, t0), d, P.at_fh(), hft, hd32), MB.eq_false_of_not_eq_true(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0), MB.eq_true_of_and_left(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct)))
              +hidx = ME.subst(U32, x => {KMd.at_idx(x) == n : U32}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), word_get(LAT.fromT(U32, t0), d, P.at_fh(), hft, hd32), MS.u32_eq_of_is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n, MB.eq_true_of_and_left(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct))))
              %ew : {AD.full(U32, KMd.words(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{_}, a}, map}, by))), d) == True{} : Bool}
              %ea : {AD.full(U32, KMd.words(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map}, by))), d) == True{} : Bool}
              %he : {AD.full(U32, KMd.words(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.sp.node_k(_, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, map}, t, i, by), by))), d) == True{} : Bool}
              %Equal.sym(S.Sp, S.sp.put(S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), map, i), S.Sp{Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)), Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, spput(S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), map, i)) :
                {AD.full(U32, KMd.words(SM.heap(S.sp.nodes(rt, (i + 1 : U32), _, by))), d) == True{} : Bool}
              %heta(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))) :
                {AD.full(U32, KMd.words(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.Sp{_, Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, by))), d) == True{} : Bool}
              full_go(rt, hd_era(rt), {==}, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), d, (i + 1 : U32), by, rn, sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), hd32, ME.subst(U32, x => {KMd.chain(rn, AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, x) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), ME.trans3(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), word_get(LAT.fromT(U32, t0), d, (n + 1 : U32), hft, hd32), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))), sn(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd, MB.eq_true_of_and_left(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(rn, d), hpa))), Equal.sym(U32, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), word_get(KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), d, P.at_fh(), sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), hd32))), ctr(rn, t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), MB.eq_true_of_and_left(KMd.apart.n(n, rn, d), KMd.apart(rn, d), hap), MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(rn, d), hpa), MB.eq_true_of_and_right(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct)))), npred_eq(SM.made(rt), List.length(&2, U32, rn), ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == List.length(&2, U32, Con{n, rn}) : Nat}, S.sp.is_era(t), False{}, Equal.sym(Bool, False{}, S.sp.is_era(t), he), hl)),
                MB.eq_true_of_and_right(KMd.apart.n(n, rn, d), KMd.apart(rn, d), hap), MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(rn, d), hpa), hhd,
                LAT.mirror(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), LAT.mirror(V.Val, KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))))

# and the map full
def mfull_go(ts: List<&2, T.TNode>, +e: Bool, +he: {e == hd_era(ts) : Bool}, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +dm: Nat, +i: U32, +by: U32,
  hfm: {AD.full(U32, map, dm) == True{} : Bool}, mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {AD.full(U32, SM.map(S.sp.nodes(ts, i, S.Sp{P.H{KM.MG{w}, a}, map}, by)), dm) == True{} : Bool}:
  match ts:
    case Nil{}:
      hfm
    case Con{+t, +rt}:
      match e:
        case True{}:
          (+tm, +em) = mm
          +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
          %em : {AD.full(U32, SM.map(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{w}, a}, _}, by)), dm) == True{} : Bool}
          %he : {AD.full(U32, SM.map(S.sp.nodes(rt, (i + 1 : U32), S.sp.node_k(_, S.Sp{P.H{KM.MG{w}, a}, LAT.fromT(U32, tm)}, t, i, by), by)), dm) == True{} : Bool}
          mfull_go(rt, hd_era(rt), {==}, w, a, Array.set(U32, LAT.fromT(U32, tm), i, P.era()), dm, (i + 1 : U32), by, LA.set_full(U32, LAT.fromT(U32, tm), dm, i, P.era(), hfmt), mw, ma, LAT.mirror(U32, Array.set(U32, LAT.fromT(U32, tm), i, P.era())))
        case False{}:
          (+t0, +ew) = mw
          (+ta, +ea) = ma
          (+tm, +em) = mm
          +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
          %ew : {AD.full(U32, SM.map(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{_}, a}, map}, by)), dm) == True{} : Bool}
          %ea : {AD.full(U32, SM.map(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map}, by)), dm) == True{} : Bool}
          %em : {AD.full(U32, SM.map(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, _}, by)), dm) == True{} : Bool}
          %he : {AD.full(U32, SM.map(S.sp.nodes(rt, (i + 1 : U32), S.sp.node_k(_, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, t, i, by), by)), dm) == True{} : Bool}
          %Equal.sym(S.Sp, S.sp.put(S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), LAT.fromT(U32, tm), i), S.Sp{Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)), Array.set(U32, LAT.fromT(U32, tm), i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, spput(S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), LAT.fromT(U32, tm), i)) :
            {AD.full(U32, SM.map(S.sp.nodes(rt, (i + 1 : U32), _, by)), dm) == True{} : Bool}
          %heta(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))) :
            {AD.full(U32, SM.map(S.sp.nodes(rt, (i + 1 : U32), S.Sp{_, Array.set(U32, LAT.fromT(U32, tm), i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, by)), dm) == True{} : Bool}
          mfull_go(rt, hd_era(rt), {==}, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), Array.set(U32, LAT.fromT(U32, tm), i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), dm, (i + 1 : U32), by, LA.set_full(U32, LAT.fromT(U32, tm), dm, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)), hfmt), LAT.mirror(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), LAT.mirror(V.Val, KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), LAT.mirror(U32, Array.set(U32, LAT.fromT(U32, tm), i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))))

def or_r(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def or_l(+a: Bool, b: Bool, ha: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  ME.subst(Bool, z => {Bool.or(z, b) == True{} : Bool}, True{}, a, Equal.sym(Bool, a, True{}, ha), {==})

def u32_refl(+x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  Equal.trans(Bool, U32.is_eq(x, x), Nat.is_eq(U32.to_nat(x), U32.to_nat(x)), True{}, MU.u32_is_eq_to_nat(x, x), MN.is_eq_refl(U32.to_nat(x)))

def ksub(xs: List<&2, U32>, +ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, r}:
      KMd.has(ys, x) && ksub(r, ys)

def khas_self(+x: U32, +ys: List<&2, U32>) -> {KMd.has(Con{x, ys}, x) == True{} : Bool}:
  or_l(U32.is_eq(x, x), KMd.has(ys, x), u32_refl(x))

def ksub_cons_r(xs: List<&2, U32>, +z: U32, +ys: List<&2, U32>, +h: {ksub(xs, ys) == True{} : Bool}) -> {ksub(xs, Con{z, ys}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      MB.and_eq_true(KMd.has(Con{z, ys}, x), ksub(r, Con{z, ys}), or_r(U32.is_eq(z, x), KMd.has(ys, x), MB.eq_true_of_and_left(KMd.has(ys, x), ksub(r, ys), h)), ksub_cons_r(r, z, ys, MB.eq_true_of_and_right(KMd.has(ys, x), ksub(r, ys), h)))

def ksub_refl(xs: List<&2, U32>) -> {ksub(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      MB.and_eq_true(KMd.has(Con{x, r}, x), ksub(r, Con{x, r}), khas_self(x, r), ksub_cons_r(r, x, r, ksub_refl(r)))

# the template's premise joined to the map: at each slot, the kind the
# node pass last wrote (SM.kind_at) and the word it wrote (SM.ent) agree,
# an eraser's the static, a node's one of the fresh nodes
def kw.ok(+k: U32, +w: U32, +all: List<&2, U32>) -> Bool:
  Bool.and(Bool.or(Bool.not(U32.is_eq(k, 2)), U32.is_eq(w, P.era())), Bool.or(Bool.not(U32.is_eq(k, 1)), KMd.has(all, w)))

def ce(+b: Bool, +ok: U32, +ow: U32, +all: List<&2, U32>, +h: {kw.ok(ok, ow, all) == True{} : Bool}) ->
    {kw.ok(SM.pick(b, 2, ok), SM.pick(b, P.era(), ow), all) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      h

def cn(+b: Bool, +ok: U32, +ow: U32, +m: U32, +all: List<&2, U32>, +hm: {KMd.has(all, m) == True{} : Bool}, +h: {kw.ok(ok, ow, all) == True{} : Bool}) ->
    {kw.ok(SM.pick(b, 1, ok), SM.pick(b, m, ow), all) == True{} : Bool}:
  match b:
    case True{}:
      hm
    case False{}:
      h

def kinds_go(ts: List<&2, T.TNode>, +e: Bool, +he: {e == hd_era(ts) : Bool}, ns: List<&2, U32>, +all: List<&2, U32>, +i: U32, +dm: Nat, +ix: U32, +ok: U32, +ow: U32,
    hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}, +hs: {ksub(ns, all) == True{} : Bool}, +hc: {kw.ok(ok, ow, all) == True{} : Bool}) ->
  {kw.ok(SM.kind_at(ts, i, dm, ix, ok), SM.ent(ts, ns, i, dm, ix, ow), all) == True{} : Bool}:
  match ts:
    case Nil{}:
      hc
    case Con{+t, +rt}:
      match e:
        case True{}:
          +hl2 = ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == List.length(&2, U32, ns) : Nat}, S.sp.is_era(t), True{}, Equal.sym(Bool, True{}, S.sp.is_era(t), he), hl)
          %he : {kw.ok(SM.kind_at(rt, (i + 1 : U32), dm, ix, SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), SM.kc(_), ok)), SM.ent(rt, SM.ent.ns(_, ns), (i + 1 : U32), dm, ix, SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), SM.ent.w(_, ns), ow)), all) == True{} : Bool}
          kinds_go(rt, hd_era(rt), {==}, ns, all, (i + 1 : U32), dm, ix, SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), 2, ok), SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), P.era(), ow), hl2, hs, ce(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), ok, ow, all, hc))
        case False{}:
          match ns:
            case Nil{}:
              Empty.absurd({kw.ok(SM.kind_at(Con{t, rt}, i, dm, ix, ok), SM.ent(Con{t, rt}, Nil{}, i, dm, ix, ow), all) == True{} : Bool}, MB.false_ne_true()(Equal.sym(Bool, True{}, False{}, ME.subst(Nat, q => {Nat.is_eq(q, 0n) == False{} : Bool}, SM.made.k(False{}, SM.made(rt)), 0n, ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == 0n : Nat}, S.sp.is_era(t), False{}, Equal.sym(Bool, False{}, S.sp.is_era(t), he), hl), {==}))))
            case Con{+m, +r}:
              %he : {kw.ok(SM.kind_at(rt, (i + 1 : U32), dm, ix, SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), SM.kc(_), ok)), SM.ent(rt, SM.ent.ns(_, Con{m, r}), (i + 1 : U32), dm, ix, SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), SM.ent.w(_, Con{m, r}), ow)), all) == True{} : Bool}
              kinds_go(rt, hd_era(rt), {==}, r, all, (i + 1 : U32), dm, ix, SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), 1, ok), SM.pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), m, ow), npred_eq(SM.made(rt), List.length(&2, U32, r), ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == List.length(&2, U32, Con{m, r}) : Nat}, S.sp.is_era(t), False{}, Equal.sym(Bool, False{}, S.sp.is_era(t), he), hl)),
                MB.eq_true_of_and_right(KMd.has(all, m), ksub(r, all), hs), cn(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), ok, ow, m, all, MB.eq_true_of_and_left(KMd.has(all, m), ksub(r, all), hs), hc))

# an end the template's premise admits, its word agreeing with its kind:
# the static at an eraser's principal, or a fresh node's port
def eo_a(+k: U32, +w: U32, +p: U32, +ns: List<&2, U32>, +q: {Bool.and(U32.is_eq(k, 2), U32.is_eq(p, 0)) == True{} : Bool}, +hc: {kw.ok(k, w, ns) == True{} : Bool}) -> {Bool.or(P.is_static((w + p : U32)), Bool.and(KMd.has(ns, w), SM.port3(p))) == True{} : Bool}:
  +k2 = MS.u32_eq_of_is_eq(k, 2, MB.eq_true_of_and_left(U32.is_eq(k, 2), U32.is_eq(p, 0), q))
  +p0 = MS.u32_eq_of_is_eq(p, 0, MB.eq_true_of_and_right(U32.is_eq(k, 2), U32.is_eq(p, 0), q))
  +hw = MS.u32_eq_of_is_eq(w, P.era(), ME.subst(U32, z => {Bool.or(Bool.not(U32.is_eq(z, 2)), U32.is_eq(w, P.era())) == True{} : Bool}, k, 2, k2, MB.eq_true_of_and_left(Bool.or(Bool.not(U32.is_eq(k, 2)), U32.is_eq(w, P.era())), Bool.or(Bool.not(U32.is_eq(k, 1)), KMd.has(ns, w)), hc)))
  %Equal.sym(U32, w, P.era(), hw) : {Bool.or(P.is_static((_ + p : U32)), Bool.and(KMd.has(ns, _), SM.port3(p))) == True{} : Bool}
  %Equal.sym(U32, p, 0, p0) : {Bool.or(P.is_static((P.era() + _ : U32)), Bool.and(KMd.has(ns, P.era()), SM.port3(_))) == True{} : Bool}
  {==}

def eo_b(+k: U32, +w: U32, +p: U32, +ns: List<&2, U32>, +q: {Bool.and(U32.is_eq(k, 1), SM.port3(p)) == True{} : Bool}, +hc: {kw.ok(k, w, ns) == True{} : Bool}) -> {Bool.or(P.is_static((w + p : U32)), Bool.and(KMd.has(ns, w), SM.port3(p))) == True{} : Bool}:
  +k1 = MS.u32_eq_of_is_eq(k, 1, MB.eq_true_of_and_left(U32.is_eq(k, 1), SM.port3(p), q))
  +hh = ME.subst(U32, z => {Bool.or(Bool.not(U32.is_eq(z, 1)), KMd.has(ns, w)) == True{} : Bool}, k, 1, k1, MB.eq_true_of_and_right(Bool.or(Bool.not(U32.is_eq(k, 2)), U32.is_eq(w, P.era())), Bool.or(Bool.not(U32.is_eq(k, 1)), KMd.has(ns, w)), hc))
  or_r(P.is_static((w + p : U32)), Bool.and(KMd.has(ns, w), SM.port3(p)), MB.and_eq_true(KMd.has(ns, w), SM.port3(p), hh, MB.eq_true_of_and_right(U32.is_eq(k, 1), SM.port3(p), q)))

def end_of(+k: U32, +w: U32, +p: U32, +ns: List<&2, U32>, +htm: {SM.tm.k(k, p) == True{} : Bool}, +hc: {kw.ok(k, w, ns) == True{} : Bool}) -> {Bool.or(P.is_static((w + p : U32)), Bool.and(KMd.has(ns, w), SM.port3(p))) == True{} : Bool}:
  or_cases(Bool.and(U32.is_eq(k, 2), U32.is_eq(p, 0)), Bool.and(U32.is_eq(k, 1), SM.port3(p)), Bool.or(P.is_static((w + p : U32)), Bool.and(KMd.has(ns, w), SM.port3(p))), htm,
    q => eo_a(k, w, p, ns, q, hc), q => eo_b(k, w, p, ns, q, hc))

# an end the template's premise admits is one links_keeps admits, read
# in the map the node pass leaves (nodes_maps)
def endk(+n: U32, +p: U32, +ts: List<&2, T.TNode>, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +d: Nat, +dm: Nat, +by: U32, +ns: List<&2, U32>,
    +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hfmt: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
    +hct: {KMd.chain(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}, +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat},
    +hap: {KMd.apart(ns, d) == True{} : Bool}, +hpa: {KMd.past(ns, d) == True{} : Bool}, +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool},
    +htm: {SM.tm.k(SM.kind_at(ts, 0, dm, n, 0), p) == True{} : Bool}) -> {SM.end.ok(T.TE{n, p}, AD.view(U32, SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))), dm, ns) == True{} : Bool}:
  ME.subst(U32, z => {Bool.or(P.is_static((z + p : U32)), Bool.and(KMd.has(ns, z), SM.port3(p))) == True{} : Bool}, SM.ent(ts, ns, 0, dm, n, KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n)), KMd.word(AD.view(U32, SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))), dm, n),
    Equal.sym(U32, KMd.word(AD.view(U32, SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))), dm, n), SM.ent(ts, ns, 0, dm, n, KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n)), Laws.nodes_maps(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), LAT.fromT(U32, tm), d, dm, ts, 0, by, ns, n, hft, hd32, hfmt, hdm, hct, hl, hap, hpa, hhd)),
    end_of(SM.kind_at(ts, 0, dm, n, 0), SM.ent(ts, ns, 0, dm, n, KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n)), p, ns, htm, kinds_go(ts, hd_era(ts), {==}, ns, ns, 0, dm, n, 0, KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n), hl, ksub_refl(ns), {==})))

def ends_go(ls: List<&2, T.TLink>, +ts: List<&2, T.TNode>, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +d: Nat, +dm: Nat, +by: U32, +ns: List<&2, U32>,
    +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hfmt: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
    +hct: {KMd.chain(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}, +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat},
    +hap: {KMd.apart(ns, d) == True{} : Bool}, +hpa: {KMd.past(ns, d) == True{} : Bool}, +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool},
    +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}) -> {SM.ends.ok(ls, AD.view(U32, SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))), dm, ns) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, +rest}:
      match l:
        case T.TL{e1, e2}:
          match e1:
            case T.TE{+n1, +p1}:
              match e2:
                case T.TE{+n2, +p2}:
                  MB.and_eq_true(SM.link.ok(T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, AD.view(U32, SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))), dm, ns), SM.ends.ok(rest, AD.view(U32, SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))), dm, ns),
                    MB.and_eq_true(SM.end.ok(T.TE{n1, p1}, AD.view(U32, SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))), dm, ns), SM.end.ok(T.TE{n2, p2}, AD.view(U32, SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))), dm, ns), endk(n1, p1, ts, t0, ta, tm, d, dm, by, ns, hft, hd32, hfmt, hdm, hct, hl, hap, hpa, hhd, MB.eq_true_of_and_left(SM.tm.end(T.TE{n1, p1}, ts, dm), SM.tm.end(T.TE{n2, p2}, ts, dm), MB.eq_true_of_and_left(SM.tm.link(T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, ts, dm), SM.tpl.ok(rest, ts, dm), ht))), endk(n2, p2, ts, t0, ta, tm, d, dm, by, ns, hft, hd32, hfmt, hdm, hct, hl, hap, hpa, hhd, MB.eq_true_of_and_right(SM.tm.end(T.TE{n1, p1}, ts, dm), SM.tm.end(T.TE{n2, p2}, ts, dm), MB.eq_true_of_and_left(SM.tm.link(T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, ts, dm), SM.tpl.ok(rest, ts, dm), ht)))),
                    ends_go(rest, ts, t0, ta, tm, d, dm, by, ns, hft, hd32, hfmt, hdm, hct, hl, hap, hpa, hhd, MB.eq_true_of_and_right(SM.tm.link(T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, ts, dm), SM.tpl.ok(rest, ts, dm), ht)))

# the splice's state, restated in its parts
def speta(s: S.Sp) -> {S.Sp{SM.heap(s), SM.map(s)} == s : S.Sp}:
  match s:
    case S.Sp{h, m}:
      {==}

# the copy's two passes: the node pass's frame, then the links pass's in
# the heap and map it leaves, its ends admitted by the template's premise
def splice_go(-w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +ts: List<&2, T.TNode>, +ls: List<&2, T.TLink>, +by: U32, +ns: List<&2, U32>, +j: U32,
    hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hfm: {AD.full(U32, map, dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
    hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}, +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat},
    +hap: {KMd.apart(ns, d) == True{} : Bool}, +hpa: {KMd.past(ns, d) == True{} : Bool}, +hj: {KMd.nodes.off(ns, d, j) == True{} : Bool},
    +hjh: {KMd.off.words(KMd.hdr_all(), d, j) == True{} : Bool}, +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}, +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool},
    mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t0, +ew) = mw
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, w, t0, d, ew, hf)
  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
  +hct = LAB.subst(Array<U32>, q => {KMd.chain(ns, AD.view(U32, q), d, KMd.word(AD.view(U32, q), d, P.at_fh())) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, ew), hc)
  %ew : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{_}, a}, map}, by))), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  %ea : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map}, by))), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, _}, j)) : U32}
  %em : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, _}, by))), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %speta(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)) : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(ls, _)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  %heta(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))) : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(ls, S.Sp{_, SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))})), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)) : U32}
  ME.trans3(U32, Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{KMd.words(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)))}, KMd.vals(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)))}, SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))})), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)))}, KMd.vals(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)))}, j)), Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)),
    Laws.links_keeps(KMd.words(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))), KMd.vals(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))), SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)), d, dm, ls, ns, j,
      full_go(ts, hd_era(ts), {==}, LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), LAT.fromT(U32, tm), d, 0, by, ns, hft, hd32, hct, hl, hap, hpa, hhd, LAT.mirror(U32, LAT.fromT(U32, t0)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))), hd32,
      mfull_go(ts, hd_era(ts), {==}, LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), LAT.fromT(U32, tm), dm, 0, by, hfmt, LAT.mirror(U32, LAT.fromT(U32, t0)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)), LAT.mirror(U32, LAT.fromT(U32, tm))), hdm,
      ends_go(ls, ts, t0, ta, tm, d, dm, by, ns, hft, hd32, hfmt, hdm, hct, hl, hap, hpa, hhd, ht), hj),
    ME.subst(P.H, q => {Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)))}, KMd.vals(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)))}, j)) == Pair.snd(P.H, U32, P.rd(q, j)) : U32}, P.H{KM.MG{KMd.words(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)))}, KMd.vals(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)))}, SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)), heta(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))), {==}),
    Laws.nodes_keeps(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), LAT.fromT(U32, tm), d, ts, 0, by, ns, j, hft, hd32, hct, hl, hap, hpa, hj, hjh, hhd))

def Laws.splice_keeps(w, a, map, d, dm, ts, ls, by, ns, j, hf, hd32, hfm, hdm, hc, hl, hap, hpa, hj, hjh, hhd, ht):
  splice_go(w, a, map, d, dm, ts, ls, by, ns, j, hf, hd32, hfm, hdm, hc, hl, hap, hpa, hj, hjh, hhd, ht, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))

# The links pass's words. A word after a set: the value at the set's
# slot, the word before elsewhere; over an array set once already
def get_slot_eq1(+t0: LAT.Tree<U32>, +k1: U32, +v1: U32, +d: Nat, +i: U32, +j: U32, +v: U32, +hfa: {AD.full(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
    hij: {Nat.is_eq(AD.slot(i, d), AD.slot(j, d)) == True{} : Bool}) -> {Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), i, v), j)) == v : U32}:
  some_inj(Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), i, v), j)), v, Equal.trans(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), i, v), j))}, List.get(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), i, v)), AD.slot(j, d)), Maybe.map(&2, U32, U32, z => v, Some{Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), i))}), LA.get_view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), i, v), d, j, LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), d, i, v, hfa), hd32), Equal.trans(Maybe<&2, U32>, List.get(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), i, v)), AD.slot(j, d)), List.get(&2, U32, List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1)), AD.slot(i, d), v), AD.slot(j, d)), Maybe.map(&2, U32, U32, z => v, Some{Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), i))}), ME.subst(List<&2, U32>, xs => {List.get(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), i, v)), AD.slot(j, d)) == List.get(&2, U32, xs, AD.slot(j, d)) : Maybe<&2, U32>}, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), i, v)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1)), AD.slot(i, d), v), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), d, i, v, hfa, hd32), {==}), Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1)), AD.slot(i, d), v), AD.slot(j, d)), List.get(&2, U32, List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1)), AD.slot(i, d), v), AD.slot(i, d)), Maybe.map(&2, U32, U32, z => v, Some{Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), i))}), ME.subst(Nat, k => {List.get(&2, U32, List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1)), AD.slot(i, d), v), AD.slot(j, d)) == List.get(&2, U32, List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1)), AD.slot(i, d), v), k) : Maybe<&2, U32>}, AD.slot(j, d), AD.slot(i, d), Equal.sym(Nat, AD.slot(i, d), AD.slot(j, d), MN.eq_of_is_eq(AD.slot(i, d), AD.slot(j, d), hij)), {==}), Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1)), AD.slot(i, d), v), AD.slot(i, d)), Maybe.map(&2, U32, U32, z => v, List.get(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1)), AD.slot(i, d))), Maybe.map(&2, U32, U32, z => v, Some{Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), i))}), ML.get_set_self(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1)), AD.slot(i, d), v), ME.subst(Maybe<&2, U32>, mm => {Maybe.map(&2, U32, U32, z => v, List.get(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1)), AD.slot(i, d))) == Maybe.map(&2, U32, U32, z => v, mm) : Maybe<&2, U32>}, List.get(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1)), AD.slot(i, d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), i))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), i))}, List.get(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1)), AD.slot(i, d)), LA.get_view(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), d, i, hfa, hd32)), {==}))))))

def aset.k(+b: Bool, +t0: LAT.Tree<U32>, +d: Nat, +k: U32, +j: U32, +v: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hb: {Nat.is_eq(AD.slot(k, d), AD.slot(j, d)) == b : Bool}) ->
    {Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), k, v), j)) == SM.pick(b, v, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j))) : U32}:
  match b:
    case True{}:
      get_slot_eq(t0, d, k, j, v, hft, hd32, hb)
    case False{}:
      LA.get_set_other(U32, LAT.fromT(U32, t0), d, k, j, v, hft, hd32, hb)

def aset(+t0: LAT.Tree<U32>, +d: Nat, +k: U32, +j: U32, +v: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
    {Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), k, v), j)) == SM.pick(Nat.is_eq(AD.slot(k, d), AD.slot(j, d)), v, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j))) : U32}:
  aset.k(Nat.is_eq(AD.slot(k, d), AD.slot(j, d)), t0, d, k, j, v, hft, hd32, {==})

def aset1.k(+b: Bool, +t0: LAT.Tree<U32>, +k1: U32, +v1: U32, +d: Nat, +k: U32, +j: U32, +v: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hb: {Nat.is_eq(AD.slot(k, d), AD.slot(j, d)) == b : Bool}) ->
    {Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), k, v), j)) == SM.pick(b, v, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), j))) : U32}:
  match b:
    case True{}:
      get_slot_eq1(t0, k1, v1, d, k, j, v, LA.set_full(U32, LAT.fromT(U32, t0), d, k1, v1, hft), hd32, hb)
    case False{}:
      LA.get_set_other(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), d, k, j, v, LA.set_full(U32, LAT.fromT(U32, t0), d, k1, v1, hft), hd32, hb)

def aset1(+t0: LAT.Tree<U32>, +k1: U32, +v1: U32, +d: Nat, +k: U32, +j: U32, +v: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
    {Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), k, v), j)) == SM.pick(Nat.is_eq(AD.slot(k, d), AD.slot(j, d)), v, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), k1, v1), j))) : U32}:
  aset1.k(Nat.is_eq(AD.slot(k, d), AD.slot(j, d)), t0, k1, v1, d, k, j, v, hft, hd32, {==})

# link_xx's content: its first end's link word written, unless static,
# then its second's
def lx_rd(+sx: Bool, +sy: Bool, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +x: U32, +y: U32, +j: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
    {Pair.snd(P.H, U32, P.rd(P.link.to(sy, P.link.to(sx, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, x, y), y, x), j)) == SM.lw.w(sy, y, x, d, j, SM.lw.w(sx, x, y, d, j, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)))) : U32}:
  match sx:
    case True{}:
      match sy:
        case True{}:
          {==}
        case False{}:
          ME.trans3(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), (y + 1 : U32), x)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), (y + 1 : U32), x), j)), SM.pick(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), x, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j))), SM.pick(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), x, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j))), SP.rd_get(Array.set(U32, LAT.fromT(U32, t0), (y + 1 : U32), x), LAT.fromT(V.Val, ta), j), aset(t0, d, (y + 1 : U32), j, x, hft, hd32), ME.subst(U32, z => {SM.pick(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), x, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j))) == SM.pick(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), x, z) : U32}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)), Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), j)), {==}))
    case False{}:
      match sy:
        case True{}:
          ME.trans3(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), (x + 1 : U32), y)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), (x + 1 : U32), y), j)), SM.pick(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(j, d)), y, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j))), SM.pick(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(j, d)), y, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j))), SP.rd_get(Array.set(U32, LAT.fromT(U32, t0), (x + 1 : U32), y), LAT.fromT(V.Val, ta), j), aset(t0, d, (x + 1 : U32), j, y, hft, hd32), ME.subst(U32, z => {SM.pick(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(j, d)), y, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j))) == SM.pick(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(j, d)), y, z) : U32}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)), Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), j)), {==}))
        case False{}:
          ME.trans3(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (x + 1 : U32), y), (y + 1 : U32), x)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (x + 1 : U32), y), (y + 1 : U32), x), j)), SM.pick(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), x, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), (x + 1 : U32), y), j))), SM.pick(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), x, SM.pick(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(j, d)), y, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)))), SP.rd_get(Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (x + 1 : U32), y), (y + 1 : U32), x), LAT.fromT(V.Val, ta), j), aset1(t0, (x + 1 : U32), y, d, (y + 1 : U32), j, x, hft, hd32),
            Equal.trans(U32, SM.pick(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), x, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), (x + 1 : U32), y), j))), SM.pick(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), x, SM.pick(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(j, d)), y, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)))), SM.pick(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), x, SM.pick(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(j, d)), y, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)))), ME.subst(U32, z => {SM.pick(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), x, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), (x + 1 : U32), y), j))) == SM.pick(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), x, z) : U32}, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), (x + 1 : U32), y), j)), SM.pick(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(j, d)), y, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j))), aset(t0, d, (x + 1 : U32), j, y, hft, hd32), {==}), ME.subst(U32, z => {SM.pick(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), x, SM.pick(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(j, d)), y, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)))) == SM.pick(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d)), x, SM.pick(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(j, d)), y, z)) : U32}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)), Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), j)), {==})))

# the links pass's words, by induction on the links, each link's writes
# by link_xx's content
def links_words_go(ls: List<&2, T.TLink>, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hfm: {AD.full(U32, map, dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{w}, a}, map})), j)) == SM.lw(ls, AD.view(U32, map), dm, d, j, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j))) : U32}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, +rest}:
      match l:
        case T.TL{e1, e2}:
          match e1:
            case T.TE{+n1, +p1}:
              match e2:
                case T.TE{+n2, +p2}:
                  (+t0, +ew) = mw
                  (+ta, +eav) = ma
                  (+tm, +em) = mm
                  +hft = LAP.full_t(U32, w, t0, d, ew, hf)
                  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
                  %ew : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(Con{T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, rest}, S.Sp{P.H{KM.MG{_}, a}, map})), j)) == SM.lw(Con{T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, rest}, AD.view(U32, map), dm, d, j, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j))) : U32}
                  %eav : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(Con{T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, rest}, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map})), j)) == SM.lw(Con{T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, rest}, AD.view(U32, map), dm, d, j, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, _}, j))) : U32}
                  %em : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(Con{T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, rest}, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, _})), j)) == SM.lw(Con{T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, rest}, AD.view(U32, _), dm, d, j, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j))) : U32}
                  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, tm), n1), (LAT.fromT(U32, tm), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1))), LA.get_pair(U32, LAT.fromT(U32, tm), n1)) :
                    {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(rest, S.sp.link1(S.sp.ref(_, p1), T.TE{n2, p2}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}))), j)) == SM.lw(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, d, j, SM.lw.w(P.is_static((KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n2) + p2 : U32)), (KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n2) + p2 : U32), (KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n1) + p1 : U32), d, j, SM.lw.w(P.is_static((KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n1) + p1 : U32)), (KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n1) + p1 : U32), (KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n2) + p2 : U32), d, j, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j))))) : U32}
                  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, tm), n2), (LAT.fromT(U32, tm), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2))), LA.get_pair(U32, LAT.fromT(U32, tm), n2)) :
                    {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(rest, S.sp.link2(S.sp.ref(_, p2), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}))), j)) == SM.lw(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, d, j, SM.lw.w(P.is_static((KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n2) + p2 : U32)), (KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n2) + p2 : U32), (KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n1) + p1 : U32), d, j, SM.lw.w(P.is_static((KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n1) + p1 : U32)), (KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n1) + p1 : U32), (KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n2) + p2 : U32), d, j, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j))))) : U32}
                  %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n1), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)), word_get(LAT.fromT(U32, tm), dm, n1, hfmt, hdm)) :
                    {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(rest, S.Sp{P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)), LAT.fromT(U32, tm)})), j)) == SM.lw(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, d, j, SM.lw.w(P.is_static((KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n2) + p2 : U32)), (KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n2) + p2 : U32), (_ + p1 : U32), d, j, SM.lw.w(P.is_static((_ + p1 : U32)), (_ + p1 : U32), (KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n2) + p2 : U32), d, j, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j))))) : U32}
                  %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, tm)), dm, n2), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)), word_get(LAT.fromT(U32, tm), dm, n2, hfmt, hdm)) :
                    {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(rest, S.Sp{P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)), LAT.fromT(U32, tm)})), j)) == SM.lw(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, d, j, SM.lw.w(P.is_static((_ + p2 : U32)), (_ + p2 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), d, j, SM.lw.w(P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32)), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (_ + p2 : U32), d, j, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j))))) : U32}
                  %heta(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32))) :
                    {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(rest, S.Sp{_, LAT.fromT(U32, tm)})), j)) == SM.lw(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, d, j, SM.lw.w(P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), d, j, SM.lw.w(P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32)), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32), d, j, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j))))) : U32}
                  ME.subst(U32, z => {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(rest, S.Sp{P.H{KM.MG{KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, LAT.fromT(U32, tm)})), j)) == SM.lw(rest, AD.view(U32, LAT.fromT(U32, tm)), dm, d, j, z) : U32}, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, j)), SM.lw.w(P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), d, j, SM.lw.w(P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32)), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32), d, j, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)))), Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, j)), Pair.snd(P.H, U32, P.rd(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)), j)), SM.lw.w(P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), d, j, SM.lw.w(P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32)), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32), d, j, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)))), ME.subst(P.H, q => {Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, j)) == Pair.snd(P.H, U32, P.rd(q, j)) : U32}, P.H{KM.MG{KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))}, P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)), heta(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32))), {==}), lx_rd(P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32)), P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)), t0, ta, d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32), j, hft, hd32)), links_words_go(rest, KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32))), KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32))), LAT.fromT(U32, tm), d, dm, j, lxf(P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32)), P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)), t0, LAT.fromT(V.Val, ta), d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32), hft), hd32, hfmt, hdm, LAT.mirror(U32, KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))), LAT.mirror(V.Val, KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))), LAT.mirror(U32, LAT.fromT(U32, tm))))

def Laws.links_words(w, a, map, d, dm, ls, j, hf, hd32, hfm, hdm):
  links_words_go(ls, w, a, map, d, dm, j, hf, hd32, hfm, hdm, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))

# The free list after the copy's nodes (splice_free): the node pass takes
# ns, the chain of the nodes F after them left at the head it leaves; as
# nodes_go, the chain carried ns's and F's together, each step's by sn and
# ctr
def nf_go(ts: List<&2, T.TNode>, +e: Bool, +he: {e == hd_era(ts) : Bool}, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +i: U32, +by: U32, ns: List<&2, U32>, +F: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hc: {KMd.chain(List.append(&2, U32, ns, F), AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool},
  hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}, +hap: {KMd.apart(List.append(&2, U32, ns, F), d) == True{} : Bool}, +hpa: {KMd.past(List.append(&2, U32, ns, F), d) == True{} : Bool},
  +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}, mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.nodes(ts, i, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.nodes(ts, i, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), d, P.at_fh())) == True{} : Bool}:
  match ts:
    case Nil{}:
      match ns:
        case Nil{}:
          hc
        case Con{+n, +rn}:
          Empty.absurd({KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.nodes([], i, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.nodes([], i, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), d, P.at_fh())) == True{} : Bool}, MB.false_ne_true()(ME.subst(Nat, q => {Nat.is_eq(0n, q) == True{} : Bool}, 0n, List.length(&2, U32, Con{n, rn}), hl, {==})))
    case Con{+t, +rt}:
      match e:
        case True{}:
          +hl2 = ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == List.length(&2, U32, ns) : Nat}, S.sp.is_era(t), True{}, Equal.sym(Bool, True{}, S.sp.is_era(t), he), hl)
          %he : {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.sp.node_k(_, S.Sp{P.H{KM.MG{w}, a}, map}, t, i, by), by)))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.sp.node_k(_, S.Sp{P.H{KM.MG{w}, a}, map}, t, i, by), by)))), d, P.at_fh())) == True{} : Bool}
          nf_go(rt, hd_era(rt), {==}, w, a, Array.set(U32, map, i, P.era()), d, (i + 1 : U32), by, ns, F, hf, hd32, hc, hl2, hap, hpa, hhd, mw, ma)
        case False{}:
          match ns:
            case Nil{}:
              Empty.absurd({KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), d, P.at_fh())) == True{} : Bool}, MB.false_ne_true()(Equal.sym(Bool, True{}, False{}, ME.subst(Nat, q => {Nat.is_eq(q, 0n) == False{} : Bool}, SM.made.k(False{}, SM.made(rt)), 0n, ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == 0n : Nat}, S.sp.is_era(t), False{}, Equal.sym(Bool, False{}, S.sp.is_era(t), he), hl), {==}))))
            case Con{+n, +rn}:
              (+t0, +ew) = mw
              (+ta, +ea) = ma
              +hft = LAP.full_t(U32, w, t0, d, ew, hf)
              +hct = LAB.subst(Array<U32>, q => {KMd.chain(Con{n, List.append(&2, U32, rn, F)}, AD.view(U32, q), d, KMd.word(AD.view(U32, q), d, P.at_fh())) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, ew), hc)
              +hne = ME.subst(U32, x => {U32.is_eq(x, 0) == False{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), word_get(LAT.fromT(U32, t0), d, P.at_fh(), hft, hd32), MB.eq_false_of_not_eq_true(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0), MB.eq_true_of_and_left(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(List.append(&2, U32, rn, F), AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct)))
              +hidx = ME.subst(U32, x => {KMd.at_idx(x) == n : U32}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), word_get(LAT.fromT(U32, t0), d, P.at_fh(), hft, hd32), MS.u32_eq_of_is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n, MB.eq_true_of_and_left(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(List.append(&2, U32, rn, F), AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(List.append(&2, U32, rn, F), AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct))))
              %ew : {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{_}, a}, map}, by)))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{_}, a}, map}, by)))), d, P.at_fh())) == True{} : Bool}
              %ea : {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map}, by)))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map}, by)))), d, P.at_fh())) == True{} : Bool}
              %he : {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.sp.node_k(_, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, map}, t, i, by), by)))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.sp.node_k(_, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, map}, t, i, by), by)))), d, P.at_fh())) == True{} : Bool}
              %Equal.sym(S.Sp, S.sp.put(S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), map, i), S.Sp{Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)), Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, spput(S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), map, i)) :
                {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.nodes(rt, (i + 1 : U32), _, by)))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.nodes(rt, (i + 1 : U32), _, by)))), d, P.at_fh())) == True{} : Bool}
              %heta(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))) :
                {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.Sp{_, Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, by)))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.Sp{_, Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, by)))), d, P.at_fh())) == True{} : Bool}
              nf_go(rt, hd_era(rt), {==}, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), d, (i + 1 : U32), by, rn, F, sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), hd32,
                ME.subst(U32, x => {KMd.chain(List.append(&2, U32, rn, F), AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, x) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), ME.trans3(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), word_get(LAT.fromT(U32, t0), d, (n + 1 : U32), hft, hd32), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))), sn(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd, MB.eq_true_of_and_left(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(List.append(&2, U32, rn, F), d), hpa))), Equal.sym(U32, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), word_get(KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), d, P.at_fh(), sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), hd32))), ctr(List.append(&2, U32, rn, F), t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), MB.eq_true_of_and_left(KMd.apart.n(n, List.append(&2, U32, rn, F), d), KMd.apart(List.append(&2, U32, rn, F), d), hap), MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(List.append(&2, U32, rn, F), d), hpa), MB.eq_true_of_and_right(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(List.append(&2, U32, rn, F), AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(List.append(&2, U32, rn, F), AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct)))),
                npred_eq(SM.made(rt), List.length(&2, U32, rn), ME.subst(Bool, x => {SM.made.k(x, SM.made(rt)) == List.length(&2, U32, Con{n, rn}) : Nat}, S.sp.is_era(t), False{}, Equal.sym(Bool, False{}, S.sp.is_era(t), he), hl)),
                MB.eq_true_of_and_right(KMd.apart.n(n, List.append(&2, U32, rn, F), d), KMd.apart(List.append(&2, U32, rn, F), d), hap), MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(List.append(&2, U32, rn, F), d), hpa), hhd,
                LAT.mirror(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), LAT.mirror(V.Val, KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))))

# a node of the list's members of ms apart from n, its words off n's
def an_at(+n: U32, ms: List<&2, U32>, +d: Nat, +f: U32, +h: {KMd.apart.n(n, ms, d) == True{} : Bool}, hf: {KMd.has(ms, f) == True{} : Bool}) -> {KMd.ws.off(KMd.nw(f), KMd.nw(n), d) == True{} : Bool}:
  match ms:
    case Nil{}:
      Empty.absurd({KMd.ws.off(KMd.nw(f), KMd.nw(n), d) == True{} : Bool}, MB.false_ne_true()(hf))
    case Con{+m, +r}:
      or_cases(U32.is_eq(m, f), KMd.has(r, f), KMd.ws.off(KMd.nw(f), KMd.nw(n), d), hf,
        q => ME.subst(U32, z => {KMd.ws.off(KMd.nw(z), KMd.nw(n), d) == True{} : Bool}, m, f, MS.u32_eq_of_is_eq(m, f, q), MB.eq_true_of_and_left(KMd.ws.off(KMd.nw(m), KMd.nw(n), d), KMd.apart.n(n, r, d), h)),
        q => an_at(n, r, d, f, MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(m), KMd.nw(n), d), KMd.apart.n(n, r, d), h), q))

def kapp_r(A: List<&2, U32>, +B: List<&2, U32>, +x: U32, +h: {KMd.has(B, x) == True{} : Bool}) -> {KMd.has(List.append(&2, U32, A, B), x) == True{} : Bool}:
  match A:
    case Nil{}:
      h
    case Con{+y, +r}:
      or_r(U32.is_eq(y, x), KMd.has(List.append(&2, U32, r, B), x), kapp_r(r, B, x, h))

# a later node's word 1 off the fresh nodes ns, all apart
def nsoff(ns: List<&2, U32>, +Fa: List<&2, U32>, +d: Nat, +f: U32, +hap: {KMd.apart(List.append(&2, U32, ns, Fa), d) == True{} : Bool}, +hf: {KMd.has(Fa, f) == True{} : Bool}) -> {KMd.nodes.off(ns, d, (f + 1 : U32)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      MB.and_eq_true(KMd.off.words(KMd.nw(n), d, (f + 1 : U32)), KMd.nodes.off(r, d, (f + 1 : U32)),
        MB.eq_true_of_and_left(KMd.off.words(KMd.nw(n), d, (f + 1 : U32)), KMd.ws.off([(f + 2 : U32), (f + 3 : U32)], KMd.nw(n), d), MB.eq_true_of_and_right(KMd.off.words(KMd.nw(n), d, f), KMd.ws.off([(f + 1 : U32), (f + 2 : U32), (f + 3 : U32)], KMd.nw(n), d),
          an_at(n, List.append(&2, U32, r, Fa), d, f, MB.eq_true_of_and_left(KMd.apart.n(n, List.append(&2, U32, r, Fa), d), KMd.apart(List.append(&2, U32, r, Fa), d), hap), kapp_r(r, Fa, f, hf)))),
        nsoff(r, Fa, d, f, MB.eq_true_of_and_right(KMd.apart.n(n, List.append(&2, U32, r, Fa), d), KMd.apart(List.append(&2, U32, r, Fa), d), hap), hf))

# the head off the fresh nodes, past the header's words
def flipn(+a: Nat, +b: Nat, +h: {Bool.not(Nat.is_eq(a, b)) == True{} : Bool}) -> {Bool.not(Nat.is_eq(b, a)) == True{} : Bool}:
  ME.subst(Bool, q => {Bool.not(q) == True{} : Bool}, Nat.is_eq(a, b), Nat.is_eq(b, a), MN.is_eq_comm(a, b), h)

def npast(ns: List<&2, U32>, +d: Nat, +hp: {KMd.past(ns, d) == True{} : Bool}) -> {KMd.nodes.off(ns, d, P.at_fh()) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      +hw = MB.eq_true_of_and_left(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(r, d), hp)
      MB.and_eq_true(KMd.off.words(KMd.nw(n), d, P.at_fh()), KMd.nodes.off(r, d, P.at_fh()), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(n, d), AD.slot(P.at_fh(), d))), Bool.not(Nat.is_eq(AD.slot((n + 1 : U32), d), AD.slot(P.at_fh(), d))) && (Bool.not(Nat.is_eq(AD.slot((n + 2 : U32), d), AD.slot(P.at_fh(), d))) && (Bool.not(Nat.is_eq(AD.slot((n + 3 : U32), d), AD.slot(P.at_fh(), d))) && True{})), flipn(AD.slot(P.at_fh(), d), AD.slot(n, d), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(n, d))), KMd.off.words(KMd.hdr_words(), d, n), MB.eq_true_of_and_left(KMd.off.words(KMd.hdr_all(), d, n), KMd.ws.off([(n + 1 : U32), (n + 2 : U32), (n + 3 : U32)], KMd.hdr_all(), d), hw))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((n + 1 : U32), d), AD.slot(P.at_fh(), d))), Bool.not(Nat.is_eq(AD.slot((n + 2 : U32), d), AD.slot(P.at_fh(), d))) && (Bool.not(Nat.is_eq(AD.slot((n + 3 : U32), d), AD.slot(P.at_fh(), d))) && True{}), flipn(AD.slot(P.at_fh(), d), AD.slot((n + 1 : U32), d), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((n + 1 : U32), d))), KMd.off.words(KMd.hdr_words(), d, (n + 1 : U32)), MB.eq_true_of_and_left(KMd.off.words(KMd.hdr_all(), d, (n + 1 : U32)), KMd.ws.off([(n + 2 : U32), (n + 3 : U32)], KMd.hdr_all(), d), MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), d, n), KMd.ws.off([(n + 1 : U32), (n + 2 : U32), (n + 3 : U32)], KMd.hdr_all(), d), hw)))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((n + 2 : U32), d), AD.slot(P.at_fh(), d))), Bool.not(Nat.is_eq(AD.slot((n + 3 : U32), d), AD.slot(P.at_fh(), d))) && True{}, flipn(AD.slot(P.at_fh(), d), AD.slot((n + 2 : U32), d), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((n + 2 : U32), d))), KMd.off.words(KMd.hdr_words(), d, (n + 2 : U32)), MB.eq_true_of_and_left(KMd.off.words(KMd.hdr_all(), d, (n + 2 : U32)), KMd.ws.off([(n + 3 : U32)], KMd.hdr_all(), d), MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), d, (n + 1 : U32)), KMd.ws.off([(n + 2 : U32), (n + 3 : U32)], KMd.hdr_all(), d), MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), d, n), KMd.ws.off([(n + 1 : U32), (n + 2 : U32), (n + 3 : U32)], KMd.hdr_all(), d), hw))))), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((n + 3 : U32), d), AD.slot(P.at_fh(), d))), True{}, flipn(AD.slot(P.at_fh(), d), AD.slot((n + 3 : U32), d), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((n + 3 : U32), d))), KMd.off.words(KMd.hdr_words(), d, (n + 3 : U32)), MB.eq_true_of_and_left(KMd.off.words(KMd.hdr_all(), d, (n + 3 : U32)), KMd.ws.off([], KMd.hdr_all(), d), MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), d, (n + 2 : U32)), KMd.ws.off([(n + 3 : U32)], KMd.hdr_all(), d), MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), d, (n + 1 : U32)), KMd.ws.off([(n + 2 : U32), (n + 3 : U32)], KMd.hdr_all(), d), MB.eq_true_of_and_right(KMd.off.words(KMd.hdr_all(), d, n), KMd.ws.off([(n + 1 : U32), (n + 2 : U32), (n + 3 : U32)], KMd.hdr_all(), d), hw)))))), {==})))),
        npast(r, d, MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(r, d), hp)))

# the fresh nodes' facts from theirs and the later nodes' together
def kchain_pre(A: List<&2, U32>, +B: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +h: U32, +hc: {KMd.chain(List.append(&2, U32, A, B), v, d, h) == True{} : Bool}) -> {KMd.chain(A, v, d, h) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      MB.and_eq_true(Bool.not(U32.is_eq(h, 0)), U32.is_eq(KMd.at_idx(h), n) && KMd.chain(r, v, d, KMd.word(v, d, (n + 1 : U32))),
        MB.eq_true_of_and_left(Bool.not(U32.is_eq(h, 0)), U32.is_eq(KMd.at_idx(h), n) && KMd.chain(List.append(&2, U32, r, B), v, d, KMd.word(v, d, (n + 1 : U32))), hc),
        MB.and_eq_true(U32.is_eq(KMd.at_idx(h), n), KMd.chain(r, v, d, KMd.word(v, d, (n + 1 : U32))),
          MB.eq_true_of_and_left(U32.is_eq(KMd.at_idx(h), n), KMd.chain(List.append(&2, U32, r, B), v, d, KMd.word(v, d, (n + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(h, 0)), U32.is_eq(KMd.at_idx(h), n) && KMd.chain(List.append(&2, U32, r, B), v, d, KMd.word(v, d, (n + 1 : U32))), hc)),
          kchain_pre(r, B, v, d, KMd.word(v, d, (n + 1 : U32)), MB.eq_true_of_and_right(U32.is_eq(KMd.at_idx(h), n), KMd.chain(List.append(&2, U32, r, B), v, d, KMd.word(v, d, (n + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(h, 0)), U32.is_eq(KMd.at_idx(h), n) && KMd.chain(List.append(&2, U32, r, B), v, d, KMd.word(v, d, (n + 1 : U32))), hc)))))

def apn_pre(+n: U32, ms: List<&2, U32>, +B: List<&2, U32>, +d: Nat, +h: {KMd.apart.n(n, List.append(&2, U32, ms, B), d) == True{} : Bool}) -> {KMd.apart.n(n, ms, d) == True{} : Bool}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      MB.and_eq_true(KMd.ws.off(KMd.nw(m), KMd.nw(n), d), KMd.apart.n(n, r, d), MB.eq_true_of_and_left(KMd.ws.off(KMd.nw(m), KMd.nw(n), d), KMd.apart.n(n, List.append(&2, U32, r, B), d), h),
        apn_pre(n, r, B, d, MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(m), KMd.nw(n), d), KMd.apart.n(n, List.append(&2, U32, r, B), d), h)))

def kapart_pre(A: List<&2, U32>, +B: List<&2, U32>, +d: Nat, +h: {KMd.apart(List.append(&2, U32, A, B), d) == True{} : Bool}) -> {KMd.apart(A, d) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      MB.and_eq_true(KMd.apart.n(n, r, d), KMd.apart(r, d), apn_pre(n, r, B, d, MB.eq_true_of_and_left(KMd.apart.n(n, List.append(&2, U32, r, B), d), KMd.apart(List.append(&2, U32, r, B), d), h)),
        kapart_pre(r, B, d, MB.eq_true_of_and_right(KMd.apart.n(n, List.append(&2, U32, r, B), d), KMd.apart(List.append(&2, U32, r, B), d), h)))

def kpast_pre(A: List<&2, U32>, +B: List<&2, U32>, +d: Nat, +h: {KMd.past(List.append(&2, U32, A, B), d) == True{} : Bool}) -> {KMd.past(A, d) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      MB.and_eq_true(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(r, d), MB.eq_true_of_and_left(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(List.append(&2, U32, r, B), d), h),
        kpast_pre(r, B, d, MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(List.append(&2, U32, r, B), d), h)))

def lfull_k(ls: List<&2, T.TLink>, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat,
  hf: {AD.full(U32, w, d) == True{} : Bool}, mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {AD.full(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{w}, a}, map}))), d) == True{} : Bool}:
  match ls:
    case Nil{}:
      hf
    case Con{l, +rest}:
      match l:
        case T.TL{e1, e2}:
          match e1:
            case T.TE{+n1, +p1}:
              match e2:
                case T.TE{+n2, +p2}:
                  (+t0, +ew) = mw
                  (+ta, +eav) = ma
                  (+tm, +em) = mm
                  +hft = LAP.full_t(U32, w, t0, d, ew, hf)
                  %ew : {AD.full(U32, KMd.words(SM.heap(S.sp.links(Con{T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, rest}, S.Sp{P.H{KM.MG{_}, a}, map}))), d) == True{} : Bool}
                  %eav : {AD.full(U32, KMd.words(SM.heap(S.sp.links(Con{T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, rest}, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map}))), d) == True{} : Bool}
                  %em : {AD.full(U32, KMd.words(SM.heap(S.sp.links(Con{T.TL{T.TE{n1, p1}, T.TE{n2, p2}}, rest}, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, _}))), d) == True{} : Bool}
                  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, tm), n1), (LAT.fromT(U32, tm), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1))), LA.get_pair(U32, LAT.fromT(U32, tm), n1)) :
                    {AD.full(U32, KMd.words(SM.heap(S.sp.links(rest, S.sp.link1(S.sp.ref(_, p1), T.TE{n2, p2}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)})))), d) == True{} : Bool}
                  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, tm), n2), (LAT.fromT(U32, tm), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2))), LA.get_pair(U32, LAT.fromT(U32, tm), n2)) :
                    {AD.full(U32, KMd.words(SM.heap(S.sp.links(rest, S.sp.link2(S.sp.ref(_, p2), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)})))), d) == True{} : Bool}
                  %heta(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32))) :
                    {AD.full(U32, KMd.words(SM.heap(S.sp.links(rest, S.Sp{_, LAT.fromT(U32, tm)}))), d) == True{} : Bool}
                  lfull_k(rest, KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32))), KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32))), LAT.fromT(U32, tm), d, lxf(P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32)), P.is_static((Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)), t0, LAT.fromT(V.Val, ta), d, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32), hft), LAT.mirror(U32, KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))), LAT.mirror(V.Val, KMd.vals(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n1)) + p1 : U32), (Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), n2)) + p2 : U32)))), LAT.mirror(U32, LAT.fromT(U32, tm)))

# the links pass: a word off the fresh nodes reads alike in the views
def lfr(+t1: LAT.Tree<U32>, +ta1: LAT.Tree<V.Val>, +tm1: LAT.Tree<U32>, +ls: List<&2, T.TLink>, +d: Nat, +dm: Nat, +ns: List<&2, U32>, +i: U32, +hft1: {AD.full(U32, LAT.fromT(U32, t1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hfmt1: {AD.full(U32, LAT.fromT(U32, tm1), dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
  +he: {SM.ends.ok(ls, AD.view(U32, LAT.fromT(U32, tm1)), dm, ns) == True{} : Bool}, +hfW2: {AD.full(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)}))), d) == True{} : Bool}, +hj: {KMd.nodes.off(ns, d, i) == True{} : Bool}) -> {KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))), d, i) == KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, i) : U32}:
  Equal.trans(U32, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))), d, i), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)}))), i)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, i), word_get(KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)}))), d, i, hfW2, hd32), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)}))), i)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))}, KMd.vals(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))}, i)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, i), Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))}, KMd.vals(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))}, i)), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)}))), i)), SP.rd_get(KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)}))), KMd.vals(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)}))), i)), Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))}, KMd.vals(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))}, i)), Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})), i)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, i), Equal.cong(P.H, U32, hh => Pair.snd(P.H, U32, P.rd(hh, i)), P.H{KM.MG{KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))}, KMd.vals(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))}, SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})), heta(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))), Equal.trans(U32, Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})), i)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, i)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, i), Laws.links_keeps(LAT.fromT(U32, t1), LAT.fromT(V.Val, ta1), LAT.fromT(U32, tm1), d, dm, ls, ns, i, hft1, hd32, hfmt1, hdm, he, hj), Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, i)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t1), i)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, i), SP.rd_get(LAT.fromT(U32, t1), LAT.fromT(V.Val, ta1), i), Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, i), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t1), i)), word_get(LAT.fromT(U32, t1), d, i, hft1, hd32)))))))

# and the chain of the later nodes, their words 1 so
def lk_ch(K: List<&2, U32>, +Fa: List<&2, U32>, +t1: LAT.Tree<U32>, +ta1: LAT.Tree<V.Val>, +tm1: LAT.Tree<U32>, +ls: List<&2, T.TLink>, +d: Nat, +dm: Nat, +ns: List<&2, U32>, +hft1: {AD.full(U32, LAT.fromT(U32, t1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hfmt1: {AD.full(U32, LAT.fromT(U32, tm1), dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
  +he: {SM.ends.ok(ls, AD.view(U32, LAT.fromT(U32, tm1)), dm, ns) == True{} : Bool}, +hfW2: {AD.full(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)}))), d) == True{} : Bool},
  +hK: {ksub(K, Fa) == True{} : Bool}, +hap: {KMd.apart(List.append(&2, U32, ns, Fa), d) == True{} : Bool}, +h: U32, +hc: {KMd.chain(K, AD.view(U32, LAT.fromT(U32, t1)), d, h) == True{} : Bool}) -> {KMd.chain(K, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))), d, h) == True{} : Bool}:
  match K:
    case Nil{}:
      {==}
    case Con{+f, +r}:
      +hfa = MB.eq_true_of_and_left(KMd.has(Fa, f), ksub(r, Fa), hK)
      +heq = lfr(t1, ta1, tm1, ls, d, dm, ns, (f + 1 : U32), hft1, hd32, hfmt1, hdm, he, hfW2, nsoff(ns, Fa, d, f, hap, hfa))
      +hc2 = MB.eq_true_of_and_right(U32.is_eq(KMd.at_idx(h), f), KMd.chain(r, AD.view(U32, LAT.fromT(U32, t1)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (f + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(h, 0)), U32.is_eq(KMd.at_idx(h), f) && KMd.chain(r, AD.view(U32, LAT.fromT(U32, t1)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (f + 1 : U32))), hc))
      +hr = lk_ch(r, Fa, t1, ta1, tm1, ls, d, dm, ns, hft1, hd32, hfmt1, hdm, he, hfW2, MB.eq_true_of_and_right(KMd.has(Fa, f), ksub(r, Fa), hK), hap, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (f + 1 : U32)), hc2)
      MB.and_eq_true(Bool.not(U32.is_eq(h, 0)), U32.is_eq(KMd.at_idx(h), f) && KMd.chain(r, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))), d, (f + 1 : U32))),
        MB.eq_true_of_and_left(Bool.not(U32.is_eq(h, 0)), U32.is_eq(KMd.at_idx(h), f) && KMd.chain(r, AD.view(U32, LAT.fromT(U32, t1)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (f + 1 : U32))), hc),
        MB.and_eq_true(U32.is_eq(KMd.at_idx(h), f), KMd.chain(r, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))), d, (f + 1 : U32))),
          MB.eq_true_of_and_left(U32.is_eq(KMd.at_idx(h), f), KMd.chain(r, AD.view(U32, LAT.fromT(U32, t1)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (f + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(h, 0)), U32.is_eq(KMd.at_idx(h), f) && KMd.chain(r, AD.view(U32, LAT.fromT(U32, t1)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (f + 1 : U32))), hc)),
          ME.subst(U32, q => {KMd.chain(r, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))), d, q) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (f + 1 : U32)), KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))), d, (f + 1 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))), d, (f + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (f + 1 : U32)), heq), hr)))

def sf2(+ls: List<&2, T.TLink>, -w1: Array<U32>, -a1: Array<V.Val>, -map1: Array<U32>, +d: Nat, +dm: Nat, +ns: List<&2, U32>, +F: List<&2, U32>,
  hf1: {AD.full(U32, w1, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hfm1: {AD.full(U32, map1, dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
  he: {SM.ends.ok(ls, AD.view(U32, map1), dm, ns) == True{} : Bool}, +hap: {KMd.apart(List.append(&2, U32, ns, F), d) == True{} : Bool}, +hpa: {KMd.past(List.append(&2, U32, ns, F), d) == True{} : Bool},
  hc1: {KMd.chain(F, AD.view(U32, w1), d, KMd.word(AD.view(U32, w1), d, P.at_fh())) == True{} : Bool}, m1: LAT.Mirror(U32, w1), ma1: LAT.Mirror(V.Val, a1), mm1: LAT.Mirror(U32, map1)) -> {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{w1}, a1}, map1})))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{w1}, a1}, map1})))), d, P.at_fh())) == True{} : Bool}:
  (+t1, +e1) = m1
  (+ta1, +ea1) = ma1
  (+tm1, +em1) = mm1
  +hft1 = LAP.full_t(U32, w1, t1, d, e1, hf1)
  +hfmt1 = LAP.full_t(U32, map1, tm1, dm, em1, hfm1)
  +hc1T = LAB.subst(Array<U32>, q => {KMd.chain(F, AD.view(U32, q), d, KMd.word(AD.view(U32, q), d, P.at_fh())) == True{} : Bool}, w1, LAT.fromT(U32, t1), Equal.sym(Array<U32>, LAT.fromT(U32, t1), w1, e1), hc1)
  +heT = LAB.subst(Array<U32>, q => {SM.ends.ok(ls, AD.view(U32, q), dm, ns) == True{} : Bool}, map1, LAT.fromT(U32, tm1), Equal.sym(Array<U32>, LAT.fromT(U32, tm1), map1, em1), he)
  %e1 : {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{_}, a1}, map1})))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{_}, a1}, map1})))), d, P.at_fh())) == True{} : Bool}
  %ea1 : {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, _}, map1})))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, _}, map1})))), d, P.at_fh())) == True{} : Bool}
  %em1 : {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, _})))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, _})))), d, P.at_fh())) == True{} : Bool}
  +hfW2 = lfull_k(ls, LAT.fromT(U32, t1), LAT.fromT(V.Val, ta1), LAT.fromT(U32, tm1), d, hft1, LAT.mirror(U32, LAT.fromT(U32, t1)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta1)), LAT.mirror(U32, LAT.fromT(U32, tm1)))
  +hfh = lfr(t1, ta1, tm1, ls, d, dm, ns, P.at_fh(), hft1, hd32, hfmt1, hdm, heT, hfW2, npast(ns, d, kpast_pre(ns, F, d, hpa)))
  ME.subst(U32, q => {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))), d, q) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, P.at_fh()), KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))), d, P.at_fh()), Equal.sym(U32, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{LAT.fromT(U32, t1)}, LAT.fromT(V.Val, ta1)}, LAT.fromT(U32, tm1)})))), d, P.at_fh()), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, P.at_fh()), hfh),
    lk_ch(F, F, t1, ta1, tm1, ls, d, dm, ns, hft1, hd32, hfmt1, hdm, heT, hfW2, ksub_refl(F), hap, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, P.at_fh()), hc1T))

# the splice: the later nodes F the free list's first after it
def sfree_go(-w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +ts: List<&2, T.TNode>, +ls: List<&2, T.TLink>, +by: U32, +ns: List<&2, U32>, +F: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hfm: {AD.full(U32, map, dm) == True{} : Bool}, +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool},
  hc: {KMd.chain(List.append(&2, U32, ns, F), AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}, +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}, +hap: {KMd.apart(List.append(&2, U32, ns, F), d) == True{} : Bool}, +hpa: {KMd.past(List.append(&2, U32, ns, F), d) == True{} : Bool},
  +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}, +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}, mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))))), d, P.at_fh())) == True{} : Bool}:
  (+t0, +ew) = mw
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, w, t0, d, ew, hf)
  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
  +hct = LAB.subst(Array<U32>, q => {KMd.chain(List.append(&2, U32, ns, F), AD.view(U32, q), d, KMd.word(AD.view(U32, q), d, P.at_fh())) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, ew), hc)
  +hcn = kchain_pre(ns, F, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), hct)
  +hapn = kapart_pre(ns, F, d, hap)
  +hpan = kpast_pre(ns, F, d, hpa)
  %ew : {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{_}, a}, map}, by))))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{_}, a}, map}, by))))), d, P.at_fh())) == True{} : Bool}
  %ea : {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map}, by))))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map}, by))))), d, P.at_fh())) == True{} : Bool}
  %em : {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, _}, by))))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, _}, by))))), d, P.at_fh())) == True{} : Bool}
  %speta(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)) : {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, _)))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, _)))), d, P.at_fh())) == True{} : Bool}
  %heta(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))) : {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{_, SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))})))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.Sp{_, SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))})))), d, P.at_fh())) == True{} : Bool}
  sf2(ls, KMd.words(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))), KMd.vals(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))), SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)), d, dm, ns, F,
    full_go(ts, hd_era(ts), {==}, LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), LAT.fromT(U32, tm), d, 0, by, ns, hft, hd32, hcn, hl, hapn, hpan, hhd, LAT.mirror(U32, LAT.fromT(U32, t0)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))), hd32,
    mfull_go(ts, hd_era(ts), {==}, LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), LAT.fromT(U32, tm), dm, 0, by, hfmt, LAT.mirror(U32, LAT.fromT(U32, t0)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta)), LAT.mirror(U32, LAT.fromT(U32, tm))), hdm,
    ends_go(ls, ts, t0, ta, tm, d, dm, by, ns, hft, hd32, hfmt, hdm, hcn, hl, hapn, hpan, hhd, ht), hap, hpa,
    nf_go(ts, hd_era(ts), {==}, LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), LAT.fromT(U32, tm), d, 0, by, ns, F, hft, hd32, hct, hl, hap, hpa, hhd, LAT.mirror(U32, LAT.fromT(U32, t0)), LAT.mirror(V.Val, LAT.fromT(V.Val, ta))),
    LAT.mirror(U32, KMd.words(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)))), LAT.mirror(V.Val, KMd.vals(SM.heap(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by)))), LAT.mirror(U32, SM.map(S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, LAT.fromT(U32, tm)}, by))))

def Laws.splice_free(w, a, map, d, dm, ts, ls, by, ns, F, hf, hd32, hfm, hdm, hc, hl, hap, hpa, hhd, ht):
  sfree_go(w, a, map, d, dm, ts, ls, by, ns, F, hf, hd32, hfm, hdm, hc, hl, hap, hpa, hhd, ht, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))

# The map's depth (T.depth_for; cursor-laws.materializer.template.depth):
# below 32, and the size at most 2^depth for a size up to 2^31. Not
# claimed: that the depth is the least.

# the search's bound: fuel f past depth d ends at most f + d
def dgo_le(f: Nat, +fits: Bool, +n: U32, +d: Nat, +pw: U32, +t: Nat, +h: MN.le(Nat.add(f, d), t)) -> MN.le(T.depth_for.go(f, fits, n, d, pw), t):
  match f:
    case 0n:
      h
    case 1n+(+p):
      match fits:
        case True{}:
          MN.le_trans(d, Nat.add(1n+p, d), t, MN.le_add_left(d, 1n+p), h)
        case False{}:
          dgo_le(p, U32.is_le(n, (pw * 2 : U32)), n, 1n+d, (pw * 2 : U32), t,
            ME.subst(Nat, z => MN.le(z, t), Nat.add(1n+p, d), Nat.add(p, 1n+d), Equal.sym(Nat, Nat.add(p, 1n+d), 1n+Nat.add(p, d), MN.add_succ(p, d)), h))

def depth_lt(+n: U32) -> {Nat.is_lt(T.depth_for(31n, n, 0n), 32n) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(T.depth_for(31n, n, 0n), 32n), Nat.is_le(T.depth_for(31n, n, 0n), 31n), True{}, MN.lt_succ_iff(T.depth_for(31n, n, 0n), 31n),
    dgo_le(31n, U32.is_le(n, U32.from_nat(Nat.pow(2n, 0n))), n, 0n, U32.from_nat(Nat.pow(2n, 0n)), 31n, {==}))

# pw doubled f times, on words: the fuel's last power
def dbl(f: Nat, +pw: U32) -> U32:
  match f:
    case 0n:
      pw
    case 1n+(+p):
      dbl(p, (pw * 2 : U32))

# a remainder at most its argument
def mod_le(+x: Nat, +m: Nat) -> MN.le(Nat.mod(x, m), x):
  ME.subst(Nat, z => MN.le(Nat.mod(x, m), z), Nat.add(Nat.mul(Nat.div(x, m), m), Nat.mod(x, m)), x, WL.nat_div_mod(x, m), MN.le_add_left(Nat.mod(x, m), Nat.mul(Nat.div(x, m), m)))

# a doubled word at most twice its bound, whatever wraps
def dbl_le(+pw: U32, +d: Nat, +hpw: MN.le(U32.to_nat(pw), Nat.pow(2n, d))) -> MN.le(U32.to_nat((pw * 2 : U32)), Nat.pow(2n, 1n+d)):
  +X = Nat.mul(U32.to_nat(pw), U32.to_nat(2))
  +h1 = ME.subst(Nat, z => MN.le(z, X), Nat.mod(X, Nat.pow(2n, 32n)), U32.to_nat((pw * 2 : U32)), Equal.sym(Nat, U32.to_nat((pw * 2 : U32)), Nat.mod(X, Nat.pow(2n, 32n)), WL.to_nat_mul(pw, 2)), mod_le(X, Nat.pow(2n, 32n)))
  +h2 = MN.mul_le_mul_right(U32.to_nat(pw), Nat.pow(2n, d), U32.to_nat(2), hpw)
  +h3 = ME.subst(Nat, z => MN.le(X, z), Nat.mul(Nat.pow(2n, d), U32.to_nat(2)), Nat.pow(2n, 1n+d), MN.mul_comm(Nat.pow(2n, d), 2n), h2)
  MN.le_trans(U32.to_nat((pw * 2 : U32)), X, Nat.pow(2n, 1n+d), h1, h3)

def fit_of_le(+n: U32, +pw: U32, +d: Nat, +h: {U32.is_le(n, pw) == True{} : Bool}, +hpw: MN.le(U32.to_nat(pw), Nat.pow(2n, d))) -> MN.le(U32.to_nat(n), Nat.pow(2n, d)):
  MN.le_trans(U32.to_nat(n), U32.to_nat(pw), Nat.pow(2n, d),
    Equal.trans(Bool, Nat.is_le(U32.to_nat(n), U32.to_nat(pw)), U32.is_le(n, pw), True{}, Equal.sym(Bool, U32.is_le(n, pw), Nat.is_le(U32.to_nat(n), U32.to_nat(pw)), MU.u32_is_le_to_nat(n, pw)), h), hpw)

# the search's fit: n at most 2^d where it ends, the power pw bounding
# 2^d at each step, n at most the fuel's last power
def dgo_fit(f: Nat, +fits: Bool, +n: U32, +d: Nat, +pw: U32, +hfits: {fits == U32.is_le(n, pw) : Bool}, +hpw: MN.le(U32.to_nat(pw), Nat.pow(2n, d)),
  +hn: {U32.is_le(n, dbl(f, pw)) == True{} : Bool}) -> MN.le(U32.to_nat(n), Nat.pow(2n, T.depth_for.go(f, fits, n, d, pw))):
  match f:
    case 0n:
      fit_of_le(n, pw, d, hn, hpw)
    case 1n+(+p):
      match fits:
        case True{}:
          fit_of_le(n, pw, d, Equal.sym(Bool, True{}, U32.is_le(n, pw), hfits), hpw)
        case False{}:
          dgo_fit(p, U32.is_le(n, (pw * 2 : U32)), n, 1n+d, (pw * 2 : U32), {==}, dbl_le(pw, d, hpw), hn)

def depth_fit(+n: U32, +hn: {U32.is_le(n, 2147483648) == True{} : Bool}) -> MN.le(U32.to_nat(n), Nat.pow(2n, T.depth_for(31n, n, 0n))):
  dgo_fit(31n, U32.is_le(n, U32.from_nat(Nat.pow(2n, 0n))), n, 0n, U32.from_nat(Nat.pow(2n, 0n)), {==}, {==}, hn)

def Laws.map_depth(n, hn):
  MB.and_eq_true(Nat.is_lt(T.depth_for(31n, n, 0n), 32n), Nat.is_le(U32.to_nat(n), Nat.pow(2n, T.depth_for(31n, n, 0n))) && AD.full(U32, [0 : U32^T.depth_for(31n, n, 0n)], T.depth_for(31n, n, 0n)), depth_lt(n),
    MB.and_eq_true(Nat.is_le(U32.to_nat(n), Nat.pow(2n, T.depth_for(31n, n, 0n))), AD.full(U32, [0 : U32^T.depth_for(31n, n, 0n)], T.depth_for(31n, n, 0n)), depth_fit(n, hn), LA.new_full(U32, T.depth_for(31n, n, 0n), 0)))
