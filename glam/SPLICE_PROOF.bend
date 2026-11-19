# The splice's proofs (glam/SPLICE_LAWS.bend; cells-freeze.nested.host.splice).
# The splice's state threaded step by step, each heap restated in its
# parts by one lemma over a heap variable (heta) rather than one per
# operation; the spike's frame laws cited through spike/LAWS.bend.

import Base
import ./SPLICE_LAWS.bend as Laws
import ../spike/LAWS.bend as SL
import ../spike/PROOF.bend as SP
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/tpl.bend as T
import ../spike/rules.bend as R
import ../spike/net.bend as N
import ../spike/knet.bend as KN
import ../spike/kmodel.bend as KMd
import ./splice.bend as S
import ./splice_model.bend as SM
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import 0x8ae61ec3a6615abd35f196c07232ad28/string.bend as MS
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MN
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/LAWS.bend as LA
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/PROOF.bend as LAP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_base.bend as LAB
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

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
      P.err_if(KN.too_big(l), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)})
    case V.PLift{+i, +up, +amt}:
      P.err_if(KN.too_big(i) || U32.is_ge(amt, 2147483648), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)})
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
      KN.bare_hd(N.kcode(k))
    case V.PFan{+f}:
      KN.bare_hd(N.kcode(k))

def pl.p(pp: V.Pay, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>) -> U32:
  match pp:
    case V.PVal{+v}:
      pww(Pair.snd(P.H, P.PW, P.put(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, v)))
    case V.PLvl{+l}:
      0
    case V.PLift{+i, +up, +amt}:
      KN.lift_word(up, amt)
    case V.PNone{}:
      0
    case V.PFan{+f}:
      0

def pre(t: T.TNode, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +by: U32) -> P.H:
  match t:
    case T.TF{+k, +site, +lvl}:
      P.err_if(KN.fan_too_big(U32.is_eq(V.raise_lvl(by, lvl), V.nolvl()), site, V.raise_lvl(by, lvl)), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)})
    case T.TN{+k, +p}:
      pre.p(V.raise_pay(by, p), t0, ta)

def hdf(t: T.TNode, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +by: U32) -> U32:
  match t:
    case T.TF{+k, +site, +lvl}:
      KN.fan_hd(N.kcode(k), site, V.raise_lvl(by, lvl))
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
      Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.err_if(KN.too_big(l), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}), ix)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, ix)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ix)), SL.err_keeps(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), d, KN.too_big(l), ix, hft, hd32, MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(ix, d))), KMd.off.words(Nil{}, d, ix), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(ix, d))), KMd.off.words(KMd.tab_words(), d, ix), hi), {==})), SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), ix))
    case V.PLift{+i2, +up, +amt}:
      Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.err_if(KN.too_big(i2) || U32.is_ge(amt, 2147483648), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}), ix)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, ix)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ix)), SL.err_keeps(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), d, KN.too_big(i2) || U32.is_ge(amt, 2147483648), ix, hft, hd32, MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(ix, d))), KMd.off.words(Nil{}, d, ix), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(ix, d))), KMd.off.words(KMd.tab_words(), d, ix), hi), {==})), SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), ix))
    case V.PNone{}:
      SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), ix)
    case V.PFan{+f}:
      SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), ix)

def pre_rd(t: T.TNode, +by: U32, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +ix: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {KMd.off.words(KMd.hdr_words(), d, ix) == True{} : Bool}) ->
  {Pair.snd(P.H, U32, P.rd(pre(t, t0, ta, by), ix)) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ix)) : U32}:
  match t:
    case T.TF{+k, +site, +lvl}:
      Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.err_if(KN.fan_too_big(U32.is_eq(V.raise_lvl(by, lvl), V.nolvl()), site, V.raise_lvl(by, lvl)), P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}), ix)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, ix)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), ix)), SL.err_keeps(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), d, KN.fan_too_big(U32.is_eq(V.raise_lvl(by, lvl), V.nolvl()), site, V.raise_lvl(by, lvl)), ix, hft, hd32, MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(ix, d))), KMd.off.words(Nil{}, d, ix), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot(P.at_errs(), d), AD.slot(ix, d))), KMd.off.words(KMd.tab_words(), d, ix), hi), {==})), SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), ix))
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
      err_full(KN.too_big(l), t0, LAT.fromT(V.Val, ta), d, hft)
    case V.PLift{+i2, +up, +amt}:
      err_full(KN.too_big(i2) || U32.is_ge(amt, 2147483648), t0, LAT.fromT(V.Val, ta), d, hft)
    case V.PNone{}:
      hft
    case V.PFan{+f}:
      hft

def pre_full(t: T.TNode, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +by: U32, +d: Nat, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}) ->
  {AD.full(U32, KMd.words(pre(t, t0, ta, by)), d) == True{} : Bool}:
  match t:
    case T.TF{+k, +site, +lvl}:
      err_full(KN.fan_too_big(U32.is_eq(V.raise_lvl(by, lvl), V.nolvl()), site, V.raise_lvl(by, lvl)), t0, LAT.fromT(V.Val, ta), d, hft)
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

# the node pass, by induction on the template's nodes, the free list's
# nodes beside them, each step's facts above
def nodes_go(ts: List<&2, T.TNode>, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +i: U32, +by: U32, ns: List<&2, U32>, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool},
  hl: {List.length(&2, T.TNode, ts) == List.length(&2, U32, ns) : Nat}, +hap: {KMd.apart(ns, d) == True{} : Bool}, +hpa: {KMd.past(ns, d) == True{} : Bool},
  +hj: {KMd.nodes.off(ns, d, j) == True{} : Bool}, +hjh: {KMd.off.words(KMd.hdr_all(), d, j) == True{} : Bool}, +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(ts, i, S.Sp{P.H{KM.MG{w}, a}, map}, by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +rt}:
      match ns:
        case Nil{}:
          Empty.absurd({Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{w}, a}, map}, by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}, MB.false_ne_true()(Equal.sym(Bool, True{}, False{}, ME.subst(Nat, q => {Nat.is_eq(q, 0n) == False{} : Bool}, List.length(&2, T.TNode, Con{t, rt}), 0n, hl, {==}))))
        case Con{+n, +rn}:
          (+t0, +e) = mw
          (+ta, +ea) = ma
          +hft = LAP.full_t(U32, w, t0, d, e, hf)
          +hct = LAB.subst(Array<U32>, q => {KMd.chain(Con{n, rn}, AD.view(U32, q), d, KMd.word(AD.view(U32, q), d, P.at_fh())) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e), hc)
          +hne = ME.subst(U32, x => {U32.is_eq(x, 0) == False{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), word_get(LAT.fromT(U32, t0), d, P.at_fh(), hft, hd32), MB.eq_false_of_not_eq_true(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0), MB.eq_true_of_and_left(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct)))
          +hidx = ME.subst(U32, x => {KMd.at_idx(x) == n : U32}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), word_get(LAT.fromT(U32, t0), d, P.at_fh(), hft, hd32), MS.u32_eq_of_is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n, MB.eq_true_of_and_left(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct))))
          %e : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{_}, a}, map}, by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
          %ea : {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(Con{t, rt}, i, S.Sp{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map}, by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, _}, j)) : U32}
          %Equal.sym(S.Sp, S.sp.put(S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), map, i), S.Sp{Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)), Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, spput(S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by), map, i)) :
            {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(rt, (i + 1 : U32), _, by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)) : U32}
          %heta(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))) :
            {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.Sp{_, Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)) : U32}
          ME.trans3(U32, Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(rt, (i + 1 : U32), S.Sp{P.H{KM.MG{KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, by)), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)), nodes_go(rt, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), Array.set(U32, map, i, Pair.snd(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), d, (i + 1 : U32), by, rn, j, sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), hd32, ME.subst(U32, x => {KMd.chain(rn, AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, x) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), ME.trans3(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), word_get(LAT.fromT(U32, t0), d, (n + 1 : U32), hft, hd32), Equal.sym(U32, Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (n + 1 : U32))), sn(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd, MB.eq_true_of_and_left(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(rn, d), hpa))), Equal.sym(U32, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), P.at_fh())), word_get(KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), d, P.at_fh(), sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), hd32))), ctr(rn, t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)), sfull(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd), MB.eq_true_of_and_left(KMd.apart.n(n, rn, d), KMd.apart(rn, d), hap), MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(rn, d), hpa), MB.eq_true_of_and_right(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32))), MB.eq_true_of_and_right(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), n), KMd.chain(rn, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (n + 1 : U32)))), hct)))), npred_eq(List.length(&2, T.TNode, rt), List.length(&2, U32, rn), hl),
          MB.eq_true_of_and_right(KMd.apart.n(n, rn, d), KMd.apart(rn, d), hap), MB.eq_true_of_and_right(KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), KMd.past(rn, d), hpa), MB.eq_true_of_and_right(KMd.off.words(KMd.nw(n), d, j), KMd.nodes.off(rn, d, j), hj), hjh, hhd,
          LAT.mirror(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))), LAT.mirror(V.Val, KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))))), Equal.trans(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by)))}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), SP.rd_get(KMd.words(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), KMd.vals(Pair.fst(P.H, U32, S.sp.node(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, 0, t, by))), j), sf(t, t0, ta, by, d, n, hft, hd32, hne, hidx, hhd, j, MB.eq_true_of_and_left(KMd.off.words(KMd.nw(n), d, j), KMd.nodes.off(rn, d, j), hj), hjh)), Equal.sym(U32, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), SP.rd_get(LAT.fromT(U32, t0), LAT.fromT(V.Val, ta), j)))

def Laws.nodes_keeps(w, a, map, d, ts, i, by, ns, j, hf, hd32, hc, hl, hap, hpa, hj, hjh, hhd):
  nodes_go(ts, w, a, map, d, i, by, ns, j, hf, hd32, hc, hl, hap, hpa, hj, hjh, hhd, LAT.mirror(U32, w), LAT.mirror(V.Val, a))
