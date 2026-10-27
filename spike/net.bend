import Base
import ./val.bend as V
import ./store.bend as S
import ./rules.bend as R

# The reducer: interaction-net rewriting over the store, interpreting the
# rules of rules.bend. A node's header word holds its kind; words 1-3 link
# its ports 0-2. Reduction pops active pairs (two principal ports linked)
# from a queue until none is left or fuel runs out.

# Kinds in headers
# ================

def kcode(k: R.NodeKind) -> U32:
  match k:
    case R.KFree{}:
      0
    case R.KFn{}:
      1
    case R.KAp{}:
      2
    case R.KCopy{}:
      3
    case R.KMerge{}:
      4
    case R.KData{}:
      5
    case R.KEraN{}:
      6
    case R.KEraP{}:
      7
    case R.KRoot{}:
      8
    case R.KCall{}:
      9
    case R.KLift{}:
      10
    case R.KLiftC{}:
      11

def kof(c: U32) -> R.NodeKind:
  match c:
    case 1:
      R.KFn{}
    case 2:
      R.KAp{}
    case 3:
      R.KCopy{}
    case 4:
      R.KMerge{}
    case 5:
      R.KData{}
    case 6:
      R.KEraN{}
    case 7:
      R.KEraP{}
    case 8:
      R.KRoot{}
    case 9:
      R.KCall{}
    case 10:
      R.KLift{}
    case 11:
      R.KLiftC{}
    case _:
      R.KFree{}

# The reducer's state
# ===================

type Redex is Data:
  Redex{+a: U32, +b: U32}

# the store, the active pairs, and counts: interactions, errors (rule
# violations, loops it cannot resolve), and nodes made, whose count names
# each node in its header's upper 28 bits for tracing
type Q is Type:
  Q{st: S.Store, rq: List<&2, Redex>, +itrs: U32, +errs: U32, +ser: U32}

def q_new() -> Q:
  Q{S.st_new(), Nil{}, 0, 0, 0}

def q_err(q: Q) -> Q:
  match q:
    case Q{st, rq, +itrs, +errs, +ser}:
      Q{st, rq, itrs, (errs + 1 : U32), ser}

def q_word.fin(r: S.Store & U32, rq: List<&2, Redex>, +itrs: U32, +errs: U32, +ser: U32) -> Q & U32:
  (st, +x) = r
  (Q{st, rq, itrs, errs, ser}, x)

def q_word(q: Q, +r: U32, +k: U32) -> Q & U32:
  match q:
    case Q{st, rq, +itrs, +errs, +ser}:
      q_word.fin(S.st_get(st, r, k), rq, itrs, errs, ser)

def q_pay.fin(r: S.Store & V.Pay, rq: List<&2, Redex>, +itrs: U32, +errs: U32, +ser: U32) -> Q & V.Pay:
  (st, p) = r
  (Q{st, rq, itrs, errs, ser}, p)

def q_pay(q: Q, +r: U32) -> Q & V.Pay:
  match q:
    case Q{st, rq, +itrs, +errs, +ser}:
      q_pay.fin(S.st_pay(st, r), rq, itrs, errs, ser)

def both0(+x: U32, +y: U32) -> Bool:
  U32.is_eq(S.ref_port(x), 0) && U32.is_eq(S.ref_port(y), 0)

def push_if(b: Bool, +x: U32, +y: U32, rq: List<&2, Redex>) -> List<&2, Redex>:
  match b:
    case True{}:
      Redex{x, y} <> rq
    case False{}:
      rq

# wire port x to port y; two principals make an active pair
def link(q: Q, +x: U32, +y: U32) -> Q:
  match q:
    case Q{st, rq, +itrs, +errs, +ser}:
      st1 = S.st_set(st, x, (S.ref_port(x) + 1 : U32), y)
      st2 = S.st_set(st1, y, (S.ref_port(y) + 1 : U32), x)
      Q{st2, push_if(both0(x, y), x, y, rq), itrs, errs, ser}

def node.fin(r: S.Store & U32, +k: U32, p: V.Pay, rq: List<&2, Redex>, +itrs: U32, +errs: U32, +ser: U32) -> Q & U32:
  (st, +ref) = r
  (Q{S.st_set_pay(S.st_set(st, ref, 0, (k .|. (ser << 4n : U32) : U32)), ref, p), rq, itrs, errs, (ser + 1 : U32)}, ref)

# a new node of kind k with payload p: its port 0
def node(q: Q, k: R.NodeKind, p: V.Pay) -> Q & U32:
  match q:
    case Q{st, rq, +itrs, +errs, +ser}:
      node.fin(S.st_alloc(st), kcode(k), p, rq, itrs, errs, ser)

def free(q: Q, +r: U32) -> Q:
  match q:
    case Q{st, rq, +itrs, +errs, +ser}:
      Q{S.st_free(st, r), rq, itrs, errs, ser}

# Applying a rule
# ===============

# the peers of the redex's auxiliary ports: A's ports 1, 2, then B's
type Ext is Data:
  Ext4{+e0: U32, +e1: U32, +e2: U32, +e3: U32}

def ext_at(+x: Ext, i: Nat) -> U32:
  match x:
    case Ext4{+e0, +e1, +e2, +e3}:
      match i:
        case 0n:
          e0
        case 1n:
          e1
        case 2n:
          e2
        case _:
          e3

def node_of(+r: U32) -> U32:
  (r .&. 4294967292 : U32)

# an external peer that is itself an auxiliary port of the redex stands
# for another external: index 0, 1 for A's ports 1, 2; 2, 3 for B's
def partner.b(isa: Bool, isb: Bool, +port: U32) -> Maybe<&2, Nat>:
  match isa isb:
    case True{} _:
      Some{U32.to_nat((port - 1 : U32))}
    case False{} True{}:
      Some{U32.to_nat((port + 1 : U32))}
    case False{} False{}:
      None{}

def partner(+e: U32, +a: U32, +b: U32) -> Maybe<&2, Nat>:
  partner.b(U32.is_eq(node_of(e), node_of(a)) && U32.is_ne(e, S.nil()),
    U32.is_eq(node_of(e), node_of(b)) && U32.is_ne(e, S.nil()), S.ref_port(e))

def nth(xs: List<&2, U32>, n: Nat) -> U32:
  match xs n:
    case Nil{} _:
      S.nil()
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+i:
      nth(t, i)

# what an end means once the new nodes exist
def resolve(+x: Ext, +refs: List<&2, U32>, e: R.End) -> U32:
  match e:
    case R.Ext{i}:
      ext_at(x, i)
    case R.New{j, p}:
      S.ref_at(nth(refs, j), U32.from_nat(p))

def fan_of(p: V.Pay) -> V.FanId:
  match p:
    case V.PFan{f}:
      f
    case _:
      V.fan_new(0, 0, 0)

def pay_val(p: V.Pay) -> V.Val:
  match p:
    case V.PVal{v}:
      v
    case _:
      V.VUnit{}

def src_pay(s: R.Src, +pa: V.Pay, +pb: V.Pay) -> V.Pay:
  match s:
    case R.SNone{}:
      V.PNone{}
    case R.SPayA{}:
      pa
    case R.SPayB{}:
      pb
    case R.SApply{}:
      V.PVal{V.apply_fn(pay_val(pa), pay_val(pb))}
    case R.SLiftA{}:
      V.lift_pay(pb, pa)
    case R.SLiftB{}:
      V.lift_pay(pa, pb)
    case R.SFanA{}:
      pa
    case R.SFanB{}:
      pb

type Made is Type:
  Made{q: Q, refs: List<&2, U32>}

def made.add(r: Q & U32, refs: List<&2, U32>) -> Made:
  (q, +ref) = r
  Made{q, List.append(&2, U32, refs, [ref])}

def made.step(m: Made, sp: R.Spec, +pa: V.Pay, +pb: V.Pay) -> Made:
  match m:
    case Made{q, refs}:
      match sp:
        case R.Spec{k, src}:
          made.add(node(q, k, src_pay(src, pa, pb)), refs)

# allocate the rule's new nodes, in order
def make(xs: List<&2, R.Spec>, +pa: V.Pay, +pb: V.Pay, m: Made) -> Made:
  match xs:
    case Nil{}:
      m
    case Con{sp, t}:
      make(t, pa, pb, made.step(m, sp, pa, pb))

def is_ext(e: R.End) -> Bool:
  match e:
    case R.Ext{i}:
      True{}
    case R.New{j, p}:
      False{}

def ext_index(e: R.End) -> Nat:
  match e:
    case R.Ext{i}:
      i
    case R.New{j, p}:
      9n

def end_internal(+x: Ext, +a: U32, +b: U32, e: R.End) -> Bool:
  match e:
    case R.Ext{i}:
      Maybe.is_some(&2, Nat, partner(ext_at(x, i), a, b))
    case R.New{j, p}:
      False{}

# the other end of the link holding Ext i
def other1(onx: Bool, ony: Bool, x: R.End, y: R.End) -> Maybe<&2, R.End>:
  match onx ony:
    case True{} _:
      Some{y}
    case False{} True{}:
      Some{x}
    case False{} False{}:
      None{}

def first(a: Maybe<&2, R.End>, b: Maybe<&2, R.End>) -> Maybe<&2, R.End>:
  match a:
    case Some{x}:
      Some{x}
    case None{}:
      b

def other(ls: List<&2, R.Link>, +i: Nat) -> Maybe<&2, R.End>:
  match ls:
    case Nil{}:
      None{}
    case Con{R.Link{+x, +y}, t}:
      first(other1(R.end_eq(x, R.Ext{i}), R.end_eq(y, R.Ext{i}), x, y), other(t, i))

def link_if(b: Bool, q: Q, +u: U32, +v: U32) -> Q:
  match b:
    case True{}:
      link(q, u, v)
    case False{}:
      q

# link every rule link whose ends are both outside the redex
def link_plain(ls: List<&2, R.Link>, +x: Ext, +refs: List<&2, U32>, +a: U32, +b: U32, q: Q) -> Q:
  match ls:
    case Nil{}:
      q
    case Con{R.Link{+u, +v}, t}:
      link_plain(t, x, refs, a, b,
        link_if(Bool.not(end_internal(x, a, b, u) || end_internal(x, a, b, v)), q, resolve(x, refs, u), resolve(x, refs, v)))

def pair_link(bad: Bool, +u: R.End, +v: R.End, +x: Ext, +refs: List<&2, U32>, q: Q) -> Q:
  match bad:
    case True{}:
      q_err(q)
    case False{}:
      link(q, resolve(x, refs, u), resolve(x, refs, v))

def pair_ends(oi: Maybe<&2, R.End>, oj: Maybe<&2, R.End>, +x: Ext, +refs: List<&2, U32>, +a: U32, +b: U32, q: Q) -> Q:
  match oi oj:
    case Some{+u} Some{+v}:
      pair_link(end_internal(x, a, b, u) || end_internal(x, a, b, v), u, v, x, refs, q)
    case _ _:
      q_err(q)

def pair_go(lt: Bool, +i: Nat, +j: Nat, +ls: List<&2, R.Link>, +x: Ext, +refs: List<&2, U32>, +a: U32, +b: U32, q: Q) -> Q:
  match lt:
    case True{}:
      pair_ends(other(ls, i), other(ls, j), x, refs, a, b, q)
    case False{}:
      q

# Ext i stands for Ext j: whatever the rule links to the one is joined to
# whatever it links to the other (each pair once, from its lower index)
def pair_at(pt: Maybe<&2, Nat>, +i: Nat, +ls: List<&2, R.Link>, +x: Ext, +refs: List<&2, U32>, +a: U32, +b: U32, q: Q) -> Q:
  match pt:
    case None{}:
      q
    case Some{+j}:
      pair_go(Nat.is_lt(i, j), i, j, ls, x, refs, a, b, q)

def link_pairs(n: Nat, +i: Nat, +ls: List<&2, R.Link>, +x: Ext, +refs: List<&2, U32>, +a: U32, +b: U32, q: Q) -> Q:
  match n:
    case 0n:
      q
    case 1n+p:
      link_pairs(p, 1n+i, ls, x, refs, a, b, pair_at(partner(ext_at(x, i), a, b), i, ls, x, refs, a, b, q))

# Fusing controls
# ---------------
#
# After a rewrite, a control that may now sit right behind another facing
# the same way merges with it, when V.compose finds one control acting as
# both. Only two things make controls adjacent: a rule making a control,
# and a rule joining two of the redex's external peers (beta's crossed
# join, a fan join, cancelling controls); so those are the nodes tried. The node freed is the
# one whose principal faces the other's auxiliary, which cannot be in an
# active pair; a pair that cancels is left alone if the survivor's
# principal is linked to a principal (an active pair may be queued).

def q_set_pay(q: Q, +r: U32, p: V.Pay) -> Q:
  match q:
    case Q{st, rq, +itrs, +errs, +ser}:
      Q{S.st_set_pay(st, r, p), rq, itrs, errs, ser}

# Lifts: p's out feeds l's in; values cross p first. p stays, l goes.
def fl.id.go(active: Bool, q: Q, +p: U32, +l: U32, +i: U32, +o: U32) -> Q:
  match active:
    case True{}:
      q
    case False{}:
      free(free(link(q, i, o), p), l)

def fl.id(r: Q & U32, +p: U32, +l: U32, +o: U32) -> Q:
  (q, +i) = r
  fl.id.go(U32.is_eq(S.ref_port(i), 0), q, p, l, i, o)

def fl.fuse(f: V.Fuse, q: Q, +p: U32, +l: U32, +o: U32) -> Q:
  match f:
    case V.FNo{}:
      q
    case V.FId{}:
      fl.id(q_word(q, p, 1), p, l, o)
    case V.FTo{pay}:
      free(link(q_set_pay(q, p, pay), S.ref_at(p, 1), o), l)

def fl.o(r: Q & U32, +p: U32, +l: U32, pp: V.Pay, pl: V.Pay) -> Q:
  (q, +o) = r
  fl.fuse(V.compose(pp, pl), q, p, l, o)

def fl.pl(r: Q & V.Pay, +p: U32, +l: U32, pp: V.Pay) -> Q:
  (q, pl) = r
  fl.o(q_word(q, l, 2), p, l, pp, pl)

def fl.pp(r: Q & V.Pay, +p: U32, +l: U32) -> Q:
  (q, pp) = r
  fl.pl(q_pay(q, l), p, l, pp)

def fuse_lifts(q: Q, +p: U32, +l: U32) -> Q:
  fl.pp(q_pay(q, p), p, l)

# LiftCs: a's out feeds b's in; consumers cross b first. b stays, a goes.
def fc.id.go(active: Bool, q: Q, +a: U32, +b: U32, +i: U32, +o: U32) -> Q:
  match active:
    case True{}:
      q
    case False{}:
      free(free(link(q, i, o), a), b)

def fc.id(r: Q & U32, +a: U32, +b: U32, +i: U32) -> Q:
  (q, +o) = r
  fc.id.go(U32.is_eq(S.ref_port(o), 0), q, a, b, i, o)

def fc.fuse(f: V.Fuse, q: Q, +a: U32, +b: U32, +i: U32) -> Q:
  match f:
    case V.FNo{}:
      q
    case V.FId{}:
      fc.id(q_word(q, b, 1), a, b, i)
    case V.FTo{pay}:
      free(link(q_set_pay(q, b, pay), i, S.ref_at(b, 1)), a)

def fc.i(r: Q & U32, +a: U32, +b: U32, pa: V.Pay, pb: V.Pay) -> Q:
  (q, +i) = r
  fc.fuse(V.compose(pb, pa), q, a, b, i)

def fc.pb(r: Q & V.Pay, +a: U32, +b: U32, pa: V.Pay) -> Q:
  (q, pb) = r
  fc.i(q_word(q, a, 2), a, b, pa, pb)

def fc.pa(r: Q & V.Pay, +a: U32, +b: U32) -> Q:
  (q, pa) = r
  fc.pb(q_pay(q, b), a, b, pa)

def fuse_liftcs(q: Q, +a: U32, +b: U32) -> Q:
  fc.pa(q_pay(q, a), a, b)

# r, a control of kind code `want`, against the peer of its word wk, when
# that is port `port` of another control of the same kind; `up` says the
# peer is the one behind
def ts.fuse(+want: U32, +up: Bool, q: Q, +r: U32, +x: U32) -> Q:
  match want up:
    case 10 True{}:
      fuse_lifts(q, node_of(x), r)
    case 10 False{}:
      fuse_lifts(q, r, node_of(x))
    case _ True{}:
      fuse_liftcs(q, node_of(x), r)
    case _ False{}:
      fuse_liftcs(q, r, node_of(x))

def ts.go(ok: Bool, +want: U32, +up: Bool, q: Q, +r: U32, +x: U32) -> Q:
  match ok:
    case True{}:
      ts.fuse(want, up, q, r, x)
    case False{}:
      q

def ts.hx(rr: Q & U32, +want: U32, +port: U32, +up: Bool, +r: U32, +x: U32) -> Q:
  (q, +hx) = rr
  ts.go(U32.is_eq((hx .&. 15 : U32), want) && U32.is_eq(S.ref_port(x), port) && U32.is_ne(node_of(x), node_of(r)), want, up, q, r, x)

def ts.x.go(nil: Bool, q: Q, +want: U32, +port: U32, +up: Bool, +r: U32, +x: U32) -> Q:
  match nil:
    case True{}:
      q
    case False{}:
      ts.hx(q_word(q, x, 0), want, port, up, r, x)

def ts.x(rr: Q & U32, +want: U32, +port: U32, +up: Bool, +r: U32) -> Q:
  (q, +x) = rr
  ts.x.go(U32.is_eq(x, S.nil()), q, want, port, up, r, x)

def ts.h.go(live: Bool, q: Q, +want: U32, +wk: U32, +port: U32, +up: Bool, +r: U32) -> Q:
  match live:
    case True{}:
      ts.x(q_word(q, r, wk), want, port, up, r)
    case False{}:
      q

def ts.h(rr: Q & U32, +want: U32, +wk: U32, +port: U32, +up: Bool, +r: U32) -> Q:
  (q, +h) = rr
  ts.h.go(U32.is_eq((h .&. 15 : U32), want), q, want, wk, port, up, r)

def try_side(q: Q, +r: U32, +want: U32, +wk: U32, +port: U32, +up: Bool) -> Q:
  ts.h(q_word(q, r, 0), want, wk, port, up, r)

def fo.k(+k: U32, q: Q, +r: U32) -> Q:
  match k:
    case 10:
      try_side(try_side(q, r, 10, 1, 1, True{}), r, 10, 2, 0, False{})
    case 11:
      try_side(try_side(q, r, 11, 2, 0, True{}), r, 11, 1, 1, False{})
    case _:
      q

def fo.h(rr: Q & U32, +r: U32) -> Q:
  (q, +h) = rr
  fo.k((h .&. 15 : U32), q, r)

def fuse_one(q: Q, +r: U32) -> Q:
  fo.h(q_word(q, r, 0), r)

def fuse_all(rs: List<&2, U32>, q: Q) -> Q:
  match rs:
    case Nil{}:
      q
    case Con{+r, t}:
      fuse_all(t, fuse_one(q, r))

def ext_node.go(skip: Bool, +e: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match skip:
    case True{}:
      rest
    case False{}:
      node_of(e) <> rest

def ext_node(+e: U32, +a: U32, +b: U32, rest: List<&2, U32>) -> List<&2, U32>:
  ext_node.go(U32.is_eq(e, S.nil()) || Maybe.is_some(&2, Nat, partner(e, a, b)), e, rest)

# the redex's external peers' nodes, those outside it
def ext_nodes(+x: Ext, +a: U32, +b: U32) -> List<&2, U32>:
  match x:
    case Ext4{+e0, +e1, +e2, +e3}:
      ext_node(e0, a, b, ext_node(e1, a, b, ext_node(e2, a, b, ext_node(e3, a, b, Nil{}))))

def is_ctl(k: R.NodeKind) -> Bool:
  match k:
    case R.KLift{}:
      True{}
    case R.KLiftC{}:
      True{}
    case _:
      False{}

def keep_if(b: Bool, +r: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match b:
    case True{}:
      r <> rest
    case False{}:
      rest

# the new nodes that are controls
def ctl_refs(xs: List<&2, R.Spec>, rs: List<&2, U32>) -> List<&2, U32>:
  match xs rs:
    case Con{R.Spec{k, s}, xt} Con{+r, rt}:
      keep_if(is_ctl(k), r, ctl_refs(xt, rt))
    case _ _:
      Nil{}

def lx.go(both: Bool, +x: Ext, +a: U32, +b: U32, +u: R.End, +v: R.End, rest: List<&2, U32>) -> List<&2, U32>:
  match both:
    case True{}:
      ext_node(ext_at(x, ext_index(u)), a, b, ext_node(ext_at(x, ext_index(v)), a, b, rest))
    case False{}:
      rest

# the external peers a rule joins to each other
def link_ext_nodes(ls: List<&2, R.Link>, +x: Ext, +a: U32, +b: U32) -> List<&2, U32>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{R.Link{+u, +v}, t}:
      lx.go(is_ext(u) && is_ext(v), x, a, b, u, v, link_ext_nodes(t, x, a, b))

def any_partner(+x: Ext, +a: U32, +b: U32) -> Bool:
  match x:
    case Ext4{+e0, +e1, +e2, +e3}:
      Maybe.is_some(&2, Nat, partner(e0, a, b)) || Maybe.is_some(&2, Nat, partner(e1, a, b)) ||
        Maybe.is_some(&2, Nat, partner(e2, a, b)) || Maybe.is_some(&2, Nat, partner(e3, a, b))

def all_if(b: Bool, +x: Ext, +a: U32, +b2: U32) -> List<&2, U32>:
  match b:
    case True{}:
      ext_nodes(x, a, b2)
    case False{}:
      Nil{}

# the nodes to try fusing after a rewrite: its new controls, the peers it
# joins, and, when the redex's own ports were joined through it, every
# external peer
def fuse_tried(+xs: List<&2, R.Spec>, +refs: List<&2, U32>, +ls: List<&2, R.Link>, +x: Ext, +a: U32, +b: U32) -> List<&2, U32>:
  List.append(&2, U32, ctl_refs(xs, refs),
    List.append(&2, U32, link_ext_nodes(ls, x, a, b), all_if(any_partner(x, a, b), x, a, b)))

def wire.made(m: Made, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +x: Ext, +a: U32, +b: U32) -> Q:
  match m:
    case Made{q, +refs}:
      fuse_all(fuse_tried(xs, refs, ls, x, a, b),
        link_pairs(4n, 0n, ls, x, refs, a, b, link_plain(ls, x, refs, a, b, q)))

# replace the redex a >< b by the rule's nodes and links
def wire(q: Q, +a: U32, +b: U32, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +x: Ext, +pa: V.Pay, +pb: V.Pay) -> Q:
  wire.made(make(xs, pa, pb, Made{free(free(q, a), b), Nil{}}), xs, ls, x, a, b)

# Interaction
# ===========

# a node's header and the links of its ports 1 and 2
type Node3 is Data:
  N3{+h: U32, +l1: U32, +l2: U32}

def rd3.c(r: Q & U32, +h: U32, +l1: U32) -> Q & Node3:
  (q, +l2) = r
  (q, N3{h, l1, l2})

def rd3.b(r: Q & U32, +h: U32, +ref: U32) -> Q & Node3:
  (q, +l1) = r
  rd3.c(q_word(q, ref, 3), h, l1)

def rd3.a(r: Q & U32, +ref: U32) -> Q & Node3:
  (q, +h) = r
  rd3.b(q_word(q, ref, 2), h, ref)

def rd3(q: Q, +ref: U32) -> Q & Node3:
  rd3.a(q_word(q, ref, 0), ref)

def n3_kind(n: Node3) -> R.NodeKind:
  match n:
    case N3{+h, l1, l2}:
      kof((h .&. 15 : U32))

def aux_or_nil(b: Bool, +l: U32) -> U32:
  match b:
    case True{}:
      l
    case False{}:
      S.nil()

def ext_of(+na: Node3, +nb: Node3) -> Ext:
  match na nb:
    case N3{h1, +a1, +a2} N3{h2, +b1, +b2}:
      Ext4{aux_or_nil(Nat.is_lt(1n, R.arity(n3_kind(na))), a1), aux_or_nil(Nat.is_lt(2n, R.arity(n3_kind(na))), a2),
        aux_or_nil(Nat.is_lt(1n, R.arity(n3_kind(nb))), b1), aux_or_nil(Nat.is_lt(2n, R.arity(n3_kind(nb))), b2)}

def is_builtin(p: V.Pay) -> Bool:
  match p:
    case V.PVal{v}:
      match v:
        case V.VFun{+op, +need, args}:
          True{}
        case _:
          False{}
    case _:
      False{}

# the payload test a rule takes (R.rule)
def rule_test(ka: R.NodeKind, kb: R.NodeKind, +pa: V.Pay, +pb: V.Pay) -> Bool:
  match ka kb:
    case R.KCopy{} R.KMerge{}:
      V.fan_eq(fan_of(pa), fan_of(pb))
    case R.KAp{} R.KData{}:
      is_builtin(pb)
    case R.KAp{} R.KFn{}:
      V.lvl_eq(pa, pb)
    case R.KLift{} R.KLiftC{}:
      V.ctl_eq(pa, pb)
    case _ _:
      False{}

# Level checks: assertions counted as errors, the rewrite proceeding
# (docs/plans/NetPairing_2026-10-26.md, "Compared with the earlier
# discussion"). A copy only copies boxes, so it meets a function only at
# a deeper level; two fans meeting at one level are residuals of one
# duplication, so their sites and instantiations agree. Fans without a
# level (V.nolvl) are not checked.

def fan_lvl(f: V.FanId) -> U32:
  match f:
    case V.FanId{+site, +inst, +lvl}:
      lvl

def fan_si_eq(a: V.FanId, b: V.FanId) -> Bool:
  match a b:
    case V.FanId{+s1, +i1, +l1} V.FanId{+s2, +i2, +l2}:
      U32.is_eq(s1, s2) && U32.is_eq(i1, i2)

def lvl_known(+l: U32) -> Bool:
  U32.is_ne(l, V.nolvl())

def fn_lvl_known(p: V.Pay) -> Bool:
  match p:
    case V.PLvl{+n}:
      True{}
    case _:
      False{}

def pay_level(p: V.Pay) -> U32:
  match p:
    case V.PLvl{+n}:
      n
    case V.PFan{f}:
      fan_lvl(f)
    case V.PLift{+n, +up, +by}:
      n
    case _:
      0

def lift_wraps(c: V.Pay, +j: U32) -> Bool:
  match c:
    case V.PLift{+n, +up, +by}:
      up && U32.is_gt(j, n) && U32.is_lt((j + by : U32), j)
    case _:
      False{}

# a control raising a level, or another control's index, past the top of
# U32 would wrap it: a fail-stop in waiting, so it counts as an error
def wraps(ka: R.NodeKind, kb: R.NodeKind, +pa: V.Pay, +pb: V.Pay) -> Bool:
  match ka kb:
    case R.KLift{} _:
      lift_wraps(pa, pay_level(pb))
    case _ R.KLiftC{}:
      lift_wraps(pb, pay_level(pa)) || lift_wraps(pa, pay_level(pb))
    case _ _:
      False{}

def violation.lv(ka: R.NodeKind, kb: R.NodeKind, +pa: V.Pay, +pb: V.Pay) -> Bool:
  match ka kb:
    case R.KCopy{} R.KFn{}:
      lvl_known(fan_lvl(fan_of(pa))) && fn_lvl_known(pb) && U32.is_ge(fan_lvl(fan_of(pa)), V.pay_lvl(pb))
    case R.KCopy{} R.KMerge{}:
      lvl_known(fan_lvl(fan_of(pa))) && U32.is_eq(fan_lvl(fan_of(pa)), fan_lvl(fan_of(pb))) &&
        Bool.not(fan_si_eq(fan_of(pa), fan_of(pb)))
    case _ _:
      False{}

def violation(+ka: R.NodeKind, +kb: R.NodeKind, +pa: V.Pay, +pb: V.Pay) -> Bool:
  wraps(ka, kb, pa, pb) || violation.lv(ka, kb, pa, pb)

def err_if(bad: Bool, q: Q) -> Q:
  match bad:
    case True{}:
      q_err(q)
    case False{}:
      q

def is_root(k: R.NodeKind) -> Bool:
  match k:
    case R.KRoot{}:
      True{}
    case _:
      False{}

def stuck(root: Bool, q: Q) -> Q:
  match root:
    case True{}:
      q
    case False{}:
      q_err(q)

def apply(r: R.Rule, q: Q, +a: U32, +b: U32, +ka: R.NodeKind, +x: Ext, +pa: V.Pay, +pb: V.Pay) -> Q:
  match r:
    case R.RWire{xs, ls}:
      wire(q, a, b, xs, ls, x, pa, pb)
    case R.RStuck{}:
      stuck(is_root(ka), q)

def interact.pays(r: Q & V.Pay, +pa: V.Pay, +a: U32, +b: U32, +na: Node3, +nb: Node3) -> Q:
  (q, +pb) = r
  apply(R.rule(n3_kind(na), n3_kind(nb), rule_test(n3_kind(na), n3_kind(nb), pa, pb)),
    err_if(violation(n3_kind(na), n3_kind(nb), pa, pb), q), a, b, n3_kind(na), ext_of(na, nb), pa, pb)

def interact.paya(r: Q & V.Pay, +a: U32, +b: U32, +na: Node3, +nb: Node3) -> Q:
  (q, +pa) = r
  interact.pays(q_pay(q, b), pa, a, b, na, nb)

# a's principal is negative, b's positive
def interact.go(q: Q, +a: U32, +b: U32, +na: Node3, +nb: Node3) -> Q:
  interact.paya(q_pay(q, a), a, b, na, nb)

def interact.ori(neg: Bool, q: Q, +a: U32, +b: U32, +na: Node3, +nb: Node3) -> Q:
  match neg:
    case True{}:
      interact.go(q, a, b, na, nb)
    case False{}:
      interact.go(q, b, a, nb, na)

def interact.b(r: Q & Node3, +na: Node3, +a: U32, +b: U32) -> Q:
  (q, +nb) = r
  interact.ori(R.pol_eq(R.port_pol(n3_kind(na), 0n), R.Neg{}), q, a, b, na, nb)

def interact.a(r: Q & Node3, +a: U32, +b: U32) -> Q:
  (q, +na) = r
  interact.b(rd3(q, b), na, a, b)

# rewrite the active pair a >< b
def interact(q: Q, +a: U32, +b: U32) -> Q:
  interact.a(rd3(q, a), a, b)

# reduce active pairs until none is left or fuel runs out
def reduce(n: Nat, q: Q) -> Q:
  match n:
    case 0n:
      q
    case 1n+p:
      match q:
        case Q{st, rq, +itrs, +errs, +ser}:
          match rq:
            case Nil{}:
              Q{st, Nil{}, itrs, errs, ser}
            case Con{Redex{+a, +b}, t}:
              reduce(p, interact(Q{st, t, (itrs + 1 : U32), errs, ser}, a, b))

# Tracing
# =======

# one interaction as the reducer met it, before the rewrite: its number,
# the two nodes (negative principal first), their headers and payloads,
# the redex's external peers and their nodes' headers (0 for none), and
# the serials of the nodes it made, s0 up to s1
type Ev is Data:
  Ev{+i: U32, +a: U32, +b: U32, +ha: U32, +hb: U32, pa: V.Pay, pb: V.Pay, +x: Ext, +xh: Ext, +s0: U32, +s1: U32}

def q_ser(q: Q) -> Q & U32:
  match q:
    case Q{st, rq, +itrs, +errs, +ser}:
      (Q{st, rq, itrs, errs, ser}, ser)

def ph.go(nil: Bool, q: Q, +e: U32) -> Q & U32:
  match nil:
    case True{}:
      (q, 0)
    case False{}:
      q_word(q, e, 0)

# the header of the node behind reference e, or 0 for no peer
def ph(q: Q, +e: U32) -> Q & U32:
  ph.go(U32.is_eq(e, S.nil()), q, e)

def phs.d(r: Q & U32, +h0: U32, +h1: U32, +h2: U32) -> Q & Ext:
  (q, +h3) = r
  (q, Ext4{h0, h1, h2, h3})

def phs.c(r: Q & U32, +x: Ext, +h0: U32, +h1: U32) -> Q & Ext:
  (q, +h2) = r
  phs.d(ph(q, ext_at(x, 3n)), h0, h1, h2)

def phs.b(r: Q & U32, +x: Ext, +h0: U32) -> Q & Ext:
  (q, +h1) = r
  phs.c(ph(q, ext_at(x, 2n)), x, h0, h1)

def phs.a(r: Q & U32, +x: Ext) -> Q & Ext:
  (q, +h0) = r
  phs.b(ph(q, ext_at(x, 1n)), x, h0)

def phs(q: Q, +x: Ext) -> Q & Ext:
  phs.a(ph(q, ext_at(x, 0n)), x)

def obs.f(r: Q & U32, +i: U32, +a: U32, +b: U32, +ha: U32, +hb: U32, pa: V.Pay, pb: V.Pay, +x: Ext, +xh: Ext) -> Q & Ev:
  (q, +s0) = r
  (q, Ev{i, a, b, ha, hb, pa, pb, x, xh, s0, s0})

def obs.e(r: Q & Ext, +i: U32, +a: U32, +b: U32, +ha: U32, +hb: U32, pa: V.Pay, pb: V.Pay, +x: Ext) -> Q & Ev:
  (q, +xh) = r
  obs.f(q_ser(q), i, a, b, ha, hb, pa, pb, x, xh)

def obs.d(r: Q & V.Pay, +i: U32, +a: U32, +b: U32, +na: Node3, +nb: Node3, pa: V.Pay) -> Q & Ev:
  (q, pb) = r
  match na nb:
    case N3{+ha, l1, l2} N3{+hb, m1, m2}:
      obs.e(phs(q, ext_of(na, nb)), i, a, b, ha, hb, pa, pb, ext_of(na, nb))

def obs.c(r: Q & V.Pay, +i: U32, +a: U32, +b: U32, +na: Node3, +nb: Node3) -> Q & Ev:
  (q, pa) = r
  obs.d(q_pay(q, b), i, a, b, na, nb, pa)

def obs.b(r: Q & Node3, +i: U32, +a: U32, +b: U32, +na: Node3) -> Q & Ev:
  (q, +nb) = r
  obs.c(q_pay(q, a), i, a, b, na, nb)

def obs.a(r: Q & Node3, +i: U32, +a: U32, +b: U32) -> Q & Ev:
  (q, +na) = r
  obs.b(rd3(q, b), i, a, b, na)

def obs.ori(neg: Bool, q: Q, +i: U32, +a: U32, +b: U32) -> Q & Ev:
  match neg:
    case True{}:
      obs.a(rd3(q, a), i, a, b)
    case False{}:
      obs.a(rd3(q, b), i, b, a)

def obs.h(r: Q & U32, +i: U32, +a: U32, +b: U32) -> Q & Ev:
  (q, +h) = r
  obs.ori(R.pol_eq(R.port_pol(kof((h .&. 15 : U32)), 0n), R.Neg{}), q, i, a, b)

# read the redex a >< b without changing it. Reads only move the store's
# focus, and interact makes its own reads after these, so allocation, and
# with it the rewrite, stays as untraced.
def obs(q: Q, +i: U32, +a: U32, +b: U32) -> Q & Ev:
  obs.h(q_word(q, a, 0), i, a, b)

type Tr is Type:
  Tr{q: Q, log: List<&2, Ev>}

def ev_done(ev: Ev, +s1: U32) -> Ev:
  match ev:
    case Ev{+i, +a, +b, +ha, +hb, pa, pb, +x, +xh, +s0, +z}:
      Ev{i, a, b, ha, hb, pa, pb, x, xh, s0, s1}

def log.fin(r: Q & U32, ev: Ev, log: List<&2, Ev>) -> Tr:
  (q, +s1) = r
  Tr{q, ev_done(ev, s1) <> log}

def log.step(r: Q & Ev, +a: U32, +b: U32, log: List<&2, Ev>) -> Tr:
  (q, ev) = r
  log.fin(q_ser(interact(q, a, b)), ev, log)

# reduce as reduce does, logging each interaction (newest first)
def reduce_log(n: Nat, tr: Tr) -> Tr:
  match n:
    case 0n:
      tr
    case 1n+p:
      match tr:
        case Tr{q, log}:
          match q:
            case Q{st, rq, +itrs, +errs, +ser}:
              match rq:
                case Nil{}:
                  Tr{Q{st, Nil{}, itrs, errs, ser}, log}
                case Con{Redex{+a, +b}, t}:
                  reduce_log(p, log.step(obs(Q{st, t, (itrs + 1 : U32), errs, ser}, itrs, a, b), a, b, log))

# Rounds
# ======

type E is Type:
  E{q: Q, +moved: Bool}

def pending(rq: List<&2, Redex>) -> List<&2, Redex> & Bool:
  match rq:
    case Nil{}:
      (Nil{}, False{})
    case Con{x, t}:
      (Con{x, t}, True{})

def settle.start(r: List<&2, Redex> & Bool, st: S.Store, +itrs: U32, +errs: U32, +ser: U32) -> E:
  (rq, +more) = r
  E{Q{st, rq, itrs, errs, ser}, more}

# it moved if active pairs remain
def settle(q: Q) -> E:
  match q:
    case Q{st, rq, +itrs, +errs, +ser}:
      settle.start(pending(rq), st, itrs, errs, ser)

# reduce until nothing moves: n rounds of at most f interactions each
def eval(n: Nat, +f: Nat, e: E) -> E:
  match n:
    case 0n:
      e
    case 1n+p:
      match e:
        case E{q, +moved}:
          match moved:
            case False{}:
              E{q, False{}}
            case True{}:
              eval(p, f, settle(reduce(f, q)))
