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
    case R.KCopyL{}:
      12
    case R.KCopyR{}:
      13
    case R.KMergeL{}:
      14
    case R.KMergeR{}:
      15

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
    case 12:
      R.KCopyL{}
    case 13:
      R.KCopyR{}
    case 14:
      R.KMergeL{}
    case 15:
      R.KMergeR{}
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

# an inside end on either side: a closed loop of wire, which vanishes
# (knet.bend's pair_link)
def pair_link(bad: Bool, +u: R.End, +v: R.End, +x: Ext, +refs: List<&2, U32>, q: Q) -> Q:
  match bad:
    case True{}:
      q
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
# both: a run of unit brackets, which peeling (below) takes apart again
# where a control facing it needs its first units. Only the links a rule
# makes can newly join two controls, so each such link is tried once
# (fuse_ends, below). The node freed is the one whose principal faces the
# other's auxiliary, which cannot be in an active pair. The link a fusion
# makes is not tried again: on 600 random terms that found one more
# fusion, saving two interactions.

def q_set_pay(q: Q, +r: U32, p: V.Pay) -> Q:
  match q:
    case Q{st, rq, +itrs, +errs, +ser}:
      Q{S.st_set_pay(st, r, p), rq, itrs, errs, ser}

# Lifts: p's out feeds l's in; values cross p first. p stays, l goes.
def fl.fuse(f: V.Fuse, q: Q, +p: U32, +l: U32, +o: U32) -> Q:
  match f:
    case V.FNo{}:
      q
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
def fc.fuse(f: V.Fuse, q: Q, +a: U32, +b: U32, +i: U32) -> Q:
  match f:
    case V.FNo{}:
      q
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

# two controls of kind k meeting at ports px and py of nodes x and y:
# fused when principal meets auxiliary in the order they fuse
def fa.go(+k: U32, +px: U32, +py: U32, q: Q, +x: U32, +y: U32) -> Q:
  match k px py:
    case 10 1 0:
      fuse_lifts(q, x, y)
    case 10 0 1:
      fuse_lifts(q, y, x)
    case 11 0 1:
      fuse_liftcs(q, x, y)
    case 11 1 0:
      fuse_liftcs(q, y, x)
    case _ _ _:
      q

def fa.k(ok: Bool, +k: U32, q: Q, +x: U32, +y: U32) -> Q:
  match ok:
    case True{}:
      fa.go(k, S.ref_port(x), S.ref_port(y), q, node_of(x), node_of(y))
    case False{}:
      q

def fa.hy(r: Q & U32, +k: U32, +x: U32, +y: U32) -> Q:
  (q, +hy) = r
  fa.k(U32.is_eq((hy .&. 15 : U32), k) && U32.is_ne(node_of(x), node_of(y)), k, q, x, y)

def fa.y.go(none: Bool, q: Q, +k: U32, +x: U32, +y: U32) -> Q:
  match none:
    case True{}:
      q
    case False{}:
      fa.hy(q_word(q, y, 0), k, x, y)

def fa.y(r: Q & U32, +k: U32, +x: U32) -> Q:
  (q, +y) = r
  fa.y.go(U32.is_eq(y, S.nil()), q, k, x, y)

def fa.ctl(ctl: Bool, q: Q, +k: U32, +x: U32) -> Q:
  match ctl:
    case True{}:
      fa.y(q_word(q, x, (S.ref_port(x) + 1 : U32)), k, x)
    case False{}:
      q

def fa.hx(r: Q & U32, +x: U32) -> Q:
  (q, +hx) = r
  fa.ctl(U32.is_eq((hx .&. 15 : U32), 10) || U32.is_eq((hx .&. 15 : U32), 11), q, (hx .&. 15 : U32), x)

def fa.go0(none: Bool, q: Q, +x: U32) -> Q:
  match none:
    case True{}:
      q
    case False{}:
      fa.hx(q_word(q, x, 0), x)

# the link at port x: when it joins two controls of one kind, principal to
# auxiliary in the order they fuse, fuse them (as kprim.bend's fuse does)
def fuse_at(q: Q, +x: U32) -> Q:
  fa.go0(U32.is_eq(x, S.nil()), q, x)

def is_ctl(k: R.NodeKind) -> Bool:
  match k:
    case R.KLift{}:
      True{}
    case R.KLiftC{}:
      True{}
    case _:
      False{}

def any_partner(+x: Ext, +a: U32, +b: U32) -> Bool:
  match x:
    case Ext4{+e0, +e1, +e2, +e3}:
      Maybe.is_some(&2, Nat, partner(e0, a, b)) || Maybe.is_some(&2, Nat, partner(e1, a, b)) ||
        Maybe.is_some(&2, Nat, partner(e2, a, b)) || Maybe.is_some(&2, Nat, partner(e3, a, b))

# Where a rewrite tries fusion, here and in the kernel (fuse_at): for each
# link a rule makes whose ends may both be controls of one kind (an
# external end, or a new control), one end, the external one if any. A
# new node's principal faces outward and its auxiliaries face new nodes of
# another kind, so no other place can newly hold two controls in a row.
def fe.keep(b: Bool, e: R.End, rest: List<&2, R.End>) -> List<&2, R.End>:
  match b:
    case True{}:
      e <> rest
    case False{}:
      rest

def fe.link(+xs: List<&2, R.Spec>, u: R.End, v: R.End, rest: List<&2, R.End>) -> List<&2, R.End>:
  match u v:
    case R.Ext{i} R.Ext{j}:
      R.Ext{i} <> rest
    case R.Ext{i} R.New{+j, +p}:
      fe.keep(is_ctl(R.spec_kind(xs, j)), R.Ext{i}, rest)
    case R.New{+j, +p} R.Ext{i}:
      fe.keep(is_ctl(R.spec_kind(xs, j)), R.Ext{i}, rest)
    case R.New{+j, +p} R.New{+k, +q}:
      fe.keep(is_ctl(R.spec_kind(xs, j)) && U32.is_eq(kcode(R.spec_kind(xs, j)), kcode(R.spec_kind(xs, k))), R.New{j, p}, rest)

def fuse_ends(+xs: List<&2, R.Spec>, ls: List<&2, R.Link>) -> List<&2, R.End>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{R.Link{u, v}, t}:
      fe.link(xs, u, v, fuse_ends(xs, t))

def fuse_ends.go(es: List<&2, R.End>, +x: Ext, +refs: List<&2, U32>, q: Q) -> Q:
  match es:
    case Nil{}:
      q
    case Con{e, t}:
      fuse_ends.go(t, x, refs, fuse_at(q, resolve(x, refs, e)))

def fuse_ext.go(skip: Bool, +e: U32, q: Q) -> Q:
  match skip:
    case True{}:
      q
    case False{}:
      fuse_at(q, e)

def fuse_ext(+e: U32, +a: U32, +b: U32, q: Q) -> Q:
  fuse_ext.go(U32.is_eq(e, S.nil()) || Maybe.is_some(&2, Nat, partner(e, a, b)), e, q)

# fusion after a rewrite: at each link the rule made that may join two
# controls, or, where the redex's own ports were joined through it, at
# each external peer outside it, in order
def fuse_made(partners: Bool, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +x: Ext, +refs: List<&2, U32>, +a: U32, +b: U32, q: Q) -> Q:
  match partners:
    case True{}:
      match x:
        case Ext4{+e0, +e1, +e2, +e3}:
          fuse_ext(e3, a, b, fuse_ext(e2, a, b, fuse_ext(e1, a, b, fuse_ext(e0, a, b, q))))
    case False{}:
      fuse_ends.go(fuse_ends(xs, ls), x, refs, q)

def wire.made(m: Made, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +x: Ext, +a: U32, +b: U32) -> Q:
  match m:
    case Made{q, +refs}:
      fuse_made(any_partner(x, a, b), xs, ls, x, refs, a, b,
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
    case R.KLift{} R.KLiftC{}:
      lift_wraps(pa, pay_level(pb)) || lift_wraps(pb, pay_level(pa))
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

# Peeling
# -------
#
# A fused control stands for a run of unit brackets (V.compose). Where a
# Lift and a LiftC meet at one index as different controls, the units
# would meet one at a time: so the one that raises further gives up its
# first units as a control of its own before the rule applies, as many
# as the other raises, and the two then cancel; facing a drop, a raise of
# more than one gives up one unit, which crosses it. The rest stays
# behind, a control from the index where those units end. Nets lowering
# makes never meet so without fusion at run time (heap-demand).

def sel_lt(c: Bool, +x: U32, +y: U32) -> U32:
  match c:
    case True{}:
      x
    case False{}:
      y

# how much of a run to keep facing, the rest peeled behind: 0 for none
def peel.amt(+ua: Bool, +ba: U32, +ub: Bool, +bb: U32) -> U32:
  match ua ub:
    case True{} True{}:
      sel_lt(U32.is_lt(bb, ba), bb, 0)
    case True{} False{}:
      sel_lt(U32.is_lt(1, ba), 1, 0)
    case _ _:
      0

# x keeps the first k units of its run of `by` at index n; a control of
# kind k2 takes the rest behind it, on x's port 1, whose peer is e
def peel.at(r: Q & U32, +x: U32, +e: U32) -> Q:
  (q, +rest) = r
  link(link(q, S.ref_at(x, 1), rest), S.ref_at(rest, 1), e)

def peel.do(r: Q & U32, +x: U32, k2: R.NodeKind, +n: U32, +k: U32, +by: U32) -> Q:
  (q, +e) = r
  peel.at(node(err_if(U32.is_lt((n + k : U32), n), q_set_pay(q, x, V.PLift{n, True{}, k})), k2, V.PLift{(n + k : U32), True{}, (by - k : U32)}), x, e)

def peel.if(+k: U32, q: Q, +x: U32, k2: R.NodeKind, +n: U32, +by: U32) -> Q:
  match k:
    case 0:
      q
    case _:
      peel.do(q_word(q, x, 2), x, k2, n, k, by)

def peel.same(same: Bool, q: Q, +l: U32, +c: U32, +n: U32, +ul: Bool, +bl: U32, +uc: Bool, +bc: U32) -> Q:
  match same:
    case True{}:
      peel.if(peel.amt(uc, bc, ul, bl), peel.if(peel.amt(ul, bl, uc, bc), q, l, R.KLift{}, n, bl), c, R.KLiftC{}, n, bc)
    case False{}:
      q

# l a Lift, c a LiftC, facing: peel l's run against c, or c's against l
def peel.pays(+pl: V.Pay, +pc: V.Pay, q: Q, +l: U32, +c: U32) -> Q:
  match pl pc:
    case V.PLift{+n, +ul, +bl} V.PLift{+m, +uc, +bc}:
      peel.same(U32.is_eq(n, m), q, l, c, n, ul, bl, uc, bc)
    case _ _:
      q

def peel.pc(r: Q & V.Pay, +pl: V.Pay, +l: U32, +c: U32) -> Q:
  (q, +pc) = r
  peel.pays(pl, pc, q, l, c)

def peel.pl(r: Q & V.Pay, +l: U32, +c: U32) -> Q:
  (q, +pl) = r
  peel.pc(q_pay(q, c), pl, l, c)

def peel.k(+ka: U32, +kb: U32, q: Q, +a: U32, +b: U32) -> Q:
  match ka kb:
    case 10 11:
      peel.pl(q_pay(q, a), a, b)
    case 11 10:
      peel.pl(q_pay(q, b), b, a)
    case _ _:
      q

def peel.hb(r: Q & U32, +ka: U32, +a: U32, +b: U32) -> Q:
  (q, +hb) = r
  peel.k(ka, (hb .&. 15 : U32), q, a, b)

def peel.ha(r: Q & U32, +a: U32, +b: U32) -> Q:
  (q, +ha) = r
  peel.hb(q_word(q, b, 0), (ha .&. 15 : U32), a, b)

# rewrite the active pair a >< b, a fused control facing a partner peeled
# first
def interact(q: Q, +a: U32, +b: U32) -> Q:
  interact.a(rd3(peel.ha(q_word(q, a, 0), a, b), a), a, b)

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
