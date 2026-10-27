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
    case _:
      R.KFree{}

# The reducer's state
# ===================

type Redex is Data:
  Redex{+a: U32, +b: U32}

# the store, the active pairs, and counts: interactions, errors (rule
# violations, loops it cannot resolve), calls left for the evaluator
type Q is Type:
  Q{st: S.Store, rq: List<&2, Redex>, +itrs: U32, +errs: U32, +calls: List<&2, Redex>}

def q_new() -> Q:
  Q{S.st_new(), Nil{}, 0, 0, Nil{}}

def q_err(q: Q) -> Q:
  match q:
    case Q{st, rq, +itrs, +errs, calls}:
      Q{st, rq, itrs, (errs + 1 : U32), calls}

def q_word.fin(r: S.Store & U32, rq: List<&2, Redex>, +itrs: U32, +errs: U32, calls: List<&2, Redex>) -> Q & U32:
  (st, +x) = r
  (Q{st, rq, itrs, errs, calls}, x)

def q_word(q: Q, +r: U32, +k: U32) -> Q & U32:
  match q:
    case Q{st, rq, +itrs, +errs, calls}:
      q_word.fin(S.st_get(st, r, k), rq, itrs, errs, calls)

def q_pay.fin(r: S.Store & V.Pay, rq: List<&2, Redex>, +itrs: U32, +errs: U32, calls: List<&2, Redex>) -> Q & V.Pay:
  (st, p) = r
  (Q{st, rq, itrs, errs, calls}, p)

def q_pay(q: Q, +r: U32) -> Q & V.Pay:
  match q:
    case Q{st, rq, +itrs, +errs, calls}:
      q_pay.fin(S.st_pay(st, r), rq, itrs, errs, calls)

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
    case Q{st, rq, +itrs, +errs, calls}:
      st1 = S.st_set(st, x, (S.ref_port(x) + 1 : U32), y)
      st2 = S.st_set(st1, y, (S.ref_port(y) + 1 : U32), x)
      Q{st2, push_if(both0(x, y), x, y, rq), itrs, errs, calls}

def node.fin(r: S.Store & U32, +k: U32, p: V.Pay, rq: List<&2, Redex>, +itrs: U32, +errs: U32, calls: List<&2, Redex>) -> Q & U32:
  (st, +ref) = r
  (Q{S.st_set_pay(S.st_set(st, ref, 0, k), ref, p), rq, itrs, errs, calls}, ref)

# a new node of kind k with payload p: its port 0
def node(q: Q, k: R.NodeKind, p: V.Pay) -> Q & U32:
  match q:
    case Q{st, rq, +itrs, +errs, calls}:
      node.fin(S.st_alloc(st), kcode(k), p, rq, itrs, errs, calls)

def free(q: Q, +r: U32) -> Q:
  match q:
    case Q{st, rq, +itrs, +errs, calls}:
      Q{S.st_free(st, r), rq, itrs, errs, calls}

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
      V.fan_new(0, 0)

def src_pay(s: R.Src, +pa: V.Pay, +pb: V.Pay) -> V.Pay:
  match s:
    case R.SNone{}:
      V.PNone{}
    case R.SPayB{}:
      pb
    case R.SFanA{}:
      pa
    case R.SFanB{}:
      pb
    case R.SFanAx{k}:
      V.PFan{V.fan_extend(fan_of(pa), V.fan_hash(fan_of(pb)), U32.from_nat(k))}
    case R.SFanBx{k}:
      V.PFan{V.fan_extend(fan_of(pb), V.fan_hash(fan_of(pa)), U32.from_nat(k))}

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

def wire.made(m: Made, +ls: List<&2, R.Link>, +x: Ext, +a: U32, +b: U32) -> Q:
  match m:
    case Made{q, +refs}:
      link_pairs(4n, 0n, ls, x, refs, a, b, link_plain(ls, x, refs, a, b, q))

# replace the redex a >< b by the rule's nodes and links
def wire(q: Q, +a: U32, +b: U32, xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +x: Ext, +pa: V.Pay, +pb: V.Pay) -> Q:
  wire.made(make(xs, pa, pb, Made{free(free(q, a), b), Nil{}}), ls, x, a, b)

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

def has_aux(k: R.NodeKind) -> Bool:
  match k:
    case R.KFn{}:
      True{}
    case R.KAp{}:
      True{}
    case R.KCopy{}:
      True{}
    case R.KMerge{}:
      True{}
    case _:
      False{}

def aux_or_nil(b: Bool, +l: U32) -> U32:
  match b:
    case True{}:
      l
    case False{}:
      S.nil()

def ext_of(+na: Node3, +nb: Node3) -> Ext:
  match na nb:
    case N3{h1, +a1, +a2} N3{h2, +b1, +b2}:
      Ext4{aux_or_nil(has_aux(n3_kind(na)), a1), aux_or_nil(has_aux(n3_kind(na)), a2),
        aux_or_nil(has_aux(n3_kind(nb)), b1), aux_or_nil(has_aux(n3_kind(nb)), b2)}

def same_fans(ka: R.NodeKind, kb: R.NodeKind, +pa: V.Pay, +pb: V.Pay) -> Bool:
  match ka kb:
    case R.KCopy{} R.KMerge{}:
      V.fan_eq(fan_of(pa), fan_of(pb))
    case _ _:
      False{}

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

def calls_add(q: Q, +a: U32, +b: U32) -> Q:
  match q:
    case Q{st, rq, +itrs, +errs, calls}:
      Q{st, rq, itrs, errs, Redex{a, b} <> calls}

def apply(r: R.Rule, q: Q, +a: U32, +b: U32, +ka: R.NodeKind, +x: Ext, +pa: V.Pay, +pb: V.Pay) -> Q:
  match r:
    case R.RWire{xs, ls}:
      wire(q, a, b, xs, ls, x, pa, pb)
    case R.RCall{}:
      calls_add(q, a, b)
    case R.RStuck{}:
      stuck(is_root(ka), q)

def interact.pays(r: Q & V.Pay, +pa: V.Pay, +a: U32, +b: U32, +na: Node3, +nb: Node3) -> Q:
  (q, +pb) = r
  apply(R.rule(n3_kind(na), n3_kind(nb), same_fans(n3_kind(na), n3_kind(nb), pa, pb)), q, a, b, n3_kind(na), ext_of(na, nb), pa, pb)

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
        case Q{st, rq, +itrs, +errs, calls}:
          match rq:
            case Nil{}:
              Q{st, Nil{}, itrs, errs, calls}
            case Con{Redex{+a, +b}, t}:
              reduce(p, interact(Q{st, t, (itrs + 1 : U32), errs, calls}, a, b))

# Calls
# =====

# An application meeting data calls it. The call waits until its argument
# is data too: reduction elsewhere may still be producing it.

def pay_val(p: V.Pay) -> V.Val:
  match p:
    case V.PVal{v}:
      v
    case _:
      V.VUnit{}

def call.link(r: Q & U32, +resp: U32) -> Q & Bool:
  (q, +d) = r
  (link(q, d, resp), True{})

def call.arg(r: Q & V.Pay, +fv: V.Val, +a: U32, +b: U32, +argn: U32, +resp: U32) -> Q & Bool:
  (q, +ap) = r
  call.link(node(free(free(free(q, a), b), argn), R.KData{}, V.PVal{V.apply_fn(fv, pay_val(ap))}), resp)

def call.fun(r: Q & V.Pay, +a: U32, +b: U32, +argn: U32, +resp: U32) -> Q & Bool:
  (q, +fp) = r
  call.arg(q_pay(q, argn), pay_val(fp), a, b, argn, resp)

def call.ready(ok: Bool, q: Q, +a: U32, +b: U32, +argn: U32, +resp: U32) -> Q & Bool:
  match ok:
    case True{}:
      call.fun(q_pay(q, b), a, b, argn, resp)
    case False{}:
      (calls_add(q, a, b), False{})

def call.hdr(r: Q & U32, +a: U32, +b: U32, +argn: U32, +resp: U32) -> Q & Bool:
  (q, +h) = r
  call.ready(U32.is_eq((h .&. 15 : U32), 5) && U32.is_eq(S.ref_port(argn), 0), q, a, b, argn, resp)

def call.peers(r: Q & Node3, +a: U32, +b: U32) -> Q & Bool:
  (q, +n) = r
  match n:
    case N3{h, +argn, +resp}:
      call.hdr(q_word(q, argn, 0), a, b, argn, resp)

# a = the application, b = the data it meets; true if the call happened
def try_call(q: Q, +a: U32, +b: U32) -> Q & Bool:
  call.peers(rd3(q, a), a, b)

type E is Type:
  E{q: Q, +moved: Bool}

def settle.one(r: Q & Bool, +moved: Bool) -> E:
  (q, +did) = r
  E{q, moved || did}

def settle.go(cs: List<&2, Redex>, e: E) -> E:
  match cs:
    case Nil{}:
      e
    case Con{Redex{+a, +b}, t}:
      match e:
        case E{q, +moved}:
          settle.go(t, settle.one(try_call(q, a, b), moved))

def pending(rq: List<&2, Redex>) -> List<&2, Redex> & Bool:
  match rq:
    case Nil{}:
      (Nil{}, False{})
    case Con{x, t}:
      (Con{x, t}, True{})

def settle.start(r: List<&2, Redex> & Bool, st: S.Store, +itrs: U32, +errs: U32, calls: List<&2, Redex>) -> E:
  (rq, +more) = r
  settle.go(calls, E{Q{st, rq, itrs, errs, Nil{}}, more})

# perform every call whose argument is ready; the rest wait again. It
# moved if a call happened or active pairs remain.
def settle(q: Q) -> E:
  match q:
    case Q{st, rq, +itrs, +errs, calls}:
      settle.start(pending(rq), st, itrs, errs, calls)

# reduce, then perform the ready calls, until nothing moves: n rounds of
# at most f interactions each
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
