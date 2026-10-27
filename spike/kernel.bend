import Base
import ./val.bend as V
import ./rules.bend as R
import ./net.bend as N
import ./tpl.bend as T
import ./nets.bend as X
import ./kprim.bend as P
import ./krules.bend as KR

# A reducer kernel with the node layout of spike-node-layout
# (docs/plans/EvalSpike_2026-10-26.md), over kprim.bend's primitives. Its
# rewrites are krules.bend's, generated from the rule table (R.rule); its
# reference is the table itself, interpreted here as net.bend does on the
# kernel's layout, which also takes every redex whose external peers
# include its own ports (the identity function's body is its argument):
# those are joined through the rule's links, as net.bend's link_pairs does.
# Payloads of data nodes and calls are linear, as in the generator: the
# first new node using one takes it over, a later one gets a duplicate, a
# rule using it nowhere drops it. Both paths make net.bend's level checks
# (but the sites of two fans meeting at one level) and fuse controls after
# each rewrite as it does, on the same links in the same order.
#
#   kernel <k> [ref|plus|plusref|fma|fmaref|lvl|lvlref]
#       reduce `k 2 succ 0` (2^k) built without levels; with plus
#       `k 2 (plus 1) 0`, adding by a partial application in a node; with
#       fma `k 2 (fma 1 1) 0`, by one in the data table; with lvl
#       `k 2 succ 0` with levels, as terms.py lowers it (k >= 2). Report
#       value, counts, time; with ref, by the interpreted table alone

# Payloads
# ========

def is_data(+k: U32) -> Bool:
  U32.is_eq(k, 5) || U32.is_eq(k, 9)

type Mk is Type:
  Mk{h: P.H, refs: List<&2, U32>, +ua: Bool, +ub: Bool}

def pw.dup(r: P.H & U32, +m: U32, +f: U32) -> P.H & P.PW:
  (h, +w) = r
  (h, P.PW{m, f, w})

# a payload's next use: the first takes it over; a later one, of a data
# node's or a call's, a duplicate
def pay.use(+dup: Bool, h: P.H, +hx: U32, +px: U32) -> P.H & P.PW:
  match dup:
    case True{}:
      pw.dup(P.dup(h, P.form(hx), px), P.form(hx), P.fld(hx))
    case False{}:
      (h, P.PW{P.form(hx), P.fld(hx), px})

# a new node's form, field and payload word, after the rule's source: A's
# and B's headers and payload words, and whether each payload is taken yet
def pay(s: R.Src, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +ua: Bool, +ub: Bool) -> P.H & P.PW:
  match s:
    case R.SNone{}:
      (h, P.PW{0, 0, 0})
    case R.SPayA{}:
      pay.use(ua && is_data(P.rk(ha)), h, ha, pa)
    case R.SPayB{}:
      pay.use(ub && is_data(P.rk(hb)), h, hb, pb)
    case R.SFanA{}:
      (h, P.PW{0, P.fld(ha), 0})
    case R.SFanB{}:
      (h, P.PW{0, P.fld(hb), 0})
    case R.SApply{}:
      P.apply(h, ha, pa, hb, pb)
    case R.SLiftA{}:
      (h, P.PW{0, P.lift(P.fld(hb), pb, P.fld(ha)), pa})
    case R.SLiftB{}:
      (h, P.PW{0, P.lift(P.fld(ha), pa, P.fld(hb)), pb})

def takes_a(s: R.Src) -> Bool:
  match s:
    case R.SPayA{}:
      True{}
    case R.SApply{}:
      True{}
    case _:
      False{}

def takes_b(s: R.Src) -> Bool:
  match s:
    case R.SPayB{}:
      True{}
    case R.SApply{}:
      True{}
    case _:
      False{}

# Applying a rule
# ===============

def mk.add(r: P.H & U32, refs: List<&2, U32>, +ua: Bool, +ub: Bool) -> Mk:
  (h, +n) = r
  Mk{h, List.append(&2, U32, refs, [n]), ua, ub}

def mk.node(r: P.H & P.PW, +k: R.NodeKind, refs: List<&2, U32>, +ua: Bool, +ub: Bool) -> Mk:
  (h, pw) = r
  mk.add(P.node_pw(h, N.kcode(k), pw), refs, ua, ub)

def mk.step(m: Mk, sp: R.Spec, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> Mk:
  match m:
    case Mk{h, refs, +ua, +ub}:
      match sp:
        case R.Spec{+k, +s}:
          mk.node(pay(s, h, ha, hb, pa, pb, ua, ub), k, refs, ua || takes_a(s), ub || takes_b(s))

# allocate the rule's new nodes, in order
def make(xs: List<&2, R.Spec>, +ha: U32, +hb: U32, +pa: U32, +pb: U32, m: Mk) -> Mk:
  match xs:
    case Nil{}:
      m
    case Con{sp, t}:
      make(t, ha, hb, pa, pb, mk.step(m, sp, ha, hb, pa, pb))

def drop_if(d: Bool, h: P.H, +hx: U32, +px: U32) -> P.H:
  match d:
    case True{}:
      P.drop(h, P.form(hx), px)
    case False{}:
      h

# a data payload no new node took, dropped
def drop_unused(m: Mk, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> Mk:
  match m:
    case Mk{h, refs, +ua, +ub}:
      Mk{drop_if(is_data(P.rk(hb)) && Bool.not(ub), drop_if(is_data(P.rk(ha)) && Bool.not(ua), h, ha, pa), hb, pb), refs, ua, ub}

def new_ref(+n: U32, +p: Nat, +k: R.NodeKind) -> U32:
  (n + U32.from_nat(p) : U32)

def resolve(+x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, e: R.End) -> U32:
  match e:
    case R.Ext{i}:
      N.ext_at(x, i)
    case R.New{+j, +p}:
      new_ref(N.nth(refs, j), p, R.spec_kind(xs, j))

def internal(+x: N.Ext, +a: U32, +b: U32, e: R.End) -> Bool:
  match e:
    case R.Ext{i}:
      Maybe.is_some(&2, Nat, N.partner(N.ext_at(x, i), a, b))
    case R.New{j, p}:
      False{}

def link_if(b: Bool, h: P.H, +u: U32, +v: U32) -> P.H:
  match b:
    case True{}:
      P.link(h, u, v)
    case False{}:
      h

# link every rule link whose ends are both outside the redex
def link_plain(ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32, h: P.H) -> P.H:
  match ls:
    case Nil{}:
      h
    case Con{R.Link{+u, +v}, t}:
      link_plain(t, x, refs, xs, a, b,
        link_if(Bool.not(internal(x, a, b, u) || internal(x, a, b, v)), h, resolve(x, refs, xs, u), resolve(x, refs, xs, v)))

def pair_link(bad: Bool, +u: R.End, +v: R.End, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, h: P.H) -> P.H:
  match bad:
    case True{}:
      P.h_err(h)
    case False{}:
      P.link(h, resolve(x, refs, xs, u), resolve(x, refs, xs, v))

def pair_ends(oi: Maybe<&2, R.End>, oj: Maybe<&2, R.End>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32, h: P.H) -> P.H:
  match oi oj:
    case Some{+u} Some{+v}:
      pair_link(internal(x, a, b, u) || internal(x, a, b, v), u, v, x, refs, xs, h)
    case _ _:
      P.h_err(h)

def pair_go(lt: Bool, +i: Nat, +j: Nat, +ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32, h: P.H) -> P.H:
  match lt:
    case True{}:
      pair_ends(N.other(ls, i), N.other(ls, j), x, refs, xs, a, b, h)
    case False{}:
      h

def pair_at(pt: Maybe<&2, Nat>, +i: Nat, +ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32, h: P.H) -> P.H:
  match pt:
    case None{}:
      h
    case Some{+j}:
      pair_go(Nat.is_lt(i, j), i, j, ls, x, refs, xs, a, b, h)

# an external peer that is a port of the redex stands for another
# external: join what the rule links to the two (net.bend's link_pairs)
def link_pairs(n: Nat, +i: Nat, +ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, +a: U32, +b: U32, h: P.H) -> P.H:
  match n:
    case 0n:
      h
    case 1n+p:
      link_pairs(p, 1n+i, ls, x, refs, xs, a, b, pair_at(N.partner(N.ext_at(x, i), a, b), i, ls, x, refs, xs, a, b, h))

# fusion at each link the rule made that may join two controls, as the
# generated rewrites try it
def fuse_ends(es: List<&2, R.End>, +x: N.Ext, +refs: List<&2, U32>, +xs: List<&2, R.Spec>, h: P.H) -> P.H:
  match es:
    case Nil{}:
      h
    case Con{e, t}:
      fuse_ends(t, x, refs, xs, P.fuse(h, resolve(x, refs, xs, e)))

def fuse_ext.go(skip: Bool, +e: U32, h: P.H) -> P.H:
  match skip:
    case True{}:
      h
    case False{}:
      P.fuse(h, e)

def fuse_ext(+e: U32, +a: U32, +b: U32, h: P.H) -> P.H:
  fuse_ext.go(U32.is_eq(e, P.nil()) || Maybe.is_some(&2, Nat, N.partner(e, a, b)), e, h)

# fusion at each external peer outside the redex: where the redex's own
# ports were joined through it, the links it made are not the rule's
def fuse_exts(+x: N.Ext, +a: U32, +b: U32, h: P.H) -> P.H:
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      fuse_ext(e3, a, b, fuse_ext(e2, a, b, fuse_ext(e1, a, b, fuse_ext(e0, a, b, h))))

def fuse_made(partners: Bool, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +a: U32, +b: U32, h: P.H) -> P.H:
  match partners:
    case True{}:
      fuse_exts(x, a, b, h)
    case False{}:
      fuse_ends(N.fuse_ends(xs, ls), x, refs, xs, h)

def wire.made(m: Mk, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +x: N.Ext, +a: U32, +b: U32) -> P.H:
  match m:
    case Mk{h, +refs, +ua, +ub}:
      fuse_made(N.any_partner(x, a, b), xs, ls, x, refs, a, b,
        link_pairs(4n, 0n, ls, x, refs, xs, a, b, link_plain(ls, x, refs, xs, a, b, h)))

# replace the redex a >< b by the rule's nodes and links
def wire(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +x: N.Ext) -> P.H:
  wire.made(drop_unused(make(xs, ha, hb, pa, pb, Mk{P.fresh2(h, a, b), Nil{}, False{}, False{}}), ha, hb, pa, pb), xs, ls, x, a, b)

def apply_rule(r: R.Rule, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> P.H:
  match r:
    case R.RWire{xs, ls}:
      wire(h, a, b, ha, hb, pa, pb, xs, ls, x)
    case R.RStuck{}:
      P.err_if(U32.is_ne(P.rk(ha), 8), h)

# Interaction
# ===========

def kof(+h: U32) -> R.NodeKind:
  N.kof(P.rk(h))

# ports, by rule kind (generated from R.arity)
def arity(+h: U32) -> U32:
  KR.kind_arity(P.rk(h))

def aux_or_nil(b: Bool, +l: U32) -> U32:
  match b:
    case True{}:
      l
    case False{}:
      P.nil()

def payload.k(+k: U32, +w1: U32, +w3: U32) -> U32:
  match k:
    case 5:
      w1
    case 9:
      w3
    case 10:
      w3
    case 11:
      w3
    case _:
      0

# a node's payload word: a data node's word 2, a call's or a control's 3
def payload(+h: U32, +w1: U32, +w3: U32) -> U32:
  payload.k(P.rk(h), w1, w3)

def ctl_eq(+ha: U32, +hb: U32, +pa: U32, +pb: U32) -> Bool:
  U32.is_eq(P.fld(ha), P.fld(hb)) && U32.is_eq(pa, pb)

# fans pair, and an application meets its function, when level and
# marker agree (a net without levels: equal sites)
def same_lvl(+ha: U32, +hb: U32) -> Bool:
  U32.is_eq((ha >> 4n : U32), (hb >> 4n : U32))

def test.k(+ka: U32, +kb: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  match ka kb:
    case 3 4:
      (h, same_lvl(ha, hb))
    case 2 5:
      P.val_is_fn(h, P.form(hb), P.fld(hb), pb)
    case 2 1:
      (h, same_lvl(ha, hb))
    case 10 11:
      (h, ctl_eq(ha, hb, pa, pb))
    case _ _:
      (h, False{})

# the payload test the rule takes (net.bend's rule_test)
def test(h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  test.k(P.rk(ha), P.rk(hb), h, ha, hb, pa, pb)

# is e a port of the redex itself? (net.bend's partner, without the index)
def mine(+e: U32, +a: U32, +b: U32) -> Bool:
  U32.is_ne(e, P.nil()) && (U32.is_eq((e >> 2n : U32), (a >> 2n : U32)) || U32.is_eq((e >> 2n : U32), (b >> 2n : U32)))

def any_partner(+x: N.Ext, +a: U32, +b: U32) -> Bool:
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      mine(e0, a, b) || mine(e1, a, b) || mine(e2, a, b) || mine(e3, a, b)

def go.gen(+t: Bool, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> P.H:
  match x:
    case N.Ext4{+e0, +e1, +e2, +e3}:
      KR.rewrite(P.rk(ha), P.rk(hb), t, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def go.which(gen: Bool, +t: Bool, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> P.H:
  match gen:
    case True{}:
      go.gen(t, h, a, b, ha, hb, pa, pb, x)
    case False{}:
      apply_rule(R.rule(kof(ha), kof(hb), t), KR.check(P.rk(ha), P.rk(hb), h, ha, hb, pa, pb), a, b, ha, hb, pa, pb, x)

# the generated rewrite, or the interpreted table: for a redex whose
# external peers include its own ports, or when `fast` is off
def go.rule(r: P.H & Bool, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> P.H:
  (h, +t) = r
  go.which(fast && Bool.not(any_partner(x, a, b)), t, h, a, b, ha, hb, pa, pb, x)

def go.ext(+fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32, +b1: U32, +b2: U32, h: P.H) -> P.H:
  go.rule(test(h, ha, hb, payload(ha, 0, a2), payload(hb, b1, b2)), fast, a, b, ha, hb, payload(ha, 0, a2), payload(hb, b1, b2),
    N.Ext4{aux_or_nil(U32.is_lt(1, arity(ha)), a1), aux_or_nil(U32.is_lt(2, arity(ha)), a2),
      aux_or_nil(U32.is_lt(1, arity(hb)), b1), aux_or_nil(U32.is_lt(2, arity(hb)), b2)})

def go.b2(r: P.H & U32, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32, +b1: U32) -> P.H:
  (h, +b2) = r
  go.ext(fast, a, b, ha, hb, a1, a2, b1, b2, h)

def go.b1(r: P.H & U32, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32) -> P.H:
  (h, +b1) = r
  go.b2(P.rd(h, (b + 3 : U32)), fast, a, b, ha, hb, a1, a2, b1)

def go.a2(r: P.H & U32, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32) -> P.H:
  (h, +a2) = r
  go.b1(P.rd(h, (b + 2 : U32)), fast, a, b, ha, hb, a1, a2)

def go.a1(r: P.H & U32, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32) -> P.H:
  (h, +a1) = r
  go.a2(P.rd(h, (a + 3 : U32)), fast, a, b, ha, hb, a1)

# a's principal is negative. Words 2 and 3 are ports 1 and 2's links, or
# a node's payload: a data node's word 2, a call's or a control's word 3.
def go(h: P.H, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32) -> P.H:
  go.a1(P.rd(h, (a + 2 : U32)), fast, a, b, ha, hb)

def ori(neg: Bool, h: P.H, +fast: Bool, +x: U32, +y: U32, +hx: U32, +hy: U32) -> P.H:
  match neg:
    case True{}:
      go(h, fast, x, y, hx, hy)
    case False{}:
      go(h, fast, y, x, hy, hx)

def int.y(r: P.H & U32, +fast: Bool, +x: U32, +y: U32, +hx: U32) -> P.H:
  (h, +hy) = r
  ori(KR.kind_neg(P.rk(hx)), h, fast, x, y, hx, hy)

def int.x(r: P.H & U32, +fast: Bool, +x: U32, +y: U32) -> P.H:
  (h, +hx) = r
  int.y(P.rd(h, y), fast, x, y, hx)

# rewrite the active pair x >< y
def interact(h: P.H, +fast: Bool, +x: U32, +y: U32) -> P.H:
  int.x(P.rd(h, x), fast, x, y)

# reduce active pairs, newest first, until none is left or fuel runs out
# the state after a run, and the fuel it left
type Ran is Type:
  Ran{h: P.H, +left: Nat}

def run(n: Nat, +fast: Bool, pp: P.Pop) -> Ran:
  match n:
    case 0n:
      Ran{P.unpop(pp), 0n}
    case 1n+p:
      match pp:
        case P.Pop{h, +x, +y, +ok}:
          match ok:
            case True{}:
              run(p, fast, P.pop(interact(h, fast, x, y)))
            case False{}:
              Ran{h, 1n+p}

def ran(r: Ran, +fuel: Nat) -> P.H:
  match r:
    case Ran{h, +left}:
      P.count(h, U32.from_nat(Nat.sub(fuel, left)))

# a run of at most fuel interactions, which counts them by the fuel it used
def reduce_h(+fuel: Nat, +fast: Bool, h: P.H) -> P.H:
  ran(run(fuel, fast, P.pop(h)), fuel)

# Loading a template
# ==================

def lift_word(+up: Bool, +by: U32) -> U32:
  match up:
    case True{}:
      (by .|. 2147483648 : U32)
    case False{}:
      by

def drop_ref(r: P.H & U32) -> P.H:
  (h, +n) = r
  h

def load.data(r: P.H & P.PW, +k: U32) -> P.H:
  (h, pw) = r
  drop_ref(P.node_pw(h, k, pw))

def fan_hd.go(none: Bool, +k: U32, +site: U32, +lvl: U32) -> U32:
  match none:
    case True{}:
      P.hd2(k, P.unlev(), site)
    case False{}:
      P.hd(k, lvl)

# a fan's header: its level, or for a net built without levels its site,
# marked so
def fan_hd(+k: U32, +site: U32, +lvl: U32) -> U32:
  fan_hd.go(U32.is_eq(lvl, V.nolvl()), k, site, lvl)

# a node with no payload: a function or an application without a level
# marked so
def bare_hd(+k: U32) -> U32:
  match k:
    case 1:
      P.hd2(k, P.unlev(), 0)
    case 2:
      P.hd2(k, P.unlev(), 0)
    case _:
      P.hd(k, 0)

def too_big(+f: U32) -> Bool:
  U32.is_ge(f, P.lvl_cap())

# the field a fan keeps, its site without a level, else its level
def fan_too_big(none: Bool, +site: U32, +lvl: U32) -> Bool:
  match none:
    case True{}:
      too_big(site)
    case False{}:
      too_big(lvl)

# a node from its template; a level, site or index past the field's 24
# bits, or an offset past 31, would be cut short: an error
def load.node(h: P.H, t: T.TNode) -> P.H:
  match t:
    case T.TF{k, +site, +lvl}:
      P.err_if(fan_too_big(U32.is_eq(lvl, V.nolvl()), site, lvl),
        drop_ref(P.node(h, fan_hd(N.kcode(k), site, lvl), 0)))
    case T.TN{k, p}:
      match p:
        case V.PVal{v}:
          load.data(P.put(h, v), N.kcode(k))
        case V.PLvl{+l}:
          P.err_if(too_big(l), drop_ref(P.node(h, P.hd(N.kcode(k), l), 0)))
        case V.PLift{+n, +up, +by}:
          P.err_if(too_big(n) || U32.is_ge(by, 2147483648),
            drop_ref(P.node(h, P.hd(N.kcode(k), n), lift_word(up, by))))
        case _:
          drop_ref(P.node(h, bare_hd(N.kcode(k)), 0))

def load.nodes(ns: List<&2, T.TNode>, h: P.H) -> P.H:
  match ns:
    case Nil{}:
      h
    case Con{t, rest}:
      load.nodes(rest, load.node(h, t))

def tref(e: T.TEnd) -> U32:
  match e:
    case T.TE{+n, +p}:
      ((n << 2n : U32) + p : U32)

def load.links(ls: List<&2, T.TLink>, h: P.H) -> P.H:
  match ls:
    case Nil{}:
      h
    case Con{T.TL{x, y}, rest}:
      load.links(rest, P.link(h, tref(x), tref(y)))

def load.root(r: P.H & U32, +x: U32) -> P.H:
  (h, +root) = r
  P.link(h, root, x)

# the template's net, its exposed port linked to a root
def load(t: T.Tpl) -> P.H:
  match t:
    case T.Tpl{nodes, links, root, +size}:
      load.root(P.node(load.links(links, load.nodes(nodes, P.h_new())), P.hd(8, 0), 0), tref(root))

# Results
# =======

# the value at the root, if any: found by scanning for the root, which a
# control facing it may have moved
type Rs is Type:
  Rs{h: P.H, +root: U32}

def pick(b: Bool, +x: U32, +y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

def find.hit(r: P.H & U32, +n: U32, +at: U32) -> Rs:
  (h, +hdr) = r
  Rs{h, pick(U32.is_eq(at, P.nil()) && U32.is_eq(P.kind(hdr), 8), (n << 2n : U32), at)}

def find(k: Nat, +n: U32, rs: Rs) -> Rs:
  match k:
    case 0n:
      rs
    case 1n+p:
      match rs:
        case Rs{h, +at}:
          find(p, (n + 1 : U32), find.hit(P.rd(h, (n << 2n : U32)), n, at))

def value.v(r: P.H & V.Val) -> P.H & Maybe<&2, V.Val>:
  (h, v) = r
  (h, Some{v})

def value.w(r: P.H & U32, +hp: U32) -> P.H & Maybe<&2, V.Val>:
  (h, +w) = r
  value.v(P.peek(h, P.form(hp), P.fld(hp), w))

def value.is(data: Bool, h: P.H, +hp: U32, +pn: U32) -> P.H & Maybe<&2, V.Val>:
  match data:
    case True{}:
      value.w(P.rd(h, (pn + 2 : U32)), hp)
    case False{}:
      (h, None{})

def value.h(r: P.H & U32, +pn: U32) -> P.H & Maybe<&2, V.Val>:
  (h, +hp) = r
  value.is(U32.is_eq(P.rk(hp), 5), h, hp, pn)

def value.peer(r: P.H & U32) -> P.H & Maybe<&2, V.Val>:
  (h, +peer) = r
  value.h(P.rd(h, P.base(peer)), P.base(peer))

def value.none(none: Bool, h: P.H, +root: U32) -> P.H & Maybe<&2, V.Val>:
  match none:
    case True{}:
      (h, None{})
    case False{}:
      value.peer(P.rd(h, (root + 1 : U32)))

def value.at(rs: Rs) -> P.H & Maybe<&2, V.Val>:
  match rs:
    case Rs{h, +root}:
      value.none(U32.is_eq(root, P.nil()), h, root)

def result.st(r: P.H & P.HS) -> P.H & Maybe<&2, V.Val>:
  (h, st) = r
  match st:
    case P.HS{+itrs, +errs, +cap}:
      value.at(find(U32.to_nat(cap), 0, Rs{h, P.nil()}))

def result(h: P.H) -> P.H & Maybe<&2, V.Val>:
  result.st(P.stats(h))

def counts.st(r: P.H & P.HS) -> String:
  (h, st) = r
  match st:
    case P.HS{+itrs, +errs, +cap}:
      U32.show(itrs) ++ " interactions, " ++ U32.show(errs) ++ " errors, " ++ U32.show(cap) ++ " nodes capacity, " ++
        U32.show(P.h_live(h)) ++ " data entries live"

def counts(h: P.H) -> String:
  counts.st(P.stats(h))

def show_val(m: Maybe<&2, V.Val>) -> String:
  match m:
    case Some{v}:
      match v:
        case V.VNum{+n}:
          U32.show(n)
        case _:
          "a non-number"
    case None{}:
      "no value"

def report(r: P.H & Maybe<&2, V.Val>) -> String:
  (h, v) = r
  show_val(v) ++ ", " ++ counts(h)

# Auditing the table
# ==================

# live nodes holding a table entry (data nodes and calls of form 0),
# which a linear table matches with its live entries one for one
type Au is Type:
  Au{h: P.H, +n: U32}

def audit.one(+tab: Bool, +n: U32) -> U32:
  match tab:
    case True{}:
      (n + 1 : U32)
    case False{}:
      n

def audit.hit(r: P.H & U32, +n: U32) -> Au:
  (h, +hdr) = r
  Au{h, audit.one(is_data(P.rk(hdr)) && U32.is_eq(P.form(hdr), 0) && U32.is_ne(hdr, 0), n)}

def audit(k: Nat, +i: U32, au: Au) -> Au:
  match k:
    case 0n:
      au
    case 1n+p:
      match au:
        case Au{h, +n}:
          audit(p, (i + 1 : U32), audit.hit(P.rd(h, (i << 2n : U32)), n))

# the value at the root, interactions, errors, and whether the table's live
# entries match the nodes holding them
type KRes is Data:
  KRes{v: Maybe<&2, V.Val>, +itrs: U32, +errs: U32, +tab_ok: Bool}

def kres.st(r: P.H & P.HS, +n: U32, v: Maybe<&2, V.Val>) -> KRes:
  (h, st) = r
  match st:
    case P.HS{+itrs, +errs, +cap}:
      KRes{v, itrs, errs, P.h_ok(h, n)}

def kres.au(au: Au, v: Maybe<&2, V.Val>) -> KRes:
  match au:
    case Au{h, +n}:
      kres.st(P.stats(h), n, v)

def kres.h.st(r: P.H & P.HS, v: Maybe<&2, V.Val>) -> KRes:
  (h, st) = r
  match st:
    case P.HS{+itrs, +errs, +cap}:
      kres.au(audit(U32.to_nat(cap), 0, Au{h, 0}), v)

def kres.h(h: P.H, v: Maybe<&2, V.Val>) -> KRes:
  kres.h.st(P.stats(h), v)

def kres(r: P.H & Maybe<&2, V.Val>) -> KRes:
  (h, v) = r
  kres.h(h, v)

# reduce t as reduce does, the result as data
def run_t(t: T.Tpl, +fuel: Nat, +fast: Bool) -> KRes:
  kres(result(reduce_h(fuel, fast, load(t))))

# reduce t for at most fuel interactions, by the generated rewrites if
# fast, else by the interpreted table: value and counts
def reduce(t: T.Tpl, +fuel: Nat, +fast: Bool) -> String:
  report(result(reduce_h(fuel, fast, load(t))))

# 0, k 2 succ 0; 1, k 2 (plus 1) 0; 2, k 2 succ 0 with levels; 3,
# k 2 (fma 1 1) 0
def workload(+w: U32, +k: U32) -> T.Tpl:
  match w:
    case 1:
      X.t_pow_plus(k, 2)
    case 2:
      X.t_pow_lvl(k, 2)
    case 3:
      X.t_pow_fma(k, 2)
    case _:
      X.t_pow(k, 2)

def main.k(+k: U32, +fast: Bool, +w: U32) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    +res : String = reduce(workload(w, k), 268435456n, fast)
    +t1 : Nat <- IO.now()
    IO.print("kernel k " ++ U32.show(k) ++ ": " ++ res ++ " in " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")

def mode_w.p(p: Bool, +l: Bool, +f: Bool) -> U32:
  match p l f:
    case True{} _ _:
      1
    case False{} True{} _:
      2
    case False{} False{} True{}:
      3
    case False{} False{} False{}:
      0

def mode_w(+m: String) -> U32:
  mode_w.p(String.eq(m, "plus") || String.eq(m, "plusref"), String.eq(m, "lvl") || String.eq(m, "lvlref"),
    String.eq(m, "fma") || String.eq(m, "fmaref"))

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{p, r}:
      match r:
        case Con{a, r2}:
          match r2:
            case Con{+m, r3}:
              main.k(Maybe.default(&2, U32, U32.read(a), 10),
                Bool.not(String.eq(m, "ref") || String.eq(m, "plusref") || String.eq(m, "lvlref") || String.eq(m, "fmaref")), mode_w(m))
            case Nil{}:
              main.k(Maybe.default(&2, U32, U32.read(a), 10), True{}, 0)
        case Nil{}:
          IO.print("usage: kernel <k> [ref|plus|plusref|fma|fmaref|lvl|lvlref]")
    case Nil{}:
      IO.print("usage: kernel <k> [ref|plus|plusref|fma|fmaref|lvl|lvlref]")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
