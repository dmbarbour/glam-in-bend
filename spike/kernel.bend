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
#   kernel <k> [succ|ref|plus|plusref|lvl|lvlref|fma|fmaref|kpow|knum|komega|whnf] [lazy]
#       reduce `k 2 succ 0` (2^k) built without levels; with plus
#       `k 2 (plus 1) 0`, adding by a partial application in a node; with
#       fma `k 2 (fma 1 1) 0`, by one in the data table; with lvl
#       `k 2 succ 0` with levels, as terms.py lowers it (k >= 2); kpow
#       `K 0 (k 2 succ 0)`; knum `K 0 #k`; komega `K 0 ((\z. z z) (\z. z
#       z))`; whnf `#k succ`, a function. Report value, counts, time; with
#       ref, by the interpreted table alone; with lazy, on demand (see
#       Demand), the state it ends in and the nodes left

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

# Demand
# ======

# Reducing toward the interface (net-demand-whnf; HeapModel's "Forcing"):
# from node 0, follow principal ports. Where one faces another node's
# auxiliary port, that node must reduce first, and the walk goes on from
# it, keeping a path; where it faces a principal port, that pair is next.
# Only the path's last node can be in a pair, the others facing auxiliary
# ports, so a rewrite there leaves the rest of the path as it was: the
# walk resumes from the node below. A rewrite's new pairs go on the pair
# stack. Erasers' pairs are reduced from it at once, and end: each removes
# a node that is no eraser and makes at most two erasers, or removes two
# erasers. Other pairs stay in the net, for the walk to find where they
# lie on its path, garbage where they do not. Done when node 0 faces a
# principal port but a control's: the value there (an error value or a
# superposition reads as none). A pair on the path stuck by its rule stops
# the walk; so does one needing another cell, an application or a strict
# call meeting a table entry that is a handle, the need recorded.

# the path below its last node, top, and its length; interactions; the
# state, 0 going, 1 done, 2 needing a lazy value, 3 stuck, 4 out of fuel;
# for a need, the handle and the data node holding it
type D is Type:
  D{h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +st: U32, +lz: U32, +at: U32}

def d.go(h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32) -> D:
  D{h, path, top, depth, n, 0, 0, 0}

def d.stop(h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +st: U32) -> D:
  D{h, path, top, depth, n, st, 0, 0}

def is_era(+k: U32) -> Bool:
  U32.is_eq(k, 6) || U32.is_eq(k, 7)

# Draining the stack: the net and the interactions so far
type Dn is Type:
  Dn{h: P.H, +n: U32}

type Dq is Type:
  Dq{pp: P.Pop, +n: U32}

# a pair from the stack, off the path: an eraser's reduced, others left
def dr.go(e: Bool, h: P.H, +n: U32, +x: U32, +y: U32) -> Dq:
  match e:
    case True{}:
      Dq{P.pop(interact(h, True{}, x, y)), (n + 1 : U32)}
    case False{}:
      Dq{P.pop(h), n}

def dr.hy(r: P.H & U32, +n: U32, +x: U32, +y: U32, +hx: U32) -> Dq:
  (h, +hy) = r
  dr.go(is_era(P.rk(hx)) || is_era(P.rk(hy)), h, n, x, y)

def dr.hx(r: P.H & U32, +n: U32, +x: U32, +y: U32) -> Dq:
  (h, +hx) = r
  dr.hy(P.rd(h, y), n, x, y, hx)

# the path's last node's pair is the walk's to take
def dr.pair(mine: Bool, h: P.H, +n: U32, +x: U32, +y: U32) -> Dq:
  match mine:
    case True{}:
      Dq{P.pop(h), n}
    case False{}:
      dr.hx(P.rd(h, x), n, x, y)

# the pairs the last rewrite made, and the erasures they lead to; what
# k leaves is drained before the walk's next step
def drain(k: Nat, +top: U32, q: Dq) -> Dn:
  match k:
    case 0n:
      match q:
        case Dq{pp, +n}:
          Dn{P.unpop(pp), n}
    case 1n+p:
      match q:
        case Dq{pp, +n}:
          match pp:
            case P.Pop{h, +x, +y, +ok}:
              match ok:
                case True{}:
                  drain(p, top, dr.pair(U32.is_eq(x, top) || U32.is_eq(y, top), h, n, x, y))
                case False{}:
                  Dn{h, n}

def wk.pop(h: P.H, path: List<&2, U32>, +depth: U32, +n: U32) -> D:
  match path:
    case Con{+p, rest}:
      d.go(h, rest, p, (depth - 1 : U32), n)
    case Nil{}:
      d.go(h, Nil{}, 0, 0, n)

def wk.past(gone: Bool, h: P.H, path: List<&2, U32>, +p: U32, +depth: U32, +n: U32) -> D:
  match gone:
    case True{}:
      wk.pop(h, path, depth, n)
    case False{}:
      d.go(h, path, p, depth, n)

def wk.hp(r: P.H & U32, path: List<&2, U32>, +p: U32, +depth: U32, +n: U32) -> D:
  (h, +hp) = r
  wk.past(U32.is_eq(hp, 0), h, path, p, depth, n)

# the path's last node rewritten: the walk goes back to the one below, or
# past it where fusing controls freed it. Fusion tries only the links a
# rule made, the node below's is one, and a fusion there may free that
# node (a lift facing the source keeps the one behind it, a control facing
# consumers the one ahead); at its auxiliary ports a fusion keeps it, and
# the node below it is not touched, its link made by no rule.
def wk.back(h: P.H, path: List<&2, U32>, +depth: U32, +n: U32) -> D:
  match path:
    case Con{+p, rest}:
      wk.hp(P.rd(h, p), rest, p, (depth - 1 : U32), n)
    case Nil{}:
      d.go(h, Nil{}, 0, 0, n)

def wk.hb.go(gone: Bool, h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32) -> D:
  match gone:
    case True{}:
      wk.back(h, path, depth, (n + 1 : U32))
    case False{}:
      d.stop(h, path, top, depth, n, 3)

def wk.hb(r: P.H & U32, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32) -> D:
  (h, +hb) = r
  wk.hb.go(U32.is_eq(hb, 0), h, path, top, depth, n)

# rewrite a >< b, unless its rule leaves it as it is (KR.stuck_by). Where
# the payload test decides that, the rule makes at most one node when it
# rewrites (law rules_tested_small) and fresh2 frees b first, so the first
# new node takes a's slot: b's slot is free after a rewrite, as it was if
# stuck. The test itself is left to the rewrite, its only caller.
def wk.rw(+sb: U32, h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match sb:
    case 0:
      wk.back(go(h, True{}, a, b, ha, hb), path, depth, (n + 1 : U32))
    case 1:
      d.stop(h, path, top, depth, n, 3)
    case _:
      wk.hb(P.rd(go(h, True{}, a, b, ha, hb), b), path, top, depth, n)

def nd.lz(z: P.Lz, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match z:
    case P.Lz{h, +lazy, +k}:
      match lazy:
        case True{}:
          D{h, path, top, depth, n, 2, k, b}
        case False{}:
          wk.rw(KR.stuck_by(P.rk(ha), P.rk(hb)), h, path, top, depth, n, a, b, ha, hb)

def nd.pb(r: P.H & U32, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  (h, +pb) = r
  nd.lz(P.val_lazy(h, P.form(hb), pb), path, top, depth, n, a, b, ha, hb)

def nd.go(chk: Bool, h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match chk:
    case True{}:
      nd.pb(P.rd(h, (b + 2 : U32)), path, top, depth, n, a, b, ha, hb)
    case False{}:
      wk.rw(KR.stuck_by(P.rk(ha), P.rk(hb)), h, path, top, depth, n, a, b, ha, hb)

# an application or a strict call meeting data in the table
def may_need(+ha: U32, +hb: U32) -> Bool:
  (U32.is_eq(P.rk(ha), 2) || U32.is_eq(P.rk(ha), 9)) && U32.is_eq(P.rk(hb), 5) && U32.is_eq(P.form(hb), 0)

def wk.ori(neg: Bool, h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +x: U32, +y: U32, +hx: U32, +hy: U32) -> D:
  match neg:
    case True{}:
      nd.go(may_need(hx, hy), h, path, top, depth, n, x, y, hx, hy)
    case False{}:
      nd.go(may_need(hy, hx), h, path, top, depth, n, y, x, hy, hx)

def wk.hy(r: P.H & U32, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +y: U32, +hx: U32) -> D:
  (h, +hy) = r
  wk.ori(KR.kind_neg(P.rk(hx)), h, path, top, depth, n, top, y, hx, hy)

def wk.hx(r: P.H & U32, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +y: U32) -> D:
  (h, +hx) = r
  wk.hy(P.rd(h, y), path, top, depth, n, y, hx)

# node 0 facing a principal port: a control's moves past it (the root's
# rule keeps node 0), anything else is the value
def wk.root.go(c: Bool, h: P.H, path: List<&2, U32>, +depth: U32, +n: U32, +y: U32) -> D:
  match c:
    case True{}:
      d.go(interact(h, True{}, 0, y), path, 0, depth, (n + 1 : U32))
    case False{}:
      d.stop(h, path, 0, depth, n, 1)

def wk.root(r: P.H & U32, path: List<&2, U32>, +depth: U32, +n: U32, +y: U32) -> D:
  (h, +hy) = r
  wk.root.go(U32.is_eq(P.rk(hy), 11), h, path, depth, n, y)

def wk.pair(root: Bool, h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +y: U32) -> D:
  match root:
    case True{}:
      wk.root(P.rd(h, y), path, depth, n, y)
    case False{}:
      wk.hx(P.rd(h, top), path, top, depth, n, y)

# a path longer than any net's nodes has gone round a cycle
def deep_cap() -> U32:
  4194304

def wk.deeper(over: Bool, h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +q: U32) -> D:
  match over:
    case True{}:
      d.stop(h, path, top, depth, n, 3)
    case False{}:
      d.go(h, Con{top, path}, P.base(q), (depth + 1 : U32), n)

def wk.q.go(nil: Bool, +pr: Bool, h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +q: U32) -> D:
  match nil pr:
    case True{} _:
      d.stop(h, path, top, depth, n, 3)
    case False{} True{}:
      wk.pair(U32.is_eq(top, 0), h, path, top, depth, n, q)
    case False{} False{}:
      wk.deeper(U32.is_ge(depth, deep_cap()), h, path, top, depth, n, q)

# what the path's last node's principal port faces
def wk.q(r: P.H & U32, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32) -> D:
  (h, +q) = r
  wk.q.go(U32.is_eq(q, P.nil()), U32.is_eq(P.port(q), 0), h, path, top, depth, n, q)

# one step of the walk, the stack drained
def d.walk(dn: Dn, path: List<&2, U32>, +top: U32, +depth: U32) -> D:
  match dn:
    case Dn{h, +n}:
      wk.q(P.rd(h, (top + 1 : U32)), path, top, depth, n)

def d.out(+st: U32) -> U32:
  match st:
    case 0:
      4
    case _:
      st

def d.end(d: D) -> D:
  match d:
    case D{h, path, +top, +depth, +n, +st, +lz, +at}:
      D{h, path, top, depth, n, d.out(st), lz, at}

# reduce toward the interface for at most k steps
def demand(k: Nat, d: D) -> D:
  match k:
    case 0n:
      d.end(d)
    case 1n+p:
      match d:
        case D{h, path, +top, +depth, +n, +st, +lz, +at}:
          match st:
            case 0:
              demand(p, d.walk(drain(16777216n, top, Dq{P.pop(h), n}), path, top, depth))
            case _:
              D{h, path, top, depth, n, st, lz, at}

def d.start(h: P.H) -> D:
  d.go(h, Nil{}, 0, 0, 0)

def resume.put(r: P.H & P.PW, +at: U32) -> P.H:
  (h, pw) = r
  match pw:
    case P.PW{+m, +f, +w}:
      P.wr(P.wr(h, at, P.hd2(5, m, f)), (at + 2 : U32), w)

def resume.pb(r: P.H & U32, +at: U32, +hb: U32, v: V.Val) -> P.H:
  (h, +pb) = r
  resume.put(P.put(P.drop(h, P.form(hb), pb), v), at)

def resume.hb(r: P.H & U32, +at: U32, v: V.Val) -> P.H:
  (h, +hb) = r
  resume.pb(P.rd(h, (at + 2 : U32)), at, hb, v)

# a need met: the data node holding the handle holds v instead, and the
# walk goes on where it stopped
def resume(d: D, v: V.Val) -> D:
  match d:
    case D{h, path, +top, +depth, +n, +st, +lz, +at}:
      d.go(resume.hb(P.rd(h, at), at, v), path, top, depth, n)

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

# a template's node n is the net's node n + 1, after the interface
def tref(e: T.TEnd) -> U32:
  match e:
    case T.TE{+n, +p}:
      (((n + 1 : U32) << 2n : U32) + p : U32)

def load.links(ls: List<&2, T.TLink>, h: P.H) -> P.H:
  match ls:
    case Nil{}:
      h
    case Con{T.TL{x, y}, rest}:
      load.links(rest, P.link(h, tref(x), tref(y)))

def load.root(r: P.H & U32, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +x: U32) -> P.H:
  (h, +root) = r
  P.link(load.links(links, load.nodes(nodes, h)), root, x)

# the template's net, its exposed port linked to the interface: node 0,
# made first, which keeps its slot for good (HeapModel's "Nets")
def load(t: T.Tpl) -> P.H:
  match t:
    case T.Tpl{nodes, links, root, +size}:
      load.root(P.node(P.h_new(), P.hd(8, 0), 0), nodes, links, tref(root))

# Results
# =======

# the value read off the root, as glam sees it (V.norm)
def value.v(r: P.H & V.Val) -> P.H & Maybe<&2, V.Val>:
  (h, v) = r
  (h, Some{V.norm(v)})

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

def value.root(r: P.H & U32) -> P.H & Maybe<&2, V.Val>:
  (h, +hdr) = r
  value.none(U32.is_ne(P.kind(hdr), 8), h, 0)

# the value at the interface, node 0: its peer's, when that is data
def result(h: P.H) -> P.H & Maybe<&2, V.Val>:
  value.root(P.rd(h, 0))

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

def table_str(+ok: Bool) -> String:
  match ok:
    case True{}:
      ""
    case False{}:
      ", TABLE MISMATCH"

def need_str(+need: Bool, +lz: U32) -> String:
  match need:
    case True{}:
      " cell " ++ U32.show(lz)
    case False{}:
      ""

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

# Results of demand
# =================

def live.hit(r: P.H & U32, +n: U32) -> Au:
  (h, +hdr) = r
  Au{h, audit.one(U32.is_ne(hdr, 0), n)}

def live(k: Nat, +i: U32, au: Au) -> Au:
  match k:
    case 0n:
      au
    case 1n+p:
      match au:
        case Au{h, +n}:
          live(p, (i + 1 : U32), live.hit(P.rd(h, (i << 2n : U32)), n))

# the nodes still live, the interface's among them
def live_nodes.st(r: P.H & P.HS) -> Au:
  (h, st) = r
  match st:
    case P.HS{+itrs, +errs, +cap}:
      live(U32.to_nat(cap), 0, Au{h, 0})

# the value a cell k holds, for a test meeting needs: vals's entry k, a
# unit past its end
def val_at(vs: List<&2, V.Val>, +k: U32) -> V.Val:
  match vs:
    case Nil{}:
      V.VUnit{}
    case Con{v, t}:
      match k:
        case 0:
          v
        case _:
          val_at(t, (k - 1 : U32))

# demand, each need met from vals, at most k times
def force(k: Nat, +fuel: Nat, +vals: List<&2, V.Val>, d: D) -> D:
  match k:
    case 0n:
      d
    case 1n+p:
      match d:
        case D{h, path, +top, +depth, +n, +st, +lz, +at}:
          match st:
            case 2:
              force(p, fuel, vals, demand(fuel, resume(D{h, path, top, depth, n, st, lz, at}, val_at(vals, lz))))
            case _:
              D{h, path, top, depth, n, st, lz, at}

# a demand's end: the result as reduce_h's, its state, the handle needed,
# the nodes left
type DRes is Data:
  DRes{r: KRes, +st: U32, +lz: U32, +live: U32}

def dres.au(au: Au, +st: U32, +lz: U32) -> DRes:
  match au:
    case Au{h, +n}:
      DRes{kres(result(h)), st, lz, n}

def dres.h(h: P.H, +st: U32, +lz: U32) -> DRes:
  dres.au(live_nodes.st(P.stats(h)), st, lz)

def dres(d: D) -> DRes:
  match d:
    case D{h, path, +top, +depth, +n, +st, +lz, +at}:
      dres.h(P.count(h, n), st, lz)

# reduce t toward weak head normal form for at most fuel steps, its needs
# met from vals, at most 64
def run_d(t: T.Tpl, +fuel: Nat, +vals: List<&2, V.Val>) -> DRes:
  dres(force(64n, fuel, vals, demand(fuel, d.start(load(t)))))

def st_name(+st: U32) -> String:
  match st:
    case 1:
      "done"
    case 2:
      "needs"
    case 3:
      "stuck"
    case 4:
      "out of fuel"
    case _:
      "going"

def kres_str(r: KRes) -> String:
  match r:
    case KRes{v, +itrs, +errs, +ok}:
      show_val(v) ++ ", " ++ U32.show(itrs) ++ " interactions, " ++ U32.show(errs) ++ " errors" ++ table_str(ok)

def dres_str(r: DRes) -> String:
  match r:
    case DRes{k, +st, +lz, +live}:
      st_name(st) ++ need_str(U32.is_eq(st, 2), lz) ++ ": " ++ kres_str(k) ++ ", " ++ U32.show(live) ++ " nodes live"

# Workloads
# =========

# 0, k 2 succ 0; 1, k 2 (plus 1) 0; 2, k 2 succ 0 with levels; 3,
# k 2 (fma 1 1) 0; 4, K 0 (k 2 succ 0); 5, K 0 applied to the numeral k;
# 6, K 0 applied to a term with no normal form; 7, the numeral k applied
# to succ, a function
def workload(+w: U32, +k: U32) -> T.Tpl:
  match w:
    case 1:
      X.t_pow_plus(k, 2)
    case 2:
      X.t_pow_lvl(k, 2)
    case 3:
      X.t_pow_fma(k, 2)
    case 4:
      X.t_k_pow(k)
    case 5:
      X.t_k_num(k)
    case 6:
      X.t_k_omega()
    case 7:
      X.t_whnf(k)
    case _:
      X.t_pow(k, 2)

# reduce the workload fully, or on demand
def main.run(+lazy: Bool, t: T.Tpl, +fast: Bool) -> String:
  match lazy:
    case True{}:
      dres_str(run_d(t, 268435456n, Nil{}))
    case False{}:
      reduce(t, 268435456n, fast)

def main.k(+k: U32, +fast: Bool, +w: U32, +lazy: Bool) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    +res : String = main.run(lazy, workload(w, k), fast)
    +t1 : Nat <- IO.now()
    IO.print("kernel k " ++ U32.show(k) ++ ": " ++ res ++ " in " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")

# a mode: its name, workload, and whether by the generated rewrites
type Md is Data:
  Md{name: String, +w: U32, +fast: Bool}

def modes() -> List<&2, Md>:
  [Md{"succ", 0, True{}}, Md{"ref", 0, False{}}, Md{"plus", 1, True{}}, Md{"plusref", 1, False{}},
   Md{"lvl", 2, True{}}, Md{"lvlref", 2, False{}}, Md{"fma", 3, True{}}, Md{"fmaref", 3, False{}},
   Md{"kpow", 4, True{}}, Md{"knum", 5, True{}}, Md{"komega", 6, True{}}, Md{"whnf", 7, True{}}]

def mode_of.hit(hit: Bool, md: Md, r: Maybe<&2, Md>) -> Maybe<&2, Md>:
  match hit:
    case True{}:
      Some{md}
    case False{}:
      r

def mode_of(ms: List<&2, Md>, +m: String) -> Maybe<&2, Md>:
  match ms:
    case Nil{}:
      None{}
    case Con{Md{+name, +w, +fast}, t}:
      mode_of.hit(String.eq(name, m), Md{name, w, fast}, mode_of(t, m))

def usage() -> String:
  "usage: kernel <k> [succ|ref|plus|plusref|lvl|lvlref|fma|fmaref|kpow|knum|komega|whnf] [lazy]"

def main.mode(md: Maybe<&2, Md>, +k: U32, +lazy: Bool) -> IO(Unit):
  match md:
    case Some{Md{name, +w, +fast}}:
      main.k(k, fast, w, lazy)
    case None{}:
      IO.print(usage())

def main.rest(+k: U32, xs: List<String>) -> IO(Unit):
  match xs:
    case Nil{}:
      main.k(k, True{}, 0, False{})
    case Con{+m, r}:
      match r:
        case Nil{}:
          main.mode(mode_of(modes(), m), k, False{})
        case Con{+l, r2}:
          main.mode(mode_of(modes(), m), k, String.eq(l, "lazy"))

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{p, r}:
      match r:
        case Con{a, r2}:
          main.rest(Maybe.default(&2, U32, U32.read(a), 10), r2)
        case Nil{}:
          IO.print(usage())
    case Nil{}:
      IO.print(usage())

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
