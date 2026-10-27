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
# Level checks and fusion are not here yet.
#
#   kernel <k> [ref]   reduce `k 2 succ 0` (2^k), report value, counts,
#                      time; with ref, by the interpreted table alone

# Payloads
# ========

type PW is Data:
  PW{+f: U32, +w: U32}

def pw.apply(r: P.H & U32) -> P.H & PW:
  (h, +i) = r
  (h, PW{0, i})

# a new node's field and payload word, after the rule's source: A's and
# B's headers and payload words
def pay(s: R.Src, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & PW:
  match s:
    case R.SNone{}:
      (h, PW{0, 0})
    case R.SPayA{}:
      (h, PW{P.fld(ha), pa})
    case R.SPayB{}:
      (h, PW{P.fld(hb), pb})
    case R.SFanA{}:
      (h, PW{P.fld(ha), 0})
    case R.SFanB{}:
      (h, PW{P.fld(hb), 0})
    case R.SApply{}:
      pw.apply(P.apply(h, pa, pb))
    case R.SLiftA{}:
      (h, PW{P.lift(P.fld(hb), pb, P.fld(ha)), pa})
    case R.SLiftB{}:
      (h, PW{P.lift(P.fld(ha), pa, P.fld(hb)), pb})

# Applying a rule
# ===============

type Mk is Type:
  Mk{h: P.H, refs: List<&2, U32>}

def mk.add(r: P.H & U32, refs: List<&2, U32>) -> Mk:
  (h, +n) = r
  Mk{h, List.append(&2, U32, refs, [n])}

def mk.pw(pw: PW, h: P.H, +k: R.NodeKind, refs: List<&2, U32>) -> Mk:
  match pw:
    case PW{+f, +w}:
      mk.add(P.node(h, P.hd(N.kcode(k), f), w), refs)

def mk.node(r: P.H & PW, +k: R.NodeKind, refs: List<&2, U32>) -> Mk:
  (h, pw) = r
  mk.pw(pw, h, k, refs)

def mk.step(m: Mk, sp: R.Spec, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> Mk:
  match m:
    case Mk{h, refs}:
      match sp:
        case R.Spec{+k, s}:
          mk.node(pay(s, h, ha, hb, pa, pb), k, refs)

# allocate the rule's new nodes, in order
def make(xs: List<&2, R.Spec>, +ha: U32, +hb: U32, +pa: U32, +pb: U32, m: Mk) -> Mk:
  match xs:
    case Nil{}:
      m
    case Con{sp, t}:
      make(t, ha, hb, pa, pb, mk.step(m, sp, ha, hb, pa, pb))

def resolve(+x: N.Ext, +refs: List<&2, U32>, e: R.End) -> U32:
  match e:
    case R.Ext{i}:
      N.ext_at(x, i)
    case R.New{j, p}:
      (N.nth(refs, j) + U32.from_nat(p) : U32)

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
def link_plain(ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +a: U32, +b: U32, h: P.H) -> P.H:
  match ls:
    case Nil{}:
      h
    case Con{R.Link{+u, +v}, t}:
      link_plain(t, x, refs, a, b,
        link_if(Bool.not(internal(x, a, b, u) || internal(x, a, b, v)), h, resolve(x, refs, u), resolve(x, refs, v)))

def pair_link(bad: Bool, +u: R.End, +v: R.End, +x: N.Ext, +refs: List<&2, U32>, h: P.H) -> P.H:
  match bad:
    case True{}:
      P.h_err(h)
    case False{}:
      P.link(h, resolve(x, refs, u), resolve(x, refs, v))

def pair_ends(oi: Maybe<&2, R.End>, oj: Maybe<&2, R.End>, +x: N.Ext, +refs: List<&2, U32>, +a: U32, +b: U32, h: P.H) -> P.H:
  match oi oj:
    case Some{+u} Some{+v}:
      pair_link(internal(x, a, b, u) || internal(x, a, b, v), u, v, x, refs, h)
    case _ _:
      P.h_err(h)

def pair_go(lt: Bool, +i: Nat, +j: Nat, +ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +a: U32, +b: U32, h: P.H) -> P.H:
  match lt:
    case True{}:
      pair_ends(N.other(ls, i), N.other(ls, j), x, refs, a, b, h)
    case False{}:
      h

def pair_at(pt: Maybe<&2, Nat>, +i: Nat, +ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +a: U32, +b: U32, h: P.H) -> P.H:
  match pt:
    case None{}:
      h
    case Some{+j}:
      pair_go(Nat.is_lt(i, j), i, j, ls, x, refs, a, b, h)

# an external peer that is a port of the redex stands for another
# external: join what the rule links to the two (net.bend's link_pairs)
def link_pairs(n: Nat, +i: Nat, +ls: List<&2, R.Link>, +x: N.Ext, +refs: List<&2, U32>, +a: U32, +b: U32, h: P.H) -> P.H:
  match n:
    case 0n:
      h
    case 1n+p:
      link_pairs(p, 1n+i, ls, x, refs, a, b, pair_at(N.partner(N.ext_at(x, i), a, b), i, ls, x, refs, a, b, h))

def wire.made(m: Mk, +ls: List<&2, R.Link>, +x: N.Ext, +a: U32, +b: U32) -> P.H:
  match m:
    case Mk{h, +refs}:
      link_pairs(4n, 0n, ls, x, refs, a, b, link_plain(ls, x, refs, a, b, h))

# replace the redex a >< b by the rule's nodes and links
def wire(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +x: N.Ext) -> P.H:
  wire.made(make(xs, ha, hb, pa, pb, Mk{P.fresh2(h, a, b), Nil{}}), ls, x, a, b)

def apply_rule(r: R.Rule, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> P.H:
  match r:
    case R.RWire{xs, ls}:
      wire(h, a, b, ha, hb, pa, pb, xs, ls, x)
    case R.RStuck{}:
      P.err_if(U32.is_ne(P.kind(ha), 8), h)

# Interaction
# ===========

def kof(+h: U32) -> R.NodeKind:
  N.kof(P.kind(h))

# ports, by kind code (generated from R.arity)
def arity(+h: U32) -> U32:
  KR.kind_arity(P.kind(h))

def aux_or_nil(b: Bool, +l: U32) -> U32:
  match b:
    case True{}:
      l
    case False{}:
      P.nil()

def payw.go(three: Bool, +w3: U32) -> U32:
  match three:
    case True{}:
      0
    case False{}:
      w3

# a node's payload word: word 3, in a node with fewer than three ports
def payw(+h: U32, +w3: U32) -> U32:
  payw.go(U32.is_ge(arity(h), 3), w3)

def ctl_eq(+ha: U32, +hb: U32, +pa: U32, +pb: U32) -> Bool:
  U32.is_eq(P.fld(ha), P.fld(hb)) && U32.is_eq(pa, pb)

def test.k(+ka: U32, +kb: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  match ka kb:
    case 3 4:
      (h, U32.is_eq(P.fld(ha), P.fld(hb)))
    case 2 5:
      P.data_is_fn(h, pb)
    case 2 1:
      (h, U32.is_eq(P.fld(ha), P.fld(hb)))
    case 10 11:
      (h, ctl_eq(ha, hb, pa, pb))
    case _ _:
      (h, False{})

# the payload test the rule takes (net.bend's rule_test)
def test(h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  test.k(P.kind(ha), P.kind(hb), h, ha, hb, pa, pb)

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
      KR.rewrite(P.kind(ha), P.kind(hb), t, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def go.which(gen: Bool, +t: Bool, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> P.H:
  match gen:
    case True{}:
      go.gen(t, h, a, b, ha, hb, pa, pb, x)
    case False{}:
      apply_rule(R.rule(kof(ha), kof(hb), t), h, a, b, ha, hb, pa, pb, x)

# the generated rewrite, or the interpreted table: for a redex whose
# external peers include its own ports, or when `fast` is off
def go.rule(r: P.H & Bool, +fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +x: N.Ext) -> P.H:
  (h, +t) = r
  go.which(fast && Bool.not(any_partner(x, a, b)), t, h, a, b, ha, hb, pa, pb, x)

def go.ext(+fast: Bool, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32, +b1: U32, +b2: U32, h: P.H) -> P.H:
  go.rule(test(h, ha, hb, payw(ha, a2), payw(hb, b2)), fast, a, b, ha, hb, payw(ha, a2), payw(hb, b2),
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
# word 3 the payload word.
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
  ori(KR.kind_neg(P.kind(hx)), h, fast, x, y, hx, hy)

def int.x(r: P.H & U32, +fast: Bool, +x: U32, +y: U32) -> P.H:
  (h, +hx) = r
  int.y(P.rd(h, y), fast, x, y, hx)

def interact(h: P.H, +fast: Bool, +x: U32, +y: U32) -> P.H:
  int.x(P.rd(h, x), fast, x, y)

# reduce active pairs, newest first, until none is left or fuel runs out
def run(n: Nat, +fast: Bool, pp: P.Pop) -> P.H:
  match n:
    case 0n:
      P.unpop(pp)
    case 1n+p:
      match pp:
        case P.Pop{h, +x, +y, +ok}:
          match ok:
            case True{}:
              run(p, fast, P.pop(interact(h, fast, x, y)))
            case False{}:
              h

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

def load.data(r: P.H & U32, +k: U32) -> P.H:
  (h, +w) = r
  drop_ref(P.node(h, P.hd(k, 0), w))

def fan_field.go(none: Bool, +site: U32, +lvl: U32) -> U32:
  match none:
    case True{}:
      site
    case False{}:
      lvl

# a fan's field: its level, or for a net built without levels its site
def fan_field(+site: U32, +lvl: U32) -> U32:
  fan_field.go(U32.is_eq(lvl, V.nolvl()), site, lvl)

def load.node(h: P.H, t: T.TNode) -> P.H:
  match t:
    case T.TF{k, +site, +lvl}:
      drop_ref(P.node(h, P.hd(N.kcode(k), fan_field(site, lvl)), 0))
    case T.TN{k, p}:
      match p:
        case V.PVal{v}:
          load.data(P.put(h, v), N.kcode(k))
        case V.PLvl{+l}:
          drop_ref(P.node(h, P.hd(N.kcode(k), l), 0))
        case V.PLift{+n, +up, +by}:
          drop_ref(P.node(h, P.hd(N.kcode(k), n), lift_word(up, by)))
        case _:
          drop_ref(P.node(h, P.hd(N.kcode(k), 0), 0))

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

# the value at the root, if a number: found by scanning for the root,
# which a control facing it may have moved
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

def value.p(r: P.H & U32) -> P.H & Maybe<&2, V.Val>:
  (h, +w) = r
  value.v(P.val_of(h, w))

def value.is(data: Bool, h: P.H, +pn: U32) -> P.H & Maybe<&2, V.Val>:
  match data:
    case True{}:
      value.p(P.rd(h, (pn + 3 : U32)))
    case False{}:
      (h, None{})

def value.h(r: P.H & U32, +pn: U32) -> P.H & Maybe<&2, V.Val>:
  (h, +hp) = r
  value.is(U32.is_eq(P.kind(hp), 5), h, pn)

def value.peer(r: P.H & U32) -> P.H & Maybe<&2, V.Val>:
  (h, +peer) = r
  value.h(P.rd(h, (peer .&. 4294967292 : U32)), (peer .&. 4294967292 : U32))

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

def result(h: P.H) -> P.H & Maybe<&2, V.Val>:
  match h:
    case P.H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      value.at(find(U32.to_nat(fresh), 0, Rs{P.H{w, fs, nf, fresh, rs, nr, itrs, errs, dt}, P.nil()}))

def counts(h: P.H) -> String:
  match h:
    case P.H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      U32.show(itrs) ++ " interactions, " ++ U32.show(errs) ++ " errors, " ++ U32.show(fresh) ++ " nodes at most"

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

# the value at the root, interactions, errors
type KRes is Data:
  KRes{v: Maybe<&2, V.Val>, +itrs: U32, +errs: U32}

def kres.h(h: P.H, v: Maybe<&2, V.Val>) -> KRes:
  match h:
    case P.H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      KRes{v, itrs, errs}

def kres(r: P.H & Maybe<&2, V.Val>) -> KRes:
  (h, v) = r
  kres.h(h, v)

# reduce t as reduce does, the result as data
def run_t(t: T.Tpl, +fuel: Nat, +fast: Bool) -> KRes:
  kres(result(run(fuel, fast, P.pop(load(t)))))

# reduce t for at most fuel interactions, by the generated rewrites if
# fast, else by the interpreted table: value and counts
def reduce(t: T.Tpl, +fuel: Nat, +fast: Bool) -> String:
  report(result(run(fuel, fast, P.pop(load(t)))))

def main.k(+k: U32, +fast: Bool) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    +res : String = reduce(X.t_pow(k, 2), 268435456n, fast)
    +t1 : Nat <- IO.now()
    IO.print("kernel k " ++ U32.show(k) ++ ": " ++ res ++ " in " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{p, r}:
      match r:
        case Con{a, r2}:
          match r2:
            case Con{m, r3}:
              main.k(Maybe.default(&2, U32, U32.read(a), 10), Bool.not(String.eq(m, "ref")))
            case Nil{}:
              main.k(Maybe.default(&2, U32, U32.read(a), 10), True{})
        case Nil{}:
          IO.print("usage: kernel <k> [ref]")
    case Nil{}:
      IO.print("usage: kernel <k> [ref]")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
