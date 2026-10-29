import Base
import ./rules.bend as R

# The net's wiring as a model in Nat, for laws
# (`heap-strategies.net.wiring` in docs/plans/HeapModel_2026-10-27.md):
# node kinds, and links between ports, a port being a node and a port
# number. A net is wired when its links' ends name no port twice, every end
# is a port of a live node, and every port of every live node is an end:
# each live port is referenced exactly once, and nothing else is. A rewrite
# replaces an active pair a >< b by the rule's new nodes, joined to the
# peers of the pair's auxiliary ports as the rule's links say; the law
# rewrite_wired says a rule exact by R.exact keeps a net wired, so with
# rules_exact every rewrite of the rule table does.
#
# A peer may be a port of the pair itself, a's auxiliary port linked to
# b's or to a's other: a pattern (R.Pat) says which, the focused net then
# lists only the peers outside (fends_in), and the kernel joins what the
# rule links to the two ends of each such link (R.contract, mirroring
# knet.bend's link_pairs), or reports an error; rules_keep_wired_in says
# every step that reports none keeps a net wired. Simplified from the
# kernel: new nodes are appended rather than taken from the free list
# (freelist.bend models that).

type Pt is Data:
  Pt{n: Nat, p: Nat}

type Ln is Data:
  Ln{x: Pt, y: Pt}

def pt_eq(a: Pt, b: Pt) -> Bool:
  match a b:
    case Pt{m, p} Pt{n, q}:
      R.nat_eq(m, n) && R.nat_eq(p, q)

# p below n, matching n first so that nothing is below 0
def under(n: Nat, p: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+k:
      match p:
        case 0n:
          True{}
        case 1n+q:
          under(k, q)

def below(p: Nat, n: Nat) -> Bool:
  under(n, p)

# node n's kind, free past the end
def kind_at(ks: List<&2, R.NodeKind>, n: Nat) -> R.NodeKind:
  match ks n:
    case Nil{} _:
      R.KFree{}
    case Con{k, t} 0n:
      k
    case Con{k, t} 1n+m:
      kind_at(t, m)

# node n's kind replaced by v, nothing past the end
def set(ks: List<&2, R.NodeKind>, n: Nat, v: R.NodeKind) -> List<&2, R.NodeKind>:
  match ks n:
    case Nil{} _:
      Nil{}
    case Con{k, t} 0n:
      Con{v, t}
    case Con{k, t} 1n+m:
      Con{k, set(t, m, v)}

# a port of a live node: below its kind's arity
def live(+ks: List<&2, R.NodeKind>, x: Pt) -> Bool:
  match x:
    case Pt{n, p}:
      below(p, R.arity(kind_at(ks, n)))

def mem(+q: Pt, xs: List<&2, Pt>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      pt_eq(x, q) || mem(q, t)

def nodup(xs: List<&2, Pt>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +t}:
      Bool.not(mem(x, t)) && nodup(t)

def all_live(+ks: List<&2, R.NodeKind>, xs: List<&2, Pt>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      live(ks, x) && all_live(ks, t)

# node m's ports below k are all in xs
def ports_in(+m: Nat, k: Nat, +xs: List<&2, Pt>) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n++p:
      mem(Pt{m, p}, xs) && ports_in(m, p, xs)

# every live port of the nodes below n is in xs
def covered(+ks: List<&2, R.NodeKind>, n: Nat, +xs: List<&2, Pt>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n++m:
      ports_in(m, R.arity(kind_at(ks, m)), xs) && covered(ks, m, xs)

# xs, a net's links' ends, name each live port once and nothing else
def wired(+ks: List<&2, R.NodeKind>, +xs: List<&2, Pt>) -> Bool:
  nodup(xs) && (all_live(ks, xs) && covered(ks, List.length(&2, R.NodeKind, ks), xs))

def ends(ls: List<&2, Ln>) -> List<&2, Pt>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Ln{x, y}, t}:
      x <> (y <> ends(t))

# node n's ports below k
def ports(+n: Nat, k: Nat) -> List<&2, Pt>:
  match k:
    case 0n:
      Nil{}
    case 1n++p:
      Pt{n, p} <> ports(n, p)

# the peers of a pair's auxiliary ports, as the rule's Ext ends number
# them: 0 and 1 link a's ports 1 and 2, 2 and 3 b's
type Peers is Data:
  Peers{e0: Pt, e1: Pt, e2: Pt, e3: Pt}

def peer(i: Nat, es: Peers) -> Pt:
  match i es:
    case 0n Peers{e0, e1, e2, e3}:
      e0
    case 1n Peers{e0, e1, e2, e3}:
      e1
    case 2n Peers{e0, e1, e2, e3}:
      e2
    case _ Peers{e0, e1, e2, e3}:
      e3

# where a rule's end lands: on a peer, or on port p of new node j, the
# new nodes numbered from n0
def sig(+n0: Nat, +es: Peers, x: R.End) -> Pt:
  match x:
    case R.Ext{i}:
      peer(i, es)
    case R.New{j, p}:
      Pt{Nat.add(n0, j), p}

def sigs(+n0: Nat, +es: Peers, xs: List<&2, R.End>) -> List<&2, Pt>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      sig(n0, es, x) <> sigs(n0, es, t)

def links(+n0: Nat, +es: Peers, ls: List<&2, R.Link>) -> List<&2, Ln>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{R.Link{x, y}, t}:
      Ln{sig(n0, es, x), sig(n0, es, y)} <> links(n0, es, t)

def aux_a(+ka: R.NodeKind) -> List<&2, R.End>:
  R.aux_ends(Nat.sub(R.arity(ka), 1n), 0n)

def aux_b(+kb: R.NodeKind) -> List<&2, R.End>:
  R.aux_ends(Nat.sub(R.arity(kb), 1n), 2n)

# a net focused on an active pair a >< b: the kinds, the pair, the peers
# of its auxiliary ports, and the other links
type Foc is Data:
  Foc{ks: List<&2, R.NodeKind>, a: Nat, b: Nat, es: Peers, c: List<&2, Ln>}

# its links' ends, grouped: the pair's ports (the principal link joins
# their ports 0; a's port i + 1 links peer i, b's peer 2 + i), the peers
# those link, then the other links' ends
def fends(f: Foc) -> List<&2, Pt>:
  match f:
    case Foc{+ks, +a, +b, +es, c}:
      List.append(&2, Pt, ports(a, R.arity(kind_at(ks, a))),
        List.append(&2, Pt, ports(b, R.arity(kind_at(ks, b))),
          List.append(&2, Pt, sigs(List.length(&2, R.NodeKind, ks), es, aux_a(kind_at(ks, a))),
            List.append(&2, Pt, sigs(List.length(&2, R.NodeKind, ks), es, aux_b(kind_at(ks, b))), ends(c)))))

def kinds(xs: List<&2, R.Spec>) -> List<&2, R.NodeKind>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{R.Spec{k, s}, t}:
      k <> kinds(t)

# the rewrite by a rule's new nodes xs and links ls: a and b freed, the new
# nodes appended, the other links kept and the rule's added, each end
# placed by sig
def rw_kinds(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, xs: List<&2, R.Spec>) -> List<&2, R.NodeKind>:
  List.append(&2, R.NodeKind, set(set(ks, a, R.KFree{}), b, R.KFree{}), kinds(xs))

def rw_links(+ks: List<&2, R.NodeKind>, +es: Peers, c: List<&2, Ln>, ls: List<&2, R.Link>) -> List<&2, Ln>:
  List.append(&2, Ln, c, links(List.length(&2, R.NodeKind, ks), es, ls))

# the focused net's ends under pattern p: the pair's ports, then only the
# peers facing outside (a link between two of the pair's ports has both
# its ends among those ports), then the other links' ends
def fends_in(f: Foc, +p: R.Pat) -> List<&2, Pt>:
  match f:
    case Foc{+ks, +a, +b, +es, c}:
      List.append(&2, Pt, ports(a, R.arity(kind_at(ks, a))),
        List.append(&2, Pt, ports(b, R.arity(kind_at(ks, b))),
          List.append(&2, Pt, sigs(List.length(&2, R.NodeKind, ks), es, R.outer(p, R.ext_ends(kind_at(ks, a), kind_at(ks, b)))), ends(c))))

def keeps_wired.m(m: Maybe<&2, List<&2, R.Link>>, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: Peers, c: List<&2, Ln>, xs: List<&2, R.Spec>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{ls}:
      wired(rw_kinds(ks, a, b, xs), ends(rw_links(ks, es, c, ls)))

# one step by rule r under pattern p leaves a wired net, or the kernel
# reports an error (R.contract's None), or the pair is stuck and the net
# stays as it was
def keeps_wired(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: Peers, c: List<&2, Ln>, r: R.Rule, +p: R.Pat) -> Bool:
  match r:
    case R.RWire{xs, +ls}:
      keeps_wired.m(R.contract(p, ls), ks, a, b, es, c, xs)
    case R.RStuck{}:
      True{}

# one rewrite by rule r, its kinds and its links' ends; a stuck pair
# leaves the net as it was
def step_kinds(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, r: R.Rule) -> List<&2, R.NodeKind>:
  match r:
    case R.RWire{xs, ls}:
      rw_kinds(ks, a, b, xs)
    case R.RStuck{}:
      ks

def step_ends(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: Peers, c: List<&2, Ln>, r: R.Rule) -> List<&2, Pt>:
  match r:
    case R.RWire{xs, ls}:
      ends(rw_links(ks, es, c, ls))
    case R.RStuck{}:
      fends(Foc{ks, a, b, es, c})

# a beta step: an application (node 0) meets a function (node 1); their
# other ports link a root, two erasers and a datum
def demo(r: R.Rule) -> Bool:
  match r:
    case R.RWire{xs, +ls}:
      wired([R.KAp{}, R.KFn{}, R.KRoot{}, R.KEraN{}, R.KEraN{}, R.KData{}],
          fends(Foc{[R.KAp{}, R.KFn{}, R.KRoot{}, R.KEraN{}, R.KEraN{}, R.KData{}], 0n, 1n,
            Peers{Pt{3n, 0n}, Pt{2n, 0n}, Pt{4n, 0n}, Pt{5n, 0n}}, []})) &&
        wired(rw_kinds([R.KAp{}, R.KFn{}, R.KRoot{}, R.KEraN{}, R.KEraN{}, R.KData{}], 0n, 1n, xs),
          ends(rw_links([R.KAp{}, R.KFn{}, R.KRoot{}, R.KEraN{}, R.KEraN{}, R.KData{}], Peers{Pt{3n, 0n}, Pt{2n, 0n}, Pt{4n, 0n}, Pt{5n, 0n}}, [], ls)))
    case R.RStuck{}:
      False{}

def demo2.m(m: Maybe<&2, List<&2, R.Link>>, +ks: List<&2, R.NodeKind>, +es: Peers, xs: List<&2, R.Spec>) -> Bool:
  match m:
    case Some{ls}:
      wired(rw_kinds(ks, 0n, 1n, xs), ends(rw_links(ks, es, [], ls)))
    case None{}:
      False{}

# a beta step whose function's body is the application's result (port 2
# of node 1 linked to port 2 of node 0, pattern P13): the argument, a
# datum, joins the variable's eraser
def demo2(r: R.Rule) -> Bool:
  match r:
    case R.RWire{xs, +ls}:
      wired([R.KAp{}, R.KFn{}, R.KData{}, R.KEraN{}], fends_in(Foc{[R.KAp{}, R.KFn{}, R.KData{}, R.KEraN{}], 0n, 1n,
          Peers{Pt{2n, 0n}, Pt{1n, 2n}, Pt{3n, 0n}, Pt{0n, 2n}}, []}, R.P13{})) &&
        demo2.m(R.contract(R.P13{}, ls), [R.KAp{}, R.KFn{}, R.KData{}, R.KEraN{}], Peers{Pt{2n, 0n}, Pt{1n, 2n}, Pt{3n, 0n}, Pt{0n, 2n}}, xs)
    case R.RStuck{}:
      False{}

def main() -> Bool:
  demo(R.rule(R.KAp{}, R.KFn{}, True{})) && demo2(R.rule(R.KAp{}, R.KFn{}, True{}))
