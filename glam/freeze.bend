import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/net.bend as N
import ../spike/kprim.bend as P
import ../spike/knet.bend as KN

# Freezing (the Cells plan's `cells-freeze.cursors`): a live net read back
# into a template, the inverse of KN.load, so that loading what is frozen
# gives the net frozen. Every node the interface reaches is read back, in
# the order a walk from the interface meets them: its kind, and its
# payload from its header and words, a data node's or an operator's value
# read from the table, the entry kept; then every link between two of
# them, once; each static at a port written as an eraser node, of the
# polarity other than its port's, which the loader makes static again;
# and the root, the port the interface faces.
#
# Frozen whole (`freeze`), every node the interface reaches is read back.
# Frozen finished (`freeze_finished`), only the finished part is: the
# interface's principal tree, each node whose principal faces the
# interface or an auxiliary port of a finished node, which no pair can
# ever reach (the Cursors review). A wire from a finished node to one
# that is not is a cursor, kept as a placeholder node and listed: the
# source's reference of the finished node's port, and whether that port
# is negative (the copy awaits a value there) or positive (the copy
# supplies one). A root not finished is a cursor at the interface.

# Reaching
# ========

# the walk's state: the net, the template index of each node reached plus
# one (0 for none) by node index, how many are reached, their references
# (the last first), and the references still to visit
type FzR is Type:
  FzR{h: P.H, map: Array<U32>, +n: U32, seen: List<&2, U32>, s: List<&2, U32>}

# the node of reference r, by index
def fz.at(+r: U32) -> U32:
  (P.base(r) >> 2n : U32)

# a peer q pushed unless static or the interface; reaching the finished
# part only, unless it is a principal port
def fz.reach.q(+all: Bool, +q: U32) -> Bool:
  Bool.not(P.is_static(q)) && U32.is_ne(P.base(q), P.iface()) && (all || U32.is_eq((q .&. 3 : U32), 0))

def fz.push.q(+go: Bool, +q: U32, s: List<&2, U32>) -> List<&2, U32>:
  match go:
    case True{}:
      Con{P.base(q), s}
    case False{}:
      s

def fz.port.q(r: P.H & U32, +all: Bool, s: List<&2, U32>) -> P.H & List<&2, U32>:
  (h, +q) = r
  (h, fz.push.q(fz.reach.q(all, q), q, s))

# port p's peer, of the node at base b, pushed
def fz.port(h: P.H, +all: Bool, +b: U32, +p: U32, s: List<&2, U32>) -> P.H & List<&2, U32>:
  fz.port.q(P.rd(h, (b + 1 + p : U32)), all, s)

def fz.port.r(r: P.H & List<&2, U32>, +all: Bool, +b: U32, +p: U32) -> P.H & List<&2, U32>:
  (h, s) = r
  fz.port(h, all, b, p, s)

# the peers of a node of k ports, at most three: reaching the finished
# part only, its auxiliary ports alone, its principal facing its parent
def fz.ports.aux(h: P.H, +all: Bool, +b: U32, k: Nat, s: List<&2, U32>) -> P.H & List<&2, U32>:
  match k:
    case 0n:
      (h, s)
    case 1n+j:
      match j:
        case 0n:
          (h, s)
        case 1n+i:
          match i:
            case 0n:
              fz.port(h, all, b, 1, s)
            case 1n+x:
              fz.port.r(fz.port(h, all, b, 1, s), all, b, 2)

def fz.ports(+all: Bool, h: P.H, +b: U32, k: Nat, s: List<&2, U32>) -> P.H & List<&2, U32>:
  match all:
    case True{}:
      fz.port.r(fz.ports.aux(h, all, b, k, s), all, b, 0)
    case False{}:
      fz.ports.aux(h, all, b, k, s)

def fz.mark.s(r: P.H & List<&2, U32>, map: Array<U32>, +n: U32, seen: List<&2, U32>) -> FzR:
  (h, s) = r
  FzR{h, map, n, seen, s}

# a control a copy takes, reached in the finished part only, is marked in
# its source so that fusion leaves it alone (copied-controls-unfused,
# kprim.bend's mark); a whole net read back is left as it is
def fz.copied.k(+take: Bool, h: P.H, +b: U32, +hd: U32) -> P.H:
  match take:
    case True{}:
      P.wr(h, b, P.mark(hd))
    case False{}:
      h

def fz.copied(+all: Bool, h: P.H, +b: U32, +hd: U32) -> P.H:
  fz.copied.k(Bool.not(all) && (U32.is_eq(P.rk(hd), 10) || U32.is_eq(P.rk(hd), 11)), h, b, hd)

def fz.mark.hd(r: P.H & U32, +all: Bool, map: Array<U32>, +b: U32, +n: U32, seen: List<&2, U32>, s: List<&2, U32>) -> FzR:
  (h, +hd) = r
  fz.mark.s(fz.ports(all, fz.copied(all, h, b, hd), b, R.arity(N.kof(P.rk(hd))), s), Array.set(U32, map, fz.at(b), (n + 1 : U32)), (n + 1 : U32), Con{b, seen})

def fz.mark.k(+seen0: Bool, +all: Bool, h: P.H, map: Array<U32>, +n: U32, seen: List<&2, U32>, +b: U32, s: List<&2, U32>) -> FzR:
  match seen0:
    case True{}:
      FzR{h, map, n, seen, s}
    case False{}:
      fz.mark.hd(P.rd(h, b), all, map, b, n, seen, s)

def fz.mark.m(r: Array<U32> & U32, +all: Bool, h: P.H, +n: U32, seen: List<&2, U32>, +b: U32, s: List<&2, U32>) -> FzR:
  (map, +v) = r
  fz.mark.k(U32.is_ne(v, 0), all, h, map, n, seen, b, s)

# the node at base b reached, unless it was already
def fz.mark(+all: Bool, h: P.H, map: Array<U32>, +n: U32, seen: List<&2, U32>, +b: U32, s: List<&2, U32>) -> FzR:
  fz.mark.m(Array.get(U32, map, fz.at(b)), all, h, n, seen, b, s)

# every node reached from the stack, fuel f bounding the visits, which the
# ports of the nodes in the net bound
def fz.reach(f: Nat, +all: Bool, z: FzR) -> FzR:
  match f:
    case 0n:
      z
    case 1n+g:
      match z:
        case FzR{h, map, +n, seen, s}:
          match s:
            case Nil{}:
              FzR{h, map, n, seen, Nil{}}
            case Con{b, rest}:
              fz.reach(g, all, fz.mark(all, h, map, n, seen, b, rest))

# Reading back
# ============

def fz.lv(+un: Bool, k: R.NodeKind, +f: U32) -> T.TNode:
  match un:
    case True{}:
      T.TN{k, V.PNone{}}
    case False{}:
      T.TN{k, V.PLvl{f}}

def fz.fan(+un: Bool, k: R.NodeKind, +f: U32) -> T.TNode:
  match un:
    case True{}:
      T.TF{k, f, V.nolvl()}
    case False{}:
      T.TF{k, 0, f}

def fz.lift(r: P.H & U32, k: R.NodeKind, +f: U32) -> P.H & T.TNode:
  (h, +w) = r
  (h, T.TN{k, V.PLift{f, U32.is_ge(w, 2147483648), (w .&. 2147483647 : U32)}})

def fz.val(r: P.H & V.Val, k: R.NodeKind) -> P.H & T.TNode:
  (h, v) = r
  (h, T.TN{k, V.PVal{v}})

def fz.word(r: P.H & U32, k: R.NodeKind, +hd: U32) -> P.H & T.TNode:
  (h, +w) = r
  fz.val(P.peek(h, P.form(hd), P.fld(hd), w), k)

# a fan, or a node with no payload
def fz.node.f(k: R.NodeKind, h: P.H, +hd: U32) -> P.H & T.TNode:
  match k:
    case R.KCopy{}:
      (h, fz.fan(U32.is_eq(P.form(hd), P.unlev()), R.KCopy{}, P.fld(hd)))
    case R.KMerge{}:
      (h, fz.fan(U32.is_eq(P.form(hd), P.unlev()), R.KMerge{}, P.fld(hd)))
    case R.KCopyL{}:
      (h, fz.fan(U32.is_eq(P.form(hd), P.unlev()), R.KCopyL{}, P.fld(hd)))
    case R.KCopyR{}:
      (h, fz.fan(U32.is_eq(P.form(hd), P.unlev()), R.KCopyR{}, P.fld(hd)))
    case R.KMergeL{}:
      (h, fz.fan(U32.is_eq(P.form(hd), P.unlev()), R.KMergeL{}, P.fld(hd)))
    case R.KMergeR{}:
      (h, fz.fan(U32.is_eq(P.form(hd), P.unlev()), R.KMergeR{}, P.fld(hd)))
    case _:
      (h, T.TN{k, V.PNone{}})

# a node read back from its header hd at base b, its kind's code c
def fz.node.c(+c: U32, h: P.H, +hd: U32, +b: U32) -> P.H & T.TNode:
  match c:
    case 1:
      (h, fz.lv(U32.is_eq(P.form(hd), P.unlev()), R.KFn{}, P.fld(hd)))
    case 2:
      (h, fz.lv(U32.is_eq(P.form(hd), P.unlev()), R.KAp{}, P.fld(hd)))
    case 17:
      (h, fz.lv(U32.is_eq(P.form(hd), P.unlev()), R.KFnD{}, P.fld(hd)))
    case 5:
      fz.word(P.rd(h, (b + 2 : U32)), R.KData{}, hd)
    case 9:
      fz.word(P.rd(h, (b + 3 : U32)), R.KOp{}, hd)
    case 16:
      fz.word(P.rd(h, (b + 3 : U32)), R.KDOp{}, hd)
    case 10:
      fz.lift(P.rd(h, (b + 3 : U32)), R.KLift{}, P.fld(hd))
    case 11:
      fz.lift(P.rd(h, (b + 3 : U32)), R.KLiftC{}, P.fld(hd))
    case _:
      fz.node.f(N.kof(c), h, hd)


# Writing the template
# ====================

# a cursor: the placeholder's index in the template, the source's
# reference of the finished node's port, whether that port is negative,
# the copy awaiting a value there, and the port it faces in the source,
# its far end
type FzC is Data:
  FzC{+at: U32, +src: U32, neg: Bool, +far: U32}

# a freeze of the finished part: the template and its cursors, the first
# placeholder first
type Fz is Data:
  Fz{tpl: T.Tpl, curs: List<&2, FzC>}

# the template being written: the net, the index map, the nodes read so
# far (the last first), the nodes standing for statics and cursors (the
# last first), the next such node's index, the links, the root, and the
# cursors (the last first)
type FzE is Type:
  FzE{h: P.H, map: Array<U32>, nodes: List<&2, T.TNode>, eras: List<&2, T.TNode>, +ne: U32, links: List<&2, T.TLink>, root: T.TEnd, curs: List<&2, FzC>}

# the eraser standing for a static at a port of polarity pol: the other
def fz.era(pol: R.Pol) -> T.TNode:
  match pol:
    case R.Neg{}:
      T.TN{R.KEraP{}, V.PNone{}}
    case R.Pos{}:
      T.TN{R.KEraN{}, V.PNone{}}

def fz.neg(pol: R.Pol) -> Bool:
  match pol:
    case R.Neg{}:
      True{}
    case R.Pos{}:
      False{}

# the placeholder of a cursor: a cursor node (`cells-freeze.cursors.kinds`),
# a negative one as loaded, which a materialization makes positive where
# the port is
def fz.hole(pol: R.Pol) -> T.TNode:
  T.TN{R.KCur{}, V.PNone{}}

# a link from port p of node i to port pq of node j, written once: from
# the end that comes first
def fz.link.k(+first: Bool, +i: U32, +p: U32, +j: U32, +pq: U32, ls: List<&2, T.TLink>) -> List<&2, T.TLink>:
  match first:
    case True{}:
      Con{T.TL{T.TE{i, p}, T.TE{j, pq}}, ls}
    case False{}:
      ls

# the peer at port q of a node reached (v its index plus one), or, v
# being 0, of one not finished: a cursor
def fz.peer.v(+unf: Bool, h: P.H, map: Array<U32>, nodes: List<&2, T.TNode>, eras: List<&2, T.TNode>, +ne: U32, ls: List<&2, T.TLink>, root: T.TEnd, curs: List<&2, FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +v: U32) -> FzE:
  match unf:
    case True{}:
      FzE{h, map, nodes, Con{fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{FzC{ne, (b + p : U32), fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}
    case False{}:
      FzE{h, map, nodes, eras, ne, fz.link.k(U32.is_lt(i, (v - 1 : U32)) || (U32.is_eq(i, (v - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (v - 1 : U32), (q .&. 3 : U32), ls), root, curs}

def fz.peer.j(r: Array<U32> & U32, h: P.H, nodes: List<&2, T.TNode>, eras: List<&2, T.TNode>, +ne: U32, ls: List<&2, T.TLink>, root: T.TEnd, curs: List<&2, FzC>, k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32) -> FzE:
  (map, +v) = r
  fz.peer.v(U32.is_eq(v, 0), h, map, nodes, eras, ne, ls, root, curs, k, b, i, p, q, v)

# port p of node i (at base b), of kind k, its link q: a static, the
# interface (the root), a node reached, or one not finished
def fz.peer.k(+st: Bool, +rt: Bool, z: FzE, k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32) -> FzE:
  match st:
    case True{}:
      match z:
        case FzE{h, map, nodes, eras, +ne, ls, root, curs}:
          FzE{h, map, nodes, Con{fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}
    case False{}:
      match rt:
        case True{}:
          match z:
            case FzE{h, map, nodes, eras, +ne, ls, root, curs}:
              FzE{h, map, nodes, eras, ne, ls, T.TE{i, p}, curs}
        case False{}:
          match z:
            case FzE{h, map, nodes, eras, +ne, ls, root, curs}:
              fz.peer.j(Array.get(U32, map, fz.at(q)), h, nodes, eras, ne, ls, root, curs, k, b, i, p, q)

def fz.peer.q(r: P.H & U32, map: Array<U32>, nodes: List<&2, T.TNode>, eras: List<&2, T.TNode>, +ne: U32, ls: List<&2, T.TLink>, root: T.TEnd, curs: List<&2, FzC>, k: R.NodeKind, +b: U32, +i: U32, +p: U32) -> FzE:
  (h, +q) = r
  fz.peer.k(P.is_static(q), U32.is_eq(P.base(q), P.iface()), FzE{h, map, nodes, eras, ne, ls, root, curs}, k, b, i, p, q)

# port p of node i at base b
def fz.peer(z: FzE, k: R.NodeKind, +b: U32, +i: U32, +p: U32) -> FzE:
  match z:
    case FzE{h, map, nodes, eras, +ne, ls, root, curs}:
      fz.peer.q(P.rd(h, (b + 1 + p : U32)), map, nodes, eras, ne, ls, root, curs, k, b, i, p)

# the ports of a node of kind k, at most three
def fz.peers(z: FzE, +k: R.NodeKind, +b: U32, +i: U32, a: Nat) -> FzE:
  match a:
    case 0n:
      z
    case 1n+j:
      match j:
        case 0n:
          fz.peer(z, k, b, i, 0)
        case 1n+x:
          match x:
            case 0n:
              fz.peer(fz.peer(z, k, b, i, 0), k, b, i, 1)
            case 1n+y:
              fz.peer(fz.peer(fz.peer(z, k, b, i, 0), k, b, i, 1), k, b, i, 2)

def fz.emit.t(r: P.H & T.TNode, map: Array<U32>, nodes: List<&2, T.TNode>, eras: List<&2, T.TNode>, +ne: U32, ls: List<&2, T.TLink>, root: T.TEnd, curs: List<&2, FzC>, +c: U32, +b: U32, +i: U32) -> FzE:
  (h, t) = r
  fz.peers(FzE{h, map, Con{t, nodes}, eras, ne, ls, root, curs}, N.kof(c), b, i, R.arity(N.kof(c)))

def fz.emit.hd(r: P.H & U32, map: Array<U32>, nodes: List<&2, T.TNode>, eras: List<&2, T.TNode>, +ne: U32, ls: List<&2, T.TLink>, root: T.TEnd, curs: List<&2, FzC>, +b: U32, +i: U32) -> FzE:
  (h, +hd) = r
  fz.emit.t(fz.node.c(P.rk(hd), h, hd, b), map, nodes, eras, ne, ls, root, curs, P.rk(hd), b, i)

# the node at base b, its index i, written with its links
def fz.emit(z: FzE, +b: U32, +i: U32) -> FzE:
  match z:
    case FzE{h, map, nodes, eras, +ne, ls, root, curs}:
      fz.emit.hd(P.rd(h, b), map, nodes, eras, ne, ls, root, curs, b, i)

# the nodes reached, the last first, written in turn: the last has index
# i, each before it one less, so that the nodes come out first first
def fz.emits(seen: List<&2, U32>, z: FzE, +i: U32) -> FzE:
  match seen:
    case Nil{}:
      z
    case Con{b, rest}:
      fz.emits(rest, fz.emit(z, b, i), (i - 1 : U32))

def fz.tpl(z: FzE) -> P.H & Fz:
  match z:
    case FzE{h, map, nodes, eras, +ne, ls, root, curs}:
      (h, Fz{T.Tpl{List.append(&2, T.TNode, nodes, List.reverse(&2, T.TNode, eras)), ls, root, ne}, List.reverse(&2, FzC, curs)})

# nothing finished: the root itself is a cursor, at the interface
def fz.written.k(+none: Bool, h: P.H, map: Array<U32>, +n: U32, seen: List<&2, U32>) -> P.H & Fz:
  match none:
    case True{}:
      (h, Fz{T.Tpl{[T.TN{R.KCur{}, V.PNone{}}], Nil{}, T.TE{0, 0}, 1}, [FzC{0, P.iface(), True{}, P.iface()}]})
    case False{}:
      fz.tpl(fz.emits(seen, FzE{h, map, Nil{}, Nil{}, n, Nil{}, T.TE{0, 0}, Nil{}}, (n - 1 : U32)))

def fz.written(z: FzR) -> P.H & Fz:
  match z:
    case FzR{h, map, +n, seen, s}:
      fz.written.k(U32.is_eq(n, 0), h, map, n, seen)

def fz.start(r: P.H & U32, +all: Bool, map: Array<U32>) -> FzR:
  (h, +q) = r
  FzR{h, map, 0, Nil{}, fz.push.q(fz.reach.q(all, q) || U32.is_eq(P.base(q), P.iface()), q, Nil{})}

def fz.cap(r: P.H & P.HS, +all: Bool) -> P.H & Fz:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      fz.written(fz.reach(U32.to_nat(((cap << 2n : U32) + 4 : U32)), all, fz.start(P.rd(h, (P.iface() + 1 : U32)), all, [0 : U32^T.depth_for(31n, cap, 0n)])))

def fz.whole(r: P.H & Fz) -> P.H & T.Tpl:
  (h, f) = r
  match f:
    case Fz{t, curs}:
      (h, t)

# the whole net the interface reaches, frozen
def freeze(h: P.H) -> P.H & T.Tpl:
  fz.whole(fz.cap(P.stats(h), True{}))

# the finished part frozen, with its cursors
def freeze_finished(h: P.H) -> P.H & Fz:
  fz.cap(P.stats(h), False{})

def fz.tree.cap(r: P.H & P.HS, +v: U32) -> P.H & Fz:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      fz.written(fz.reach(U32.to_nat(((cap << 2n : U32) + 4 : U32)), False{}, FzR{h, [0 : U32^T.depth_for(31n, cap, 0n)], 0, Nil{}, [v]}))

# the finished tree rooted at the node at base v frozen, with its
# cursors: every wire leaving it, its root's principal among them, a
# cursor whose far end says where it led (a materialization's tree,
# `cells-freeze.cursors.materialize`). The interface met is the root, as
# freeze_finished has it.
def freeze_tree(h: P.H, +v: U32) -> P.H & Fz:
  fz.tree.cap(P.stats(h), v)
