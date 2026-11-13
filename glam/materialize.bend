import Base
import ../spike/val.bend as V
import ../spike/tpl.bend as T
import ../spike/kprim.bend as P
import ../spike/kdemand.bend as KD
import ./splice.bend as S
import ./freeze.bend as F
import ./position.bend as Q

# Materializing (the Cells plan's cells-freeze.cursors.materialize, the
# design in docs/reviews/Joins_2026-11-11.md): a copy's cursor served
# from its live source, the newly finished nodes copied into the host
# and every wire leaving them joined.
#
# A copy's cursors form a ring in the host's heap through word 3, with
# one situating node holding the source's handle (word 2) and the copy's
# level offset (its field); form 2 of the cursor kind. A cursor holds its
# position in the source in word 2: form 0 negative, standing for a
# value; form 1 positive, receiving one. A use of a live template is a
# negative cursor at the source's interface, so the first copy is a serve
# like any other.
#
# Serving a negative cursor runs positioned demand at its position
# (`glam/position.bend`), then:
# - a value: the finished tree under it is frozen (`F.freeze_tree`),
#   spliced at the offset, and each wire leaving it joined: its far end
#   looked up in the ring, a cursor there replaced by the wire, the
#   served cursor among them; otherwise a new cursor of the port's
#   polarity, put in the ring;
# - the frontier: a cursor of the ring at the port reached is joined to
#   the served one directly, nothing copied (the identity's case); else
#   the finished tree holding that port is found by climbing its
#   principal links to a position of the ring, and materialized;
# - a static: the served cursor's peer gets it.
#
# Not yet: the marks on copied nodes (`copied-nodes-untouched`), so a
# source must run no events, fusion or collection near copied nodes;
# scratch the size of the source in each freeze.

# A ring
# ======

def rg.next(h: P.H, +x: U32) -> P.H & U32:
  P.rd(h, (x + 3 : U32))

# a walk round a ring: the net, the node reached, the one before it, and
# what was found, the walk done once it is
type Rw is Type:
  Rw{h: P.H, +x: U32, +p: U32, found: Maybe<&2, U32>, done: Bool}

def rw.on(r: P.H & U32, +x: U32) -> Rw:
  (h, +n) = r
  Rw{h, n, x, None{}, False{}}

# looking for position far: at the situating node again, none; x's
# position far, x; else on to the next
def rw.find.k(+hit: Bool, h: P.H, +x: U32) -> Rw:
  match hit:
    case True{}:
      Rw{h, x, x, Some{x}, True{}}
    case False{}:
      rw.on(rg.next(h, x), x)

def rw.find.p(r: P.H & U32, +x: U32, +far: U32) -> Rw:
  (h, +pos) = r
  rw.find.k(U32.is_eq(pos, far), h, x)

def rw.find.s(+home: Bool, h: P.H, +x: U32, +far: U32) -> Rw:
  match home:
    case True{}:
      Rw{h, x, x, None{}, True{}}
    case False{}:
      rw.find.p(P.rd(h, (x + 2 : U32)), x, far)

def rg.find.go(f: Nat, w: Rw, +situ: U32, +far: U32) -> Rw:
  match f:
    case 0n:
      w
    case 1n+g:
      match w:
        case Rw{h, +x, +p, found, done}:
          match done:
            case True{}:
              Rw{h, x, p, found, True{}}
            case False{}:
              rg.find.go(g, rw.find.s(U32.is_eq(x, situ), h, x, far), situ, far)

def rg.found(w: Rw) -> P.H & Maybe<&2, U32>:
  match w:
    case Rw{h, +x, +p, found, done}:
      (h, found)

# the cursor of situ's ring at position far, if any
def rg.find(h: P.H, +situ: U32, +far: U32) -> P.H & Maybe<&2, U32>:
  rg.found(rg.find.go(1000000n, rw.on(rg.next(h, situ), situ), situ, far))

# looking for x's predecessor: the node reached is x, the one before it
# found
def rw.pred.k(+hit: Bool, h: P.H, +n: U32, +p: U32) -> Rw:
  match hit:
    case True{}:
      Rw{h, n, p, Some{p}, True{}}
    case False{}:
      rw.on(rg.next(h, n), n)

def rg.pred.go(f: Nat, w: Rw, +x: U32) -> Rw:
  match f:
    case 0n:
      w
    case 1n+g:
      match w:
        case Rw{h, +n, +p, found, done}:
          match done:
            case True{}:
              Rw{h, n, p, found, True{}}
            case False{}:
              rg.pred.go(g, rw.pred.k(U32.is_eq(n, x), h, n, p), x)

def rg.unlink.set(r: P.H & U32, +p: U32) -> P.H:
  (h, +nx) = r
  P.wr(h, (p + 3 : U32), nx)

def rg.unlink.w(w: Rw, +x: U32) -> P.H:
  match w:
    case Rw{h, +n, +p, found, done}:
      rg.unlink.set(rg.next(h, x), p)

# x taken out of its ring, its predecessor found by walking from x
def rg.unlink(h: P.H, +x: U32) -> P.H:
  rg.unlink.w(rg.pred.go(1000000n, rw.on(rg.next(h, x), x), x), x)

# x put in situ's ring, after situ
def rg.insert.r(r: P.H & U32, +situ: U32, +x: U32) -> P.H:
  (h, +n) = r
  P.wr(P.wr(h, (x + 3 : U32), n), (situ + 3 : U32), x)

def rg.insert(h: P.H, +situ: U32, +x: U32) -> P.H:
  rg.insert.r(rg.next(h, situ), situ, x)

# looking for the situating node: its form 2
def rw.situ.k(+yes: Bool, h: P.H, +n: U32) -> Rw:
  match yes:
    case True{}:
      Rw{h, n, n, Some{n}, True{}}
    case False{}:
      rw.on(rg.next(h, n), n)

def rw.situ.f(r: P.H & U32, +n: U32) -> Rw:
  (h, +hd) = r
  rw.situ.k(U32.is_eq(P.form(hd), 2), h, n)

def rg.situ.go(f: Nat, w: Rw) -> Rw:
  match f:
    case 0n:
      w
    case 1n+g:
      match w:
        case Rw{h, +n, +p, found, done}:
          match done:
            case True{}:
              Rw{h, n, p, found, True{}}
            case False{}:
              rg.situ.go(g, rw.situ.f(P.rd(h, n), n))

def rg.situ.w(w: Rw) -> P.H & U32:
  match w:
    case Rw{h, +n, +p, found, done}:
      (h, n)

# the situating node of x's ring
def rg.situ(h: P.H, +x: U32) -> P.H & U32:
  rg.situ.w(rg.situ.go(1000000n, Rw{h, x, x, None{}, False{}}))

# Joins
# =====

def jn.w(r: P.H & U32, +u: U32, +x: U32, +y: U32) -> P.H:
  (h, +w) = r
  P.free(P.free(rg.unlink(rg.unlink(P.link_xx(h, u, w), x), y), x), y)

def jn.u(r: P.H & U32, +x: U32, +y: U32) -> P.H:
  (h, +u) = r
  jn.w(P.rd(h, (y + 1 : U32)), u, x, y)

# two cursors x and y of one ring (or a placeholder x, not in the ring,
# and a cursor y) replaced by one wire between what each faced
def join(h: P.H, +x: U32, +y: U32) -> P.H:
  jn.u(P.rd(h, (x + 1 : U32)), x, y)

def jn1.w(r: P.H & U32, +u: U32, +x: U32, +y: U32) -> P.H:
  (h, +w) = r
  P.free(P.free(rg.unlink(P.link_xx(h, u, w), y), x), y)

def jn1.u(r: P.H & U32, +x: U32, +y: U32) -> P.H:
  (h, +u) = r
  jn1.w(P.rd(h, (y + 1 : U32)), u, x, y)

# a placeholder x, in no ring, and a ring's cursor y, replaced by a wire
def join1(h: P.H, +x: U32, +y: U32) -> P.H:
  jn1.u(P.rd(h, (x + 1 : U32)), x, y)

def mz.neg.form(+neg: Bool) -> U32:
  match neg:
    case True{}:
      0
    case False{}:
      1

# a placeholder made a cursor at position src and put in the ring
def mz.cursor(h: P.H, +situ: U32, +pl: U32, +src: U32, +neg: Bool) -> P.H:
  rg.insert(P.wr(P.wr(h, pl, P.hd2(18, mz.neg.form(neg), 0)), (pl + 2 : U32), src), situ, pl)

def mz.found(r: P.H & Maybe<&2, U32>, +situ: U32, +pl: U32, +src: U32, +neg: Bool) -> P.H:
  (h, m) = r
  match m:
    case Some{+y}:
      join1(h, pl, y)
    case None{}:
      mz.cursor(h, situ, pl, src, neg)

def mz.pl(r: Array<U32> & U32, h: P.H, +situ: U32, +src: U32, +neg: Bool, +far: U32) -> Array<U32> & P.H:
  (map, +pl) = r
  (map, mz.found(rg.find(h, situ, far), situ, pl, src, neg))

def mz.cur(q: Array<U32> & P.H, c: F.FzC, +situ: U32) -> Array<U32> & P.H:
  (map, h) = q
  match c:
    case F.FzC{+at, +src, neg, +far}:
      mz.pl(Array.get(U32, map, at), h, situ, src, neg, far)

def mz.curs(cs: List<&2, F.FzC>, q: Array<U32> & P.H, +situ: U32) -> Array<U32> & P.H:
  match cs:
    case Nil{}:
      q
    case Con{c, rest}:
      mz.curs(rest, mz.cur(q, c, situ), situ)

# the copy's root, where the tree faced the source's interface (a first
# copy): joined to the served cursor nc
def mz.root.w(r: P.H & U32, +x: U32, +nc: U32) -> P.H:
  (h, +w) = r
  P.free(rg.unlink(P.link_xx(h, x, w), nc), nc)

def mz.root.e(r: Array<U32> & U32, h: P.H, +p: U32, +nc: U32) -> P.H:
  (map, +n) = r
  mz.root.w(P.rd(h, (nc + 1 : U32)), (n + p : U32), nc)

def mz.root(+at_root: Bool, map: Array<U32>, h: P.H, root: T.TEnd, +nc: U32) -> P.H:
  match at_root:
    case True{}:
      match root:
        case T.TE{+n, +p}:
          mz.root.e(Array.get(U32, map, n), h, p, nc)
    case False{}:
      h

def mz.sp.r(q: Array<U32> & P.H, root: T.TEnd, +nc: U32, +at_root: Bool) -> P.H:
  (map, h) = q
  mz.root(at_root, map, h, root, nc)

def mz.sp(s: S.Sp, curs: List<&2, F.FzC>, root: T.TEnd, +situ: U32, +nc: U32, +at_root: Bool) -> P.H:
  match s:
    case S.Sp{h, map}:
      mz.sp.r(mz.curs(curs, (map, h), situ), root, nc, at_root)

def mz.fz(r: P.H & F.Fz, h: P.H, +situ: U32, +k: U32, +nc: U32, +at_root: Bool) -> P.H & P.H:
  (s, f) = r
  match f:
    case F.Fz{t, curs}:
      match t:
        case T.Tpl{nodes, links, root, +size}:
          (s, mz.sp(S.sp.statics(U32.to_nat(size), S.sp.links(links, S.sp.nodes(nodes, 0, S.Sp{h, [0 : U32^T.depth_for(31n, size, 0n)]}, k)), 0), curs, root, situ, nc, at_root))

# the finished tree at node base v of source s copied into host h at
# offset k, its wires joined in situ's ring; at_root where it is the
# source's root, faced by the interface, served by cursor nc
def materialize(s: P.H, h: P.H, +situ: U32, +v: U32, +k: U32, +nc: U32, +at_root: Bool) -> P.H & P.H:
  mz.fz(F.freeze_tree(s, v), h, situ, k, nc, at_root)

# Serving
# =======

# what a serve leaves: the source and the host, or a stop of positioned
# demand in the source, for the core, with the host as it was
# a serve's end: the source and the host, or positioned demand's stop in
# the source, as it stood; with the interactions made in the source
type Sv is Type:
  SvOk{s: P.H, h: P.H, +n: U32}
  SvStop{d: KD.D, h: P.H, +n: U32}

# a climb from a finished node of the source toward the root of its tree,
# a node whose principal faces a position the ring holds
type Cl is Type:
  Cl{s: P.H, h: P.H, +x: U32, done: Bool}

def cl.k(m: Maybe<&2, U32>, s: P.H, h: P.H, +x: U32, +f: U32) -> Cl:
  match m:
    case Some{+c}:
      Cl{s, h, x, True{}}
    case None{}:
      Cl{s, h, P.base(f), False{}}

def cl.found(r: P.H & Maybe<&2, U32>, s: P.H, +x: U32, +f: U32) -> Cl:
  (h, m) = r
  cl.k(m, s, h, x, f)

def cl.f(r: P.H & U32, h: P.H, +x: U32, +situ: U32) -> Cl:
  (s, +f) = r
  cl.found(rg.find(h, situ, f), s, x, f)

def cl.go(g: Nat, c: Cl, +situ: U32) -> Cl:
  match g:
    case 0n:
      c
    case 1n+k:
      match c:
        case Cl{s, h, +x, done}:
          match done:
            case True{}:
              Cl{s, h, x, True{}}
            case False{}:
              cl.go(k, cl.f(P.rd(s, (x + 1 : U32)), h, x, situ), situ)

def sv.pair(r: P.H & P.H, +n: U32) -> Sv:
  (s, h) = r
  SvOk{s, h, n}

def sv.climbed(c: Cl, +situ: U32, +k: U32, +nc: U32, +n: U32) -> Sv:
  match c:
    case Cl{s, h, +x, done}:
      sv.pair(materialize(s, h, situ, x, k, nc, False{}), n)

# the frontier at port q: a cursor of the ring there, joined to nc; else
# the tree holding q climbed to and materialized
def sv.front.m(r: P.H & Maybe<&2, U32>, s: P.H, +situ: U32, +k: U32, +nc: U32, +q: U32, +n: U32) -> Sv:
  (h, m) = r
  match m:
    case Some{+c}:
      SvOk{s, join(h, nc, c), n}
    case None{}:
      sv.climbed(cl.go(1000000n, Cl{s, h, P.base(q), False{}}, situ), situ, k, nc, n)

def sv.static.w(r: P.H & U32, s: P.H, +nc: U32, +n: U32) -> Sv:
  (h, +w) = r
  SvOk{s, P.free(rg.unlink(P.put_st(h, w, P.era()), nc), nc), n}

# a stop, its own walk's interactions added
def sv.stop(d: KD.D, h: P.H, +acc: U32) -> Sv:
  match d:
    case KD.D{s, path, +top, +depth, +n, +st}:
      SvStop{KD.D{s, path, top, depth, n, st}, h, (acc + n : U32)}

def sv.pd(p: Q.Pd, h: P.H, +situ: U32, +k: U32, +nc: U32, +pos: U32) -> Sv:
  match p:
    case Q.PdValue{s, +q, +n}:
      sv.pair(materialize(s, h, situ, P.base(q), k, nc, U32.is_eq(pos, P.iface())), n)
    case Q.PdFront{s, +q, +n}:
      sv.front.m(rg.find(h, situ, q), s, situ, k, nc, q, n)
    case Q.PdStatic{s, +n}:
      sv.static.w(P.rd(h, (nc + 1 : U32)), s, nc, n)
    case Q.PdStop{d, +n}:
      sv.stop(d, h, n)

def sv.k(r: P.H & U32, s: P.H, +situ: U32, +nc: U32, +pos: U32, +g: Nat, +f: Nat) -> Sv:
  (h, +hd) = r
  sv.pd(Q.positioned(s, pos, g, f), h, situ, P.fld(hd), nc, pos)

def sv.situ(r: P.H & U32, s: P.H, +nc: U32, +pos: U32, +g: Nat, +f: Nat) -> Sv:
  (h, +situ) = r
  sv.k(P.rd(h, situ), s, situ, nc, pos, g, f)

def sv.pos(r: P.H & U32, s: P.H, +nc: U32, +g: Nat, +f: Nat) -> Sv:
  (h, +pos) = r
  sv.situ(rg.situ(h, nc), s, nc, pos, g, f)

# the negative cursor nc of host h served from its source s: positioned
# demand at its position, at most g walks of f steps, then materialized,
# joined or given a static
def serve(s: P.H, h: P.H, +nc: U32, +g: Nat, +f: Nat) -> Sv:
  sv.pos(P.rd(h, (nc + 2 : U32)), s, nc, g, f)

def sv.from.k(r: P.H & U32, d: KD.D, +situ: U32, +nc: U32, +pos: U32, +g: Nat, +f: Nat) -> Sv:
  (h, +hd) = r
  sv.pd(Q.positioned.from(d, pos, g, f), h, situ, P.fld(hd), nc, pos)

def sv.from.situ(r: P.H & U32, d: KD.D, +nc: U32, +pos: U32, +g: Nat, +f: Nat) -> Sv:
  (h, +situ) = r
  sv.from.k(P.rd(h, situ), d, situ, nc, pos, g, f)

def sv.from.pos(r: P.H & U32, d: KD.D, +nc: U32, +g: Nat, +f: Nat) -> Sv:
  (h, +pos) = r
  sv.from.situ(rg.situ(h, nc), d, nc, pos, g, f)

# and served going on from d, a walk in the source stopped and set going
# again, its path kept (cells-freeze.rewalk)
def serve.from(d: KD.D, h: P.H, +nc: U32, +g: Nat, +f: Nat) -> Sv:
  sv.from.pos(P.rd(h, (nc + 2 : U32)), d, nc, g, f)
