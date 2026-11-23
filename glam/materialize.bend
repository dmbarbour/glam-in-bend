import Base
import ../spike/val.bend as V
import ../spike/tpl.bend as T
import ../spike/kprim.bend as P
import ../spike/kdemand.bend as KD
import ../spike/kmem_grow.bend as KM
import ./splice_copy.bend as S
import ./freeze.bend as F
import ./position.bend as Q
import ./ring.bend as R

# Materializing (the Cells plan's cells-freeze.cursors.materialize, the
# design in docs/reviews/Joins_2026-11-11.md): a copy's cursor served
# from its live source, the newly finished nodes copied into the host
# and every wire leaving them joined.
#
# A copy's cursors live in its index (glam/index.bend; cursors-indexed),
# a crit-bit tree of the host's nodes keyed by position, its root in word
# 3 of one situating node, which holds the source's handle (word 2) and
# the copy's level offset (its field); form 2 of the cursor kind. A cursor holds its
# position in the source in word 2: form 0 negative, standing for a
# value; form 1 positive, receiving one. A use of a live template is a
# negative cursor at the source's interface, so the first copy is a serve
# like any other.
#
# Serving a negative cursor runs positioned demand at its position
# (`glam/position.bend`), then:
# - a value: the finished tree under it is frozen (`F.freeze_tree`),
#   spliced at the offset, and each wire leaving it joined: its far end
#   looked up in the index, a cursor there replaced by the wire, the
#   served cursor among them; otherwise a new cursor of the port's
#   polarity, put in the index;
# - the frontier: a cursor of the index at the port reached is joined to
#   the served one directly, nothing copied (the identity's case); else
#   the finished tree holding that port is found by climbing its
#   principal links to a position the index holds, and materialized;
# - a static: the served cursor's peer gets it;
# - a cursor of the source, a copy it holds of another live source: left
#   to the core, which serves that one into this source first, then this
#   one again (cells-freeze.nested).
#
# Not yet: the marks on copied nodes (`copied-nodes-untouched`), so a
# source must run no events, fusion or collection near copied nodes;
# scratch the size of the source in each freeze.

# the copy's root, where the tree faced the source's interface (a first
# copy): joined to the served cursor nc, which leaves the index
def mz.root.e(r: Array<U32> & U32, h: P.H, +p: U32, +nc: U32) -> P.H:
  (map, +n) = r
  R.leave(h, (n + p : U32), nc)

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

def mz.sp(s: S.Sp, curs: List<&2, R.FzC>, root: T.TEnd, +situ: U32, +nc: U32, +at_root: Bool) -> P.H:
  match s:
    case S.Sp{h, map}:
      mz.sp.r(R.crossings(curs, (map, h), situ), root, nc, at_root)

# a materialization's end: the source, the host, and the nodes copied,
# each a cursor interaction: the cursor replaced by a node, new cursors
# behind it (the maintainer, 2026-11-13)
type Mz is Type:
  Mz{s: P.H, h: P.H, +m: U32}
  # and the source wholly finished, its whole template t: frozen at its
  # root with no crossing, so that everything its interface reaches was
  # copied (finished-sources-freeze; cells-freeze.whole)
  MzW{s: P.H, h: P.H, +m: U32, t: T.Tpl}

# no crossing
def mz.none(cs: List<&2, R.FzC>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, r}:
      False{}

def mz.end(+whole: Bool, s: P.H, h: P.H, +m: U32, +t: T.Tpl) -> Mz:
  match whole:
    case True{}:
      MzW{s, h, m, t}
    case False{}:
      Mz{s, h, m}

def mz.fz.t(+whole: Bool, s: P.H, +t: T.Tpl, +curs: List<&2, R.FzC>, +m: U32, h: P.H, +situ: U32, +k: U32, +nc: U32, +at_root: Bool) -> Mz:
  match t:
    case T.Tpl{nodes, links, root, +size}:
      mz.end(whole, s, mz.sp(S.sp.links(links, S.sp.nodes(nodes, 0, S.Sp{h, [0 : U32^T.depth_for(31n, size, 0n)]}, k)), curs, root, situ, nc, at_root), m, t)

def mz.fz(r: P.H & F.Fz, h: P.H, +situ: U32, +k: U32, +nc: U32, +at_root: Bool) -> Mz:
  (s, f) = r
  match f:
    case F.Fz{+t, +curs, +m}:
      mz.fz.t(at_root && mz.none(curs), s, t, curs, m, h, situ, k, nc, at_root)

# the finished tree at node base v of source s copied into host h at
# offset k, its wires joined through situ's index; at_root where it is the
# source's root, faced by the interface, served by cursor nc
def materialize(s: P.H, h: P.H, +situ: U32, +v: U32, +k: U32, +nc: U32, +at_root: Bool) -> Mz:
  mz.fz(F.freeze_tree(s, v), h, situ, k, nc, at_root)

# Serving
# =======

# a serve's end: the source and the host, or positioned demand's stop in
# the source, as it stood; with the interactions made in the source, and
# a done serve's cursor interactions: the nodes it copied, or one where
# it joined the cursor or gave it a static
type Sv is Type:
  SvOk{s: P.H, h: P.H, +n: U32, +m: U32}
  SvStop{d: KD.D, h: P.H, +n: U32}
  # the position faces cursor x of the source, a copy it holds of another
  # live source, which the core serves into it first (cells-freeze.nested)
  SvCur{s: P.H, h: P.H, +x: U32, +n: U32}
  # a done serve at the source's root that found the source wholly
  # finished: its whole template t, which the source's cell takes, later
  # uses splicing it (finished-sources-freeze)
  SvWhole{s: P.H, h: P.H, +n: U32, +m: U32, t: T.Tpl}
  # corruption a well-formed source and index never reach: a climb that
  # found no position of the index, or a frontier facing the served
  # cursor's own position; the core stops with an error, since the cursor
  # left unserved would be served again without end
  SvBad{s: P.H, h: P.H, +n: U32}

# a climb from a finished node of the source toward the root of its tree,
# a node whose principal faces a position the index holds
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
  cl.found(R.rg.find(h, situ, f), s, x, f)

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

def sv.pair(r: Mz, +n: U32) -> Sv:
  match r:
    case Mz{s, h, +m}:
      SvOk{s, h, n, m}
    case MzW{s, h, +m, t}:
      SvWhole{s, h, n, m, t}

# a climb that found no position of the index: corruption, which a
# well-formed source and index never reach (each tree a copy takes hangs
# from a node it holds), reported and nothing copied
# (corruption-reported-when-cheap; docs/reviews/Freeze_2026-11-21.md, B4)
def sv.climbed.k(+done: Bool, s: P.H, h: P.H, +x: U32, +situ: U32, +k: U32, +nc: U32, +n: U32) -> Sv:
  match done:
    case True{}:
      sv.pair(materialize(s, h, situ, x, k, nc, False{}), n)
    case False{}:
      SvBad{s, h, n}

def sv.climbed(c: Cl, +situ: U32, +k: U32, +nc: U32, +n: U32) -> Sv:
  match c:
    case Cl{s, h, +x, done}:
      sv.climbed.k(done, s, h, x, situ, k, nc, n)

# a climb's fuel: the source's nodes, one step a node at most
def sv.climb.f(r: P.H & P.HS, h: P.H, +situ: U32, +k: U32, +nc: U32, +q: U32, +n: U32) -> Sv:
  (s, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      sv.climbed(cl.go(U32.to_nat((cap + 1 : U32)), Cl{s, h, P.base(q), False{}}, situ), situ, k, nc, n)

# the frontier's cursor c joined to nc; nc itself, a port facing its own
# position, which a well-formed source never holds, is corruption,
# reported and nothing joined: a join of a cursor with itself frees one
# node twice (corruption-reported-when-cheap; one compare a serve, until
# a law of freeze shows it unreached, cells-freeze.nested.host.join.self)
def sv.front.c(+same: Bool, s: P.H, h: P.H, +nc: U32, +c: U32, +n: U32) -> Sv:
  match same:
    case True{}:
      SvBad{s, h, n}
    case False{}:
      SvOk{s, R.join(h, nc, c), n, 1}

# the frontier at port q: a cursor of the index there, joined to nc; else
# the tree holding q climbed to and materialized
def sv.front.m(r: P.H & Maybe<&2, U32>, s: P.H, +situ: U32, +k: U32, +nc: U32, +q: U32, +n: U32) -> Sv:
  (h, m) = r
  match m:
    case Some{+c}:
      sv.front.c(U32.is_eq(c, nc), s, h, nc, c, n)
    case None{}:
      sv.climb.f(P.stats(s), h, situ, k, nc, q, n)

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
      sv.front.m(R.rg.find(h, situ, q), s, situ, k, nc, q, n)
    case Q.PdCur{s, +x, +n}:
      SvCur{s, h, x, n}
    case Q.PdStatic{s, +n}:
      SvOk{s, R.leave(h, P.era(), nc), n, 1}
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
  sv.situ(R.rg.situ(h, nc), s, nc, pos, g, f)

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
  sv.from.situ(R.rg.situ(h, nc), d, nc, pos, g, f)

# and served going on from d, a walk in the source stopped and set going
# again, its path kept (cells-freeze.rewalk)
def serve.from(d: KD.D, h: P.H, +nc: U32, +g: Nat, +f: Nat) -> Sv:
  sv.from.pos(P.rd(h, (nc + 2 : U32)), d, nc, g, f)

# One net
# =======
#
# A copy of a source in itself (self-copies-are-cursors, the Cells plan's
# cells-freeze.nested.self): served as any copy is, positioned demand at
# the cursor's position, then the finished tree there frozen and spliced
# back where the cursor stands, its wires joined in the same net. The
# walk that needed the copy is released before, being reentered.

# a one-net serve's end, as Sv's with the host and the source one net
type Sv1 is Type:
  S1Ok{h: P.H, +n: U32, +m: U32}
  S1Stop{d: KD.D, +n: U32}
  S1Cur{h: P.H, +x: U32, +n: U32}
  S1Bad{h: P.H, +n: U32}

def mz1.fz(r: P.H & F.Fz, +situ: U32, +k: U32, +nc: U32, +at_root: Bool) -> P.H & U32:
  (h, f) = r
  match f:
    case F.Fz{t, curs, +m}:
      match t:
        case T.Tpl{nodes, links, root, +size}:
          (mz.sp(S.sp.links(links, S.sp.nodes(nodes, 0, S.Sp{h, [0 : U32^T.depth_for(31n, size, 0n)]}, k)), curs, root, situ, nc, at_root), m)

# the finished tree at node base v of net h copied into h itself at
# offset k, as materialize does between two nets
def materialize1(h: P.H, +situ: U32, +v: U32, +k: U32, +nc: U32, +at_root: Bool) -> P.H & U32:
  mz1.fz(F.freeze_tree(h, v), situ, k, nc, at_root)

def sv1.ok(r: P.H & U32, +n: U32) -> Sv1:
  (h, +m) = r
  S1Ok{h, n, m}

# a climb, as Cl's, in one net
type Cl1 is Type:
  Cl1{h: P.H, +x: U32, done: Bool}

def cl1.k(m: Maybe<&2, U32>, h: P.H, +x: U32, +f: U32) -> Cl1:
  match m:
    case Some{+c}:
      Cl1{h, x, True{}}
    case None{}:
      Cl1{h, P.base(f), False{}}

def cl1.found(r: P.H & Maybe<&2, U32>, +x: U32, +f: U32) -> Cl1:
  (h, m) = r
  cl1.k(m, h, x, f)

def cl1.f(r: P.H & U32, +x: U32, +situ: U32) -> Cl1:
  (h, +f) = r
  cl1.found(R.rg.find(h, situ, f), x, f)

def cl1.go(g: Nat, c: Cl1, +situ: U32) -> Cl1:
  match g:
    case 0n:
      c
    case 1n+k:
      match c:
        case Cl1{h, +x, done}:
          match done:
            case True{}:
              Cl1{h, x, True{}}
            case False{}:
              cl1.go(k, cl1.f(P.rd(h, (x + 1 : U32)), x, situ), situ)

def sv1.climbed.k(+done: Bool, h: P.H, +x: U32, +situ: U32, +k: U32, +nc: U32, +n: U32) -> Sv1:
  match done:
    case True{}:
      sv1.ok(materialize1(h, situ, x, k, nc, False{}), n)
    case False{}:
      S1Bad{h, n}

def sv1.climbed(c: Cl1, +situ: U32, +k: U32, +nc: U32, +n: U32) -> Sv1:
  match c:
    case Cl1{h, +x, done}:
      sv1.climbed.k(done, h, x, situ, k, nc, n)

def sv1.climb.f(r: P.H & P.HS, +situ: U32, +k: U32, +nc: U32, +q: U32, +n: U32) -> Sv1:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      sv1.climbed(cl1.go(U32.to_nat((cap + 1 : U32)), Cl1{h, P.base(q), False{}}, situ), situ, k, nc, n)

# as sv.front.c, on the one-net path
def sv1.front.c(+same: Bool, h: P.H, +nc: U32, +c: U32, +n: U32) -> Sv1:
  match same:
    case True{}:
      S1Bad{h, n}
    case False{}:
      S1Ok{R.join(h, nc, c), n, 1}

def sv1.front.m(r: P.H & Maybe<&2, U32>, +situ: U32, +k: U32, +nc: U32, +q: U32, +n: U32) -> Sv1:
  (h, m) = r
  match m:
    case Some{+c}:
      sv1.front.c(U32.is_eq(c, nc), h, nc, c, n)
    case None{}:
      sv1.climb.f(P.stats(h), situ, k, nc, q, n)

def sv1.stop(d: KD.D, +acc: U32) -> Sv1:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      S1Stop{KD.D{h, path, top, depth, n, st}, (acc + n : U32)}

def sv1.pd(p: Q.Pd, +situ: U32, +k: U32, +nc: U32, +pos: U32) -> Sv1:
  match p:
    case Q.PdValue{h, +q, +n}:
      sv1.ok(materialize1(h, situ, P.base(q), k, nc, U32.is_eq(pos, P.iface())), n)
    case Q.PdFront{h, +q, +n}:
      sv1.front.m(R.rg.find(h, situ, q), situ, k, nc, q, n)
    case Q.PdCur{h, +x, +n}:
      S1Cur{h, x, n}
    case Q.PdStatic{h, +n}:
      S1Ok{R.leave(h, P.era(), nc), n, 1}
    case Q.PdStop{d, +n}:
      sv1.stop(d, n)

def sv1.k(r: P.H & U32, +situ: U32, +nc: U32, +pos: U32, +g: Nat, +f: Nat) -> Sv1:
  (h, +hd) = r
  sv1.pd(Q.positioned(h, pos, g, f), situ, P.fld(hd), nc, pos)

def sv1.situ(r: P.H & U32, +nc: U32, +pos: U32, +g: Nat, +f: Nat) -> Sv1:
  (h, +situ) = r
  sv1.k(P.rd(h, situ), situ, nc, pos, g, f)

def sv1.pos(r: P.H & U32, +nc: U32, +g: Nat, +f: Nat) -> Sv1:
  (h, +pos) = r
  sv1.situ(R.rg.situ(h, nc), nc, pos, g, f)

# the negative cursor nc of net h served from h itself
def serve1(h: P.H, +nc: U32, +g: Nat, +f: Nat) -> Sv1:
  sv1.pos(P.rd(h, (nc + 2 : U32)), nc, g, f)

def sv1.from.k(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +situ: U32, +nc: U32, +pos: U32, +g: Nat, +f: Nat) -> Sv1:
  (h, +hd) = r
  sv1.pd(Q.positioned.from(KD.D{h, path, top, depth, n, st}, pos, g, f), situ, P.fld(hd), nc, pos)

def sv1.from.situ(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +nc: U32, +pos: U32, +g: Nat, +f: Nat) -> Sv1:
  (h, +situ) = r
  sv1.from.k(P.rd(h, situ), path, top, depth, n, st, situ, nc, pos, g, f)

def sv1.from.pos(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +nc: U32, +g: Nat, +f: Nat) -> Sv1:
  (h, +pos) = r
  sv1.from.situ(R.rg.situ(h, nc), path, top, depth, n, st, nc, pos, g, f)

# and served going on from d, a walk in the net stopped and set going
# again, its path kept
def serve1.from(d: KD.D, +nc: U32, +g: Nat, +f: Nat) -> Sv1:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      sv1.from.pos(P.rd(h, (nc + 2 : U32)), path, top, depth, n, st, nc, g, f)
