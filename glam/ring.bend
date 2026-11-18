import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V

# A copy's ring and its joins (the Cells plan's
# cells-freeze.cursors.materialize; docs/reviews/Joins_2026-11-11.md),
# out of glam/materialize.bend, which uses them, so that the laws of
# rings (glam/LAWS.bend) import the heap's primitives alone (kprim, its
# store and its values): a ring is a
# copy's cursors linked through word 3, round a situating node of form 2
# holding the source's handle; a join replaces two cursors by one wire.

# A ring
# ======

def rg.next(h: P.H, +x: U32) -> P.H & U32:
  P.rd(h, (x + 3 : U32))

# a walk's fuel: the heap's words, so that a walk round an exact ring,
# whose members' word 3 lie in distinct words, never runs out
# (ring-walks-fueled-by-heap)
def rg.fuel.s(r: Array<U32> & U32, a: Array<V.Val>) -> P.H & Nat:
  (w, +n) = r
  (P.H{KM.MG{w}, a}, U32.to_nat(n))

def rg.fuel(h: P.H) -> P.H & Nat:
  match h:
    case P.H{w, a}:
      match w:
        case KM.MG{x}:
          rg.fuel.s(Array.size(U32, x), a)

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

# a walk's end; one out of fuel, on a corrupt ring, raises the kernel's
# error (corruption-reported-when-cheap)
def rg.found(w: Rw) -> P.H & Maybe<&2, U32>:
  match w:
    case Rw{h, +x, +p, found, done}:
      (P.err_if(Bool.not(done), h), found)

# the cursor of situ's ring at position far, if any
def rg.find.f(r: P.H & Nat, +situ: U32, +far: U32) -> P.H & Maybe<&2, U32>:
  (h, f) = r
  rg.found(rg.find.go(f, rw.on(rg.next(h, situ), situ), situ, far))

def rg.find(h: P.H, +situ: U32, +far: U32) -> P.H & Maybe<&2, U32>:
  rg.find.f(rg.fuel(h), situ, far)

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

def rg.pred.w(w: Rw) -> P.H & U32:
  match w:
    case Rw{h, +n, +p, found, done}:
      (P.err_if(Bool.not(done), h), p)

# x's predecessor in its ring, found by walking from x
def rg.pred.f(r: P.H & Nat, +x: U32) -> P.H & U32:
  (h, f) = r
  rg.pred.w(rg.pred.go(f, rw.on(rg.next(h, x), x), x))

def rg.pred(h: P.H, +x: U32) -> P.H & U32:
  rg.pred.f(rg.fuel(h), x)

def rg.unlink.set(r: P.H & U32, +p: U32) -> P.H:
  (h, +nx) = r
  P.wr(h, (p + 3 : U32), nx)

def rg.unlink.p(r: P.H & U32, +x: U32) -> P.H:
  (h, +p) = r
  rg.unlink.set(rg.next(h, x), p)

# x taken out of its ring: its predecessor's word 3 given x's
def rg.unlink(h: P.H, +x: U32) -> P.H:
  rg.unlink.p(rg.pred(h, x), x)

# x put in situ's ring, after situ
def rg.insert.r(r: P.H & U32, +situ: U32, +x: U32) -> P.H:
  (h, +n) = r
  P.wr(P.wr(h, (x + 3 : U32), n), (situ + 3 : U32), x)

def rg.insert(h: P.H, +situ: U32, +x: U32) -> P.H:
  rg.insert.r(rg.next(h, situ), situ, x)

# a cursor's form: 0 negative, standing for a value; 1 positive,
# receiving one
def cur.form(+neg: Bool) -> U32:
  match neg:
    case True{}:
      0
    case False{}:
      1

# a placeholder pl made a cursor at position src, its header and word 2
# written, and put in situ's ring (out of glam/materialize.bend, as leave
# is, so that its laws import the heap's primitives alone)
def cursor(h: P.H, +situ: U32, +pl: U32, +src: U32, +neg: Bool) -> P.H:
  rg.insert(P.wr(P.wr(h, pl, P.hd2(18, cur.form(neg), 0)), (pl + 2 : U32), src), situ, pl)

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
      (P.err_if(Bool.not(done), h), n)

# the situating node of x's ring
def rg.situ.f(r: P.H & Nat, +x: U32) -> P.H & U32:
  (h, f) = r
  rg.situ.w(rg.situ.go(f, Rw{h, x, x, None{}, False{}}))

def rg.situ(h: P.H, +x: U32) -> P.H & U32:
  rg.situ.f(rg.fuel(h), x)

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

# a crossing's placeholder pl, standing at position src, its far end at
# position far: joined to the cursor of situ's ring there, if any, else
# made a cursor in the ring (out of glam/materialize.bend, as cursor is)
def cross.k(r: P.H & Maybe<&2, U32>, +situ: U32, +pl: U32, +src: U32, +neg: Bool) -> P.H:
  (h, m) = r
  match m:
    case Some{+y}:
      join1(h, pl, y)
    case None{}:
      cursor(h, situ, pl, src, neg)

def cross(h: P.H, +situ: U32, +pl: U32, +src: U32, +neg: Bool, +far: U32) -> P.H:
  cross.k(rg.find(h, situ, far), situ, pl, src, neg)

def lv.w(r: P.H & U32, +p: U32, +c: U32) -> P.H:
  (h, +w) = r
  P.free(rg.unlink(P.link_xx(h, p, w), c), c)

# a ring's cursor c left: the port it faced linked to port p, which may
# be static (the copy's root, joined to the served cursor; or the eraser,
# given to the served cursor's peer), c unlinked and freed
def leave(h: P.H, +p: U32, +c: U32) -> P.H:
  lv.w(P.rd(h, (c + 1 : U32)), p, c)
