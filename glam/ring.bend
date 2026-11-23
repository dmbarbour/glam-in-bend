import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ./index.bend as X

# A copy's cursors and their joins (the Cells plan's
# cells-freeze.cursors.materialize; docs/reviews/Joins_2026-11-11.md),
# out of glam/materialize.bend, which uses them, so that their laws
# (glam/LAWS.bend) import the heap's primitives and the index alone: a
# copy's cursors are the leaves of a crit-bit index of the net's own
# nodes (glam/index.bend), round a situating node of form 2 holding the
# source's handle, each cursor's word 3 its home (cursors-indexed); a
# join replaces two cursors by one wire. The names (rg.*) are the ring's
# the index replaced.

# The index
# =========

# the cursor of situ's index at position far, if any
def rg.find(h: P.H, +situ: U32, +far: U32) -> P.H & Maybe<&2, U32>:
  X.ix.find(h, situ, far)

def rg.unlink.s(r: P.H & U32, +x: U32) -> P.H:
  (h, +s) = r
  X.ix.remove(h, s, x)

# x taken out of its home's index
def rg.unlink(h: P.H, +x: U32) -> P.H:
  rg.unlink.s(X.ix.home(h, x), x)

# x put in situ's index, its position already in word 2
def rg.insert(h: P.H, +situ: U32, +x: U32) -> P.H:
  X.ix.insert(h, situ, x)

# a cursor's form: 0 negative, standing for a value; 1 positive,
# receiving one
def cur.form(+neg: Bool) -> U32:
  match neg:
    case True{}:
      0
    case False{}:
      1

# a placeholder pl made a cursor at position src, its header and word 2
# written, and put in situ's index (out of glam/materialize.bend, as leave
# is, so that its laws import the heap's primitives alone)
def cursor(h: P.H, +situ: U32, +pl: U32, +src: U32, +neg: Bool) -> P.H:
  rg.insert(P.wr(P.wr(h, pl, P.hd2(18, cur.form(neg), 0)), (pl + 2 : U32), src), situ, pl)

# a cursor's home, one read
def rg.situ(h: P.H, +x: U32) -> P.H & U32:
  X.ix.home(h, x)

# Joins
# =====

def jn.w(r: P.H & U32, +u: U32, +x: U32, +y: U32) -> P.H:
  (h, +w) = r
  P.free(P.free(rg.unlink(rg.unlink(P.link_xx(h, u, w), x), y), x), y)

def jn.u(r: P.H & U32, +x: U32, +y: U32) -> P.H:
  (h, +u) = r
  jn.w(P.rd(h, (y + 1 : U32)), u, x, y)

# two cursors x and y of one index, both taken out of it, replaced by one
# wire between what each faced (a placeholder and a cursor: join1)
def join(h: P.H, +x: U32, +y: U32) -> P.H:
  jn.u(P.rd(h, (x + 1 : U32)), x, y)

def jn1.w(r: P.H & U32, +u: U32, +x: U32, +y: U32) -> P.H:
  (h, +w) = r
  P.free(P.free(rg.unlink(P.link_xx(h, u, w), y), x), y)

def jn1.u(r: P.H & U32, +x: U32, +y: U32) -> P.H:
  (h, +u) = r
  jn1.w(P.rd(h, (y + 1 : U32)), u, x, y)

# a placeholder x, in no index, and an index's cursor y, replaced by a wire
def join1(h: P.H, +x: U32, +y: U32) -> P.H:
  jn1.u(P.rd(h, (x + 1 : U32)), x, y)

# a crossing's placeholder pl, standing at position src, its far end at
# position far: joined to the cursor of situ's index there, if any, else
# made a cursor in the index (out of glam/materialize.bend, as cursor is)
def cross.k(r: P.H & Maybe<&2, U32>, +situ: U32, +pl: U32, +src: U32, +neg: Bool) -> P.H:
  (h, m) = r
  match m:
    case Some{+y}:
      join1(h, pl, y)
    case None{}:
      cursor(h, situ, pl, src, neg)

def cross(h: P.H, +situ: U32, +pl: U32, +src: U32, +neg: Bool, +far: U32) -> P.H:
  cross.k(rg.find(h, situ, far), situ, pl, src, neg)

# A serve's crossings
# ===================

# a cursor of the copy, a crossing of the index it joins: the placeholder's
# index in the template, the source's reference of the finished node's
# port, whether that port is negative, the copy awaiting a value there,
# and the port it faces in the source, its far end (built by
# glam/freeze.bend; here so that the cursors' laws take it)
type FzC is Data:
  FzC{+at: U32, +src: U32, neg: Bool, +far: U32}

def crossing.pl(r: Array<U32> & U32, h: P.H, +situ: U32, +src: U32, +neg: Bool, +far: U32) -> Array<U32> & P.H:
  (map, +pl) = r
  (map, cross(h, situ, pl, src, neg, far))

def crossing(q: Array<U32> & P.H, c: FzC, +situ: U32) -> Array<U32> & P.H:
  (map, h) = q
  match c:
    case FzC{+at, +src, neg, +far}:
      crossing.pl(Array.get(U32, map, at), h, situ, src, neg, far)

# the copy's crossings in turn, each placeholder found through map, the
# template's index to its node (moved from glam/materialize.bend)
def crossings(cs: List<&2, FzC>, q: Array<U32> & P.H, +situ: U32) -> Array<U32> & P.H:
  match cs:
    case Nil{}:
      q
    case Con{c, rest}:
      crossings(rest, crossing(q, c, situ), situ)

def lv.w(r: P.H & U32, +p: U32, +c: U32) -> P.H:
  (h, +w) = r
  P.free(rg.unlink(P.link_xx(h, p, w), c), c)

# an index's cursor c left: the port it faced linked to port p, which may
# be static (the copy's root, joined to the served cursor; or the eraser,
# given to the served cursor's peer), c unlinked and freed
def leave(h: P.H, +p: U32, +c: U32) -> P.H:
  lv.w(P.rd(h, (c + 1 : U32)), p, c)
