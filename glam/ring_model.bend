import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD
import ./ring.bend as R
import ../spike/kmodel.bend as KMd
import ./index_model.bend as IM

# A copy's cursors, modelled for glam's laws (glam/LAWS.bend; the Cells
# plan's cells-freeze.nested.host.ring, then .sharing.cursors.index): no
# code of the materializer calls these. Stated on the heap's words read as
# a list (lawful-arrays' view, AD.view), data that copies freely, by node
# bases: the situating node, the cursors (the leaves of a copy's index,
# glam/index_model.bend), the placeholders pending, the free list's first
# nodes. The names (ring_model, RG) are the ring's the index replaced.

# whether x is among xs
def has(xs: List<&2, U32>, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+h, t}:
      U32.is_eq(h, x) || has(t, x)

# members of ys all members of M
def sub(ys: List<&2, U32>, +M: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, t}:
      has(M, y) && sub(t, M)

# no member of ys a member of M
def none.in(ys: List<&2, U32>, +M: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, t}:
      Bool.not(has(M, y)) && none.in(t, M)

# no member of ys listed twice
def distinct(ys: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, +t}:
      Bool.not(has(t, y)) && distinct(t)

# a heap's words, as the laws read a heap after a step
def words(h: P.H) -> Array<U32>:
  match h:
    case P.H{w, a}:
      match w:
        case KM.MG{x}:
          x

# x's word 3 is no member's word 3, slot by slot: a node apart from the
# nodes xs
def apart(ys: List<&2, U32>, +d: Nat, +x: U32) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, t}:
      Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d))) && apart(t, d, x)

# word j's slot none of node m's four words' slots
def off.node(+d: Nat, +m: U32, +j: U32) -> Bool:
  Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))) && (Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))) && (Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))) && Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d)))))

# word i's slot no member's word 3: a write there leaves the cursors'
# homes, and a word so placed is none a join writes in a cursor
def off.links(ys: List<&2, U32>, +d: Nat, +i: U32) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, t}:
      Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((y + 3 : U32), d))) && off.links(t, d, i)

# no two members' word 3 in one slot
def apart.all(ys: List<&2, U32>, +d: Nat) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, +t}:
      apart(t, d, y) && apart.all(t, d)

# a list with x taken out, for laws stated by membership (JoinExact
# review, F1)
def keep(+b: Bool, +y: U32) -> List<&2, U32>:
  match b:
    case True{}:
      Nil{}
    case False{}:
      Con{y, Nil{}}

# ys without x
def without(ys: List<&2, U32>, +x: U32) -> List<&2, U32>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{+y, t}:
      List.append(&2, U32, keep(U32.is_eq(y, x), y), without(t, x))

# A find's model (cells-freeze.nested.host.serve): a member's word 2, its
# position, among words v, is far
def pos.is.m(m: Maybe<&2, U32>, +far: U32) -> Bool:
  match m:
    case Some{+q}:
      U32.is_eq(q, far)
    case None{}:
      False{}

def pos.is(+v: List<&2, U32>, +d: Nat, +y: U32, +far: U32) -> Bool:
  pos.is.m(List.get(&2, U32, v, AD.slot((y + 2 : U32), d)), far)

def first.k(+b: Bool, +y: U32, +r: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match b:
    case True{}:
      Some{y}
    case False{}:
      r

# the first of ys, in walk order, at position far, as a find stops at it
def first(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +far: U32) -> Maybe<&2, U32>:
  match ys:
    case Nil{}:
      None{}
    case Con{+y, r}:
      first.k(pos.is(v, d, y, far), y, first(r, v, d, far))

# a node's four words
def nw(+a: U32) -> List<&2, U32>:
  Con{a, Con{(a + 1 : U32), Con{(a + 2 : U32), Con{(a + 3 : U32), Nil{}}}}}

# word j's slot none of ws's
def off(ws: List<&2, U32>, +d: Nat, +j: U32) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+v, t}:
      Bool.not(Nat.is_eq(AD.slot(v, d), AD.slot(j, d))) && off(t, d, j)

# no two of ws in one slot
def apartw(ws: List<&2, U32>, +d: Nat) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+v, +t}:
      off(t, d, v) && apartw(t, d)

# none of node a's words in a slot of node b's
def disj4(+d: Nat, +a: U32, +b: U32) -> Bool:
  off(nw(b), d, a) && (off(nw(b), d, (a + 1 : U32)) && (off(nw(b), d, (a + 2 : U32)) && off(nw(b), d, (a + 3 : U32))))

# node a apart from every node of ys
def cross(ys: List<&2, U32>, +d: Nat, +a: U32) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+b, t}:
      disj4(d, a, b) && cross(t, d, a)

# the nodes of ys laid out apart: each node's four words in four slots,
# none on the free list's head, no two nodes sharing a slot
def layout(ys: List<&2, U32>, +d: Nat) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+a, +t}:
      apartw(nw(a), d) && (off(nw(a), d, P.at_fh()) && (cross(t, d, a) && layout(t, d)))

# every member its own node's base
def bases(ys: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+m, t}:
      U32.is_eq(P.base(m), m) && bases(t)

# word i's slot no member's word 2, its position: a write there leaves
# the positions a find reads
def off.pos(ys: List<&2, U32>, +d: Nat, +i: U32) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, t}:
      Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((y + 2 : U32), d))) && off.pos(t, d, i)

# a port r faceable by M's members: its link word, r + 1, in no member's
# word 3 nor word 2, so that linking it leaves the cursors' homes and
# keys (ring-ports-faced-off-positions); a member's word 1 may be
# faced, two cursors facing each other. A static has no link word, and
# r + 1 holds of every static by alignment, not by its value: r ends in
# 11, so r + 1 in 00, a node's word 0, while a member is a node's base
# (bases) and the heap's depth at least 2 (layout), so that a slot keeps
# a word's low two bits and a member's words 2 and 3 end in 10 and 11
# (docs/reviews/Refs_2026-11-18.md, Corrections)
def port.ok(+M: List<&2, U32>, +d: Nat, +r: U32) -> Bool:
  off.links(M, d, (r + 1 : U32)) && off.pos(M, d, (r + 1 : U32))

# what a member faces, by its word 1: a port faceable by M's members
def faces.m(m: Maybe<&2, U32>, +d: Nat, +M: List<&2, U32>) -> Bool:
  match m:
    case Some{+r}:
      port.ok(M, d, r)
    case None{}:
      False{}

def faces(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +M: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+m, t}:
      faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, M) && faces(t, v, d, M)

def pl.of(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{+q}:
      q
    case None{}:
      0

# the placeholders a copy's crossings name, each through the map's view vm
# (the map a perfect tree of depth dm: each the node map holds at the
# crossing's index, LA.get_view)
def pls(cs: List<&2, R.FzC>, +vm: List<&2, U32>, +dm: Nat) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, r}:
      match c:
        case R.FzC{+at, +src, neg, +far}:
          Con{pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), pls(r, vm, dm)}

# The crossings' writes by region (crossings_keeps): the ports the nodes
# of ys face, by their words 1 among v
def faced(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat) -> List<&2, U32>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{+m, r}:
      Con{pl.of(List.get(&2, U32, v, AD.slot((m + 1 : U32), d))), faced(r, v, d)}

# the members of xs not among ys
def minus.k(+b: Bool, +x: U32, r: List<&2, U32>) -> List<&2, U32>:
  match b:
    case True{}:
      r
    case False{}:
      Con{x, r}

def minus(xs: List<&2, U32>, +ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, r}:
      minus.k(has(ys, x), x, minus(r, ys))

# word j in no node of ys
def off.nodes(ys: List<&2, U32>, +d: Nat, +j: U32) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+m, r}:
      off.node(d, m, j) && off.nodes(r, d, j)

# word j no link word of a port of fs (KMd.off.port: a static, no
# node's, has none)
def off.ports(fs: List<&2, U32>, +d: Nat, +j: U32) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{+f, r}:
      KMd.off.port(d, f, j) && off.ports(r, d, j)

# port r's link word off node n's words, all four where n is not live
def po.n(+r: U32, +L: List<&2, U32>, +d: Nat, +n: U32) -> Bool:
  KMd.off.port(d, r, n) && Bool.or(has(L, n), KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32))))

# and off the free list's head, which the list's chain reads
def po.all(+r: U32, +L: List<&2, U32>, +d: Nat, N: List<&2, U32>) -> Bool:
  match N:
    case Nil{}:
      KMd.off.port(d, r, P.at_fh())
    case Con{+n, t}:
      po.n(r, L, d, n) && po.all(r, L, d, t)

# the port each of ys faces (its word 1) so, over the tracked nodes N
def px.off(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +L: List<&2, U32>, +N: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+z, t}:
      po.all(KMd.word(v, d, (z + 1 : U32)), L, d, N) && px.off(t, v, d, L, N)

# z, facing port r, faced back by each node of Q whose word 1 r's link
# word is: that node's faced port's link word z's word 1, by slots, as a
# link's writes land
def tw.q(Q: List<&2, U32>, +r: U32, +z: U32, +v: List<&2, U32>, +d: Nat) -> Bool:
  match Q:
    case Nil{}:
      True{}
    case Con{+q, t}:
      Bool.or(KMd.off.port(d, r, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, (q + 1 : U32)), (z + 1 : U32)))) && tw.q(t, r, z, v, d)

# each of ys facing not itself (its faced port's link word off its own
# word 1), and faced back by the live node it faces
def px.tw(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +L: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+z, t}:
      KMd.off.port(d, KMd.word(v, d, (z + 1 : U32)), (z + 1 : U32)) && (tw.q(L, KMd.word(v, d, (z + 1 : U32)), z, v, d) && px.tw(t, v, d, L))

# the invariant: the index realized, on its invariant, laid out; s and the
# cursors live, the pending live and of no role else, listed once; no
# branch live; the free list's first nodes F listed once, of no role
# else; the live, the free and the index's nodes all tracked; the live
# facing as above
def px.ok(+v: List<&2, U32>, +d: Nat, +s: U32, +I: IM.Ix, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>) -> Bool:
  IM.ix.real(v, d, s, I) && (IM.ix.inv(I) && (IM.ix.lay(I, s, d) && (sub(Con{s, IM.ix.leaves(I)}, L) && (sub(ps, L) && (none.in(ps, Con{s, IM.ix.nodes(I)}) && (distinct(ps) && (none.in(L, IM.ix.branches(I)) && (KMd.chain(F, v, d, KMd.word(v, d, P.at_fh())) && (distinct(F) && (none.in(F, Con{s, IM.ix.nodes(I)}) && (none.in(F, L) && (sub(L, N) && (sub(F, N) && (sub(IM.ix.nodes(I), N) && (faces(L, v, d, L) && (px.off(L, v, d, L, N) && px.tw(L, v, d, L)))))))))))))))))

def isnone(m: Maybe<&2, U32>) -> Bool:
  match m:
    case Some{+y}:
      False{}
    case None{}:
      True{}

# A crossing over the index (R.cross): the find at its far end m, the
# placeholder x joined to the cursor found (the index without it, the
# live nodes without both, the free list's first nodes y, x, the parent
# freed, then the list before), else made a cursor at its position src
# (put, the branch b the list's first node in a tree)
def cx.I(m: Maybe<&2, U32>, +I: IM.Ix, +x: U32, +src: U32, +b: U32, +far: U32) -> IM.Ix:
  match m:
    case Some{+y}:
      IM.ix.del(I, y, far)
    case None{}:
      IM.ix.put(I, x, src, b)

def cx.L(m: Maybe<&2, U32>, +x: U32, +L: List<&2, U32>) -> List<&2, U32>:
  match m:
    case Some{+y}:
      without(without(L, x), y)
    case None{}:
      L

# the free list's first nodes before: as they are for a join, the branch b
# first for an insert into a tree
def cx.F0(m: Maybe<&2, U32>, +I: IM.Ix, +b: U32, +F: List<&2, U32>) -> List<&2, U32>:
  match m:
    case Some{+y}:
      F
    case None{}:
      IM.ix.take(I, b, F)

def cx.F1(m: Maybe<&2, U32>, +I: IM.Ix, +x: U32, +far: U32, +F: List<&2, U32>) -> List<&2, U32>:
  match m:
    case Some{+y}:
      Con{y, Con{x, IM.mb.cons(IM.ix.par(I, y, far), F)}}
    case None{}:
      F

# the crossing's own position absent from the index where it makes a
# cursor (one cursor a position; serve-premises-over-index)
def cx.ab(m: Maybe<&2, U32>, +I: IM.Ix, +src: U32) -> Bool:
  match m:
    case Some{+y}:
      True{}
    case None{}:
      isnone(IM.ix.look(I, src))

# A copy's crossings over the index (R.crossings; crossings_pend): each
# crossing's placeholder the node map holds at its index (pls), its find
# the index's lookup, so that the model shares none of the code's finds;
# one making a cursor in a tree takes its branch from the free list's
# first node, the list after it the rest
def cx.hd(F: List<&2, U32>) -> U32:
  match F:
    case Nil{}:
      0
    case Con{+b, r}:
      b

def cx.tl(m: Maybe<&2, U32>, +I: IM.Ix, F: List<&2, U32>) -> List<&2, U32>:
  match m:
    case Some{+y}:
      F
    case None{}:
      match I:
        case IM.Ept{}:
          F
        case IM.Has{+t}:
          match F:
            case Nil{}:
              Nil{}
            case Con{+b, r}:
              r

# room for the branch a cursor made in a tree takes
def cx.room(m: Maybe<&2, U32>, +I: IM.Ix, +F: List<&2, U32>) -> Bool:
  match m:
    case Some{+y}:
      True{}
    case None{}:
      match I:
        case IM.Ept{}:
          True{}
        case IM.Has{+t}:
          match F:
            case Nil{}:
              False{}
            case Con{+b, r}:
              True{}

# the index, the live nodes and the free list's first nodes after
type Cxs is Data:
  Cxs{I: IM.Ix, +L: List<&2, U32>, +F: List<&2, U32>}

def cxs.I(S: Cxs) -> IM.Ix:
  match S:
    case Cxs{I, +L, +F}:
      I

def cxs.L(S: Cxs) -> List<&2, U32>:
  match S:
    case Cxs{I, +L, +F}:
      L

def cxs.F(S: Cxs) -> List<&2, U32>:
  match S:
    case Cxs{I, +L, +F}:
      F

def cxs(cs: List<&2, R.FzC>, +vm: List<&2, U32>, +dm: Nat, +I: IM.Ix, +L: List<&2, U32>, +F: List<&2, U32>) -> Cxs:
  match cs:
    case Nil{}:
      Cxs{I, L, F}
    case Con{c, r}:
      match c:
        case R.FzC{+at, +src, neg, +far}:
          cxs(r, vm, dm, cx.I(IM.ix.look(I, far), I, pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), src, cx.hd(F), far),
            cx.L(IM.ix.look(I, far), pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), L),
            cx.F1(IM.ix.look(I, far), I, pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), far, cx.tl(IM.ix.look(I, far), I, F)))

# each crossing's premises in turn: its position absent where it makes a
# cursor, room for the branch it takes
def cxs.ok(cs: List<&2, R.FzC>, +vm: List<&2, U32>, +dm: Nat, +I: IM.Ix, +F: List<&2, U32>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, r}:
      match c:
        case R.FzC{+at, +src, neg, +far}:
          (cx.ab(IM.ix.look(I, far), I, src) && cx.room(IM.ix.look(I, far), I, F)) &&
            cxs.ok(r, vm, dm, cx.I(IM.ix.look(I, far), I, pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), src, cx.hd(F), far),
              cx.F1(IM.ix.look(I, far), I, pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), far, cx.tl(IM.ix.look(I, far), I, F)))
