import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD
import ./ring.bend as R
import ../spike/kmodel.bend as KMd
import ./index_model.bend as IM

# Rings, modelled for glam's laws (glam/LAWS.bend; the Cells plan's
# cells-freeze.nested.host.ring): no code of the materializer calls these.
# A ring is stated on the heap's words read as a list (lawful-arrays'
# view, AD.view), data that copies freely, by its members' node bases xs,
# the situating node and the cursors alike, each one's word 3 the next.

# whether x is among xs
def has(xs: List<&2, U32>, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+h, t}:
      U32.is_eq(h, x) || has(t, x)

def link.in.m(m: Maybe<&2, U32>, +xs: List<&2, U32>) -> Bool:
  match m:
    case Some{+l}:
      has(xs, l)
    case None{}:
      False{}

# member m's word 3, among words v (the view of a perfect tree of depth
# d), holds a member of xs
def link.in(+v: List<&2, U32>, +d: Nat, +xs: List<&2, U32>, +m: U32) -> Bool:
  link.in.m(List.get(&2, U32, v, AD.slot((m + 3 : U32), d)), xs)

def closed.go(+v: List<&2, U32>, +d: Nat, +xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, t}:
      link.in(v, d, xs, y) && closed.go(v, d, xs, t)

# the ring xs closed on words v: every member's word 3 holds a member, so
# that a walk round it from a member meets members alone
def closed(+v: List<&2, U32>, +d: Nat, +xs: List<&2, U32>) -> Bool:
  closed.go(v, d, xs, xs)

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
# ring xs, as a cursor new to it is
def apart(ys: List<&2, U32>, +d: Nat, +x: U32) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, t}:
      Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot((y + 3 : U32), d))) && apart(t, d, x)


# word j's slot none of node m's four words' slots
def off.node(+d: Nat, +m: U32, +j: U32) -> Bool:
  Bool.not(Nat.is_eq(AD.slot(m, d), AD.slot(j, d))) && (Bool.not(Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot(j, d))) && (Bool.not(Nat.is_eq(AD.slot((m + 2 : U32), d), AD.slot(j, d))) && Bool.not(Nat.is_eq(AD.slot((m + 3 : U32), d), AD.slot(j, d)))))

# word i's slot no member's word 3: a write there leaves the ring's
# links, and a word so placed is none a join writes in the ring
def off.links(ys: List<&2, U32>, +d: Nat, +i: U32) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, t}:
      Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((y + 3 : U32), d))) && off.links(t, d, i)

# The ring exact (cells-freeze.nested.host.ring.exact): its members
# listed in walk order, so that a cycle holds by computation and a
# member taken out leaves the list

# member m's word 3, among words v, holds n
def link.is.m(m: Maybe<&2, U32>, +n: U32) -> Bool:
  match m:
    case Some{+l}:
      U32.is_eq(l, n)
    case None{}:
      False{}

def link.is(+v: List<&2, U32>, +d: Nat, +m: U32, +n: U32) -> Bool:
  link.is.m(List.get(&2, U32, v, AD.slot((m + 3 : U32), d)), n)

# through ys in order from a to b: a's word 3 the first of ys (or b),
# each one's the next, the last's b
def chain(+v: List<&2, U32>, +d: Nat, ys: List<&2, U32>, +a: U32, +b: U32) -> Bool:
  match ys:
    case Nil{}:
      link.is(v, d, a, b)
    case Con{+y, t}:
      link.is(v, d, a, y) && chain(v, d, t, y, b)

# no two members' word 3 in one slot
def apart.all(ys: List<&2, U32>, +d: Nat) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, +t}:
      apart(t, d, y) && apart.all(t, d)

# the ring exact: the situating node s, then its cursors t in walk
# order, the last's word 3 s again; no two word 3 in one slot
def ring(+v: List<&2, U32>, +d: Nat, +s: U32, +t: List<&2, U32>) -> Bool:
  chain(v, d, t, s, s) && apart.all(Con{s, t}, d)

# the last of ys, or a where ys is empty
def last(ys: List<&2, U32>, +a: U32) -> U32:
  match ys:
    case Nil{}:
      a
    case Con{+y, t}:
      last(t, y)

# a list with x taken out, and the member listed before x, for the exact
# ring's laws stated by membership (JoinExact review, F1)
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

def pick(+b: Bool, +a: U32, +r: U32) -> U32:
  match b:
    case True{}:
      a
    case False{}:
      r

# the member listed before x in ys, a first: the last before x
def before(ys: List<&2, U32>, +a: U32, +x: U32) -> U32:
  match ys:
    case Nil{}:
      a
    case Con{+y, t}:
      pick(U32.is_eq(y, x), a, before(t, y, x))

# The ring's nodes laid out (JoinExact review, F3; the second reviewer's
# F2, F4): facts of the members' words, stated on the list alone, so that
# taking members out keeps them by computation

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
# word 3 nor word 2, so that linking it leaves the ring's links and
# positions (ring-ports-faced-off-positions); a member's word 1 may be
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

# the ring exact, its nodes laid out apart, each member a base, each
# facing a port faceable by them, its link word no member's word 2 or 3
def ring.ok(+v: List<&2, U32>, +d: Nat, +s: U32, +t: List<&2, U32>) -> Bool:
  ring(v, d, s, t) && (layout(Con{s, t}, d) && (bases(Con{s, t}) && faces(Con{s, t}, v, d, Con{s, t})))

# a node x apart from the ring M, as a placeholder joined to it is: none
# of its words in a slot of a member's, its own base, facing a port
# faceable by the ring's members (the serve's to show, from the
# allocator and the splice)
def node.ok(+v: List<&2, U32>, +d: Nat, +M: List<&2, U32>, +x: U32) -> Bool:
  cross(M, d, x) && (U32.is_eq(P.base(x), x) && faces.m(List.get(&2, U32, v, AD.slot((x + 1 : U32), d)), d, M))

# a node x ready to enter the ring Con{s, t} after s, as a cursor new to
# it is: what node.ok asks and more, x becoming a member: its own words
# in four slots, none the head's, none a member's, its own base, facing
# a port faceable by the members and x, and no member facing a port whose
# link word is x's word 2 or 3 (the serve's to show: the allocator gives x's
# words and that nothing faces into x, the splice x's port)
def enter.ok(+v: List<&2, U32>, +d: Nat, +s: U32, +t: List<&2, U32>, +x: U32) -> Bool:
  apartw(nw(x), d) && (off(nw(x), d, P.at_fh()) && (cross(Con{s, t}, d, x) && (U32.is_eq(P.base(x), x) && (faces.m(List.get(&2, U32, v, AD.slot((x + 1 : U32), d)), d, Con{s, Con{x, t}}) && faces(Con{s, t}, v, d, Con{x, Nil{}})))))

# The serve's pending placeholders (cells-freeze.nested.host.serve): the
# ring s, t exact; the placeholders ps not yet joined nor made cursors,
# none of the ring's and none listed twice; every node of either in the
# list L, laid out apart, each its own base, each facing a port faceable
# by all of L. L is carried, not computed from the others: a join takes
# its placeholder and its cursor out of it, a cursor made moves a
# placeholder from ps to t and leaves L as it was
def pend.ok(+v: List<&2, U32>, +d: Nat, +s: U32, +t: List<&2, U32>, +ps: List<&2, U32>, +L: List<&2, U32>) -> Bool:
  ring(v, d, s, t) && (sub(Con{s, t}, L) && (sub(ps, L) && (none.in(ps, Con{s, t}) && (distinct(ps) && (layout(L, d) && (bases(L) && faces(L, v, d, L)))))))

# a crossing's ring after it (R.cross): the cursor m found at its far
# position out, the placeholder x joined to it; else x made a cursor
def cross.t(m: Maybe<&2, U32>, +x: U32, +t: List<&2, U32>) -> List<&2, U32>:
  match m:
    case Some{+y}:
      without(t, y)
    case None{}:
      Con{x, t}

# and the nodes' list after it: both out, or as it was
def cross.L(m: Maybe<&2, U32>, +x: U32, +L: List<&2, U32>) -> List<&2, U32>:
  match m:
    case Some{+y}:
      without(without(L, x), y)
    case None{}:
      L

# A copy's crossings, modelled (R.crossings): two words read alike
def meq(m: Maybe<&2, U32>, +n: Maybe<&2, U32>) -> Bool:
  match m:
    case Some{+x}:
      match n:
        case Some{+y}:
          U32.is_eq(x, y)
        case None{}:
          False{}
    case None{}:
      match n:
        case Some{+y}:
          False{}
        case None{}:
          True{}

# every member of ys holding at its word 2, its position, the same in v1
# as in v2: the heap and a view of the positions agreeing
def agree(ys: List<&2, U32>, +v1: List<&2, U32>, +v2: List<&2, U32>, +d: Nat) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+m, r}:
      meq(List.get(&2, U32, v1, AD.slot((m + 2 : U32), d)), List.get(&2, U32, v2, AD.slot((m + 2 : U32), d))) && agree(r, v1, v2, d)

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

# the view of the positions after a crossing: a cursor made, its word 2
# its position src
def cr.pv(m: Maybe<&2, U32>, +x: U32, +src: U32, +pv: List<&2, U32>, +d: Nat) -> List<&2, U32>:
  match m:
    case Some{+y}:
      pv
    case None{}:
      List.set(&2, U32, pv, AD.slot((x + 2 : U32), d), src)

# the ring and the nodes' list after a copy's crossings: each crossing's
# find modelled over the view of the positions pv (RG.first), the ring
# and list stepped by cross.t and cross.L, so that the model shares none
# of the code's finds
def cr(cs: List<&2, R.FzC>, +vm: List<&2, U32>, +dm: Nat, +pv: List<&2, U32>, +d: Nat, +t: List<&2, U32>, +L: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match cs:
    case Nil{}:
      (t, L)
    case Con{c, r}:
      match c:
        case R.FzC{+at, +src, neg, +far}:
          cr(r, vm, dm, cr.pv(first(t, pv, d, far), pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), src, pv, d), d,
            cross.t(first(t, pv, d, far), pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), t),
            cross.L(first(t, pv, d, far), pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), L))

# The crossings' writes by region (crossings_keeps): the ports the nodes
# of ys face, by their words 1 among v
def faced(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat) -> List<&2, U32>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{+m, r}:
      Con{pl.of(List.get(&2, U32, v, AD.slot((m + 1 : U32), d))), faced(r, v, d)}

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

# no crossing of cs looks for c's position in v, as the find reads it
# (pos.is): the served cursor, which no crossing then joins (serve_exact)
def unfound(cs: List<&2, R.FzC>, +v: List<&2, U32>, +d: Nat, +c: U32) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{f, r}:
      match f:
        case R.FzC{+at, +src, neg, +far}:
          Bool.not(pos.is(v, d, c, far)) && unfound(r, v, d, c)

# The pending placeholders over the index
# =======================================
#
# cells-freeze.sharing.cursors.index.ring.inv: the serve's invariant with a
# copy's cursors in a tree of the net's nodes (cursors-indexed). N lists
# every node a serve touches, laid out apart once (layout, bases); each
# holds one role in it: the situating node s; the index I's leaves, the
# cursors, and its branches; the pending placeholders ps; the free list's
# first nodes F, which an insert takes its branch from and a join gives
# its nodes to. L, carried as before, lists the live ones: s, the cursors
# and the pending, no branch nor free node among them. A live node faces a
# port faceable by L (faces); that port's link word, which a join writes,
# is off every word of a tracked node that is not live and off the word 0
# of one that is, and off the free list's head (po.all, KMd.off.port: a
# static has none); and live nodes
# facing one another face one another both ways, none itself
# (copy-links-two-way), so that a join leaves no live node facing the
# nodes it frees.

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

# z, facing port r, faced back by each node of Q that r names
def tw.q(Q: List<&2, U32>, +r: U32, +z: U32, +v: List<&2, U32>, +d: Nat) -> Bool:
  match Q:
    case Nil{}:
      True{}
    case Con{+q, t}:
      Bool.or(Bool.not(U32.is_eq(r, q)), U32.is_eq(KMd.word(v, d, (q + 1 : U32)), z)) && tw.q(t, r, z, v, d)

# each of ys facing not itself, and faced back by the live node it faces
def px.tw(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +L: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+z, t}:
      Bool.not(U32.is_eq(KMd.word(v, d, (z + 1 : U32)), z)) && (tw.q(L, KMd.word(v, d, (z + 1 : U32)), z, v, d) && px.tw(t, v, d, L))

# the invariant: the index realized, on its invariant, laid out; s and the
# cursors live, the pending live and of no role else, listed once; no
# branch live; the free list's first nodes F listed once, of no role
# else; the live, the free and the index's nodes all tracked; the live
# facing as above
def px.ok(+v: List<&2, U32>, +d: Nat, +s: U32, +I: IM.Ix, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>) -> Bool:
  IM.ix.real(v, d, s, I) && (IM.ix.inv(I) && (IM.ix.lay(I, s, d) && (sub(Con{s, IM.ix.leaves(I)}, L) && (sub(ps, L) && (none.in(ps, Con{s, IM.ix.nodes(I)}) && (distinct(ps) && (none.in(L, IM.ix.branches(I)) && (KMd.chain(F, v, d, KMd.word(v, d, P.at_fh())) && (distinct(F) && (none.in(F, Con{s, IM.ix.nodes(I)}) && (none.in(F, L) && (sub(L, N) && (sub(F, N) && (sub(IM.ix.nodes(I), N) && (faces(L, v, d, L) && (px.off(L, v, d, L, N) && px.tw(L, v, d, L)))))))))))))))))
