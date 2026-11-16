import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

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

# what a member faces, by its word 1: a port whose link word is no word
# 3 of M's, so that linking it leaves the ring's links alone; a static
# eraser (all ones) has its link word on the head's word, off them too
def faces.m(m: Maybe<&2, U32>, +d: Nat, +M: List<&2, U32>) -> Bool:
  match m:
    case Some{+r}:
      off.links(M, d, (r + 1 : U32))
    case None{}:
      False{}

def faces(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +M: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+m, t}:
      faces.m(List.get(&2, U32, v, AD.slot((m + 1 : U32), d)), d, M) && faces(t, v, d, M)

# the ring exact, its nodes laid out apart, each member a base, each
# facing a port off its links
def ring.ok(+v: List<&2, U32>, +d: Nat, +s: U32, +t: List<&2, U32>) -> Bool:
  ring(v, d, s, t) && (layout(Con{s, t}, d) && (bases(Con{s, t}) && faces(Con{s, t}, v, d, Con{s, t})))

# a node x apart from the ring M, as a placeholder joined to it is: none
# of its words in a slot of a member's, its own base, facing a port off
# the ring's links (the serve's to show, from the allocator and the
# splice)
def node.ok(+v: List<&2, U32>, +d: Nat, +M: List<&2, U32>, +x: U32) -> Bool:
  cross(M, d, x) && (U32.is_eq(P.base(x), x) && faces.m(List.get(&2, U32, v, AD.slot((x + 1 : U32), d)), d, M))
