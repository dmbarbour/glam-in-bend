import Base
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
