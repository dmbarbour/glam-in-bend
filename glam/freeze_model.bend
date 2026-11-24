import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ./ring.bend as RN
import ./freeze.bend as F

# What glam/FREEZE_LAWS.bend states of freeze's write phase (the
# CursorLaws plan's cursor-laws.materializer.template.emit): no code of
# freeze calls these. The template's nodes standing for statics and
# cursors are kept the last first (FzE's eras), the first of them at
# index n0, after the n0 nodes read back; each crossing's placeholder is
# one of them. The write phase's own model, over its six data fields,
# which the proofs rewrite the code into, is glam/FREEZE_PROOF.bend's.

# the index after eras' last: n0, then one more for each, counted on words
def er.top(eras: List<&2, T.TNode>, +n0: U32) -> U32:
  match eras:
    case Nil{}:
      n0
    case Con{t, r}:
      (er.top(r, n0) + 1 : U32)

# a cursor's placeholder (F.fz.hole), not a static's eraser (F.fz.era)
def is_hole(t: T.TNode) -> Bool:
  match t:
    case T.TN{k, p}:
      match k:
        case R.KCur{}:
          True{}
        case _:
          False{}
    case T.TF{k, +site, +lvl}:
      False{}

def er.holes.k(+h: Bool, +top: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match h:
    case True{}:
      Con{top, rest}
    case False{}:
      rest

# the placeholders' indices among eras, the last first
def er.holes(eras: List<&2, T.TNode>, +n0: U32) -> List<&2, U32>:
  match eras:
    case Nil{}:
      Nil{}
    case Con{t, +r}:
      er.holes.k(is_hole(t), er.top(r, n0), er.holes(r, n0))

# the crossings' placeholders, the last first
def ats(cs: List<&2, RN.FzC>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, r}:
      match c:
        case RN.FzC{+at, +src, neg, +far}:
          Con{at, ats(r)}

def lsteq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          True{}
        case Con{y, s}:
          False{}
    case Con{+x, r}:
      match ys:
        case Nil{}:
          False{}
        case Con{+y, s}:
          U32.is_eq(x, y) && lsteq(r, s)

# the write phase's count: the next index after eras, and each crossing's
# placeholder one of eras' placeholders, in their order
def inv.f(+eras: List<&2, T.TNode>, +ne: U32, curs: List<&2, RN.FzC>, +n0: U32) -> Bool:
  U32.is_eq(ne, er.top(eras, n0)) && lsteq(ats(curs), er.holes(eras, n0))

def inv(z: F.FzE, +n0: U32) -> Bool:
  match z:
    case F.FzE{h, map, nodes, +eras, +ne, ls, root, curs}:
      inv.f(eras, ne, curs, n0)
