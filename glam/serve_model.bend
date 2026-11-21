import Base
import ../spike/kprim.bend as P
import ../spike/tpl.bend as T
import ./ring.bend as R
import ./splice_model.bend as SM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# What the serve's laws (glam/SERVE_LAWS.bend) ask of a copy's template
# and its crossings, which freeze builds (cells-freeze.nested.host.serve):
# premises stated as model predicates, so that freeze's redesign
# (cells-freeze.nested.host.templates) changes them, not the proofs. No
# code calls these.

# indices i and j share a slot of the map, depth dm
def sl.eq(+i: U32, +j: U32, +dm: Nat) -> Bool:
  Nat.is_eq(AD.slot(i, dm), AD.slot(j, dm))

# the crossings' holes, as template indices
def ats(cs: List<&2, R.FzC>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, r}:
      match c:
        case R.FzC{+at, +src, neg, +far}:
          Con{at, ats(r)}

# index n's slot one of xs's
def sl.in(xs: List<&2, U32>, +dm: Nat, +n: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, r}:
      sl.eq(x, n, dm) || sl.in(r, dm, n)

# no two of xs in one slot
def sl.apart(xs: List<&2, U32>, +dm: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +r}:
      Bool.not(sl.in(r, dm, x)) && sl.apart(r, dm)

# a template index the node pass makes a node at (SM.kind_at: 1)
def node.at(+ts: List<&2, T.TNode>, +dm: Nat, +n: U32) -> Bool:
  U32.is_eq(SM.kind_at(ts, 0, dm, n, 0), 1)

# some end of ls names the hole at's slot
def names(ls: List<&2, T.TLink>, +dm: Nat, +at: U32) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{l, r}:
      match l:
        case T.TL{a, b}:
          match a:
            case T.TE{+n1, +p1}:
              match b:
                case T.TE{+n2, +p2}:
                  sl.eq(n1, at, dm) || (sl.eq(n2, at, dm) || names(r, dm, at))

# an end naming the hole at's slot is its port 0, its partner a node no
# hole shares a slot with
def hole.end(+n: U32, +p: U32, +m: U32, +ts: List<&2, T.TNode>, +dm: Nat, +at: U32, +hs: List<&2, U32>) -> Bool:
  Bool.not(sl.eq(n, at, dm)) || (U32.is_eq(p, 0) && (node.at(ts, dm, m) && Bool.not(sl.in(hs, dm, m))))

def hole.links(ls: List<&2, T.TLink>, +ts: List<&2, T.TNode>, +dm: Nat, +at: U32, +hs: List<&2, U32>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, r}:
      match l:
        case T.TL{a, b}:
          match a:
            case T.TE{+n1, +p1}:
              match b:
                case T.TE{+n2, +p2}:
                  hole.end(n1, p1, n2, ts, dm, at, hs) && (hole.end(n2, p2, n1, ts, dm, at, hs) && hole.links(r, ts, dm, at, hs))

# each hole: a node's index, named by some link, every end naming it the
# hole's port 0 with a node not a hole for partner
def holes.ok(xs: List<&2, U32>, +ls: List<&2, T.TLink>, +ts: List<&2, T.TNode>, +dm: Nat, +hs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+at, r}:
      node.at(ts, dm, at) && (names(ls, dm, at) && (hole.links(ls, ts, dm, at, hs) && holes.ok(r, ls, ts, dm, hs)))

# a copy's crossings fit its template: their holes in slots apart, each
# hole as above
def copy.ok(+cs: List<&2, R.FzC>, +ls: List<&2, T.TLink>, +ts: List<&2, T.TNode>, +dm: Nat) -> Bool:
  sl.apart(ats(cs), dm) && holes.ok(ats(cs), ls, ts, dm, ats(cs))

# no fresh node a static reference, as the allocator's nodes are not
# (theirs is a base, a multiple of four, a static's low two bits ones):
# the allocator's to show
def dyn(ns: List<&2, U32>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+n, r}:
      Bool.not(P.is_static(n)) && dyn(r)

# the copy's root, at the source's root (the materializer's mz.root): a
# node's index no hole shares a slot with, at a port below 3. So freeze
# builds it there, read 2026-11-20: the materializer is at the root only
# for a value at the interface (sv.pd's PdValue), its node neither a
# cursor nor an eraser (glam/position.bend's pd.v serves those as a
# cursor and as the static); freeze_tree reaches the interface through
# that node's port, its index a node's, the holes' after the nodes'. The
# one template with a hole for root, nothing finished (fz.written.k),
# is never a value's. The slots apart: the nodes no more than the map's
# slots, an obligation of freeze's already
def root.ok(+rn: U32, +rp: U32, +ts: List<&2, T.TNode>, +dm: Nat, +cs: List<&2, R.FzC>) -> Bool:
  node.at(ts, dm, rn) && (Bool.not(sl.in(ats(cs), dm, rn)) && SM.port3(rp))
