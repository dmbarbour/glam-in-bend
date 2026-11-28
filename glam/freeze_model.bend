import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ./ring.bend as RN
import ./freeze.bend as F
import ./splice_model.bend as SM
import ./splice_copy.bend as S
import ../spike/kprim.bend as P
import ../spike/net.bend as N
import ../spike/kmodel.bend as KMd
import ./ring_model.bend as RG

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

# The links (cursor-laws.materializer.template.emit.links.ends)

# eras' indices, the last first: n0 for the first
def er.idx(eras: List<&2, T.TNode>, +n0: U32) -> List<&2, U32>:
  match eras:
    case Nil{}:
      Nil{}
    case Con{t, +r}:
      Con{er.top(r, n0), er.idx(r, n0)}

# a link's near end a node read back, below n0, its ports below 3
def lk.ok(l: T.TLink, +n0: U32) -> Bool:
  match l:
    case T.TL{a, b}:
      match a:
        case T.TE{+i, +p}:
          match b:
            case T.TE{+j, +r}:
              U32.is_lt(i, n0) && (SM.port3(p) && SM.port3(r))

def lks.ok(ls: List<&2, T.TLink>, +n0: U32) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, r}:
      lk.ok(l, n0) && lks.ok(r, n0)

# a link from a node read back to port 0 of index e
def lk.to(l: T.TLink, +n0: U32, +e: U32) -> Bool:
  match l:
    case T.TL{a, b}:
      match a:
        case T.TE{+i, +p}:
          match b:
            case T.TE{+j, +r}:
              U32.is_lt(i, n0) && (U32.is_eq(j, e) && U32.is_eq(r, 0))

def lks.to(ls: List<&2, T.TLink>, +n0: U32, +e: U32) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{l, r}:
      lk.to(l, n0, e) || lks.to(r, n0, e)

def all.to(es: List<&2, U32>, +ls: List<&2, T.TLink>, +n0: U32) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, r}:
      lks.to(ls, n0, e) && all.to(r, ls, n0)

# the write phase's links: each from a node read back, its ports below 3,
# and each index of eras linked at its port 0 from a node read back
def inv.k(+ls: List<&2, T.TLink>, +eras: List<&2, T.TNode>, +n0: U32) -> Bool:
  lks.ok(ls, n0) && all.to(er.idx(eras, n0), ls, n0)

def inv.l(z: F.FzE, +n0: U32) -> Bool:
  match z:
    case F.FzE{h, map, nodes, +eras, +ne, +ls, root, curs}:
      inv.k(ls, eras, n0)

# A link's far end (cursor-laws.materializer.template.emit.links.far)

def lsin(+x: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+y, r}:
      U32.is_eq(x, y) || lsin(x, r)

# the map's values at most n0: its view's odd positions (a base at each
# even one, its index plus one after it)
def vals.le(xs: List<&2, U32>, +n0: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{k, r}:
      match r:
        case Nil{}:
          True{}
        case Con{+v, s}:
          U32.is_le(v, n0) && vals.le(s, n0)

# a link's far end a node read back, or port 0 of an index of eras
def lk.far(l: T.TLink, +eras: List<&2, T.TNode>, +n0: U32) -> Bool:
  match l:
    case T.TL{a, b}:
      match a:
        case T.TE{+i, +p}:
          match b:
            case T.TE{+j, +r}:
              U32.is_lt(j, n0) || (U32.is_eq(r, 0) && lsin(j, er.idx(eras, n0)))

def lks.far(ls: List<&2, T.TLink>, +eras: List<&2, T.TNode>, +n0: U32) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, r}:
      lk.far(l, eras, n0) && lks.far(r, eras, n0)

def inv.j(z: F.FzE, +n0: U32) -> Bool:
  match z:
    case F.FzE{h, map, nodes, +eras, +ne, +ls, root, curs}:
      lks.far(ls, eras, n0)

# The root and the eras' kinds (cursor-laws.materializer.template.emit.kinds.root)

# the root a node read back's port below 3
def rt.ok(+root: T.TEnd, +n0: U32) -> Bool:
  match root:
    case T.TE{+r, +rp}:
      U32.is_lt(r, n0) && SM.port3(rp)

# each of eras an eraser exactly when it is no placeholder
def eras.ok(eras: List<&2, T.TNode>) -> Bool:
  match eras:
    case Nil{}:
      True{}
    case Con{+t, r}:
      Bool.xor(S.sp.is_era(t), is_hole(t)) && eras.ok(r)

def inv.r(z: F.FzE, +n0: U32) -> Bool:
  match z:
    case F.FzE{h, map, nodes, +eras, +ne, +ls, +root, curs}:
      rt.ok(root, n0) && eras.ok(eras)

# The read nodes' kinds (cursor-laws.materializer.template.emit.kinds.nodes)

# a kind no eraser's, by S.sp.is_era itself (eraser has one owner)
def k.ok(+k: R.NodeKind) -> Bool:
  Bool.not(S.sp.is_era(T.TN{k, V.PNone{}}))

# each base aligned (a multiple of 4) and its header's kind no eraser's,
# in the words' view v at depth d
def hdrs.ok(bs: List<&2, U32>, +v: List<&2, U32>, +d: Nat) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{+b, r}:
      Nat.is_eq(Nat.mod(U32.to_nat(b), 4n), 0n) && (k.ok(N.kof(P.rk(KMd.word(v, d, b)))) && hdrs.ok(r, v, d))

def no_era(ns: List<&2, T.TNode>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+t, r}:
      Bool.not(S.sp.is_era(t)) && no_era(r)

def inv.n(z: F.FzE) -> Bool:
  match z:
    case F.FzE{h, map, +nodes, eras, +ne, ls, root, curs}:
      no_era(nodes)

# The nodes read back (cursor-laws.materializer.template.emit.length)
def nodes.of(z: F.FzE) -> List<&2, T.TNode>:
  match z:
    case F.FzE{h, map, nodes, eras, +ne, ls, root, curs}:
      nodes

# The crossings' positions (cursor-laws.materializer.template.emit.positions)

# each base's three port positions, b + p for p below 3, in the list's
# order: a crossing at port p of node b is made at b + p
def ports(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+b, r}:
      Con{(b + 0 : U32), Con{(b + 1 : U32), Con{(b + 2 : U32), ports(r)}}}

# none of xs among ys
def disj(xs: List<&2, U32>, +ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, r}:
      Bool.not(RG.has(ys, x)) && disj(r, ys)

def curs.of(z: F.FzE) -> List<&2, RN.FzC>:
  match z:
    case F.FzE{h, map, nodes, eras, +ne, ls, root, curs}:
      curs

# the template's crossings (tpl_pos)
def fz.curs(f: F.Fz) -> List<&2, RN.FzC>:
  match f:
    case F.Fz{tpl, curs, +n}:
      curs
