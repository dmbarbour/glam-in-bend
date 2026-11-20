import Base
import ../spike/kprim.bend as P
import ../spike/tpl.bend as T
import ../spike/kmodel.bend as KMd
import ./splice.bend as S
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# What the splice's laws (glam/SPLICE_LAWS.bend) name of its state and the
# heap: no code calls these (cells-freeze.nested.host.splice).

# the splice's net
def heap(s: S.Sp) -> P.H:
  match s:
    case S.Sp{h, map}:
      h

# the nodes the node pass makes of a template's: one for each, an eraser
# none (S.sp.is_era; its index maps to the static)
def made.k(+e: Bool, +n: Nat) -> Nat:
  match e:
    case True{}:
      n
    case False{}:
      1n+n

def made(ts: List<&2, T.TNode>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case Con{t, rest}:
      made.k(S.sp.is_era(t), made(rest))

# The node pass's map (nodes_maps): the splice's map
def map(s: S.Sp) -> Array<U32>:
  match s:
    case S.Sp{h, m}:
      m

def pick(+b: Bool, +x: U32, +y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

# what a step of the pass writes in the map: for an eraser the static,
# else the next fresh node
def ent.w(+e: Bool, +ns: List<&2, U32>) -> U32:
  match e:
    case True{}:
      P.era()
    case False{}:
      match ns:
        case Nil{}:
          0
        case Con{+m, +r}:
          m

# the fresh nodes left after a step
def ent.ns(+e: Bool, +ns: List<&2, U32>) -> List<&2, U32>:
  match e:
    case True{}:
      ns
    case False{}:
      match ns:
        case Nil{}:
          Nil{}
        case Con{+m, +r}:
          r

# the map's word at index ix after the pass over ts from index i, old
# the word before: each step's write folded in the pass's order, at its
# index's slot (the map's array takes an index mod 2^dm), a later write
# over an earlier
def ent(ts: List<&2, T.TNode>, +ns: List<&2, U32>, +i: U32, +dm: Nat, +ix: U32, +old: U32) -> U32:
  match ts:
    case Nil{}:
      old
    case Con{+t, rest}:
      ent(rest, ent.ns(S.sp.is_era(t), ns), (i + 1 : U32), dm, ix, pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), ent.w(S.sp.is_era(t), ns), old))

# A template's links, as the links pass reads them: a node's port, 0, 1
# or 2 (port 3's "link word" would be the next node's header)
def port3(+p: U32) -> Bool:
  U32.is_eq(p, 0) || (U32.is_eq(p, 1) || U32.is_eq(p, 2))

# an end: its node's entry in the map (view vm, depth dm) and its port
# naming a static (an eraser's index, mapped to the eraser), which the
# link writes nothing for, or a port of one of the fresh nodes ns
def end.ok(e: T.TEnd, +vm: List<&2, U32>, +dm: Nat, +ns: List<&2, U32>) -> Bool:
  match e:
    case T.TE{+n, +p}:
      P.is_static((KMd.word(vm, dm, n) + p : U32)) || (KMd.has(ns, KMd.word(vm, dm, n)) && port3(p))

def link.ok(l: T.TLink, +vm: List<&2, U32>, +dm: Nat, +ns: List<&2, U32>) -> Bool:
  match l:
    case T.TL{a, b}:
      end.ok(a, vm, dm, ns) && end.ok(b, vm, dm, ns)

def ends.ok(ls: List<&2, T.TLink>, +vm: List<&2, U32>, +dm: Nat, +ns: List<&2, U32>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, r}:
      link.ok(l, vm, dm, ns) && ends.ok(r, vm, dm, ns)

# The template's premise (cells-freeze.nested.host.splice.tpl), over the
# same fold: the kind the node pass last wrote at index ix's slot, 0 none,
# 1 a node, 2 an eraser
def kc(+e: Bool) -> U32:
  match e:
    case True{}:
      2
    case False{}:
      1

def kind_at(ts: List<&2, T.TNode>, +i: U32, +dm: Nat, +ix: U32, +old: U32) -> U32:
  match ts:
    case Nil{}:
      old
    case Con{+t, rest}:
      kind_at(rest, (i + 1 : U32), dm, ix, pick(Nat.is_eq(AD.slot(i, dm), AD.slot(ix, dm)), kc(S.sp.is_era(t)), old))

# an end's port fits what its index names: an eraser's principal, or a
# node's port below 3
def tm.k(+k: U32, +p: U32) -> Bool:
  (U32.is_eq(k, 2) && U32.is_eq(p, 0)) || (U32.is_eq(k, 1) && port3(p))

def tm.end(e: T.TEnd, +ts: List<&2, T.TNode>, +dm: Nat) -> Bool:
  match e:
    case T.TE{+n, +p}:
      tm.k(kind_at(ts, 0, dm, n, 0), p)

def tm.link(l: T.TLink, +ts: List<&2, T.TNode>, +dm: Nat) -> Bool:
  match l:
    case T.TL{a, b}:
      tm.end(a, ts, dm) && tm.end(b, ts, dm)

# every link's ends name, at the map's depth dm, a slot the node pass
# writes from index 0, at a port its node has
def tpl.ok(ls: List<&2, T.TLink>, +ts: List<&2, T.TNode>, +dm: Nat) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, r}:
      tm.link(l, ts, dm) && tpl.ok(r, ts, dm)
