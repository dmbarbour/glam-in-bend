import Base
import ../spike/kprim.bend as P
import ../spike/tpl.bend as T
import ../spike/kmodel.bend as KMd
import ./splice.bend as S

# What the splice's laws (glam/SPLICE_LAWS.bend) name of its state and the
# heap: no code calls these (cells-freeze.nested.host.splice).

# the splice's net
def heap(s: S.Sp) -> P.H:
  match s:
    case S.Sp{h, map}:
      h

# A template's links, as the links pass reads them: a node's port, 0, 1
# or 2 (port 3's "link word" would be the next node's header)
def port3(+p: U32) -> Bool:
  U32.is_eq(p, 0) || (U32.is_eq(p, 1) || U32.is_eq(p, 2))

# an end: its node's entry in the map (view vm, depth dm) one of the
# fresh nodes ns, its port a node's
def end.ok(e: T.TEnd, +vm: List<&2, U32>, +dm: Nat, +ns: List<&2, U32>) -> Bool:
  match e:
    case T.TE{+n, +p}:
      KMd.has(ns, KMd.word(vm, dm, n)) && port3(p)

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
