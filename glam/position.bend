import Base
import ../spike/kprim.bend as P
import ../spike/kernel.bend as K
import ../spike/kstrat.bend as KS
import ../spike/kmem_grow.bend as KM
import ../spike/kdemand.bend as KD

# Positioned demand (the Cells plan's cells-freeze.demand): a live
# source demanded at a position, a finished node's port, rather than at
# its interface, as a copy's cursor asks. It is a loop of the kernel's
# ordinary walks, no change to them. Each walk starts at the node whose
# output the position faces and runs until that node is rewritten, when
# the walk, at depth 0, goes back to the interface and ends done; the
# position is then read again (`Positions_2026-11-11.md`: a walk keeps
# no path across a stop and walks again from its position).
#
# It ends at one of:
# - a value: a principal port faces the position, the newly finished
#   tree hanging there;
# - the frontier: the position faces an auxiliary port of a finished
#   node, met when a walk steps forward into finished nodes (the walk's
#   state 7, "a variable demanded outside its function's body", read
#   here as reaching what a copy may already hold);
# - a static: the position's port holds one, its value erased or void;
# - a stop the core must handle: a need, stuck, a cycle, out of fuel or
#   memory, the walk's own state.

type Pd is Type:
  # a principal port q faces the position
  PdValue{h: P.H, +q: U32}
  # the auxiliary port q of a finished node faces it
  PdFront{h: P.H, +q: U32}
  # its port holds a static
  PdStatic{h: P.H}
  # a walk stopped otherwise, as it stood
  PdStop{d: KD.D}

# a step of the loop: an end, or the net to read the position again in
type PdS is Type:
  PdEnd{pd: Pd}
  PdMore{h: P.H}

def pd.h(d: KD.D) -> P.H:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      h

def pd.peer.r(r: P.H & U32) -> Pd:
  (h, +q) = r
  PdFront{h, q}

# what the position's port faces
def pd.peer(h: P.H, +pos: U32) -> P.H & U32:
  P.rd(h, (pos + 1 : U32))

# a walk ended in state st: done, the position read again; 7, the
# frontier; anything else, a stop
def pd.ended.k(+st: U32, d: KD.D, +pos: U32) -> PdS:
  match st:
    case 1:
      PdMore{pd.h(d)}
    case 7:
      PdEnd{pd.peer.r(pd.peer(pd.h(d), pos))}
    case _:
      PdEnd{PdStop{d}}

def pd.ended(d: KD.D, +pos: U32) -> PdS:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      pd.ended.k(st, KD.D{h, path, top, depth, n, st}, pos)

# one walk from node base b, f the fuel for it
def pd.walk(h: P.H, +b: U32, +f: Nat) -> KD.D:
  K.demand_ev(0, f, KD.d.go(h, KS.d.path(KM.m_new(6n, P.w_maxd())), b, 0, 0))

def pd.q.k(+st: Bool, +pr: Bool, h: P.H, +q: U32, +pos: U32, +f: Nat) -> PdS:
  match st:
    case True{}:
      PdEnd{PdStatic{h}}
    case False{}:
      match pr:
        case True{}:
          PdEnd{PdValue{h, q}}
        case False{}:
          pd.ended(pd.walk(h, P.base(q), f), pos)

def pd.q(r: P.H & U32, +pos: U32, +f: Nat) -> PdS:
  (h, +q) = r
  pd.q.k(P.is_static(q), U32.is_eq((q .&. 3 : U32), 0), h, q, pos, f)

def pd.loop.r(s: PdS, more: P.H -> Pd) -> Pd:
  match s:
    case PdEnd{pd}:
      pd
    case PdMore{h}:
      more(h)

# out of walks: the last walk's net, stopped as out of fuel
def pd.out(h: P.H, +pos: U32) -> Pd:
  PdStop{KD.D{h, KS.d.path(KM.m_new(6n, P.w_maxd())), pos, 0, 0, 4}}

# at most g walks of f steps each
def pd.loop(g: Nat, +f: Nat, h: P.H, +pos: U32) -> Pd:
  match g:
    case 0n:
      pd.out(h, pos)
    case 1n+k:
      pd.loop.r(pd.q(pd.peer(h, pos), pos, f), h2 => pd.loop(k, f, h2, pos))

# source h demanded at position pos, a finished node's port (its
# reference, node and port), at most g walks of f steps each
def positioned(h: P.H, +pos: U32, +g: Nat, +f: Nat) -> Pd:
  pd.loop(g, f, h, pos)
