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
# - a cursor: the principal port facing the position is a cursor's, a
#   copy this source holds of another live source, to be served into
#   this one before anything is copied from here (cells-freeze.nested);
# - a static: the position's port holds one, its value erased or void;
# - a stop the core must handle: a need, stuck, a cycle, out of fuel or
#   memory, the walk's own state.
# Each end carries n, the interactions of the walks done before it; a
# stop's own walk keeps its count in its state.

type Pd is Type:
  # a principal port q faces the position
  PdValue{h: P.H, +q: U32, +n: U32}
  # the auxiliary port q of a finished node faces it
  PdFront{h: P.H, +q: U32, +n: U32}
  # the principal port of cursor x faces it
  PdCur{h: P.H, +x: U32, +n: U32}
  # its port holds a static
  PdStatic{h: P.H, +n: U32}
  # a walk stopped otherwise, as it stood
  PdStop{d: KD.D, +n: U32}

# a step of the loop: an end, or the net to read the position again in,
# with the interactions of the walk that ended
type PdS is Type:
  PdEnd{pd: Pd}
  PdMore{h: P.H, +n: U32}

def pd.h(d: KD.D) -> P.H:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      h

def pd.f.k(+cur: Bool, h: P.H, +q: U32, +n: U32) -> Pd:
  match cur:
    case True{}:
      PdCur{h, P.base(q), n}
    case False{}:
      PdFront{h, q, n}

def pd.f.c(r: P.H & U32, +q: U32, +n: U32) -> Pd:
  (h, +hd) = r
  pd.f.k(U32.is_eq(P.rk(hd), 18), h, q, n)

def pd.f.p(+pr: Bool, h: P.H, +q: U32, +n: U32) -> Pd:
  match pr:
    case True{}:
      pd.f.c(P.rd(h, P.base(q)), q, n)
    case False{}:
      PdFront{h, q, n}

# the frontier's end, port q facing the position: a cursor if q is one's
# principal, as the first read of the position has it (pd.v); a guard,
# the walk reaching the frontier only while the node it started at still
# faces the position (cells-freeze.nested)
def pd.peer.r(r: P.H & U32, +n: U32) -> Pd:
  (h, +q) = r
  pd.f.p(Bool.not(P.is_static(q)) && U32.is_eq((q .&. 3 : U32), 0), h, q, n)

# what the position's port faces
def pd.peer(h: P.H, +pos: U32) -> P.H & U32:
  P.rd(h, (pos + 1 : U32))

# a walk ended in state st: done, the position read again; 7, the
# frontier; anything else, a stop
def pd.ended.k(+st: U32, d: KD.D, +pos: U32, +n: U32, +acc: U32) -> PdS:
  match st:
    case 1:
      PdMore{pd.h(d), n}
    case 7:
      PdEnd{pd.peer.r(pd.peer(pd.h(d), pos), (acc + n : U32))}
    case _:
      PdEnd{PdStop{d, acc}}

def pd.ended(d: KD.D, +pos: U32, +acc: U32) -> PdS:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      pd.ended.k(st, KD.D{h, path, top, depth, n, st}, pos, n, acc)

# one walk from node base b, f the fuel for it
def pd.walk(h: P.H, +b: U32, +f: Nat) -> KD.D:
  K.demand_ev(0, f, KD.d.go(h, KS.d.path(KM.m_new(6n, P.w_maxd())), b, 0, 0))

def pd.v.k(+cur: Bool, h: P.H, +q: U32, +acc: U32) -> PdS:
  match cur:
    case True{}:
      PdEnd{PdCur{h, P.base(q), acc}}
    case False{}:
      PdEnd{PdValue{h, q, acc}}

# principal port q facing the position: a value, or a cursor
def pd.v(r: P.H & U32, +q: U32, +acc: U32) -> PdS:
  (h, +hd) = r
  pd.v.k(U32.is_eq(P.rk(hd), 18), h, q, acc)

def pd.q.k(+st: Bool, +pr: Bool, h: P.H, +q: U32, +pos: U32, +f: Nat, +acc: U32) -> PdS:
  match st:
    case True{}:
      PdEnd{PdStatic{h, acc}}
    case False{}:
      match pr:
        case True{}:
          pd.v(P.rd(h, P.base(q)), q, acc)
        case False{}:
          pd.ended(pd.walk(h, P.base(q), f), pos, acc)

def pd.q(r: P.H & U32, +pos: U32, +f: Nat, +acc: U32) -> PdS:
  (h, +q) = r
  pd.q.k(P.is_static(q), U32.is_eq((q .&. 3 : U32), 0), h, q, pos, f, acc)

def pd.loop.r(s: PdS, +acc: U32, more: P.H -> U32 -> Pd) -> Pd:
  match s:
    case PdEnd{pd}:
      pd
    case PdMore{h, +n}:
      more(h, (acc + n : U32))

# out of walks: the last walk's net, stopped as out of fuel
def pd.out(h: P.H, +pos: U32, +acc: U32) -> Pd:
  PdStop{KD.D{h, KS.d.path(KM.m_new(6n, P.w_maxd())), pos, 0, 0, 4}, acc}

# at most g walks of f steps each, acc the interactions so far
def pd.loop(g: Nat, +f: Nat, h: P.H, +pos: U32, +acc: U32) -> Pd:
  match g:
    case 0n:
      pd.out(h, pos, acc)
    case 1n+k:
      pd.loop.r(pd.q(pd.peer(h, pos), pos, f, acc), acc, h2 => a2 => pd.loop(k, f, h2, pos, a2))

# source h demanded at position pos, a finished node's port (its
# reference, node and port), at most g walks of f steps each
def positioned(h: P.H, +pos: U32, +g: Nat, +f: Nat) -> Pd:
  pd.loop(g, f, h, pos, 0)

# and from a walk d at position pos set going again where it stopped,
# its path kept: a template spliced or a value resumed at the need it
# stopped at, or its fuel run out (cells-freeze.rewalk)
def positioned.from(d: KD.D, +pos: U32, +g: Nat, +f: Nat) -> Pd:
  pd.loop.r(pd.ended(K.demand_ev(0, f, d), pos, 0), 0, h2 => a2 => pd.loop(g, f, h2, pos, a2))
