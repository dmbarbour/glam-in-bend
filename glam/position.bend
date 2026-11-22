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
#   or, at the interface, an eraser node's principal faces it, the same
#   value;
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

def pd.v.e(+era: Bool, h: P.H, +q: U32, +acc: U32) -> PdS:
  match era:
    case True{}:
      PdEnd{PdStatic{h, acc}}
    case False{}:
      PdEnd{PdValue{h, q, acc}}

def pd.v.k(+cur: Bool, +era: Bool, h: P.H, +q: U32, +acc: U32) -> PdS:
  match cur:
    case True{}:
      PdEnd{PdCur{h, P.base(q), acc}}
    case False{}:
      pd.v.e(era, h, q, acc)

# principal port q facing the position: a cursor; an eraser node, at any
# position, served as the static eraser is, the value the same
# (representations-interchangeable, static-links-count-as-nodes), so that
# no eraser is copied as a tree of its own: at the interface its one port
# the root, which the splice's statics pass would read before the root is
# linked (docs/reviews/Splice_2026-11-19.md, S1); elsewhere a placeholder
# made, joined and freed for nothing, its template outside the serve's
# laws (docs/reviews/Erasers_2026-11-21.md, E2); else a value
def pd.v(r: P.H & U32, +q: U32, +acc: U32) -> PdS:
  (h, +hd) = r
  pd.v.k(U32.is_eq(P.rk(hd), 18), U32.is_eq((P.rk(hd) .|. 1 : U32), 7), h, q, acc)

# A walk's climb known in advance (cells-freeze.sharing.cursors.growth):
# a walk climbs from its start by principal-on-auxiliary links, no pair
# among them, until something can reduce or it reaches what a copy holds.
# A control a copy has taken is marked (kprim.bend's mark,
# `copied-nodes-untouched`) and finished; a climb that meets one ends at
# the frontier, state 7, with no interaction, every time over the ladder
# and the cursor workloads (826 walks measured, none otherwise). A folded
# list in a source climbs so at every element, a chain of copies of the
# fold function a cell deep, each walk to its top; the climb looked at
# here is at most pd.climb_most() nodes, marked controls joining it
# within five, and else the walk runs.
def pd.climb_most() -> Nat:
  8n

type Cl is Type:
  Cl{h: P.H, +x: U32, +hit: Bool, +go: Bool}

# node x reached: is it a marked control?
def cl.hd(r: P.H & U32, +x: U32) -> Cl:
  (h, +hd) = r
  Cl{h, x, (U32.is_eq(P.rk(hd), 10) || U32.is_eq(P.rk(hd), 11)) && P.marked(hd), True{}}

def cl.peer.k(+aux: Bool, h: P.H, +q: U32) -> Cl:
  match aux:
    case True{}:
      cl.hd(P.rd(h, P.base(q)), P.base(q))
    case False{}:
      Cl{h, 0, False{}, False{}}

# the peer q of the node's principal port: on to its node if q is an
# auxiliary port, else the climb stops, a pair or a static
def cl.peer(r: P.H & U32) -> Cl:
  (h, +q) = r
  cl.peer.k(Bool.not(P.is_static(q)) && U32.is_ne((q .&. 3 : U32), 0), h, q)

def cl.step.k(+stop: Bool, h: P.H, +x: U32, +hit: Bool) -> Cl:
  match stop:
    case True{}:
      Cl{h, x, hit, False{}}
    case False{}:
      cl.peer(P.rd(h, (x + 1 : U32)))

def cl.step(c: Cl) -> Cl:
  match c:
    case Cl{h, +x, +hit, +go}:
      cl.step.k(hit || Bool.not(go), h, x, hit)

def cl.run(k: Nat, c: Cl) -> Cl:
  match k:
    case 0n:
      c
    case 1n+g:
      cl.run(g, cl.step(c))

# the climb met a marked control: the frontier, as the walk would end, no
# walk made; else the walk from b
def pd.climbed(c: Cl, +b: U32, +pos: U32, +f: Nat, +acc: U32) -> PdS:
  match c:
    case Cl{h, +x, +hit, +go}:
      match hit:
        case True{}:
          PdEnd{pd.peer.r(pd.peer(h, pos), acc)}
        case False{}:
          pd.ended(pd.walk(h, b, f), pos, acc)

def pd.q.k(+st: Bool, +pr: Bool, h: P.H, +q: U32, +pos: U32, +f: Nat, +acc: U32) -> PdS:
  match st:
    case True{}:
      PdEnd{PdStatic{h, acc}}
    case False{}:
      match pr:
        case True{}:
          pd.v(P.rd(h, P.base(q)), q, acc)
        case False{}:
          pd.climbed(cl.run(pd.climb_most(), Cl{h, P.base(q), False{}, True{}}), P.base(q), pos, f, acc)

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
