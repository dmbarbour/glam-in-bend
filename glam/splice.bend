import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/net.bend as N
import ../spike/kprim.bend as P
import ../spike/kstrat.bend as KS
import ../spike/kmem_grow.bend as KM
import ../spike/kdemand.bend as KD
import ./splice_copy.bend as SC

# Splicing (Cells, re-scoped by the bridge: `bridge-recursion`): a
# template, the closed net of a top-level function or of a value whose
# outcome was a function, copied into a running net where demand stopped
# needing it (state 2). Demand stops with its top the application whose
# principal port faces the data node that holds the template's handle
# (kstrat.bend's d.at): that node is freed, its entry dropped, and the
# copy's root linked to the application in its place, so that demand walks
# on from where it stopped. The copy itself, its nodes and links, is
# glam/splice_copy.bend's (an eraser made static as it is linked, as the
# loader's statics, KN.load, without a node made and freed). A template
# is lowered at depth 0, so every level in the copy is raised by the
# application's level, where it is applied (the Cells plan's item 2, an
# experiment); a level past the
# header's field is an error, as at load. A handle met by an operator,
# which carries no level, is spliced unraised: the operator meeting a
# bind stays stuck.

# The splice
# ==========

# the copy's root linked to the application, demand walking on
def sp.walk2(q: Array<U32> & U32, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32) -> KD.D:
  (map, +x) = q
  KD.d.go(P.link_xx(h, top, x), path, top, depth, n)

def sp.walk(s: SC.Sp, root: T.TEnd, path: KM.M, +top: U32, +depth: U32, +n: U32) -> KD.D:
  match s:
    case SC.Sp{h, map}:
      sp.walk2(SC.sp.end(map, root), h, path, top, depth, n)

# the application's level, the amount the copy is raised: none for an
# operator, which has no level
def sp.by.k(+ap: Bool, +hd: U32) -> U32:
  match ap:
    case True{}:
      P.fld(hd)
    case False{}:
      0

def sp.by(+hd: U32) -> U32:
  sp.by.k(U32.is_eq(P.rk(hd), N.kcode(R.KAp{})), hd)

def sp.copy(h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +by: U32, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, root: T.TEnd, +size: U32) -> KD.D:
  sp.walk(SC.sp.links(links, SC.sp.nodes(nodes, 0, SC.Sp{h, [0 : U32^T.depth_for(31n, size, 0n)]}, by)),
    root, path, top, depth, n)

def sp.top(q: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, root: T.TEnd, +size: U32) -> KD.D:
  (h, +hd) = q
  sp.copy(h, path, top, depth, n, sp.by(hd), nodes, links, root, size)

# the leaf's entry dropped, the leaf freed
def sp.word(q: P.H & U32, +hb: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +leaf: U32, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, root: T.TEnd, +size: U32) -> KD.D:
  (h, +w) = q
  sp.top(P.rd(P.free(P.drop(h, P.form(hb), w), leaf), top), path, top, depth, n, nodes, links, root, size)

def sp.hb(q: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +leaf: U32, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, root: T.TEnd, +size: U32) -> KD.D:
  (h, +hb) = q
  sp.word(P.rd(h, (leaf + 2 : U32)), hb, path, top, depth, n, leaf, nodes, links, root, size)

def sp.leaf(q: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, root: T.TEnd, +size: U32) -> KD.D:
  (h, +leaf) = q
  sp.hb(P.rd(h, leaf), path, top, depth, n, leaf, nodes, links, root, size)

# t spliced where d waits, d stopped needing t's handle (state 2)
def splice(d: KD.D, t: T.Tpl) -> KD.D:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      match t:
        case T.Tpl{nodes, links, root, +size}:
          sp.leaf(KS.d.at(h, top), path, top, depth, n, nodes, links, root, size)

# A finished demand whose root faces a data node holding a handle, as when
# a function returns a value's leaf (kernel.bend reads a result from the
# interface's peer alike): the handle, with the demand set as if stopped at
# the interface needing it (state 2, a fresh path, the interface its top,
# a negative node whose peer d.at finds), so that resuming or splicing
# serves it as any need; else the demand as it was, and none

def lazy.z.k(+lazy: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +k: U32) -> KD.D & Maybe<&2, U32>:
  match lazy:
    case True{}:
      (KD.D{h, KS.d.path(KM.m_new(6n, P.w_maxd())), P.iface(), 0, n, 2}, Some{k})
    case False{}:
      (KD.D{h, path, top, depth, n, st}, None{})

def lazy.z(z: P.Lz, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> KD.D & Maybe<&2, U32>:
  match z:
    case P.Lz{h, +lazy, +k}:
      lazy.z.k(lazy, h, path, top, depth, n, st, k)

def lazy.w(q: P.H & U32, +hb: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> KD.D & Maybe<&2, U32>:
  (h, +w) = q
  lazy.z(P.val_lazy(h, P.form(hb), w), path, top, depth, n, st)

def lazy.data(+data: Bool, h: P.H, +at: U32, +hb: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> KD.D & Maybe<&2, U32>:
  match data:
    case True{}:
      lazy.w(P.rd(h, (at + 2 : U32)), hb, path, top, depth, n, st)
    case False{}:
      (KD.D{h, path, top, depth, n, st}, None{})

def lazy.hb(q: P.H & U32, +at: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> KD.D & Maybe<&2, U32>:
  (h, +hb) = q
  lazy.data(U32.is_eq(P.rk(hb), 5), h, at, hb, path, top, depth, n, st)

def lazy.ps(+stat: Bool, h: P.H, +peer: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> KD.D & Maybe<&2, U32>:
  match stat:
    case True{}:
      (KD.D{h, path, top, depth, n, st}, None{})
    case False{}:
      lazy.hb(P.rd(h, P.base(peer)), P.base(peer), path, top, depth, n, st)

def lazy.peer(q: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> KD.D & Maybe<&2, U32>:
  (h, +peer) = q
  lazy.ps(P.is_static(peer), h, peer, path, top, depth, n, st)

def lazy_at(d: KD.D) -> KD.D & Maybe<&2, U32>:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      lazy.peer(P.rd(h, (P.iface() + 1 : U32)), path, top, depth, n, st)
