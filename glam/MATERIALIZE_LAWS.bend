# Laws of the cursor serve (glam/materialize.bend), composed of the laws
# of positioned demand (glam/POSITION_LAWS.bend) and of the index
# (glam/INDEX_LAWS.bend); proved in glam/MATERIALIZE_PROOF.bend.

import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/knet.bend as KN
import ../spike/krules.bend as KR
import ../spike/kmodel.bend as KMd
import ./position.bend as Q
import ./ring.bend as R
import ./index_model.bend as IM
import ./materialize.bend as M
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: a serve whose positioned demand ends at the frontier joins the
# served cursor nc to the cursor the host's index finds at the frontier's
# port, never reporting it as itself (cursor-laws.noself.frontier.cursor):
# the port faces the position (front_faces) and is not it (front_apart),
# and the cursor found there holds the port as its key, where nc holds
# the position (found_apart). So sv.front.c's check never fires, under
# the premises. On the source's frontier heap, the kernel's to discharge
# (kernel-refine): wired (wiring-premise-before-refinement), and the
# position a live node's port there, a finished node being untouched by
# the walks (copied-nodes-untouched). On the host: its words realizing
# the index of the situating node on its invariant (find_tree's), and
# nc's word 2 the position, as the serve reads it there. Not claimed:
# the frontier's port without a cursor (the climb), or the other ends.
# Record: wiring-premise-before-refinement
# Record: cursors-indexed
law front_joins:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +hf: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hwd: {Pair.snd(P.H, Bool, KN.wired_ok(P.H{KM.MG{w}, a})) == True{} : Bool}
  for +j: U32
  for +p: U32
  for +hj: {U32.is_le(P.first(), j) == True{} : Bool}
  for hjc: {U32.is_lt(j, KMd.word(AD.view(U32, w), d, P.at_wcap())) == True{} : Bool}
  for hpa: {U32.is_lt(p, KR.kind_arity(P.rk(KMd.word(AD.view(U32, w), d, (j << 2n : U32))))) == True{} : Bool}
  for +pos: U32
  for +hpos: {pos == ((j << 2n : U32) + p : U32) : U32}
  for +hns: {P.is_static(pos) == False{} : Bool}
  for s0: P.H
  for +g: Nat
  for +f: Nat
  for +q: U32
  for +n: U32
  for +hpd: {Q.positioned(s0, pos, g, f) == Q.PdFront{P.H{KM.MG{w}, a}, q, n} : Q.Pd}
  for wh: Array<U32>
  for ah: Array<V.Val>
  for +dh: Nat
  for hfh: {AD.full(U32, wh, dh) == True{} : Bool}
  for +hdh32: {Nat.is_lt(dh, 32n) == True{} : Bool}
  for +situ: U32
  for +I: IM.Ix
  for +hr: {IM.ix.real(AD.view(U32, wh), dh, situ, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for +nc: U32
  for +hn: {KMd.word(AD.view(U32, wh), dh, (nc + 2 : U32)) == pos : U32}
  for +k: U32
  for +c: U32
  for +hc: {IM.ix.look(I, q) == Some{c} : Maybe<&2, U32>}
  {M.sv.pd(Q.positioned(s0, pos, g, f), P.H{KM.MG{wh}, ah}, situ, k, nc, pos) == M.SvOk{P.H{KM.MG{w}, a}, R.join(P.H{KM.MG{wh}, ah}, nc, c), n, 1} : M.Sv}

# LAW: front_joins on the one-net path (sv1.pd, self-copies-are-cursors):
# the source the host itself, every premise on the heap after the walks,
# the index's among them: that the walks keep the host's index and nc's
# word 2 is owed (cursor-laws.noself.frontier.cursor).
# Record: wiring-premise-before-refinement
# Record: cursors-indexed
# Record: self-copies-are-cursors
law front_joins1:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +hf: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hwd: {Pair.snd(P.H, Bool, KN.wired_ok(P.H{KM.MG{w}, a})) == True{} : Bool}
  for +j: U32
  for +p: U32
  for +hj: {U32.is_le(P.first(), j) == True{} : Bool}
  for hjc: {U32.is_lt(j, KMd.word(AD.view(U32, w), d, P.at_wcap())) == True{} : Bool}
  for hpa: {U32.is_lt(p, KR.kind_arity(P.rk(KMd.word(AD.view(U32, w), d, (j << 2n : U32))))) == True{} : Bool}
  for +pos: U32
  for +hpos: {pos == ((j << 2n : U32) + p : U32) : U32}
  for +hns: {P.is_static(pos) == False{} : Bool}
  for s0: P.H
  for +g: Nat
  for +f: Nat
  for +q: U32
  for +n: U32
  for +hpd: {Q.positioned(s0, pos, g, f) == Q.PdFront{P.H{KM.MG{w}, a}, q, n} : Q.Pd}
  for +situ: U32
  for +I: IM.Ix
  for +hr: {IM.ix.real(AD.view(U32, w), d, situ, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for +nc: U32
  for +hn: {KMd.word(AD.view(U32, w), d, (nc + 2 : U32)) == pos : U32}
  for +k: U32
  for +c: U32
  for +hc: {IM.ix.look(I, q) == Some{c} : Maybe<&2, U32>}
  {M.sv1.pd(Q.positioned(s0, pos, g, f), situ, k, nc, pos) == M.S1Ok{R.join(P.H{KM.MG{w}, a}, nc, c), n, 1} : M.Sv1}
