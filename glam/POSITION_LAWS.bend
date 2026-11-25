# Laws of positioned demand (glam/position.bend), stated over
# glam/position_model.bend; proved in glam/POSITION_PROOF.bend.

import Base
import ../spike/kprim.bend as P
import ./position.bend as Q
import ./position_model.bend as QM
import ../spike/kdemand.bend as KD
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/knet.bend as KN
import ../spike/krules.bend as KR
import ../spike/kmodel.bend as KMd
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: positioned demand's frontier faces the position
# (cursor-laws.noself.frontier.faces): when a source demanded at a
# position ends at the frontier (Q.PdFront), its port is the position's
# link word in the frontier's own heap, however many walks ran. Any heap.
# So the cursor a serve finds there is at the port the position faces;
# with the source wired (wired_port), never the position itself
# (.frontier.apart). Not claimed: anything of the other ends.
# Record: copy-reduced-function-nets
# Record: cursors-indexed
law front_faces:
  for h: P.H
  for +pos: U32
  for +g: Nat
  for +f: Nat
  {QM.front.at(Q.positioned(h, pos, g, f), pos) == True{} : Bool}

# LAW: front_faces for demand going on from a walk d stopped and set
# going again (Q.positioned.from, a serve going on, serve.from): its
# frontier's port is the position's link word in the frontier's own
# heap, any walk, no premise.
# Record: copy-reduced-function-nets
# Record: cursors-indexed
law front_faces_from:
  for d: KD.D
  for +pos: U32
  for +g: Nat
  for +f: Nat
  {QM.front.at(Q.positioned.from(d, pos, g, f), pos) == True{} : Bool}

# LAW: the frontier apart from the position
# (cursor-laws.noself.frontier.apart): a frontier facing a position
# (front_faces' fact, QM.front.at) in a heap the wiring's audit passes is
# not the position itself, the position node j's port p below its kind's
# arity and no static. So the cursor found at the frontier's port is not
# keyed at the position (.frontier.cursor). Premises on the frontier's
# heap, the kernel's to discharge (kernel-refine): wired
# (net-obvious-errors), and the position a live node's
# port there, a finished node being untouched by the walks
# (copied-nodes-untouched).
# Record: net-obvious-errors
# Record: cursors-indexed
law front_apart:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for hf: {AD.full(U32, w, d) == True{} : Bool}
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
  for +q: U32
  for +n: U32
  for hfa: {QM.front.at(Q.PdFront{P.H{KM.MG{w}, a}, q, n}, pos) == True{} : Bool}
  {U32.is_eq(q, pos) == False{} : Bool}
