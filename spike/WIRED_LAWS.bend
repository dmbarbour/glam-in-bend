# Laws of the wiring's audit (KN.wired_ok, spike/knet.bend), read as
# facts the materializer's laws take as premises
# (wiring-premise-before-refinement); proved in spike/WIRED_PROOF.bend.

import Base
import ./kprim.bend as P
import ./kmem_grow.bend as KM
import ./val.bend as V
import ./knet.bend as KN
import ./krules.bend as KR
import ./kmodel.bend as KMd
import ./wired_model.bend as WR
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: a net the wiring's audit passes (KN.wired_ok, the premise the
# materializer's laws take) has each live node's port below its kind's
# arity pass the audit's check of one port (WR.port.ok): its link a
# static eraser, or a port of a live node within the capacity, below its
# kind's arity, not itself, that links it back. So no port faces itself,
# and links are two-way (cursor-laws.noself.model). The node is named
# by its index j, its port by p, as the audit counts them. Not claimed:
# that the kernel's rewrites keep the audit passing (kernel-refine).
# Record: wiring-premise-before-refinement
# Record: static-links-count-as-nodes
law wired_port:
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
  {WR.port.ok(AD.view(U32, w), d, ((j << 2n : U32) + p : U32), KMd.word(AD.view(U32, w), d, P.at_wcap())) == True{} : Bool}
