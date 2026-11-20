# The serve's laws (cells-freeze.nested.host.serve): the splice's copy
# (glam/SPLICE_LAWS.bend) joined to the ring's crossings (glam/LAWS.bend).
# Apart from both, so that the ring's laws keep their imports to the
# heap's primitives and the splice's theirs; importing both, a verdict
# here costs about the splice's (the Cells plan's .host.witness.verdicts).

import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/tpl.bend as T
import ../spike/kmodel.bend as KMd
import ./ring.bend as R
import ./ring_model.bend as RG
import ./splice.bend as S
import ./splice_model.bend as SM
import ./serve_model.bend as SV
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: the copy leaves the pending placeholders' invariant
# (RG.pend.ok): after the splice's two passes, the ring as it was, the
# copy's holes pending (RG.pls, through the map the node pass leaves),
# the ring's nodes and the holes the list L. Premises: the ring exact
# with its nodes; the fresh nodes ns the free list's first ones, as many
# as the template makes, laid out apart from the ring's and each other
# (RG.layout), their own bases, none static (SV.dyn), past the header's
# written words, the ring's too, and no port a member faces linked into
# them (RG.faces against ns); the template's (SM.tpl.ok) and the
# crossings' (SV.copy.ok: each hole a node's index, apart, its port 0
# alone linked, to a node no hole) (cells-freeze.nested.host.serve.pend).
# Not claimed:
# growth; that ns are free (the allocator's prefix law); that freeze
# builds such templates (.splice.freeze, after freeze's design).
# Record: copy-reduced-function-nets
# Record: splice-frame-premises
# Record: serve-write-sets-hybrid
law copy_pend:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for +dm: Nat
  for +ts: List<&2, T.TNode>
  for +ls: List<&2, T.TLink>
  for +by: U32
  for +ns: List<&2, U32>
  for +s: U32
  for +t: List<&2, U32>
  for +cs: List<&2, R.FzC>
  for +hf: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for +hr: {RG.ring.ok(AD.view(U32, w), d, s, t) == True{} : Bool}
  for +hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}
  for +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}
  for +hlay: {RG.layout(List.append(&2, U32, Con{s, t}, ns), d) == True{} : Bool}
  for +hbs: {RG.bases(ns) == True{} : Bool}
  for +hdy: {SV.dyn(ns) == True{} : Bool}
  for +hpa: {KMd.past(List.append(&2, U32, Con{s, t}, ns), d) == True{} : Bool}
  for +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  for +hfr: {RG.faces(Con{s, t}, AD.view(U32, w), d, ns) == True{} : Bool}
  for +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}
  for +hcp: {SV.copy.ok(cs, ls, ts, dm) == True{} : Bool}
  {RG.pend.ok(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))))), d, s, t, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm), List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm))) == True{} : Bool}
