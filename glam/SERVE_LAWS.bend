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
import ./splice_copy.bend as S
import ./splice_model.bend as SM
import ./serve_model.bend as SV
import ./index_model.bend as IM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: the copy leaves the pending placeholders' invariant over the index
# (RG.px.ok): before it none pending, the live nodes Con{s, t}, the free
# list's first nodes the fresh nodes ns then F, the tracked nodes M then
# ns; after the splice's two passes, the copy's holes pending (RG.pls,
# through the map the node pass leaves) and live, F the free list's first
# nodes, the tracked nodes M then the holes alone (a hole faces a port of
# a copy node that is no hole, which no tracked node but a live one may
# hold the link word of). Premises besides: the tracked nodes laid out
# apart, their own bases, past the header's words; ns as many as the
# template makes, none static (SV.dyn); no port a live node faces linked
# into ns (RG.faces against ns); the live nodes distinct; the template's
# (SM.tpl.ok) and the
# crossings' (SV.copy.ok) (cells-freeze.sharing.cursors.index.ring.copy).
# Not claimed: growth; that ns are free; that freeze builds such
# templates.
# Record: copy-reduced-function-nets
# Record: splice-frame-premises
# Record: serve-write-sets-hybrid
# Record: cursors-indexed
# Record: serve-premises-over-index
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
  for +I: IM.Ix
  for +F: List<&2, U32>
  for +M: List<&2, U32>
  for +hf: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for +hN: {RG.layout(List.append(&2, U32, M, ns), d) == True{} : Bool}
  for +hB: {RG.bases(List.append(&2, U32, M, ns)) == True{} : Bool}
  for +hp: {RG.px.ok(AD.view(U32, w), d, s, I, Nil{}, Con{s, t}, List.append(&2, U32, ns, F), List.append(&2, U32, M, ns)) == True{} : Bool}
  for +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}
  for +hdy: {SV.dyn(ns) == True{} : Bool}
  for +hpa: {KMd.past(List.append(&2, U32, M, ns), d) == True{} : Bool}
  for +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  for +hfr: {RG.faces(Con{s, t}, AD.view(U32, w), d, ns) == True{} : Bool}
  for +hLd: {RG.distinct(Con{s, t}) == True{} : Bool}
  for +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}
  for +hcp: {SV.copy.ok(cs, ls, ts, dm) == True{} : Bool}
  {RG.px.ok(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))))), d, s, I, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm), List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F, List.append(&2, U32, M, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm))) == True{} : Bool}

# LAW: a serve's writes, its copy then its crossings (R.crossings, the
# holes joined to the ring's cursors or made cursors), as the materializer
# makes them off the source's root: no word but the fresh nodes', the
# ring's nodes', the header's a value or an error writes, and the link
# words of the ports the ring's members faced; under copy_pend's premises
# (cells-freeze.nested.host.serve.frame). The bound the Hierarchy review
# asked of a serve, what the demand's walk resumed may read past. At the
# source's root the served cursor leaves after (R.leave), a law to come.
# Record: copy-reduced-function-nets
# Record: serve-write-sets-hybrid
law serve_keeps:
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
  for +j: U32
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
  for +hj: {KMd.nodes.off(ns, d, j) == True{} : Bool}
  for +hjr: {RG.off.nodes(Con{s, t}, d, j) == True{} : Bool}
  for +hjh: {KMd.off.words(KMd.hdr_all(), d, j) == True{} : Bool}
  for +hjf: {RG.off.ports(RG.faced(Con{s, t}, AD.view(U32, w), d), d, j) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(Pair.snd(Array<U32>, P.H, R.crossings(cs, (SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))), SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), s)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: a serve at the source's root, its copy, its crossings and then the
# served cursor nc leaving, the copy's root port (read through the map as
# the materializer reads it, mz.root) joined in its place, leaves the ring
# exact with its nodes, nc out of it (serve_exact on copy_pend): the
# premises copy_pend's, nc in the ring, no crossing looking for its
# position (RG.unfound), and the root a node no hole at a port below 3
# (SV.root.ok) (cells-freeze.nested.host.serve.exact). Not claimed: the
# frame of the leave at the root (.serve.root); that freeze builds such
# roots; the net's links two-way after the leave, which overwrites the
# root port's link word: a template linking the root's port would leave
# its partner facing the root alone, the ring exact still (freeze links
# no root port, fz.peer.k, an obligation for its review).
# Record: copy-reduced-function-nets
# Record: serve-write-sets-hybrid
law serve_ring_exact:
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
  for +nc: U32
  for +rn: U32
  for +rp: U32
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
  for +hnc: {RG.has(t, nc) == True{} : Bool}
  for +hu: {RG.unfound(cs, AD.view(U32, w), d, nc) == True{} : Bool}
  for +hro: {SV.root.ok(rn, rp, ts, dm, cs) == True{} : Bool}
  {RG.ring.ok(AD.view(U32, RG.words(R.leave(Pair.snd(Array<U32>, P.H, R.crossings(cs, (SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))), SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), s)), (Pair.snd(Array<U32>, U32, Array.get(U32, Pair.fst(Array<U32>, P.H, R.crossings(cs, (SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))), SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), s)), rn)) + rp : U32), nc))), d, s, RG.without(Pair.fst(List<&2, U32>, List<&2, U32>, RG.cr(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))))), d, t, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)))), nc)) == True{} : Bool}

# LAW: a serve's writes at the source's root, its copy, its crossings and
# the served cursor's leave (serve_keeps's, then the leave's): no word
# but the fresh nodes', the ring's nodes', the header's a value or an
# error writes, and the link words of the ports the ring's members faced;
# under serve_ring_exact's premises (cells-freeze.nested.host.serve.root).
# The leave writes the link word of the port the cursor faces after the
# crossings, which a join may have changed: each node of the ring and the
# holes faces, through the crossings, a port one of them faced after the
# copy, so that the bound holds. Not claimed: as serve_ring_exact.
# Record: copy-reduced-function-nets
# Record: serve-write-sets-hybrid
law serve_root_keeps:
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
  for +nc: U32
  for +rn: U32
  for +rp: U32
  for +j: U32
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
  for +hnc: {RG.has(t, nc) == True{} : Bool}
  for +hu: {RG.unfound(cs, AD.view(U32, w), d, nc) == True{} : Bool}
  for +hro: {SV.root.ok(rn, rp, ts, dm, cs) == True{} : Bool}
  for +hj: {KMd.nodes.off(ns, d, j) == True{} : Bool}
  for +hjr: {RG.off.nodes(Con{s, t}, d, j) == True{} : Bool}
  for +hjh: {KMd.off.words(KMd.hdr_all(), d, j) == True{} : Bool}
  for +hjf: {RG.off.ports(RG.faced(Con{s, t}, AD.view(U32, w), d), d, j) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(R.leave(Pair.snd(Array<U32>, P.H, R.crossings(cs, (SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))), SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), s)), (Pair.snd(Array<U32>, U32, Array.get(U32, Pair.fst(Array<U32>, P.H, R.crossings(cs, (SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))), SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), s)), rn)) + rp : U32), nc), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}
