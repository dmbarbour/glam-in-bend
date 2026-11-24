# The serve's laws (cells-freeze.nested.host.serve): the splice's copy
# (glam/SPLICE_LAWS.bend) joined to the crossings over the index
# (glam/LAWS.bend). Apart from both, so that the cursors' laws keep their
# imports to the heap's primitives and the splice's theirs; importing both, a verdict
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
import ./serve.bend as SC
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
# hold the link word of). With it, what the crossings ask besides
# (crossings_pend; IndexPremises P1): the words and the map full, the
# tracked nodes after laid out apart, each its own base. Premises
# besides: the tracked nodes laid out apart, their own bases, past the
# header's words; ns as many as the template makes; the live nodes
# distinct; the template's (SM.tpl.ok) and the crossings' (SV.copy.ok)
# (cells-freeze.sharing.cursors.index.ring.copy). That ns are no statics
# (SV.dyn) and that no port a live node faces is linked into them
# (RG.faces against ns) follow, from their bases and the invariant's
# link words (dyn_of_bases, faces_fresh; IndexPremises P3).
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
  for +hpa: {KMd.past(List.append(&2, U32, M, ns), d) == True{} : Bool}
  for +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  for +hLd: {RG.distinct(Con{s, t}) == True{} : Bool}
  for +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}
  for +hcp: {SV.copy.ok(cs, ls, ts, dm) == True{} : Bool}
  {RG.px.ok(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))))), d, s, I, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm), List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F, List.append(&2, U32, M, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm))) && (AD.full(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), d) && (AD.full(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))), dm) && (RG.layout(List.append(&2, U32, M, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), d) && RG.bases(List.append(&2, U32, M, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)))))) == True{} : Bool}

# LAW: a serve away from the source's root, its copy then its crossings
# (R.crossings, the holes joined to the cursors the index finds or made
# cursors), keeps the pending placeholders' invariant over the index and
# the words full: copy_pend, then crossings_pend on what it gives, the
# laws composed as laws (IndexPremises P1). Over the crossings' model
# (RG.cxs) from the index, the live nodes and the free list the copy
# leaves; none pending after, the tracked nodes M then the holes.
# Premises: copy_pend's, and the crossings' over the map the copy leaves
# (RG.cxs.ok).
# Stated over SC.serve, the materializer's own composition
# (glam/serve.bend; laws-over-tests, cursor-laws.materializer).
# Record: copy-reduced-function-nets
# Record: serve-premises-over-index
# Record: cursors-indexed
law serve_pend:
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
  for +nc: U32
  for +rn: U32
  for +rp: U32
  for +hf: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for +hN: {RG.layout(List.append(&2, U32, M, ns), d) == True{} : Bool}
  for +hB: {RG.bases(List.append(&2, U32, M, ns)) == True{} : Bool}
  for +hp: {RG.px.ok(AD.view(U32, w), d, s, I, Nil{}, Con{s, t}, List.append(&2, U32, ns, F), List.append(&2, U32, M, ns)) == True{} : Bool}
  for +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}
  for +hpa: {KMd.past(List.append(&2, U32, M, ns), d) == True{} : Bool}
  for +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  for +hLd: {RG.distinct(Con{s, t}) == True{} : Bool}
  for +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}
  for +hcp: {SV.copy.ok(cs, ls, ts, dm) == True{} : Bool}
  for +hok: {RG.cxs.ok(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, F) == True{} : Bool}
  {RG.px.ok(AD.view(U32, RG.words(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, False{}))), d, s, RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), Nil{}, RG.cxs.L(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), RG.cxs.F(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), List.append(&2, U32, M, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm))) && AD.full(U32, RG.words(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, False{})), d) == True{} : Bool}

# LAW: a serve's writes, its copy then its crossings (R.crossings, the
# holes joined to the cursors the index finds or made cursors), as the
# materializer makes them off the source's root: no word but the fresh
# nodes', the tracked nodes' (M: the live nodes, the index's, the free
# list's), the header's a value or an error writes, and the link words of
# the ports the live nodes faced; under copy_pend's premises and the
# crossings' (RG.cxs.ok, over the index and the free list the copy leaves)
# (cells-freeze.sharing.cursors.index.ring.leave). The bound the
# Hierarchy review asked of a serve, what the demand's walk resumed may
# read past. At the source's root the served cursor leaves after
# (R.leave), serve_root_keeps.
# Stated over SC.serve, the materializer's own composition
# (glam/serve.bend; laws-over-tests, cursor-laws.materializer).
# Record: copy-reduced-function-nets
# Record: serve-write-sets-hybrid
# Record: cursors-indexed
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
  for +I: IM.Ix
  for +F: List<&2, U32>
  for +M: List<&2, U32>
  for +nc: U32
  for +rn: U32
  for +rp: U32
  for +j: U32
  for +hf: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for +hN: {RG.layout(List.append(&2, U32, M, ns), d) == True{} : Bool}
  for +hB: {RG.bases(List.append(&2, U32, M, ns)) == True{} : Bool}
  for +hp: {RG.px.ok(AD.view(U32, w), d, s, I, Nil{}, Con{s, t}, List.append(&2, U32, ns, F), List.append(&2, U32, M, ns)) == True{} : Bool}
  for +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}
  for +hpa: {KMd.past(List.append(&2, U32, M, ns), d) == True{} : Bool}
  for +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  for +hLd: {RG.distinct(Con{s, t}) == True{} : Bool}
  for +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}
  for +hcp: {SV.copy.ok(cs, ls, ts, dm) == True{} : Bool}
  for +hok: {RG.cxs.ok(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, F) == True{} : Bool}
  for +hj: {KMd.nodes.off(ns, d, j) == True{} : Bool}
  for +hjM: {RG.off.nodes(M, d, j) == True{} : Bool}
  for +hjh: {KMd.off.words(KMd.hdr_all(), d, j) == True{} : Bool}
  for +hjf: {RG.off.ports(RG.faced(Con{s, t}, AD.view(U32, w), d), d, j) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, False{}), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: a serve at the source's root, its copy, its crossings and then the
# served cursor nc leaving, the copy's root port (read through the map as
# the materializer reads it, glam/serve.bend's rt) linked in its place,
# keeps the pending placeholders' invariant over the index and the words
# full (IndexPremises P1): nc out of the index and of the live nodes the
# crossings leave, the free list's first nodes nc
# and the removal's parent, then the crossings' (leave_pend on
# crossings_pend on copy_pend). Premises: copy_pend's, the crossings'
# (RG.cxs.ok), nc found at k in the index before them and no crossing
# looking for k at its far end (RG.far.off: nc kept through the
# crossings, look_del_other, look_put_other), and the root a node no
# hole at a port below 3 (SV.root.ok)
# (cells-freeze.sharing.cursors.index.ring.leave). Not claimed: the frame
# of the leave at the root (serve_root_keeps); that freeze builds such
# roots; the net's links two-way after the leave, which overwrites the
# root port's link word: a template linking the root's port would leave
# its partner facing the root alone, the invariant still (freeze links no
# root port, fz.peer.k, an obligation for its review).
# Stated over SC.serve, the materializer's own composition
# (glam/serve.bend; laws-over-tests, cursor-laws.materializer).
# Record: copy-reduced-function-nets
# Record: serve-write-sets-hybrid
# Record: cursors-indexed
# Record: serve-premises-over-index
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
  for +I: IM.Ix
  for +F: List<&2, U32>
  for +M: List<&2, U32>
  for +nc: U32
  for +k: U32
  for +rn: U32
  for +rp: U32
  for +hf: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for +hN: {RG.layout(List.append(&2, U32, M, ns), d) == True{} : Bool}
  for +hB: {RG.bases(List.append(&2, U32, M, ns)) == True{} : Bool}
  for +hp: {RG.px.ok(AD.view(U32, w), d, s, I, Nil{}, Con{s, t}, List.append(&2, U32, ns, F), List.append(&2, U32, M, ns)) == True{} : Bool}
  for +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}
  for +hpa: {KMd.past(List.append(&2, U32, M, ns), d) == True{} : Bool}
  for +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  for +hLd: {RG.distinct(Con{s, t}) == True{} : Bool}
  for +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}
  for +hcp: {SV.copy.ok(cs, ls, ts, dm) == True{} : Bool}
  for +hok: {RG.cxs.ok(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, F) == True{} : Bool}
  for +hc: {IM.ix.look(I, k) == Some{nc} : Maybe<&2, U32>}
  for +hu: {RG.far.off(cs, k) == True{} : Bool}
  for +hro: {SV.root.ok(rn, rp, ts, dm, cs) == True{} : Bool}
  {RG.px.ok(AD.view(U32, RG.words(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, True{}))), d, s, IM.ix.del(RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc, k), Nil{}, RG.without(RG.cxs.L(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc), Con{nc, IM.mb.cons(IM.ix.par(RG.cxs.I(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)), nc, k), RG.cxs.F(RG.cxs(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, List.append(&2, U32, Con{s, t}, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm)), F)))}, List.append(&2, U32, M, RG.pls(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm))) && AD.full(U32, RG.words(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, True{})), d) == True{} : Bool}

# LAW: a serve's writes at the source's root, its copy, its crossings and
# the served cursor's leave (serve_keeps's, then leave_keeps's): no word
# but the fresh nodes', the tracked nodes' (M: the live nodes, the
# index's, the free list's), the header's a value or an error writes, and
# the link words of the ports the live nodes faced; under
# serve_ring_exact's premises
# (cells-freeze.sharing.cursors.index.ring.leave). The leave writes the
# link word of the port the served cursor faces after the crossings, which
# a join may have changed: each live node faces, through the crossings, a
# port a live node or a hole faced after the copy (cfi.go), so that the
# bound holds. Not claimed: as serve_ring_exact.
# Stated over SC.serve, the materializer's own composition
# (glam/serve.bend; laws-over-tests, cursor-laws.materializer).
# Record: copy-reduced-function-nets
# Record: serve-write-sets-hybrid
# Record: cursors-indexed
# Record: serve-premises-over-index
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
  for +I: IM.Ix
  for +F: List<&2, U32>
  for +M: List<&2, U32>
  for +nc: U32
  for +k: U32
  for +rn: U32
  for +rp: U32
  for +j: U32
  for +hf: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for +hN: {RG.layout(List.append(&2, U32, M, ns), d) == True{} : Bool}
  for +hB: {RG.bases(List.append(&2, U32, M, ns)) == True{} : Bool}
  for +hp: {RG.px.ok(AD.view(U32, w), d, s, I, Nil{}, Con{s, t}, List.append(&2, U32, ns, F), List.append(&2, U32, M, ns)) == True{} : Bool}
  for +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}
  for +hpa: {KMd.past(List.append(&2, U32, M, ns), d) == True{} : Bool}
  for +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  for +hLd: {RG.distinct(Con{s, t}) == True{} : Bool}
  for +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}
  for +hcp: {SV.copy.ok(cs, ls, ts, dm) == True{} : Bool}
  for +hok: {RG.cxs.ok(cs, AD.view(U32, SM.map(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)))), dm, I, F) == True{} : Bool}
  for +hc: {IM.ix.look(I, k) == Some{nc} : Maybe<&2, U32>}
  for +hu: {RG.far.off(cs, k) == True{} : Bool}
  for +hro: {SV.root.ok(rn, rp, ts, dm, cs) == True{} : Bool}
  for +hj: {KMd.nodes.off(ns, d, j) == True{} : Bool}
  for +hjM: {RG.off.nodes(M, d, j) == True{} : Bool}
  for +hjh: {KMd.off.words(KMd.hdr_all(), d, j) == True{} : Bool}
  for +hjf: {RG.off.ports(RG.faced(Con{s, t}, AD.view(U32, w), d), d, j) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(SC.serve(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by)), cs, T.TE{rn, rp}, s, nc, True{}), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}
