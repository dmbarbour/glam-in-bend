# The splice's laws (cells-freeze.nested.host.splice): a frame over an
# exact list of words (serve-write-sets-hybrid; splice-frame-premises).
# Apart from glam/LAWS.bend, the cursors', so that the cursors' laws keep
# their imports to the heap's primitives: the splice's reach the kernel's
# loader (knet.bend), and every change to the kernel reruns these.

import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/tpl.bend as T
import ../spike/kmodel.bend as KMd
import ./splice_copy.bend as S
import ./splice_model.bend as SM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: the splice's node pass, its fresh nodes ns the free list's first
# ones (KMd.chain), laid out apart and past the header's words a splice
# writes, one for each template node but an eraser, which makes none
# (SM.made; cells-freeze.nested.host.splice.single), writes no word but
# theirs, the head, and the header's words a value or an error writes
# (KMd.hdr_all), the heap deep enough that those words are apart from
# the head's: every other word reads as before
# (cells-freeze.nested.host.splice.pops). Not claimed: the reserve's and
# the doubling's paths, the list running out; that ns are free and none
# live (the allocator's prefix law, to come).
# Record: splice-frame-premises
# Record: serve-write-sets-hybrid
# Record: splice-erasers-static
law nodes_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for +ts: List<&2, T.TNode>
  for +i: U32
  for +by: U32
  for +ns: List<&2, U32>
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}
  for hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}
  for hap: {KMd.apart(ns, d) == True{} : Bool}
  for hpa: {KMd.past(ns, d) == True{} : Bool}
  for hj: {KMd.nodes.off(ns, d, j) == True{} : Bool}
  for hjh: {KMd.off.words(KMd.hdr_all(), d, j) == True{} : Bool}
  for hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.nodes(ts, i, S.Sp{P.H{KM.MG{w}, a}, map}, by)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: the splice's node pass, under nodes_keeps's premises and the map
# full at a depth below 32, leaves the map as the model folds the pass's
# writes (SM.ent): at an eraser's slot the static, at a node's the next
# fresh node of ns, in order, a later write over an earlier at one slot
# (the index mod 2^dm), every other slot as before
# (cells-freeze.nested.host.splice.maps). Which slot holds what for the
# links is the template's premise to say (.splice.tpl).
# Record: splice-frame-premises
# Record: splice-erasers-static
law nodes_maps:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for +dm: Nat
  for +ts: List<&2, T.TNode>
  for +i: U32
  for +by: U32
  for +ns: List<&2, U32>
  for +ix: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}
  for hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}
  for hap: {KMd.apart(ns, d) == True{} : Bool}
  for hpa: {KMd.past(ns, d) == True{} : Bool}
  for hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  {KMd.word(AD.view(U32, SM.map(S.sp.nodes(ts, i, S.Sp{P.H{KM.MG{w}, a}, map}, by))), dm, ix) == SM.ent(ts, ns, i, dm, ix, KMd.word(AD.view(U32, map), dm, ix)) : U32}

# LAW: the splice's links pass, each link's ends naming through the map
# a static or a fresh node of ns and a node's port (SM.ends.ok), writes
# no word but the fresh nodes': a static's link word is none, so that an
# eraser mapped to the static writes nothing of its own; every other
# word reads as before (cells-freeze.nested.host.splice,
# .splice.single; splice-frame-premises).
# Record: splice-frame-premises
# Record: serve-write-sets-hybrid
# Record: splice-erasers-static
law links_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for +dm: Nat
  for +ls: List<&2, T.TLink>
  for +ns: List<&2, U32>
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for he: {SM.ends.ok(ls, AD.view(U32, map), dm, ns) == True{} : Bool}
  for hj: {KMd.nodes.off(ns, d, j) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{w}, a}, map})), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: the splice's links pass leaves every word as the model folds its
# writes (SM.lw): each link writes its first end's link word with the
# second end, then the second's with the first, a static end's none, a
# later write over an earlier at one slot; the heap and the map full, no
# premise on the ends (cells-freeze.nested.host.serve.pend: a hole's
# word 1, the port it faces, read from it).
# Record: splice-frame-premises
# Record: splice-erasers-static
law links_words:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for +dm: Nat
  for +ls: List<&2, T.TLink>
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(ls, S.Sp{P.H{KM.MG{w}, a}, map})), j)) == SM.lw(ls, AD.view(U32, map), dm, d, j, Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j))) : U32}

# LAW: the copy's two passes, the node pass from index 0 then the links
# pass, write no word but the fresh nodes', the head and the header's
# words a value or an error writes, under the node pass's premises, the
# map full at a depth below 32, and the template's (SM.tpl.ok: each
# link's ends name a slot the node pass writes, at a port its node has):
# every other word reads as before (cells-freeze.nested.host.splice.law;
# serve-write-sets-hybrid). Not claimed: growth; that ns are free and
# none live (the allocator's prefix law); that freeze's templates satisfy
# SM.tpl.ok; the splice's writes around the copy (.host.path).
# Record: splice-frame-premises
# Record: serve-write-sets-hybrid
# Record: splice-erasers-static
law splice_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for +dm: Nat
  for +ts: List<&2, T.TNode>
  for +ls: List<&2, T.TLink>
  for +by: U32
  for +ns: List<&2, U32>
  for +j: U32
  for +hf: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for +hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for +hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}
  for +hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}
  for +hap: {KMd.apart(ns, d) == True{} : Bool}
  for +hpa: {KMd.past(ns, d) == True{} : Bool}
  for +hj: {KMd.nodes.off(ns, d, j) == True{} : Bool}
  for +hjh: {KMd.off.words(KMd.hdr_all(), d, j) == True{} : Bool}
  for +hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  for +ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: and the splice, its fresh nodes ns the free list's first ones and
# the nodes F the next (KMd.chain over both), all apart and past the
# header's words, leaves F the free list's first nodes: the node pass
# takes ns, the head it leaves F's first, and neither pass writes F's
# links (cells-freeze.sharing.cursors.index.ring.copy: the copy's hand-off,
# a crossing's insert taking F's first for its branch). Not claimed:
# growth, which the list's running out would take.
# Record: splice-frame-premises
# Record: cursors-indexed
law splice_free:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for +dm: Nat
  for +ts: List<&2, T.TNode>
  for +ls: List<&2, T.TLink>
  for +by: U32
  for +ns: List<&2, U32>
  for +F: List<&2, U32>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for hc: {KMd.chain(List.append(&2, U32, ns, F), AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}
  for hl: {SM.made(ts) == List.length(&2, U32, ns) : Nat}
  for hap: {KMd.apart(List.append(&2, U32, ns, F), d) == True{} : Bool}
  for hpa: {KMd.past(List.append(&2, U32, ns, F), d) == True{} : Bool}
  for hhd: {KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{} : Bool}
  for ht: {SM.tpl.ok(ls, ts, dm) == True{} : Bool}
  {KMd.chain(F, AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))))), d, KMd.word(AD.view(U32, KMd.words(SM.heap(S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{P.H{KM.MG{w}, a}, map}, by))))), d, P.at_fh())) == True{} : Bool}

# LAW: the map a splice and a freeze make for a template of n nodes
# ([0 : U32^T.depth_for(31n, n, 0n)], glam/materialize.bend's mz.fz.t)
# has a depth below 32, is full at it, and holds n indices apart, n at
# most 2^depth, for n up to 2^31: what the serve's laws ask of the map
# (hfm, hdm) and of a template's indices in its slots
# (cursor-laws.materializer.template.depth). Not claimed: that the depth
# is the least.
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law map_depth:
  for +n: U32
  for hn: {U32.is_le(n, 2147483648) == True{} : Bool}
  {Nat.is_lt(T.depth_for(31n, n, 0n), 32n) && (Nat.is_le(U32.to_nat(n), Nat.pow(2n, T.depth_for(31n, n, 0n))) && AD.full(U32, [0 : U32^T.depth_for(31n, n, 0n)], T.depth_for(31n, n, 0n))) == True{} : Bool}

# LAW: the map's depth at most k for a size at most 2^k, k at most 31: the
# search stops at its first fit (cursor-laws.materializer.template.depth.upper).
# With map_depth's n at most 2^depth, the depth is the least that fits.
# What the write phase's laws ask of the hash map's depth, 1 +
# depth_for(n << 1), below 32 (emits_far, put_keeps): k = 29 for a
# template of at most 2^28 nodes read back, the heap's capacity.
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law depth_upper:
  for +n: U32
  for +k: Nat
  for hk: {Nat.is_le(k, 31n) == True{} : Bool}
  for hn: {U32.is_le(n, U32.shln(1, k)) == True{} : Bool}
  {Nat.is_le(T.depth_for(31n, n, 0n), k) == True{} : Bool}
