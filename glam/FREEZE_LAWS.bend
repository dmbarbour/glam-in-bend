# Laws of glam/freeze.bend's write phase (the CursorLaws plan's
# cursor-laws.materializer.template.emit), stated over
# glam/freeze_model.bend; proved in glam/FREEZE_PROOF.bend.

import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/tpl.bend as T
import ./ring.bend as RN
import ./freeze.bend as F
import ./freeze_model.bend as FM
import ./ring_model.bend as RG
import ./splice_model.bend as SM
import ./serve_model.bend as SV
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: the write phase's count (cursor-laws.materializer.template.emit.counts):
# writing the nodes reached (F.fz.emits) keeps the template's next index
# just past the nodes standing for statics and cursors, and each crossing
# made at one of those cursors' placeholders, the crossings in the
# placeholders' order (FM.inv). Any heap; the map full at its depth, for
# the lookups' probe. Not claimed: what the links, the root or the
# crossings' positions are (.emit.links, .kinds, .positions); the
# placeholders' indices distinct, the count being on words (.compose,
# with no wrap past n); the template fz.tpl makes of the record, nor the
# nodes read n long (.compose); the map hm.fill makes full (.walk).
# Record: copy-reduced-function-nets
# Record: cursors-indexed
# Record: hub-laws-reused
law emits_counts:
  for +seen: List<&2, U32>
  for h: P.H
  for map: Array<U32>
  for +dm: Nat
  for hf: {AD.full(U32, map, dm) == True{} : Bool}
  for +n0: U32
  for +i: U32
  for +nodes: List<&2, T.TNode>
  for +eras: List<&2, T.TNode>
  for +ne: U32
  for +ls: List<&2, T.TLink>
  for +root: T.TEnd
  for +curs: List<&2, RN.FzC>
  for +hz: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}
  {FM.inv(F.fz.emits(seen, F.FzE{h, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}

# LAW: the write phase's links (cursor-laws.materializer.template.emit.links.ends):
# writing the nodes reached (F.fz.emits) keeps each link's near end a
# node read back (below n0), its ports below 3, and each index of the
# nodes standing for statics and cursors linked at its port 0 from a
# node read back (FM.inv.k). Premises: the counts' (emits_counts), the
# links' at the start, and the nodes' indices counting down from i below
# n0, at most i + 1 of them. Not claimed: where a link between two nodes
# read back ends (.emit.links.far); that a link names no index of eras
# but at port 0, which wants that end below n0; the root (.kinds).
# Record: copy-reduced-function-nets
# Record: cursors-indexed
# Record: hub-laws-reused
law emits_links:
  for +seen: List<&2, U32>
  for h: P.H
  for map: Array<U32>
  for +dm: Nat
  for hf: {AD.full(U32, map, dm) == True{} : Bool}
  for +n0: U32
  for +i: U32
  for +nodes: List<&2, T.TNode>
  for +eras: List<&2, T.TNode>
  for +ne: U32
  for +ls: List<&2, T.TLink>
  for +root: T.TEnd
  for +curs: List<&2, RN.FzC>
  for +hz: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}
  for +hk: {FM.inv.k(ls, eras, n0) == True{} : Bool}
  for +hi: {U32.is_lt(i, n0) == True{} : Bool}
  for +hl: {Nat.is_le(List.length(&2, U32, seen), 1n+U32.to_nat(i)) == True{} : Bool}
  {FM.inv.l(F.fz.emits(seen, F.FzE{h, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}

# LAW: a link's far end (cursor-laws.materializer.template.emit.links.far):
# writing the nodes reached (F.fz.emits) keeps each link's far end either
# a node read back (below n0) or port 0 of an index of the nodes for
# statics and cursors (FM.inv.j). Premises: the counts' (emits_counts);
# the map's values at most n0 (FM.vals.le over its view: the values sit
# at odd words, (i << 1) + 1), the map full at a depth of one or more
# and below 32 (the view's law); the links' far ends so at the start. Not
# claimed: the near ends (emits_links'); that the indices of eras are
# no node read back, which wants no wrap past n0 (.compose); the map's
# values so, which hm.fill gives (.walk).
# Record: copy-reduced-function-nets
# Record: cursors-indexed
# Record: hub-laws-reused
law emits_far:
  for +seen: List<&2, U32>
  for h: P.H
  for map: Array<U32>
  for +e: Nat
  for hf: {AD.full(U32, map, 1n+e) == True{} : Bool}
  for +hd32: {Nat.is_lt(1n+e, 32n) == True{} : Bool}
  for +n0: U32
  for hv: {FM.vals.le(AD.view(U32, map), n0) == True{} : Bool}
  for +i: U32
  for +nodes: List<&2, T.TNode>
  for +eras: List<&2, T.TNode>
  for +ne: U32
  for +ls: List<&2, T.TLink>
  for +root: T.TEnd
  for +curs: List<&2, RN.FzC>
  for +hz: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}
  for +hj: {FM.lks.far(ls, eras, n0) == True{} : Bool}
  {FM.inv.j(F.fz.emits(seen, F.FzE{h, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}

# LAW: the table's put (F.hm.put) keeps the map full at its depth and its
# values at most n0, for a value at most n0 (cursor-laws.materializer.template.walk.vals):
# what emits_far asks of the map (FM.vals.le), kept by each put of
# hm.fill. The key goes to the even word of the slot the probe stops at,
# the value to the odd word after it, so the keys never meet the bound.
# The map full at a depth of one or more and below 32 (the view's law).
# Not claimed: that a lookup finds what was put; that hm.new's map
# starts so (it computes for each size).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law put_keeps:
  for a: Array<U32>
  for +b: U32
  for +v: U32
  for +e: Nat
  for +n0: U32
  for hf: {AD.full(U32, a, 1n+e) == True{} : Bool}
  for +hd32: {Nat.is_lt(1n+e, 32n) == True{} : Bool}
  for hv: {FM.vals.le(AD.view(U32, a), n0) == True{} : Bool}
  for +hvn: {U32.is_le(v, n0) == True{} : Bool}
  {(AD.full(U32, F.hm.put(a, b, v), 1n+e) && FM.vals.le(AD.view(U32, F.hm.put(a, b, v)), n0)) == True{} : Bool}

# LAW: the root and the eras' kinds (cursor-laws.materializer.template.emit.kinds.root):
# writing the nodes reached (F.fz.emits) keeps the root a node read
# back's port below 3 (below n0), and each of the nodes standing for
# statics and cursors an eraser exactly when it is no placeholder
# (FM.inv.r; what SM.made counts). Premises: the root and eras so at the
# start, the nodes' indices counting down from i below n0, at most i + 1
# of them, the map full at its depth. Not claimed: that nodes is n long
# in index order, and that the root is no placeholder's index
# (.compose's); that the root faces the interface; the read nodes'
# kinds (.kinds.nodes).
# Record: copy-reduced-function-nets
# Record: cursors-indexed
# Record: hub-laws-reused
law emits_root:
  for +seen: List<&2, U32>
  for h: P.H
  for map: Array<U32>
  for +dm: Nat
  for hf: {AD.full(U32, map, dm) == True{} : Bool}
  for +n0: U32
  for +i: U32
  for +nodes: List<&2, T.TNode>
  for +eras: List<&2, T.TNode>
  for +ne: U32
  for +ls: List<&2, T.TLink>
  for +root: T.TEnd
  for +curs: List<&2, RN.FzC>
  for +hr: {FM.rt.ok(root, n0) == True{} : Bool}
  for +he: {FM.eras.ok(eras) == True{} : Bool}
  for +hi: {U32.is_lt(i, n0) == True{} : Bool}
  for +hl: {Nat.is_le(List.length(&2, U32, seen), 1n+U32.to_nat(i)) == True{} : Bool}
  {FM.inv.r(F.fz.emits(seen, F.FzE{h, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}

# LAW: the read nodes' kinds (cursor-laws.materializer.template.emit.kinds.nodes):
# writing the nodes reached (F.fz.emits) adds no eraser to the nodes read
# back (FM.inv.n), given each base reached aligned (a multiple of 4)
# with its header's kind no eraser's in the heap's words (FM.hdrs.ok, a
# kind tested by S.sp.is_era itself), the words full at a depth of 2 or
# more and below 32. An error's count (a free table entry read, word 1
# written) keeps each base's header, the base never word 1. Not claimed:
# that the walk's own test of a header (fz.is_era, on its code) agrees
# with its kind's (.walk's); that nodes is n long in index order.
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law emits_nodes:
  for +seen: List<&2, U32>
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +dm: Nat
  for hf: {AD.full(U32, map, dm) == True{} : Bool}
  for +d: Nat
  for hfw: {AD.full(U32, w, d) == True{} : Bool}
  for +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +h2: {Nat.is_le(2n, d) == True{} : Bool}
  for hh: {FM.hdrs.ok(seen, AD.view(U32, w), d) == True{} : Bool}
  for +n0: U32
  for +i: U32
  for +nodes: List<&2, T.TNode>
  for +eras: List<&2, T.TNode>
  for +ne: U32
  for +ls: List<&2, T.TLink>
  for +root: T.TEnd
  for +curs: List<&2, RN.FzC>
  for +hn: {FM.no_era(nodes) == True{} : Bool}
  {FM.inv.n(F.fz.emits(seen, F.FzE{P.H{KM.MG{w}, a}, map, nodes, eras, ne, ls, root, curs}, i)) == True{} : Bool}

# LAW: the nodes read back (cursor-laws.materializer.template.emit.length):
# writing the nodes reached (F.fz.emits) adds one node read back for each
# base listed, so that starting from none, nodes is as long as the list:
# n, the template's first n indices, when the walk lists n bases. Any
# heap, the map full at its depth. Not claimed: that the walk lists n
# bases (.walk's); which node each index holds (each is no eraser,
# emits_nodes, which is what the kinds want).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law emits_len:
  for +seen: List<&2, U32>
  for h: P.H
  for map: Array<U32>
  for +dm: Nat
  for hf: {AD.full(U32, map, dm) == True{} : Bool}
  for +i: U32
  for +nodes: List<&2, T.TNode>
  for +eras: List<&2, T.TNode>
  for +ne: U32
  for +ls: List<&2, T.TLink>
  for +root: T.TEnd
  for +curs: List<&2, RN.FzC>
  {List.length(&2, T.TNode, FM.nodes.of(F.fz.emits(seen, F.FzE{h, map, nodes, eras, ne, ls, root, curs}, i))) == Nat.add(List.length(&2, U32, seen), List.length(&2, T.TNode, nodes)) : Nat}

# LAW: the crossings' positions (cursor-laws.materializer.template.emit.positions):
# writing the nodes reached (F.fz.emits) keeps the crossings' positions
# distinct (RG.srcs), what cxs_start asks of a serve's crossings, given
# the listed nodes' port positions distinct (FM.ports: b + 0, b + 1,
# b + 2 for each base, as one list) and the crossings' so at the start,
# none of them among those. Any heap, the map full at its depth. Not
# claimed: that distinct aligned bases give distinct port positions (a
# lemma on words, .walk's); distinctness after fz.tpl's reversal
# (.compose's); the index's premises (RG.lacks.all, RG.enough) and
# RG.far.off, which are the serve's.
# Record: copy-reduced-function-nets
# Record: cursors-indexed
# Record: hub-laws-reused
law emits_pos:
  for +seen: List<&2, U32>
  for h: P.H
  for map: Array<U32>
  for +dm: Nat
  for hf: {AD.full(U32, map, dm) == True{} : Bool}
  for +i: U32
  for +nodes: List<&2, T.TNode>
  for +eras: List<&2, T.TNode>
  for +ne: U32
  for +ls: List<&2, T.TLink>
  for +root: T.TEnd
  for +curs: List<&2, RN.FzC>
  for +hd: {RG.distinct(FM.ports(seen)) == True{} : Bool}
  for +hs: {RG.distinct(RG.srcs(curs)) == True{} : Bool}
  for +hj: {FM.disj(RG.srcs(curs), FM.ports(seen)) == True{} : Bool}
  {RG.distinct(RG.srcs(FM.curs.of(F.fz.emits(seen, F.FzE{h, map, nodes, eras, ne, ls, root, curs}, i)))) == True{} : Bool}

# LAW: the template's crossings (cursor-laws.materializer.template.compose.positions):
# the template the write phase's record makes (F.fz.tpl) lists the record's
# crossings reversed, so that their positions are distinct where the
# record's are (emits_pos): what cxs_start asks of a serve's crossings.
# Not claimed: that the record's are so after the walk's (.tree's).
# Record: copy-reduced-function-nets
# Record: cursors-indexed
law tpl_pos:
  for h: P.H
  for map: Array<U32>
  for +nodes: List<&2, T.TNode>
  for +eras: List<&2, T.TNode>
  for +ne: U32
  for +ls: List<&2, T.TLink>
  for +root: T.TEnd
  for +curs: List<&2, RN.FzC>
  for +n: U32
  for +hs: {RG.distinct(RG.srcs(curs)) == True{} : Bool}
  {RG.distinct(RG.srcs(FM.fz.curs(Pair.snd(P.H, F.Fz, F.fz.tpl(F.FzE{h, map, nodes, eras, ne, ls, root, curs}, n))))) == True{} : Bool}

# LAW: the node pass's kind at an index (cursor-laws.materializer.template.compose.kinds):
# where every index of a template's nodes has a slot of its own at the
# map's depth (as many nodes as 2^dm at most), the kind the node pass
# last wrote at an index's slot (SM.kind_at) is the code of the node at
# that index (FM.kind.m: 1 for a node, 2 for an eraser, 0 past the last).
# So that the serve's premises on kinds (SM.tpl.ok, SV.copy.ok,
# SV.root.ok) read the template's nodes by position.
# Record: copy-reduced-function-nets
law kind_at_get:
  for +ts: List<&2, T.TNode>
  for +dm: Nat
  for +ix: U32
  for +hb: {Nat.is_le(List.length(&2, T.TNode, ts), Nat.pow(2n, dm)) == True{} : Bool}
  for +hd32: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for +hix: {Nat.is_lt(U32.to_nat(ix), Nat.pow(2n, dm)) == True{} : Bool}
  {SM.kind_at(ts, 0, dm, ix, 0) == FM.kind.m(List.get(&2, T.TNode, ts, U32.to_nat(ix))) : U32}

# LAW: the template's root (cursor-laws.materializer.template.compose.root):
# the template the write phase's record makes (F.fz.tpl) has its root at a
# node read back's port below 3, in no placeholder's slot, what the serve
# asks of a copy's root (SV.root.ok): given the record's root a node's
# port below 3 (emits_root's FM.rt.ok), the nodes read back n0 (emits_len)
# and no eraser (emits_nodes), the crossings the placeholders' (FM.inv.f,
# emits_counts), all within 2^dm, the map's depth. Not claimed: that the
# record is so after the walk (.tree's).
# Record: copy-reduced-function-nets
# Record: cursors-indexed
law tpl_root:
  for h: P.H
  for map: Array<U32>
  for +nodes: List<&2, T.TNode>
  for +eras: List<&2, T.TNode>
  for +ne: U32
  for +ls: List<&2, T.TLink>
  for +rn: U32
  for +rp: U32
  for +curs: List<&2, RN.FzC>
  for +n0: U32
  for +dm: Nat
  for +hn0: {U32.to_nat(n0) == List.length(&2, T.TNode, nodes) : Nat}
  for +hr: {FM.rt.ok(T.TE{rn, rp}, n0) == True{} : Bool}
  for +hne: {FM.no_era(nodes) == True{} : Bool}
  for +hf: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}
  for +hb: {Nat.is_le(Nat.add(U32.to_nat(n0), List.length(&2, T.TNode, eras)), Nat.pow(2n, dm)) == True{} : Bool}
  for +hd32: {Nat.is_lt(dm, 32n) == True{} : Bool}
  {SV.root.ok(FM.fz.rn(Pair.snd(P.H, F.Fz, F.fz.tpl(F.FzE{h, map, nodes, eras, ne, ls, T.TE{rn, rp}, curs}, n0))), FM.fz.rp(Pair.snd(P.H, F.Fz, F.fz.tpl(F.FzE{h, map, nodes, eras, ne, ls, T.TE{rn, rp}, curs}, n0))), FM.fz.tnodes(Pair.snd(P.H, F.Fz, F.fz.tpl(F.FzE{h, map, nodes, eras, ne, ls, T.TE{rn, rp}, curs}, n0))), dm, FM.fz.curs(Pair.snd(P.H, F.Fz, F.fz.tpl(F.FzE{h, map, nodes, eras, ne, ls, T.TE{rn, rp}, curs}, n0)))) == True{} : Bool}

# LAW: the template's links (cursor-laws.materializer.template.compose.links):
# the template the write phase's record makes (F.fz.tpl) has every link's
# end at a node read back's port below 3 or at an era's port 0, which the
# serve's node pass writes (SM.tpl.ok): given each link's near end so and
# its far end a node read back or an era's port 0 (emits_links' FM.lks.ok,
# emits_far's FM.lks.far), the nodes read back n0 and no eraser, all within
# 2^dm, the map's depth. Not claimed: that the record is so after the walk
# (.tree's).
# Record: copy-reduced-function-nets
law tpl_links:
  for h: P.H
  for map: Array<U32>
  for +nodes: List<&2, T.TNode>
  for +eras: List<&2, T.TNode>
  for +ne: U32
  for +ls: List<&2, T.TLink>
  for +root: T.TEnd
  for +curs: List<&2, RN.FzC>
  for +n0: U32
  for +dm: Nat
  for +hn0: {U32.to_nat(n0) == List.length(&2, T.TNode, nodes) : Nat}
  for +hne: {FM.no_era(nodes) == True{} : Bool}
  for +hl: {FM.lks.ok(ls, n0) == True{} : Bool}
  for +hf: {FM.lks.far(ls, eras, n0) == True{} : Bool}
  for +hb: {Nat.is_le(Nat.add(U32.to_nat(n0), List.length(&2, T.TNode, eras)), Nat.pow(2n, dm)) == True{} : Bool}
  for +hd32: {Nat.is_lt(dm, 32n) == True{} : Bool}
  {SM.tpl.ok(FM.fz.links(Pair.snd(P.H, F.Fz, F.fz.tpl(F.FzE{h, map, nodes, eras, ne, ls, root, curs}, n0))), FM.fz.tnodes(Pair.snd(P.H, F.Fz, F.fz.tpl(F.FzE{h, map, nodes, eras, ne, ls, root, curs}, n0))), dm) == True{} : Bool}

# LAW: the template's placeholders (cursor-laws.materializer.template.compose.holes):
# the template the write phase's record makes (F.fz.tpl) has its crossings'
# placeholders in slots apart, each a node, named by a link at its port 0,
# every link end at a placeholder's slot its port 0 from a node read back
# in no placeholder's slot (SV.copy.ok): given the record's links so
# (FM.inv.k's near ends and each era's index linked from a node read back,
# emits_links; FM.lks.far, emits_far), the crossings the placeholders'
# (FM.inv.f, emits_counts), each era an eraser exactly where no
# placeholder (FM.eras.ok, emits_root), the nodes read back n0 and no
# eraser, all within 2^dm, the map's depth. Not claimed: that the record
# is so after the walk (.tree's).
# Record: copy-reduced-function-nets
# Record: cursors-indexed
law tpl_holes:
  for h: P.H
  for map: Array<U32>
  for +nodes: List<&2, T.TNode>
  for +eras: List<&2, T.TNode>
  for +ne: U32
  for +ls: List<&2, T.TLink>
  for +root: T.TEnd
  for +curs: List<&2, RN.FzC>
  for +n0: U32
  for +dm: Nat
  for +hn0: {U32.to_nat(n0) == List.length(&2, T.TNode, nodes) : Nat}
  for +hne: {FM.no_era(nodes) == True{} : Bool}
  for +hk: {FM.inv.k(ls, eras, n0) == True{} : Bool}
  for +hj: {FM.lks.far(ls, eras, n0) == True{} : Bool}
  for +hf: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}
  for +hok: {FM.eras.ok(eras) == True{} : Bool}
  for +hb: {Nat.is_le(Nat.add(U32.to_nat(n0), List.length(&2, T.TNode, eras)), Nat.pow(2n, dm)) == True{} : Bool}
  for +hd32: {Nat.is_lt(dm, 32n) == True{} : Bool}
  {SV.copy.ok(FM.fz.curs(Pair.snd(P.H, F.Fz, F.fz.tpl(F.FzE{h, map, nodes, eras, ne, ls, root, curs}, n0))), FM.fz.links(Pair.snd(P.H, F.Fz, F.fz.tpl(F.FzE{h, map, nodes, eras, ne, ls, root, curs}, n0))), FM.fz.tnodes(Pair.snd(P.H, F.Fz, F.fz.tpl(F.FzE{h, map, nodes, eras, ne, ls, root, curs}, n0))), dm) == True{} : Bool}

# LAW: the template a record meeting the write phase's invariants makes
# (cursor-laws.materializer.template.compose.tree.record): F.fz.tpl's
# template meets all the serve asks of a copy's (SV.root.ok, SM.tpl.ok,
# SV.copy.ok, its crossings at distinct positions), given the record's
# invariants as the write phase's laws keep them (FM.inv, FM.inv.l,
# FM.inv.j, FM.inv.r, FM.inv.n; emits_counts to emits_pos), its nodes read
# back n0, all within 2^dm, the map's depth: tpl_root, tpl_links,
# tpl_holes and tpl_pos over any record. Not claimed: that the walk's
# record is such (.tree.walk's).
# Record: copy-reduced-function-nets
# Record: cursors-indexed
law tpl_ok:
  for z: F.FzE
  for +n0: U32
  for +dm: Nat
  for +hn0: {U32.to_nat(n0) == List.length(&2, T.TNode, FM.nodes.of(z)) : Nat}
  for +hf: {FM.inv(z, n0) == True{} : Bool}
  for +hk: {FM.inv.l(z, n0) == True{} : Bool}
  for +hj: {FM.inv.j(z, n0) == True{} : Bool}
  for +hr: {FM.inv.r(z, n0) == True{} : Bool}
  for +hne: {FM.inv.n(z) == True{} : Bool}
  for +hs: {RG.distinct(RG.srcs(FM.curs.of(z))) == True{} : Bool}
  for +hb: {Nat.is_le(Nat.add(U32.to_nat(n0), List.length(&2, T.TNode, FM.eras.of(z))), Nat.pow(2n, dm)) == True{} : Bool}
  for +hd32: {Nat.is_lt(dm, 32n) == True{} : Bool}
  {SV.root.ok(FM.fz.rn(Pair.snd(P.H, F.Fz, F.fz.tpl(z, n0))), FM.fz.rp(Pair.snd(P.H, F.Fz, F.fz.tpl(z, n0))), FM.fz.tnodes(Pair.snd(P.H, F.Fz, F.fz.tpl(z, n0))), dm, FM.fz.curs(Pair.snd(P.H, F.Fz, F.fz.tpl(z, n0)))) && (SM.tpl.ok(FM.fz.links(Pair.snd(P.H, F.Fz, F.fz.tpl(z, n0))), FM.fz.tnodes(Pair.snd(P.H, F.Fz, F.fz.tpl(z, n0))), dm) && (SV.copy.ok(FM.fz.curs(Pair.snd(P.H, F.Fz, F.fz.tpl(z, n0))), FM.fz.links(Pair.snd(P.H, F.Fz, F.fz.tpl(z, n0))), FM.fz.tnodes(Pair.snd(P.H, F.Fz, F.fz.tpl(z, n0))), dm) && RG.distinct(RG.srcs(FM.fz.curs(Pair.snd(P.H, F.Fz, F.fz.tpl(z, n0))))))) == True{} : Bool}
