# Laws of glam/freeze.bend's write phase (the CursorLaws plan's
# cursor-laws.materializer.template.emit), stated over
# glam/freeze_model.bend; proved in glam/FREEZE_PROOF.bend.

import Base
import ../spike/kprim.bend as P
import ../spike/tpl.bend as T
import ./ring.bend as RN
import ./freeze.bend as F
import ./freeze_model.bend as FM
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
