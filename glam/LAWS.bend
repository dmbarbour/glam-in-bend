# glam's laws over its own modules, proved in glam/PROOF.bend, beside the
# evaluator spike's (spike/LAWS.bend), whose laws of the kernel's heap
# they build on. As there, a heap is stated by its parts, its words w and
# its value table a, the words a perfect tree of depth d below 32
# (lawful-arrays, hub-laws-reused).

import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ./ring.bend as R
import ./ring_model.bend as RG
import ../spike/kmodel.bend as KMd
import ./index_model.bend as IM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: two cursors x and y of the index joined (R.join), on join_pend's
# premises, leave every word as it was but the tracked nodes' (N: the
# live nodes, the index's, the free list's), the free list's head, and
# the link words of the two ports x and y faced, a static having none:
# the join's frame, for the materializer's frontier, which joins two
# cursors directly (cells-freeze.sharing.cursors.index.ring.retire).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
# Record: cursors-indexed
law join_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +ps: List<&2, U32>
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +x: U32
  for +y: U32
  for +kx: U32
  for +ky: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, ps, L, F, N) == True{} : Bool}
  for hx: {IM.ix.look(I, kx) == Some{x} : Maybe<&2, U32>}
  for hy: {IM.ix.look(I, ky) == Some{y} : Maybe<&2, U32>}
  for hxy: {U32.is_eq(x, y) == False{} : Bool}
  for hj: {RG.off.nodes(N, d, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  for hju: {KMd.off.port(d, KMd.word(AD.view(U32, w), d, (x + 1 : U32)), j) == True{} : Bool}
  for hjw: {KMd.off.port(d, KMd.word(AD.view(U32, w), d, (y + 1 : U32)), j) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(R.join(P.H{KM.MG{w}, a}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: a placeholder x made a cursor (R.cursor), on cursor_pend's
# premises, holds its header, a cursor's kind (18) and form (0 negative,
# 1 positive), at word 0 after the insert into the index
# (cells-freeze.sharing.cursors.index.ring.retire: no other law sees a
# cursor's form).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
# Record: cursors-indexed
law cursor_head:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +ps: List<&2, U32>
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +x: U32
  for +src: U32
  for +neg: Bool
  for +b: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, Con{x, ps}, L, IM.ix.take(I, b, F), N) == True{} : Bool}
  for ha: {IM.ix.look(I, src) == None{} : Maybe<&2, U32>}
  {Pair.snd(P.H, U32, P.rd(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg), x)) == P.hd2(18, R.cur.form(neg), 0) : U32}

# LAW: the serve's first pending placeholder x made a cursor keeps the
# pending placeholders' invariant over the index (RG.px.ok) and the words
# full, what the next step asks (IndexPremises P1): x put in the index at its position src, absent from it (one cursor a position), the
# put's branch, in a tree, the free list's first node b (the list's first
# nodes IM.ix.take(I, b, F) before, F after); every node a serve touches
# in N, laid out apart, each its own base
# (cells-freeze.sharing.cursors.index.ring.inv).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
# Record: cursors-indexed
# Record: copy-links-two-way
law cursor_pend:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +ps: List<&2, U32>
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +x: U32
  for +src: U32
  for +neg: Bool
  for +b: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, Con{x, ps}, L, IM.ix.take(I, b, F), N) == True{} : Bool}
  for ha: {IM.ix.look(I, src) == None{} : Maybe<&2, U32>}
  {RG.px.ok(AD.view(U32, RG.words(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg))), d, s, IM.ix.put(I, x, src, b), ps, L, F, N) && AD.full(U32, RG.words(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg)), d) == True{} : Bool}

# LAW: the serve's first pending placeholder x joined to the cursor y a
# find at key k gives (R.join1: the ports they faced linked, y taken out
# of the index, both freed) keeps the pending placeholders' invariant
# over the index (RG.px.ok) and the words full: the index without y, the live nodes without
# x and y, the free list's first nodes y, x, the parent the removal frees
# if any, then the nodes before (cells-freeze.sharing.cursors.index.ring.inv).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
# Record: cursors-indexed
# Record: copy-links-two-way
law join1_pend:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +ps: List<&2, U32>
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +x: U32
  for +y: U32
  for +k: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, Con{x, ps}, L, F, N) == True{} : Bool}
  for hy: {IM.ix.look(I, k) == Some{y} : Maybe<&2, U32>}
  {RG.px.ok(AD.view(U32, RG.words(R.join1(P.H{KM.MG{w}, a}, x, y))), d, s, IM.ix.del(I, y, k), ps, RG.without(RG.without(L, x), y), Con{y, Con{x, IM.mb.cons(IM.ix.par(I, y, k), F)}}, N) && AD.full(U32, RG.words(R.join1(P.H{KM.MG{w}, a}, x, y)), d) == True{} : Bool}

# LAW: a crossing of the serve (R.cross), its placeholder x the first
# pending, keeps the pending placeholders' invariant over the index
# (RG.px.ok) and the words full: x joined to the cursor a find at its far end gives, if
# any, else made a cursor at its position src, absent from the index
# (RG.cx.I, RG.cx.L, RG.cx.F0, RG.cx.F1, RG.cx.ab, by the index's
# lookup) (cells-freeze.sharing.cursors.index.ring.inv).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
# Record: cursors-indexed
# Record: serve-premises-over-index
law cross_pend:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +ps: List<&2, U32>
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +x: U32
  for +src: U32
  for +neg: Bool
  for +far: U32
  for +b: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, Con{x, ps}, L, RG.cx.F0(IM.ix.look(I, far), I, b, F), N) == True{} : Bool}
  for ha: {RG.cx.ab(IM.ix.look(I, far), I, src) == True{} : Bool}
  {RG.px.ok(AD.view(U32, RG.words(R.cross(P.H{KM.MG{w}, a}, s, x, src, neg, far))), d, s, RG.cx.I(IM.ix.look(I, far), I, x, src, b, far), ps, RG.cx.L(IM.ix.look(I, far), x, L), RG.cx.F1(IM.ix.look(I, far), I, x, far, F), N) && AD.full(U32, RG.words(R.cross(P.H{KM.MG{w}, a}, s, x, src, neg, far)), d) == True{} : Bool}

# LAW: a copy's crossings (R.crossings, each placeholder found through
# map), their placeholders the pending ones (RG.pls), keep the pending
# placeholders' invariant over the index (RG.px.ok) and the words full,
# none pending after:
# the index, the live nodes and the free list's first nodes as the model
# gives them (RG.cxs: each find the index's lookup, a cursor made in a
# tree taking the list's first node), on each crossing's premises in
# turn (RG.cxs.ok: its position absent where it makes a cursor, room for
# the branch it takes) (cells-freeze.sharing.cursors.index.ring.fold).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
# Record: cursors-indexed
# Record: serve-premises-over-index
law crossings_pend:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for +dm: Nat
  for +s: U32
  for +I: IM.Ix
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +cs: List<&2, R.FzC>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, RG.pls(cs, AD.view(U32, map), dm), L, F, N) == True{} : Bool}
  for hok: {RG.cxs.ok(cs, AD.view(U32, map), dm, I, F) == True{} : Bool}
  {RG.px.ok(AD.view(U32, RG.words(Pair.snd(Array<U32>, P.H, R.crossings(cs, (map, P.H{KM.MG{w}, a}), s)))), d, s, RG.cxs.I(RG.cxs(cs, AD.view(U32, map), dm, I, L, F)), Nil{}, RG.cxs.L(RG.cxs(cs, AD.view(U32, map), dm, I, L, F)), RG.cxs.F(RG.cxs(cs, AD.view(U32, map), dm, I, L, F)), N) && AD.full(U32, RG.words(Pair.snd(Array<U32>, P.H, R.crossings(cs, (map, P.H{KM.MG{w}, a}), s))), d) == True{} : Bool}

# LAW: and a copy's crossings, on crossings_pend's premises, leave every
# word as it was but the tracked nodes' words (N: the live nodes, the
# index's, the free list's first nodes), the free list's head, and the
# link word of each port a node of L faced at the start (RG.faced),
# static ports having none: the crossings' writes by region, what the
# demand's walk resumed reads; a join moving a faced port from one node
# to another, the ports the live nodes face kept among the first ones
# (cells-freeze.sharing.cursors.index.ring.fold).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
# Record: cursors-indexed
# Record: serve-premises-over-index
law crossings_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for +dm: Nat
  for +s: U32
  for +I: IM.Ix
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +cs: List<&2, R.FzC>
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, RG.pls(cs, AD.view(U32, map), dm), L, F, N) == True{} : Bool}
  for hok: {RG.cxs.ok(cs, AD.view(U32, map), dm, I, F) == True{} : Bool}
  for hj: {RG.off.nodes(N, d, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  for hjf: {RG.off.ports(RG.faced(L, AD.view(U32, w), d), d, j) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(Pair.snd(Array<U32>, P.H, R.crossings(cs, (map, P.H{KM.MG{w}, a}), s)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: a cursor c the index finds at k leaving (R.leave), a port p linked in
# its place (its link word off every tracked node's words and the free
# list's head, RG.po.all over no live node, and faceable by the live
# nodes: the copy's root port, or the eraser), keeps the pending
# placeholders' invariant over the index and the words full: c out of the index and of the
# live nodes, the free list's first nodes c and the parent the removal
# frees (cells-freeze.sharing.cursors.index.ring.leave).
# Record: copy-reduced-function-nets
# Record: cursors-indexed
# Record: copy-links-two-way
# Record: serve-premises-over-index
law leave_pend:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +ps: List<&2, U32>
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +p: U32
  for +c: U32
  for +k: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, ps, L, F, N) == True{} : Bool}
  for hc: {IM.ix.look(I, k) == Some{c} : Maybe<&2, U32>}
  for hpo: {RG.po.all(p, Nil{}, d, N) == True{} : Bool}
  for hpk: {RG.port.ok(L, d, p) == True{} : Bool}
  {RG.px.ok(AD.view(U32, RG.words(R.leave(P.H{KM.MG{w}, a}, p, c))), d, s, IM.ix.del(I, c, k), ps, RG.without(L, c), Con{c, IM.mb.cons(IM.ix.par(I, c, k), F)}, N) && AD.full(U32, RG.words(R.leave(P.H{KM.MG{w}, a}, p, c)), d) == True{} : Bool}

# LAW: two cursors x and y of the index joined (R.join: the ports they
# faced linked, x then y taken out of the index, both freed), two cursors
# apart found at kx and ky, keep the pending placeholders'
# invariant over the index and the words full: the index without x and y, the live nodes
# without x and y, the free list's first nodes y, x, the parents the
# removals free if any, then the nodes before
# (cells-freeze.sharing.cursors.index.ring.leave).
# Record: copy-reduced-function-nets
# Record: cursors-indexed
# Record: copy-links-two-way
# Record: serve-premises-over-index
law join_pend:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +ps: List<&2, U32>
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +x: U32
  for +y: U32
  for +kx: U32
  for +ky: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, ps, L, F, N) == True{} : Bool}
  for hx: {IM.ix.look(I, kx) == Some{x} : Maybe<&2, U32>}
  for hy: {IM.ix.look(I, ky) == Some{y} : Maybe<&2, U32>}
  for hxy: {U32.is_eq(x, y) == False{} : Bool}
  {RG.px.ok(AD.view(U32, RG.words(R.join(P.H{KM.MG{w}, a}, x, y))), d, s, IM.ix.del(IM.ix.del(I, x, kx), y, ky), ps, RG.without(RG.without(L, x), y), Con{y, Con{x, IM.mb.cons(IM.ix.par(IM.ix.del(I, x, kx), y, ky), IM.mb.cons(IM.ix.par(I, x, kx), F))}}, N) && AD.full(U32, RG.words(R.join(P.H{KM.MG{w}, a}, x, y)), d) == True{} : Bool}

# LAW: a cursor c the index finds at k leaving (R.leave), a port p linked
# in its place, on leave_pend's premises, leaves every word as it was but
# the tracked nodes' (N: the live nodes, the index's, the free list's),
# the free list's head, and the two ports' link words, p's and the one c
# faced, a static having none: the leave's frame
# (cells-freeze.sharing.cursors.index.ring.leave; the frame law leave
# lacked: .host.witness.audit).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
# Record: cursors-indexed
law leave_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +ps: List<&2, U32>
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +p: U32
  for +c: U32
  for +k: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, ps, L, F, N) == True{} : Bool}
  for hc: {IM.ix.look(I, k) == Some{c} : Maybe<&2, U32>}
  for hpo: {RG.po.all(p, Nil{}, d, N) == True{} : Bool}
  for hpk: {RG.port.ok(L, d, p) == True{} : Bool}
  for hj: {RG.off.nodes(N, d, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  for hjp: {KMd.off.port(d, p, j) == True{} : Bool}
  for hjw: {KMd.off.port(d, KMd.word(AD.view(U32, w), d, (c + 1 : U32)), j) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(R.leave(P.H{KM.MG{w}, a}, p, c), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}
