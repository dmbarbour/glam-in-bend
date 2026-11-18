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
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: the node the ring's walk finds before a member x, the one whose
# word 3 an unlink writes, is a member of x's ring, the
# ring closed on the heap's words (glam/ring_model.bend), whatever fuel the
# walk stops with (cells-freeze.nested.host.ring).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law pred_in_ring:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +x: U32
  for +xs: List<&2, U32>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hc: {RG.closed(AD.view(U32, w), d, xs) == True{} : Bool}
  for hx: {RG.has(xs, x) == True{} : Bool}
  {RG.has(xs, Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{w}, a}, x))) == True{} : Bool}

# LAW: inserting a cursor x apart from a closed ring, after its member
# situ, leaves the ring with x added closed: x's word 3 given situ's
# next, a member, and situ's given x (cells-freeze.nested.host.ring).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law insert_closed:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +situ: U32
  for +x: U32
  for +xs: List<&2, U32>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hc: {RG.closed(AD.view(U32, w), d, xs) == True{} : Bool}
  for hs: {RG.has(xs, situ) == True{} : Bool}
  for hx: {RG.apart(xs, d, x) == True{} : Bool}
  {RG.closed(AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{w}, a}, situ, x))), d, Con{x, xs}) == True{} : Bool}


# LAW: a join of two distinct cursors x and y of a ring exact with its
# nodes (RG.ring.ok) writes no word but the members' word 3, x's and y's
# own four words, the free list's head and the link words of the two
# ports x and y faced (each one's word 1 holds the port it faces): every
# other word reads as before, the other members' words 0 to 2 among them,
# which the serve's next finds and joins read, and the kernel's error
# count, which no walk round an exact ring raises
# (cells-freeze.nested.host.join; docs/reviews/JoinLaws_2026-11-14.md,
# F1).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law join_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +x: U32
  for +y: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring.ok(AD.view(U32, w), d, s, t) == True{} : Bool}
  for hx: {RG.has(t, x) == True{} : Bool}
  for hy: {RG.has(t, y) == True{} : Bool}
  for hxy: {U32.is_eq(x, y) == False{} : Bool}
  for hj: {RG.off.links(Con{s, t}, d, j) == True{} : Bool}
  for hjx: {RG.off.node(d, x, j) == True{} : Bool}
  for hjy: {RG.off.node(d, y, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  for hju: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}
  for hjw: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(R.join(P.H{KM.MG{w}, a}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: and a join of a placeholder x, a node apart from the ring
# (RG.node.ok), with a cursor y of a ring exact with its nodes writes no
# word but the members' word 3, x's and y's own four words, the free
# list's head and the two faced ports' link words
# (cells-freeze.nested.host.join), on the same premises.
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law join1_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +x: U32
  for +y: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring.ok(AD.view(U32, w), d, s, t) == True{} : Bool}
  for hx: {RG.node.ok(AD.view(U32, w), d, Con{s, t}, x) == True{} : Bool}
  for hy: {RG.has(t, y) == True{} : Bool}
  for hj: {RG.off.links(Con{s, t}, d, j) == True{} : Bool}
  for hjx: {RG.off.node(d, x, j) == True{} : Bool}
  for hjy: {RG.off.node(d, y, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  for hju: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}
  for hjw: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(R.join1(P.H{KM.MG{w}, a}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: in an exact ring (glam/ring_model.bend's ring: the situating
# node s, then its cursors t in walk order, each one's word 3 the next,
# the last's s, no two word 3 in one slot), the node the walk finds
# before a cursor x is the one listed before it (RG.before)
# (cells-freeze.nested.host.ring.exact). The walk's fuel, the heap's
# words (ring-walks-fueled-by-heap), is enough: an exact ring's members'
# word 3 lie in distinct slots of them.
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law pred_exact:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +x: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring(AD.view(U32, w), d, s, t) == True{} : Bool}
  for hx: {RG.has(t, x) == True{} : Bool}
  {Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{w}, a}, x)) == RG.before(t, s, x) : U32}

# LAW: a find for position far on an exact ring hands the heap back, no
# error raised, and finds the first member in walk order whose word 2 is
# far, or none (RG.first) (cells-freeze.nested.host.serve).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law find_exact:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +far: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring(AD.view(U32, w), d, s, t) == True{} : Bool}
  {R.rg.find(P.H{KM.MG{w}, a}, s, far) == (P.H{KM.MG{w}, a}, RG.first(t, AD.view(U32, w), d, far)) : P.H & Maybe<&2, U32>}

# LAW: unlinking a cursor x of an exact ring leaves the ring exact
# without it (RG.without): the one listed before x now links the one
# after (cells-freeze.nested.host.ring.exact).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law unlink_exact:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +x: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring(AD.view(U32, w), d, s, t) == True{} : Bool}
  for hx: {RG.has(t, x) == True{} : Bool}
  {RG.ring(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{w}, a}, x))), d, s, RG.without(t, x)) == True{} : Bool}

# LAW: inserting a cursor x after the situating node s of an exact ring,
# x's word 3 in no member's slot, leaves the ring exact with x listed
# first (cells-freeze.nested.host.ring.exact).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law insert_exact:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +x: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring(AD.view(U32, w), d, s, t) == True{} : Bool}
  for hx: {RG.apart(Con{s, t}, d, x) == True{} : Bool}
  {RG.ring(AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{w}, a}, s, x))), d, s, Con{x, t}) == True{} : Bool}

# LAW: inserting a cursor x after the situating node s of a ring exact
# with its nodes, x ready to enter it (RG.enter.ok: its words apart from
# each other, the head's and the members', its own base, facing a port
# whose link word is no word 2 or 3 of the members' or its own, no
# member facing one whose link word is x's word 2 or 3), leaves the ring
# so with x listed first
# (cells-freeze.nested.host.serve).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law insert_ok:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +x: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring.ok(AD.view(U32, w), d, s, t) == True{} : Bool}
  for hx: {RG.enter.ok(AD.view(U32, w), d, s, t, x) == True{} : Bool}
  {RG.ring.ok(AD.view(U32, RG.words(R.rg.insert(P.H{KM.MG{w}, a}, s, x))), d, s, Con{x, t}) == True{} : Bool}

# LAW: a placeholder x made a cursor (R.cursor: its header and its
# position src written, then inserted after s) of a ring exact with its
# nodes, x ready to enter it, leaves the ring so with x listed first: the
# two words written, x's words 0 and 2, are no member's word 1 or 3 nor
# x's own (cells-freeze.nested.host.serve).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law cursor_ok:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +x: U32
  for +src: U32
  for +neg: Bool
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring.ok(AD.view(U32, w), d, s, t) == True{} : Bool}
  for hx: {RG.enter.ok(AD.view(U32, w), d, s, t, x) == True{} : Bool}
  {RG.ring.ok(AD.view(U32, RG.words(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg))), d, s, Con{x, t}) == True{} : Bool}

# LAW: a placeholder x made a cursor, x ready to enter the ring, holds
# its header, a cursor's kind (18) and form (0 negative, 1 positive), at word 0 (cells-freeze.nested.host.serve).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law cursor_head:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +x: U32
  for +src: U32
  for +neg: Bool
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hx: {RG.enter.ok(AD.view(U32, w), d, s, t, x) == True{} : Bool}
  {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg)), x)) == P.hd2(18, R.cur.form(neg), 0) : U32}

# LAW: a placeholder x made a cursor, x ready to enter the ring, holds
# its position src at word 2, where a find reads it (cells-freeze.nested.host.serve).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law cursor_pos:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +x: U32
  for +src: U32
  for +neg: Bool
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hx: {RG.enter.ok(AD.view(U32, w), d, s, t, x) == True{} : Bool}
  {Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg)), (x + 2 : U32))) == src : U32}

# LAW: a placeholder x made a cursor leaves every word as it was but its
# own node's and the situating node's word 3 (cells-freeze.nested.host.serve,
# the frame law beside join_keeps, join1_keeps and leave_keeps).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law cursor_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +x: U32
  for +src: U32
  for +neg: Bool
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hjx: {RG.off.node(d, x, j) == True{} : Bool}
  for hjs: {Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: the serve's first pending placeholder x made a cursor keeps the
# pending placeholders' invariant (RG.pend.ok: the ring exact, the rest
# pending outside it and none twice, every node of either in L, laid out
# apart, its own base, facing a port faceable by all of L), x now the
# ring's first cursor, L as it was (cells-freeze.nested.host.serve).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law cursor_pend:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +ps: List<&2, U32>
  for +L: List<&2, U32>
  for +x: U32
  for +src: U32
  for +neg: Bool
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hp: {RG.pend.ok(AD.view(U32, w), d, s, t, Con{x, ps}, L) == True{} : Bool}
  {RG.pend.ok(AD.view(U32, RG.words(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg))), d, s, Con{x, t}, ps, L) == True{} : Bool}

# LAW: the serve's first pending placeholder x joined to a cursor y of
# the ring keeps the pending placeholders' invariant (RG.pend.ok), y out
# of the ring and both out of L (cells-freeze.nested.host.serve).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law join1_pend:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +ps: List<&2, U32>
  for +L: List<&2, U32>
  for +x: U32
  for +y: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hp: {RG.pend.ok(AD.view(U32, w), d, s, t, Con{x, ps}, L) == True{} : Bool}
  for hy: {RG.has(t, y) == True{} : Bool}
  {RG.pend.ok(AD.view(U32, RG.words(R.join1(P.H{KM.MG{w}, a}, x, y))), d, s, RG.without(t, y), ps, RG.without(RG.without(L, x), y)) == True{} : Bool}

# LAW: a crossing of the serve (R.cross), its placeholder x the first
# pending, keeps the pending placeholders' invariant: x joined to the
# cursor found at its far position, if any, both then out of the ring and
# of L; else x made a cursor (RG.cross.t, RG.cross.L, by the find's model,
# RG.first) (cells-freeze.nested.host.serve).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law cross_pend:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +ps: List<&2, U32>
  for +L: List<&2, U32>
  for +x: U32
  for +src: U32
  for +neg: Bool
  for +far: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hp: {RG.pend.ok(AD.view(U32, w), d, s, t, Con{x, ps}, L) == True{} : Bool}
  {RG.pend.ok(AD.view(U32, RG.words(R.cross(P.H{KM.MG{w}, a}, s, x, src, neg, far))), d, s, RG.cross.t(RG.first(t, AD.view(U32, w), d, far), x, t), ps, RG.cross.L(RG.first(t, AD.view(U32, w), d, far), x, L)) == True{} : Bool}

# LAW: a copy's crossings (R.crossings, each placeholder found through
# map), their placeholders the pending ones (RG.pls), keep the pending
# placeholders' invariant, none pending after: the ring and the nodes'
# list as the model gives them (RG.cr), each find modelled over a view of
# the positions, a new cursor's word 2 its position, so that the model
# shares none of the code's finds (cells-freeze.nested.host.serve).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law crossings_pend:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for +dm: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +L: List<&2, U32>
  for +cs: List<&2, R.FzC>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for hp: {RG.pend.ok(AD.view(U32, w), d, s, t, RG.pls(cs, AD.view(U32, map), dm), L) == True{} : Bool}
  {RG.pend.ok(AD.view(U32, RG.words(Pair.snd(Array<U32>, P.H, R.crossings(cs, (map, P.H{KM.MG{w}, a}), s)))), d, s, Pair.fst(List<&2, U32>, List<&2, U32>, RG.cr(cs, AD.view(U32, map), dm, AD.view(U32, w), d, t, L)), Nil{}, Pair.snd(List<&2, U32>, List<&2, U32>, RG.cr(cs, AD.view(U32, map), dm, AD.view(U32, w), d, t, L))) == True{} : Bool}

# LAW: and a copy's crossings leave every word as it was but the words
# of the nodes of L, the free list's head, and the link word of each port
# a node of L faced at the start (RG.faced): the crossings' writes by
# region, what the demand's walk resumed reads (cells-freeze.nested.host.serve).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law crossings_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for +dm: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +L: List<&2, U32>
  for +cs: List<&2, R.FzC>
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hfm: {AD.full(U32, map, dm) == True{} : Bool}
  for hdm: {Nat.is_lt(dm, 32n) == True{} : Bool}
  for hp: {RG.pend.ok(AD.view(U32, w), d, s, t, RG.pls(cs, AD.view(U32, map), dm), L) == True{} : Bool}
  for hj: {RG.off.nodes(L, d, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  for hjf: {RG.off.ports(RG.faced(L, AD.view(U32, w), d), d, j) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(Pair.snd(Array<U32>, P.H, R.crossings(cs, (map, P.H{KM.MG{w}, a}), s)), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: a join of two distinct cursors x and y of a ring exact with its
# nodes (RG.ring.ok: the ring exact, its nodes laid out apart, no two
# sharing a word's slot nor any on the head's, each member a base, each
# facing a port whose link word is no member's word 2 nor 3, so that
# linking it leaves the ring's positions and links) leaves it so without
# both (cells-freeze.nested.host.ring.exact).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law join_exact:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +x: U32
  for +y: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring.ok(AD.view(U32, w), d, s, t) == True{} : Bool}
  for hx: {RG.has(t, x) == True{} : Bool}
  for hy: {RG.has(t, y) == True{} : Bool}
  for hxy: {U32.is_eq(x, y) == False{} : Bool}
  {RG.ring.ok(AD.view(U32, RG.words(R.join(P.H{KM.MG{w}, a}, x, y))), d, s, RG.without(RG.without(t, x), y)) == True{} : Bool}
# LAW: a join of a placeholder x, a node apart from the ring
# (RG.node.ok), with a cursor y of a ring exact with its nodes
# (RG.ring.ok) leaves it so without y (cells-freeze.nested.host.ring.exact).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law join1_exact:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +x: U32
  for +y: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring.ok(AD.view(U32, w), d, s, t) == True{} : Bool}
  for hx: {RG.node.ok(AD.view(U32, w), d, Con{s, t}, x) == True{} : Bool}
  for hy: {RG.has(t, y) == True{} : Bool}
  {RG.ring.ok(AD.view(U32, RG.words(R.join1(P.H{KM.MG{w}, a}, x, y))), d, s, RG.without(t, y)) == True{} : Bool}

# LAW: a cursor c of a ring exact with its nodes leaving it, the port it
# faced linked to a port p faceable by the ring's members (RG.port.ok,
# its link word no member's word 2 nor 3: a copied node's port, or the
# static eraser, whose link word is the head's), leaves the ring so
# without c (cells-freeze.nested.host.ring.exact).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law leave_exact:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +p: U32
  for +c: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring.ok(AD.view(U32, w), d, s, t) == True{} : Bool}
  for hc: {RG.has(t, c) == True{} : Bool}
  for hp: {RG.port.ok(Con{s, t}, d, p) == True{} : Bool}
  {RG.ring.ok(AD.view(U32, RG.words(R.leave(P.H{KM.MG{w}, a}, p, c))), d, s, RG.without(t, c)) == True{} : Bool}
# LAW: a cursor c of a ring exact with its nodes leaving it, the port it
# faced linked to a port p faceable by the ring's members, leaves every
# word as it was but the ring's links (the word 3 its predecessor gets),
# c's own node, the free list's head, and the two ports' link words, p's
# and the one c faced (cells-freeze.nested.host.serve, the frame law
# leave lacked: .host.witness.audit).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law leave_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +t: List<&2, U32>
  for +p: U32
  for +c: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring.ok(AD.view(U32, w), d, s, t) == True{} : Bool}
  for hc: {RG.has(t, c) == True{} : Bool}
  for hp: {RG.port.ok(Con{s, t}, d, p) == True{} : Bool}
  for hj: {RG.off.links(Con{s, t}, d, j) == True{} : Bool}
  for hjc: {RG.off.node(d, c, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  for hjp: {Nat.is_eq(AD.slot((p + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}
  for hjw: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (c + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(R.leave(P.H{KM.MG{w}, a}, p, c), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

