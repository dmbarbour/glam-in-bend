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

# LAW: unlinking a cursor x from its ring writes one word alone: word 3
# of the node the ring's walk finds before x (R.rg.pred), given x's next;
# every other word reads as before (cells-freeze.nested.host.join). Not
# claimed: that the node found is x's predecessor, a member of its ring,
# which a model of rings would show; so that its word 3 is no word a
# walk's path reads.
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law unlink_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +x: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hj: {Nat.is_eq(AD.slot((Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{w}, a}, x)) + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(R.rg.unlink(P.H{KM.MG{w}, a}, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: the node the ring's walk finds before a member x, the one whose
# word 3 unlinking writes (unlink_keeps), is a member of x's ring, the
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

# LAW: unlinking a member x of a closed ring leaves it closed: the one
# word written, the found node's word 3 (unlink_keeps, a member,
# pred_in_ring), given x's next, itself a member (cells-freeze.nested.
# host.ring). The member list is the same: x stays listed, its own word
# 3 a member still.
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law unlink_closed:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +x: U32
  for +xs: List<&2, U32>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hc: {RG.closed(AD.view(U32, w), d, xs) == True{} : Bool}
  for hx: {RG.has(xs, x) == True{} : Bool}
  {RG.closed(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{w}, a}, x))), d, xs) == True{} : Bool}

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


# LAW: a join of two members x and y of a closed ring, each a node's
# base, writes no word but the members' word 3, x's and y's own four
# words, the free list's head and the link words of the two ports x and
# y faced (each one's word 1 holds the port it faces): every other word
# reads as before, the other members' words 0 to 2 among them, which the
# serve's next finds and joins read (cells-freeze.nested.host.join;
# docs/reviews/JoinLaws_2026-11-14.md, F1). Premises not yet derived: the
# ports' link words are no member's word 3 (off.links), so that the link
# leaves the ring closed for the two walks that follow; and x and y node
# bases (P.base). Not claimed: which members' word 3 are written, nor
# that the ring left is a cycle without x and y.
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law join_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +x: U32
  for +y: U32
  for +xs: List<&2, U32>
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hc: {RG.closed(AD.view(U32, w), d, xs) == True{} : Bool}
  for hx: {RG.has(xs, x) == True{} : Bool}
  for hy: {RG.has(xs, y) == True{} : Bool}
  for hbx: {P.base(x) == x : U32}
  for hby: {P.base(y) == y : U32}
  for hu: {RG.off.links(xs, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}
  for hw: {RG.off.links(xs, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32)) == True{} : Bool}
  for hj: {RG.off.links(xs, d, j) == True{} : Bool}
  for hjx: {RG.off.node(d, x, j) == True{} : Bool}
  for hjy: {RG.off.node(d, y, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  for hju: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}
  for hjw: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(R.join(P.H{KM.MG{w}, a}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: and a join of a placeholder x, in no ring (or in it: x's words
# are allowed either way), with a member y of a closed ring writes no
# word but the members' word 3, x's and y's own four words, the free
# list's head and the two faced ports' link words
# (cells-freeze.nested.host.join), on the same premises.
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law join1_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +x: U32
  for +y: U32
  for +xs: List<&2, U32>
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hc: {RG.closed(AD.view(U32, w), d, xs) == True{} : Bool}
  for hy: {RG.has(xs, y) == True{} : Bool}
  for hbx: {P.base(x) == x : U32}
  for hby: {P.base(y) == y : U32}
  for hu: {RG.off.links(xs, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}
  for hw: {RG.off.links(xs, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32)) == True{} : Bool}
  for hj: {RG.off.links(xs, d, j) == True{} : Bool}
  for hjx: {RG.off.node(d, x, j) == True{} : Bool}
  for hjy: {RG.off.node(d, y, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  for hju: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}
  for hjw: {Nat.is_eq(AD.slot((Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(R.join1(P.H{KM.MG{w}, a}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: in an exact ring (glam/ring_model.bend's ring: the situating
# node s, then its cursors in walk order, each one's word 3 the next,
# the last's s, no two word 3 in one slot), the node the walk finds
# before a cursor x is the one listed before it: the last of s and the
# cursors before x (cells-freeze.nested.host.ring.exact). The ring has
# fewer cursors than the heap has words, the walk's fuel
# (ring-walks-fueled-by-heap); a pigeonhole over the members' distinct
# word-3 slots will make that a theorem.
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law pred_exact:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +pre: List<&2, U32>
  for +x: U32
  for +post: List<&2, U32>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pre, Con{x, post})) == True{} : Bool}
  for hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pre, Con{x, post})), U32.to_nat(U32.shln(1, d))) == True{} : Bool}
  {Pair.snd(P.H, U32, R.rg.pred(P.H{KM.MG{w}, a}, x)) == RG.last(pre, s) : U32}

# LAW: unlinking a cursor x of an exact ring leaves the ring exact
# without it: the one listed before x now links the one after
# (cells-freeze.nested.host.ring.exact).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law unlink_exact:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +pre: List<&2, U32>
  for +x: U32
  for +post: List<&2, U32>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pre, Con{x, post})) == True{} : Bool}
  for hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pre, Con{x, post})), U32.to_nat(U32.shln(1, d))) == True{} : Bool}
  {RG.ring(AD.view(U32, RG.words(R.rg.unlink(P.H{KM.MG{w}, a}, x))), d, s, List.append(&2, U32, pre, post)) == True{} : Bool}

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

# LAW: a join of two cursors x and y of an exact ring leaves the ring
# exact without both: listed as pa, x, pb, and pa, pb as pc, y, pd, the
# ring after the join is pc, pd (cells-freeze.nested.host.ring.exact).
# Premises not yet derived, each of the nodes' forms and bases: the two
# faced ports' link words are no member's word 3; nor are the words the
# frees write, x's and y's words 0 and 1 and the head, any remaining
# member's; and x and y node bases.
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
law join_exact:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +pa: List<&2, U32>
  for +x: U32
  for +pb: List<&2, U32>
  for +pc: List<&2, U32>
  for +y: U32
  for +pd: List<&2, U32>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {RG.ring(AD.view(U32, w), d, s, List.append(&2, U32, pa, Con{x, pb})) == True{} : Bool}
  for hsp: {List.append(&2, U32, pa, pb) == List.append(&2, U32, pc, Con{y, pd}) : List<&2, U32>}
  for hn: {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, pa, Con{x, pb})), U32.to_nat(U32.shln(1, d))) == True{} : Bool}
  for hbx: {P.base(x) == x : U32}
  for hby: {P.base(y) == y : U32}
  for hu: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{x, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (x + 1 : U32))) + 1 : U32)) == True{} : Bool}
  for hw: {RG.off.links(Con{s, List.append(&2, U32, pa, Con{x, pb})}, d, (Pair.snd(Array<U32>, U32, Array.get(U32, w, (y + 1 : U32))) + 1 : U32)) == True{} : Bool}
  for hx0: {RG.off.links(Con{s, List.append(&2, U32, pc, pd)}, d, x) == True{} : Bool}
  for hx1: {RG.off.links(Con{s, List.append(&2, U32, pc, pd)}, d, (x + 1 : U32)) == True{} : Bool}
  for hy0: {RG.off.links(Con{s, List.append(&2, U32, pc, pd)}, d, y) == True{} : Bool}
  for hy1: {RG.off.links(Con{s, List.append(&2, U32, pc, pd)}, d, (y + 1 : U32)) == True{} : Bool}
  for hh: {RG.off.links(Con{s, List.append(&2, U32, pc, pd)}, d, P.at_fh()) == True{} : Bool}
  {RG.ring(AD.view(U32, RG.words(R.join(P.H{KM.MG{w}, a}, x, y))), d, s, List.append(&2, U32, pc, pd)) == True{} : Bool}
