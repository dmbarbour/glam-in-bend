# A copy's index's laws (glam/index.bend; the Cells plan's
# cells-freeze.sharing.cursors.index.laws): the tree's operations on the
# heap's words against its model (glam/index_model.bend), and the model's
# own. Apart from glam/LAWS.bend, the ring's, so that a change to either
# reruns its own proofs alone. As there, a heap is stated by its parts,
# its words w and its value table a, the words a perfect tree of depth d
# below 32 (lawful-arrays, hub-laws-reused).

import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/kmodel.bend as KMd
import ./index.bend as X
import ./index_model.bend as IM
import ./ring_model.bend as RG
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: two keys unequal, the scan of their 32 bits from the lowest
# (X.ix.diff) stops, at a bit they differ at, so that an insert of a key
# absent from a tree finds the bit its new branch tests and raises no
# error: a U32 is its 32 bits.
# Record: cursors-indexed
# Record: hub-laws-reused
law ne_found:
  for +a: U32
  for +b: U32
  for hne: {U32.is_eq(a, b) == False{} : Bool}
  {IM.cr.go(X.ix.diff(a, b)) == False{} : Bool}

# LAW: a tree's descent for key k (the model's look, as the code's find
# goes) hands back the leaf at k, if any (IM.tr.at, a search of every
# leaf): every key below a branch on the side its bit gives, so that no
# leaf off the descent's way holds k.
# Record: cursors-indexed
law look_at:
  for +I: IM.Ix
  for +k: U32
  for hi: {IM.ix.inv(I) == True{} : Bool}
  {IM.ix.look(I, k) == IM.ix.at(I, k) : Maybe<&2, U32>}

# LAW: a find for key k in the index of situating node s, the heap's
# words realizing the model I (IM.ix.real) on its invariant, hands the
# heap back, no error raised, and gives the model's look: the cursor at
# k, if any (look_at). The descent's fuel, 33, is enough: bits rise from
# the root, each below 32.
# Record: cursors-indexed
# Record: hub-laws-reused
law find_tree:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +k: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  {X.ix.find(P.H{KM.MG{w}, a}, s, k) == (P.H{KM.MG{w}, a}, IM.ix.look(I, k)) : P.H & Maybe<&2, U32>}

# LAW: removing cursor x, the leaf at key k (IM.ix.look), from the index
# of situating node s, the heap's words realizing the model I on its
# invariant and its nodes laid out apart (IM.ix.lay), leaves the words
# realizing the model without x (IM.ix.del): x's parent, if any, given
# up for x's sibling, the pointer to it rewritten and the parent freed
# (IM.tr.cutat); where x was the tree, the index empty. That the parent
# is freed (the free list's head after), which the realization does not
# read, is remove_free's.
# Record: cursors-indexed
# Record: hub-laws-reused
law remove_tree:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}
  {IM.ix.real(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{w}, a}, s, x))), d, s, IM.ix.del(I, x, k)) == True{} : Bool}

# LAW: inserting cursor x, its key k written at its word 2 and its
# header a leaf's, into the index of situating node s, the heap's words
# realizing the model I on its invariant and laid out apart, k absent
# from it, x and the free list's first node b fresh (IM.ix.fresh,
# IM.ix.room), leaves the words realizing the model with x put
# (IM.ix.put): in an empty index, x alone; else a branch at b, of the
# lowest bit k and the key its descent meets differ at, above the first
# node on k's way not a branch of a bit below it. Not claimed: growth,
# the free list empty with a tree to put into (the splice's precedent).
# Record: cursors-indexed
# Record: hub-laws-reused
law insert_tree:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +b: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}
  for hm: {IM.ix.room(I, AD.view(U32, w), d, b) == True{} : Bool}
  for hk: {KMd.word(AD.view(U32, w), d, (x + 2 : U32)) == k : U32}
  for hb: {X.ix.branch(KMd.word(AD.view(U32, w), d, x)) == False{} : Bool}
  for ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}
  {IM.ix.real(AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{w}, a}, s, x))), d, s, IM.ix.put(I, x, k, b)) == True{} : Bool}

# LAW: one cursor a position (cursors-indexed): an insert meeting its own
# key, a cursor x whose position k the index already holds (y found
# there), puts nothing; it counts one kernel error and writes no other
# word, the heap otherwise as it was (P.err_if, whose frame is
# spike/HEAP_LAWS.bend's), so that the run stops at the serve's end
# (implementation-errors-stop). Of the insert's two refusals the leaf's
# key compared equal (ix.put.n) is this one; the scan finding no
# differing bit (ix.put.c) follows only equal keys (ne_found), and is
# not reached past it.
# Record: cursors-indexed
# Record: implementation-errors-stop
law insert_dup:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +y: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hk: {KMd.word(AD.view(U32, w), d, (x + 2 : U32)) == k : U32}
  for hy: {IM.ix.look(I, k) == Some{y} : Maybe<&2, U32>}
  {X.ix.insert(P.H{KM.MG{w}, a}, s, x) == P.err_if(True{}, P.H{KM.MG{w}, a}) : P.H}

# LAW: and a removal, on remove_tree's premises, writes no word but the
# situating node's word 3, the branches' words and the free list's head
# (the pointer to the parent rewritten, the parent freed): every other
# word reads as before, every cursor's words among them, which a serve's
# next finds and joins read, and the kernel's error count, which no
# removal on these premises raises.
# Record: cursors-indexed
# Record: hub-laws-reused
law remove_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}
  for hj: {IM.ix.offb(I, s, d, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(X.ix.remove(P.H{KM.MG{w}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: and an insert, on insert_tree's premises, writes no word but the
# situating node's word 3, the branches' words, the free list's head,
# the words of the node it takes for its branch, if any, and the new
# cursor's word 3: every other word reads as before, the cursors' words
# and the error count among them.
# Record: cursors-indexed
# Record: hub-laws-reused
law insert_keeps:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +b: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}
  for hm: {IM.ix.room(I, AD.view(U32, w), d, b) == True{} : Bool}
  for hk: {KMd.word(AD.view(U32, w), d, (x + 2 : U32)) == k : U32}
  for hb: {X.ix.branch(KMd.word(AD.view(U32, w), d, x)) == False{} : Bool}
  for ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}
  for hj: {IM.ix.offb(I, s, d, j) == True{} : Bool}
  for hjb: {IM.ix.newb(I, b, d, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  for hjx: {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}
  {Pair.snd(P.H, U32, P.rd(X.ix.insert(P.H{KM.MG{w}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}

# LAW: a put of a key absent from an index on its invariant leaves the
# invariant: the new branch's bit, the lowest the key and the key its
# descent meets differ at, below 32 and between its parent's and the
# bit of the node it goes above; every key below each branch alike below
# its bit and on its child's side at it, the new key with them (the
# crit-bit argument). So an insert's tree may take the next operation.
# Record: cursors-indexed
law put_inv:
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +b: U32
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}
  {IM.ix.inv(IM.ix.put(I, x, k, b)) == True{} : Bool}

# LAW: a removal of the cursor at key k from an index on its invariant
# leaves the invariant: the sibling taken up from its parent's bound, the
# keys below each branch fewer, the leftmost's change crossed. So a
# removal's tree may take the next operation.
# Record: cursors-indexed
law del_inv:
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}
  {IM.ix.inv(IM.ix.del(I, x, k)) == True{} : Bool}

# LAW: a put of fresh nodes into an index laid out apart leaves it laid
# out apart: the new leaf and branch apart from the tree's nodes, the
# situating node and each other.
# Record: cursors-indexed
law put_lay:
  for +I: IM.Ix
  for +s: U32
  for +x: U32
  for +k: U32
  for +b: U32
  for +d: Nat
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}
  {IM.ix.lay(IM.ix.put(I, x, k, b), s, d) == True{} : Bool}

# LAW: and a removal leaves it so: the tree after a removal has no node
# the tree before had not.
# Record: cursors-indexed
law del_lay:
  for +I: IM.Ix
  for +s: U32
  for +x: U32
  for +k: U32
  for +d: Nat
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  {IM.ix.lay(IM.ix.del(I, x, k), s, d) == True{} : Bool}

# LAW: the leftmost cursor at key k (IM.ix.at, which a find gives by
# look_at and find_tree) is the ring's first match over the tree's
# leaves (RG.first, its keys read from the words), so that a find on
# the index gives what the ring's find gave, the members the
# leaves.
# Record: cursors-indexed
# Record: hub-laws-reused
law at_first:
  for w: Array<U32>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +k: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  {IM.ix.at(I, k) == RG.first(IM.ix.leaves(I), AD.view(U32, w), d, k) : Maybe<&2, U32>}

# LAW: a removal's leaves, the tree laid out apart and x the cursor at
# key k, are the leaves before without x (RG.without, the ring's unlink),
# in order: x a leaf once, every other leaf apart from it.
# Record: cursors-indexed
law del_leaves:
  for +I: IM.Ix
  for +s: U32
  for +x: U32
  for +k: U32
  for +d: Nat
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}
  {IM.ix.leaves(IM.ix.del(I, x, k)) == RG.without(IM.ix.leaves(I), x) : List<&2, U32>}

# LAW: a put's leaves are the leaves before and the new cursor, as the
# ring's members after an insert are (RG.has; the order is the tree's).
# Record: cursors-indexed
law put_leaves:
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +b: U32
  for +z: U32
  {RG.has(IM.ix.leaves(IM.ix.put(I, x, k, b)), z) == Bool.or(U32.is_eq(x, z), RG.has(IM.ix.leaves(I), z)) : Bool}

# LAW: a removal, on remove_tree's premises, gives the branch it frees
# (IM.ix.par: x's parent, none where x is the tree's only cursor) to the
# free list: ns the list's first nodes before (KMd.chain), each its own
# and apart from the index's nodes and the situating node, the list after
# begins with that branch, then ns (P.free). With insert_free, the free
# list threaded through a serve's crossings.
# Record: cursors-indexed
law remove_free:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +ns: List<&2, U32>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}
  for hno: {IM.fl.ok(ns, d) == True{} : Bool}
  for hns: {IM.ix.flsep(I, s, d, ns) == True{} : Bool}
  for hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}
  {KMd.chain(IM.mb.cons(IM.ix.par(I, x, k), ns), AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{w}, a}, s, x))), d, KMd.word(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{w}, a}, s, x))), d, P.at_fh())) == True{} : Bool}

# LAW: an insert, on insert_tree's premises but its free list's, the
# list's first nodes the branch b where the index is a tree, then ns
# (IM.ix.take), each of ns its own and apart from the index's nodes, the
# situating node, x and b, leaves the list's first nodes ns: the insert
# takes b and no other node.
# Record: cursors-indexed
law insert_free:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +b: U32
  for +ns: List<&2, U32>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}
  for hk: {KMd.word(AD.view(U32, w), d, (x + 2 : U32)) == k : U32}
  for hb: {X.ix.branch(KMd.word(AD.view(U32, w), d, x)) == False{} : Bool}
  for ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}
  for hno: {IM.fl.ok(ns, d) == True{} : Bool}
  for hns: {IM.ix.flsep(I, s, d, ns) == True{} : Bool}
  for hnx: {IM.fl.sep(ns, d, x) == True{} : Bool}
  for hnb: {IM.fl.sep(ns, d, b) == True{} : Bool}
  for hc: {KMd.chain(IM.ix.take(I, b, ns), AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}
  {KMd.chain(ns, AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{w}, a}, s, x))), d, KMd.word(AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{w}, a}, s, x))), d, P.at_fh())) == True{} : Bool}

# LAW: a cursor of the index, on its invariant, is what a find at the
# key its word 2 holds gives (one cursor a position): so that a join or
# a leave, which knows its cursor only as a member, meets remove_tree's
# premise.
# Record: cursors-indexed
law look_member:
  for w: Array<U32>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +y: U32
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hy: {RG.has(IM.ix.leaves(I), y) == True{} : Bool}
  {IM.ix.look(I, KMd.word(AD.view(U32, w), d, (y + 2 : U32))) == Some{y} : Maybe<&2, U32>}

# The serve's side: what its invariant asks of the index's laws
# =============================================================

# LAW: a node of a list laid out apart, each its own base (the ring's
# RG.layout and RG.bases, which a serve states of every node it touches),
# is its own as the index's laws ask (IM.nd.ok).
# Record: cursors-indexed
law layout_ok:
  for +N: List<&2, U32>
  for +d: Nat
  for +a: U32
  for hl: {RG.layout(N, d) == True{} : Bool}
  for hb: {RG.bases(N) == True{} : Bool}
  for ha: {RG.has(N, a) == True{} : Bool}
  {IM.nd.ok(a, d) == True{} : Bool}

# LAW: and two distinct nodes of it apart (IM.nd.sep).
# Record: cursors-indexed
law layout_sep:
  for +N: List<&2, U32>
  for +d: Nat
  for +a: U32
  for +b: U32
  for hl: {RG.layout(N, d) == True{} : Bool}
  for ha: {RG.has(N, a) == True{} : Bool}
  for hb: {RG.has(N, b) == True{} : Bool}
  for hab: {U32.is_eq(a, b) == False{} : Bool}
  {IM.nd.sep(d, a, b) == True{} : Bool}

# LAW: nodes apart from an index and its situating node (IM.ix.flsep),
# and from a put's cursor x and branch b, are apart from the index after
# the put.
# Record: cursors-indexed
law put_flsep:
  for +I: IM.Ix
  for +s: U32
  for +d: Nat
  for +x: U32
  for +k: U32
  for +b: U32
  for +ns: List<&2, U32>
  for h: {IM.ix.flsep(I, s, d, ns) == True{} : Bool}
  for hx: {IM.fl.sep(ns, d, x) == True{} : Bool}
  for hb: {IM.fl.sep(ns, d, b) == True{} : Bool}
  {IM.ix.flsep(IM.ix.put(I, x, k, b), s, d, ns) == True{} : Bool}

# LAW: and from the index after a removal, which adds no node.
# Record: cursors-indexed
law del_flsep:
  for +I: IM.Ix
  for +s: U32
  for +d: Nat
  for +x: U32
  for +k: U32
  for +ns: List<&2, U32>
  for h: {IM.ix.flsep(I, s, d, ns) == True{} : Bool}
  {IM.ix.flsep(IM.ix.del(I, x, k), s, d, ns) == True{} : Bool}

# LAW: an index's nodes all of a list N (RG.sub), and a put's cursor and
# branch of it: the index's nodes after the put all of N.
# Record: cursors-indexed
law put_sub:
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +b: U32
  for +N: List<&2, U32>
  for h: {RG.sub(IM.ix.nodes(I), N) == True{} : Bool}
  for hx: {RG.has(N, x) == True{} : Bool}
  for hb: {RG.has(N, b) == True{} : Bool}
  {RG.sub(IM.ix.nodes(IM.ix.put(I, x, k, b)), N) == True{} : Bool}

# LAW: and after a removal.
# Record: cursors-indexed
law del_sub:
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +N: List<&2, U32>
  for h: {RG.sub(IM.ix.nodes(I), N) == True{} : Bool}
  {RG.sub(IM.ix.nodes(IM.ix.del(I, x, k)), N) == True{} : Bool}

# LAW: what a removal drops, the cursor x and the parent it frees
# (IM.ix.par), is apart from the index that remains and its situating
# node, the index laid out apart: so that the nodes a join frees join the
# free list's nodes apart from the index.
# Record: cursors-indexed
law del_drop:
  for +I: IM.Ix
  for +s: U32
  for +d: Nat
  for +x: U32
  for +k: U32
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}
  {IM.ix.flsep(IM.ix.del(I, x, k), s, d, IM.mb.cons(IM.ix.par(I, x, k), [x])) == True{} : Bool}

# LAW: a write off the free list's first nodes (KMd.nodes.off) and its
# head keeps them its first nodes.
# Record: cursors-indexed
law chain_kept:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +j: U32
  for +val: U32
  for +ns: List<&2, U32>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(j, d), AD.slot(P.at_fh(), d)) == False{} : Bool}
  for hn: {KMd.nodes.off(ns, d, j) == True{} : Bool}
  for hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}
  {KMd.chain(ns, AD.view(U32, KMd.words(P.wr(P.H{KM.MG{w}, a}, j, val))), d, KMd.word(AD.view(U32, KMd.words(P.wr(P.H{KM.MG{w}, a}, j, val))), d, P.at_fh())) == True{} : Bool}

# LAW: a node r freed, its own and apart from the free list's first nodes
# ns, each their own: r, then ns, the list's first nodes after (P.free).
# Record: cursors-indexed
law free_push:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +r: U32
  for +ns: List<&2, U32>
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hok: {IM.nd.ok(r, d) == True{} : Bool}
  for hno: {IM.fl.ok(ns, d) == True{} : Bool}
  for hsep: {IM.fl.sep(ns, d, r) == True{} : Bool}
  for hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}
  {KMd.chain(Con{r, ns}, AD.view(U32, KMd.words(P.free(P.H{KM.MG{w}, a}, r))), d, KMd.word(AD.view(U32, KMd.words(P.free(P.H{KM.MG{w}, a}, r))), d, P.at_fh())) == True{} : Bool}

# LAW: a free leaves the heap's words full at their depth.
# Record: cursors-indexed
law free_full:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +r: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  {AD.full(U32, KMd.words(P.free(P.H{KM.MG{w}, a}, r)), d) == True{} : Bool}

# LAW: and an insert, on insert_tree's premises, its branch taken from
# the free list, the store not grown.
# Record: cursors-indexed
law insert_full:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +b: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}
  for hm: {IM.ix.room(I, AD.view(U32, w), d, b) == True{} : Bool}
  for hk: {KMd.word(AD.view(U32, w), d, (x + 2 : U32)) == k : U32}
  for hb: {X.ix.branch(KMd.word(AD.view(U32, w), d, x)) == False{} : Bool}
  for ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}
  {AD.full(U32, KMd.words(X.ix.insert(P.H{KM.MG{w}, a}, s, x)), d) == True{} : Bool}

# LAW: and a removal, on remove_tree's premises.
# Record: cursors-indexed
law remove_full:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}
  {AD.full(U32, KMd.words(X.ix.remove(P.H{KM.MG{w}, a}, s, x)), d) == True{} : Bool}

# LAW: a write off the index's words (IM.ix.offall) leaves it realized.
# Record: cursors-indexed
law real_kept:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +j: U32
  for +val: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hj: {IM.ix.offall(I, s, d, j) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  {IM.ix.real(AD.view(U32, KMd.words(P.wr(P.H{KM.MG{w}, a}, j, val))), d, s, I) == True{} : Bool}

# LAW: an index's branches all of a list N, and a put's branch of it:
# the branches after the put all of N.
# Record: cursors-indexed
law put_bsub:
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +b: U32
  for +N: List<&2, U32>
  for h: {RG.sub(IM.ix.branches(I), N) == True{} : Bool}
  for hb: {RG.has(N, b) == True{} : Bool}
  {RG.sub(IM.ix.branches(IM.ix.put(I, x, k, b)), N) == True{} : Bool}

# LAW: and after a removal.
# Record: cursors-indexed
law del_bsub:
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +N: List<&2, U32>
  for h: {RG.sub(IM.ix.branches(I), N) == True{} : Bool}
  {RG.sub(IM.ix.branches(IM.ix.del(I, x, k)), N) == True{} : Bool}

# LAW: an index's leaves all of a list, and a put's cursor of it: the
# leaves after the put all of it.
# Record: cursors-indexed
law put_lsub:
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +b: U32
  for +N: List<&2, U32>
  for h: {RG.sub(IM.ix.leaves(I), N) == True{} : Bool}
  for hx: {RG.has(N, x) == True{} : Bool}
  {RG.sub(IM.ix.leaves(IM.ix.put(I, x, k, b)), N) == True{} : Bool}

# LAW: a write off the words the realization reads (IM.ix.offr: a
# cursor's word 1, which a join's link may write, not among them) leaves
# the index realized.
# Record: cursors-indexed
law real_kept1:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +j: U32
  for +val: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hj: {IM.ix.offr(I, s, d, j) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  {IM.ix.real(AD.view(U32, KMd.words(P.wr(P.H{KM.MG{w}, a}, j, val))), d, s, I) == True{} : Bool}

# LAW: the cursor a find gives is one of the index's leaves.
# Record: cursors-indexed
law look_leaf:
  for +I: IM.Ix
  for +k: U32
  for +y: U32
  for hy: {IM.ix.look(I, k) == Some{y} : Maybe<&2, U32>}
  {RG.has(IM.ix.leaves(I), y) == True{} : Bool}

# LAW: the parent a removal frees is one of the index's branches.
# Record: cursors-indexed
law par_branch:
  for +I: IM.Ix
  for +x: U32
  for +k: U32
  for +p: U32
  for hp: {IM.ix.par(I, x, k) == Some{p} : Maybe<&2, U32>}
  {RG.has(IM.ix.branches(I), p) == True{} : Bool}

# LAW: what a removal drops, the cursor and the parent it frees, is none
# of the nodes of the index that remains, the index laid out apart.
# Record: cursors-indexed
law del_absent:
  for +I: IM.Ix
  for +s: U32
  for +d: Nat
  for +x: U32
  for +k: U32
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}
  {RG.none.in(IM.mb.cons(IM.ix.par(I, x, k), [x]), IM.ix.nodes(IM.ix.del(I, x, k))) == True{} : Bool}

# LAW: the cursor a find gives holds the situating node at its word 3, its
# home, as a removal reads it.
# Record: cursors-indexed
law look_home:
  for w: Array<U32>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +k: U32
  for +y: U32
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  for hy: {IM.ix.look(I, k) == Some{y} : Maybe<&2, U32>}
  {KMd.word(AD.view(U32, w), d, (y + 3 : U32)) == s : U32}

# LAW: a free of a node whose words 0 and 1 and the free list's head are
# off the words the realization reads (IM.ix.offr) leaves the index
# realized.
# Record: cursors-indexed
law free_real:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +r: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for h0: {IM.ix.offr(I, s, d, P.base(r)) == True{} : Bool}
  for h1: {IM.ix.offr(I, s, d, (P.base(r) + 1 : U32)) == True{} : Bool}
  for hh: {IM.ix.offr(I, s, d, P.at_fh()) == True{} : Bool}
  for hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}
  {IM.ix.real(AD.view(U32, KMd.words(P.free(P.H{KM.MG{w}, a}, r))), d, s, I) == True{} : Bool}

# LAW: a lookup at key k after a removal at another key kx (IM.ix.del, x
# found at kx) gives what it gave before: the removal's cut keeps the
# leftmost leaf at k (look_at). So a cursor stays found through another's
# removal (cells-freeze.sharing.cursors.index.ring.premises.lookups).
# Record: cursors-indexed
law look_del_other:
  for +I: IM.Ix
  for +s: U32
  for +x: U32
  for +kx: U32
  for +k: U32
  for +d: Nat
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for hl: {IM.ix.lay(I, s, d) == True{} : Bool}
  for hx: {IM.ix.look(I, kx) == Some{x} : Maybe<&2, U32>}
  for hne: {U32.is_eq(kx, k) == False{} : Bool}
  {IM.ix.look(IM.ix.del(I, x, kx), k) == IM.ix.look(I, k) : Maybe<&2, U32>}

# LAW: a lookup at key k after an insert at another key src (IM.ix.put, src
# absent) gives what it gave before: the insert keeps the other leaves'
# order and adds one keyed src (look_at)
# (cells-freeze.sharing.cursors.index.ring.premises.lookups).
# Record: cursors-indexed
law look_put_other:
  for +I: IM.Ix
  for +x: U32
  for +src: U32
  for +b: U32
  for +k: U32
  for hi: {IM.ix.inv(I) == True{} : Bool}
  for ha: {IM.ix.look(I, src) == None{} : Maybe<&2, U32>}
  for hne: {U32.is_eq(src, k) == False{} : Bool}
  {IM.ix.look(IM.ix.put(I, x, src, b), k) == IM.ix.look(I, k) : Maybe<&2, U32>}

# LAW: the cursor a realized index finds at key q, holding q in its word
# 2, is no cursor nc whose word 2 holds another key pos
# (cursor-laws.noself.frontier.cursor): so the cursor a serve finds at
# the frontier's port is not the served one, whose word 2 the serve
# reads its position from, once the port is not the position
# (front_apart).
# Record: cursors-indexed
law found_apart:
  for +v: List<&2, U32>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +q: U32
  for +pos: U32
  for +c: U32
  for +nc: U32
  for +hr: {IM.ix.real(v, d, s, I) == True{} : Bool}
  for +hq: {IM.ix.look(I, q) == Some{c} : Maybe<&2, U32>}
  for +hn: {KMd.word(v, d, (nc + 2 : U32)) == pos : U32}
  for +hne: {U32.is_eq(q, pos) == False{} : Bool}
  {U32.is_eq(c, nc) == False{} : Bool}
