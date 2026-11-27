# The store's growth (cursor-laws.loop.shape.grow.copy.store): what the
# kernel's doubling (KM.grow, under P.grow_more) does to a store's words,
# so that the loop's growth premises (LM.kept, LM.ext.ok's for the fresh
# nodes) are discharged by laws of the kernel's own code. The depth of
# the store, which KM.depth computes by matching the literal 1 and so
# never reduces over a symbolic capacity, is a premise.

import Base
import ./kmem_grow.bend as KM
import ./kprim.bend as P
import ./grow_model.bend as GM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: a copy keeps its destination full.
# Record: net-nodes-double
law copy_full:
  for k: Nat
  for +i: U32
  for src: Array<U32>
  for dst: Array<U32>
  for +dd: Nat
  for +hfd: {AD.full(U32, dst, dd) == True{} : Bool}
  {AD.full(U32, KM.copy(k, i, KM.CP{src, dst}), dd) == True{} : Bool}

# LAW: the store doubled is full one level deeper.
# Record: net-nodes-double
law grow_full:
  for w: Array<U32>
  for +d: Nat
  for +cap: U32
  for +hdp: {KM.depth(32n, cap, 0n) == d : Nat}
  {AD.full(U32, GM.arr(KM.grow(KM.MG{w}, cap)), 1n+d) == True{} : Bool}

# LAW: a word below the old capacity, 2^d, reads as before: the copy
# takes word j for each j below it.
# Record: net-nodes-double
law grow_old:
  for w: Array<U32>
  for +d: Nat
  for +cap: U32
  for +j: U32
  for +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}
  for +hc: {U32.to_nat(cap) == Nat.pow(2n, d) : Nat}
  for +hdp: {KM.depth(32n, cap, 0n) == d : Nat}
  for +hj: {Nat.is_lt(U32.to_nat(j), Nat.pow(2n, d)) == True{} : Bool}
  {Pair.snd(Array<U32>, U32, Array.get(U32, GM.arr(KM.grow(KM.MG{w}, cap)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, w, j)) : U32}

# LAW: a word of the new half reads 0, the doubled store zero-filled.
# Record: net-nodes-double
law grow_new:
  for w: Array<U32>
  for +d: Nat
  for +cap: U32
  for +j: U32
  for +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}
  for +hc: {U32.to_nat(cap) == Nat.pow(2n, d) : Nat}
  for +hdp: {KM.depth(32n, cap, 0n) == d : Nat}
  for +hj0: {Nat.is_le(Nat.pow(2n, d), U32.to_nat(j)) == True{} : Bool}
  for +hj1: {Nat.is_lt(U32.to_nat(j), Nat.pow(2n, 1n+d)) == True{} : Bool}
  {Pair.snd(Array<U32>, U32, Array.get(U32, GM.arr(KM.grow(KM.MG{w}, cap)), j)) == 0 : U32}

# LAW: a store asked for room it lacks, that may grow and that twice its
# capacity holds, doubles once (KM.m_ensure, as grow.c asks it): the
# store grown, its capacity twice. The products a caller asks with stand
# in the premises, which the capacity word's law gives where it is used.
# Record: net-nodes-double
law ensure_once:
  for m: KM.M
  for +n: U32
  for +cap: U32
  for +maxd: Nat
  for +h1: {U32.is_le(n, cap) == False{} : Bool}
  for +h2: {Nat.is_ge(KM.depth(32n, cap, 0n), maxd) == False{} : Bool}
  for +h3: {U32.is_le(n, (cap * 2 : U32)) == True{} : Bool}
  {KM.m_ensure(m, n, cap, maxd) == (KM.grow(m, cap), (cap * 2 : U32)) : KM.M & U32}

# LAW: threading the grown store's new nodes (P.thread, under grow.done)
# writes only word 1 of nodes i on, so that each word below node i's,
# index 4i, reads as before: the old store's words kept. c a word bound
# on the words written (4(i + k) of them), within the store's 2^D.
# Record: net-nodes-double
law thread_below:
  for k: Nat
  for +i: U32
  for +to: U32
  for a: Array<U32>
  for +j: U32
  for +D: Nat
  for +c: U32
  for +hf: {AD.full(U32, a, D) == True{} : Bool}
  for +hD: {Nat.is_lt(D, 32n) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(Nat.mul(U32.to_nat(i), 4n), Nat.mul(k, 4n)), U32.to_nat(c)) == True{} : Bool}
  for +hcD: {Nat.is_le(U32.to_nat(c), Nat.pow(2n, D)) == True{} : Bool}
  for +hj: {Nat.is_lt(U32.to_nat(j), Nat.mul(U32.to_nat(i), 4n)) == True{} : Bool}
  {Pair.snd(Array<U32>, U32, Array.get(U32, GM.arr(P.thread(k, KM.MG{a}, i, to)), j)) == Pair.snd(Array<U32>, U32, Array.get(U32, a, j)) : U32}

# LAW: threading the grown store's new nodes links each in turn: node n
# of i .. i + k - 1 reads, in its word 1, the next node (n + 1, encoded
# one on) or, for the last before to, the list's end (P.link_of.go). The
# bounds as thread_below's.
# Record: net-nodes-double
law thread_link:
  for k: Nat
  for +i: U32
  for +to: U32
  for a: Array<U32>
  for +n: U32
  for +D: Nat
  for +c: U32
  for +hf: {AD.full(U32, a, D) == True{} : Bool}
  for +hD: {Nat.is_lt(D, 32n) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(Nat.mul(U32.to_nat(i), 4n), Nat.mul(k, 4n)), U32.to_nat(c)) == True{} : Bool}
  for +hcD: {Nat.is_le(U32.to_nat(c), Nat.pow(2n, D)) == True{} : Bool}
  for +hlo: {Nat.is_le(U32.to_nat(i), U32.to_nat(n)) == True{} : Bool}
  for +hhi: {Nat.is_lt(U32.to_nat(n), Nat.add(U32.to_nat(i), k)) == True{} : Bool}
  {Pair.snd(Array<U32>, U32, Array.get(U32, GM.arr(P.thread(k, KM.MG{a}, i, to)), ((n << 2n : U32) + 1 : U32))) == P.link_of.go(U32.is_lt((n + 1 : U32), to), (n + 1 : U32)) : U32}

# LAW: the depth m_ensure reads of a store of 2^d words is d (KM.depth),
# so that the growth laws' depth premise is the capacity's relation to
# the depth, for every d below 32.
# Record: net-nodes-double
law depth_pow:
  for +cap: U32
  for +d: Nat
  for +hc: {U32.to_nat(cap) == Nat.pow(2n, d) : Nat}
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {KM.depth(32n, cap, 0n) == d : Nat}

# LAW: a node's reference, its index shifted two places, is its own base
# (P.base): its low two bits clear, the rest kept. So that the nodes
# growth threads and frees are bases, as the free list's are taken.
# Record: net-nodes-double
law base_shl:
  for +i: U32
  {P.base((i << 2n : U32)) == (i << 2n : U32) : U32}
