# The store's growth (cursor-laws.loop.shape.grow.copy.store): what the
# kernel's doubling (KM.grow, under P.grow_more) does to a store's words,
# so that the loop's growth premises (LM.kept, LM.ext.ok's for the fresh
# nodes) are discharged by laws of the kernel's own code. The depth of
# the store, which KM.depth computes by matching the literal 1 and so
# never reduces over a symbolic capacity, is a premise.

import Base
import ./kmem_grow.bend as KM
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
