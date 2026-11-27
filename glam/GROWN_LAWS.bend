# Laws of the grown heap in the loop's views (the CursorLaws plan's
# cursor-laws.loop.shape.grow.copy.store.kept): P.grow_more's laws at the
# array level (spike/GROW_LAWS.bend) carried to the views the loop's
# invariant reads, so that the loop laws' growth premises are discharged;
# proved in glam/GROWN_PROOF.bend.

import Base
import ../spike/grow_model.bend as GM
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/kmodel.bend as KMd
import ./ring_model.bend as RG
import ./loop_model.bend as LM
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: each word of each tracked node reads alike after growth (LM.kept,
# lx_up's and grow_next's premise): the view of a heap of 2^(e + 2)
# words whose capacity word reads wc = 2^e nodes, 3 <= e < 28, and the
# view of the grown heap one level deeper, for tracked nodes in range and
# past the header's words. A node off words 0, 1 and 4 is at word 4 or
# past it, so its words miss the capacity's too, which growth writes.
# Record: net-nodes-double
# Record: laws-across-steps-iterative
law grown_kept:
  for w: Array<U32>
  for a: Array<V.Val>
  for +wc: U32
  for +e: Nat
  for N: List<&2, U32>
  for +hf: {AD.full(U32, w, 2n+e) == True{} : Bool}
  for +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_wcap())) == wc : U32}
  for +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}
  for +he3: {Nat.is_le(3n, e) == True{} : Bool}
  for +he27: {Nat.is_lt(e, 28n) == True{} : Bool}
  for +hin: {RG.nodes.in(N, 2n+e) == True{} : Bool}
  for +hp: {KMd.past(N, 2n+e) == True{} : Bool}
  {LM.kept(N, AD.view(U32, w), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a}))))) == True{} : Bool}

# LAW: the fresh nodes, node wc on to node 2wc - 1 (GM.fresh), are the
# grown free list's first: chained from the head in the grown view
# (LM.ext.ok's chain, its prefix empty), on a heap as grown_kept's.
# Record: net-nodes-double
# Record: laws-across-steps-iterative
law grown_chain:
  for w: Array<U32>
  for a: Array<V.Val>
  for +wc: U32
  for +e: Nat
  for +hf: {AD.full(U32, w, 2n+e) == True{} : Bool}
  for +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_wcap())) == wc : U32}
  for +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}
  for +he3: {Nat.is_le(3n, e) == True{} : Bool}
  for +he27: {Nat.is_lt(e, 28n) == True{} : Bool}
  {KMd.chain(GM.fresh(U32.to_nat(wc), wc), AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a})))), 3n+e, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a})))), 3n+e, P.at_fh())) == True{} : Bool}

# LAW: the fresh nodes are distinct, none of them tracked (in range at
# the old depth), each its own base, past the header's words and in
# range at the grown depth (LM.ext.ok's other conjuncts but the ports').
# Record: net-nodes-double
law grown_distinct:
  for +wc: U32
  for +e: Nat
  for +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}
  for +he3: {Nat.is_le(3n, e) == True{} : Bool}
  for +he27: {Nat.is_lt(e, 28n) == True{} : Bool}
  {RG.distinct(GM.fresh(U32.to_nat(wc), wc)) == True{} : Bool}

# Record: net-nodes-double
law grown_none:
  for +wc: U32
  for +e: Nat
  for +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}
  for +he3: {Nat.is_le(3n, e) == True{} : Bool}
  for +he27: {Nat.is_lt(e, 28n) == True{} : Bool}
  for N: List<&2, U32>
  for +hin: {RG.nodes.in(N, 2n+e) == True{} : Bool}
  {RG.none.in(GM.fresh(U32.to_nat(wc), wc), N) == True{} : Bool}

# Record: net-nodes-double
law grown_bases:
  for +wc: U32
  for +e: Nat
  for +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}
  for +he3: {Nat.is_le(3n, e) == True{} : Bool}
  for +he27: {Nat.is_lt(e, 28n) == True{} : Bool}
  {RG.bases(GM.fresh(U32.to_nat(wc), wc)) == True{} : Bool}

# Record: net-nodes-double
law grown_past:
  for +wc: U32
  for +e: Nat
  for +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}
  for +he3: {Nat.is_le(3n, e) == True{} : Bool}
  for +he27: {Nat.is_lt(e, 28n) == True{} : Bool}
  {KMd.past(GM.fresh(U32.to_nat(wc), wc), 3n+e) == True{} : Bool}

# Record: net-nodes-double
law grown_in:
  for +wc: U32
  for +e: Nat
  for +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}
  for +he3: {Nat.is_le(3n, e) == True{} : Bool}
  for +he27: {Nat.is_lt(e, 28n) == True{} : Bool}
  {RG.nodes.in(GM.fresh(U32.to_nat(wc), wc), 3n+e) == True{} : Bool}

# LAW: the fresh nodes lie past the old store, each at word 2^(e + 2)
# or past it.
# Record: net-nodes-double
law grown_above:
  for +wc: U32
  for +e: Nat
  for +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}
  for +he3: {Nat.is_le(3n, e) == True{} : Bool}
  for +he27: {Nat.is_lt(e, 28n) == True{} : Bool}
  {GM.above(GM.fresh(U32.to_nat(wc), wc), 2n+e) == True{} : Bool}

# LAW: across the heap's doubling from depth d, each cursor's faced port
# keeps off the nodes made past the old store (E, GM.above, in range one
# level deeper) and off the free list's head: LM.ext.ok's ports, from
# the old invariant's (px.off over the tracked nodes, its base the head),
# the cursors tracked (sub) and read alike (LM.kept), and each faced port
# linking a word in range (LM.faced.in).
# Record: net-nodes-double
# Record: laws-across-steps-iterative
law grown_ports:
  for +v: List<&2, U32>
  for +v2: List<&2, U32>
  for +d: Nat
  for +L: List<&2, U32>
  for +N: List<&2, U32>
  for +E: List<&2, U32>
  for +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}
  for +hs: {RG.sub(L, N) == True{} : Bool}
  for +hk: {LM.kept(N, v, d, v2) == True{} : Bool}
  for +hfi: {LM.faced.in(L, v, d) == True{} : Bool}
  for +hpo: {RG.px.off(L, v, d, L, N) == True{} : Bool}
  for +hab: {GM.above(E, d) == True{} : Bool}
  for +hin: {RG.nodes.in(E, 1n+d) == True{} : Bool}
  {RG.px.off(L, v2, 1n+d, L, E) == True{} : Bool}

# LAW: across the heap's doubling from depth d, each cursor's faced port
# still links a word in range (LM.faced.in, at 1n+d), the cursors tracked
# and read alike (LM.kept): a link word below 2^d is below 2^(d + 1), a
# static's none. So that the guard's rounds of growth carry it.
# Record: net-nodes-double
# Record: laws-across-steps-iterative
law grown_faced:
  for +v: List<&2, U32>
  for +v2: List<&2, U32>
  for +d: Nat
  for +L: List<&2, U32>
  for +N: List<&2, U32>
  for +hs: {RG.sub(L, N) == True{} : Bool}
  for +hk: {LM.kept(N, v, d, v2) == True{} : Bool}
  for +hfi: {LM.faced.in(L, v, d) == True{} : Bool}
  {LM.faced.in(L, v2, 1n+d) == True{} : Bool}

# LAW: after one growth the free list holds any k nodes up to the old
# node count, wc (P.frees answers, the heap kept): the fresh nodes chained from the
# head, each link one on. So that the guard's growth is its last when
# the room it asks is no more than the heap's nodes.
# Record: net-nodes-double
law grown_frees:
  for w: Array<U32>
  for a: Array<V.Val>
  for +wc: U32
  for +e: Nat
  for +k: Nat
  for +hf: {AD.full(U32, w, 2n+e) == True{} : Bool}
  for +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_wcap())) == wc : U32}
  for +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}
  for +he3: {Nat.is_le(3n, e) == True{} : Bool}
  for +he27: {Nat.is_lt(e, 28n) == True{} : Bool}
  for +hk: {Nat.is_le(k, U32.to_nat(wc)) == True{} : Bool}
  {P.frees(k, Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a}))) == (Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a})), True{}) : P.H & Bool}

# LAW: after growth the grown view chains the fresh nodes, then the old
# free list's tracked prefix F (its chain from the old head kept, F
# tracked): the last fresh node links the old head (more_last), and F's
# link words read alike (LM.kept). So that growth keeps the old prefix
# after the fresh nodes (lx_more), a request past them still tracked.
# Record: net-nodes-double
# Record: laws-across-steps-iterative
law grown_chain_keep:
  for w: Array<U32>
  for a: Array<V.Val>
  for +wc: U32
  for +e: Nat
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +hf: {AD.full(U32, w, 2n+e) == True{} : Bool}
  for +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_wcap())) == wc : U32}
  for +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}
  for +he3: {Nat.is_le(3n, e) == True{} : Bool}
  for +he27: {Nat.is_lt(e, 28n) == True{} : Bool}
  for +hc: {KMd.chain(F, AD.view(U32, w), 2n+e, KMd.word(AD.view(U32, w), 2n+e, P.at_fh())) == True{} : Bool}
  for +hs: {RG.sub(F, N) == True{} : Bool}
  for +hk: {LM.kept(N, AD.view(U32, w), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a}))))) == True{} : Bool}
  {KMd.chain(List.append(&2, U32, GM.fresh(U32.to_nat(wc), wc), F), AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a})))), 3n+e, KMd.word(AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a})))), 3n+e, P.at_fh())) == True{} : Bool}

# LAW: growth keeps the free list's tracked prefix the whole list
# (LM.ends): the fresh nodes before it, the link after them the old head
# (more_last), its links read alike (LM.kept). So that the guard's rounds
# keep the room it finds tracked.
# Record: net-nodes-double
# Record: laws-across-steps-iterative
law grown_ends:
  for w: Array<U32>
  for a: Array<V.Val>
  for +wc: U32
  for +e: Nat
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +hf: {AD.full(U32, w, 2n+e) == True{} : Bool}
  for +hwc: {Pair.snd(Array<U32>, U32, Array.get(U32, w, P.at_wcap())) == wc : U32}
  for +hw: {U32.to_nat(wc) == Nat.pow(2n, e) : Nat}
  for +he3: {Nat.is_le(3n, e) == True{} : Bool}
  for +he27: {Nat.is_lt(e, 28n) == True{} : Bool}
  for +hen: {LM.ends(F, AD.view(U32, w), 2n+e) == True{} : Bool}
  for +hs: {RG.sub(F, N) == True{} : Bool}
  for +hk: {LM.kept(N, AD.view(U32, w), 2n+e, AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a}))))) == True{} : Bool}
  {LM.ends(List.append(&2, U32, GM.fresh(U32.to_nat(wc), wc), F), AD.view(U32, KMd.words(Pair.fst(P.H, Bool, P.grow_more(P.H{KM.MG{w}, a})))), 3n+e) == True{} : Bool}

# LAW: a tracked prefix that is the whole free list holds the room the
# guard finds (LM.fr, P.frees as the model reads it): the walk's link past
# the prefix is 0, so a link k - 1 steps on that is a node lies within it.
# Record: collect-before-growth
law cover_room:
  for +v: List<&2, U32>
  for +d: Nat
  for +F: List<&2, U32>
  for +k: Nat
  for +hc: {KMd.chain(F, v, d, KMd.word(v, d, P.at_fh())) == True{} : Bool}
  for +hen: {LM.ends(F, v, d) == True{} : Bool}
  for +hfr: {LM.fr(k, v, d) == True{} : Bool}
  {Nat.is_le(k, List.length(&2, U32, F)) == True{} : Bool}
