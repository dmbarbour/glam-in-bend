# The laws of a join's link over the pending invariant's facing
# (glam/JOIN_PROOF.bend; cells-freeze.sharing.cursors.index.ring.inv):
# what a join's P.link_xx, linking the ports its two live nodes x and y
# faced, leaves of the live nodes after, x and y no longer among them.

import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ./ring_model.bend as RG
import ../spike/kmodel.bend as KMd
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# LAW: the ports two live nodes x and y face linked (P.link_xx), the live
# nodes then L2 (L's but x and y, L2 none of them): each of L2 faces a
# port faceable by L2 (RG.faces), its link word off every tracked node's
# words but the live ones' words 1 to 3 and off the free list's head
# (RG.px.off), and they face one another both ways, none itself
# (RG.px.tw), as before the link over L, the nodes tracked in N laid
# out apart. A live node that x faced faces what y faced, and the other
# way round; none faces x or y.
# Record: cursors-indexed
# Record: copy-links-two-way
# Record: serve-premises-over-index
law link_live:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +L: List<&2, U32>
  for +L2: List<&2, U32>
  for +N: List<&2, U32>
  for +x: U32
  for +y: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hLN: {RG.sub(L, N) == True{} : Bool}
  for hx: {RG.has(L, x) == True{} : Bool}
  for hy: {RG.has(L, y) == True{} : Bool}
  for hxy: {U32.is_eq(x, y) == False{} : Bool}
  for hs1: {RG.sub(L2, L) == True{} : Bool}
  for hs2: {RG.sub(L, Con{x, Con{y, L2}}) == True{} : Bool}
  for hx2: {RG.has(L2, x) == False{} : Bool}
  for hy2: {RG.has(L2, y) == False{} : Bool}
  for hF: {RG.faces(L, AD.view(U32, w), d, L) == True{} : Bool}
  for hO: {RG.px.off(L, AD.view(U32, w), d, L, N) == True{} : Bool}
  for hT: {RG.px.tw(L, AD.view(U32, w), d, L) == True{} : Bool}
  {RG.faces(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{w}, a}, KMd.word(AD.view(U32, w), d, (x + 1 : U32)), KMd.word(AD.view(U32, w), d, (y + 1 : U32))))), d, L2) && (RG.px.off(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{w}, a}, KMd.word(AD.view(U32, w), d, (x + 1 : U32)), KMd.word(AD.view(U32, w), d, (y + 1 : U32))))), d, L2, N) && RG.px.tw(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{w}, a}, KMd.word(AD.view(U32, w), d, (x + 1 : U32)), KMd.word(AD.view(U32, w), d, (y + 1 : U32))))), d, L2)) == True{} : Bool}
