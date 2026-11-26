# The pending invariant across serves (glam/LOOP_LAWS.bend,
# cursor-laws.loop.shape): RG.px.ok with nothing pending, and what no
# step returns of it, the live nodes distinct and the tracked nodes laid
# out apart, each its own base, past the header. No code calls these.

import Base
import ../spike/kmodel.bend as KMd
import ./ring_model.bend as RG
import ./index_model.bend as IM

# the wider invariant between serves
def lx.ok(+v: List<&2, U32>, +d: Nat, +s: U32, +I: IM.Ix, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>) -> Bool:
  RG.px.ok(v, d, s, I, Nil{}, L, F, N) && (RG.distinct(L) && (RG.layout(N, d) && (RG.bases(N) && KMd.past(N, d))))
