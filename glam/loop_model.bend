# The pending invariant across serves (glam/LOOP_LAWS.bend,
# cursor-laws.loop.shape): RG.px.ok with nothing pending, and what no
# step returns of it, the live nodes distinct, the tracked nodes
# distinct and in range, each its own base, past the header, so laid out
# apart (bases_apart). No code calls these.

import Base
import ../spike/kmodel.bend as KMd
import ../spike/kprim.bend as P
import ./ring_model.bend as RG
import ./index_model.bend as IM

# the wider invariant between serves
def lx.ok(+v: List<&2, U32>, +d: Nat, +s: U32, +I: IM.Ix, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>) -> Bool:
  RG.px.ok(v, d, s, I, Nil{}, L, F, N) && (RG.distinct(L) && (RG.distinct(N) && (RG.nodes.in(N, d) && (RG.bases(N) && KMd.past(N, d)))))

# a list headed by s
def headed(L: List<&2, U32>, +s: U32) -> Bool:
  match L:
    case Nil{}:
      False{}
    case Con{+x, r}:
      U32.is_eq(x, s)

# a list's tail
def tl(L: List<&2, U32>) -> List<&2, U32>:
  match L:
    case Nil{}:
      Nil{}
    case Con{+x, r}:
      r

# the growth premises (glam/LOOP_LAWS.bend, lx_extend): free nodes E past
# the free list's tracked prefix F, chained after it, none twice and
# none of the tracked nodes N, in range (RG.nodes.in), so laid out apart
# from them (bases_apart), no live node's faced port linking into them,
# each its own base, past the header; the
# kernel's to discharge (kernel-refine; docs/reviews/Alloc_2026-11-26.md)
def ext.ok(+v: List<&2, U32>, +d: Nat, +s: U32, +I: IM.Ix, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +E: List<&2, U32>) -> Bool:
  KMd.chain(List.append(&2, U32, F, E), v, d, KMd.word(v, d, P.at_fh())) && (RG.distinct(E) && (RG.none.in(E, N) && (RG.px.off(L, v, d, L, E) && (RG.bases(E) && (KMd.past(E, d) && (RG.nodes.in(E, d)))))))
