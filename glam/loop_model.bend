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
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

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

# a word read alike: the same, or none in both
def same(a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Bool:
  match a:
    case Some{+x}:
      match b:
        case Some{+y}:
          U32.is_eq(x, y)
        case None{}:
          False{}
    case None{}:
      match b:
        case Some{+y}:
          False{}
        case None{}:
          True{}

# word i read alike in v2 at depth 1n+d as in v at d
def kept.w(+i: U32, +v: List<&2, U32>, +d: Nat, +v2: List<&2, U32>) -> Bool:
  same(List.get(&2, U32, v2, AD.slot(i, 1n+d)), List.get(&2, U32, v, AD.slot(i, d)))

# the doubling's relation (cursor-laws.loop.shape.grow.copy.up): each word
# of each node of N read alike in the grown view v2 at 1n+d as in v at d;
# the growth law's to discharge (cursor-laws.loop.shape.grow.copy.store)
def kept(N: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +v2: List<&2, U32>) -> Bool:
  match N:
    case Nil{}:
      True{}
    case Con{+n, t}:
      kept.w(n, v, d, v2) && (kept.w((n + 1 : U32), v, d, v2) && (kept.w((n + 2 : U32), v, d, v2) && (kept.w((n + 3 : U32), v, d, v2) && kept(t, v, d, v2))))

# a link word in range: below 2^d, or none (a static)
def lw.in(m: Maybe<&2, U32>, +d: Nat) -> Bool:
  match m:
    case Some{+i}:
      Nat.is_lt(U32.to_nat(i), Nat.pow(2n, d))
    case None{}:
      True{}

# the port each of ys faces (its word 1) linked in range: scaffolding, the
# wiring's to discharge (WR.port.ok reads a live node's port as one of a
# node in range; net-obvious-errors, kernel-refine)
def faced.in(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+z, t}:
      lw.in(KMd.lw(KMd.word(v, d, (z + 1 : U32))), d) && faced.in(t, v, d)
