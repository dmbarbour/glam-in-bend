import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/kmodel.bend as KMd
import ./ring_model.bend as RG

# Witness heaps built by the code's own writes, not spelled word by word
# (docs/reviews/Refs_2026-11-18.md, R4): a face by P.link, a static by
# P.put_st, a header by P.hd2, a reference by KMd.ref; so that a change
# of encoding changes them with the code. Only the kernel's primitives,
# which glam's mutations leave alone: a witness built by R.cursor would
# change under a mutation of it. A node's words are laid out in place:
# a cursor's word 2 its key, its position, word 3 its home; a branch's
# words 2 and 3 its children. The witnesses of
# glam/MUTANTS.txt and glam/SERVE_MUTANTS.txt name them; glam/PROOF.bend
# and glam/SERVE_PROOF.bend import this file so that a witness, written
# beside them, may.

# an empty heap of 64 words, the free list's head hd
def empty(+hd: U32) -> P.H:
  P.wr(P.H{KM.MG{[0 : U32^6n]}, [V.VUnit{} : V.Val^1n]}, P.at_fh(), hd)

# a node at x: header hd, word 2 pos, word 3 nx
def member(h: P.H, +x: U32, +hd: U32, +pos: U32, +nx: U32) -> P.H:
  P.wr(P.wr(P.wr(h, x, hd), (x + 2 : U32), pos), (x + 3 : U32), nx)

# a situating node at s, of form 2, facing the static eraser, its word 2
# x, its word 3 nx: itself for an empty index, else the index's root
def situ(h: P.H, +s: U32, +x: U32, +nx: U32) -> P.H:
  P.put_st(member(h, s, P.hd2(18, 2, 0), x, nx), s, P.era())

# a placeholder at x, facing port f, its word 2 pos
def placeholder(h: P.H, +x: U32, +f: U32, +pos: U32) -> P.H:
  P.wr(P.link(P.wr(h, x, P.hd2(18, 0, 0)), x, f), (x + 2 : U32), pos)

# A copy's cursors in an index of the net's nodes (cursors-indexed): a
# cursor at x, negative, its key k (word 2), its home s (word 3), facing
# port f
def leaf(h: P.H, +x: U32, +k: U32, +s: U32, +f: U32) -> P.H:
  P.link(member(h, x, P.hd2(18, 0, 0), k, s), x, f)

# The pending index: s at 8, its word 3 its one leaf, the cursor 16 (key
# 9, facing node 52's port 0); a placeholder 20 (position pos, facing node
# 44's); the free list's head 10, node 36 its last
def ix_heap(+pos: U32) -> P.H:
  placeholder(leaf(situ(empty(10), 8, 99, 16), 16, 9, 8, KMd.ref(52, 0)), 20, KMd.ref(44, 0), pos)

def ix_one(+pos: U32) -> Array<U32>:
  RG.words(ix_heap(pos))

# and a second placeholder, 24, facing port f24 (node 48's port 0, or a
# static)
def ix_two_f(+pos: U32, +f24: U32) -> Array<U32>:
  RG.words(placeholder(ix_heap(pos), 24, f24, 3))

def ix_two(+pos: U32) -> Array<U32>:
  ix_two_f(pos, KMd.ref(48, 0))

# Two cursors in the index: s at 8, its word 3 the branch 28 (testing bit
# 1), its left child the cursor 16 (key ky, facing node 52's port 0), its
# right the cursor 12 (key 7, facing node 40's port 1, or with ix_pair_st
# the static f12; with ix_pair_g, the cursors facing f12 and f16); the
# free list's head 10
def ix_branch28(h: P.H) -> Array<U32>:
  RG.words(P.wr(P.wr(P.wr(h, 28, P.hd2(18, 3, 1)), 30, 16), 31, 12))

def ix_pair_g(+f12: U32, +f16: U32, +ky: U32) -> Array<U32>:
  ix_branch28(leaf(leaf(situ(empty(10), 8, 99, 28), 16, ky, 8, f16), 12, 7, 8, f12))

def ix_pair_k(+ky: U32) -> Array<U32>:
  ix_pair_g(KMd.ref(40, 1), KMd.ref(52, 0), ky)

def ix_pair() -> Array<U32>:
  ix_pair_k(9)

def ix_pair_st(+f12: U32) -> Array<U32>:
  ix_branch28(P.put_st(member(leaf(situ(empty(10), 8, 99, 28), 16, 9, 8, KMd.ref(52, 0)), 12, P.hd2(18, 0, 0), 7, 8), 12, f12))
