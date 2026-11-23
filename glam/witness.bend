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
# change under a mutation of it. A ring's words are laid out in place
# (word 2 a position, word 3 the next member). The witnesses of
# glam/MUTANTS.txt and glam/SERVE_MUTANTS.txt name them; glam/PROOF.bend
# and glam/SERVE_PROOF.bend import this file so that a witness, written
# beside them, may.

# an empty heap of 64 words, the free list's head hd
def empty(+hd: U32) -> P.H:
  P.wr(P.H{KM.MG{[0 : U32^6n]}, [V.VUnit{} : V.Val^1n]}, P.at_fh(), hd)

# a ring's member at x: header hd, position pos, the next member nx
def member(h: P.H, +x: U32, +hd: U32, +pos: U32, +nx: U32) -> P.H:
  P.wr(P.wr(P.wr(h, x, hd), (x + 2 : U32), pos), (x + 3 : U32), nx)

# a situating node at s, of form 2, facing the static eraser, its word 2
# x, the next member nx
def situ(h: P.H, +s: U32, +x: U32, +nx: U32) -> P.H:
  P.put_st(member(h, s, P.hd2(18, 2, 0), x, nx), s, P.era())

# a cursor at x, negative, at position pos, facing port f
def cursor(h: P.H, +x: U32, +pos: U32, +nx: U32, +f: U32) -> P.H:
  P.link(member(h, x, P.hd2(18, 0, 0), pos, nx), x, f)

# a placeholder at x, facing port f, its word 2 pos
def placeholder(h: P.H, +x: U32, +f: U32, +pos: U32) -> P.H:
  P.wr(P.link(P.wr(h, x, P.hd2(18, 0, 0)), x, f), (x + 2 : U32), pos)

# The pending ring: s at 8, its cursors 12 (position 7, facing node 40's
# port 1) and 16 (position 9, facing node 52's), placeholders 20
# (position 5, facing node 44's) and 24 (position 3, facing f24); the
# free list's head 10
def pending(+f24: U32) -> Array<U32>:
  RG.words(placeholder(placeholder(
    cursor(cursor(situ(empty(10), 8, 99, 12), 12, 7, 16, KMd.ref(40, 1)), 16, 9, 8, KMd.ref(52, 0)),
    20, KMd.ref(44, 0), 5), 24, f24, 3))

# A copy's cursors in an index of the net's nodes (cursors-indexed): a
# cursor at x, negative, its key k (word 2), its home s (word 3), facing
# port f
def leaf(h: P.H, +x: U32, +k: U32, +s: U32, +f: U32) -> P.H:
  P.link(member(h, x, P.hd2(18, 0, 0), k, s), x, f)

# The pending index: s at 8, its word 3 its one leaf, the cursor 16 (key
# 9, facing node 52's port 0); a placeholder 20 (position pos, facing node
# 44's); the free list's head 10, node 36 its last
def ix_one(+pos: U32) -> Array<U32>:
  RG.words(placeholder(leaf(situ(empty(10), 8, 99, 16), 16, 9, 8, KMd.ref(52, 0)), 20, KMd.ref(44, 0), pos))
