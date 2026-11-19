import Base
import ./kprim.bend as P
import ./kmem_grow.bend as KM
import ./val.bend as V
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# The heap's words as the laws name them (cells-freeze.nested.host.repr,
# docs/reviews/Refs_2026-11-18.md): no code calls these; laws in spike/
# and glam/ name them, so that a law does not spell the encoding, and
# proofs unfold them.

# the link word of port r: a node's port links at its reference plus one;
# a static has no node and so none (static-links-count-as-nodes)
def lw.k(+st: Bool, +r: U32) -> Maybe<&2, U32>:
  match st:
    case True{}:
      None{}
    case False{}:
      Some{(r + 1 : U32)}

def lw(+r: U32) -> Maybe<&2, U32>:
  lw.k(P.is_static(r), r)

# word j none of link word m's, in a heap of depth d
def off.lw(m: Maybe<&2, U32>, +d: Nat, +j: U32) -> Bool:
  match m:
    case Some{+i}:
      Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot(j, d)))
    case None{}:
      True{}

# word j not port r's link word, which linking r writes
def off.port(+d: Nat, +r: U32, +j: U32) -> Bool:
  off.lw(lw(r), d, j)

# the reference of port p of the node at b (the code writes b + p in
# place); for witnesses built by the code's writes (Refs_2026-11-18, R4)
def ref(+b: U32, +p: U32) -> U32:
  (b + p : U32)

# The header's words a splice writes besides the head (the splice's
# frame, an exact list: splice-frame-premises): the error count, which an
# error counted writes (P.err_if), and the value table's bookkeeping, its
# free head, count, capacity and depth, which a value put in the table
# writes (P.tab_put's dt_back)
def err_words() -> List<&2, U32>:
  [P.at_errs()]

def tab_words() -> List<&2, U32>:
  [P.at_tfh(), P.at_tn(), P.at_tcap(), P.at_td()]

def hdr_words() -> List<&2, U32>:
  Con{P.at_errs(), tab_words()}

# word j's slot none of ws's: j off every word a step writes
def off.words(ws: List<&2, U32>, +d: Nat, +j: U32) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+w, t}:
      Bool.not(Nat.is_eq(AD.slot(w, d), AD.slot(j, d))) && off.words(t, d, j)

# with the head, the header's words a splice may write
def hdr_all() -> List<&2, U32>:
  Con{P.at_fh(), hdr_words()}

# The free list's nodes, as a splice takes them (splice-frame-premises):
# the word a view holds at i, 0 where none
def word.m(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{+q}:
      q
    case None{}:
      0

def word(+v: List<&2, U32>, +d: Nat, +i: U32) -> U32:
  word.m(List.get(&2, U32, v, AD.slot(i, d)))

# the node a free list's link names, the link its index plus one (P.alloc)
def at_idx(+h: U32) -> U32:
  ((h - 1 : U32) << 2n : U32)

# ns the free list's nodes from link h on: h not 0 and naming ns's first,
# whose word 1 links the next
def chain(ns: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +h: U32) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+n, r}:
      Bool.not(U32.is_eq(h, 0)) && (U32.is_eq(at_idx(h), n) && chain(r, v, d, word(v, d, (n + 1 : U32))))

# a node's four words
def nw(+n: U32) -> List<&2, U32>:
  [n, (n + 1 : U32), (n + 2 : U32), (n + 3 : U32)]

# every word of xs off every word of ys
def ws.off(xs: List<&2, U32>, +ys: List<&2, U32>, +d: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, r}:
      off.words(ys, d, x) && ws.off(r, ys, d)

# word j in no node of ns
def nodes.off(ns: List<&2, U32>, +d: Nat, +j: U32) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+n, r}:
      off.words(nw(n), d, j) && nodes.off(r, d, j)

# the nodes of ns apart, every later one's words off each one's
def apart.n(+n: U32, ms: List<&2, U32>, +d: Nat) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case Con{+m, r}:
      ws.off(nw(m), nw(n), d) && apart.n(n, r, d)

def apart(ns: List<&2, U32>, +d: Nat) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+n, +r}:
      apart.n(n, r, d) && apart(r, d)

# the nodes of ns past the header's words a splice writes
def past(ns: List<&2, U32>, +d: Nat) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+n, r}:
      ws.off(nw(n), hdr_all(), d) && past(r, d)

# a heap's words, and its values
def words(h: P.H) -> Array<U32>:
  match h:
    case P.H{w, a}:
      match w:
        case KM.MG{x}:
          x

def vals(h: P.H) -> Array<V.Val>:
  match h:
    case P.H{w, a}:
      a
