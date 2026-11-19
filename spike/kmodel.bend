import Base
import ./kprim.bend as P
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
