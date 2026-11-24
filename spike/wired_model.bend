import Base
import ./kprim.bend as P
import ./krules.bend as KR
import ./kmodel.bend as KMd

# The wiring as the laws name it (cursor-laws.noself.model,
# wiring-premise-before-refinement): no code calls these. A port's link as
# the wiring's audit checks it (KN.wa.link), over the words' view: a
# static eraser, or a port of a live node past the header, within the
# capacity, below its kind's arity, not itself, linking it back.

def live(+live: Bool, +v: List<&2, U32>, +d: Nat, +x: U32, +y: U32) -> Bool:
  match live:
    case True{}:
      U32.is_eq(KMd.word(v, d, (y + 1 : U32)), x)
    case False{}:
      False{}

def at(+inside: Bool, +v: List<&2, U32>, +d: Nat, +x: U32, +y: U32) -> Bool:
  match inside:
    case True{}:
      live(U32.is_ne(KMd.word(v, d, P.base(y)), 0) && U32.is_lt(P.port(y), KR.kind_arity(P.rk(KMd.word(v, d, P.base(y))))), v, d, x, y)
    case False{}:
      False{}

def lk(+st: Bool, +v: List<&2, U32>, +d: Nat, +x: U32, +y: U32, +cap: U32) -> Bool:
  match st:
    case True{}:
      U32.is_eq(y, P.era())
    case False{}:
      at(U32.is_ge((y >> 2n : U32), P.first()) && U32.is_lt((y >> 2n : U32), cap) && U32.is_ne(y, x), v, d, x, y)

def port.ok(+v: List<&2, U32>, +d: Nat, +x: U32, +cap: U32) -> Bool:
  lk(P.is_static(KMd.word(v, d, (x + 1 : U32))), v, d, x, KMd.word(v, d, (x + 1 : U32)), cap)
