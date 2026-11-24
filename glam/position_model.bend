import Base
import ../spike/kprim.bend as P
import ./position.bend as Q

# What glam/POSITION_LAWS.bend states of positioned demand (the cursor-laws
# plan's cursor-laws.noself.frontier.faces): no code calls these.

# a frontier faces the position: its port is the position's link word,
# read in the frontier's own heap
def front.at(r: Q.Pd, +pos: U32) -> Bool:
  match r:
    case Q.PdFront{h, +q, +n}:
      U32.is_eq(Pair.snd(P.H, U32, P.rd(h, (pos + 1 : U32))), q)
    case Q.PdValue{h, +q, +n}:
      True{}
    case Q.PdCur{h, +x, +n}:
      True{}
    case Q.PdStatic{h, +n}:
      True{}
    case Q.PdStop{d, +n}:
      True{}
