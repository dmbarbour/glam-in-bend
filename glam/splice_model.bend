import Base
import ../spike/kprim.bend as P
import ./splice.bend as S

# What the splice's laws (glam/SPLICE_LAWS.bend) name of its state and the
# heap: no code calls these (cells-freeze.nested.host.splice).

# the splice's net
def heap(s: S.Sp) -> P.H:
  match s:
    case S.Sp{h, map}:
      h
