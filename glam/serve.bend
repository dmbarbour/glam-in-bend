# A serve's writes composed (the CursorLaws plan's
# cursor-laws.materializer): the copy the splice makes, its crossings
# (R.crossings, joining the holes to the cursors the index finds or making
# them cursors), then, at the source's root, the served cursor leaving,
# the copy's root port linked in its place. Out of glam/materialize.bend so
# that the serve's laws (glam/SERVE_LAWS.bend) state the materializer's
# own composition, importing the heap's primitives, the splice, the
# cursors and the template alone (laws-over-tests).
import Base
import ../spike/tpl.bend as T
import ../spike/kprim.bend as P
import ./splice_copy.bend as S
import ./ring.bend as R

# the copy's root, where the tree faced the source's interface (a first
# copy): joined to the served cursor nc, which leaves the index
def rt.e(r: Array<U32> & U32, h: P.H, +p: U32, +nc: U32) -> P.H:
  (map, +n) = r
  R.leave(h, (n + p : U32), nc)

def rt(+at_root: Bool, map: Array<U32>, h: P.H, root: T.TEnd, +nc: U32) -> P.H:
  match at_root:
    case True{}:
      match root:
        case T.TE{+n, +p}:
          rt.e(Array.get(U32, map, n), h, p, nc)
    case False{}:
      h

def serve.r(q: Array<U32> & P.H, root: T.TEnd, +nc: U32, +at_root: Bool) -> P.H:
  (map, h) = q
  rt(at_root, map, h, root, nc)

# the copy s, its crossings curs joined through situating node situ's
# index, then the root's leave where at_root
def serve(s: S.Sp, curs: List<&2, R.FzC>, root: T.TEnd, +situ: U32, +nc: U32, +at_root: Bool) -> P.H:
  match s:
    case S.Sp{h, map}:
      serve.r(R.crossings(curs, (map, h), situ), root, nc, at_root)
