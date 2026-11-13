import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/kprim.bend as P
import ../spike/kernel.bend as K
import ../spike/knet.bend as KN
import ../spike/kdemand.bend as KD
import ./position.bend as Q

# Positioned demand on small sources (the Cells plan's
# cells-freeze.demand): each loaded, demanded at a position, and its end
# written out: a value and the kind facing the position, the frontier
# and the port reached, a static, or the walk's own stop. A template's
# node i is the net's node i + 8, so its function at node 0 has its
# result at reference 33 and its variable at 34; the interface is 28.
# Run by scripts/ladder.py, which expects `ok` alone.
#
#   bend glam/test_position.bend

def fn() -> T.TNode:
  T.TN{R.KFn{}, V.PNone{}}

def ap() -> T.TNode:
  T.TN{R.KAp{}, V.PNone{}}

def num(+n: U32) -> T.TNode:
  T.TN{R.KData{}, V.PVal{V.VNum{n}}}

def ln(+a: U32, +p: U32, +b: U32, +q: U32) -> T.TLink:
  T.TL{T.TE{a, p}, T.TE{b, q}}

# `\x -> (\y -> y) x`: the beta wires the result to the variable, a
# finished node's port: the frontier at 34, nothing materialized
def id_redex() -> T.Tpl:
  T.Tpl{[fn(), ap(), fn()], [ln(0, 1, 1, 2), ln(1, 0, 2, 0), ln(1, 1, 0, 2), ln(2, 1, 2, 2)], T.TE{0, 0}, 3}

# `\x -> (\y -> \z -> z) x`: the beta leaves a function facing the result
def const_redex() -> T.Tpl:
  T.Tpl{[fn(), ap(), fn(), fn(), T.TN{R.KEraN{}, V.PNone{}}],
    [ln(0, 1, 1, 2), ln(1, 0, 2, 0), ln(1, 1, 0, 2), ln(2, 1, 3, 0), ln(2, 2, 4, 0), ln(3, 1, 3, 2)], T.TE{0, 0}, 5}

# `\x -> (g c) x`, g a handle: a need
def gcx() -> T.Tpl:
  T.Tpl{[fn(), ap(), ap(), T.TN{R.KData{}, V.PVal{V.VLazy{5}}}, num(1)],
    [ln(0, 1, 1, 2), ln(1, 0, 2, 2), ln(1, 1, 0, 2), ln(2, 0, 3, 0), ln(2, 1, 4, 0)], T.TE{0, 0}, 5}

def kind_at.r(r: P.H & U32) -> String:
  (h, +hd) = r
  U32.show(P.rk(hd))

def st_of(d: KD.D) -> U32:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      st

def show(p: Q.Pd) -> String:
  match p:
    case Q.PdValue{h, +q, +n}:
      "value " ++ kind_at.r(P.rd(h, P.base(q)))
    case Q.PdFront{h, +q, +n}:
      "front " ++ U32.show(q)
    case Q.PdStatic{h, +n}:
      "static"
    case Q.PdStop{d, +n}:
      "stop " ++ K.st_name(st_of(d))

def at(t: T.Tpl, +pos: U32) -> String:
  show(Q.positioned(KN.load(t), pos, 16n, 1000n))

def check.k(+same: Bool, got: String, want: String, name: String) -> String:
  match same:
    case True{}:
      ""
    case False{}:
      name ++ ": got " ++ got ++ ", want " ++ want ++ "\n"

def check(+got: String, +want: String, name: String) -> String:
  check.k(String.eq(got, want), got, want, name)

def report.k(+none: Bool, s: String) -> String:
  match none:
    case True{}:
      "ok"
    case False{}:
      s

def report(+s: String) -> String:
  report.k(String.eq(s, ""), s)

def main() -> String:
  report(
    check(at(id_redex(), 33), "front 34", "id_redex") ++
    check(at(const_redex(), 33), "value 1", "const_redex") ++
    check(at(gcx(), 33), "stop needs", "gcx") ++
    check(at(id_redex(), 28), "value 1", "root"))
