import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/kernel.bend as K
import ../spike/knet.bend as KN
import ../spike/kstrat.bend as KS
import ../spike/kdemand.bend as KD

# A negative cursor met by demand (the Cells plan's
# cells-freeze.cursors.kinds): a need, state 2, as a lazy handle met is,
# wherever demand meets it. These templates are small nets whose demand
# reaches a cursor through an application, a copy fan, a control, or at
# the interface itself; each must stop needing it, not stuck and not
# done. Run by scripts/ladder.py, which expects `ok` alone.
#
#   bend glam/test_cursor.bend

def cur() -> T.TNode:
  T.TN{R.KCur{}, V.PNone{}}

def num(+n: U32) -> T.TNode:
  T.TN{R.KData{}, V.PVal{V.VNum{n}}}

# the interface facing a cursor
def at_root() -> T.Tpl:
  T.Tpl{[cur()], Nil{}, T.TE{0, 0}, 1}

# an application whose function is a cursor, applied to 1
def under_ap() -> T.Tpl:
  T.Tpl{[T.TN{R.KAp{}, V.PNone{}}, cur(), num(1)],
    [T.TL{T.TE{0, 0}, T.TE{1, 0}}, T.TL{T.TE{0, 1}, T.TE{2, 0}}], T.TE{0, 2}, 3}

# a copy fan whose input is a cursor, one output the root, the other
# erased: the fan waits on the cursor rather than duplicating it
def under_copy() -> T.Tpl:
  T.Tpl{[T.TF{R.KCopy{}, 0, V.nolvl()}, cur(), T.TN{R.KEraN{}, V.PNone{}}],
    [T.TL{T.TE{0, 0}, T.TE{1, 0}}, T.TL{T.TE{0, 2}, T.TE{2, 0}}], T.TE{0, 1}, 3}

# a control whose source is a cursor
def under_lift() -> T.Tpl:
  T.Tpl{[T.TN{R.KLift{}, V.PLift{0, True{}, 1}}, cur()],
    [T.TL{T.TE{0, 0}, T.TE{1, 0}}], T.TE{0, 1}, 2}

def st_of(d: KD.D) -> U32:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      st

# the state demand ends in, at most 100 steps
def demanded(t: T.Tpl) -> String:
  K.st_name(st_of(K.demand_ev(0, 100n, KS.d.start(KN.load(t)))))

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
    check(demanded(at_root()), "needs", "at_root") ++
    check(demanded(under_ap()), "needs", "under_ap") ++
    check(demanded(under_copy()), "needs", "under_copy") ++
    check(demanded(under_lift()), "needs", "under_lift"))
