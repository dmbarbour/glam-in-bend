import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/kprim.bend as P
import ../spike/knet.bend as KN
import ./freeze.bend as F

# A control a copy has taken is left alone by fusion (the Cells plan's
# cells-freeze.cells; copied-controls-unfused): freezing a source's
# finished part marks each control it takes, and fusion refuses a marked
# control (law marked_unfused). Checked on the kernel's own code:
# - two raises in series, (0, +1) then (1, +1), fuse into (0, +2);
# - with either marked, they do not;
# - a LiftC at a source's interface, taken by freezing the finished tree
#   under it, is marked; read back whole, it is not.
# Run by scripts/ladder.py, which expects `ok` alone.
#
#   bend glam/test_mark.bend

def num(+n: U32) -> T.TNode:
  T.TN{R.KData{}, V.PVal{V.VNum{n}}}

def ctl(k: R.NodeKind, +n: U32) -> T.TNode:
  T.TN{k, V.PLift{n, True{}, 1}}

def ln(+a: U32, +p: U32, +b: U32, +q: U32) -> T.TLink:
  T.TL{T.TE{a, p}, T.TE{b, q}}

# Lift p (node 0, base 32) feeding Lift l (node 1, base 36): p's out to
# l's in, a value at p's in, the interface at l's out
def lifts() -> T.Tpl:
  T.Tpl{[ctl(R.KLift{}, 0), ctl(R.KLift{}, 1), num(5)], [ln(0, 1, 1, 0), ln(0, 0, 2, 0)], T.TE{1, 1}, 3}

# a LiftC (node 0, base 32) at the interface, a value at its in
def at_root() -> T.Tpl:
  T.Tpl{[ctl(R.KLiftC{}, 0), num(5)], [ln(0, 1, 1, 0)], T.TE{0, 0}, 2}

def hdr_mark(r: P.H & U32, +b: U32) -> P.H:
  (h, +hd) = r
  P.wr(h, b, P.mark(hd))

# node base b marked
def marked_at(h: P.H, +b: U32) -> P.H:
  hdr_mark(P.rd(h, b), b)

def amt(r: P.H & U32) -> U32:
  (h, +o) = r
  P.off_by(o)

# the amount p's offset holds after fusion is tried
def fused_by(h: P.H) -> U32:
  amt(P.rd(P.fuse_lifts(h, 32, 36), 35))

def is_marked(r: P.H & U32) -> Bool:
  (h, +hd) = r
  P.marked(hd)

def tree_marks(r: P.H & F.Fz) -> Bool:
  (h, z) = r
  is_marked(P.rd(h, 32))

def whole_marks(r: P.H & T.Tpl) -> Bool:
  (h, t) = r
  is_marked(P.rd(h, 32))

def check.k(+same: Bool, got: String, want: String, name: String) -> String:
  match same:
    case True{}:
      ""
    case False{}:
      name ++ ": got " ++ got ++ ", want " ++ want ++ "\n"

def check(+got: String, +want: String, name: String) -> String:
  check.k(String.eq(got, want), got, want, name)

def bool_s(+b: Bool) -> String:
  match b:
    case True{}:
      "marked"
    case False{}:
      "unmarked"

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
    check(U32.show(fused_by(KN.load(lifts()))), "2", "unmarked raises fuse") ++
    check(U32.show(fused_by(marked_at(KN.load(lifts()), 32))), "1", "first marked") ++
    check(U32.show(fused_by(marked_at(KN.load(lifts()), 36))), "1", "second marked") ++
    check(bool_s(tree_marks(F.freeze_tree(KN.load(at_root()), 32))), "marked", "taken by a copy") ++
    check(bool_s(whole_marks(F.freeze(KN.load(at_root())))), "unmarked", "read back whole"))
