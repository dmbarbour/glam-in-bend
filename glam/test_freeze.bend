import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/net.bend as N
import ../spike/kprim.bend as P
import ../spike/knet.bend as KN
import ./freeze.bend as F

# Freezing on small templates (the Cells plan's `cells-freeze.cursors`):
# each loaded and frozen back, the template it gives written out and
# compared with what it must be. The ladder's round trip (`--refreeze`)
# covers the templates lowering makes; these cover what it never makes
# and live nets will: a function whose result is wired straight to its
# own variable (the identity without a control), a static eraser at a
# port, a level, a control's index and offset, a value. Run by
# scripts/ladder.py, which expects `ok` alone.
#
#   bend glam/test_freeze.bend

def sh.u(+n: U32) -> String:
  U32.show(n)

def sh.up(+up: Bool) -> String:
  match up:
    case True{}:
      "+"
    case False{}:
      "-"

def sh.val(v: V.Val) -> String:
  match v:
    case V.VNum{+n}:
      "#" ++ sh.u(n)
    case _:
      "?"

def sh.pay(p: V.Pay) -> String:
  match p:
    case V.PNone{}:
      "-"
    case V.PLvl{+n}:
      "l" ++ sh.u(n)
    case V.PLift{+n, +up, +by}:
      "c" ++ sh.u(n) ++ sh.up(up) ++ sh.u(by)
    case V.PVal{v}:
      sh.val(v)
    case V.PFan{f}:
      "fan"

def sh.node(t: T.TNode) -> String:
  match t:
    case T.TN{k, p}:
      sh.u(N.kcode(k)) ++ ":" ++ sh.pay(p)
    case T.TF{k, +site, +lvl}:
      sh.u(N.kcode(k)) ++ "f" ++ sh.u(site) ++ "/" ++ sh.u(lvl)

def sh.end(e: T.TEnd) -> String:
  match e:
    case T.TE{+n, +p}:
      sh.u(n) ++ "." ++ sh.u(p)

def sh.link(l: T.TLink) -> String:
  match l:
    case T.TL{a, b}:
      sh.end(a) ++ "-" ++ sh.end(b)

def sh.nodes(ts: List<&2, T.TNode>) -> String:
  match ts:
    case Nil{}:
      ""
    case Con{t, rest}:
      sh.node(t) ++ " " ++ sh.nodes(rest)

def sh.links(ls: List<&2, T.TLink>) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{l, rest}:
      sh.link(l) ++ " " ++ sh.links(rest)

def sh.tpl(t: T.Tpl) -> String:
  match t:
    case T.Tpl{nodes, links, root, +size}:
      "[" ++ sh.nodes(nodes) ++ "| " ++ sh.links(links) ++ "| " ++ sh.end(root) ++ " " ++ sh.u(size) ++ "]"

def frozen.r(r: P.H & T.Tpl) -> String:
  (h, t) = r
  sh.tpl(t)

def frozen(t: T.Tpl) -> String:
  frozen.r(F.freeze(KN.load(t)))

# the identity with no control: the function's result (port 1) wired to
# its variable (port 2), one wire with both ends on one node
def id_bare() -> T.Tpl:
  T.Tpl{[T.TN{R.KFn{}, V.PNone{}}], [T.TL{T.TE{0, 1}, T.TE{0, 2}}], T.TE{0, 0}, 1}

# `\x -> 7` at level 2, its variable erased: the eraser static once loaded
def const_lvl() -> T.Tpl:
  T.Tpl{[T.TN{R.KFn{}, V.PLvl{2}}, T.TN{R.KData{}, V.PVal{V.VNum{7}}}, T.TN{R.KEraN{}, V.PNone{}}],
    [T.TL{T.TE{0, 1}, T.TE{1, 0}}, T.TL{T.TE{0, 2}, T.TE{2, 0}}], T.TE{0, 0}, 3}

# `\x -> x` at level 1 with a control between variable and result, as
# lowering makes it: a lift at index 1 raising by 3
def id_lift() -> T.Tpl:
  T.Tpl{[T.TN{R.KFn{}, V.PLvl{1}}, T.TN{R.KLift{}, V.PLift{1, True{}, 3}}],
    [T.TL{T.TE{0, 2}, T.TE{1, 0}}, T.TL{T.TE{1, 1}, T.TE{0, 1}}], T.TE{0, 0}, 2}

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
    check(frozen(id_bare()), "[1:- | 0.1-0.2 | 0.0 1]", "id_bare") ++
    check(frozen(const_lvl()), "[1:l2 5:#7 6:- | 0.2-2.0 0.1-1.0 | 0.0 3]", "const_lvl") ++
    check(frozen(id_lift()), "[1:l1 10:c1+3 | 0.2-1.0 0.1-1.1 | 0.0 2]", "id_lift"))
