import Base
import ./kprim.bend as P

# The kernel's rewrites, generated from the rule table (spike/rules.bend)
# by spike/tools/gen_krules.bend; do not edit. scripts/check.sh fails if
# this file differs from what the generator writes. Two families: the
# plain one on the net alone, and the eager one (`.e`), which notes on a
# strategy's stack each link it makes between two principal ports.

# ports by kind code (R.arity)
def kind_arity(+k: U32) -> U32:
  match k:
    case 0:
      0
    case 1:
      3
    case 2:
      3
    case 3:
      3
    case 4:
      3
    case 5:
      1
    case 6:
      1
    case 7:
      1
    case 8:
      1
    case 9:
      2
    case 10:
      2
    case 11:
      2
    case _:
      0

# is the principal port negative? (R.port_pol)
def kind_neg(+k: U32) -> Bool:
  match k:
    case 0:
      False{}
    case 1:
      False{}
    case 2:
      True{}
    case 3:
      True{}
    case 4:
      False{}
    case 5:
      False{}
    case 6:
      True{}
    case 7:
      False{}
    case 8:
      True{}
    case 9:
      True{}
    case 10:
      True{}
    case 11:
      False{}
    case _:
      False{}

# when the rule leaves A, negative principal, meeting B as it is (R.rule):
# 0 never, 1 always, 2 when the payload test fails, 3 when it passes
def stuck_by(+ka: U32, +kb: U32) -> U32:
  match ka kb:
    case 2 1:
      2
    case 2 4:
      0
    case 2 5:
      2
    case 2 7:
      0
    case 2 11:
      0
    case 3 1:
      0
    case 3 4:
      0
    case 3 5:
      0
    case 3 7:
      0
    case 3 11:
      0
    case 6 1:
      0
    case 6 4:
      0
    case 6 5:
      0
    case 6 7:
      0
    case 6 11:
      0
    case 8 11:
      0
    case 9 4:
      0
    case 9 5:
      0
    case 9 7:
      0
    case 9 11:
      0
    case 10 1:
      0
    case 10 4:
      0
    case 10 5:
      0
    case 10 7:
      0
    case 10 11:
      0
    case _ _:
      1

# the level checks the rewrites below make, for the kernel's interpreter
def check(+ka: U32, +kb: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H:
  match ka kb:
    case 2 11:
      P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h)
    case 3 1:
      P.err_if(P.copy_fn_bad(ha, hb), h)
    case 3 11:
      P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h)
    case 10 1:
      P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h)
    case 10 4:
      P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h)
    case 10 11:
      P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)) || P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h)
    case _ _:
      h

# the most active pairs one rewrite makes (R.pairs_made, over the table):
# a strategy's stack keeps room for that many before each rewrite (P.pop)
def most_pairs() -> U32:
  4

# the payload test that picks a rule's variant where the two differ (R.rule's
# t; net.bend's rule_test), a copy for each family: shared, it has two
# callers, and the compiler folds it into neither, which cost the eager
# chain 5% to 12% (heap-strategies.stack). A Lift facing a LiftC is tested
# after peeling instead (P.peel_ctl).
def test.k(+ka: U32, +kb: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  match ka kb:
    case 2 1:
      (h, P.same_lvl(ha, hb))
    case 2 5:
      P.val_is_fn(h, P.form(hb), P.fld(hb), pb)
    case 3 4:
      (h, P.same_lvl(ha, hb))
    case _ _:
      (h, False{})

def test(h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  test.k(P.rk(ha), P.rk(hb), h, ha, hb, pa, pb)

def test.k.e(+ka: U32, +kb: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  match ka kb:
    case 2 1:
      (h, P.same_lvl(ha, hb))
    case 2 5:
      P.val_is_fn(h, P.form(hb), P.fld(hb), pb)
    case 3 4:
      (h, P.same_lvl(ha, hb))
    case _ _:
      (h, False{})

def test.e(h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  test.k.e(P.rk(ha), P.rk(hb), h, ha, hb, pa, pb)

# does A, negative principal, meeting B make more nodes than the two it
# frees? (R.rule; the pairs a two-stack strategy defers)
def grows(+ka: U32, +kb: U32, +ha: U32, +hb: U32) -> Bool:
  match ka kb:
    case 2 4:
      True{}
    case 2 11:
      True{}
    case 3 1:
      True{}
    case 3 4:
      Bool.not(P.same_lvl(ha, hb))
    case 3 11:
      True{}
    case 9 4:
      True{}
    case 10 1:
      True{}
    case 10 4:
      True{}
    case _ _:
      False{}

def rw.Ap.Fn.yes(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  P.fuse(P.fuse(P.link(P.link(P.fresh2(h, a, b), e0, e3), e1, e2), e0), e1)

def rw.Ap.Merge.k4(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> P.H:
  (h, +n3) = r
  P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e3), n2, e0), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), n3, e1), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32))

def rw.Ap.Merge.k3(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  rw.Ap.Merge.k4(P.node(h, P.hd2(4, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Ap.Merge.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Ap.Merge.k3(P.node(h, P.hd2(3, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.Merge.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Ap.Merge.k2(P.node(h, P.hd2(2, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.Merge(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Ap.Merge.k1(P.node(P.fresh2(h, a, b), P.hd2(2, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.Data.yes.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(P.link(h, n0, e0), (n0 + 1 : U32), e1)

def rw.Ap.Data.yes(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Ap.Data.yes.k1(P.node(P.fresh2(h, a, b), P.hd2(9, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.EraP.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.link(P.link(h, n0, e0), n1, e1)

def rw.Ap.EraP.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Ap.EraP.k2(P.node(h, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.EraP(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Ap.EraP.k1(P.node(P.fresh2(h, a, b), P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.LiftC.k3(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), e0), e1)

def rw.Ap.LiftC.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Ap.LiftC.k3(P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.LiftC.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Ap.LiftC.k2(P.node(h, P.hd2(10, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.LiftC(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Ap.LiftC.k1(P.node(P.fresh2(h, a, b), P.hd2(2, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Fn.k4(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> P.H:
  (h, +n3) = r
  P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), e2, n2), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), e3, n3), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32))

def rw.Copy.Fn.k3(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  rw.Copy.Fn.k4(P.node(h, P.hd2(4, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Copy.Fn.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Copy.Fn.k3(P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.Fn.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Copy.Fn.k2(P.node(h, P.hd2(1, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Fn(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Copy.Fn.k1(P.node(P.fresh2(h, a, b), P.hd2(1, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Merge.yes(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  P.fuse(P.fuse(P.link(P.link(P.fresh2(h, a, b), e0, e2), e1, e3), e0), e1)

def rw.Copy.Merge.no.k4(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> P.H:
  (h, +n3) = r
  P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), n2, e2), n3, e3), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32))

def rw.Copy.Merge.no.k3(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  rw.Copy.Merge.no.k4(P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Copy.Merge.no.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Copy.Merge.no.k3(P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.Merge.no.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Copy.Merge.no.k2(P.node(h, P.hd2(4, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Merge.no(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Copy.Merge.no.k1(P.node(P.fresh2(h, a, b), P.hd2(4, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Data.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.link(P.link(h, n0, e0), n1, e1)

def rw.Copy.Data.k2.pre(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +dw) = r
  rw.Copy.Data.k2(P.node(h, P.hd2(5, P.form(hb), P.fld(hb)), dw), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Data.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Copy.Data.k2.pre(P.dup(h, P.form(hb), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Data(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Copy.Data.k1(P.node(P.fresh2(h, a, b), P.hd2(5, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.EraP.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.link(P.link(h, n0, e0), n1, e1)

def rw.Copy.EraP.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Copy.EraP.k2(P.node(h, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.EraP(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Copy.EraP.k1(P.node(P.fresh2(h, a, b), P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.LiftC.k3(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), e0), e1)

def rw.Copy.LiftC.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Copy.LiftC.k3(P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.LiftC.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Copy.LiftC.k2(P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.LiftC(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Copy.LiftC.k1(P.node(P.fresh2(h, a, b), P.hd2(3, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Fn.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.link(P.link(h, n0, e2), n1, e3)

def rw.EraN.Fn.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.EraN.Fn.k2(P.node(h, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.EraN.Fn(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.EraN.Fn.k1(P.node(P.fresh2(h, a, b), P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Merge.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.link(P.link(h, n0, e2), n1, e3)

def rw.EraN.Merge.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.EraN.Merge.k2(P.node(h, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.EraN.Merge(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.EraN.Merge.k1(P.node(P.fresh2(h, a, b), P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Data(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  P.drop(P.fresh2(h, a, b), P.form(hb), pb)

def rw.EraN.EraP(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  P.fresh2(h, a, b)

def rw.EraN.LiftC.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, n0, e2)

def rw.EraN.LiftC(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.EraN.LiftC.k1(P.node(P.fresh2(h, a, b), P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Root.LiftC.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, n0, e2)

def rw.Root.LiftC(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Root.LiftC.k1(P.node(P.fresh2(h, a, b), P.hd(8, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Merge.k3(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e3), n2, e0), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32))

def rw.Call.Merge.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Call.Merge.k3(P.node(h, P.hd2(4, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Call.Merge.k2.pre(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +dw) = r
  rw.Call.Merge.k2(P.node(h, P.hd2(9, P.form(ha), P.fld(ha)), dw), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.Merge.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Call.Merge.k2.pre(P.dup(h, P.form(ha), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.Merge(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Call.Merge.k1(P.node(P.fresh2(h, a, b), P.hd2(9, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Data.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, n0, e0)

def rw.Call.Data.k1.pre(r: P.H & P.PW, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, pw) = r
  rw.Call.Data.k1(P.node_pw(h, 5, pw), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Data(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Call.Data.k1.pre(P.apply(P.fresh2(h, a, b), ha, pa, hb, pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.EraP.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, n0, e0)

def rw.Call.EraP(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Call.EraP.k1(P.node(P.drop(P.fresh2(h, a, b), P.form(ha), pa), P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.LiftC.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.fuse(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), e0)

def rw.Call.LiftC.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Call.LiftC.k2(P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.LiftC(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Call.LiftC.k1(P.node(P.fresh2(h, a, b), P.hd2(9, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Fn.k3(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e3), (n2 + 1 : U32), (n0 + 2 : U32)), e2), e3)

def rw.Lift.Fn.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Lift.Fn.k3(P.node(h, P.hd2(11, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Lift.Fn.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Lift.Fn.k2(P.node(h, P.hd2(10, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.Fn(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Lift.Fn.k1(P.node(P.fresh2(h, a, b), P.hd2(1, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Merge.k3(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e3), (n2 + 1 : U32), (n0 + 2 : U32)), e2), e3)

def rw.Lift.Merge.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Lift.Merge.k3(P.node(h, P.hd2(10, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Lift.Merge.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Lift.Merge.k2(P.node(h, P.hd2(10, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.Merge(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Lift.Merge.k1(P.node(P.fresh2(h, a, b), P.hd2(4, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Data.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, n0, e0)

def rw.Lift.Data(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Lift.Data.k1(P.node(P.fresh2(h, a, b), P.hd2(5, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.EraP.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, n0, e0)

def rw.Lift.EraP(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Lift.EraP.k1(P.node(P.fresh2(h, a, b), P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.LiftC.yes(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  P.fuse(P.link(P.fresh2(h, a, b), e0, e2), e0)

def rw.Lift.LiftC.no.k2(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.fuse(P.fuse(P.link(P.link(P.link(h, n0, e2), (n0 + 1 : U32), (n1 + 1 : U32)), n1, e0), e2), e0)

def rw.Lift.LiftC.no.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Lift.LiftC.no.k2(P.node(h, P.hd2(11, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.LiftC.no(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Lift.LiftC.no.k1(P.node(P.fresh2(h, a, b), P.hd2(10, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.LiftC.peeled(r: P.Pl, +a: U32, +b: U32, +ha: U32, +hb: U32, +e1: U32, +e3: U32) -> P.H:
  match r:
    case P.Pl{h, +t, +pa, +pb, +e0, +e2}:
      match t:
        case True{}:
          rw.Lift.LiftC.yes(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Lift.LiftC.no(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.Fn.yes.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  P.E{P.fuse(P.fuse(P.link(P.link(P.fresh2(h, a, b), e0, e3), e1, e2), e0), e1), P.note(P.note(st, e0, e3), e1, e2)}

def rw.Ap.Merge.e.k4(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> P.E:
  (h, +n3) = r
  P.E{P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e3), n2, e0), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), n3, e1), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32)), P.note(P.note(P.note(P.note(st, n0, e2), n1, e3), n2, e0), n3, e1)}

def rw.Ap.Merge.e.k3(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  rw.Ap.Merge.e.k4(P.node(h, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Ap.Merge.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Ap.Merge.e.k3(P.node(h, P.hd2(3, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.Merge.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Ap.Merge.e.k2(P.node(h, P.hd2(2, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.Merge.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Ap.Merge.e.k1(P.node(P.fresh2(h, a, b), P.hd2(2, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.Data.yes.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(P.link(h, n0, e0), (n0 + 1 : U32), e1), P.note(st, n0, e0)}

def rw.Ap.Data.yes.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Ap.Data.yes.e.k1(P.node(P.fresh2(h, a, b), P.hd2(9, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.EraP.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.link(P.link(h, n0, e0), n1, e1), P.note(P.note(st, n0, e0), n1, e1)}

def rw.Ap.EraP.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Ap.EraP.e.k2(P.node(h, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.EraP.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Ap.EraP.e.k1(P.node(P.fresh2(h, a, b), P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.LiftC.e.k3(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), e0), e1), P.note(P.note(P.note(st, n0, e2), n1, e0), n2, e1)}

def rw.Ap.LiftC.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Ap.LiftC.e.k3(P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.LiftC.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Ap.LiftC.e.k2(P.node(h, P.hd2(10, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.LiftC.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Ap.LiftC.e.k1(P.node(P.fresh2(h, a, b), P.hd2(2, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Fn.e.k4(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> P.E:
  (h, +n3) = r
  P.E{P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), e2, n2), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), e3, n3), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32)), P.note(P.note(P.note(P.note(st, n0, e0), n1, e1), e2, n2), e3, n3)}

def rw.Copy.Fn.e.k3(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  rw.Copy.Fn.e.k4(P.node(h, P.hd2(4, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Copy.Fn.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Copy.Fn.e.k3(P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.Fn.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Copy.Fn.e.k2(P.node(h, P.hd2(1, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Fn.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Copy.Fn.e.k1(P.node(P.fresh2(h, a, b), P.hd2(1, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Merge.yes.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  P.E{P.fuse(P.fuse(P.link(P.link(P.fresh2(h, a, b), e0, e2), e1, e3), e0), e1), P.note(P.note(st, e0, e2), e1, e3)}

def rw.Copy.Merge.no.e.k4(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> P.E:
  (h, +n3) = r
  P.E{P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), n2, e2), n3, e3), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32)), P.note(P.note(P.note(P.note(st, n0, e0), n1, e1), n2, e2), n3, e3)}

def rw.Copy.Merge.no.e.k3(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  rw.Copy.Merge.no.e.k4(P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Copy.Merge.no.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Copy.Merge.no.e.k3(P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.Merge.no.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Copy.Merge.no.e.k2(P.node(h, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Merge.no.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Copy.Merge.no.e.k1(P.node(P.fresh2(h, a, b), P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Data.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.link(P.link(h, n0, e0), n1, e1), P.note(P.note(st, n0, e0), n1, e1)}

def rw.Copy.Data.e.k2.pre(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +dw) = r
  rw.Copy.Data.e.k2(P.node(h, P.hd2(5, P.form(hb), P.fld(hb)), dw), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Data.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Copy.Data.e.k2.pre(P.dup(h, P.form(hb), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Data.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Copy.Data.e.k1(P.node(P.fresh2(h, a, b), P.hd2(5, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.EraP.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.link(P.link(h, n0, e0), n1, e1), P.note(P.note(st, n0, e0), n1, e1)}

def rw.Copy.EraP.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Copy.EraP.e.k2(P.node(h, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.EraP.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Copy.EraP.e.k1(P.node(P.fresh2(h, a, b), P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.LiftC.e.k3(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), e0), e1), P.note(P.note(P.note(st, n0, e2), n1, e0), n2, e1)}

def rw.Copy.LiftC.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Copy.LiftC.e.k3(P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.LiftC.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Copy.LiftC.e.k2(P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.LiftC.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Copy.LiftC.e.k1(P.node(P.fresh2(h, a, b), P.hd2(3, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Fn.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.link(P.link(h, n0, e2), n1, e3), P.note(P.note(st, n0, e2), n1, e3)}

def rw.EraN.Fn.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.EraN.Fn.e.k2(P.node(h, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.EraN.Fn.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.EraN.Fn.e.k1(P.node(P.fresh2(h, a, b), P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Merge.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.link(P.link(h, n0, e2), n1, e3), P.note(P.note(st, n0, e2), n1, e3)}

def rw.EraN.Merge.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.EraN.Merge.e.k2(P.node(h, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.EraN.Merge.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.EraN.Merge.e.k1(P.node(P.fresh2(h, a, b), P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Data.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  P.E{P.drop(P.fresh2(h, a, b), P.form(hb), pb), st}

def rw.EraN.EraP.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  P.E{P.fresh2(h, a, b), st}

def rw.EraN.LiftC.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, n0, e2), P.note(st, n0, e2)}

def rw.EraN.LiftC.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.EraN.LiftC.e.k1(P.node(P.fresh2(h, a, b), P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Root.LiftC.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, n0, e2), P.note(st, n0, e2)}

def rw.Root.LiftC.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Root.LiftC.e.k1(P.node(P.fresh2(h, a, b), P.hd(8, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Merge.e.k3(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e3), n2, e0), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), P.note(P.note(P.note(st, n0, e2), n1, e3), n2, e0)}

def rw.Call.Merge.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Call.Merge.e.k3(P.node(h, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Call.Merge.e.k2.pre(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +dw) = r
  rw.Call.Merge.e.k2(P.node(h, P.hd2(9, P.form(ha), P.fld(ha)), dw), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.Merge.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Call.Merge.e.k2.pre(P.dup(h, P.form(ha), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.Merge.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Call.Merge.e.k1(P.node(P.fresh2(h, a, b), P.hd2(9, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Data.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, n0, e0), P.note(st, n0, e0)}

def rw.Call.Data.e.k1.pre(r: P.H & P.PW, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, pw) = r
  rw.Call.Data.e.k1(P.node_pw(h, 5, pw), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Data.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Call.Data.e.k1.pre(P.apply(P.fresh2(h, a, b), ha, pa, hb, pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.EraP.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, n0, e0), P.note(st, n0, e0)}

def rw.Call.EraP.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Call.EraP.e.k1(P.node(P.drop(P.fresh2(h, a, b), P.form(ha), pa), P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.LiftC.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.fuse(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), e0), P.note(P.note(st, n0, e2), n1, e0)}

def rw.Call.LiftC.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Call.LiftC.e.k2(P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.LiftC.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Call.LiftC.e.k1(P.node(P.fresh2(h, a, b), P.hd2(9, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Fn.e.k3(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e3), (n2 + 1 : U32), (n0 + 2 : U32)), e2), e3), P.note(P.note(P.note(st, n0, e0), n1, e2), n2, e3)}

def rw.Lift.Fn.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Lift.Fn.e.k3(P.node(h, P.hd2(11, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Lift.Fn.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Lift.Fn.e.k2(P.node(h, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.Fn.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Lift.Fn.e.k1(P.node(P.fresh2(h, a, b), P.hd2(1, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Merge.e.k3(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e3), (n2 + 1 : U32), (n0 + 2 : U32)), e2), e3), P.note(P.note(P.note(st, n0, e0), n1, e2), n2, e3)}

def rw.Lift.Merge.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Lift.Merge.e.k3(P.node(h, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Lift.Merge.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Lift.Merge.e.k2(P.node(h, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.Merge.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Lift.Merge.e.k1(P.node(P.fresh2(h, a, b), P.hd2(4, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Data.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, n0, e0), P.note(st, n0, e0)}

def rw.Lift.Data.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Lift.Data.e.k1(P.node(P.fresh2(h, a, b), P.hd2(5, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.EraP.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, n0, e0), P.note(st, n0, e0)}

def rw.Lift.EraP.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Lift.EraP.e.k1(P.node(P.fresh2(h, a, b), P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.LiftC.yes.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  P.E{P.fuse(P.link(P.fresh2(h, a, b), e0, e2), e0), P.note(st, e0, e2)}

def rw.Lift.LiftC.no.e.k2(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.fuse(P.fuse(P.link(P.link(P.link(h, n0, e2), (n0 + 1 : U32), (n1 + 1 : U32)), n1, e0), e2), e0), P.note(P.note(st, n0, e2), n1, e0)}

def rw.Lift.LiftC.no.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Lift.LiftC.no.e.k2(P.node(h, P.hd2(11, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.LiftC.no.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Lift.LiftC.no.e.k1(P.node(P.fresh2(h, a, b), P.hd2(10, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.LiftC.peeled.e(r: P.Pl, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +e1: U32, +e3: U32) -> P.E:
  match r:
    case P.Pl{h, +t, +pa, +pb, +e0, +e2}:
      match t:
        case True{}:
          rw.Lift.LiftC.yes.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Lift.LiftC.no.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

# the rewrite for A, negative principal, meeting B; t is the payload test
def rewrite(+ka: U32, +kb: U32, +t: Bool, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  match ka kb:
    case 2 1:
      match t:
        case True{}:
          rw.Ap.Fn.yes(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          P.err_if(U32.is_ne(ka, 8), h)
    case 2 4:
      rw.Ap.Merge(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 5:
      match t:
        case True{}:
          rw.Ap.Data.yes(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          P.err_if(U32.is_ne(ka, 8), h)
    case 2 7:
      rw.Ap.EraP(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 11:
      rw.Ap.LiftC(P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 1:
      rw.Copy.Fn(P.err_if(P.copy_fn_bad(ha, hb), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 4:
      match t:
        case True{}:
          rw.Copy.Merge.yes(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Copy.Merge.no(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 5:
      rw.Copy.Data(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 7:
      rw.Copy.EraP(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 11:
      rw.Copy.LiftC(P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 1:
      rw.EraN.Fn(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 4:
      rw.EraN.Merge(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 5:
      rw.EraN.Data(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 7:
      rw.EraN.EraP(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 11:
      rw.EraN.LiftC(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 8 11:
      rw.Root.LiftC(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 4:
      rw.Call.Merge(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 5:
      rw.Call.Data(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 7:
      rw.Call.EraP(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 11:
      rw.Call.LiftC(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 1:
      rw.Lift.Fn(P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 4:
      rw.Lift.Merge(P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 5:
      rw.Lift.Data(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 7:
      rw.Lift.EraP(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 11:
      rw.Lift.LiftC.peeled(P.peel_ctl(P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)) || P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), a, b, ha, hb, pa, pb, e0, e2), a, b, ha, hb, e1, e3)
    case _ _:
      P.err_if(U32.is_ne(ka, 8), h)

# the same, noting the pairs it makes on the strategy's stack
def rewrite.e(+ka: U32, +kb: U32, +t: Bool, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  match ka kb:
    case 2 1:
      match t:
        case True{}:
          rw.Ap.Fn.yes.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          P.E{P.err_if(U32.is_ne(ka, 8), h), st}
    case 2 4:
      rw.Ap.Merge.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 5:
      match t:
        case True{}:
          rw.Ap.Data.yes.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          P.E{P.err_if(U32.is_ne(ka, 8), h), st}
    case 2 7:
      rw.Ap.EraP.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 11:
      rw.Ap.LiftC.e(P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 1:
      rw.Copy.Fn.e(P.err_if(P.copy_fn_bad(ha, hb), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 4:
      match t:
        case True{}:
          rw.Copy.Merge.yes.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Copy.Merge.no.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 5:
      rw.Copy.Data.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 7:
      rw.Copy.EraP.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 11:
      rw.Copy.LiftC.e(P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 1:
      rw.EraN.Fn.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 4:
      rw.EraN.Merge.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 5:
      rw.EraN.Data.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 7:
      rw.EraN.EraP.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 11:
      rw.EraN.LiftC.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 8 11:
      rw.Root.LiftC.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 4:
      rw.Call.Merge.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 5:
      rw.Call.Data.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 7:
      rw.Call.EraP.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 11:
      rw.Call.LiftC.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 1:
      rw.Lift.Fn.e(P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 4:
      rw.Lift.Merge.e(P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 5:
      rw.Lift.Data.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 7:
      rw.Lift.EraP.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 11:
      rw.Lift.LiftC.peeled.e(P.peel_ctl(P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)) || P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), a, b, ha, hb, pa, pb, e0, e2), st, a, b, ha, hb, e1, e3)
    case _ _:
      P.E{P.err_if(U32.is_ne(ka, 8), h), st}

