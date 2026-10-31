import Base
import ./kprim.bend as P
import ./net.bend as N

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
    case 12:
      2
    case 13:
      2
    case 14:
      2
    case 15:
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
    case 12:
      True{}
    case 13:
      True{}
    case 14:
      False{}
    case 15:
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
    case 2 14:
      0
    case 2 15:
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
    case 3 14:
      0
    case 3 15:
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
    case 6 14:
      0
    case 6 15:
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
    case 9 14:
      0
    case 9 15:
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
    case 10 14:
      0
    case 10 15:
      0
    case 12 1:
      0
    case 12 4:
      0
    case 12 5:
      0
    case 12 7:
      0
    case 12 11:
      0
    case 12 14:
      0
    case 12 15:
      0
    case 13 1:
      0
    case 13 4:
      0
    case 13 5:
      0
    case 13 7:
      0
    case 13 11:
      0
    case 13 14:
      0
    case 13 15:
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
    case 10 14:
      P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h)
    case 10 15:
      P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h)
    case 12 1:
      P.err_if(P.copy_fn_bad(ha, hb), h)
    case 12 11:
      P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h)
    case 13 1:
      P.err_if(P.copy_fn_bad(ha, hb), h)
    case 13 11:
      P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h)
    case _ _:
      h

# the most active pairs one rewrite makes (R.pairs_made, over the table):
# a strategy's stack keeps room for that many before each rewrite (P.pop)
def most_pairs() -> U32:
  4

# the payload test that picks a rule's variant where the two differ (R.rule's
# t; net.bend's rule_test), a copy for each family and, a template over
# what follows the rewrite, for each strategy's chain: shared, it has two
# callers, and the compiler folds it into neither, which cost the eager
# chain 5% to 12% (heap-strategies.stack). A Lift facing a LiftC is tested
# after peeling instead (P.peel_ctl).
def test.k(~after: P.H -> @+x:N.Ext -> P.H, +ka: U32, +kb: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  match ka kb:
    case 2 1:
      (h, P.same_lvl(ha, hb))
    case 2 5:
      P.val_is_fn(h, P.form(hb), P.fld(hb), pb)
    case 3 4:
      (h, P.same_lvl(ha, hb))
    case 3 14:
      (h, P.same_lvl(ha, hb))
    case 3 15:
      (h, P.same_lvl(ha, hb))
    case 12 4:
      (h, P.same_lvl(ha, hb))
    case 12 14:
      (h, P.same_lvl(ha, hb))
    case 12 15:
      (h, P.same_lvl(ha, hb))
    case 13 4:
      (h, P.same_lvl(ha, hb))
    case 13 14:
      (h, P.same_lvl(ha, hb))
    case 13 15:
      (h, P.same_lvl(ha, hb))
    case _ _:
      (h, False{})

def test(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  test.k(~after, P.rk(ha), P.rk(hb), h, ha, hb, pa, pb)

def test.k.e(~after: P.E -> @+x:N.Ext -> P.E, +ka: U32, +kb: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  match ka kb:
    case 2 1:
      (h, P.same_lvl(ha, hb))
    case 2 5:
      P.val_is_fn(h, P.form(hb), P.fld(hb), pb)
    case 3 4:
      (h, P.same_lvl(ha, hb))
    case 3 14:
      (h, P.same_lvl(ha, hb))
    case 3 15:
      (h, P.same_lvl(ha, hb))
    case 12 4:
      (h, P.same_lvl(ha, hb))
    case 12 14:
      (h, P.same_lvl(ha, hb))
    case 12 15:
      (h, P.same_lvl(ha, hb))
    case 13 4:
      (h, P.same_lvl(ha, hb))
    case 13 14:
      (h, P.same_lvl(ha, hb))
    case 13 15:
      (h, P.same_lvl(ha, hb))
    case _ _:
      (h, False{})

def test.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  test.k.e(~after, P.rk(ha), P.rk(hb), h, ha, hb, pa, pb)

# does A, negative principal, meeting B make more nodes than the two it
# frees? (R.rule; the pairs a two-stack strategy defers)
def grows(+ka: U32, +kb: U32, +ha: U32, +hb: U32) -> Bool:
  match ka kb:
    case 2 4:
      True{}
    case 2 11:
      True{}
    case 2 14:
      True{}
    case 2 15:
      True{}
    case 3 1:
      True{}
    case 3 4:
      Bool.not(P.same_lvl(ha, hb))
    case 3 11:
      True{}
    case 3 14:
      Bool.not(P.same_lvl(ha, hb))
    case 3 15:
      Bool.not(P.same_lvl(ha, hb))
    case 9 4:
      True{}
    case 10 1:
      True{}
    case 10 4:
      True{}
    case 12 1:
      True{}
    case 12 4:
      Bool.not(P.same_lvl(ha, hb))
    case 13 1:
      True{}
    case 13 4:
      Bool.not(P.same_lvl(ha, hb))
    case _ _:
      False{}

def rw.Ap.Fn.yes(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  after(P.fuse(P.fuse(P.link(P.link(P.fresh2(h, a, b), e0, e3), e1, e2), e0), e1), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Ap.Merge.k4(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> P.H:
  (h, +n3) = r
  P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e3), n2, e0), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), n3, e1), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32))

def rw.Ap.Merge.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  rw.Ap.Merge.k4(~after, P.node(h, P.hd2(4, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Ap.Merge.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Ap.Merge.k3(~after, P.node(h, P.hd2(3, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.Merge.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Ap.Merge.k2(~after, P.renode(h, b, P.hd2(2, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.Merge(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Ap.Merge.k1(~after, P.renode(h, a, P.hd2(2, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.Data.yes.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(P.link(h, n0, e0), (n0 + 1 : U32), e1)

def rw.Ap.Data.yes(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Ap.Data.yes.k1(~after, P.renode(P.free(h, b), a, P.hd2(9, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.EraP.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  after(P.link(P.link(h, n0, e0), n1, e1), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Ap.EraP.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Ap.EraP.k2(~after, P.renode(h, b, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.EraP(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Ap.EraP.k1(~after, P.renode(h, a, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.LiftC.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), e0), e1)

def rw.Ap.LiftC.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Ap.LiftC.k3(~after, P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.LiftC.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Ap.LiftC.k2(~after, P.renode(h, b, P.hd2(10, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.LiftC(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Ap.LiftC.k1(~after, P.renode(h, a, P.hd2(2, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.MergeL.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32))

def rw.Ap.MergeL.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Ap.MergeL.k3(~after, P.node(h, P.hd2(14, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.MergeL.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Ap.MergeL.k2(~after, P.renode(h, b, P.hd2(12, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.MergeL(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Ap.MergeL.k1(~after, P.renode(h, a, P.hd2(2, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.MergeR.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32))

def rw.Ap.MergeR.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Ap.MergeR.k3(~after, P.node(h, P.hd2(15, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.MergeR.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Ap.MergeR.k2(~after, P.renode(h, b, P.hd2(13, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.MergeR(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Ap.MergeR.k1(~after, P.renode(h, a, P.hd2(2, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Fn.k4(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> P.H:
  (h, +n3) = r
  P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), e2, n2), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), e3, n3), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32))

def rw.Copy.Fn.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  rw.Copy.Fn.k4(~after, P.node(h, P.hd2(4, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Copy.Fn.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Copy.Fn.k3(~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.Fn.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Copy.Fn.k2(~after, P.renode(h, b, P.hd2(1, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Fn(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Copy.Fn.k1(~after, P.renode(h, a, P.hd2(1, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Merge.yes(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  after(P.fuse(P.fuse(P.link(P.link(P.fresh2(h, a, b), e0, e2), e1, e3), e0), e1), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.Merge.no.k4(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> P.H:
  (h, +n3) = r
  P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), n2, e2), n3, e3), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32))

def rw.Copy.Merge.no.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  rw.Copy.Merge.no.k4(~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Copy.Merge.no.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Copy.Merge.no.k3(~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.Merge.no.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Copy.Merge.no.k2(~after, P.renode(h, b, P.hd2(4, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Merge.no(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Copy.Merge.no.k1(~after, P.renode(h, a, P.hd2(4, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Data.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.link(P.link(h, n0, e0), n1, e1)

def rw.Copy.Data.k2.pre(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +dw) = r
  rw.Copy.Data.k2(~after, P.renode(h, b, P.hd2(5, P.form(hb), P.fld(hb)), dw), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Data.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Copy.Data.k2.pre(~after, P.dup(h, P.form(hb), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Data(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Copy.Data.k1(~after, P.renode(h, a, P.hd2(5, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.EraP.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  after(P.link(P.link(h, n0, e0), n1, e1), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.EraP.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Copy.EraP.k2(~after, P.renode(h, b, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.EraP(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Copy.EraP.k1(~after, P.renode(h, a, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.LiftC.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), e0), e1)

def rw.Copy.LiftC.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Copy.LiftC.k3(~after, P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.LiftC.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Copy.LiftC.k2(~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.LiftC(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Copy.LiftC.k1(~after, P.renode(h, a, P.hd2(3, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeL.yes.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  after(P.fuse(P.link(P.link(h, e0, e2), e1, n0), e0), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.MergeL.yes(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Copy.MergeL.yes.k1(~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeL.no.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), n2, e2), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32))

def rw.Copy.MergeL.no.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Copy.MergeL.no.k3(~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.MergeL.no.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Copy.MergeL.no.k2(~after, P.renode(h, b, P.hd2(14, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.MergeL.no(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Copy.MergeL.no.k1(~after, P.renode(h, a, P.hd2(14, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeR.yes.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  after(P.fuse(P.link(P.link(h, e0, n0), e1, e2), e1), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.MergeR.yes(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Copy.MergeR.yes.k1(~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeR.no.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), n2, e2), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32))

def rw.Copy.MergeR.no.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Copy.MergeR.no.k3(~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.MergeR.no.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Copy.MergeR.no.k2(~after, P.renode(h, b, P.hd2(15, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.MergeR.no(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Copy.MergeR.no.k1(~after, P.renode(h, a, P.hd2(15, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Fn.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  after(P.link(P.link(h, n0, e2), n1, e3), N.Ext4{P.nil(), P.nil(), e2, e3})

def rw.EraN.Fn.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.EraN.Fn.k2(~after, P.renode(h, b, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.EraN.Fn(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.EraN.Fn.k1(~after, P.renode(h, a, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Merge.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  after(P.link(P.link(h, n0, e2), n1, e3), N.Ext4{P.nil(), P.nil(), e2, e3})

def rw.EraN.Merge.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.EraN.Merge.k2(~after, P.renode(h, b, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.EraN.Merge(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.EraN.Merge.k1(~after, P.renode(h, a, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Data(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  P.drop(P.fresh2(h, a, b), P.form(hb), pb)

def rw.EraN.EraP(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  P.fresh2(h, a, b)

def rw.EraN.LiftC.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  after(P.link(h, n0, e2), N.Ext4{P.nil(), P.nil(), e2, P.nil()})

def rw.EraN.LiftC(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.EraN.LiftC.k1(~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.MergeL.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  after(P.link(h, n0, e2), N.Ext4{P.nil(), P.nil(), e2, P.nil()})

def rw.EraN.MergeL(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.EraN.MergeL.k1(~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.MergeR.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  after(P.link(h, n0, e2), N.Ext4{P.nil(), P.nil(), e2, P.nil()})

def rw.EraN.MergeR(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.EraN.MergeR.k1(~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Root.LiftC.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, n0, e2)

def rw.Root.LiftC(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Root.LiftC.k1(~after, P.renode(P.free(h, b), a, P.hd(8, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Merge.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e3), n2, e0), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32))

def rw.Call.Merge.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Call.Merge.k3(~after, P.node(h, P.hd2(4, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Call.Merge.k2.pre(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +dw) = r
  rw.Call.Merge.k2(~after, P.renode(h, b, P.hd2(9, P.form(ha), P.fld(ha)), dw), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.Merge.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Call.Merge.k2.pre(~after, P.dup(h, P.form(ha), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.Merge(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Call.Merge.k1(~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Data.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, n0, e0)

def rw.Call.Data.k1.pre(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & P.PW, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, pw) = r
  rw.Call.Data.k1(~after, P.renode_pw(h, a, 5, pw), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Data(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Call.Data.k1.pre(~after, P.apply(P.free(h, b), ha, pa, hb, pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.EraP.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  after(P.link(h, n0, e0), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.Call.EraP(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Call.EraP.k1(~after, P.renode(P.drop(P.free(h, b), P.form(ha), pa), a, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.LiftC.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.fuse(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), e0)

def rw.Call.LiftC.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Call.LiftC.k2(~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.LiftC(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Call.LiftC.k1(~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.MergeL.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32))

def rw.Call.MergeL.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Call.MergeL.k2(~after, P.renode(h, b, P.hd2(14, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.MergeL(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Call.MergeL.k1(~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.MergeR.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32))

def rw.Call.MergeR.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Call.MergeR.k2(~after, P.renode(h, b, P.hd2(15, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.MergeR(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Call.MergeR.k1(~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Fn.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e3), (n2 + 1 : U32), (n0 + 2 : U32)), e2), e3)

def rw.Lift.Fn.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Lift.Fn.k3(~after, P.node(h, P.hd2(11, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Lift.Fn.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Lift.Fn.k2(~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.Fn(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Lift.Fn.k1(~after, P.renode(h, a, P.hd2(1, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Merge.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e3), (n2 + 1 : U32), (n0 + 2 : U32)), e2), e3)

def rw.Lift.Merge.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.Lift.Merge.k3(~after, P.node(h, P.hd2(10, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Lift.Merge.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Lift.Merge.k2(~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.Merge(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Lift.Merge.k1(~after, P.renode(h, a, P.hd2(4, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Data.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, n0, e0)

def rw.Lift.Data(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Lift.Data.k1(~after, P.renode(P.free(h, b), a, P.hd2(5, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.EraP.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  after(P.link(h, n0, e0), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.Lift.EraP(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Lift.EraP.k1(~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.LiftC.yes(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  after(P.fuse(P.link(P.fresh2(h, a, b), e0, e2), e0), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.Lift.LiftC.no.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.fuse(P.fuse(P.link(P.link(P.link(h, n0, e2), (n0 + 1 : U32), (n1 + 1 : U32)), n1, e0), e2), e0)

def rw.Lift.LiftC.no.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Lift.LiftC.no.k2(~after, P.renode(h, b, P.hd2(11, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.LiftC.no(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Lift.LiftC.no.k1(~after, P.renode(h, a, P.hd2(10, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.LiftC.peeled(~after: P.H -> @+x:N.Ext -> P.H, r: P.Pl, +a: U32, +b: U32, +ha: U32, +hb: U32, +e1: U32, +e3: U32) -> P.H:
  match r:
    case P.Pl{h, +t, +pa, +pb, +e0, +e2}:
      match t:
        case True{}:
          rw.Lift.LiftC.yes(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Lift.LiftC.no(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.MergeL.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.fuse(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), e2)

def rw.Lift.MergeL.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Lift.MergeL.k2(~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.MergeL(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Lift.MergeL.k1(~after, P.renode(h, a, P.hd2(14, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.MergeR.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.fuse(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), e2)

def rw.Lift.MergeR.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.Lift.MergeR.k2(~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.MergeR(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.Lift.MergeR.k1(~after, P.renode(h, a, P.hd2(15, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Fn.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.link(P.link(P.link(P.link(P.link(h, n0, e0), e2, n1), (n1 + 1 : U32), (n0 + 1 : U32)), e3, n2), (n2 + 1 : U32), (n0 + 2 : U32))

def rw.CopyL.Fn.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.CopyL.Fn.k3(~after, P.node(h, P.hd2(14, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyL.Fn.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.CopyL.Fn.k2(~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.Fn(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyL.Fn.k1(~after, P.renode(h, a, P.hd2(1, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Merge.yes.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  after(P.fuse(P.link(P.link(h, e0, e2), n0, e3), e0), N.Ext4{e0, P.nil(), P.nil(), e3})

def rw.CopyL.Merge.yes(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyL.Merge.yes.k1(~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Merge.no.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), n2, e3), (n1 + 1 : U32), (n0 + 1 : U32)), (n2 + 1 : U32), (n0 + 2 : U32))

def rw.CopyL.Merge.no.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.CopyL.Merge.no.k3(~after, P.node(h, P.hd2(12, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyL.Merge.no.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.CopyL.Merge.no.k2(~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.Merge.no(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyL.Merge.no.k1(~after, P.renode(h, a, P.hd2(4, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Data.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, n0, e0)

def rw.CopyL.Data(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyL.Data.k1(~after, P.renode(P.free(h, b), a, P.hd2(5, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.EraP.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  after(P.link(h, n0, e0), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyL.EraP(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyL.EraP.k1(~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.LiftC.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.fuse(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), e0)

def rw.CopyL.LiftC.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.CopyL.LiftC.k2(~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.LiftC(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyL.LiftC.k1(~after, P.renode(h, a, P.hd2(12, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.MergeL.yes(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  after(P.fuse(P.link(P.fresh2(h, a, b), e0, e2), e0), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyL.MergeL.no.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32))

def rw.CopyL.MergeL.no.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.CopyL.MergeL.no.k2(~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.MergeL.no(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyL.MergeL.no.k1(~after, P.renode(h, a, P.hd2(14, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.MergeR.yes.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  after(P.link(P.link(h, e0, n1), n0, e2), N.Ext4{e0, P.nil(), e2, P.nil()})

def rw.CopyL.MergeR.yes.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.CopyL.MergeR.yes.k2(~after, P.renode(h, b, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.MergeR.yes(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyL.MergeR.yes.k1(~after, P.renode(h, a, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.MergeR.no.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32))

def rw.CopyL.MergeR.no.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.CopyL.MergeR.no.k2(~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.MergeR.no(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyL.MergeR.no.k1(~after, P.renode(h, a, P.hd2(15, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Fn.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.link(P.link(P.link(P.link(P.link(h, n0, e0), e2, n1), (n1 + 1 : U32), (n0 + 1 : U32)), e3, n2), (n2 + 1 : U32), (n0 + 2 : U32))

def rw.CopyR.Fn.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.CopyR.Fn.k3(~after, P.node(h, P.hd2(15, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyR.Fn.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.CopyR.Fn.k2(~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.Fn(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyR.Fn.k1(~after, P.renode(h, a, P.hd2(1, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Merge.yes.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  after(P.fuse(P.link(P.link(h, n0, e2), e0, e3), e0), N.Ext4{e0, P.nil(), e2, P.nil()})

def rw.CopyR.Merge.yes(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyR.Merge.yes.k1(~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Merge.no.k3(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.H:
  (h, +n2) = r
  P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), n2, e3), (n1 + 1 : U32), (n0 + 1 : U32)), (n2 + 1 : U32), (n0 + 2 : U32))

def rw.CopyR.Merge.no.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  rw.CopyR.Merge.no.k3(~after, P.node(h, P.hd2(13, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyR.Merge.no.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.CopyR.Merge.no.k2(~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.Merge.no(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyR.Merge.no.k1(~after, P.renode(h, a, P.hd2(4, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Data.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, n0, e0)

def rw.CopyR.Data(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyR.Data.k1(~after, P.renode(P.free(h, b), a, P.hd2(5, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.EraP.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  after(P.link(h, n0, e0), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyR.EraP(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyR.EraP.k1(~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.LiftC.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.fuse(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), e0)

def rw.CopyR.LiftC.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.CopyR.LiftC.k2(~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.LiftC(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyR.LiftC.k1(~after, P.renode(h, a, P.hd2(13, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.MergeL.yes.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  after(P.link(P.link(h, n0, e2), e0, n1), N.Ext4{e0, P.nil(), e2, P.nil()})

def rw.CopyR.MergeL.yes.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.CopyR.MergeL.yes.k2(~after, P.renode(h, b, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.MergeL.yes(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyR.MergeL.yes.k1(~after, P.renode(h, a, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.MergeL.no.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32))

def rw.CopyR.MergeL.no.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.CopyR.MergeL.no.k2(~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.MergeL.no(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyR.MergeL.no.k1(~after, P.renode(h, a, P.hd2(14, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.MergeR.yes(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  after(P.fuse(P.link(P.fresh2(h, a, b), e0, e2), e0), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyR.MergeR.no.k2(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.H:
  (h, +n1) = r
  P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32))

def rw.CopyR.MergeR.no.k1(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  rw.CopyR.MergeR.no.k2(~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.MergeR.no(~after: P.H -> @+x:N.Ext -> P.H, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  rw.CopyR.MergeR.no.k1(~after, P.renode(h, a, P.hd2(15, P.form(hb), P.fld(hb)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.Fn.yes.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  after(P.E{P.fuse(P.fuse(P.link(P.link(P.fresh2(h, a, b), e0, e3), e1, e2), e0), e1), P.note(P.note(st, e0, e3), e1, e2)}, N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Ap.Merge.e.k4(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> P.E:
  (h, +n3) = r
  P.E{P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e3), n2, e0), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), n3, e1), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32)), P.note(P.note(P.note(P.note(st, n0, e2), n1, e3), n2, e0), n3, e1)}

def rw.Ap.Merge.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  rw.Ap.Merge.e.k4(~after, P.node(h, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Ap.Merge.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Ap.Merge.e.k3(~after, P.node(h, P.hd2(3, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.Merge.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Ap.Merge.e.k2(~after, P.renode(h, b, P.hd2(2, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.Merge.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Ap.Merge.e.k1(~after, P.renode(h, a, P.hd2(2, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.Data.yes.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(P.link(h, n0, e0), (n0 + 1 : U32), e1), P.note(st, n0, e0)}

def rw.Ap.Data.yes.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Ap.Data.yes.e.k1(~after, P.renode(P.free(h, b), a, P.hd2(9, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.EraP.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  after(P.E{P.link(P.link(h, n0, e0), n1, e1), P.note(P.note(st, n0, e0), n1, e1)}, N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Ap.EraP.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Ap.EraP.e.k2(~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.EraP.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Ap.EraP.e.k1(~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.LiftC.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), e0), e1), P.note(P.note(P.note(st, n0, e2), n1, e0), n2, e1)}

def rw.Ap.LiftC.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Ap.LiftC.e.k3(~after, P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.LiftC.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Ap.LiftC.e.k2(~after, P.renode(h, b, P.hd2(10, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.LiftC.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Ap.LiftC.e.k1(~after, P.renode(h, a, P.hd2(2, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.MergeL.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), P.note(P.note(P.note(st, n0, e2), n1, e0), n2, e1)}

def rw.Ap.MergeL.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Ap.MergeL.e.k3(~after, P.node(h, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.MergeL.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Ap.MergeL.e.k2(~after, P.renode(h, b, P.hd2(12, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.MergeL.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Ap.MergeL.e.k1(~after, P.renode(h, a, P.hd2(2, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.MergeR.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), P.note(P.note(P.note(st, n0, e2), n1, e0), n2, e1)}

def rw.Ap.MergeR.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Ap.MergeR.e.k3(~after, P.node(h, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.MergeR.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Ap.MergeR.e.k2(~after, P.renode(h, b, P.hd2(13, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.MergeR.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Ap.MergeR.e.k1(~after, P.renode(h, a, P.hd2(2, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Fn.e.k4(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> P.E:
  (h, +n3) = r
  P.E{P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), e2, n2), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), e3, n3), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32)), P.note(P.note(P.note(P.note(st, n0, e0), n1, e1), e2, n2), e3, n3)}

def rw.Copy.Fn.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  rw.Copy.Fn.e.k4(~after, P.node(h, P.hd2(4, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Copy.Fn.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Copy.Fn.e.k3(~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.Fn.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Copy.Fn.e.k2(~after, P.renode(h, b, P.hd2(1, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Fn.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Copy.Fn.e.k1(~after, P.renode(h, a, P.hd2(1, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Merge.yes.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  after(P.E{P.fuse(P.fuse(P.link(P.link(P.fresh2(h, a, b), e0, e2), e1, e3), e0), e1), P.note(P.note(st, e0, e2), e1, e3)}, N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.Merge.no.e.k4(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> P.E:
  (h, +n3) = r
  P.E{P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), n2, e2), n3, e3), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32)), P.note(P.note(P.note(P.note(st, n0, e0), n1, e1), n2, e2), n3, e3)}

def rw.Copy.Merge.no.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  rw.Copy.Merge.no.e.k4(~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Copy.Merge.no.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Copy.Merge.no.e.k3(~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.Merge.no.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Copy.Merge.no.e.k2(~after, P.renode(h, b, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Merge.no.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Copy.Merge.no.e.k1(~after, P.renode(h, a, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Data.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.link(P.link(h, n0, e0), n1, e1), P.note(P.note(st, n0, e0), n1, e1)}

def rw.Copy.Data.e.k2.pre(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +dw) = r
  rw.Copy.Data.e.k2(~after, P.renode(h, b, P.hd2(5, P.form(hb), P.fld(hb)), dw), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Data.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Copy.Data.e.k2.pre(~after, P.dup(h, P.form(hb), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Data.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Copy.Data.e.k1(~after, P.renode(h, a, P.hd2(5, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.EraP.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  after(P.E{P.link(P.link(h, n0, e0), n1, e1), P.note(P.note(st, n0, e0), n1, e1)}, N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.EraP.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Copy.EraP.e.k2(~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.EraP.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Copy.EraP.e.k1(~after, P.renode(h, a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.LiftC.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), e0), e1), P.note(P.note(P.note(st, n0, e2), n1, e0), n2, e1)}

def rw.Copy.LiftC.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Copy.LiftC.e.k3(~after, P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.LiftC.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Copy.LiftC.e.k2(~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.LiftC.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Copy.LiftC.e.k1(~after, P.renode(h, a, P.hd2(3, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeL.yes.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  after(P.E{P.fuse(P.link(P.link(h, e0, e2), e1, n0), e0), P.note(P.note(st, e0, e2), e1, n0)}, N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.MergeL.yes.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Copy.MergeL.yes.e.k1(~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeL.no.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), n2, e2), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), P.note(P.note(P.note(st, n0, e0), n1, e1), n2, e2)}

def rw.Copy.MergeL.no.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Copy.MergeL.no.e.k3(~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.MergeL.no.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Copy.MergeL.no.e.k2(~after, P.renode(h, b, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.MergeL.no.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Copy.MergeL.no.e.k1(~after, P.renode(h, a, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeR.yes.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  after(P.E{P.fuse(P.link(P.link(h, e0, n0), e1, e2), e1), P.note(P.note(st, e0, n0), e1, e2)}, N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.MergeR.yes.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Copy.MergeR.yes.e.k1(~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeR.no.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), n2, e2), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), P.note(P.note(P.note(st, n0, e0), n1, e1), n2, e2)}

def rw.Copy.MergeR.no.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Copy.MergeR.no.e.k3(~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.MergeR.no.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Copy.MergeR.no.e.k2(~after, P.renode(h, b, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.MergeR.no.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Copy.MergeR.no.e.k1(~after, P.renode(h, a, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Fn.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  after(P.E{P.link(P.link(h, n0, e2), n1, e3), P.note(P.note(st, n0, e2), n1, e3)}, N.Ext4{P.nil(), P.nil(), e2, e3})

def rw.EraN.Fn.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.EraN.Fn.e.k2(~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.EraN.Fn.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.EraN.Fn.e.k1(~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Merge.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  after(P.E{P.link(P.link(h, n0, e2), n1, e3), P.note(P.note(st, n0, e2), n1, e3)}, N.Ext4{P.nil(), P.nil(), e2, e3})

def rw.EraN.Merge.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.EraN.Merge.e.k2(~after, P.renode(h, b, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.EraN.Merge.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.EraN.Merge.e.k1(~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Data.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  P.E{P.drop(P.fresh2(h, a, b), P.form(hb), pb), st}

def rw.EraN.EraP.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  P.E{P.fresh2(h, a, b), st}

def rw.EraN.LiftC.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  after(P.E{P.link(h, n0, e2), P.note(st, n0, e2)}, N.Ext4{P.nil(), P.nil(), e2, P.nil()})

def rw.EraN.LiftC.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.EraN.LiftC.e.k1(~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.MergeL.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  after(P.E{P.link(h, n0, e2), P.note(st, n0, e2)}, N.Ext4{P.nil(), P.nil(), e2, P.nil()})

def rw.EraN.MergeL.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.EraN.MergeL.e.k1(~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.MergeR.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  after(P.E{P.link(h, n0, e2), P.note(st, n0, e2)}, N.Ext4{P.nil(), P.nil(), e2, P.nil()})

def rw.EraN.MergeR.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.EraN.MergeR.e.k1(~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Root.LiftC.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, n0, e2), P.note(st, n0, e2)}

def rw.Root.LiftC.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Root.LiftC.e.k1(~after, P.renode(P.free(h, b), a, P.hd(8, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Merge.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e3), n2, e0), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), P.note(P.note(P.note(st, n0, e2), n1, e3), n2, e0)}

def rw.Call.Merge.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Call.Merge.e.k3(~after, P.node(h, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Call.Merge.e.k2.pre(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +dw) = r
  rw.Call.Merge.e.k2(~after, P.renode(h, b, P.hd2(9, P.form(ha), P.fld(ha)), dw), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.Merge.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Call.Merge.e.k2.pre(~after, P.dup(h, P.form(ha), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.Merge.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Call.Merge.e.k1(~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Data.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, n0, e0), P.note(st, n0, e0)}

def rw.Call.Data.e.k1.pre(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & P.PW, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, pw) = r
  rw.Call.Data.e.k1(~after, P.renode_pw(h, a, 5, pw), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Data.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Call.Data.e.k1.pre(~after, P.apply(P.free(h, b), ha, pa, hb, pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.EraP.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  after(P.E{P.link(h, n0, e0), P.note(st, n0, e0)}, N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.Call.EraP.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Call.EraP.e.k1(~after, P.renode(P.drop(P.free(h, b), P.form(ha), pa), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.LiftC.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.fuse(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), e0), P.note(P.note(st, n0, e2), n1, e0)}

def rw.Call.LiftC.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Call.LiftC.e.k2(~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.LiftC.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Call.LiftC.e.k1(~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.MergeL.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), P.note(P.note(st, n0, e2), n1, e0)}

def rw.Call.MergeL.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Call.MergeL.e.k2(~after, P.renode(h, b, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.MergeL.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Call.MergeL.e.k1(~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.MergeR.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), P.note(P.note(st, n0, e2), n1, e0)}

def rw.Call.MergeR.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Call.MergeR.e.k2(~after, P.renode(h, b, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.MergeR.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Call.MergeR.e.k1(~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Fn.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e3), (n2 + 1 : U32), (n0 + 2 : U32)), e2), e3), P.note(P.note(P.note(st, n0, e0), n1, e2), n2, e3)}

def rw.Lift.Fn.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Lift.Fn.e.k3(~after, P.node(h, P.hd2(11, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Lift.Fn.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Lift.Fn.e.k2(~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.Fn.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Lift.Fn.e.k1(~after, P.renode(h, a, P.hd2(1, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Merge.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e3), (n2 + 1 : U32), (n0 + 2 : U32)), e2), e3), P.note(P.note(P.note(st, n0, e0), n1, e2), n2, e3)}

def rw.Lift.Merge.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.Lift.Merge.e.k3(~after, P.node(h, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Lift.Merge.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Lift.Merge.e.k2(~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.Merge.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Lift.Merge.e.k1(~after, P.renode(h, a, P.hd2(4, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Data.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, n0, e0), P.note(st, n0, e0)}

def rw.Lift.Data.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Lift.Data.e.k1(~after, P.renode(P.free(h, b), a, P.hd2(5, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.EraP.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  after(P.E{P.link(h, n0, e0), P.note(st, n0, e0)}, N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.Lift.EraP.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Lift.EraP.e.k1(~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.LiftC.yes.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  after(P.E{P.fuse(P.link(P.fresh2(h, a, b), e0, e2), e0), P.note(st, e0, e2)}, N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.Lift.LiftC.no.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.fuse(P.fuse(P.link(P.link(P.link(h, n0, e2), (n0 + 1 : U32), (n1 + 1 : U32)), n1, e0), e2), e0), P.note(P.note(st, n0, e2), n1, e0)}

def rw.Lift.LiftC.no.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Lift.LiftC.no.e.k2(~after, P.renode(h, b, P.hd2(11, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.LiftC.no.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Lift.LiftC.no.e.k1(~after, P.renode(h, a, P.hd2(10, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.LiftC.peeled.e(~after: P.E -> @+x:N.Ext -> P.E, r: P.Pl, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +e1: U32, +e3: U32) -> P.E:
  match r:
    case P.Pl{h, +t, +pa, +pb, +e0, +e2}:
      match t:
        case True{}:
          rw.Lift.LiftC.yes.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Lift.LiftC.no.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.MergeL.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.fuse(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), e2), P.note(P.note(st, n0, e0), n1, e2)}

def rw.Lift.MergeL.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Lift.MergeL.e.k2(~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.MergeL.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Lift.MergeL.e.k1(~after, P.renode(h, a, P.hd2(14, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.MergeR.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.fuse(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), e2), P.note(P.note(st, n0, e0), n1, e2)}

def rw.Lift.MergeR.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.Lift.MergeR.e.k2(~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.MergeR.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.Lift.MergeR.e.k1(~after, P.renode(h, a, P.hd2(15, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Fn.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.link(P.link(P.link(P.link(P.link(h, n0, e0), e2, n1), (n1 + 1 : U32), (n0 + 1 : U32)), e3, n2), (n2 + 1 : U32), (n0 + 2 : U32)), P.note(P.note(P.note(st, n0, e0), e2, n1), e3, n2)}

def rw.CopyL.Fn.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.CopyL.Fn.e.k3(~after, P.node(h, P.hd2(14, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyL.Fn.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.CopyL.Fn.e.k2(~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.Fn.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyL.Fn.e.k1(~after, P.renode(h, a, P.hd2(1, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Merge.yes.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  after(P.E{P.fuse(P.link(P.link(h, e0, e2), n0, e3), e0), P.note(P.note(st, e0, e2), n0, e3)}, N.Ext4{e0, P.nil(), P.nil(), e3})

def rw.CopyL.Merge.yes.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyL.Merge.yes.e.k1(~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Merge.no.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), n2, e3), (n1 + 1 : U32), (n0 + 1 : U32)), (n2 + 1 : U32), (n0 + 2 : U32)), P.note(P.note(P.note(st, n0, e0), n1, e2), n2, e3)}

def rw.CopyL.Merge.no.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.CopyL.Merge.no.e.k3(~after, P.node(h, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyL.Merge.no.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.CopyL.Merge.no.e.k2(~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.Merge.no.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyL.Merge.no.e.k1(~after, P.renode(h, a, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Data.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, n0, e0), P.note(st, n0, e0)}

def rw.CopyL.Data.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyL.Data.e.k1(~after, P.renode(P.free(h, b), a, P.hd2(5, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.EraP.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  after(P.E{P.link(h, n0, e0), P.note(st, n0, e0)}, N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyL.EraP.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyL.EraP.e.k1(~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.LiftC.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.fuse(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), e0), P.note(P.note(st, n0, e2), n1, e0)}

def rw.CopyL.LiftC.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.CopyL.LiftC.e.k2(~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.LiftC.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyL.LiftC.e.k1(~after, P.renode(h, a, P.hd2(12, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.MergeL.yes.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  after(P.E{P.fuse(P.link(P.fresh2(h, a, b), e0, e2), e0), P.note(st, e0, e2)}, N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyL.MergeL.no.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), P.note(P.note(st, n0, e0), n1, e2)}

def rw.CopyL.MergeL.no.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.CopyL.MergeL.no.e.k2(~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.MergeL.no.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyL.MergeL.no.e.k1(~after, P.renode(h, a, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.MergeR.yes.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  after(P.E{P.link(P.link(h, e0, n1), n0, e2), P.note(P.note(st, e0, n1), n0, e2)}, N.Ext4{e0, P.nil(), e2, P.nil()})

def rw.CopyL.MergeR.yes.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.CopyL.MergeR.yes.e.k2(~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.MergeR.yes.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyL.MergeR.yes.e.k1(~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.MergeR.no.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), P.note(P.note(st, n0, e0), n1, e2)}

def rw.CopyL.MergeR.no.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.CopyL.MergeR.no.e.k2(~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.MergeR.no.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyL.MergeR.no.e.k1(~after, P.renode(h, a, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Fn.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.link(P.link(P.link(P.link(P.link(h, n0, e0), e2, n1), (n1 + 1 : U32), (n0 + 1 : U32)), e3, n2), (n2 + 1 : U32), (n0 + 2 : U32)), P.note(P.note(P.note(st, n0, e0), e2, n1), e3, n2)}

def rw.CopyR.Fn.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.CopyR.Fn.e.k3(~after, P.node(h, P.hd2(15, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyR.Fn.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.CopyR.Fn.e.k2(~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.Fn.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyR.Fn.e.k1(~after, P.renode(h, a, P.hd2(1, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Merge.yes.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  after(P.E{P.fuse(P.link(P.link(h, n0, e2), e0, e3), e0), P.note(P.note(st, n0, e2), e0, e3)}, N.Ext4{e0, P.nil(), e2, P.nil()})

def rw.CopyR.Merge.yes.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyR.Merge.yes.e.k1(~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Merge.no.e.k3(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> P.E:
  (h, +n2) = r
  P.E{P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), n2, e3), (n1 + 1 : U32), (n0 + 1 : U32)), (n2 + 1 : U32), (n0 + 2 : U32)), P.note(P.note(P.note(st, n0, e0), n1, e2), n2, e3)}

def rw.CopyR.Merge.no.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  rw.CopyR.Merge.no.e.k3(~after, P.node(h, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyR.Merge.no.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.CopyR.Merge.no.e.k2(~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.Merge.no.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyR.Merge.no.e.k1(~after, P.renode(h, a, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Data.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, n0, e0), P.note(st, n0, e0)}

def rw.CopyR.Data.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyR.Data.e.k1(~after, P.renode(P.free(h, b), a, P.hd2(5, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.EraP.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  after(P.E{P.link(h, n0, e0), P.note(st, n0, e0)}, N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyR.EraP.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyR.EraP.e.k1(~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.LiftC.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.fuse(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), e0), P.note(P.note(st, n0, e2), n1, e0)}

def rw.CopyR.LiftC.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.CopyR.LiftC.e.k2(~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.LiftC.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyR.LiftC.e.k1(~after, P.renode(h, a, P.hd2(13, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.MergeL.yes.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  after(P.E{P.link(P.link(h, n0, e2), e0, n1), P.note(P.note(st, n0, e2), e0, n1)}, N.Ext4{e0, P.nil(), e2, P.nil()})

def rw.CopyR.MergeL.yes.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.CopyR.MergeL.yes.e.k2(~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.MergeL.yes.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyR.MergeL.yes.e.k1(~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.MergeL.no.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), P.note(P.note(st, n0, e0), n1, e2)}

def rw.CopyR.MergeL.no.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.CopyR.MergeL.no.e.k2(~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.MergeL.no.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyR.MergeL.no.e.k1(~after, P.renode(h, a, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.MergeR.yes.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  after(P.E{P.fuse(P.link(P.fresh2(h, a, b), e0, e2), e0), P.note(st, e0, e2)}, N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyR.MergeR.no.e.k2(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> P.E:
  (h, +n1) = r
  P.E{P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), P.note(P.note(st, n0, e0), n1, e2)}

def rw.CopyR.MergeR.no.e.k1(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  rw.CopyR.MergeR.no.e.k2(~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.MergeR.no.e(~after: P.E -> @+x:N.Ext -> P.E, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  rw.CopyR.MergeR.no.e.k1(~after, P.renode(h, a, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

# Events (R.event)

# rules linking two of their own new nodes into an event: none, or this
# names what does not exist
def inner_events() -> U32:
  0

# the eraser kind making an event at port p of kind k, 0 for none: two
# bits a port (0 none, 1 EraN, 2 EraP), eight a kind, four kinds a word
def ev_word(+w: U32) -> U32:
  match w:
    case 0:
      335544320
    case 1:
      40
    case 2:
      134479872
    case _:
      134743044

def ev_by.c(+c: U32) -> U32:
  match c:
    case 0:
      0
    case _:
      (c + 5 : U32)

def ev_by(+k: U32, +p: U32) -> U32:
  ev_by.c(((ev_word((k >> 2n : U32)) >> U32.to_nat((((k .&. 3 : U32) * 8 : U32) + (p * 2 : U32) : U32)) : U32) .&. 3 : U32))

# may port p of kind k be one end of an event: an eraser's principal, or
# an auxiliary port some eraser makes an event at
def ev_end(+k: U32, +p: U32) -> Bool:
  (U32.is_eq(p, 0) && U32.is_eq((k .|. 1 : U32), 7)) || U32.is_ne(ev_by(k, p), 0)

# the most active pairs one event makes
def ev_most() -> U32:
  0

def ev.Copy.p1.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, (n0 + 1 : U32), e1)

def ev.Copy.p1(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  ev.Copy.p1.k1(P.renode(P.free(h, b), a, P.hd2(13, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Copy.p2.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, (n0 + 1 : U32), e1)

def ev.Copy.p2(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  ev.Copy.p2.k1(P.renode(P.free(h, b), a, P.hd2(12, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Merge.p1.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, (n0 + 1 : U32), e1)

def ev.Merge.p1(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  ev.Merge.p1.k1(P.renode(P.free(h, b), a, P.hd2(15, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Merge.p2.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  P.link(h, (n0 + 1 : U32), e1)

def ev.Merge.p2(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  ev.Merge.p2.k1(P.renode(P.free(h, b), a, P.hd2(14, P.form(ha), P.fld(ha)), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Lift.p1.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  h

def ev.Lift.p1(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  ev.Lift.p1.k1(P.renode(P.free(h, b), a, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.LiftC.p1.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  h

def ev.LiftC.p1(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  ev.LiftC.p1.k1(P.renode(P.free(h, b), a, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.CopyL.p1.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  h

def ev.CopyL.p1(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  ev.CopyL.p1.k1(P.renode(P.free(h, b), a, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.CopyR.p1.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  h

def ev.CopyR.p1(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  ev.CopyR.p1.k1(P.renode(P.free(h, b), a, P.hd(6, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.MergeL.p1.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  h

def ev.MergeL.p1(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  ev.MergeL.p1.k1(P.renode(P.free(h, b), a, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.MergeR.p1.k1(r: P.H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  (h, +n0) = r
  h

def ev.MergeR.p1(h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  ev.MergeR.p1.k1(P.renode(P.free(h, b), a, P.hd(7, 0), 0), a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Copy.p1.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, (n0 + 1 : U32), e1), st}

def ev.Copy.p1.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  ev.Copy.p1.e.k1(P.renode(P.free(h, b), a, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Copy.p2.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, (n0 + 1 : U32), e1), st}

def ev.Copy.p2.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  ev.Copy.p2.e.k1(P.renode(P.free(h, b), a, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Merge.p1.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, (n0 + 1 : U32), e1), st}

def ev.Merge.p1.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  ev.Merge.p1.e.k1(P.renode(P.free(h, b), a, P.hd2(15, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Merge.p2.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{P.link(h, (n0 + 1 : U32), e1), st}

def ev.Merge.p2.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  ev.Merge.p2.e.k1(P.renode(P.free(h, b), a, P.hd2(14, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Lift.p1.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{h, st}

def ev.Lift.p1.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  ev.Lift.p1.e.k1(P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.LiftC.p1.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{h, st}

def ev.LiftC.p1.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  ev.LiftC.p1.e.k1(P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.CopyL.p1.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{h, st}

def ev.CopyL.p1.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  ev.CopyL.p1.e.k1(P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.CopyR.p1.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{h, st}

def ev.CopyR.p1.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  ev.CopyR.p1.e.k1(P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.MergeL.p1.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{h, st}

def ev.MergeL.p1.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  ev.MergeL.p1.e.k1(P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.MergeR.p1.e.k1(r: P.H & U32, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  (h, +n0) = r
  P.E{h, st}

def ev.MergeR.p1.e(h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  ev.MergeR.p1.e.k1(P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

# the event at port p of a node of kind ka, A, the eraser facing it B;
# e0 the peer of A's principal, e1 of its other auxiliary port
def event(+ka: U32, +p: U32, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  match ka p:
    case 3 1:
      ev.Copy.p1(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 2:
      ev.Copy.p2(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 4 1:
      ev.Merge.p1(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 4 2:
      ev.Merge.p2(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 1:
      ev.Lift.p1(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 11 1:
      ev.LiftC.p1(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 1:
      ev.CopyL.p1(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 1:
      ev.CopyR.p1(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 14 1:
      ev.MergeL.p1(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 15 1:
      ev.MergeR.p1(h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case _ _:
      P.h_err(h)

# the same, noting the pairs it makes on the strategy's stack
def event.e(+ka: U32, +p: U32, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  match ka p:
    case 3 1:
      ev.Copy.p1.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 2:
      ev.Copy.p2.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 4 1:
      ev.Merge.p1.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 4 2:
      ev.Merge.p2.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 1:
      ev.Lift.p1.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 11 1:
      ev.LiftC.p1.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 1:
      ev.CopyL.p1.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 1:
      ev.CopyR.p1.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 14 1:
      ev.MergeL.p1.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 15 1:
      ev.MergeR.p1.e(h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case _ _:
      P.E{P.h_err(h), st}

# the rewrite for A, negative principal, meeting B; t is the payload test;
# then `after`, at the external peers where the rule may make an event
def rewrite(~after: P.H -> @+x:N.Ext -> P.H, +ka: U32, +kb: U32, +t: Bool, h: P.H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H:
  match ka kb:
    case 2 1:
      match t:
        case True{}:
          rw.Ap.Fn.yes(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          P.err_if(U32.is_ne(ka, 8), h)
    case 2 4:
      rw.Ap.Merge(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 5:
      match t:
        case True{}:
          rw.Ap.Data.yes(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          P.err_if(U32.is_ne(ka, 8), h)
    case 2 7:
      rw.Ap.EraP(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 11:
      rw.Ap.LiftC(~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 14:
      rw.Ap.MergeL(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 15:
      rw.Ap.MergeR(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 1:
      rw.Copy.Fn(~after, P.err_if(P.copy_fn_bad(ha, hb), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 4:
      match t:
        case True{}:
          rw.Copy.Merge.yes(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Copy.Merge.no(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 5:
      rw.Copy.Data(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 7:
      rw.Copy.EraP(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 11:
      rw.Copy.LiftC(~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 14:
      match t:
        case True{}:
          rw.Copy.MergeL.yes(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Copy.MergeL.no(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 15:
      match t:
        case True{}:
          rw.Copy.MergeR.yes(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Copy.MergeR.no(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 1:
      rw.EraN.Fn(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 4:
      rw.EraN.Merge(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 5:
      rw.EraN.Data(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 7:
      rw.EraN.EraP(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 11:
      rw.EraN.LiftC(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 14:
      rw.EraN.MergeL(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 15:
      rw.EraN.MergeR(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 8 11:
      rw.Root.LiftC(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 4:
      rw.Call.Merge(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 5:
      rw.Call.Data(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 7:
      rw.Call.EraP(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 11:
      rw.Call.LiftC(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 14:
      rw.Call.MergeL(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 15:
      rw.Call.MergeR(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 1:
      rw.Lift.Fn(~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 4:
      rw.Lift.Merge(~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 5:
      rw.Lift.Data(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 7:
      rw.Lift.EraP(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 11:
      rw.Lift.LiftC.peeled(~after, P.peel_ctl(P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)) || P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), a, b, ha, hb, pa, pb, e0, e2), a, b, ha, hb, e1, e3)
    case 10 14:
      rw.Lift.MergeL(~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 15:
      rw.Lift.MergeR(~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 1:
      rw.CopyL.Fn(~after, P.err_if(P.copy_fn_bad(ha, hb), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 4:
      match t:
        case True{}:
          rw.CopyL.Merge.yes(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyL.Merge.no(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 5:
      rw.CopyL.Data(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 7:
      rw.CopyL.EraP(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 11:
      rw.CopyL.LiftC(~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 14:
      match t:
        case True{}:
          rw.CopyL.MergeL.yes(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyL.MergeL.no(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 15:
      match t:
        case True{}:
          rw.CopyL.MergeR.yes(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyL.MergeR.no(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 1:
      rw.CopyR.Fn(~after, P.err_if(P.copy_fn_bad(ha, hb), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 4:
      match t:
        case True{}:
          rw.CopyR.Merge.yes(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyR.Merge.no(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 5:
      rw.CopyR.Data(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 7:
      rw.CopyR.EraP(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 11:
      rw.CopyR.LiftC(~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 14:
      match t:
        case True{}:
          rw.CopyR.MergeL.yes(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyR.MergeL.no(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 15:
      match t:
        case True{}:
          rw.CopyR.MergeR.yes(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyR.MergeR.no(~after, h, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case _ _:
      P.err_if(U32.is_ne(ka, 8), h)

# the same, noting the pairs it makes on the strategy's stack
def rewrite.e(~after: P.E -> @+x:N.Ext -> P.E, +ka: U32, +kb: U32, +t: Bool, h: P.H, st: P.Stk, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.E:
  match ka kb:
    case 2 1:
      match t:
        case True{}:
          rw.Ap.Fn.yes.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          P.E{P.err_if(U32.is_ne(ka, 8), h), st}
    case 2 4:
      rw.Ap.Merge.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 5:
      match t:
        case True{}:
          rw.Ap.Data.yes.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          P.E{P.err_if(U32.is_ne(ka, 8), h), st}
    case 2 7:
      rw.Ap.EraP.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 11:
      rw.Ap.LiftC.e(~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 14:
      rw.Ap.MergeL.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 15:
      rw.Ap.MergeR.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 1:
      rw.Copy.Fn.e(~after, P.err_if(P.copy_fn_bad(ha, hb), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 4:
      match t:
        case True{}:
          rw.Copy.Merge.yes.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Copy.Merge.no.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 5:
      rw.Copy.Data.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 7:
      rw.Copy.EraP.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 11:
      rw.Copy.LiftC.e(~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 14:
      match t:
        case True{}:
          rw.Copy.MergeL.yes.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Copy.MergeL.no.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 15:
      match t:
        case True{}:
          rw.Copy.MergeR.yes.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Copy.MergeR.no.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 1:
      rw.EraN.Fn.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 4:
      rw.EraN.Merge.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 5:
      rw.EraN.Data.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 7:
      rw.EraN.EraP.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 11:
      rw.EraN.LiftC.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 14:
      rw.EraN.MergeL.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 15:
      rw.EraN.MergeR.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 8 11:
      rw.Root.LiftC.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 4:
      rw.Call.Merge.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 5:
      rw.Call.Data.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 7:
      rw.Call.EraP.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 11:
      rw.Call.LiftC.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 14:
      rw.Call.MergeL.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 15:
      rw.Call.MergeR.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 1:
      rw.Lift.Fn.e(~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 4:
      rw.Lift.Merge.e(~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 5:
      rw.Lift.Data.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 7:
      rw.Lift.EraP.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 11:
      rw.Lift.LiftC.peeled.e(~after, P.peel_ctl(P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)) || P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), a, b, ha, hb, pa, pb, e0, e2), st, a, b, ha, hb, e1, e3)
    case 10 14:
      rw.Lift.MergeL.e(~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 15:
      rw.Lift.MergeR.e(~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 1:
      rw.CopyL.Fn.e(~after, P.err_if(P.copy_fn_bad(ha, hb), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 4:
      match t:
        case True{}:
          rw.CopyL.Merge.yes.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyL.Merge.no.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 5:
      rw.CopyL.Data.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 7:
      rw.CopyL.EraP.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 11:
      rw.CopyL.LiftC.e(~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 14:
      match t:
        case True{}:
          rw.CopyL.MergeL.yes.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyL.MergeL.no.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 15:
      match t:
        case True{}:
          rw.CopyL.MergeR.yes.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyL.MergeR.no.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 1:
      rw.CopyR.Fn.e(~after, P.err_if(P.copy_fn_bad(ha, hb), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 4:
      match t:
        case True{}:
          rw.CopyR.Merge.yes.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyR.Merge.no.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 5:
      rw.CopyR.Data.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 7:
      rw.CopyR.EraP.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 11:
      rw.CopyR.LiftC.e(~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 14:
      match t:
        case True{}:
          rw.CopyR.MergeL.yes.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyR.MergeL.no.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 15:
      match t:
        case True{}:
          rw.CopyR.MergeR.yes.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyR.MergeR.no.e(~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case _ _:
      P.E{P.err_if(U32.is_ne(ka, 8), h), st}

