import Base
import ./kprim.bend as P
import ./net.bend as N

# The kernel's rewrites, generated from the rule table (spike/rules.bend)
# by spike/tools/gen_krules.bend; do not edit. scripts/check.sh fails if
# this file differs from what the generator writes. One family, generic
# over what a strategy threads beside the net (knet.bend's Families): a
# stack, on which each link a rewrite makes between two principal ports
# is noted, or nothing.

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
# t; net.bend's rule_test), a template over the family and what follows
# the rewrite, for a copy in each strategy's chain: shared, it has two
# callers, and the compiler folds it into neither, which cost the eager
# chain 5% to 12% (heap-strategies.stack). A Lift facing a LiftC is tested
# after peeling instead (P.peel_ctl).
def test.k(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +kb: U32, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
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

def test(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, +ha: U32, +hb: U32, +pa: U32, +pb: U32) -> P.H & Bool:
  test.k(~S, ~R, ~note, ~fin, ~after, P.rk(ha), P.rk(hb), h, ha, hb, pa, pb)

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

def rw.Ap.Fn.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  after(fin(P.fuse(P.fuse(P.link(P.link(P.fresh2(h, a, b), e0, e3), e1, e2), e0), e1), note(note(st, e0, e3), e1, e2)), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Ap.Merge.k4(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> R:
  (h, +n3) = r
  fin(P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e3), n2, e0), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), n3, e1), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32)), note(note(note(note(st, n0, e2), n1, e3), n2, e0), n3, e1))

def rw.Ap.Merge.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  rw.Ap.Merge.k4(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Ap.Merge.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Ap.Merge.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(3, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.Merge.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Ap.Merge.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(2, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.Merge(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.Merge.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(2, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.Data.yes.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  fin(P.link(P.link(h, n0, e0), (n0 + 1 : U32), e1), note(st, n0, e0))

def rw.Ap.Data.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.Data.yes.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd2(9, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.EraP.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  after(fin(P.link(P.link(h, n0, e0), n1, e1), note(note(st, n0, e0), n1, e1)), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Ap.EraP.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Ap.EraP.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.EraP.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.LiftC.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), e0), e1), note(note(note(st, n0, e2), n1, e0), n2, e1))

def rw.Ap.LiftC.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Ap.LiftC.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Ap.LiftC.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(10, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(2, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.MergeL.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), note(note(note(st, n0, e2), n1, e0), n2, e1))

def rw.Ap.MergeL.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Ap.MergeL.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.MergeL.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Ap.MergeL.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(12, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.MergeL(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.MergeL.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(2, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Ap.MergeR.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), note(note(note(st, n0, e2), n1, e0), n2, e1))

def rw.Ap.MergeR.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Ap.MergeR.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Ap.MergeR.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Ap.MergeR.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(13, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Ap.MergeR(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Ap.MergeR.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(2, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Fn.k4(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> R:
  (h, +n3) = r
  fin(P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), e2, n2), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), e3, n3), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32)), note(note(note(note(st, n0, e0), n1, e1), e2, n2), e3, n3))

def rw.Copy.Fn.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  rw.Copy.Fn.k4(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(4, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Copy.Fn.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Copy.Fn.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.Fn.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Copy.Fn.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(1, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Fn(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.Fn.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(1, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Merge.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  after(fin(P.fuse(P.fuse(P.link(P.link(P.fresh2(h, a, b), e0, e2), e1, e3), e0), e1), note(note(st, e0, e2), e1, e3)), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.Merge.no.k4(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32, +n2: U32) -> R:
  (h, +n3) = r
  fin(P.link(P.link(P.link(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), n2, e2), n3, e3), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), (n3 + 1 : U32), (n0 + 2 : U32)), (n3 + 2 : U32), (n1 + 2 : U32)), note(note(note(note(st, n0, e0), n1, e1), n2, e2), n3, e3))

def rw.Copy.Merge.no.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  rw.Copy.Merge.no.k4(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1, n2)

def rw.Copy.Merge.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Copy.Merge.no.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.Merge.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Copy.Merge.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Merge.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.Merge.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.Data.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(h, n0, e0), n1, e1), note(note(st, n0, e0), n1, e1))

def rw.Copy.Data.k2.pre(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +dw) = r
  rw.Copy.Data.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(5, P.form(hb), P.fld(hb)), dw), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Data.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Copy.Data.k2.pre(~S, ~R, ~note, ~fin, ~after, P.dup(h, P.form(hb), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.Data(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.Data.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(5, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.EraP.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  after(fin(P.link(P.link(h, n0, e0), n1, e1), note(note(st, n0, e0), n1, e1)), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.EraP.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Copy.EraP.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.EraP.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.LiftC.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e1), (n2 + 1 : U32), (n0 + 2 : U32)), e0), e1), note(note(note(st, n0, e2), n1, e0), n2, e1))

def rw.Copy.LiftC.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Copy.LiftC.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Copy.LiftC.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(3, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeL.yes.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.fuse(P.link(P.link(h, e0, e2), e1, n0), e0), note(note(st, e0, e2), e1, n0)), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.MergeL.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.MergeL.yes.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeL.no.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), n2, e2), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), note(note(note(st, n0, e0), n1, e1), n2, e2))

def rw.Copy.MergeL.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Copy.MergeL.no.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.MergeL.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Copy.MergeL.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.MergeL.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.MergeL.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeR.yes.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.fuse(P.link(P.link(h, e0, n0), e1, e2), e1), note(note(st, e0, n0), e1, e2)), N.Ext4{e0, e1, P.nil(), P.nil()})

def rw.Copy.MergeR.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.MergeR.yes.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Copy.MergeR.no.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e1), n2, e2), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), note(note(note(st, n0, e0), n1, e1), n2, e2))

def rw.Copy.MergeR.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Copy.MergeR.no.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(3, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Copy.MergeR.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Copy.MergeR.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Copy.MergeR.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Copy.MergeR.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Fn.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  after(fin(P.link(P.link(h, n0, e2), n1, e3), note(note(st, n0, e2), n1, e3)), N.Ext4{P.nil(), P.nil(), e2, e3})

def rw.EraN.Fn.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.EraN.Fn.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.EraN.Fn(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.Fn.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Merge.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  after(fin(P.link(P.link(h, n0, e2), n1, e3), note(note(st, n0, e2), n1, e3)), N.Ext4{P.nil(), P.nil(), e2, e3})

def rw.EraN.Merge.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.EraN.Merge.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.EraN.Merge(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.Merge.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.Data(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  fin(P.drop(P.fresh2(h, a, b), P.form(hb), pb), st)

def rw.EraN.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  fin(P.fresh2(h, a, b), st)

def rw.EraN.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(h, n0, e2), note(st, n0, e2)), N.Ext4{P.nil(), P.nil(), e2, P.nil()})

def rw.EraN.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.MergeL.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(h, n0, e2), note(st, n0, e2)), N.Ext4{P.nil(), P.nil(), e2, P.nil()})

def rw.EraN.MergeL(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.MergeL.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.EraN.MergeR.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(h, n0, e2), note(st, n0, e2)), N.Ext4{P.nil(), P.nil(), e2, P.nil()})

def rw.EraN.MergeR(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.EraN.MergeR.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Root.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  fin(P.link(h, n0, e2), note(st, n0, e2))

def rw.Root.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Root.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(8, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Merge.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e2), n1, e3), n2, e0), (n2 + 1 : U32), (n0 + 1 : U32)), (n2 + 2 : U32), (n1 + 1 : U32)), note(note(note(st, n0, e2), n1, e3), n2, e0))

def rw.Call.Merge.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Call.Merge.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Call.Merge.k2.pre(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +dw) = r
  rw.Call.Merge.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(9, P.form(ha), P.fld(ha)), dw), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.Merge.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Call.Merge.k2.pre(~S, ~R, ~note, ~fin, ~after, P.dup(h, P.form(ha), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.Merge(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.Merge.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Data.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  fin(P.link(h, n0, e0), note(st, n0, e0))

def rw.Call.Data.k1.pre(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & P.PW, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, pw) = r
  rw.Call.Data.k1(~S, ~R, ~note, ~fin, ~after, P.renode_pw(h, a, 5, pw), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.Data(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.Data.k1.pre(~S, ~R, ~note, ~fin, ~after, P.apply(P.free(h, b), ha, pa, hb, pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.EraP.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(h, n0, e0), note(st, n0, e0)), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.Call.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.EraP.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.drop(P.free(h, b), P.form(ha), pa), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.LiftC.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.fuse(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), e0), note(note(st, n0, e2), n1, e0))

def rw.Call.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Call.LiftC.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.MergeL.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), note(note(st, n0, e2), n1, e0))

def rw.Call.MergeL.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Call.MergeL.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.MergeL(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.MergeL.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Call.MergeR.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), note(note(st, n0, e2), n1, e0))

def rw.Call.MergeR.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Call.MergeR.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Call.MergeR(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Call.MergeR.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(9, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Fn.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e3), (n2 + 1 : U32), (n0 + 2 : U32)), e2), e3), note(note(note(st, n0, e0), n1, e2), n2, e3))

def rw.Lift.Fn.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Lift.Fn.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(11, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Lift.Fn.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Lift.Fn.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.Fn(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.Fn.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(1, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Merge.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.fuse(P.fuse(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), n2, e3), (n2 + 1 : U32), (n0 + 2 : U32)), e2), e3), note(note(note(st, n0, e0), n1, e2), n2, e3))

def rw.Lift.Merge.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.Lift.Merge.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.Lift.Merge.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Lift.Merge.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.Merge(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.Merge.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(4, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.Data.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  fin(P.link(h, n0, e0), note(st, n0, e0))

def rw.Lift.Data(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.Data.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd2(5, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.EraP.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(h, n0, e0), note(st, n0, e0)), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.Lift.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.EraP.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.LiftC.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  after(fin(P.fuse(P.link(P.fresh2(h, a, b), e0, e2), e0), note(st, e0, e2)), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.Lift.LiftC.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.fuse(P.fuse(P.link(P.link(P.link(h, n0, e2), (n0 + 1 : U32), (n1 + 1 : U32)), n1, e0), e2), e0), note(note(st, n0, e2), n1, e0))

def rw.Lift.LiftC.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Lift.LiftC.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(11, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.LiftC.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.LiftC.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(10, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.LiftC.peeled(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.Pl, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +e1: U32, +e3: U32) -> R:
  match r:
    case P.Pl{h, +t, +pa, +pb, +e0, +e2}:
      match t:
        case True{}:
          rw.Lift.LiftC.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Lift.LiftC.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.MergeL.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.fuse(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), e2), note(note(st, n0, e0), n1, e2))

def rw.Lift.MergeL.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Lift.MergeL.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.MergeL(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.MergeL.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(14, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.Lift.MergeR.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.fuse(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), e2), note(note(st, n0, e0), n1, e2))

def rw.Lift.MergeR.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.Lift.MergeR.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(10, P.form(ha), P.fld(ha)), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.Lift.MergeR(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.Lift.MergeR.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(15, P.form(hb), P.lift(P.fld(ha), pa, P.fld(hb))), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Fn.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e0), e2, n1), (n1 + 1 : U32), (n0 + 1 : U32)), e3, n2), (n2 + 1 : U32), (n0 + 2 : U32)), note(note(note(st, n0, e0), e2, n1), e3, n2))

def rw.CopyL.Fn.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.CopyL.Fn.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(14, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyL.Fn.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyL.Fn.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.Fn(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.Fn.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(1, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Merge.yes.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.fuse(P.link(P.link(h, e0, e2), n0, e3), e0), note(note(st, e0, e2), n0, e3)), N.Ext4{e0, P.nil(), P.nil(), e3})

def rw.CopyL.Merge.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.Merge.yes.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Merge.no.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), n2, e3), (n1 + 1 : U32), (n0 + 1 : U32)), (n2 + 1 : U32), (n0 + 2 : U32)), note(note(note(st, n0, e0), n1, e2), n2, e3))

def rw.CopyL.Merge.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.CopyL.Merge.no.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyL.Merge.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyL.Merge.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.Merge.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.Merge.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.Data.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  fin(P.link(h, n0, e0), note(st, n0, e0))

def rw.CopyL.Data(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.Data.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd2(5, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.EraP.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(h, n0, e0), note(st, n0, e0)), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyL.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.EraP.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.LiftC.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.fuse(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), e0), note(note(st, n0, e2), n1, e0))

def rw.CopyL.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyL.LiftC.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(12, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.MergeL.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  after(fin(P.fuse(P.link(P.fresh2(h, a, b), e0, e2), e0), note(st, e0, e2)), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyL.MergeL.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), note(note(st, n0, e0), n1, e2))

def rw.CopyL.MergeL.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyL.MergeL.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.MergeL.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.MergeL.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.MergeR.yes.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  after(fin(P.link(P.link(h, e0, n1), n0, e2), note(note(st, e0, n1), n0, e2)), N.Ext4{e0, P.nil(), e2, P.nil()})

def rw.CopyL.MergeR.yes.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyL.MergeR.yes.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.MergeR.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.MergeR.yes.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyL.MergeR.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), note(note(st, n0, e0), n1, e2))

def rw.CopyL.MergeR.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyL.MergeR.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyL.MergeR.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyL.MergeR.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Fn.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e0), e2, n1), (n1 + 1 : U32), (n0 + 1 : U32)), e3, n2), (n2 + 1 : U32), (n0 + 2 : U32)), note(note(note(st, n0, e0), e2, n1), e3, n2))

def rw.CopyR.Fn.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.CopyR.Fn.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(15, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyR.Fn.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyR.Fn.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.Fn(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.Fn.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(1, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Merge.yes.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.fuse(P.link(P.link(h, n0, e2), e0, e3), e0), note(note(st, n0, e2), e0, e3)), N.Ext4{e0, P.nil(), e2, P.nil()})

def rw.CopyR.Merge.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.Merge.yes.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Merge.no.k3(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32, +n1: U32) -> R:
  (h, +n2) = r
  fin(P.link(P.link(P.link(P.link(P.link(h, n0, e0), n1, e2), n2, e3), (n1 + 1 : U32), (n0 + 1 : U32)), (n2 + 1 : U32), (n0 + 2 : U32)), note(note(note(st, n0, e0), n1, e2), n2, e3))

def rw.CopyR.Merge.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  rw.CopyR.Merge.no.k3(~S, ~R, ~note, ~fin, ~after, P.node(h, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0, n1)

def rw.CopyR.Merge.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyR.Merge.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.Merge.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.Merge.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(4, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.Data.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  fin(P.link(h, n0, e0), note(st, n0, e0))

def rw.CopyR.Data(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.Data.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd2(5, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.EraP.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  after(fin(P.link(h, n0, e0), note(st, n0, e0)), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyR.EraP(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.EraP.k1(~S, ~R, ~note, ~fin, ~after, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.LiftC.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.fuse(P.link(P.link(P.link(h, n0, e2), n1, e0), (n1 + 1 : U32), (n0 + 1 : U32)), e0), note(note(st, n0, e2), n1, e0))

def rw.CopyR.LiftC.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyR.LiftC.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(11, P.form(hb), P.fld(hb)), pb), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.LiftC(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.LiftC.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(13, P.form(ha), P.lift(P.fld(hb), pb, P.fld(ha))), pa), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.MergeL.yes.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  after(fin(P.link(P.link(h, n0, e2), e0, n1), note(note(st, n0, e2), e0, n1)), N.Ext4{e0, P.nil(), e2, P.nil()})

def rw.CopyR.MergeL.yes.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyR.MergeL.yes.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.MergeL.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.MergeL.yes.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.MergeL.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), note(note(st, n0, e0), n1, e2))

def rw.CopyR.MergeL.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyR.MergeL.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.MergeL.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.MergeL.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(14, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def rw.CopyR.MergeR.yes(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  after(fin(P.fuse(P.link(P.fresh2(h, a, b), e0, e2), e0), note(st, e0, e2)), N.Ext4{e0, P.nil(), P.nil(), P.nil()})

def rw.CopyR.MergeR.no.k2(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +n0: U32) -> R:
  (h, +n1) = r
  fin(P.link(P.link(P.link(h, n0, e0), n1, e2), (n1 + 1 : U32), (n0 + 1 : U32)), note(note(st, n0, e0), n1, e2))

def rw.CopyR.MergeR.no.k1(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  (h, +n0) = r
  rw.CopyR.MergeR.no.k2(~S, ~R, ~note, ~fin, ~after, P.renode(h, b, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3, n0)

def rw.CopyR.MergeR.no(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  rw.CopyR.MergeR.no.k1(~S, ~R, ~note, ~fin, ~after, P.renode(h, a, P.hd2(15, P.form(hb), P.fld(hb)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

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

def ev.Copy.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (P.link(h, (n0 + 1 : U32), e1), st)

def ev.Copy.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.Copy.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd2(13, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Copy.p2.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (P.link(h, (n0 + 1 : U32), e1), st)

def ev.Copy.p2(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.Copy.p2.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd2(12, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Merge.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (P.link(h, (n0 + 1 : U32), e1), st)

def ev.Merge.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.Merge.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd2(15, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Merge.p2.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (P.link(h, (n0 + 1 : U32), e1), st)

def ev.Merge.p2(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.Merge.p2.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd2(14, P.form(ha), P.fld(ha)), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.Lift.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (h, st)

def ev.Lift.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.Lift.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.LiftC.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (h, st)

def ev.LiftC.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.LiftC.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.CopyL.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (h, st)

def ev.CopyL.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.CopyL.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.CopyR.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (h, st)

def ev.CopyR.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.CopyR.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd(6, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.MergeL.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (h, st)

def ev.MergeL.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.MergeL.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

def ev.MergeR.p1.k1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, r: P.H & U32, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  (h, +n0) = r
  (h, st)

def ev.MergeR.p1(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  ev.MergeR.p1.k1(~S, ~note, P.renode(P.free(h, b), a, P.hd(7, 0), 0), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)

# the event at port p of a node of kind ka, A, the eraser facing it B;
# e0 the peer of A's principal, e1 of its other auxiliary port; the net
# and the family's state, the pairs it makes noted
def event(~S: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, +ka: U32, +p: U32, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> P.H & S:
  match ka p:
    case 3 1:
      ev.Copy.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 2:
      ev.Copy.p2(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 4 1:
      ev.Merge.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 4 2:
      ev.Merge.p2(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 1:
      ev.Lift.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 11 1:
      ev.LiftC.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 1:
      ev.CopyL.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 1:
      ev.CopyR.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 14 1:
      ev.MergeL.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 15 1:
      ev.MergeR.p1(~S, ~note, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case _ _:
      (P.h_err(h), st)

# the rewrite for A, negative principal, meeting B; t is the payload test;
# then `after`, at the external peers where the rule may make an event
def rewrite(~S: Type, ~R: Type, ~note: S -> @+x:U32 -> @+y:U32 -> S, ~fin: P.H -> S -> R, ~after: R -> @+x:N.Ext -> R, +ka: U32, +kb: U32, +t: Bool, h: P.H, st: S, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> R:
  match ka kb:
    case 2 1:
      match t:
        case True{}:
          rw.Ap.Fn.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          fin(P.err_if(U32.is_ne(ka, 8), h), st)
    case 2 4:
      rw.Ap.Merge(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 5:
      match t:
        case True{}:
          rw.Ap.Data.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          fin(P.err_if(U32.is_ne(ka, 8), h), st)
    case 2 7:
      rw.Ap.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 11:
      rw.Ap.LiftC(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 14:
      rw.Ap.MergeL(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 2 15:
      rw.Ap.MergeR(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 1:
      rw.Copy.Fn(~S, ~R, ~note, ~fin, ~after, P.err_if(P.copy_fn_bad(ha, hb), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 4:
      match t:
        case True{}:
          rw.Copy.Merge.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Copy.Merge.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 5:
      rw.Copy.Data(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 7:
      rw.Copy.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 11:
      rw.Copy.LiftC(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 14:
      match t:
        case True{}:
          rw.Copy.MergeL.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Copy.MergeL.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 3 15:
      match t:
        case True{}:
          rw.Copy.MergeR.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.Copy.MergeR.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 1:
      rw.EraN.Fn(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 4:
      rw.EraN.Merge(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 5:
      rw.EraN.Data(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 7:
      rw.EraN.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 11:
      rw.EraN.LiftC(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 14:
      rw.EraN.MergeL(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 6 15:
      rw.EraN.MergeR(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 8 11:
      rw.Root.LiftC(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 4:
      rw.Call.Merge(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 5:
      rw.Call.Data(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 7:
      rw.Call.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 11:
      rw.Call.LiftC(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 14:
      rw.Call.MergeL(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 9 15:
      rw.Call.MergeR(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 1:
      rw.Lift.Fn(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 4:
      rw.Lift.Merge(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 5:
      rw.Lift.Data(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 7:
      rw.Lift.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 11:
      rw.Lift.LiftC.peeled(~S, ~R, ~note, ~fin, ~after, P.peel_ctl(P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)) || P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), a, b, ha, hb, pa, pb, e0, e2), st, a, b, ha, hb, e1, e3)
    case 10 14:
      rw.Lift.MergeL(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 10 15:
      rw.Lift.MergeR(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(ha), pa, P.fld(hb)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 1:
      rw.CopyL.Fn(~S, ~R, ~note, ~fin, ~after, P.err_if(P.copy_fn_bad(ha, hb), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 4:
      match t:
        case True{}:
          rw.CopyL.Merge.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyL.Merge.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 5:
      rw.CopyL.Data(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 7:
      rw.CopyL.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 11:
      rw.CopyL.LiftC(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 14:
      match t:
        case True{}:
          rw.CopyL.MergeL.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyL.MergeL.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 12 15:
      match t:
        case True{}:
          rw.CopyL.MergeR.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyL.MergeR.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 1:
      rw.CopyR.Fn(~S, ~R, ~note, ~fin, ~after, P.err_if(P.copy_fn_bad(ha, hb), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 4:
      match t:
        case True{}:
          rw.CopyR.Merge.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyR.Merge.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 5:
      rw.CopyR.Data(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 7:
      rw.CopyR.EraP(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 11:
      rw.CopyR.LiftC(~S, ~R, ~note, ~fin, ~after, P.err_if(P.lift_wraps(P.fld(hb), pb, P.fld(ha)), h), st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 14:
      match t:
        case True{}:
          rw.CopyR.MergeL.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyR.MergeL.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case 13 15:
      match t:
        case True{}:
          rw.CopyR.MergeR.yes(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
        case False{}:
          rw.CopyR.MergeR.no(~S, ~R, ~note, ~fin, ~after, h, st, a, b, ha, hb, pa, pb, e0, e1, e2, e3)
    case _ _:
      fin(P.err_if(U32.is_ne(ka, 8), h), st)

