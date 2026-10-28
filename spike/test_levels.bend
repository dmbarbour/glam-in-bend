import Base
import ./val.bend as V
import ./rules.bend as R
import ./net.bend as N
import ./tpl.bend as T
import ./nets.bend as X
import ./kernel.bend as K

# The level checks, the kernel's field guards and control fusion, on small
# nets with known outcomes: each through the spike, the kernel's
# interpreted table and its generated rewrites, against the value and the
# errors each should report. The spike's levels are U32 and the kernel's
# fields 24 bits, so a raise can pass the kernel's range and not the
# spike's; a field the kernel cannot hold is an error when it loads.
# Controls of one index meeting as different runs are peeled, the same
# interactions in all three. Then `m 2 succ 0` with levels, whose
# interaction counts must agree.
#
#   test_levels

def show_m(m: Maybe<&2, V.Val>) -> String:
  match m:
    case Some{v}:
      match v:
        case V.VNum{+n}:
          U32.show(n)
        case _:
          "fn"
    case None{}:
      "none"

type Out is Data:
  Out{v: String, +itrs: U32, +errs: U32}

def spike_out(r: N.Q & Maybe<&2, V.Val>) -> Out:
  (q, v) = r
  match q:
    case N.Q{st, rq, +itrs, +errs, +ser}:
      Out{show_m(v), itrs, errs}

def sel_u(b: Bool, +x: U32, +y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

# a table whose live entries do not match their holders counts 1000 errors
def kernel_out(r: K.KRes) -> Out:
  match r:
    case K.KRes{v, +itrs, +errs, +ok}:
      Out{show_m(v), itrs, (errs + sel_u(ok, 0, 1000) : U32)}

def out_str(o: Out) -> String:
  match o:
    case Out{+v, +itrs, +errs}:
      v ++ " (" ++ U32.show(itrs) ++ " interactions, " ++ U32.show(errs) ++ " errors)"

def out_ok(o: Out, +v: String, +errs: U32) -> Bool:
  match o:
    case Out{+w, +i, +e}:
      String.eq(w, v) && U32.is_eq(e, errs)

def mark(ok: Bool) -> String:
  match ok:
    case True{}:
      "ok  "
    case False{}:
      "FAIL"

# a net, the value it reduces to ("none" for a function: only data is read
# off the root), and the errors the spike and the kernel report
def case_line(+name: String, +t: T.Tpl, +v: String, +es: U32, +ek: U32) -> String:
  +s = spike_out(T.result(T.run(t, 5000n)))
  +r = kernel_out(K.run_t(t, 5000n, False{}))
  +f = kernel_out(K.run_t(t, 5000n, True{}))
  mark(out_ok(s, v, es) && out_ok(r, v, ek) && out_ok(f, v, ek)) ++ " " ++ name ++ ": spike " ++ out_str(s) ++
    " | ref " ++ out_str(r) ++ " | fast " ++ out_str(f)

def cap() -> U32:
  16777216

# a copy at level lc meeting the identity at level lf; one copy erased
def t_copy_fn(+lc: U32, +lf: U32) -> T.Tpl:
  T.Tpl{[X.cpl(1, lc), X.fnl(lf), X.era()], [X.l(0, 0, 1, 0), X.l(1, 1, 1, 2), X.l(0, 2, 2, 0)], T.TE{0, 1}, 3}

# a control (0, up by) meeting the identity at level j
def t_lift_fn(+by: U32, +j: U32) -> T.Tpl:
  T.Tpl{[X.ctl(0, True{}, by), X.fnl(j)], [X.l(0, 0, 1, 0), X.l(1, 1, 1, 2)], T.TE{0, 1}, 2}

# a control (n1, up by1) meeting one facing consumers (n2, up by2), 5
# behind them
def t_lift_liftc(+n1: U32, +by1: U32, +n2: U32, +by2: U32) -> T.Tpl:
  T.Tpl{[X.ctl(n1, True{}, by1), X.ctlc(n2, True{}, by2), X.num(5)], [X.l(0, 0, 1, 0), X.l(1, 1, 2, 0)], T.TE{0, 1}, 3}

# a control (n1, up1 by1) meeting one facing consumers (n2, up2 by2), 5
# behind them
def t_ctl_pair(+n1: U32, +u1: Bool, +b1: U32, +n2: U32, +u2: Bool, +b2: U32) -> T.Tpl:
  T.Tpl{[X.ctl(n1, u1, b1), X.ctlc(n2, u2, b2), X.num(5)], [X.l(0, 0, 1, 0), X.l(1, 1, 2, 0)], T.TE{0, 1}, 3}

# the identity at level j
def t_id(+j: U32) -> T.Tpl:
  T.Tpl{[X.fnl(j)], [X.l(0, 1, 0, 2)], T.TE{0, 0}, 1}

# a fan built without levels at a site, copying 5, one copy erased
def t_site(+site: U32) -> T.Tpl:
  T.Tpl{[X.cp(site), X.num(5), X.era()], [X.l(0, 0, 1, 0), X.l(0, 2, 2, 0)], T.TE{0, 1}, 3}

# a builtin with op `op`, needing one argument, applied to 5
def t_op(+op: U32) -> T.Tpl:
  T.Tpl{[X.ap(), T.TN{R.KData{}, V.PVal{V.VFun{op, 1, Nil{}}}}, X.num(5)], [X.l(0, 0, 1, 0), X.l(0, 1, 2, 0)], T.TE{0, 2}, 3}

def itrs_of(o: Out) -> U32:
  match o:
    case Out{+v, +itrs, +errs}:
      itrs

# controls of one index meeting as different runs (kprim.bend's peeling):
# the value, no errors, and the interactions all three must make
def peel_line(+name: String, +t: T.Tpl, +itrs: U32) -> String:
  +s = spike_out(T.result(T.run(t, 5000n)))
  +r = kernel_out(K.run_t(t, 5000n, False{}))
  +f = kernel_out(K.run_t(t, 5000n, True{}))
  mark(out_ok(s, "5", 0) && out_ok(r, "5", 0) && out_ok(f, "5", 0) &&
      U32.is_eq(itrs_of(s), itrs) && U32.is_eq(itrs_of(r), itrs) && U32.is_eq(itrs_of(f), itrs)) ++
    " " ++ name ++ ": spike " ++ out_str(s) ++ " | ref " ++ out_str(r) ++ " | fast " ++ out_str(f)

# the profiling strategy on facing controls (kstrat.bend's Profiling):
# its line, each run weighted as its unit brackets would interact, a
# peel counted where the kernel splits a run
def prof_line(+name: String, +t: T.Tpl, +want: String) -> String:
  +p = K.profile_t(t, 5000n, True{})
  mark(String.eq(p, want)) ++ " profile, " ++ name ++ ": " ++ p

def pow_line(+m: U32) -> String:
  +s = spike_out(T.result(T.run(X.t_pow_lvl(m, 2), 5000000n)))
  +f = kernel_out(K.run_t(X.t_pow_lvl(m, 2), 5000000n, True{}))
  +r = kernel_out(K.run_t(X.t_pow_lvl(m, 2), 5000000n, False{}))
  mark(String.eq(out_str(s), out_str(f)) && String.eq(out_str(s), out_str(r)) && out_ok(s, U32.show((1 << U32.to_nat(m) : U32)), 0)) ++
    " " ++ U32.show(m) ++ " 2 succ 0 with levels: spike " ++ out_str(s) ++ " | ref " ++ out_str(r) ++ " | fast " ++ out_str(f)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(case_line("copy at 0 meets a function at 1", t_copy_fn(0, 1), "none", 0, 0))
    IO.print(case_line("copy at 1 meets a function at 1", t_copy_fn(1, 1), "none", 1, 1))
    IO.print(case_line("copy at 2 meets a function at 1", t_copy_fn(2, 1), "none", 1, 1))
    IO.print(case_line("raise by 1 past a function at 1", t_lift_fn(1, 1), "none", 0, 0))
    IO.print(case_line("raise to 2^24 - 1", t_lift_fn((cap() - 2 : U32), 1), "none", 0, 0))
    IO.print(case_line("raise to 2^24", t_lift_fn((cap() - 1 : U32), 1), "none", 0, 1))
    IO.print(case_line("raise past 2^32, offset too big", t_lift_fn(4294967295, 1), "none", 1, 2))
    IO.print(case_line("lift raises a liftc's index to 2^24", t_lift_liftc(0, (cap() - 1 : U32), 1, 1), "5", 0, 1))
    IO.print(case_line("liftc raises a lift's index to 2^24", t_lift_liftc(1, 1, 0, (cap() - 1 : U32)), "5", 0, 1))
    IO.print(case_line("liftc raises a lift's index past 2^32", t_lift_liftc(1, 1, 0, 4294967295), "5", 1, 2))
    IO.print(case_line("lift and liftc cancel", t_lift_liftc(0, 1, 0, 1), "5", 0, 0))
    IO.print(peel_line("a lift raising 2 cancels a liftc raising 1, its rest passes 5", t_ctl_pair(0, True{}, 2, 0, True{}, 1), 3))
    IO.print(peel_line("a liftc raising 2 cancels a lift raising 1", t_ctl_pair(0, True{}, 1, 0, True{}, 2), 3))
    IO.print(peel_line("a drop facing a lift raising 2 crosses its first unit", t_ctl_pair(0, True{}, 2, 0, False{}, 1), 6))
    IO.print(peel_line("a liftc raising 2 facing a drop", t_ctl_pair(0, False{}, 1, 0, True{}, 2), 6))
    IO.print(peel_line("different indices cross whole", t_ctl_pair(0, True{}, 2, 1, True{}, 1), 4))
    IO.print(prof_line("a raise of 2 peeled by a raise of 1", t_ctl_pair(0, True{}, 2, 0, True{}, 1), "5 (3, 0); weighted 3, 1 peels, 0 wide; pairs 8.5:1 10.5:1 10.11:1"))
    IO.print(prof_line("a drop facing a raise of 2", t_ctl_pair(0, True{}, 2, 0, False{}, 1), "5 (6, 0); weighted 6, 1 peels, 0 wide; pairs 8.5:1 8.11:1 10.5:2 10.11:2"))
    IO.print(prof_line("runs of 2 and 1 crossing weigh 2", t_ctl_pair(0, True{}, 2, 1, True{}, 1), "5 (4, 0); weighted 6, 0 peels, 0 wide; pairs 8.5:1 8.11:1 10.5:1 10.11:1"))
    IO.print(prof_line("equal runs of 3 cancelling weigh 3", t_ctl_pair(0, True{}, 3, 0, True{}, 3), "5 (2, 0); weighted 4, 0 peels, 0 wide; pairs 8.5:1 10.11:1"))
    IO.print(case_line("a function at 2^24 - 1", t_id((cap() - 1 : U32)), "none", 0, 0))
    IO.print(case_line("a function at 2^24", t_id(cap()), "none", 0, 1))
    IO.print(case_line("a fan at site 2^24 - 1", t_site((cap() - 1 : U32)), "5", 0, 0))
    IO.print(case_line("a fan at site 2^24", t_site(cap()), "5", 0, 1))
    IO.print(case_line("succ by its op", t_op(1), "6", 0, 0))
    IO.print(case_line("an op past the field, not succ", t_op((cap() + 1 : U32)), "fn", 0, 0))
    IO.print(pow_line(2))
    IO.print(pow_line(3))
    IO.print(pow_line(5))
    IO.print(pow_line(8))
