import Base
import ./val.bend as V
import ./rules.bend as R
import ./tpl.bend as T
import ./nets.bend as X
import ./kernel.bend as K
import ./knet.bend as KN

# Demand (heap-demand in docs/plans/HeapModel_2026-10-27.md): small nets
# reduced toward the interface, each against the state it should end in
# (done, stuck, out of fuel), its value, and for some the nodes it should
# leave; needs for lazy values met from a list, cell k's value its entry
# k. Then nets that reduce to a number fully, on demand: the value must be
# the full reduction's, in no more interactions, every node but the
# interface and its value freed.
#
#   test_demand

def show_v(v: V.Val) -> String:
  match v:
    case V.VNum{+n}:
      U32.show(n)
    case V.VLazy{+k}:
      "lazy " ++ U32.show(k)
    case _:
      "fn"

def show_m(m: Maybe<&2, V.Val>) -> String:
  match m:
    case Some{v}:
      show_v(v)
    case None{}:
      "none"

type Out is Data:
  Out{+st: U32, v: String, +itrs: U32, +errs: U32, +live: U32, +tab: Bool}

def out(r: K.DRes) -> Out:
  match r:
    case K.DRes{k, +st, +lz, +live, +cap, +reach}:
      match k:
        case K.KRes{v, +itrs, +errs, +ok}:
          Out{st, show_m(v), itrs, errs, live, ok}

def eager(r: K.KRes) -> Out:
  match r:
    case K.KRes{v, +itrs, +errs, +ok}:
      Out{1, show_m(v), itrs, errs, 0, ok}

def out_str(o: Out) -> String:
  match o:
    case Out{+st, +v, +itrs, +errs, +live, +tab}:
      K.st_name(st) ++ " " ++ v ++ " (" ++ U32.show(itrs) ++ " interactions, " ++ U32.show(errs) ++ " errors, " ++
        U32.show(live) ++ " nodes live" ++ KN.table_str(tab) ++ ")"

def mark(ok: Bool) -> String:
  match ok:
    case True{}:
      "ok  "
    case False{}:
      "FAIL"

# 0 for any count of nodes left
def live_ok(+live: U32, +want: U32) -> Bool:
  U32.is_eq(want, 0) || U32.is_eq(live, want)

def case_ok(o: Out, +st: U32, +v: String, +live: U32) -> Bool:
  match o:
    case Out{+s, +w, +itrs, +errs, +l, +tab}:
      U32.is_eq(s, st) && String.eq(w, v) && live_ok(l, live) && tab

# a net on demand, its needs met from vals: the state, value and nodes
# left it should end with
def case_line(+name: String, +t: T.Tpl, +vals: List<&2, V.Val>, +fuel: Nat, +st: U32, +v: String, +live: U32) -> String:
  +o = out(K.run_d(t, fuel, vals))
  mark(case_ok(o, st, v, live)) ++ " " ++ name ++ ": " ++ out_str(o)

# a net on demand as case_line has it, then swept (K.run_ds)
def sweep_line(+name: String, +t: T.Tpl, +vals: List<&2, V.Val>, +fuel: Nat, +st: U32, +v: String, +live: U32) -> String:
  +o = out(K.run_ds(t, fuel, vals))
  mark(case_ok(o, st, v, live)) ++ " " ++ name ++ ": " ++ out_str(o)

def agree(d: Out, e: Out) -> Bool:
  match d e:
    case Out{+st, +v, +itrs, +errs, +live, +tab} Out{+st2, +v2, +itrs2, +errs2, +live2, +tab2}:
      U32.is_eq(st, 1) && String.eq(v, v2) && U32.is_le(itrs, itrs2) && U32.is_eq(errs, errs2) && U32.is_eq(live, 2) && tab && tab2

# a net reducing to a number: on demand, as fully
def agree_line(+name: String, +t: T.Tpl) -> String:
  +d = out(K.run_d(t, 5000000n, []))
  +e = eager(K.run_t(t, 5000000n, True{}))
  mark(agree(d, e)) ++ " " ++ name ++ ": demand " ++ out_str(d) ++ " | full " ++ out_str(e)

def t_i() -> T.Tpl:
  T.Tpl{[X.fn()], [X.l(0, 1, 0, 2)], T.TE{0, 0}, 1}

# \x. plus x x
def t_double() -> T.Tpl:
  T.Tpl{[X.fn(), X.cp(1), X.ap(), X.ap(), X.plus()],
    [X.l(0, 2, 1, 0), X.l(2, 0, 4, 0), X.l(2, 1, 1, 1), X.l(3, 0, 2, 2), X.l(3, 1, 1, 2), X.l(0, 1, 3, 2)],
    T.TE{0, 0}, 5}

def num(+n: U32) -> T.Tpl:
  X.t_one(X.num(n))

# a data node holding fma 1 1, a partial application kept in the table
def t_fma11() -> T.Tpl:
  X.t_one(T.TN{R.KData{}, V.PVal{V.VFun{3, 1, [V.VNum{1}, V.VNum{1}]}}})

def succ() -> T.Tpl:
  X.t_one(X.succ())

# a copy whose input is a lift fed by the copy's second output: polarized,
# no active pair, and a cycle of principal ports each facing an auxiliary
# one, which a walk from the interface would go round forever
def t_cycle() -> T.Tpl:
  T.Tpl{[X.cpl(1, 0), X.ctl(0, True{}, 1)], [X.l(0, 0, 1, 1), X.l(1, 0, 0, 2)], T.TE{0, 1}, 2}

# k lifts
def lifts(k: Nat) -> List<&2, T.TNode>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      X.ctl(0, True{}, 1) <> lifts(p)

# each of k nodes from i on its principal port facing the next one's
# output
def lift_links(k: Nat, +i: U32) -> List<&2, T.TLink>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      X.l(i, 0, (i + 1 : U32), 1) <> lift_links(p, (i + 1 : U32))

# n lifts in a ring through a copy: the copy's principal port facing the
# first lift's output, each lift's the next one's, the last one's the
# copy's first output, the second the root; a vicious circle of n + 1
# nodes, which the walk closes only past the path's first growths
def t_ring(+n: U32) -> T.Tpl:
  T.Tpl{X.cpl(1, 0) <> lifts(U32.to_nat(n)),
    X.l(0, 0, 1, 1) <> List.append(&2, T.TLink, lift_links(U32.to_nat((n - 1 : U32)), 1), [X.l(n, 0, 0, 1)]),
    T.TE{0, 2}, (n + 1 : U32)}

# n lifts in a line from the root to a 5: a path n deep with no cycle
def t_line(+n: U32) -> T.Tpl:
  T.Tpl{List.append(&2, T.TNode, lifts(U32.to_nat(n)), [X.num(5)]),
    List.append(&2, T.TLink, lift_links(U32.to_nat((n - 1 : U32)), 0), [X.l((n - 1 : U32), 0, n, 0)]), T.TE{0, 1}, (n + 1 : U32)}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(case_line("succ L0, L0 = 41", X.t_ap(succ(), X.t_lazy(0)), [V.VNum{41}], 5000n, 1, "42", 2))
    IO.print(case_line("plus x x on L0 = 5, needed twice", X.t_ap(t_double(), X.t_lazy(0)), [V.VNum{5}], 5000n, 1, "10", 2))
    IO.print(case_line("L0 1, L0 = succ", X.t_ap(X.t_lazy(0), num(1)), [V.VFun{1, 1, Nil{}}], 5000n, 1, "2", 2))
    IO.print(case_line("succ (succ L1), L1 = 7", X.t_ap(succ(), X.t_ap(succ(), X.t_lazy(1))), [V.VUnit{}, V.VNum{7}], 5000n, 1, "9", 2))
    IO.print(case_line("K 0 L0: the handle left, its eraser too", X.t_k0(X.t_lazy(0)), [], 5000n, 1, "0", 4))
    IO.print(case_line("I L0: a handle is a value", X.t_ap(t_i(), X.t_lazy(0)), [], 5000n, 1, "lazy 0", 2))
    IO.print(case_line("L0 1, L0 a unit: stuck once met", X.t_ap(X.t_lazy(0), num(1)), [], 5000n, 3, "none", 0))
    IO.print(case_line("0 1: stuck", X.t_ap(num(0), num(1)), [], 5000n, 3, "none", 0))
    IO.print(case_line("succ I: stuck", X.t_ap(succ(), t_i()), [], 5000n, 3, "none", 0))
    IO.print(case_line("a cycle of principal ports facing auxiliary ones: found, not walked", t_cycle(), [], 5000n, 5, "none", 0))
    IO.print(case_line("a vicious circle of 201 nodes: found where the path grows past it", t_ring(200), [], 5000n, 5, "none", 0))
    IO.print(case_line("300 lifts in a line: the path grown three times, no cycle", t_line(300), [], 5000n, 1, "5", 0))
    IO.print(case_line("K 0 omega: omega never reduced", X.t_k_omega(), [], 5000n, 1, "0", 0))
    IO.print(case_line("K 0 (10 2 succ 0): the power never reduced", X.t_k_pow(10), [], 5000n, 1, "0", 0))
    IO.print(case_line("K 0 #64: the numeral left, never erased", X.t_k_num(64), [], 5000n, 1, "0", 132))
    IO.print(sweep_line("K 0 #64 swept: the numeral, cut off from the interface, freed", X.t_k_num(64), [], 5000n, 1, "0", 2))
    IO.print(sweep_line("K 0 (fma 1 1) swept: the partial application's table entry released with its node", X.t_k0(t_fma11()), [], 5000n, 1, "0", 2))
    IO.print(case_line("#3 succ: a function, its body left", X.t_whnf(3), [], 5000n, 1, "none", 0))
    IO.print(case_line("8 2 succ 0 for 100 steps", X.t_pow(8, 2), [], 100n, 4, "none", 0))
    IO.print(agree_line("2 2 succ 0", X.t_pow(2, 2)))
    IO.print(agree_line("5 2 succ 0", X.t_pow(5, 2)))
    IO.print(agree_line("8 2 (plus 1) 0", X.t_pow_plus(8, 2)))
    IO.print(agree_line("8 2 (fma 1 1) 0", X.t_pow_fma(8, 2)))
    IO.print(agree_line("2 2 succ 0 with levels", X.t_pow_lvl(2, 2)))
    IO.print(agree_line("8 2 succ 0 with levels", X.t_pow_lvl(8, 2)))
    IO.print(agree_line("two (two two) succ 0", X.t_two_two_two()))
    IO.print(agree_line("12 succ 0", X.t_chain(12)))
