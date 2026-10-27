import Base
import ./val.bend as V
import ./net.bend as N
import ./tpl.bend as T
import ./nets.bend as X
import ./tracelib.bend as L

# Times one workload under the rewrites as built, for comparing ways of
# running the rule table (docs/plans/EvalSpike_2026-10-26.md,
# spike-node-layout): `k 2 succ 0`, which is 2^k, a numeral applied to a
# numeral, so fans copy live functions and meet.
#
#   bench_rules <k>                 reduce it, report value, counts, time
#   bench_rules trace <k> <steps>   trace it (tracelib), for rule counts

def show_val(m: Maybe<&2, V.Val>) -> String:
  match m:
    case Some{v}:
      match v:
        case V.VNum{+n}:
          U32.show(n)
        case _:
          "a non-number"
    case None{}:
      "no value"

def report(r: N.Q & Maybe<&2, V.Val>) -> String:
  (q, v) = r
  match q:
    case N.Q{st, rq, +itrs, +errs, +ser}:
      show_val(v) ++ ", " ++ U32.show(itrs) ++ " interactions, " ++ U32.show(errs) ++ " errors"

def go.trace(+k: String, +s: String) -> String:
  L.trace(X.t_pow(L.u32_of(k), 2), "k 2 succ 0", L.nat_of(s), 0)

def main.k(+k: U32) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    +res : String = report(T.result(T.run(X.t_pow(k, 2), 4000000n)))
    +t1 : Nat <- IO.now()
    IO.print("k " ++ U32.show(k) ++ ": " ++ res ++ " in " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{p, r}:
      match r:
        case Con{a, r2}:
          match r2:
            case Con{k, r3}:
              match r3:
                case Con{s, r4}:
                  IO.print(go.trace(k, s))
                case Nil{}:
                  IO.print("usage: bench_rules <k> | trace <k> <steps>")
            case Nil{}:
              main.k(L.u32_of(a))
        case Nil{}:
          IO.print("usage: bench_rules <k> | trace <k> <steps>")
    case Nil{}:
      IO.print("usage: bench_rules <k> | trace <k> <steps>")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
