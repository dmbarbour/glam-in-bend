import Base
import ./val.bend as V
import ./rules.bend as R
import ./net.bend as N
import ./tpl.bend as T
import ./nets.bend as X

# Reduces nets with known results: small ones, Church numerals applied to
# each other (where fan pairing decides the answer), then a long chain for
# throughput.
#
#   test_net <n>

def show_val(m: Maybe<&2, V.Val>) -> String:
  match m:
    case Some{v}:
      match v:
        case V.VNum{n}:
          U32.show(n)
        case _:
          "a non-number"
    case None{}:
      "no value"

def counts(q: N.Q) -> String:
  match q:
    case N.Q{st, rq, +itrs, +errs}:
      U32.show(itrs) ++ " interactions, " ++ U32.show(errs) ++ " errors"

def report(r: N.Q & Maybe<&2, V.Val>) -> String:
  (q, v) = r
  show_val(v) ++ " (" ++ counts(q) ++ ")"

def check(+name: String, t: T.Tpl) -> String:
  name ++ ": " ++ report(T.result(T.run(t, 5000n)))

def arg(xs: List<String>) -> U32:
  match xs:
    case Con{_, r}:
      match r:
        case Con{s, _}:
          Maybe.default(&2, U32, U32.read(s), 0)
        case Nil{}:
          0
    case Nil{}:
      0

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    +n : U32 = arg(xs)
    IO.print(check("two two succ 0, want 4", X.t_pow(2, 2)))
    IO.print(check("three three succ 0, want 27", X.t_pow(3, 3)))
    IO.print(check("two three succ 0, want 9", X.t_pow(2, 3)))
    IO.print(check("three two succ 0, want 8", X.t_pow(3, 2)))
    IO.print(check("two (two two) succ 0, want 16", X.t_two_two_two()))
    IO.print(check("(\\t -> t t) two succ 0, want 4", X.t_self(2)))
    IO.print(check("(\\t -> t t) three succ 0, want 27", X.t_self(3)))
    +t0 : Nat <- IO.now()
    +res : String = report(T.result(T.run(X.t_chain(n), U32.to_nat((n * 20 : U32)))))
    +t1 : Nat <- IO.now()
    IO.print(U32.show(n) ++ " succ 0, want " ++ U32.show(n) ++ ": " ++ res ++ " in " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms, building included")
