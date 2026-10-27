import Base
import ./tpl.bend as T
import ./nets.bend as X
import ./tracelib.bend as L

# Traces one of the test nets (tracelib.bend describes the output).
#
#   trace <net> <steps> [from]   nets: pow22 pow33 pow23 pow32 two_two_two
#                                      self2 self3 chain5
#
# runs at most <steps> interactions, listing those numbered from [from] on.

def net_of(+k: U32) -> T.Tpl:
  match k:
    case 0:
      X.t_pow(2, 2)
    case 1:
      X.t_pow(3, 3)
    case 2:
      X.t_pow(2, 3)
    case 3:
      X.t_pow(3, 2)
    case 4:
      X.t_two_two_two()
    case 5:
      X.t_self(2)
    case 6:
      X.t_self(3)
    case _:
      X.t_chain(5)

def pick(b: Bool, +x: U32, +y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

def find(ns: List<&2, String>, +name: String, +i: U32) -> U32:
  match ns:
    case Nil{}:
      i
    case Con{n, t}:
      pick(String.eq(n, name), i, find(t, name, (i + 1 : U32)))

def names() -> List<&2, String>:
  ["pow22", "pow33", "pow23", "pow32", "two_two_two", "self2", "self3", "chain5"]

def go(+name: String, +steps: Nat, +from: U32) -> String:
  L.trace(net_of(find(names(), name, 0)), name, steps, from)

def go.args(xs: List<String>) -> String:
  match xs:
    case Con{p, r}:
      match r:
        case Con{name, r2}:
          match r2:
            case Con{s, r3}:
              match r3:
                case Con{f, r4}:
                  go(name, L.nat_of(s), L.u32_of(f))
                case Nil{}:
                  go(name, L.nat_of(s), 0)
            case Nil{}:
              go(name, 0n, 0)
        case Nil{}:
          "usage: trace <net> <steps> [from]"
    case Nil{}:
      "usage: trace <net> <steps> [from]"

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    IO.print(go.args(xs))
