import Base

# Making a zeroed array of 2^d words, d from the command line, then one
# read: Bend fills it element by element (docs/BendIssues.md, "Array
# creation fills word by word"). Count instructions at d, d + 1, d + 2:
# the slope is the cost a word.
#
#   zero_fill <d>

def first(r: Array<U32> & U32) -> U32:
  (a, +v) = r
  v

def run(+d: Nat) -> U32:
  first(Array.get(U32, [0 : U32^d], 3))

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{p, r}:
      match r:
        case Con{a, r2}:
          IO.print(U32.show(run(U32.to_nat(Maybe.default(&2, U32, U32.read(a), 10)))))
        case Nil{}:
          IO.print("usage: zero_fill <d>")
    case Nil{}:
      IO.print("usage: zero_fill <d>")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
