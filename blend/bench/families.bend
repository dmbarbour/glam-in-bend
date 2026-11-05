# Families of modules for measuring how Blend's cost grows with a
# module's definitions: prints a module of N definitions of one shape,
# definition i calling earlier ones, and a main calling the last. Each is
# measured at N, 2N and 4N (blend/bench/README.md).
#
#   bend blend/bench/families.bend chain|fan|dense N > module.blend
import Base

# a family's shape: i calling i-1 (chain); i-1, i-2, i/2 and i/3 (fan);
# every earlier definition (dense)
type Sh is Data:
  Chain{}
  Fan{}
  Dense{}
  Unknown{}

def sh.of.k(chain: Bool, fan: Bool, dense: Bool) -> Sh:
  match chain fan dense:
    case True{} _ _:
      Chain{}
    case False{} True{} _:
      Fan{}
    case False{} False{} True{}:
      Dense{}
    case False{} False{} False{}:
      Unknown{}

def sh.of(+w: String) -> Sh:
  sh.of.k(String.eq(w, "chain"), String.eq(w, "fan"), String.eq(w, "dense"))

def before.k(keep: Bool, +j: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match keep:
    case True{}:
      Con{j, rest}
    case False{}:
      rest

# those of js before i, in order
def before(js: List<&2, U32>, +i: U32) -> List<&2, U32>:
  match js:
    case Nil{}:
      Nil{}
    case Con{+j, t}:
      before.k(U32.is_lt(j, i), j, before(t, i))

# k numbers from j up
def upto(k: Nat, +j: U32) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      Con{j, upto(p, (j + 1 : U32))}

# the definitions i calls, the first innermost
def calls(sh: Sh, +i: U32) -> List<&2, U32>:
  match sh:
    case Chain{}:
      before([(i - 1 : U32)], i)
    case Fan{}:
      before([(i - 1 : U32), (i - 2 : U32), (i / 2 : U32), (i / 3 : U32)], i)
    case Dense{}:
      upto(U32.to_nat(i), 0)
    case Unknown{}:
      Nil{}

# the calls' openings, the last call's first
def opens(js: List<&2, U32>, acc: String) -> String:
  match js:
    case Nil{}:
      acc
    case Con{+j, t}:
      opens(t, "f" ++ U32.show(j) ++ "(" ++ acc)

def closes(js: List<&2, U32>) -> String:
  match js:
    case Nil{}:
      ""
    case Con{j, t}:
      ")" ++ closes(t)

def body(+js: List<&2, U32>) -> String:
  opens(js, "") ++ "n" ++ closes(js)

def defn(sh: Sh, +i: U32) -> String:
  "def f" ++ U32.show(i) ++ "(+n: U32) -> U32:\n  " ++ body(calls(sh, i)) ++ "\n\n"

# definitions i to i + k - 1, each printed as it is made
def defs(k: Nat, +sh: Sh, +i: U32) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+p:
      do IO<Unit>:
        IO.write(defn(sh, i))
        defs(p, sh, (i + 1 : U32))

def usage() -> IO(Unit):
  IO.die(Unit, 2, "usage: bend blend/bench/families.bend chain|fan|dense N")

def module(+sh: Sh, +n: U32) -> IO(Unit):
  match sh:
    case Unknown{}:
      usage()
    case _:
      do IO<Unit>:
        IO.write("import Base\n\n")
        defs(U32.to_nat(n), sh, 0)
        IO.write("def main() -> IO(Unit):\n  IO.print(U32.show(f" ++ U32.show((n - 1 : U32)) ++ "(1)))\n\n")

# the arguments after the program's name: the shape, then N
def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{prog, rest}:
      match rest:
        case Con{w, more}:
          match more:
            case Con{num, extra}:
              module(sh.of(w), Maybe.default(&2, U32, U32.read(num), 0))
            case Nil{}:
              usage()
        case Nil{}:
          usage()
    case Nil{}:
      usage()

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
