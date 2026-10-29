import Base
import ./flag.bend as F

# Does a constant Bool from another file fold away? A hot loop of n steps
# from the command line, each through a check guarded by F.debug_mode()
# (mode 0) or with no check at all (mode 1); both pay the same branch on
# the mode. With the flag False, mode 0 costing what mode 1 costs means
# Bend and clang folded the guard; with it True, the audit's cost shows.
# Modes 2 and 3 do the same from two call sites picked by i's parity, the
# guarded function shared in the hot path. Count instructions at n, 2n and
# 4n (scripts/count.sh): the slope is the cost of a step.
#
#   const_flag <mode> <n>

# a step clang cannot sum in closed form: the accumulator fed back
# through a shift
def plain(+acc: U32, +i: U32) -> U32:
  (((acc * 3 : U32) + i : U32) + (acc >> 5n : U32) : U32)

# an audit worth avoiding: 16 more rounds of the same mixing
def audit(k: Nat, +x: U32) -> U32:
  match k:
    case 0n:
      x
    case 1n+p:
      audit(p, plain(x, 1))

def step.go(dbg: Bool, +acc: U32, +i: U32) -> U32:
  match dbg:
    case True{}:
      plain(audit(16n, acc), i)
    case False{}:
      plain(acc, i)

def checked(+acc: U32, +i: U32) -> U32:
  step.go(F.debug_mode(), acc, i)

# the guarded step from two call sites, picked by i's parity, which no
# compiler can hoist out of the loop (mode 2); the same shape unguarded
# (mode 3)
def shared.go(odd: Bool, +acc: U32, +i: U32) -> U32:
  match odd:
    case True{}:
      checked(acc, i)
    case False{}:
      plain(checked(acc, i), 1)

def unshared.go(odd: Bool, +acc: U32, +i: U32) -> U32:
  match odd:
    case True{}:
      plain(acc, i)
    case False{}:
      plain(plain(acc, i), 1)

def one(+mode: U32, +acc: U32, +i: U32) -> U32:
  match mode:
    case 0:
      checked(acc, i)
    case 1:
      plain(acc, i)
    case 2:
      shared.go(U32.is_eq((i .&. 1 : U32), 1), acc, i)
    case _:
      unshared.go(U32.is_eq((i .&. 1 : U32), 1), acc, i)

def loop(n: Nat, +mode: U32, +acc: U32, +i: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+p:
      loop(p, mode, one(mode, acc, i), (i + 1 : U32))

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{p, r}:
      match r:
        case Con{m, r2}:
          match r2:
            case Con{c, r3}:
              IO.print(U32.show(loop(U32.to_nat(Maybe.default(&2, U32, U32.read(c), 1000)), Maybe.default(&2, U32, U32.read(m), 0), 0, 0)))
            case Nil{}:
              IO.print("usage: const_flag <mode> <n>")
        case Nil{}:
          IO.print("usage: const_flag <mode> <n>")
    case Nil{}:
      IO.print("usage: const_flag <mode> <n>")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
