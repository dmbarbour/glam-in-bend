import Base

# Does a template specialize code on a constant data value
# (docs/BendIssues.md, "Compile-time specialization"; EvalSpike's
# spike-templates)? A hot loop of n steps from the command line, each
# mixing an accumulator with constants written five ways: by hand (mode
# 0); a constructor passed as a template argument (1); a list passed as a
# template argument, read to a fixed depth (2); a constructor from a def
# (3); a recursive interpreter over a constant list of operations (4). A
# template cannot match its argument itself (a match takes a variable), so
# each hands it to a helper of its own, called once. Count instructions at n, 2n and 4n
# (scripts/count.sh): the slope is the cost of a step, and a mode costing
# what mode 0 does has had its constant folded. Bend 2.0.39, 2026-10-31,
# n 10^7 to 4 x 10^7: 7.25 a step in modes 0, 1 and 3, 36 in mode 2, 102
# in mode 4. A flat constructor folds, from a template or a def alike; a
# list does not.
#
#   template_const <mode> <n>

type Par is Data:
  Par{+c1: U32, +c2: U32}

type Op is Data:
  OMul{+k: U32}
  OAddI{}
  OAddDiv{+k: U32}

# by hand
def step.h(+acc: U32, +i: U32) -> U32:
  (((acc * 3 : U32) + i : U32) + (acc / 32 : U32) : U32)

def step.t.go(p: Par, +acc: U32, +i: U32) -> U32:
  match p:
    case Par{+c1, +c2}:
      (((acc * c1 : U32) + i : U32) + (acc / c2 : U32) : U32)

# a constructor, a template's argument
def step.t(~p: Par, +acc: U32, +i: U32) -> U32:
  step.t.go(p, acc, i)

def step.l.go(ps: List<&2, U32>, +acc: U32, +i: U32) -> U32:
  match ps:
    case Con{+c1, t}:
      match t:
        case Con{+c2, u}:
          (((acc * c1 : U32) + i : U32) + (acc / c2 : U32) : U32)
        case Nil{}:
          acc
    case Nil{}:
      acc

# a list, a template's argument, read to a fixed depth
def step.l(~ps: List<&2, U32>, +acc: U32, +i: U32) -> U32:
  step.l.go(ps, acc, i)

def par() -> Par:
  Par{3, 32}

# a constructor from a def, at run time
def step.r(p: Par, +acc: U32, +i: U32) -> U32:
  match p:
    case Par{+c1, +c2}:
      (((acc * c1 : U32) + i : U32) + (acc / c2 : U32) : U32)

def ops() -> List<&2, Op>:
  [OMul{3}, OAddI{}, OAddDiv{32}]

# a recursive interpreter: x the value so far, acc the step's input
def run.op(o: Op, +x: U32, +acc: U32, +i: U32) -> U32:
  match o:
    case OMul{+k}:
      (x * k : U32)
    case OAddI{}:
      (x + i : U32)
    case OAddDiv{+k}:
      (x + (acc / k : U32) : U32)

def run.ops(os: List<&2, Op>, +x: U32, +acc: U32, +i: U32) -> U32:
  match os:
    case Nil{}:
      x
    case Con{o, t}:
      run.ops(t, run.op(o, x, acc, i), acc, i)

def one(+mode: U32, +acc: U32, +i: U32) -> U32:
  match mode:
    case 0:
      step.h(acc, i)
    case 1:
      step.t(~Par{3, 32}, acc, i)
    case 2:
      step.l(~[3, 32], acc, i)
    case 3:
      step.r(par(), acc, i)
    case _:
      run.ops(ops(), acc, acc, i)

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
              IO.print("usage: template_const <mode> <n>")
        case Nil{}:
          IO.print("usage: template_const <mode> <n>")
    case Nil{}:
      IO.print("usage: template_const <mode> <n>")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
