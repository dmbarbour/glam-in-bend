import Base

# How pure work shares Bend's one IO event loop. A spawned computation
# sends a message every 10 ms while the main computation runs n steps of
# pure work in k slices, polling the channel between slices, optionally
# after yielding with IO.sleep(0).
#
#   interleave <steps> <slices> <yield: 0|1>

# sends 0, 1, 2, ... every 10 ms, n times
def ticker(n: Nat, +c: Chan(U32), +i: U32) -> IO(Unit):
  match n:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+p:
      do IO<Unit>:
        IO.sleep(10)
        r : Result<&1, &1, U32, Unit> <- Chan.send(U32, c, i)
        ticker(p, c, (i + 1 : U32))

# pure work the compiler can't fold away
def work(n: Nat, +k: U32, acc: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+p:
      work(p, k, ((acc * 31 : U32) + k : U32))

def heard(p: Poll<&1, &1, Maybe<&1, U32>, Unit>, +got: U32) -> U32:
  match p:
    case Ready{m}:
      match m:
        case Some{x}:
          (got + 1 : U32)
        case None{}:
          got
    case Wait{w}:
      got

def pause(y: Bool) -> IO(Unit):
  match y:
    case True{}:
      IO.sleep(0)
    case False{}:
      IO.pure(Unit, Unit{})

# s slices of per steps each; between slices, maybe yield, then poll once
def drive(s: Nat, +per: Nat, +y: Bool, +c: Chan(U32), acc: U32, +got: U32) -> IO(U32 & U32):
  match s:
    case 0n:
      IO.pure(U32 & U32, (acc, got))
    case 1n+p:
      +a = work(per, 7, acc)
      do IO<U32 & U32>:
        pause(y)
        r : Poll<&1, &1, Maybe<&1, U32>, Unit> <- Chan.try_recv(U32, c, 0)
        drive(p, per, y, c, a, heard(r, got))

def nums(xs: List<String>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{s, rest}:
      Maybe.default(&2, U32, U32.read(s), 0) <> nums(rest)

def at(xs: List<&2, U32>, n: Nat) -> U32:
  match xs n:
    case Nil{} _:
      0
    case Con{x, _} 0n:
      x
    case Con{_, rest} 1n+p:
      at(rest, p)

def show(r: U32 & U32, +ms: Nat) -> String:
  (acc, got) = r
  "heard " ++ U32.show(got) ++ " ticks in " ++ Nat.show(ms) ++ " ms (acc " ++ U32.show(acc) ++ ")"

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    +ns : List<&2, U32> = nums(xs)
    +n : U32 = at(ns, 1n)
    +k : U32 = at(ns, 2n)
    +y : Bool = U32.is_eq(at(ns, 3n), 1)
    +c : Chan(U32) <- Chan.new(U32, 1000)
    IO.spawn(Unit, ticker(50n, c, 0))
    +t0 : Nat <- IO.now()
    r : U32 & U32 <- drive(U32.to_nat(k), U32.to_nat(U32.div(n, k)), y, c, 0, 0)
    +t1 : Nat <- IO.now()
    IO.print(U32.show(k) ++ " slice(s): " ++ show(r, Nat.sub(t1, t0)))
