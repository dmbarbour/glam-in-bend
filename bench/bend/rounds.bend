import Base

# Pages owned linearly: a tree of affine arrays. A round hands each worker
# its own page through a parallel call, then swaps subtrees so pages
# migrate between workers. No @unsafe anywhere.
type Pages is Type:
  One{a: Array<U32>}
  Two{l: Pages, r: Pages}

def make(+d: Nat, +pd: Nat) -> Pages:
  match d:
    case 0n:
      One{Array.new(U32, pd, 0)}
    case 1n+p:
      Two{make(p, pd), make(p, pd)}

def step.fin(+k: U32, +i: U32, r: Array<U32> & U32) -> Array<U32>:
  (a, +x) = r
  Array.set(U32, a, i, (x + k : U32))

def step(+k: U32, +mask: U32, a: Array<U32>) -> Array<U32>:
  +i = ((k * 2654435761 : U32) .&. mask : U32)
  step.fin(k, i, Array.get(U32, a, i))

# one worker's quantum: f scattered read-modify-writes in its own page
def churn(f: Nat, +k: U32, +mask: U32, a: Array<U32>) -> Array<U32>:
  match f:
    case 0n:
      a
    case 1n+p:
      churn(p, (k + 1 : U32), mask, step(k, mask, a))

# one round: every page's worker runs in parallel; subtrees swap afterwards
def round(p: Pages, +f: Nat, +k: U32, +mask: U32) -> Pages:
  match p:
    case One{a}:
      One{churn(f, k, mask, a)}
    case Two{l, r}:
      x y = round(l, f, (k * 3 : U32), mask) round(r, f, ((k * 3 : U32) + 1 : U32), mask)
      Two{y, x}

def rounds(n: Nat, +k: U32, p: Pages, +f: Nat, +mask: U32) -> Pages:
  match n:
    case 0n:
      p
    case 1n+q:
      rounds(q, (k + 1 : U32), round(p, f, k, mask), f, mask)

def snd(r: Array<U32> & U32) -> U32:
  (a, x) = r
  x

def check(p: Pages) -> U32:
  match p:
    case One{a}:
      snd(Array.get(U32, a, 7))
    case Two{l, r}:
      (check(l) + check(r) : U32)

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

# args: log2 workers, rounds, fuel per worker per round, log2 page cells
def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    +ns : List<&2, U32> = nums(xs)
    +w : U32 = at(ns, 1n)
    +r : U32 = at(ns, 2n)
    +f : U32 = at(ns, 3n)
    +pd : U32 = at(ns, 4n)
    +mask : U32 = ((1 << U32.to_nat(pd) : U32) - 1 : U32)
    p : Pages = make(U32.to_nat(w), U32.to_nat(pd))
    +t0 : Nat <- IO.now()
    +c : U32 = check(rounds(U32.to_nat(r), 1, p, U32.to_nat(f), mask))
    +t1 : Nat <- IO.now()
    IO.print(U32.show((1 << U32.to_nat(w) : U32)) ++ " workers, " ++ U32.show(r) ++ " rounds of " ++ U32.show(f) ++ " steps: " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms (check " ++ U32.show(c) ++ ")")
