import Base
import ./store.bend as S

# Exercises the store: allocate n nodes across pages, write and read back
# every word, free every other node, allocate them again. Prints checks and
# per-phase times.
#
#   bench_store <n>

type T is Type:
  T{st: S.Store, +acc: U32}

def t_st(t: T) -> S.Store:
  match t:
    case T{st, acc}:
      st

def t_acc(t: T) -> T & U32:
  match t:
    case T{st, +acc}:
      (T{st, acc}, acc)

# allocate one node and write its four words from its reference
def fill.fin(r: S.Store & U32, +acc: U32) -> T:
  (st, +ref) = r
  st1 = S.st_set(st, ref, 0, ref)
  st2 = S.st_set(st1, ref, 1, (ref + 1 : U32))
  st3 = S.st_set(st2, ref, 2, (ref + 2 : U32))
  st4 = S.st_set(st3, ref, 3, (ref + 3 : U32))
  T{st4, (acc + ref : U32)}

def fill.step(t: T) -> T:
  match t:
    case T{st, +acc}:
      fill.fin(S.st_alloc(st), acc)

def fill(n: Nat, t: T) -> T:
  match n:
    case 0n:
      t
    case 1n+p:
      fill(p, fill.step(t))

# the i-th node allocated from fresh pages sits at page i/4096, slot i%4096
def nth(+i: U32) -> U32:
  S.mk_ref((i >> 12n : U32), (i .&. 4095 : U32), 0)

def sum4.fin(r: S.Store & U32, +acc: U32) -> T:
  (st, +x) = r
  T{st, (acc + x : U32)}

def sum4.step(+ref: U32, t: T) -> T:
  match t:
    case T{st, +acc}:
      sum4.fin(S.st_get(st, ref, 3), acc)

# read word 3 of nodes 0 .. n-1
def sum(n: Nat, +i: U32, t: T) -> T:
  match n:
    case 0n:
      t
    case 1n+p:
      sum(p, (i + 1 : U32), sum4.step(nth(i), t))

def free.step(+ref: U32, t: T) -> T:
  match t:
    case T{st, +acc}:
      T{S.st_free(st, ref), acc}

# free nodes 0, 2, 4, ... below 2n
def free_even(n: Nat, +i: U32, t: T) -> T:
  match n:
    case 0n:
      t
    case 1n+p:
      free_even(p, (i + 2 : U32), free.step(nth(i), t))

def report.pages(r: S.Store & U32, +errs: U32, +acc: U32) -> String:
  (st, +np) = r
  "pages " ++ U32.show(np) ++ ", missing-page errors " ++ U32.show(errs) ++ ", acc " ++ U32.show(acc)

def report.fin(r: S.Store & U32, +acc: U32) -> String:
  (st, +errs) = r
  report.pages(S.st_pages(st), errs, acc)

def report(t: T) -> String:
  match t:
    case T{st, +acc}:
      report.fin(S.st_errs(st), acc)

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

# what sum(n) must give: word 3 of node i is ref + 3
def expect(n: Nat, +i: U32, +acc: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+p:
      expect(p, (i + 1 : U32), (acc + (nth(i) + 3 : U32) : U32))

def ms(+a: Nat, +b: Nat) -> String:
  Nat.show(Nat.sub(b, a)) ++ " ms"

# after the read-back: free half, allocate it again, report
def rest(r2: T & U32, +n: U32, +t0: Nat, +ta: Nat, +tb: Nat) -> IO(Unit):
  (t2, +got) = r2
  do IO<Unit>:
    IO.print("alloc+write " ++ U32.show(n) ++ " nodes: " ++ ms(t0, ta) ++ "; read back: " ++ ms(ta, tb))
    IO.print("read sum " ++ U32.show(got) ++ ", expected " ++ U32.show(expect(U32.to_nat(n), 0, 0)))
    t3 : T = free_even(U32.to_nat(U32.div(n, 2)), 0, T{t_st(t2), 0})
    +tc : Nat <- IO.now()
    t4 : T = fill(U32.to_nat(U32.div(n, 2)), t3)
    +td : Nat <- IO.now()
    IO.print("free half: " ++ ms(tb, tc) ++ "; allocate half again: " ++ ms(tc, td))
    IO.print(report(t4))

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    +n : U32 = arg(xs)
    +t0 : Nat <- IO.now()
    t1 : T = fill(U32.to_nat(n), T{S.st_new(), 0})
    +ta : Nat <- IO.now()
    t2 : T = sum(U32.to_nat(n), 0, T{t_st(t1), 0})
    +tb : Nat <- IO.now()
    rest(t_acc(t2), n, t0, ta, tb)
