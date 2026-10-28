import Base
import ./val.bend as V
import ./kprim.bend as P

# The kernel's primitives one at a time, for their cost in instructions
# (spike-node-layout in docs/plans/EvalSpike_2026-10-26.md): each op runs
# n times in one loop, so the slope of instructions over n, 2n and 4n
# (scripts/count.sh) is its cost, the loop's own (op 0) included.
#
#   bench_kprim <op> <n>
#
# Ops: 0 nothing; 1 read a word; 2 write one; 3 allocate a node and free
# it; 4 link two auxiliary ports; 5 push an active pair and pop it; 6 read
# a table entry; 7 duplicate an entry and drop the copy; 8 put an entry
# and take it; 9 put fma 1 1 and apply it to a number by the general path;
# 10 apply plus 1 (form 3) to a number natively; 11 V.apply_fn on fma 1 1
# and a number, Bend values only; 12 is a table entry a function; 13 put a
# number (immediate) and take it.

type B is Type:
  B{h: P.H, st: P.Stk, +acc: U32}

def fma11() -> V.Val:
  V.VFun{3, 1, [V.VNum{1}, V.VNum{1}]}

def b.acc(r: P.H & U32, st: P.Stk, +acc: U32) -> B:
  (h, +x) = r
  B{h, st, (acc + x : U32)}

def b.h(h: P.H, st: P.Stk, +acc: U32) -> B:
  B{h, st, acc}

def b.free(r: P.H & U32, st: P.Stk, +acc: U32) -> B:
  (h, +n) = r
  B{P.free(h, n), st, acc}

def b.pop(pp: P.Pop, +acc: U32) -> B:
  match pp:
    case P.Pop{h, st, +cap, +x, +y, +ok}:
      B{h, st, (acc + x : U32)}

def b.val(r: P.H & V.Val, st: P.Stk, +acc: U32) -> B:
  (h, v) = r
  B{h, st, acc}

def b.dup(r: P.H & U32, st: P.Stk, +acc: U32) -> B:
  (h, +w) = r
  B{P.drop(h, 0, w), st, acc}

def b.take(r: P.H & U32, st: P.Stk, +acc: U32) -> B:
  (h, +w) = r
  b.val(P.tab_take(h, w), st, acc)

def b.pw(r: P.H & P.PW, st: P.Stk, +acc: U32) -> B:
  (h, pw) = r
  match pw:
    case P.PW{+m, +f, +w}:
      B{h, st, (acc + w : U32)}

def b.apply(r: P.H & U32, st: P.Stk, +acc: U32, +i: U32) -> B:
  (h, +w) = r
  b.pw(P.apply(h, P.hd2(9, 0, 0), w, P.hd2(5, 1, 0), i), st, acc)

def b.fn(v: V.Val, +acc: U32) -> U32:
  match v:
    case V.VNum{+n}:
      (acc + n : U32)
    case _:
      acc

def b.isfn(r: P.H & Bool, st: P.Stk, +acc: U32) -> B:
  (h, +t) = r
  match t:
    case True{}:
      B{h, st, (acc + 1 : U32)}
    case False{}:
      B{h, st, acc}

def b.imm(r: P.H & P.PW, st: P.Stk, +acc: U32) -> B:
  (h, pw) = r
  match pw:
    case P.PW{+m, +f, +w}:
      b.val(P.take(h, m, f, w), st, (acc + w : U32))

# node 0 and node 1 are allocated, entry 0 holds fma 1 1
def step(b: B, +op: U32, +i: U32) -> B:
  match b:
    case B{h, st, +acc}:
      match op:
        case 1:
          b.acc(P.rd(h, (i .&. 7 : U32)), st, acc)
        case 2:
          b.h(P.wr(h, 3, i), st, acc)
        case 3:
          b.free(P.node(h, P.hd(7, 0), 0), st, acc)
        case 4:
          b.h(P.link(h, 1, 5), st, acc)
        case 5:
          b.pop(P.pop(P.E{h, P.push(st, 1)}, 64), acc)
        case 6:
          b.val(P.tab_get(h, 0), st, acc)
        case 7:
          b.dup(P.dup(h, 0, 0), st, acc)
        case 8:
          b.take(P.tab_put(h, fma11()), st, acc)
        case 9:
          b.apply(P.tab_put(h, fma11()), st, acc, i)
        case 10:
          b.pw(P.apply(h, P.hd2(9, 3, 2), 1, P.hd2(5, 1, 0), i), st, acc)
        case 11:
          B{h, st, b.fn(V.apply_fn(fma11(), V.VNum{i}), acc)}
        case 12:
          b.isfn(P.val_is_fn(h, 0, 0, 0), st, acc)
        case 13:
          b.imm(P.put(h, V.VNum{i}), st, acc)
        case _:
          B{h, st, acc}

def loop(n: Nat, +op: U32, b: B, +i: U32) -> B:
  match n:
    case 0n:
      b
    case 1n+p:
      loop(p, op, step(b, op, i), (i + 1 : U32))

def setup.e(r: P.H & U32) -> P.H:
  (h, +e) = r
  h

def setup.n(r: P.H & U32) -> P.H:
  (h, +n) = r
  h

# two nodes and one entry
def setup() -> P.H:
  setup.e(P.tab_put(setup.n(P.node(setup.n(P.node(P.h_new(), P.hd(10, 0), 0)), P.hd(10, 0), 0)), fma11()))

# the net, an empty stack, nothing accumulated
def start(r: P.Stk & U32) -> B:
  (st, +cap) = r
  B{setup(), st, 0}

def report(b: B) -> String:
  match b:
    case B{h, st, +acc}:
      "acc " ++ U32.show(acc)

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{p, r}:
      match r:
        case Con{a, r2}:
          match r2:
            case Con{c, r3}:
              IO.print(report(loop(U32.to_nat(Maybe.default(&2, U32, U32.read(c), 1000)), Maybe.default(&2, U32, U32.read(a), 0), start(P.stk_new(64)), 0)))
            case Nil{}:
              IO.print("usage: bench_kprim <op> <n>")
        case Nil{}:
          IO.print("usage: bench_kprim <op> <n>")
    case Nil{}:
      IO.print("usage: bench_kprim <op> <n>")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
