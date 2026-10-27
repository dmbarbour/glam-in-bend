import Base

# glam values, as far as the spike needs them: grown step by step.
type Val is Data:
  VUnit{}
  VNum{+n: U32}
  VLazy{+h: U32}
  VFun{+op: U32, +need: U32, args: List<&2, Val>}
  # never a glam value: a freed entry of a net's data table, linking the
  # next free entry (its index plus one, 0 for none; kprim.bend)
  VFree{+next: U32}
  # never glam values: the kernel's flat forms of a builtin given one or
  # two numbers, VFun{op, need, [VNum{a}]} and VFun{op, need, [VNum{a},
  # VNum{b}]}, which a match shared among copies takes without touching a
  # list (kprim.bend); V.norm turns them back
  VP1{+op: U32, +need: U32, +a: U32}
  VP2{+op: U32, +need: U32, +a: U32, +b: U32}

# Builtins: op 1 succ (one argument), op 2 add (two), op 3 fma, a * b + c
# (three). A builtin waits for `need` more arguments, collected in order.
# The arithmetic on numbers is num1's, num2's and num3's alone, which the
# kernel's native path calls too.

# op on one number
def num1(+op: U32, +a: U32) -> Val:
  match op:
    case 1:
      VNum{(a + 1 : U32)}
    case _:
      VUnit{}

# op on two numbers
def num2(+op: U32, +a: U32, +b: U32) -> Val:
  match op:
    case 2:
      VNum{(a + b : U32)}
    case _:
      VUnit{}

# op on three numbers
def num3(+op: U32, +a: U32, +b: U32, +c: U32) -> Val:
  match op:
    case 3:
      VNum{((a * b : U32) + c : U32)}
    case _:
      VUnit{}

def builtin(+op: U32, args: List<&2, Val>) -> Val:
  match args:
    case Con{VNum{+a}, t}:
      match t:
        case Con{VNum{+b}, u}:
          match u:
            case Con{VNum{+c}, w}:
              num3(op, a, b, c)
            case _:
              num2(op, a, b)
        case _:
          num1(op, a)
    case _:
      VUnit{}

def last.x1(+op: U32, x: Val) -> Val:
  match x:
    case VNum{+a}:
      num1(op, a)
    case _:
      VUnit{}

def last.x2(+op: U32, +a: U32, x: Val) -> Val:
  match x:
    case VNum{+b}:
      num2(op, a, b)
    case _:
      num1(op, a)

def last.x3(+op: U32, +a: U32, +b: U32, x: Val) -> Val:
  match x:
    case VNum{+c}:
      num3(op, a, b, c)
    case _:
      num2(op, a, b)

# builtin(op, args ++ [x]) without building the list: the collected
# arguments matched where they lie, x where it would follow them. Past
# three numbers, x cannot matter.
def builtin_last(+op: U32, args: List<&2, Val>, x: Val) -> Val:
  match args:
    case Nil{}:
      last.x1(op, x)
    case Con{VNum{+a}, t}:
      match t:
        case Nil{}:
          last.x2(op, a, x)
        case Con{VNum{+b}, u}:
          match u:
            case Nil{}:
              last.x3(op, a, b, x)
            case Con{VNum{+c}, w}:
              num3(op, a, b, c)
            case _:
              num2(op, a, b)
        case _:
          num1(op, a)
    case _:
      VUnit{}

# a value as glam sees it: a flat form as the VFun it stands for
def norm(v: Val) -> Val:
  match v:
    case VP1{+op, +need, +a}:
      VFun{op, need, [VNum{a}]}
    case VP2{+op, +need, +a, +b}:
      VFun{op, need, [VNum{a}, VNum{b}]}
    case _:
      v

def fun.go(+last: Bool, +op: U32, +need: U32, args: List<&2, Val>, x: Val) -> Val:
  match last:
    case True{}:
      builtin_last(op, args, x)
    case False{}:
      VFun{op, (need - 1 : U32), List.append(&2, Val, args, [x])}

def vp1.more(+op: U32, +need: U32, +a: U32, x: Val) -> Val:
  match x:
    case VNum{+b}:
      VP2{op, need, a, b}
    case _:
      VFun{op, need, [VNum{a}, x]}

def vp1.go(+last: Bool, +op: U32, +need: U32, +a: U32, x: Val) -> Val:
  match last:
    case True{}:
      last.x2(op, a, x)
    case False{}:
      vp1.more(op, (need - 1 : U32), a, x)

def vp2.go(+last: Bool, +op: U32, +need: U32, +a: U32, +b: U32, x: Val) -> Val:
  match last:
    case True{}:
      last.x3(op, a, b, x)
    case False{}:
      VFun{op, (need - 1 : U32), [VNum{a}, VNum{b}, x]}

def apply_fn(f: Val, x: Val) -> Val:
  match f:
    case VFun{+op, +need, args}:
      fun.go(U32.is_eq(need, 1), op, need, args, x)
    case VP1{+op, +need, +a}:
      vp1.go(U32.is_eq(need, 1), op, need, a, x)
    case VP2{+op, +need, +a, +b}:
      vp2.go(U32.is_eq(need, 1), op, need, a, b, x)
    case _:
      VUnit{}

# A fan's identity: the site it was lowered at, the instantiation it came
# from, and its level, the depth of boxes around it (after Lamping). Two
# fans are residuals of one duplication when all three agree
# (docs/plans/NetPairing_2026-10-26.md, "Derivation").
type FanId is Data:
  FanId{+site: U32, +inst: U32, +lvl: U32}

def fan_new(+site: U32, +inst: U32, +lvl: U32) -> FanId:
  FanId{site, inst, lvl}

# the level of a fan in a net built without levels (hand-built nets,
# terms lowered with --labels): the level checks skip it
def nolvl() -> U32:
  4294967295

def fan_eq(a: FanId, b: FanId) -> Bool:
  match a b:
    case FanId{+s1, +i1, +l1} FanId{+s2, +i2, +l2}:
      U32.is_eq(s1, s2) && U32.is_eq(i1, i2) && U32.is_eq(l1, l2)

# what a store slot carries beside its four words: a function's or an
# application's level; a control node's index n and offset, which moves
# every level above n up by `by` (a bracket for by 1) or down by it (a
# croissant for by 1). Lowering fuses a run of brackets ending in at most
# one croissant into one control, down only by 1.
type Pay is Data:
  PNone{}
  PVal{v: Val}
  PFan{f: FanId}
  PLvl{+n: U32}
  PLift{+n: U32, +up: Bool, +by: U32}

def lift_lvl.go(above: Bool, +up: Bool, +by: U32, +j: U32) -> U32:
  match above up:
    case True{} True{}:
      (j + by : U32)
    case True{} False{}:
      (j - by : U32)
    case False{} _:
      j

# level j after the control n, up, by
def lift_lvl(+n: U32, +up: Bool, +by: U32, +j: U32) -> U32:
  lift_lvl.go(U32.is_gt(j, n), up, by, j)

def lift_pay.b(+n: U32, +up: Bool, +by: U32, pb: Pay) -> Pay:
  match pb:
    case PLvl{+j}:
      PLvl{lift_lvl(n, up, by, j)}
    case PLift{+j, +u, +b}:
      PLift{lift_lvl(n, up, by, j), u, b}
    case PFan{f}:
      match f:
        case FanId{+site, +inst, +l}:
          PFan{FanId{site, inst, lift_lvl(n, up, by, l)}}
    case _:
      pb

# B's payload (a level, a fan's, or a control node's index) passed
# through the control node whose payload is pa
def lift_pay(pa: Pay, pb: Pay) -> Pay:
  match pa:
    case PLift{+n, +up, +by}:
      lift_pay.b(n, up, by, pb)
    case _:
      pb

def bool_eq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

# two control nodes of one index and offset, which cancel facing each other
def ctl_eq(a: Pay, b: Pay) -> Bool:
  match a b:
    case PLift{+n, +u, +x} PLift{+m, +v, +y}:
      U32.is_eq(n, m) && bool_eq(u, v) && U32.is_eq(x, y)
    case _ _:
      False{}

# Fusing controls: two controls one after the other on a wire, `first`
# crossed first, act as one when first moves up by k1 and second's index
# lies in [n1, n1 + k1]: then every level, and every control index that
# crosses them in that order, moves as through the one control (n1,
# k1 + k2). Offsets down stay at most 1.
type Fuse is Data:
  FNo{}
  FId{}
  FTo{p: Pay}

def compose.down.go(gt: Bool, eq: Bool, +n: U32, +b1: U32, +b2: U32) -> Fuse:
  match gt eq:
    case True{} _:
      FTo{PLift{n, True{}, (b1 - b2 : U32)}}
    case False{} True{}:
      FId{}
    case False{} False{}:
      FTo{PLift{n, False{}, (b2 - b1 : U32)}}

def compose.down(+n: U32, +b1: U32, +b2: U32) -> Fuse:
  compose.down.go(U32.is_gt(b1, b2), U32.is_eq(b1, b2), n, b1, b2)

def compose.ok(ok: Bool, +n1: U32, +b1: U32, +u2: Bool, +b2: U32) -> Fuse:
  match ok:
    case False{}:
      FNo{}
    case True{}:
      match u2:
        case True{}:
          FTo{PLift{n1, True{}, (b1 + b2 : U32)}}
        case False{}:
          compose.down(n1, b1, b2)

# the one control acting as `first` then `second`, when there is one
def compose(first: Pay, second: Pay) -> Fuse:
  match first second:
    case PLift{+n1, +u1, +b1} PLift{+n2, +u2, +b2}:
      compose.ok(u1 && U32.is_le(n1, n2) && U32.is_le(n2, (n1 + b1 : U32)), n1, b1, u2, b2)
    case _ _:
      FNo{}

def pay_lvl(p: Pay) -> U32:
  match p:
    case PLvl{+n}:
      n
    case _:
      0

# an application and a function meet at one level in a well-formed net
def lvl_eq(+a: Pay, +b: Pay) -> Bool:
  U32.is_eq(pay_lvl(a), pay_lvl(b))
