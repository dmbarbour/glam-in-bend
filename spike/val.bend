import Base

# glam values, as far as the spike needs them: grown step by step.
type Val is Data:
  VUnit{}
  VNum{+n: U32}
  VLazy{+h: U32}
  VFun{+op: U32, +need: U32, args: List<&2, Val>}

# Builtins: op 1 succ (one argument), op 2 add (two). A builtin waits for
# `need` more arguments, collected in order.
def builtin(+op: U32, args: List<&2, Val>) -> Val:
  match op:
    case 1:
      match args:
        case Con{VNum{+n}, t}:
          VNum{(n + 1 : U32)}
        case _:
          VUnit{}
    case 2:
      match args:
        case Con{VNum{+a}, t}:
          match t:
            case Con{VNum{+b}, u}:
              VNum{(a + b : U32)}
            case _:
              VUnit{}
        case _:
          VUnit{}
    case _:
      VUnit{}

def apply_fn(f: Val, x: Val) -> Val:
  match f:
    case VFun{+op, +need, args}:
      match need:
        case 1:
          builtin(op, List.append(&2, Val, args, [x]))
        case _:
          VFun{op, (need - 1 : U32), List.append(&2, Val, args, [x])}
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

def fan_eq(a: FanId, b: FanId) -> Bool:
  match a b:
    case FanId{+s1, +i1, +l1} FanId{+s2, +i2, +l2}:
      U32.is_eq(s1, s2) && U32.is_eq(i1, i2) && U32.is_eq(l1, l2)

# what a store slot carries beside its four words: a function's or an
# application's level; a control node's index n and direction (up: a
# bracket, raising levels above n by one; else a croissant, lowering them)
type Pay is Data:
  PNone{}
  PVal{v: Val}
  PFan{f: FanId}
  PLvl{+n: U32}
  PLift{+n: U32, +up: Bool}

def lift_lvl.go(above: Bool, +up: Bool, +j: U32) -> U32:
  match above up:
    case True{} True{}:
      (j + 1 : U32)
    case True{} False{}:
      (j - 1 : U32)
    case False{} _:
      j

# level j after the control node n, up
def lift_lvl(+n: U32, +up: Bool, +j: U32) -> U32:
  lift_lvl.go(U32.is_gt(j, n), up, j)

def lift_pay.b(+n: U32, +up: Bool, pb: Pay) -> Pay:
  match pb:
    case PLvl{+j}:
      PLvl{lift_lvl(n, up, j)}
    case PLift{+j, +u}:
      PLift{lift_lvl(n, up, j), u}
    case PFan{f}:
      match f:
        case FanId{+site, +inst, +l}:
          PFan{FanId{site, inst, lift_lvl(n, up, l)}}
    case _:
      pb

# B's payload (a level, a fan's, or a control node's index) passed
# through the control node whose payload is pa
def lift_pay(pa: Pay, pb: Pay) -> Pay:
  match pa:
    case PLift{+n, +up}:
      lift_pay.b(n, up, pb)
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

# two control nodes of one kind and index, which cancel facing each other
def ctl_eq(a: Pay, b: Pay) -> Bool:
  match a b:
    case PLift{+n, +u} PLift{+m, +v}:
      U32.is_eq(n, m) && bool_eq(u, v)
    case _ _:
      False{}

def pay_lvl(p: Pay) -> U32:
  match p:
    case PLvl{+n}:
      n
    case _:
      0

# an application and a function meet at one level in a well-formed net
def lvl_eq(+a: Pay, +b: Pay) -> Bool:
  U32.is_eq(pay_lvl(a), pay_lvl(b))
