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
