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

# A fan's identity: a static label, the site it was lowered at and the
# instantiation it came from. Two fans are residuals of one duplication
# when their labels are equal, which holds wherever no two duplications
# under one label meet (docs/plans/NetPairing_2026-10-26.md: duplication
# histories, tried first, pair wrongly).
type FanId is Data:
  FanId{+site: U32, +inst: U32}

def fan_new(+site: U32, +inst: U32) -> FanId:
  FanId{site, inst}

def fan_eq(a: FanId, b: FanId) -> Bool:
  match a b:
    case FanId{+s1, +i1} FanId{+s2, +i2}:
      U32.is_eq(s1, s2) && U32.is_eq(i1, i2)

# what a store slot carries beside its four words
type Pay is Data:
  PNone{}
  PVal{v: Val}
  PFan{f: FanId}
