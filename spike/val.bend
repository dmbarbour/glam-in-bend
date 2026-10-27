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
# from, and its duplication history, the fans it has commuted through and
# on which branch (newest first). Two fans are residuals of one
# duplication exactly when their identities are equal (Design.md,
# "Interaction Nets"). h hashes the rest, to compare quickly.
type Step is Data:
  Step{+h: U32, +b: U32}

type FanId is Data:
  FanId{+site: U32, +inst: U32, +h: U32, ctx: List<&2, Step>}

def mix(+a: U32, +b: U32) -> U32:
  +x = ((a .^. b : U32) * 2654435761 : U32)
  (x .^. (x >> 15n : U32) : U32)

def fan_new(+site: U32, +inst: U32) -> FanId:
  FanId{site, inst, mix(site, inst), Nil{}}

def fan_hash(f: FanId) -> U32:
  match f:
    case FanId{site, inst, h, ctx}:
      h

# f, having commuted through the fan g, on g's branch b
def fan_extend(f: FanId, +gh: U32, +b: U32) -> FanId:
  match f:
    case FanId{+site, +inst, +h, ctx}:
      FanId{site, inst, mix(h, mix(gh, b)), Step{gh, b} <> ctx}

def steps_eq(a: List<&2, Step>, b: List<&2, Step>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{Step{+h1, +b1}, t1} Con{Step{+h2, +b2}, t2}:
      U32.is_eq(h1, h2) && U32.is_eq(b1, b2) && steps_eq(t1, t2)
    case _ _:
      False{}

def fan_eq.ctx(same: Bool, a: List<&2, Step>, b: List<&2, Step>) -> Bool:
  match same:
    case True{}:
      steps_eq(a, b)
    case False{}:
      False{}

def fan_eq(a: FanId, b: FanId) -> Bool:
  match a b:
    case FanId{+s1, +i1, +h1, c1} FanId{+s2, +i2, +h2, c2}:
      fan_eq.ctx(U32.is_eq(s1, s2) && U32.is_eq(i1, i2) && U32.is_eq(h1, h2), c1, c2)

# what a store slot carries beside its four words
type Pay is Data:
  PNone{}
  PVal{v: Val}
  PFan{f: FanId}
