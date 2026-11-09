import Base

# glam values, as far as the spike needs them: grown step by step.
type Val is Data:
  VUnit{}
  VNum{+n: U32}
  VLazy{+h: U32}
  VFun{+op: U32, +need: U32, args: List<&2, Val>}
  # a glam list, texts and binaries among them (DistilledDesign: lists
  # are ropes; texts and binaries are lists): its first form, a Bend list
  # of values, an entry of a net's table that copies share and erasure
  # drops (HelloLadder's ladder-text; netdata-structures decides the
  # lasting one). Not a function, not a number, no placeholder.
  VList{xs: List<&2, Val>}
  # a glam dict, its first form: its entries, each a key, any comparable
  # value, and its value (HelloLadder's ladder-dicts; netdata-structures
  # decides the lasting one)
  VDict{es: List<&2, Ent>}
  # a glam error: a permanent failure as a value, its diagnostic itself a
  # glam value, a text for now (`net-error-values`). Applying one gives
  # it; a builtin given one gives it; a builtin given arguments it has no
  # case for gives one saying so. Copied, erased and passed by controls
  # as any data is.
  VErr{e: Val}
  # never a glam value: a freed entry of a net's data table, linking the
  # next free entry (its index plus one, 0 for none; kprim.bend)
  VFree{+next: U32}
  # never a glam value: the kernel's flat form of a builtin given two
  # numbers, VFun{op, need, [VNum{a}, VNum{b}]}, which a match shared among
  # copies takes without touching a list (kprim.bend), one number being
  # held in the node itself; V.norm turns it back
  VP2{+op: U32, +need: U32, +a: U32, +b: U32}

# a dict's entry: its key, a comparable value, and its value
type Ent is Data:
  Ent{key: Val, v: Val}

# Builtins: op 1 succ (one argument), op 2 add (two), op 3 fma, a * b + c
# (three), op 4 append, glam's `++` (two lists: HelloLadder's
# ladder-lists), op 5 get, reading a dict's field, its key collected as a
# text (ladder-lambda.dicts). A builtin waits for `need` more arguments,
# collected in order. The arithmetic on numbers is num1's, num2's and
# num3's alone, which the kernel's native path calls too; lists only meet
# the general path (V.apply_fn), a list being an entry of a net's table.
# A builtin given arguments it has no case for answers an error saying so
# (`net-error-values`); every path to one answer gives one message, so
# that builtin_last computes what builtin does (law builtin_last_agrees).

# a Bend string's characters as a glam text's values
def text(s: String) -> List<&2, Val>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, rest}:
      match c:
        case Chr{+code}:
          Con{VNum{code}, text(rest)}

# an error whose diagnostic is the text msg
def err(msg: String) -> Val:
  VErr{VList{text(msg)}}

def bname(+op: U32) -> String:
  match op:
    case 1:
      "succ"
    case 2:
      "add"
    case 3:
      "fma"
    case 4:
      "++"
    case 5:
      "a field's read"
    case _:
      "a builtin"

# the error a builtin gives for arguments it has no case for
def nocase(+op: U32) -> Val:
  err(bname(op) ++ " met an argument it has no case for")

def num1.go(+t: Bool, +a: U32) -> Val:
  match t:
    case True{}:
      VNum{(a + 1 : U32)}
    case False{}:
      err("a builtin met a number it has no case for")

def num2.go(+t: Bool, +a: U32, +b: U32) -> Val:
  match t:
    case True{}:
      VNum{(a + b : U32)}
    case False{}:
      err("a builtin met two numbers it has no case for")

def num3.go(+t: Bool, +a: U32, +b: U32, +c: U32) -> Val:
  match t:
    case True{}:
      VNum{((a * b : U32) + c : U32)}
    case False{}:
      err("a builtin met three numbers it has no case for")

# op on one number (each tests its op by a Bool, which a proof can split)
def num1(+op: U32, +a: U32) -> Val:
  num1.go(U32.is_eq(op, 1), a)

# op on two numbers
def num2(+op: U32, +a: U32, +b: U32) -> Val:
  num2.go(U32.is_eq(op, 2), a, b)

# op on three numbers
def num3(+op: U32, +a: U32, +b: U32, +c: U32) -> Val:
  num3.go(U32.is_eq(op, 3), a, b, c)

# Placeholders: VFree and VP2 are never glam values. A flat form may
# stand at the top of a value the kernel holds, never among a function's
# collected arguments: apply_fn collects each normalized, and the kernel
# normalizes every value it hands out (laws norm_not_placeholder,
# apply_keeps_clean, norm_keeps_clean). A free slot read as a value is a
# kernel fault, which the kernel reports as an error, never a value.

def is_ph(v: Val) -> Bool:
  match v:
    case VFree{+k}:
      True{}
    case VP2{+op, +need, +a, +b}:
      True{}
    case _:
      False{}

def is_free(v: Val) -> Bool:
  match v:
    case VFree{+k}:
      True{}
    case _:
      False{}

# v, and whether it is a free slot, without sharing it: a value matched
# whole passes through
def free_chk(v: Val) -> Val & Bool:
  match v:
    case VFree{+k}:
      (VFree{k}, True{})
    case _:
      (v, False{})

# no placeholder among these values
def all_np(l: List<&2, Val>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Bool.not(is_ph(h)), all_np(t))

# no placeholder among a function's collected arguments
def clean(v: Val) -> Bool:
  match v:
    case VFun{+op, +need, args}:
      all_np(args)
    case _:
      True{}

def lst2.go(+t: Bool, xs: List<&2, Val>, ys: List<&2, Val>) -> Val:
  match t:
    case True{}:
      VList{List.append(&2, Val, xs, ys)}
    case False{}:
      err("a builtin met two lists it has no case for")

# op on two lists
def lst2(+op: U32, xs: List<&2, Val>, ys: List<&2, Val>) -> Val:
  lst2.go(U32.is_eq(op, 4), xs, ys)

# a dict member read: a function whose collected arguments hold a
# placeholder is no glam value, and the kernel stores none (it normalizes
# what it hands out); the read answers an error where it would, defence
# in depth as free_chk is, and so that applying keeps a value clean (law
# apply_keeps_clean)
def member.go(+ok: Bool, v: Val) -> Val:
  match ok:
    case True{}:
      v
    case False{}:
      err("a dict member holds a placeholder, which is no glam value: a kernel fault")

def member(+v: Val) -> Val:
  member.go(clean(v), v)

# Keys: any comparable value (only-comparables-compare), compared
# structurally: numbers by value, lists and dicts entry by entry, unit
# with unit; a dict entry by entry in its order for now, which an atom, a
# singleton dict, meets exactly (a dict's canonical order waits for
# netdata-structures). A work list of pairs under fuel, Bend admitting no
# mutual recursion between values and their lists; a key too large for
# the fuel compares unequal.
type Pq is Data:
  Pq{a: Val, b: Val}

def zipv(xs: List<&2, Val>, ys: List<&2, Val>, rest: List<&2, Pq>) -> Maybe<&2, List<&2, Pq>>:
  match xs ys:
    case Nil{} Nil{}:
      Some{rest}
    case Con{x, xr} Con{y, yr}:
      zipv(xr, yr, Con{Pq{x, y}, rest})
    case _ _:
      None{}

def zipe(xs: List<&2, Ent>, ys: List<&2, Ent>, rest: List<&2, Pq>) -> Maybe<&2, List<&2, Pq>>:
  match xs ys:
    case Nil{} Nil{}:
      Some{rest}
    case Con{Ent{ka, va}, xr} Con{Ent{kb, vb}, yr}:
      zipe(xr, yr, Con{Pq{ka, kb}, Con{Pq{va, vb}, rest}})
    case _ _:
      None{}

def keep(+eq: Bool, rest: List<&2, Pq>) -> Maybe<&2, List<&2, Pq>>:
  match eq:
    case True{}:
      Some{rest}
    case False{}:
      None{}

# one pair compared: the pairs left to compare, or none where they differ
def veq.step(q: Pq, rest: List<&2, Pq>) -> Maybe<&2, List<&2, Pq>>:
  match q:
    case Pq{a, b}:
      match a b:
        case VNum{+x} VNum{+y}:
          keep(U32.is_eq(x, y), rest)
        case VList{xs} VList{ys}:
          zipv(xs, ys, rest)
        case VDict{xs} VDict{ys}:
          zipe(xs, ys, rest)
        case VUnit{} VUnit{}:
          Some{rest}
        case _ _:
          None{}

def veq.go(k: Nat, m: Maybe<&2, List<&2, Pq>>) -> Bool:
  match k:
    case 0n:
      False{}
    case 1n+p:
      match m:
        case None{}:
          False{}
        case Some{ps}:
          match ps:
            case Nil{}:
              True{}
            case Con{q, rest}:
              veq.go(p, veq.step(q, rest))

# two keys alike
def veq(a: Val, b: Val) -> Bool:
  veq.go(1048576n, Some{[Pq{a, b}]})

# a key as a diagnostic names it: an atom by its name, a text in brackets
def key_show(k: Val) -> List<&2, Val>:
  match k:
    case VDict{es}:
      match es:
        case Con{e, more}:
          match e:
            case Ent{kk, vv}:
              match kk:
                case VList{t}:
                  t
                case _:
                  text("a key")
        case Nil{}:
          text("{}")
    case VList{t}:
      List.append(&2, Val, text("[\""), List.append(&2, Val, t, text("\"]")))
    case _:
      text("a key")

def dfind.k(+hit: Bool, v: Val, r: Val) -> Val:
  match hit:
    case True{}:
      member(v)
    case False{}:
      r

# the value at a key, an error naming the key where there is none: the
# rest searched whatever the head (eager, as Bend is), so that no lambda
# enters a proof
def dfind(es: List<&2, Ent>, +key: Val) -> Val:
  match es:
    case Nil{}:
      VErr{VList{List.append(&2, Val, text("the dict has no field "), key_show(key))}}
    case Con{e, rest}:
      match e:
        case Ent{k, v}:
          dfind.k(veq(k, key), v, dfind(rest, key))

def dhas.k(+hit: Bool, rest: Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      rest

def dhas(es: List<&2, Ent>, +key: Val) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{e, rest}:
      match e:
        case Ent{k, v}:
          dhas.k(veq(k, key), dhas(rest, key))

def dunion.k(+dup: Bool, r: Val) -> Val:
  match dup:
    case True{}:
      err("a key is introduced twice: a dict's members share no key")
    case False{}:
      r

# b's entries after acc's, each key new (dict-literals-introduce-in-order:
# a union is shallow)
def dunion(b: List<&2, Ent>, +acc: List<&2, Ent>) -> Val:
  match b:
    case Nil{}:
      VDict{acc}
    case Con{e, rest}:
      match e:
        case Ent{+k, v}:
          dunion.k(dhas(acc, k), dunion(rest, List.append(&2, Ent, acc, [Ent{k, v}])))

# a value that may key a dict: a number, a list, a dict, unit
def comparable(v: Val) -> Bool:
  match v:
    case VNum{+n}:
      True{}
    case VList{xs}:
      True{}
    case VDict{es}:
      True{}
    case VUnit{}:
      True{}
    case _:
      False{}

def tag.go(+ok: Bool, k: Val, v: Val) -> Val:
  match ok:
    case True{}:
      VDict{[Ent{k, v}]}
    case False{}:
      err("a key must be comparable: a number, a list, a dict or unit")

# the dict of one entry, v at key k: what `k:v` and `(k:)` build
def tagv(+k: Val, v: Val) -> Val:
  tag.go(comparable(k), k, v)

# Builtins on numbers and lists, ops below 5, by the arguments' shapes
def builtin.n(+op: U32, args: List<&2, Val>) -> Val:
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
    case Con{VList{xs}, t}:
      match t:
        case Con{VList{ys}, u}:
          lst2(op, xs, ys)
        case _:
          nocase(op)
    case _:
      nocase(op)

def last.x1(+op: U32, x: Val) -> Val:
  match x:
    case VNum{+a}:
      num1(op, a)
    case _:
      nocase(op)

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

def last.l2(+op: U32, xs: List<&2, Val>, x: Val) -> Val:
  match x:
    case VList{ys}:
      lst2(op, xs, ys)
    case _:
      nocase(op)

# builtin.n(op, args ++ [x]) without building the list: the collected
# arguments matched where they lie, x where it would follow them. Past
# three numbers, or two lists, x cannot matter.
def builtin_last.n(+op: U32, args: List<&2, Val>, x: Val) -> Val:
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
    case Con{VList{xs}, t}:
      match t:
        case Nil{}:
          last.l2(op, xs, x)
        case Con{VList{ys}, u}:
          lst2(op, xs, ys)
        case _:
          nocase(op)
    case _:
      nocase(op)

# Builtins on dicts, ops 5 to 7, each needing two arguments: get, a key
# then a dict; union, two dicts; tag, a key then a value. Each always an
# entry of a net's table (kprim.bend's bfits), so that the kernel's native
# path, which computes numbers, never meets one. `.l` takes the last
# argument where it would follow the collected ones, as builtin_last does.

def get.b(args: List<&2, Val>) -> Val:
  match args:
    case Con{k, t}:
      match t:
        case Con{VDict{es}, u}:
          dfind(es, k)
        case _:
          nocase(5)
    case _:
      nocase(5)

def get.x(k: Val, x: Val) -> Val:
  match x:
    case VDict{es}:
      dfind(es, k)
    case _:
      nocase(5)

def get.l(args: List<&2, Val>, x: Val) -> Val:
  match args:
    case Nil{}:
      nocase(5)
    case Con{k, t}:
      match t:
        case Nil{}:
          get.x(k, x)
        case Con{VDict{es}, u}:
          dfind(es, k)
        case _:
          nocase(5)

def union.b(args: List<&2, Val>) -> Val:
  match args:
    case Con{VDict{a}, t}:
      match t:
        case Con{VDict{b}, u}:
          dunion(b, a)
        case _:
          nocase(6)
    case _:
      nocase(6)

def union.x(a: List<&2, Ent>, x: Val) -> Val:
  match x:
    case VDict{b}:
      dunion(b, a)
    case _:
      nocase(6)

def union.l(args: List<&2, Val>, x: Val) -> Val:
  match args:
    case Nil{}:
      nocase(6)
    case Con{VDict{a}, t}:
      match t:
        case Nil{}:
          union.x(a, x)
        case Con{VDict{b}, u}:
          dunion(b, a)
        case _:
          nocase(6)
    case _:
      nocase(6)

def tag.b(args: List<&2, Val>) -> Val:
  match args:
    case Con{k, t}:
      match t:
        case Con{v, u}:
          tagv(k, v)
        case _:
          nocase(7)
    case _:
      nocase(7)

def tag.l(args: List<&2, Val>, x: Val) -> Val:
  match args:
    case Nil{}:
      nocase(7)
    case Con{k, t}:
      match t:
        case Nil{}:
          tagv(k, x)
        case Con{v, u}:
          tagv(k, v)

def dict.b7(+t: Bool, +op: U32, args: List<&2, Val>) -> Val:
  match t:
    case True{}:
      tag.b(args)
    case False{}:
      nocase(op)

def dict.b6(+t: Bool, +op: U32, args: List<&2, Val>) -> Val:
  match t:
    case True{}:
      union.b(args)
    case False{}:
      dict.b7(U32.is_eq(op, 7), op, args)

def dict.b5(+t: Bool, +op: U32, args: List<&2, Val>) -> Val:
  match t:
    case True{}:
      get.b(args)
    case False{}:
      dict.b6(U32.is_eq(op, 6), op, args)

def dict.l7(+t: Bool, +op: U32, args: List<&2, Val>, x: Val) -> Val:
  match t:
    case True{}:
      tag.l(args, x)
    case False{}:
      nocase(op)

def dict.l6(+t: Bool, +op: U32, args: List<&2, Val>, x: Val) -> Val:
  match t:
    case True{}:
      union.l(args, x)
    case False{}:
      dict.l7(U32.is_eq(op, 7), op, args, x)

def dict.l5(+t: Bool, +op: U32, args: List<&2, Val>, x: Val) -> Val:
  match t:
    case True{}:
      get.l(args, x)
    case False{}:
      dict.l6(U32.is_eq(op, 6), op, args, x)

def builtin.k(+arith: Bool, +op: U32, args: List<&2, Val>) -> Val:
  match arith:
    case True{}:
      builtin.n(op, args)
    case False{}:
      dict.b5(U32.is_eq(op, 5), op, args)

def builtin_last.k(+arith: Bool, +op: U32, args: List<&2, Val>, x: Val) -> Val:
  match arith:
    case True{}:
      builtin_last.n(op, args, x)
    case False{}:
      dict.l5(U32.is_eq(op, 5), op, args, x)

# a builtin on all its arguments: by its op first, those below 5 by the
# arguments' shapes
def builtin(+op: U32, args: List<&2, Val>) -> Val:
  builtin.k(U32.is_lt(op, 5), op, args)

# builtin(op, args ++ [x]) without building the list
def builtin_last(+op: U32, args: List<&2, Val>, x: Val) -> Val:
  builtin_last.k(U32.is_lt(op, 5), op, args, x)

# a value as glam sees it: a flat form as the VFun it stands for
def norm(v: Val) -> Val:
  match v:
    case VP2{+op, +need, +a, +b}:
      VFun{op, need, [VNum{a}, VNum{b}]}
    case _:
      v

def fun.go(+last: Bool, +op: U32, +need: U32, args: List<&2, Val>, x: Val) -> Val:
  match last:
    case True{}:
      builtin_last(op, args, x)
    case False{}:
      VFun{op, (need - 1 : U32), List.append(&2, Val, args, [norm(x)])}

# the flat form's builtin given its last argument: a builtin on numbers
# straight to its arithmetic, the hot path; any other as builtin_last
# takes it, so that applying the flat form computes what applying its
# VFun does (law flat_two_applies_as_fun)
def vp2.k(+arith: Bool, +op: U32, +a: U32, +b: U32, x: Val) -> Val:
  match arith:
    case True{}:
      last.x3(op, a, b, x)
    case False{}:
      dict.l5(U32.is_eq(op, 5), op, [VNum{a}, VNum{b}], x)

def vp2.go(+last: Bool, +op: U32, +need: U32, +a: U32, +b: U32, x: Val) -> Val:
  match last:
    case True{}:
      vp2.k(U32.is_lt(op, 5), op, a, b, x)
    case False{}:
      VFun{op, (need - 1 : U32), [VNum{a}, VNum{b}, norm(x)]}

# a builtin applied to x: an error x passes through, the builtin strict
def fun.e(x: Val, +op: U32, +need: U32, args: List<&2, Val>) -> Val:
  match x:
    case VErr{e}:
      VErr{e}
    case _:
      fun.go(U32.is_eq(need, 1), op, need, args, x)

def vp2.e(x: Val, +op: U32, +need: U32, +a: U32, +b: U32) -> Val:
  match x:
    case VErr{e}:
      VErr{e}
    case _:
      vp2.go(U32.is_eq(need, 1), op, need, a, b, x)

# f applied to x: a builtin, or an error, which applying gives again
def apply_fn(f: Val, x: Val) -> Val:
  match f:
    case VFun{+op, +need, args}:
      fun.e(x, op, need, args)
    case VP2{+op, +need, +a, +b}:
      vp2.e(x, op, need, a, b)
    case VErr{e}:
      VErr{e}
    case _:
      err("applying what is no function")

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
# crossed first, act as one when both raise and second's index is where
# first's raise ends, n2 = n1 + k1: a run of unit brackets n1, n1 + 1,
# ..., which (n1, k1 + k2) stands for exactly, so that a control facing
# it can be matched against its first units (peeling, net.bend and
# kprim.bend). No other pair fuses: a raise and a drop that compose to
# less, or to nothing, or raises split some other way, would hide a
# control a facing one cancels, and the fused control would cross it
# instead (heap-demand and pairing-fusion in the plans).
type Fuse is Data:
  FNo{}
  FTo{p: Pay}

def compose.ok(ok: Bool, +n1: U32, +b1: U32, +b2: U32) -> Fuse:
  match ok:
    case True{}:
      FTo{PLift{n1, True{}, (b1 + b2 : U32)}}
    case False{}:
      FNo{}

# the one control acting as `first` then `second`, when there is one
def compose(first: Pay, second: Pay) -> Fuse:
  match first second:
    case PLift{+n1, +u1, +b1} PLift{+n2, +u2, +b2}:
      compose.ok(u1 && u2 && U32.is_eq(n2, (n1 + b1 : U32)), n1, b1, b2)
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
