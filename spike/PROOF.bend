# The evaluator spike's proofs.

import Base
import ./LAWS.bend as Laws
import ./store.bend as S
import ./rules.bend as R
import ./val.bend as V

def add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# by cases on the free list, then the fresh count: each moves one slot to
# live, and add_succ shifts the 1 across
def Laws.alloc_conserves(m):
  match m:
    case S.Meta{free, fresh, live}:
      match free:
        case Con{s, rest}:
          %add_succ(live, Nat.add(S.len(rest), fresh)) : {1n+Nat.add(live, Nat.add(S.len(rest), fresh)) == _ : Nat}
          {==}
        case Nil{}:
          match fresh:
            case 0n:
              {==}
            case 1n+p:
              %add_succ(live, p) : {1n+Nat.add(live, p) == _ : Nat}
              {==}

def Laws.free_conserves(m, s):
  match m:
    case S.Meta{free, fresh, live}:
      match live:
        case 0n:
          {==}
        case 1n+q:
          %add_succ(q, Nat.add(S.len(free), fresh)) : {_ == 1n+Nat.add(q, Nat.add(S.len(free), fresh)) : Nat}
          {==}

# by cases: every rule is a constant the checker computes
def Laws.rules_polarized(a, b, s):
  match a:
    case R.KFree{}:
      {==}
    case R.KFn{}:
      {==}
    case R.KAp{}:
      match b:
        case R.KFree{}:
          {==}
        case R.KFn{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          {==}
        case R.KCopy{}:
          {==}
        case R.KMerge{}:
          {==}
        case R.KData{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          {==}
        case R.KEraP{}:
          {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
    case R.KCopy{}:
      match b:
        case R.KFree{}:
          {==}
        case R.KFn{}:
          {==}
        case R.KAp{}:
          {==}
        case R.KCopy{}:
          {==}
        case R.KMerge{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          {==}
        case R.KEraN{}:
          {==}
        case R.KEraP{}:
          {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
    case R.KMerge{}:
      {==}
    case R.KData{}:
      {==}
    case R.KEraN{}:
      match b:
        case R.KFree{}:
          {==}
        case R.KFn{}:
          {==}
        case R.KAp{}:
          {==}
        case R.KCopy{}:
          {==}
        case R.KMerge{}:
          {==}
        case R.KData{}:
          {==}
        case R.KEraN{}:
          {==}
        case R.KEraP{}:
          {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
    case R.KEraP{}:
      {==}
    case R.KRoot{}:
      match b:
        case R.KFree{}:
          {==}
        case R.KFn{}:
          {==}
        case R.KAp{}:
          {==}
        case R.KCopy{}:
          {==}
        case R.KMerge{}:
          {==}
        case R.KData{}:
          {==}
        case R.KEraN{}:
          {==}
        case R.KEraP{}:
          {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
    case R.KCall{}:
      match b:
        case R.KFree{}:
          {==}
        case R.KFn{}:
          {==}
        case R.KAp{}:
          {==}
        case R.KCopy{}:
          {==}
        case R.KMerge{}:
          {==}
        case R.KData{}:
          {==}
        case R.KEraN{}:
          {==}
        case R.KEraP{}:
          {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
    case R.KLift{}:
      match b:
        case R.KFree{}:
          {==}
        case R.KFn{}:
          {==}
        case R.KAp{}:
          {==}
        case R.KCopy{}:
          {==}
        case R.KMerge{}:
          {==}
        case R.KData{}:
          {==}
        case R.KEraN{}:
          {==}
        case R.KEraP{}:
          {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KLiftC{}:
      {==}

# by cases: every rule is a constant the checker computes
def Laws.rules_linear(a, b, s):
  match a:
    case R.KFree{}:
      {==}
    case R.KFn{}:
      {==}
    case R.KAp{}:
      match b:
        case R.KFree{}:
          {==}
        case R.KFn{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          {==}
        case R.KCopy{}:
          {==}
        case R.KMerge{}:
          {==}
        case R.KData{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          {==}
        case R.KEraP{}:
          {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
    case R.KCopy{}:
      match b:
        case R.KFree{}:
          {==}
        case R.KFn{}:
          {==}
        case R.KAp{}:
          {==}
        case R.KCopy{}:
          {==}
        case R.KMerge{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          {==}
        case R.KEraN{}:
          {==}
        case R.KEraP{}:
          {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
    case R.KMerge{}:
      {==}
    case R.KData{}:
      {==}
    case R.KEraN{}:
      match b:
        case R.KFree{}:
          {==}
        case R.KFn{}:
          {==}
        case R.KAp{}:
          {==}
        case R.KCopy{}:
          {==}
        case R.KMerge{}:
          {==}
        case R.KData{}:
          {==}
        case R.KEraN{}:
          {==}
        case R.KEraP{}:
          {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
    case R.KEraP{}:
      {==}
    case R.KRoot{}:
      match b:
        case R.KFree{}:
          {==}
        case R.KFn{}:
          {==}
        case R.KAp{}:
          {==}
        case R.KCopy{}:
          {==}
        case R.KMerge{}:
          {==}
        case R.KData{}:
          {==}
        case R.KEraN{}:
          {==}
        case R.KEraP{}:
          {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
    case R.KCall{}:
      match b:
        case R.KFree{}:
          {==}
        case R.KFn{}:
          {==}
        case R.KAp{}:
          {==}
        case R.KCopy{}:
          {==}
        case R.KMerge{}:
          {==}
        case R.KData{}:
          {==}
        case R.KEraN{}:
          {==}
        case R.KEraP{}:
          {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
    case R.KLift{}:
      match b:
        case R.KFree{}:
          {==}
        case R.KFn{}:
          {==}
        case R.KAp{}:
          {==}
        case R.KCopy{}:
          {==}
        case R.KMerge{}:
          {==}
        case R.KData{}:
          {==}
        case R.KEraN{}:
          {==}
        case R.KEraP{}:
          {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KLiftC{}:
      {==}

# by cases on the collected arguments, as deep as builtin looks, and on
# the last argument where it is the first, second or third: each side then
# computes the same numN, or VUnit
def Laws.builtin_last_agrees(op, args, x):
  match args:
    case Nil{}:
      match x:
        case V.VUnit{}:
          {==}
        case V.VNum{n}:
          {==}
        case V.VLazy{k}:
          {==}
        case V.VFun{o, nd, l}:
          {==}
        case V.VFree{f}:
          {==}
        case V.VP1{o, nd, c}:
          {==}
        case V.VP2{o, nd, c, d}:
          {==}
    case Con{h1, t1}:
      match h1:
        case V.VUnit{}:
          {==}
        case V.VLazy{k}:
          {==}
        case V.VFun{o, nd, l}:
          {==}
        case V.VFree{f}:
          {==}
        case V.VP1{o, nd, c}:
          {==}
        case V.VP2{o, nd, c, d}:
          {==}
        case V.VNum{a}:
          match t1:
            case Nil{}:
              match x:
                case V.VUnit{}:
                  {==}
                case V.VNum{n}:
                  {==}
                case V.VLazy{k}:
                  {==}
                case V.VFun{o, nd, l}:
                  {==}
                case V.VFree{f}:
                  {==}
                case V.VP1{o, nd, c}:
                  {==}
                case V.VP2{o, nd, c, d}:
                  {==}
            case Con{h2, t2}:
              match h2:
                case V.VUnit{}:
                  {==}
                case V.VLazy{k}:
                  {==}
                case V.VFun{o, nd, l}:
                  {==}
                case V.VFree{f}:
                  {==}
                case V.VP1{o, nd, c}:
                  {==}
                case V.VP2{o, nd, c, d}:
                  {==}
                case V.VNum{b}:
                  match t2:
                    case Nil{}:
                      match x:
                        case V.VUnit{}:
                          {==}
                        case V.VNum{n}:
                          {==}
                        case V.VLazy{k}:
                          {==}
                        case V.VFun{o, nd, l}:
                          {==}
                        case V.VFree{f}:
                          {==}
                        case V.VP1{o, nd, c}:
                          {==}
                        case V.VP2{o, nd, c, d}:
                          {==}
                    case Con{h3, t3}:
                      match h3:
                        case V.VUnit{}:
                          {==}
                        case V.VNum{n}:
                          {==}
                        case V.VLazy{k}:
                          {==}
                        case V.VFun{o, nd, l}:
                          {==}
                        case V.VFree{f}:
                          {==}
                        case V.VP1{o, nd, c}:
                          {==}
                        case V.VP2{o, nd, c, d}:
                          {==}

# whether the builtin is given its last argument (need = 1) or not, each
# side computes the same number, flat form or VFun
def vp1_by(t: Bool, -op: U32, -need: U32, -a: U32, x: V.Val) -> {V.norm(V.vp1.go(t, op, need, a, x)) == V.norm(V.fun.go(t, op, need, [V.VNum{a}], x)) : V.Val}:
  match t:
    case True{}:
      match x:
        case V.VUnit{}:
          {==}
        case V.VNum{y}:
          {==}
        case V.VLazy{k}:
          {==}
        case V.VFun{o, nd, l}:
          {==}
        case V.VFree{f}:
          {==}
        case V.VP1{o, nd, c}:
          {==}
        case V.VP2{o, nd, c, d}:
          {==}
    case False{}:
      match x:
        case V.VUnit{}:
          {==}
        case V.VNum{y}:
          {==}
        case V.VLazy{k}:
          {==}
        case V.VFun{o, nd, l}:
          {==}
        case V.VFree{f}:
          {==}
        case V.VP1{o, nd, c}:
          {==}
        case V.VP2{o, nd, c, d}:
          {==}

def Laws.vp1_agrees(op, need, a, x):
  vp1_by(U32.is_eq(need, 1), op, need, a, x)

def vp2_by(t: Bool, -op: U32, -need: U32, -a: U32, -b: U32, x: V.Val) -> {V.norm(V.vp2.go(t, op, need, a, b, x)) == V.norm(V.fun.go(t, op, need, [V.VNum{a}, V.VNum{b}], x)) : V.Val}:
  match t:
    case True{}:
      match x:
        case V.VUnit{}:
          {==}
        case V.VNum{y}:
          {==}
        case V.VLazy{k}:
          {==}
        case V.VFun{o, nd, l}:
          {==}
        case V.VFree{f}:
          {==}
        case V.VP1{o, nd, c}:
          {==}
        case V.VP2{o, nd, c, d}:
          {==}
    case False{}:
      match x:
        case V.VUnit{}:
          {==}
        case V.VNum{y}:
          {==}
        case V.VLazy{k}:
          {==}
        case V.VFun{o, nd, l}:
          {==}
        case V.VFree{f}:
          {==}
        case V.VP1{o, nd, c}:
          {==}
        case V.VP2{o, nd, c, d}:
          {==}

def Laws.vp2_agrees(op, need, a, b, x):
  vp2_by(U32.is_eq(need, 1), op, need, a, b, x)

# Placeholders
# ------------

# b || True, whatever b is
def or_true(+b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# not b || b
def or_not(+b: Bool) -> {Bool.or(Bool.not(b), b) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a builtin's arithmetic yields a number or unit, no placeholder
def num1_ok(+b: Bool, +t: Bool, +a: U32) -> {Bool.or(b, V.clean(V.num1.go(t, a))) == True{} : Bool}:
  match t:
    case True{}:
      or_true(b)
    case False{}:
      or_true(b)

def num2_ok(+b: Bool, +t: Bool, +a: U32, +c: U32) -> {Bool.or(b, V.clean(V.num2.go(t, a, c))) == True{} : Bool}:
  match t:
    case True{}:
      or_true(b)
    case False{}:
      or_true(b)

def num3_ok(+b: Bool, +t: Bool, +a: U32, +c: U32, +d: U32) -> {Bool.or(b, V.clean(V.num3.go(t, a, c, d))) == True{} : Bool}:
  match t:
    case True{}:
      or_true(b)
    case False{}:
      or_true(b)

def x1_ok(+b: Bool, +op: U32, +x: V.Val) -> {Bool.or(b, V.clean(V.last.x1(op, x))) == True{} : Bool}:
  match x:
    case V.VUnit{}:
      or_true(b)
    case V.VNum{y}:
      num1_ok(b, U32.is_eq(op, 1), y)
    case V.VLazy{k}:
      or_true(b)
    case V.VFun{o, nd, l}:
      or_true(b)
    case V.VFree{f}:
      or_true(b)
    case V.VP1{o, nd, c}:
      or_true(b)
    case V.VP2{o, nd, c, d}:
      or_true(b)

def x2_ok(+b: Bool, +op: U32, +a: U32, +x: V.Val) -> {Bool.or(b, V.clean(V.last.x2(op, a, x))) == True{} : Bool}:
  match x:
    case V.VUnit{}:
      num1_ok(b, U32.is_eq(op, 1), a)
    case V.VNum{y}:
      num2_ok(b, U32.is_eq(op, 2), a, y)
    case V.VLazy{k}:
      num1_ok(b, U32.is_eq(op, 1), a)
    case V.VFun{o, nd, l}:
      num1_ok(b, U32.is_eq(op, 1), a)
    case V.VFree{f}:
      num1_ok(b, U32.is_eq(op, 1), a)
    case V.VP1{o, nd, c}:
      num1_ok(b, U32.is_eq(op, 1), a)
    case V.VP2{o, nd, c, d}:
      num1_ok(b, U32.is_eq(op, 1), a)

def x3_ok(+b: Bool, +op: U32, +a: U32, +e: U32, +x: V.Val) -> {Bool.or(b, V.clean(V.last.x3(op, a, e, x))) == True{} : Bool}:
  match x:
    case V.VUnit{}:
      num2_ok(b, U32.is_eq(op, 2), a, e)
    case V.VNum{y}:
      num3_ok(b, U32.is_eq(op, 3), a, e, y)
    case V.VLazy{k}:
      num2_ok(b, U32.is_eq(op, 2), a, e)
    case V.VFun{o, nd, l}:
      num2_ok(b, U32.is_eq(op, 2), a, e)
    case V.VFree{f}:
      num2_ok(b, U32.is_eq(op, 2), a, e)
    case V.VP1{o, nd, c}:
      num2_ok(b, U32.is_eq(op, 2), a, e)
    case V.VP2{o, nd, c, d}:
      num2_ok(b, U32.is_eq(op, 2), a, e)

# builtin_last yields a number or unit
def last_ok(+b: Bool, +op: U32, +args: List<&2, V.Val>, +x: V.Val) -> {Bool.or(b, V.clean(V.builtin_last(op, args, x))) == True{} : Bool}:
  match args:
    case Nil{}:
      x1_ok(b, op, x)
    case Con{h1, t1}:
      match h1:
        case V.VNum{a}:
          match t1:
            case Nil{}:
              x2_ok(b, op, a, x)
            case Con{h2, t2}:
              match h2:
                case V.VNum{e}:
                  match t2:
                    case Nil{}:
                      x3_ok(b, op, a, e, x)
                    case Con{h3, t3}:
                      match h3:
                        case V.VNum{g}:
                          num3_ok(b, U32.is_eq(op, 3), a, e, g)
                        case V.VUnit{}:
                          num2_ok(b, U32.is_eq(op, 2), a, e)
                        case V.VLazy{k}:
                          num2_ok(b, U32.is_eq(op, 2), a, e)
                        case V.VFun{o, nd, l}:
                          num2_ok(b, U32.is_eq(op, 2), a, e)
                        case V.VFree{f}:
                          num2_ok(b, U32.is_eq(op, 2), a, e)
                        case V.VP1{o, nd, c}:
                          num2_ok(b, U32.is_eq(op, 2), a, e)
                        case V.VP2{o, nd, c, d}:
                          num2_ok(b, U32.is_eq(op, 2), a, e)
                case V.VUnit{}:
                  num1_ok(b, U32.is_eq(op, 1), a)
                case V.VLazy{k}:
                  num1_ok(b, U32.is_eq(op, 1), a)
                case V.VFun{o, nd, l}:
                  num1_ok(b, U32.is_eq(op, 1), a)
                case V.VFree{f}:
                  num1_ok(b, U32.is_eq(op, 1), a)
                case V.VP1{o, nd, c}:
                  num1_ok(b, U32.is_eq(op, 1), a)
                case V.VP2{o, nd, c, d}:
                  num1_ok(b, U32.is_eq(op, 1), a)
        case V.VUnit{}:
          or_true(b)
        case V.VLazy{k}:
          or_true(b)
        case V.VFun{o, nd, l}:
          or_true(b)
        case V.VFree{f}:
          or_true(b)
        case V.VP1{o, nd, c}:
          or_true(b)
        case V.VP2{o, nd, c, d}:
          or_true(b)

# collecting a normalized argument, not a free slot, keeps a list clean
def app_ok(+l: List<&2, V.Val>, +x: V.Val) -> {Bool.or(Bool.or(Bool.not(V.all_np(l)), V.is_free(x)), V.all_np(List.append(&2, V.Val, l, [V.norm(x)]))) == True{} : Bool}:
  match l:
    case Nil{}:
      match x:
        case V.VUnit{}:
          {==}
        case V.VNum{y}:
          {==}
        case V.VLazy{k}:
          {==}
        case V.VFun{o, nd, l}:
          {==}
        case V.VFree{f}:
          {==}
        case V.VP1{o, nd, c}:
          {==}
        case V.VP2{o, nd, c, d}:
          {==}
    case Con{h, t}:
      match h:
        case V.VUnit{}:
          app_ok(t, x)
        case V.VNum{y}:
          app_ok(t, x)
        case V.VLazy{k}:
          app_ok(t, x)
        case V.VFun{o, nd, l}:
          app_ok(t, x)
        case V.VFree{f}:
          {==}
        case V.VP1{o, nd, c}:
          {==}
        case V.VP2{o, nd, c, d}:
          {==}

def fun_ok(+t: Bool, +op: U32, +need: U32, +args: List<&2, V.Val>, +x: V.Val) -> {Bool.or(Bool.or(Bool.not(V.all_np(args)), V.is_free(x)), V.clean(V.fun.go(t, op, need, args, x))) == True{} : Bool}:
  match t:
    case True{}:
      last_ok(Bool.or(Bool.not(V.all_np(args)), V.is_free(x)), op, args, x)
    case False{}:
      app_ok(args, x)

def vp1_ok(+t: Bool, +op: U32, +need: U32, +a: U32, +x: V.Val) -> {Bool.or(V.is_free(x), V.clean(V.vp1.go(t, op, need, a, x))) == True{} : Bool}:
  match t:
    case True{}:
      x2_ok(V.is_free(x), op, a, x)
    case False{}:
      match x:
        case V.VUnit{}:
          {==}
        case V.VNum{y}:
          {==}
        case V.VLazy{k}:
          {==}
        case V.VFun{o, nd, l}:
          {==}
        case V.VFree{f}:
          {==}
        case V.VP1{o, nd, c}:
          {==}
        case V.VP2{o, nd, c, d}:
          {==}

def vp2_ok(+t: Bool, +op: U32, +need: U32, +a: U32, +e: U32, +x: V.Val) -> {Bool.or(V.is_free(x), V.clean(V.vp2.go(t, op, need, a, e, x))) == True{} : Bool}:
  match t:
    case True{}:
      x3_ok(V.is_free(x), op, a, e, x)
    case False{}:
      match x:
        case V.VUnit{}:
          {==}
        case V.VNum{y}:
          {==}
        case V.VLazy{k}:
          {==}
        case V.VFun{o, nd, l}:
          {==}
        case V.VFree{f}:
          {==}
        case V.VP1{o, nd, c}:
          {==}
        case V.VP2{o, nd, c, d}:
          {==}

def Laws.norm_not_placeholder(v):
  match v:
    case V.VUnit{}:
      {==}
    case V.VNum{y}:
      {==}
    case V.VLazy{k}:
      {==}
    case V.VFun{o, nd, l}:
      {==}
    case V.VFree{f}:
      {==}
    case V.VP1{o, nd, c}:
      {==}
    case V.VP2{o, nd, c, d}:
      {==}

def Laws.apply_keeps_clean(f, x):
  match f:
    case V.VUnit{}:
      or_true(V.is_free(x))
    case V.VNum{y}:
      or_true(V.is_free(x))
    case V.VLazy{k}:
      or_true(V.is_free(x))
    case V.VFree{k}:
      or_true(V.is_free(x))
    case V.VFun{op, need, args}:
      fun_ok(U32.is_eq(need, 1), op, need, args, x)
    case V.VP1{op, need, a}:
      vp1_ok(U32.is_eq(need, 1), op, need, a, x)
    case V.VP2{op, need, a, e}:
      vp2_ok(U32.is_eq(need, 1), op, need, a, e, x)

def Laws.norm_keeps_clean(v):
  match v:
    case V.VUnit{}:
      {==}
    case V.VNum{y}:
      {==}
    case V.VLazy{k}:
      {==}
    case V.VFun{o, nd, l}:
      or_not(V.all_np(l))
    case V.VFree{f}:
      {==}
    case V.VP1{o, nd, c}:
      {==}
    case V.VP2{o, nd, c, d}:
      {==}
