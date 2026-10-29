# The evaluator spike's proofs.

import Base
import ./LAWS.bend as Laws
import ./store.bend as S
import ./rules.bend as R
import ./val.bend as V
import ./ctl.bend as CT
import ./kprim.bend as P
import ./freelist.bend as FL
import 0x78e347bf8d0582a322c01b02c727566f/nat.bend as MNat
import 0x78e347bf8d0582a322c01b02c727566f/u32.bend as MU
import ../vendor/wilderness-labs-stt/u32.bend as UD

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

def Laws.rules_tested_small(a, b):
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
          {==}
    case R.KLiftC{}:
      {==}

# Control runs (ctl.bend)
# =======================

def add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def succ_add(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %succ_add(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

def above_succ(a: Nat) -> {True{} == CT.above(Nat.add(a, 1n), 0n) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def raise_zero.go(t: Bool, j: Nat) -> {CT.raise.go(t, j, 0n) == j : Nat}:
  match t:
    case True{}:
      add_zero(j)
    case False{}:
      {==}

def raise_shift.go(t: Bool, -a: Nat, -b: Nat) -> {1n+CT.raise.go(t, a, b) == CT.raise.go(t, 1n+a, b) : Nat}:
  match t:
    case True{}:
      {==}
    case False{}:
      {==}

# one index and one level higher: one level higher
def raise_shift(+m: Nat, -b: Nat, +a: Nat) -> {1n+CT.raise(m, b, a) == CT.raise(1n+m, b, 1n+a) : Nat}:
  raise_shift.go(CT.above(a, m), a, b)

# the first unit, then the rest of the run from the next index
def one_then_rest(+n: Nat, +j: Nat, -p: Nat) -> {CT.raise(1n+n, p, CT.raise(n, 1n, j)) == CT.raise(n, 1n+p, j) : Nat}:
  match n j:
    case _ 0n:
      {==}
    case 0n 1n+a:
      %above_succ(a) : {CT.raise.go(_, Nat.add(1n+a, 1n), p) == CT.raise(0n, 1n+p, 1n+a) : Nat}
      %add_assoc(a, 1n, p) : {1n+_ == 1n+Nat.add(a, 1n+p) : Nat}
      {==}
    case 1n+m 1n+a:
      %raise_shift(m, 1n, a) : {CT.raise(2n+m, p, _) == CT.raise(1n+m, 1n+p, 1n+a) : Nat}
      %raise_shift(1n+m, p, CT.raise(m, 1n, a)) : {_ == CT.raise(1n+m, 1n+p, 1n+a) : Nat}
      %raise_shift(m, 1n+p, a) : {1n+CT.raise(1n+m, p, CT.raise(m, 1n, a)) == _ : Nat}
      %one_then_rest(m, a, p) : {1n+CT.raise(1n+m, p, CT.raise(m, 1n, a)) == 1n+_ : Nat}
      {==}

def Laws.units_are_run(b, n, j):
  match b:
    case 0n:
      %raise_zero.go(CT.above(j, n), j) : {_ == CT.raise.go(CT.above(j, n), j, 0n) : Nat}
      {==}
    case 1n+p:
      %one_then_rest(n, j, p) : {CT.units(p, 1n+n, CT.raise(n, 1n, j)) == _ : Nat}
      Laws.units_are_run(p, 1n+n, CT.raise(n, 1n, j))

# k units then r more, from the index where the k end
def units_split(+k: Nat, -r: Nat, +n: Nat, +j: Nat) -> {CT.units(Nat.add(k, r), n, j) == CT.units(r, Nat.add(k, n), CT.units(k, n, j)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      %succ_add(q, n) : {CT.units(Nat.add(q, r), 1n+n, CT.raise(n, 1n, j)) == CT.units(r, _, CT.units(q, 1n+n, CT.raise(n, 1n, j))) : Nat}
      units_split(q, r, 1n+n, CT.raise(n, 1n, j))

def Laws.run_splits(k, r, n, j):
  %Laws.units_are_run(k, n, j) : {CT.raise(Nat.add(k, n), r, _) == CT.raise(n, Nat.add(k, r), j) : Nat}
  %Laws.units_are_run(r, Nat.add(k, n), CT.units(k, n, j)) : {_ == CT.raise(n, Nat.add(k, r), j) : Nat}
  %Laws.units_are_run(Nat.add(k, r), n, j) : {CT.units(r, Nat.add(k, n), CT.units(k, n, j)) == _ : Nat}
  %units_split(k, r, n, j) : {_ == CT.units(Nat.add(k, r), n, j) : Nat}
  {==}

def peel_shift(lt: Bool, eq: Bool, +n: Nat, +p: Nat, +q: Nat) -> {CT.peel.go(lt, eq, 1n+n, p, q) == CT.peel.go(lt, eq, n, 1n+p, 1n+q) : CT.Left}:
  match lt eq:
    case True{} True{}:
      %add_succ(p, n) : {CT.Left{0, _, 0n} == CT.Left{0, 1n+Nat.add(p, n), 0n} : CT.Left}
      {==}
    case False{} True{}:
      %add_succ(p, n) : {CT.Left{0, _, 0n} == CT.Left{0, 1n+Nat.add(p, n), 0n} : CT.Left}
      {==}
    case True{} False{}:
      %add_succ(p, n) : {CT.Left{1, _, Nat.sub(q, p)} == CT.Left{1, 1n+Nat.add(p, n), Nat.sub(q, p)} : CT.Left}
      {==}
    case False{} False{}:
      %add_succ(q, n) : {CT.Left{2, _, Nat.sub(p, q)} == CT.Left{2, 1n+Nat.add(q, n), Nat.sub(p, q)} : CT.Left}
      {==}

def Laws.peel_pairs_units(c, l, n):
  match c l:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %peel_shift(Nat.is_lt(p, q), Nat.is_eq(p, q), n, p, q) : {CT.pair_off(p, q, 1n+n) == _ : CT.Left}
      Laws.peel_pairs_units(p, q, 1n+n)

# Nat.is_gt read as the model's "above", for rewriting toward it
def gt_is_above(a: Nat, b: Nat) -> {Nat.is_gt(a, b) == CT.above(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+m:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+m:
      gt_is_above(p, m)

# over a Bool guard: raising by b in U32 is raising in Nat, when j + b fits
def raise_g(g: Bool, +b: U32, +j: U32, h: MNat.lt(Nat.add(U32.to_nat(j), U32.to_nat(b)), Nat.pow(2n, 32n))) ->
  {U32.to_nat(P.lift.go(g, True{}, b, j)) == CT.raise.go(g, U32.to_nat(j), U32.to_nat(b)) : Nat}:
  match g:
    case True{}:
      MU.u32_add_exact(j, b, h)
    case False{}:
      {==}

# the guard rewritten from the model's above to Nat.is_gt, then to the
# kernel's U32.is_gt (bend-mathlib's u32_is_gt_to_nat); raise_g does the
# rest
def Laws.lift_raise(n, b, j, h):
  %gt_is_above(U32.to_nat(j), U32.to_nat(n)) : {U32.to_nat(P.lift.go(U32.is_gt(j, n), True{}, b, j)) == CT.raise.go(_, U32.to_nat(j), U32.to_nat(b)) : Nat}
  %MU.u32_is_gt_to_nat(j, n) : {U32.to_nat(P.lift.go(U32.is_gt(j, n), True{}, b, j)) == CT.raise.go(_, U32.to_nat(j), U32.to_nat(b)) : Nat}
  raise_g(U32.is_gt(j, n), b, j, h)

# Field bounds
# ============
#
# The checker compares two Nats that differ in form by expanding both in
# unary, and overflows its stack at 2^16 (docs/BendIssues.md, "Reasoning
# about U32 in proofs"). So a closed power such as Nat.pow(2n, 24n) only
# ever meets itself: each lemma reasons under a variable bound, and is
# instantiated with the power where the forms match exactly.

# a below x * (1 + b) leaves a / (1 + b) below x
def div_lt(+a: Nat, +x: Nat, +b: Nat, h: MNat.lt(a, Nat.mul(x, 1n+b))) -> MNat.lt(Nat.div(a, 1n+b), x):
  MNat.lt_of_not_le(x, Nat.div(a, 1n+b),
    Equal.trans(Bool, Nat.is_le(x, Nat.div(a, 1n+b)), Nat.is_le(Nat.mul(x, 1n+b), a), False{},
      MNat.le_div_iff_mul_le(x, a, b),
      MNat.not_le_of_lt(a, Nat.mul(x, 1n+b), h)))

def pow_8() -> {Nat.pow(2n, 8n) == 256n : Nat}:
  {==}

def sum_32() -> {32n == Nat.add(24n, 8n) : Nat}:
  {==}

# a U32 lies below 2^24 * 256
def lt_32(+h: U32) -> MNat.lt(U32.to_nat(h), Nat.mul(Nat.pow(2n, 24n), 256n)):
  %pow_8() : MNat.lt(U32.to_nat(h), Nat.mul(Nat.pow(2n, 24n), _))
  %MNat.pow_add(2n, 24n, 8n) : MNat.lt(U32.to_nat(h), _)
  %sum_32() : MNat.lt(U32.to_nat(h), Nat.pow(2n, _))
  MU.u32_to_nat_lt(h)

def fld_bits.go(+h: U32, +x: Nat, l: MNat.lt(Nat.div(U32.to_nat(h), 1n+255n), x)) -> MNat.lt(U32.to_nat(P.fld(h)), x):
  %Equal.sym(Nat, U32.to_nat(U32.div(h, 256)), Nat.div(U32.to_nat(h), 1n+255n), UD.U32.to_nat_div(h, 256)) : MNat.lt(_, x)
  l

def Laws.fld_bits(h):
  fld_bits.go(h, Nat.pow(2n, 24n), div_lt(U32.to_nat(h), Nat.pow(2n, 24n), 255n, lt_32(h)))

# the w-bit word with one bit set, at n
def one_at(w: Nat, n: Nat) -> Word(w):
  match w:
    case 0n:
      WNil{}
    case 1n+q:
      match n:
        case 0n:
          WCon{True{}, Word.zero(q)}
        case 1n+p:
          WCon{False{}, one_at(q, p)}

def one_at_nat(+w: Nat, +n: Nat, h: MNat.lt(n, w)) -> {Word.to_nat(w, one_at(w, n)) == Nat.pow(2n, n) : Nat}:
  match w n:
    case 0n 0n:
      Empty.absurd({Word.to_nat(0n, one_at(0n, 0n)) == Nat.pow(2n, 0n) : Nat}, MNat.internal_false_ne_true(h))
    case 0n 1n+p:
      Empty.absurd({Word.to_nat(0n, one_at(0n, 1n+p)) == Nat.pow(2n, 1n+p) : Nat}, MNat.internal_false_ne_true(h))
    case 1n++q 0n:
      %Equal.sym(Nat, Word.to_nat(q, Word.zero(q)), 0n, MU.word_to_nat_zero(q)) : {1n+Nat.double(_) == 1n : Nat}
      {==}
    case 1n++q 1n++p:
      %MNat.two_pow_succ_sym(p) : {Nat.double(Word.to_nat(q, one_at(q, p))) == _ : Nat}
      %one_at_nat(q, p, h) : {Nat.double(Word.to_nat(q, one_at(q, p))) == Nat.double(_) : Nat}
      {==}

def one_31() -> {one_at(32n, 31n) == UD.U32.word(2147483648) : Word(32n)}:
  {==}

def one_24() -> {one_at(32n, 24n) == UD.U32.word(P.lvl_cap()) : Word(32n)}:
  {==}

def u32_31() -> {U32.to_nat(2147483648) == Nat.pow(2n, 31n) : Nat}:
  %UD.U32.word_nat(2147483648) : {_ == Nat.pow(2n, 31n) : Nat}
  %one_31() : {Word.to_nat(32n, _) == Nat.pow(2n, 31n) : Nat}
  one_at_nat(32n, 31n, {==})

def u32_24() -> {U32.to_nat(P.lvl_cap()) == Nat.pow(2n, 24n) : Nat}:
  %UD.U32.word_nat(P.lvl_cap()) : {_ == Nat.pow(2n, 24n) : Nat}
  %one_24() : {Word.to_nat(32n, _) == Nat.pow(2n, 24n) : Nat}
  one_at_nat(32n, 24n, {==})

# zero is not below zero
def lt0(+x: Nat, e: {x == 0n : Nat}, pos: MNat.lt(0n, x)) -> MNat.lt(0n, 0n):
  %e : MNat.lt(0n, _)
  pos

def mod_lt.fin(+a: Word(32n), +b: U32, qr: Word(32n) & U32, v: UD.U32.DivSpec(32n, a, b, qr)) ->
  MNat.lt(U32.to_nat(U32.mod.fin(qr)), U32.to_nat(b)):
  (+q, +r) = qr
  (e, hr) = v
  hr

def mod_lt.if(z: Bool, +a: U32, +b: U32, e: {U32.is_zero(b) == z : Bool}, pos: MNat.lt(0n, U32.to_nat(b))) ->
  MNat.lt(U32.to_nat(U32.mod.if(UD.U32.word(a), b, z)), U32.to_nat(b)):
  match z:
    case True{}:
      +zero = MNat.eq_of_is_eq(U32.to_nat(b), 0n,
        Equal.trans(Bool, Nat.is_eq(U32.to_nat(b), 0n), U32.is_zero(b), True{},
          Equal.sym(Bool, U32.is_zero(b), Nat.is_eq(U32.to_nat(b), 0n), UD.U32.zero_nat(b)), e))
      Empty.absurd(MNat.lt(U32.to_nat(U32.mod.if(UD.U32.word(a), b, True{})), U32.to_nat(b)),
        MNat.internal_false_ne_true(lt0(U32.to_nat(b), zero, pos)))
    case False{}:
      +pos = pos
      mod_lt.fin(UD.U32.word(a), b, U32.divmod.go(32n, UD.U32.word(a), b),
        UD.U32.divmod_spec(32n, UD.U32.word(a), b, MNat.le_refl(32n), pos))

def mod_word(a: U32, b: U32) -> {U32.mod.if(UD.U32.word(a), b, U32.is_zero(b)) == U32.mod(a, b) : U32}:
  match a b:
    case U32{x} U32{y}:
      {==}

# a U32 remainder lies below a positive divisor
def mod_lt(+a: U32, +b: U32, pos: MNat.lt(0n, U32.to_nat(b))) -> MNat.lt(U32.to_nat(U32.mod(a, b)), U32.to_nat(b)):
  %mod_word(a, b) : MNat.lt(U32.to_nat(_), U32.to_nat(b))
  mod_lt.if(U32.is_zero(b), a, b, {==}, pos)

def off_by_mod(+o: U32) -> {U32.mod(o, 2147483648) == P.off_by(o) : U32}:
  {==}

def pos_31() -> MNat.lt(0n, U32.to_nat(2147483648)):
  {==}

def off_by_bits.go(+o: U32, +x: Nat, eb: {U32.to_nat(2147483648) == x : Nat}) -> MNat.lt(U32.to_nat(P.off_by(o)), x):
  %eb : MNat.lt(U32.to_nat(P.off_by(o)), _)
  %off_by_mod(o) : MNat.lt(U32.to_nat(_), U32.to_nat(2147483648))
  mod_lt(o, 2147483648, pos_31())

def Laws.off_by_bits(o):
  off_by_bits.go(o, Nat.pow(2n, 31n), u32_31())

# a below x and b below y, x no more than y, sum below y + y
def sum_lt(+a: Nat, +b: Nat, +x: Nat, +y: Nat, ha: MNat.lt(a, x), hb: MNat.lt(b, y), xy: MNat.le(x, y)) ->
  MNat.lt(Nat.add(a, b), Nat.add(y, y)):
  MNat.lt_of_lt_of_le(Nat.add(a, b), Nat.add(x, y), Nat.add(y, y), MNat.add_lt_add(a, b, x, y, ha, hb),
    MNat.add_le_add(x, y, y, y, xy, MNat.le_refl(y)))

# a 24-bit level and a 31-bit amount sum within a U32
def fits_32(+a: Nat, +b: Nat, ha: MNat.lt(a, Nat.pow(2n, 24n)), hb: MNat.lt(b, Nat.pow(2n, 31n))) ->
  MNat.lt(Nat.add(a, b), Nat.pow(2n, 32n)):
  %MNat.two_pow_succ_sym(31n) : MNat.lt(Nat.add(a, b), _)
  %MNat.double_eq_add_sym(Nat.pow(2n, 31n)) : MNat.lt(Nat.add(a, b), _)
  sum_lt(a, b, Nat.pow(2n, 24n), Nat.pow(2n, 31n), ha, hb, MNat.pow_le_pow_right(1n, 24n, 31n, {==}))

# off_up(o) rewritten to True, then lift_raise with its fit discharged
def Laws.lift_decoded(n, o, h, up):
  %Equal.sym(Bool, P.off_up(o), True{}, up) : {U32.to_nat(P.lift.go(U32.is_gt(P.fld(h), n), _, P.off_by(o), P.fld(h))) == CT.raise(U32.to_nat(n), U32.to_nat(P.off_by(o)), U32.to_nat(P.fld(h))) : Nat}
  Laws.lift_raise(n, P.off_by(o), P.fld(h),
    fits_32(U32.to_nat(P.fld(h)), U32.to_nat(P.off_by(o)), Laws.fld_bits(h), Laws.off_by_bits(o)))

# over the guards as variables: a level not above n is unchanged; one
# above, raised, is below the cap, which lift_wraps compares in U32
def lift_fits.go(above: Bool, u: Bool, +b: U32, +j: U32, +cap: U32, +x: Nat,
  eu: {u == True{} : Bool},
  ok: {(u && above && U32.is_ge((j + b : U32), cap)) == False{} : Bool},
  hj: MNat.lt(U32.to_nat(j), x),
  ecap: {U32.to_nat(cap) == x : Nat}) -> MNat.lt(U32.to_nat(P.lift.go(above, u, b, j)), x):
  match above:
    case False{}:
      hj
    case True{}:
      match u:
        case False{}:
          Empty.absurd(MNat.lt(U32.to_nat(P.lift.go(True{}, False{}, b, j)), x), MNat.internal_false_ne_true(eu))
        case True{}:
          %ecap : MNat.lt(U32.to_nat((j + b : U32)), _)
          MNat.lt_of_not_le(U32.to_nat(cap), U32.to_nat((j + b : U32)),
            Equal.trans(Bool, Nat.is_le(U32.to_nat(cap), U32.to_nat((j + b : U32))), Nat.is_ge(U32.to_nat((j + b : U32)), U32.to_nat(cap)), False{},
              MNat.is_ge_eq_is_le_sym(U32.to_nat((j + b : U32)), U32.to_nat(cap)),
              Equal.trans(Bool, Nat.is_ge(U32.to_nat((j + b : U32)), U32.to_nat(cap)), U32.is_ge((j + b : U32), cap), False{},
                MU.u32_is_ge_to_nat_sym((j + b : U32), cap), ok)))

def lift_fits.at(+n: U32, +o: U32, +j: U32, +x: Nat, up: {P.off_up(o) == True{} : Bool},
  ok: {P.lift_wraps(n, o, j) == False{} : Bool}, hj: MNat.lt(U32.to_nat(j), x),
  ecap: {U32.to_nat(P.lvl_cap()) == x : Nat}) -> MNat.lt(U32.to_nat(P.lift(n, o, j)), x):
  lift_fits.go(U32.is_gt(j, n), P.off_up(o), P.off_by(o), j, P.lvl_cap(), x, up, ok, hj, ecap)

def Laws.lift_fits(n, o, h, up, ok):
  lift_fits.at(n, o, P.fld(h), Nat.pow(2n, 24n), up, ok, Laws.fld_bits(h), u32_24())

# The free list
# =============
#
# Over the model in freelist.bend: Bool steps, slot lemmas, then each
# operation's case. A rule's fact about a computed value (a slot, a
# comparison) is taken through a helper's parameter with its equation.

def ne_tf(e: {True{} == False{} : Bool}) -> Empty:
  MNat.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, e))

def and_l(a: Bool, b: Bool, h: {(a && b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def and_r(a: Bool, b: Bool, h: {(a && b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, MNat.internal_false_ne_true(h))

def and_i(a: Bool, b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {(a && b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      ha

def or_false_l(a: Bool, b: Bool, h: {(a || b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

def or_false_r(a: Bool, b: Bool, h: {(a || b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, ne_tf(h))
    case False{}:
      h

# x || (y || z) with y false is x || z
def or_drop(+x: Bool, y: Bool, +z: Bool, h: {(x || (y || z)) == True{} : Bool}, hy: {y == False{} : Bool}) -> {(x || z) == True{} : Bool}:
  match y:
    case True{}:
      Empty.absurd({(x || z) == True{} : Bool}, ne_tf(hy))
    case False{}:
      h

def not_true(a: Bool, h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MNat.internal_false_ne_true(h))
    case False{}:
      {==}

def not_false(a: Bool, h: {a == False{} : Bool}) -> {Bool.not(a) == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, ne_tf(h))
    case False{}:
      {==}

def same_refl(a: Nat) -> {FL.same(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      same_refl(p)

def same_eq(a: Nat, b: Nat, h: {FL.same(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      Empty.absurd({0n == 1n+y : Nat}, MNat.internal_false_ne_true(h))
    case 1n+x 0n:
      Empty.absurd({1n+x == 0n : Nat}, MNat.internal_false_ne_true(h))
    case 1n+x 1n+y:
      %same_eq(x, y, h) : {1n+x == 1n+_ : Nat}
      {==}

def same_comm(a: Nat, b: Nat) -> {FL.same(a, b) == FL.same(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      same_comm(x, y)

def get_set_ne(s: List<&2, FL.Slot>, i: Nat, +v: FL.Slot, j: Nat, h: {FL.same(i, j) == False{} : Bool}) ->
  {FL.get(FL.set(s, i, v), j) == FL.get(s, j) : FL.Slot}:
  match s i j:
    case Nil{} _ _:
      {==}
    case Con{c, t} 0n 0n:
      Empty.absurd({FL.get(FL.set(Con{c, t}, 0n, v), 0n) == FL.get(Con{c, t}, 0n) : FL.Slot}, ne_tf(h))
    case Con{c, t} 0n 1n+k:
      {==}
    case Con{c, t} 1n+m 0n:
      {==}
    case Con{c, t} 1n+m 1n+k:
      get_set_ne(t, m, v, k, h)

# a slot set in use reads in use, past the end too
def get_set_used(s: List<&2, FL.Slot>, i: Nat) -> {FL.get(FL.set(s, i, FL.Used{}), i) == FL.Used{} : FL.Slot}:
  match s i:
    case Nil{} _:
      {==}
    case Con{c, t} 0n:
      {==}
    case Con{c, t} 1n+j:
      get_set_used(t, j)

def get_set_live(s: List<&2, FL.Slot>, i: Nat, +v: FL.Slot, h: {FL.in_use(s, i) == True{} : Bool}) ->
  {FL.get(FL.set(s, i, v), i) == v : FL.Slot}:
  match s i:
    case Nil{} _:
      Empty.absurd({FL.get(FL.set(Nil{}, i, v), i) == v : FL.Slot}, MNat.internal_false_ne_true(h))
    case Con{c, t} 0n:
      {==}
    case Con{c, t} 1n+j:
      get_set_live(t, j, v, h)

def len_set(s: List<&2, FL.Slot>, i: Nat, +v: FL.Slot) ->
  {List.length(&2, FL.Slot, FL.set(s, i, v)) == List.length(&2, FL.Slot, s) : Nat}:
  match s i:
    case Nil{} _:
      {==}
    case Con{c, t} 0n:
      {==}
    case Con{c, t} 1n+j:
      %len_set(t, j, v) : {1n+List.length(&2, FL.Slot, FL.set(t, j, v)) == 1n+_ : Nat}
      {==}

def in_use_not_free(s: List<&2, FL.Slot>, i: Nat, h: {FL.in_use(s, i) == True{} : Bool}) ->
  {FL.is_free(FL.get(s, i)) == False{} : Bool}:
  match s i:
    case Nil{} _:
      {==}
    case Con{c, t} 0n:
      not_true(FL.is_free(c), h)
    case Con{c, t} 1n+j:
      in_use_not_free(t, j, h)

# setting a slot off the list leaves what the links spell
def walks_set(l: List<&2, Nat>, +s: List<&2, FL.Slot>, +i: Nat, +v: FL.Slot, x: Nat, h: {FL.mem(i, l) == False{} : Bool}) ->
  {FL.walks(l, FL.set(s, i, v), x) == FL.walks(l, s, x) : Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      +h = h
      %Equal.sym(FL.Slot, FL.get(FL.set(s, i, v), j), FL.get(s, j), get_set_ne(s, i, v, j, or_false_l(FL.same(i, j), FL.mem(i, t), h))) : {(FL.same(x, 1n+j) && (FL.is_free(_) && FL.walks(t, FL.set(s, i, v), FL.next_of(_)))) == (FL.same(x, 1n+j) && (FL.is_free(FL.get(s, j)) && FL.walks(t, s, FL.next_of(FL.get(s, j))))) : Bool}
      %Equal.sym(Bool, FL.walks(t, FL.set(s, i, v), FL.next_of(FL.get(s, j))), FL.walks(t, s, FL.next_of(FL.get(s, j))), walks_set(t, s, i, v, FL.next_of(FL.get(s, j)), or_false_r(FL.same(i, j), FL.mem(i, t), h))) : {(FL.same(x, 1n+j) && (FL.is_free(FL.get(s, j)) && _)) == (FL.same(x, 1n+j) && (FL.is_free(FL.get(s, j)) && FL.walks(t, s, FL.next_of(FL.get(s, j))))) : Bool}
      {==}

# a fact about slot j, for slot i equal to j
def tr_free(+s: List<&2, FL.Slot>, +i: Nat, +j: Nat, e: {i == j : Nat}, h: {FL.is_free(FL.get(s, j)) == True{} : Bool}) ->
  {FL.is_free(FL.get(s, i)) == True{} : Bool}:
  %Equal.sym(Nat, i, j, e) : {FL.is_free(FL.get(s, _)) == True{} : Bool}
  h

# j on the list is free; i is not, so i is not j
def wnm.go(e: Bool, +i: Nat, +j: Nat, +s: List<&2, FL.Slot>, +t: List<&2, Nat>, he: {FL.same(i, j) == e : Bool},
  hf: {FL.is_free(FL.get(s, j)) == True{} : Bool}, hu: {FL.is_free(FL.get(s, i)) == False{} : Bool},
  ih: {FL.mem(i, t) == False{} : Bool}) -> {(e || FL.mem(i, t)) == False{} : Bool}:
  match e:
    case True{}:
      Empty.absurd({(True{} || FL.mem(i, t)) == False{} : Bool}, MNat.internal_false_ne_true(
        Equal.trans(Bool, False{}, FL.is_free(FL.get(s, i)), True{}, Equal.sym(Bool, FL.is_free(FL.get(s, i)), False{}, hu),
          tr_free(s, i, j, same_eq(i, j, he), hf))))
    case False{}:
      ih

# a slot not free is on no list the links spell
def walks_not_mem(l: List<&2, Nat>, +s: List<&2, FL.Slot>, x: Nat, +i: Nat, hw: {FL.walks(l, s, x) == True{} : Bool},
  +hu: {FL.is_free(FL.get(s, i)) == False{} : Bool}) -> {FL.mem(i, l) == False{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      +hr = and_r(FL.same(x, 1n+j), (FL.is_free(FL.get(s, j)) && FL.walks(t, s, FL.next_of(FL.get(s, j)))), hw)
      wnm.go(FL.same(i, j), i, j, s, t, {==},
        and_l(FL.is_free(FL.get(s, j)), FL.walks(t, s, FL.next_of(FL.get(s, j))), hr), hu,
        walks_not_mem(t, s, FL.next_of(FL.get(s, j)), i, and_r(FL.is_free(FL.get(s, j)), FL.walks(t, s, FL.next_of(FL.get(s, j))), hr), hu))

# one slot of listed after alloc takes i: i reads in use; any other is as it was
def la.step(e: Bool, +s: List<&2, FL.Slot>, +i: Nat, +k: Nat, +t: List<&2, Nat>, +he: {FL.same(i, k) == e : Bool},
  h: {(Bool.not(FL.is_free(FL.get(s, k))) || (FL.same(k, i) || FL.mem(k, t))) == True{} : Bool}) ->
  {(Bool.not(FL.is_free(FL.get(FL.set(s, i, FL.Used{}), k))) || FL.mem(k, t)) == True{} : Bool}:
  match e:
    case True{}:
      %same_eq(i, k, he) : {(Bool.not(FL.is_free(FL.get(FL.set(s, i, FL.Used{}), _))) || FL.mem(k, t)) == True{} : Bool}
      %Equal.sym(FL.Slot, FL.get(FL.set(s, i, FL.Used{}), i), FL.Used{}, get_set_used(s, i)) : {(Bool.not(FL.is_free(_)) || FL.mem(k, t)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(FL.Slot, FL.get(FL.set(s, i, FL.Used{}), k), FL.get(s, k), get_set_ne(s, i, FL.Used{}, k, he)) : {(Bool.not(FL.is_free(_)) || FL.mem(k, t)) == True{} : Bool}
      or_drop(Bool.not(FL.is_free(FL.get(s, k))), FL.same(k, i), FL.mem(k, t), h,
        Equal.trans(Bool, FL.same(k, i), FL.same(i, k), False{}, same_comm(k, i), he))

def listed_alloc(n: Nat, +s: List<&2, FL.Slot>, +i: Nat, +t: List<&2, Nat>, h: {FL.listed(s, n, Con{i, t}) == True{} : Bool}) ->
  {FL.listed(FL.set(s, i, FL.Used{}), n, t) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      +h = h
      and_i((Bool.not(FL.is_free(FL.get(FL.set(s, i, FL.Used{}), k))) || FL.mem(k, t)), FL.listed(FL.set(s, i, FL.Used{}), k, t),
        la.step(FL.same(i, k), s, i, k, t, {==},
          and_l((Bool.not(FL.is_free(FL.get(s, k))) || FL.mem(k, Con{i, t})), FL.listed(s, k, Con{i, t}), h)),
        listed_alloc(k, s, i, t, and_r((Bool.not(FL.is_free(FL.get(s, k))) || FL.mem(k, Con{i, t})), FL.listed(s, k, Con{i, t}), h)))

# one slot of listed after free puts i on the list: i is on it; any other is as it was
def lf.step(e: Bool, +s: List<&2, FL.Slot>, +i: Nat, +k: Nat, +l: List<&2, Nat>, +fh: Nat, +he: {FL.same(i, k) == e : Bool},
  h: {(Bool.not(FL.is_free(FL.get(s, k))) || FL.mem(k, l)) == True{} : Bool}) ->
  {(Bool.not(FL.is_free(FL.get(FL.set(s, i, FL.Free{fh}), k))) || (FL.same(k, i) || FL.mem(k, l))) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.trans(Bool, True{}, FL.same(i, k), FL.same(k, i), Equal.sym(Bool, FL.same(i, k), True{}, he), same_comm(i, k)) : {(Bool.not(FL.is_free(FL.get(FL.set(s, i, FL.Free{fh}), k))) || (_ || FL.mem(k, l))) == True{} : Bool}
      or_true(Bool.not(FL.is_free(FL.get(FL.set(s, i, FL.Free{fh}), k))))
    case False{}:
      %Equal.sym(FL.Slot, FL.get(FL.set(s, i, FL.Free{fh}), k), FL.get(s, k), get_set_ne(s, i, FL.Free{fh}, k, he)) : {(Bool.not(FL.is_free(_)) || (FL.same(k, i) || FL.mem(k, l))) == True{} : Bool}
      %Equal.trans(Bool, False{}, FL.same(i, k), FL.same(k, i), Equal.sym(Bool, FL.same(i, k), False{}, he), same_comm(i, k)) : {(Bool.not(FL.is_free(FL.get(s, k))) || (_ || FL.mem(k, l))) == True{} : Bool}
      h

def listed_free(n: Nat, +s: List<&2, FL.Slot>, +i: Nat, +l: List<&2, Nat>, +fh: Nat, h: {FL.listed(s, n, l) == True{} : Bool}) ->
  {FL.listed(FL.set(s, i, FL.Free{fh}), n, Con{i, l}) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      +h = h
      and_i((Bool.not(FL.is_free(FL.get(FL.set(s, i, FL.Free{fh}), k))) || FL.mem(k, Con{i, l})), FL.listed(FL.set(s, i, FL.Free{fh}), k, Con{i, l}),
        lf.step(FL.same(i, k), s, i, k, l, fh, {==},
          and_l((Bool.not(FL.is_free(FL.get(s, k))) || FL.mem(k, l)), FL.listed(s, k, l), h)),
        listed_free(k, s, i, l, fh, and_r((Bool.not(FL.is_free(FL.get(s, k))) || FL.mem(k, l)), FL.listed(s, k, l), h)))

# listed over the slots' count after a set: the count is unchanged
def listed_len(+s: List<&2, FL.Slot>, +i: Nat, +v: FL.Slot, +l: List<&2, Nat>,
  h: {FL.listed(FL.set(s, i, v), List.length(&2, FL.Slot, s), l) == True{} : Bool}) ->
  {FL.listed(FL.set(s, i, v), List.length(&2, FL.Slot, FL.set(s, i, v)), l) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, FL.Slot, FL.set(s, i, v)), List.length(&2, FL.Slot, s), len_set(s, i, v)) : {FL.listed(FL.set(s, i, v), _, l) == True{} : Bool}
  h

# alloc's slot j, the list's head, after it is set in use: the list's rest,
# off it, still spelled from j's link
def alloc_walks(+s: List<&2, FL.Slot>, +j: Nat, +t: List<&2, Nat>, +n: Nat, hc: {FL.get(s, j) == FL.Free{n} : FL.Slot},
  hm: {FL.mem(j, t) == False{} : Bool}, hw: {FL.walks(t, s, FL.next_of(FL.get(s, j))) == True{} : Bool}) ->
  {FL.walks(t, FL.set(s, j, FL.Used{}), n) == True{} : Bool}:
  %Equal.sym(Bool, FL.walks(t, FL.set(s, j, FL.Used{}), n), FL.walks(t, s, n), walks_set(t, s, j, FL.Used{}, n, hm)) : {_ == True{} : Bool}
  %hc : {FL.walks(t, s, FL.next_of(_)) == True{} : Bool}
  hw

def alloc_ok.go(c: FL.Slot, +s: List<&2, FL.Slot>, +j: Nat, +t: List<&2, Nat>, hc: {FL.get(s, j) == c : FL.Slot},
  hf: {FL.is_free(FL.get(s, j)) == True{} : Bool}, hw: {FL.walks(t, s, FL.next_of(FL.get(s, j))) == True{} : Bool},
  +hn: {FL.nodup(Con{j, t}) == True{} : Bool}, hl: {FL.listed(s, List.length(&2, FL.Slot, s), Con{j, t}) == True{} : Bool}) ->
  {FL.ok(FL.alloc.go(c, s, j, Con{j, t})) == True{} : Bool}:
  match c:
    case FL.Used{}:
      Empty.absurd({FL.ok(FL.alloc.go(FL.Used{}, s, j, Con{j, t})) == True{} : Bool}, MNat.internal_false_ne_true(
        Equal.trans(Bool, False{}, FL.is_free(FL.get(s, j)), True{},
          Equal.cong(FL.Slot, Bool, FL.is_free, FL.Used{}, FL.get(s, j), Equal.sym(FL.Slot, FL.get(s, j), FL.Used{}, hc)), hf)))
    case FL.Free{+n}:
      and_i(FL.walks(t, FL.set(s, j, FL.Used{}), n),
        (FL.nodup(t) && FL.listed(FL.set(s, j, FL.Used{}), List.length(&2, FL.Slot, FL.set(s, j, FL.Used{})), t)),
        alloc_walks(s, j, t, n, hc, not_true(FL.mem(j, t), and_l(Bool.not(FL.mem(j, t)), FL.nodup(t), hn)), hw),
        and_i(FL.nodup(t), FL.listed(FL.set(s, j, FL.Used{}), List.length(&2, FL.Slot, FL.set(s, j, FL.Used{})), t),
          and_r(Bool.not(FL.mem(j, t)), FL.nodup(t), hn),
          listed_len(s, j, FL.Used{}, t, listed_alloc(List.length(&2, FL.Slot, s), s, j, t, hl))))

def alloc_ok(+s: List<&2, FL.Slot>, +i: Nat, +j: Nat, +t: List<&2, Nat>, e: {i == j : Nat},
  hf: {FL.is_free(FL.get(s, j)) == True{} : Bool}, hw: {FL.walks(t, s, FL.next_of(FL.get(s, j))) == True{} : Bool},
  hn: {FL.nodup(Con{j, t}) == True{} : Bool}, hl: {FL.listed(s, List.length(&2, FL.Slot, s), Con{j, t}) == True{} : Bool}) ->
  {FL.ok(FL.alloc.go(FL.get(s, i), s, i, Con{j, t})) == True{} : Bool}:
  %Equal.sym(Nat, i, j, e) : {FL.ok(FL.alloc.go(FL.get(s, _), s, _, Con{j, t})) == True{} : Bool}
  alloc_ok.go(FL.get(s, j), s, j, t, {==}, hf, hw, hn, hl)

# ok, split
def ok_w(+s: List<&2, FL.Slot>, +fh: Nat, +l: List<&2, Nat>, h: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}) -> {FL.walks(l, s, fh) == True{} : Bool}:
  and_l(FL.walks(l, s, fh), (FL.nodup(l) && FL.listed(s, List.length(&2, FL.Slot, s), l)), h)

def ok_n(+s: List<&2, FL.Slot>, +fh: Nat, +l: List<&2, Nat>, h: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}) -> {FL.nodup(l) == True{} : Bool}:
  and_l(FL.nodup(l), FL.listed(s, List.length(&2, FL.Slot, s), l), and_r(FL.walks(l, s, fh), (FL.nodup(l) && FL.listed(s, List.length(&2, FL.Slot, s), l)), h))

def ok_l(+s: List<&2, FL.Slot>, +fh: Nat, +l: List<&2, Nat>, h: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}) -> {FL.listed(s, List.length(&2, FL.Slot, s), l) == True{} : Bool}:
  and_r(FL.nodup(l), FL.listed(s, List.length(&2, FL.Slot, s), l), and_r(FL.walks(l, s, fh), (FL.nodup(l) && FL.listed(s, List.length(&2, FL.Slot, s), l)), h))

def fl_alloc(f: FL.FL, ok: {FL.ok(f) == True{} : Bool}) -> {FL.ok(FL.alloc(f)) == True{} : Bool}:
  match f:
    case FL.FL{+s, fh, +l}:
      match fh:
        case 0n:
          ok
        case 1n++i:
          match l:
            case Nil{}:
              Empty.absurd({FL.ok(FL.alloc(FL.FL{s, 1n+i, Nil{}})) == True{} : Bool}, MNat.internal_false_ne_true(ok))
            case Con{+j, +t}:
              +ok = ok
              +hw = ok_w(s, 1n+i, Con{j, t}, ok)
              +hr = and_r(FL.same(1n+i, 1n+j), (FL.is_free(FL.get(s, j)) && FL.walks(t, s, FL.next_of(FL.get(s, j)))), hw)
              alloc_ok(s, i, j, t, same_eq(i, j, and_l(FL.same(1n+i, 1n+j), (FL.is_free(FL.get(s, j)) && FL.walks(t, s, FL.next_of(FL.get(s, j)))), hw)),
                and_l(FL.is_free(FL.get(s, j)), FL.walks(t, s, FL.next_of(FL.get(s, j))), hr),
                and_r(FL.is_free(FL.get(s, j)), FL.walks(t, s, FL.next_of(FL.get(s, j))), hr),
                ok_n(s, 1n+i, Con{j, t}, ok), ok_l(s, 1n+i, Con{j, t}, ok))

# the head's link, after free: slot i reads free, linking the old head
def free_walks(+s: List<&2, FL.Slot>, +fh: Nat, +l: List<&2, Nat>, +i: Nat, live: {FL.in_use(s, i) == True{} : Bool},
  hw: {FL.walks(l, s, fh) == True{} : Bool}, hm: {FL.mem(i, l) == False{} : Bool}) ->
  {FL.walks(Con{i, l}, FL.set(s, i, FL.Free{fh}), 1n+i) == True{} : Bool}:
  %Equal.sym(FL.Slot, FL.get(FL.set(s, i, FL.Free{fh}), i), FL.Free{fh}, get_set_live(s, i, FL.Free{fh}, live)) : {(FL.same(1n+i, 1n+i) && (FL.is_free(_) && FL.walks(l, FL.set(s, i, FL.Free{fh}), FL.next_of(_)))) == True{} : Bool}
  %Equal.sym(Bool, FL.same(i, i), True{}, same_refl(i)) : {(_ && (True{} && FL.walks(l, FL.set(s, i, FL.Free{fh}), fh))) == True{} : Bool}
  %Equal.sym(Bool, FL.walks(l, FL.set(s, i, FL.Free{fh}), fh), FL.walks(l, s, fh), walks_set(l, s, i, FL.Free{fh}, fh, hm)) : {(True{} && (True{} && _)) == True{} : Bool}
  hw

def fl_free(+s: List<&2, FL.Slot>, +fh: Nat, +l: List<&2, Nat>, +i: Nat, +live: {FL.in_use(s, i) == True{} : Bool},
  +ok: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}) -> {FL.ok(FL.free(FL.FL{s, fh, l}, i)) == True{} : Bool}:
  +hw = ok_w(s, fh, l, ok)
  +hm = walks_not_mem(l, s, fh, i, hw, in_use_not_free(s, i, live))
  and_i(FL.walks(Con{i, l}, FL.set(s, i, FL.Free{fh}), 1n+i),
    (FL.nodup(Con{i, l}) && FL.listed(FL.set(s, i, FL.Free{fh}), List.length(&2, FL.Slot, FL.set(s, i, FL.Free{fh})), Con{i, l})),
    free_walks(s, fh, l, i, live, hw, hm),
    and_i(FL.nodup(Con{i, l}), FL.listed(FL.set(s, i, FL.Free{fh}), List.length(&2, FL.Slot, FL.set(s, i, FL.Free{fh})), Con{i, l}),
      and_i(Bool.not(FL.mem(i, l)), FL.nodup(l), not_false(FL.mem(i, l), hm), ok_n(s, fh, l, ok)),
      listed_len(s, i, FL.Free{fh}, Con{i, l}, listed_free(List.length(&2, FL.Slot, s), s, i, l, fh, ok_l(s, fh, l, ok)))))

def fl_head(+s: List<&2, FL.Slot>, +i: Nat, l: List<&2, Nat>, ok: {FL.ok(FL.FL{s, 1n+i, l}) == True{} : Bool}) ->
  {FL.is_free(FL.get(s, i)) == True{} : Bool}:
  match l:
    case Nil{}:
      Empty.absurd({FL.is_free(FL.get(s, i)) == True{} : Bool}, MNat.internal_false_ne_true(ok))
    case Con{+j, +t}:
      +hw = ok_w(s, 1n+i, Con{j, t}, ok)
      tr_free(s, i, j, same_eq(i, j, and_l(FL.same(1n+i, 1n+j), (FL.is_free(FL.get(s, j)) && FL.walks(t, s, FL.next_of(FL.get(s, j)))), hw)),
        and_l(FL.is_free(FL.get(s, j)), FL.walks(t, s, FL.next_of(FL.get(s, j))),
          and_r(FL.same(1n+i, 1n+j), (FL.is_free(FL.get(s, j)) && FL.walks(t, s, FL.next_of(FL.get(s, j)))), hw)))

def Laws.free_list_alloc(f, ok):
  fl_alloc(f, ok)

def Laws.free_list_free(s, fh, l, i, live, ok):
  fl_free(s, fh, l, i, live, ok)

def Laws.free_list_takes_free(s, i, l, ok):
  fl_head(s, i, l, ok)
