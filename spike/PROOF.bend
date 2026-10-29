# The evaluator spike's proofs.

import Base
import ./LAWS.bend as Laws
import ./store.bend as S
import ./rules.bend as R
import ./val.bend as V
import ./ctl.bend as CT
import ./kprim.bend as P
import ./freelist.bend as FL
import ./wiring.bend as W
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

# The net's wiring
# ================
#
# Over the model in wiring.bend. A function-typed hypothesis can be used
# only once, so facts holding for every port are Bool checks over lists,
# and an induction step that needs a case's own fact is passed as a
# function, called once in that case. The terms are long: P is the
# focused net's ends (the pair's ports, the peers, the other links' ends),
# P' the rewritten net's (the other links' ends, then the rule's placed).

# by cases: every rule is a constant the checker computes
def Laws.rules_exact(a, b, s):
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


def or_l(a: Bool, b: Bool, h: {a == True{} : Bool}) -> {(a || b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({(False{} || b) == True{} : Bool}, MNat.internal_false_ne_true(h))

def or_r(a: Bool, b: Bool, h: {b == True{} : Bool}) -> {(a || b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def or_f(a: Bool, b: Bool, ha: {a == False{} : Bool}, hb: {b == False{} : Bool}) -> {(a || b) == False{} : Bool}:
  match a:
    case True{}:
      ha
    case False{}:
      hb

def and_fr(a: Bool, b: Bool, h: {b == False{} : Bool}) -> {(a && b) == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

# a || b true with a false: b
def or_res(a: Bool, b: Bool, h: {(a || b) == True{} : Bool}, ha: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == True{} : Bool}, ne_tf(ha))
    case False{}:
      h

def and_fl(a: Bool, b: Bool, h: {a == False{} : Bool}) -> {(a && b) == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({(True{} && b) == False{} : Bool}, ne_tf(h))
    case False{}:
      {==}

def tf(h: {True{} == False{} : Bool}, -P: Type) -> P:
  Empty.absurd(P, ne_tf(h))

def ft(h: {False{} == True{} : Bool}, -P: Type) -> P:
  Empty.absurd(P, MNat.internal_false_ne_true(h))

def neq_refl(a: Nat) -> {R.nat_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      neq_refl(p)

def neq_eq(a: Nat, b: Nat, h: {R.nat_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      ft(h, {0n == 1n+y : Nat})
    case 1n+x 0n:
      ft(h, {1n+x == 0n : Nat})
    case 1n+x 1n+y:
      %neq_eq(x, y, h) : {1n+x == 1n+_ : Nat}
      {==}

def neq_comm(a: Nat, b: Nat) -> {R.nat_eq(a, b) == R.nat_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      neq_comm(x, y)

def neq_add(n: Nat, -j: Nat, -k: Nat) -> {R.nat_eq(Nat.add(n, j), Nat.add(n, k)) == R.nat_eq(j, k) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      neq_add(m, j, k)

# m below n is not n + j
def below_ne_add(n: Nat, m: Nat, -j: Nat, h: {W.below(m, n) == True{} : Bool}) -> {R.nat_eq(m, Nat.add(n, j)) == False{} : Bool}:
  match n m:
    case 0n _:
      ft(h, {R.nat_eq(m, Nat.add(0n, j)) == False{} : Bool})
    case 1n+k 0n:
      {==}
    case 1n+k 1n+q:
      below_ne_add(k, q, j, h)

def below_succ(n: Nat, p: Nat, h: {W.below(p, n) == True{} : Bool}) -> {W.below(p, 1n+n) == True{} : Bool}:
  match n p:
    case 0n _:
      ft(h, {W.below(p, 1n) == True{} : Bool})
    case 1n+k 0n:
      {==}
    case 1n+k 1n+q:
      below_succ(k, q, h)

def below_self(n: Nat) -> {W.below(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      below_self(k)

# p below 1 + n and not n: below n
def below_pred(n: Nat, p: Nat, h: {W.below(p, 1n+n) == True{} : Bool}, hn: {R.nat_eq(n, p) == False{} : Bool}) -> {W.below(p, n) == True{} : Bool}:
  match n p:
    case 0n 0n:
      tf(hn, {W.below(0n, 0n) == True{} : Bool})
    case 0n 1n+q:
      ft(h, {W.below(1n+q, 0n) == True{} : Bool})
    case 1n+k 0n:
      {==}
    case 1n+k 1n+q:
      below_pred(k, q, h, hn)

def pt_refl(x: W.Pt) -> {W.pt_eq(x, x) == True{} : Bool}:
  match x:
    case W.Pt{+m, +p}:
      and_i(R.nat_eq(m, m), R.nat_eq(p, p), neq_refl(m), neq_refl(p))

def pt_eqv(x: W.Pt, y: W.Pt, h: {W.pt_eq(x, y) == True{} : Bool}) -> {x == y : W.Pt}:
  match x y:
    case W.Pt{+m, +p} W.Pt{+n, +q}:
      +h = h
      %neq_eq(m, n, and_l(R.nat_eq(m, n), R.nat_eq(p, q), h)) : {W.Pt{m, p} == W.Pt{_, q} : W.Pt}
      %neq_eq(p, q, and_r(R.nat_eq(m, n), R.nat_eq(p, q), h)) : {W.Pt{m, p} == W.Pt{m, _} : W.Pt}
      {==}

def end_eqv(x: R.End, y: R.End, h: {R.end_eq(x, y) == True{} : Bool}) -> {x == y : R.End}:
  match x y:
    case R.Ext{i} R.Ext{j}:
      %neq_eq(i, j, h) : {R.Ext{i} == R.Ext{_} : R.End}
      {==}
    case R.Ext{i} R.New{j, q}:
      ft(h, {R.Ext{i} == R.New{j, q} : R.End})
    case R.New{i, p} R.Ext{j}:
      ft(h, {R.New{i, p} == R.Ext{j} : R.End})
    case R.New{+i, +p} R.New{+j, +q}:
      +h = h
      %neq_eq(i, j, and_l(R.nat_eq(i, j), R.nat_eq(p, q), h)) : {R.New{i, p} == R.New{_, q} : R.End}
      %neq_eq(p, q, and_r(R.nat_eq(i, j), R.nat_eq(p, q), h)) : {R.New{i, p} == R.New{i, _} : R.End}
      {==}

def end_refl(x: R.End) -> {R.end_eq(x, x) == True{} : Bool}:
  match x:
    case R.Ext{i}:
      neq_refl(i)
    case R.New{+j, +p}:
      and_i(R.nat_eq(j, j), R.nat_eq(p, p), neq_refl(j), neq_refl(p))

def or_assoc(a: Bool, +b: Bool, +c: Bool) -> {(a || (b || c)) == ((a || b) || c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def mem_app(+q: W.Pt, A: List<&2, W.Pt>, +B: List<&2, W.Pt>) -> {W.mem(q, List.append(&2, W.Pt, A, B)) == (W.mem(q, A) || W.mem(q, B)) : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Bool, W.mem(q, List.append(&2, W.Pt, t, B)), (W.mem(q, t) || W.mem(q, B)), mem_app(q, t, B)) : {(W.pt_eq(x, q) || _) == ((W.pt_eq(x, q) || W.mem(q, t)) || W.mem(q, B)) : Bool}
      or_assoc(W.pt_eq(x, q), W.mem(q, t), W.mem(q, B))

def mem_il(+q: W.Pt, +A: List<&2, W.Pt>, +B: List<&2, W.Pt>, h: {W.mem(q, A) == True{} : Bool}) -> {W.mem(q, List.append(&2, W.Pt, A, B)) == True{} : Bool}:
  Equal.trans(Bool, W.mem(q, List.append(&2, W.Pt, A, B)), (W.mem(q, A) || W.mem(q, B)), True{}, mem_app(q, A, B), or_l(W.mem(q, A), W.mem(q, B), h))

def mem_ir(+q: W.Pt, +A: List<&2, W.Pt>, +B: List<&2, W.Pt>, h: {W.mem(q, B) == True{} : Bool}) -> {W.mem(q, List.append(&2, W.Pt, A, B)) == True{} : Bool}:
  Equal.trans(Bool, W.mem(q, List.append(&2, W.Pt, A, B)), (W.mem(q, A) || W.mem(q, B)), True{}, mem_app(q, A, B), or_r(W.mem(q, A), W.mem(q, B), h))

def mem_res(+q: W.Pt, +A: List<&2, W.Pt>, +B: List<&2, W.Pt>, h: {W.mem(q, List.append(&2, W.Pt, A, B)) == True{} : Bool}, ha: {W.mem(q, A) == False{} : Bool}) -> {W.mem(q, B) == True{} : Bool}:
  or_res(W.mem(q, A), W.mem(q, B), Equal.trans(Bool, (W.mem(q, A) || W.mem(q, B)), W.mem(q, List.append(&2, W.Pt, A, B)), True{}, Equal.sym(Bool, W.mem(q, List.append(&2, W.Pt, A, B)), (W.mem(q, A) || W.mem(q, B)), mem_app(q, A, B)), h), ha)

def mem_fl(+q: W.Pt, +A: List<&2, W.Pt>, +B: List<&2, W.Pt>, h: {W.mem(q, List.append(&2, W.Pt, A, B)) == False{} : Bool}) -> {W.mem(q, A) == False{} : Bool}:
  or_false_l(W.mem(q, A), W.mem(q, B), Equal.trans(Bool, (W.mem(q, A) || W.mem(q, B)), W.mem(q, List.append(&2, W.Pt, A, B)), False{}, Equal.sym(Bool, W.mem(q, List.append(&2, W.Pt, A, B)), (W.mem(q, A) || W.mem(q, B)), mem_app(q, A, B)), h))

def mem_fr(+q: W.Pt, +A: List<&2, W.Pt>, +B: List<&2, W.Pt>, h: {W.mem(q, List.append(&2, W.Pt, A, B)) == False{} : Bool}) -> {W.mem(q, B) == False{} : Bool}:
  or_false_r(W.mem(q, A), W.mem(q, B), Equal.trans(Bool, (W.mem(q, A) || W.mem(q, B)), W.mem(q, List.append(&2, W.Pt, A, B)), False{}, Equal.sym(Bool, W.mem(q, List.append(&2, W.Pt, A, B)), (W.mem(q, A) || W.mem(q, B)), mem_app(q, A, B)), h))

def mem_ff(+q: W.Pt, +A: List<&2, W.Pt>, +B: List<&2, W.Pt>, ha: {W.mem(q, A) == False{} : Bool}, hb: {W.mem(q, B) == False{} : Bool}) -> {W.mem(q, List.append(&2, W.Pt, A, B)) == False{} : Bool}:
  Equal.trans(Bool, W.mem(q, List.append(&2, W.Pt, A, B)), (W.mem(q, A) || W.mem(q, B)), False{}, mem_app(q, A, B), or_f(W.mem(q, A), W.mem(q, B), ha, hb))

# a fact about q's membership holds of a point equal to q
def mem_tr(+x: W.Pt, +q: W.Pt, +B: List<&2, W.Pt>, e: {x == q : W.Pt}, h: {W.mem(q, B) == True{} : Bool}) -> {W.mem(x, B) == True{} : Bool}:
  %Equal.sym(W.Pt, x, q, e) : {W.mem(_, B) == True{} : Bool}
  h

def nodup_l(A: List<&2, W.Pt>, +B: List<&2, W.Pt>, h: {W.nodup(List.append(&2, W.Pt, A, B)) == True{} : Bool}) -> {W.nodup(A) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h = h
      and_i(Bool.not(W.mem(x, t)), W.nodup(t),
        not_false(W.mem(x, t), mem_fl(x, t, B, not_true(W.mem(x, List.append(&2, W.Pt, t, B)), and_l(Bool.not(W.mem(x, List.append(&2, W.Pt, t, B))), W.nodup(List.append(&2, W.Pt, t, B)), h)))),
        nodup_l(t, B, and_r(Bool.not(W.mem(x, List.append(&2, W.Pt, t, B))), W.nodup(List.append(&2, W.Pt, t, B)), h)))

def nodup_r(A: List<&2, W.Pt>, +B: List<&2, W.Pt>, h: {W.nodup(List.append(&2, W.Pt, A, B)) == True{} : Bool}) -> {W.nodup(B) == True{} : Bool}:
  match A:
    case Nil{}:
      h
    case Con{+x, +t}:
      nodup_r(t, B, and_r(Bool.not(W.mem(x, List.append(&2, W.Pt, t, B))), W.nodup(List.append(&2, W.Pt, t, B)), h))

# no element of xs is in ys
def all_out(xs: List<&2, W.Pt>, +ys: List<&2, W.Pt>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.not(W.mem(x, ys)) && all_out(t, ys)

def nodup_out(A: List<&2, W.Pt>, +B: List<&2, W.Pt>, h: {W.nodup(List.append(&2, W.Pt, A, B)) == True{} : Bool}) -> {all_out(A, B) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h = h
      and_i(Bool.not(W.mem(x, B)), all_out(t, B),
        not_false(W.mem(x, B), mem_fr(x, t, B, not_true(W.mem(x, List.append(&2, W.Pt, t, B)), and_l(Bool.not(W.mem(x, List.append(&2, W.Pt, t, B))), W.nodup(List.append(&2, W.Pt, t, B)), h)))),
        nodup_out(t, B, and_r(Bool.not(W.mem(x, List.append(&2, W.Pt, t, B))), W.nodup(List.append(&2, W.Pt, t, B)), h)))

def nodup_cat(A: List<&2, W.Pt>, +B: List<&2, W.Pt>, hA: {W.nodup(A) == True{} : Bool}, +hB: {W.nodup(B) == True{} : Bool}, hd: {all_out(A, B) == True{} : Bool}) ->
  {W.nodup(List.append(&2, W.Pt, A, B)) == True{} : Bool}:
  match A:
    case Nil{}:
      hB
    case Con{+x, +t}:
      +hA = hA
      +hd = hd
      and_i(Bool.not(W.mem(x, List.append(&2, W.Pt, t, B))), W.nodup(List.append(&2, W.Pt, t, B)),
        not_false(W.mem(x, List.append(&2, W.Pt, t, B)), mem_ff(x, t, B,
          not_true(W.mem(x, t), and_l(Bool.not(W.mem(x, t)), W.nodup(t), hA)),
          not_true(W.mem(x, B), and_l(Bool.not(W.mem(x, B)), all_out(t, B), hd)))),
        nodup_cat(t, B, and_r(Bool.not(W.mem(x, t)), W.nodup(t), hA), hB, and_r(Bool.not(W.mem(x, B)), all_out(t, B), hd)))

# x in A, A's elements out of B: x is not in B
def out_mem.go(e: Bool, +x: W.Pt, +y: W.Pt, +B: List<&2, W.Pt>, he: {W.pt_eq(x, y) == e : Bool}, hx: {W.mem(x, B) == False{} : Bool}, hy: {W.mem(y, B) == True{} : Bool}) -> {e == False{} : Bool}:
  match e:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MNat.internal_false_ne_true(Equal.trans(Bool, False{}, W.mem(x, B), True{}, Equal.sym(Bool, W.mem(x, B), False{}, hx), mem_tr(x, y, B, pt_eqv(x, y, he), hy))))
    case False{}:
      {==}

def out_mem(A: List<&2, W.Pt>, +B: List<&2, W.Pt>, +y: W.Pt, h: {all_out(A, B) == True{} : Bool}, +hy: {W.mem(y, B) == True{} : Bool}) -> {W.mem(y, A) == False{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h = h
      or_f(W.pt_eq(x, y), W.mem(y, t),
        out_mem.go(W.pt_eq(x, y), x, y, B, {==}, not_true(W.mem(x, B), and_l(Bool.not(W.mem(x, B)), all_out(t, B), h)), hy),
        out_mem(t, B, y, and_r(Bool.not(W.mem(x, B)), all_out(t, B), h), hy))

def out_tail(A: List<&2, W.Pt>, +y: W.Pt, +B: List<&2, W.Pt>, h: {all_out(A, Con{y, B}) == True{} : Bool}) -> {all_out(A, B) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h = h
      and_i(Bool.not(W.mem(x, B)), all_out(t, B),
        not_false(W.mem(x, B), or_false_r(W.pt_eq(y, x), W.mem(x, B), not_true(W.mem(x, Con{y, B}), and_l(Bool.not(W.mem(x, Con{y, B})), all_out(t, Con{y, B}), h)))),
        out_tail(t, y, B, and_r(Bool.not(W.mem(x, Con{y, B})), all_out(t, Con{y, B}), h)))

def out_sym(+A: List<&2, W.Pt>, B: List<&2, W.Pt>, h: {all_out(A, B) == True{} : Bool}) -> {all_out(B, A) == True{} : Bool}:
  match B:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +h = h
      and_i(Bool.not(W.mem(y, A)), all_out(t, A),
        not_false(W.mem(y, A), out_mem(A, Con{y, t}, y, h, or_l(W.pt_eq(y, y), W.mem(y, t), pt_refl(y)))),
        out_sym(A, t, out_tail(A, y, t, h)))

def out_fst(A: List<&2, W.Pt>, +B: List<&2, W.Pt>, +Z: List<&2, W.Pt>, h: {all_out(List.append(&2, W.Pt, A, B), Z) == True{} : Bool}) -> {all_out(A, Z) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h = h
      and_i(Bool.not(W.mem(x, Z)), all_out(t, Z), and_l(Bool.not(W.mem(x, Z)), all_out(List.append(&2, W.Pt, t, B), Z), h),
        out_fst(t, B, Z, and_r(Bool.not(W.mem(x, Z)), all_out(List.append(&2, W.Pt, t, B), Z), h)))

def out_snd(A: List<&2, W.Pt>, +B: List<&2, W.Pt>, +Z: List<&2, W.Pt>, h: {all_out(List.append(&2, W.Pt, A, B), Z) == True{} : Bool}) -> {all_out(B, Z) == True{} : Bool}:
  match A:
    case Nil{}:
      h
    case Con{+x, +t}:
      out_snd(t, B, Z, and_r(Bool.not(W.mem(x, Z)), all_out(List.append(&2, W.Pt, t, B), Z), h))

# x in xs, xs out of ys: x not in ys
def out_at(+xs: List<&2, W.Pt>, +ys: List<&2, W.Pt>, +x: W.Pt, h: {all_out(xs, ys) == True{} : Bool}, hx: {W.mem(x, xs) == True{} : Bool}) -> {W.mem(x, ys) == False{} : Bool}:
  out_mem(ys, xs, x, out_sym(xs, ys, h), hx)

def live_l(+ks: List<&2, R.NodeKind>, A: List<&2, W.Pt>, +B: List<&2, W.Pt>, h: {W.all_live(ks, List.append(&2, W.Pt, A, B)) == True{} : Bool}) -> {W.all_live(ks, A) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h = h
      and_i(W.live(ks, x), W.all_live(ks, t), and_l(W.live(ks, x), W.all_live(ks, List.append(&2, W.Pt, t, B)), h),
        live_l(ks, t, B, and_r(W.live(ks, x), W.all_live(ks, List.append(&2, W.Pt, t, B)), h)))

def live_r(+ks: List<&2, R.NodeKind>, A: List<&2, W.Pt>, +B: List<&2, W.Pt>, h: {W.all_live(ks, List.append(&2, W.Pt, A, B)) == True{} : Bool}) -> {W.all_live(ks, B) == True{} : Bool}:
  match A:
    case Nil{}:
      h
    case Con{+x, +t}:
      live_r(ks, t, B, and_r(W.live(ks, x), W.all_live(ks, List.append(&2, W.Pt, t, B)), h))

def live_cat(+ks: List<&2, R.NodeKind>, A: List<&2, W.Pt>, +B: List<&2, W.Pt>, hA: {W.all_live(ks, A) == True{} : Bool}, +hB: {W.all_live(ks, B) == True{} : Bool}) -> {W.all_live(ks, List.append(&2, W.Pt, A, B)) == True{} : Bool}:
  match A:
    case Nil{}:
      hB
    case Con{+x, +t}:
      +hA = hA
      and_i(W.live(ks, x), W.all_live(ks, List.append(&2, W.Pt, t, B)), and_l(W.live(ks, x), W.all_live(ks, t), hA),
        live_cat(ks, t, B, and_r(W.live(ks, x), W.all_live(ks, t), hA), hB))

# x in xs, all of xs live: x live
def live_at.go(e: Bool, +ks: List<&2, R.NodeKind>, +x: W.Pt, +y: W.Pt, +t: List<&2, W.Pt>, he: {W.pt_eq(y, x) == e : Bool},
  hy: {W.live(ks, y) == True{} : Bool}, hm: {(e || W.mem(x, t)) == True{} : Bool},
  ih: {W.mem(x, t) == True{} : Bool} -> {W.live(ks, x) == True{} : Bool}) -> {W.live(ks, x) == True{} : Bool}:
  match e:
    case True{}:
      %pt_eqv(y, x, he) : {W.live(ks, _) == True{} : Bool}
      hy
    case False{}:
      ih(hm)

def live_at(xs: List<&2, W.Pt>, +ks: List<&2, R.NodeKind>, +x: W.Pt, h: {W.all_live(ks, xs) == True{} : Bool}, hx: {W.mem(x, xs) == True{} : Bool}) -> {W.live(ks, x) == True{} : Bool}:
  match xs:
    case Nil{}:
      ft(hx, {W.live(ks, x) == True{} : Bool})
    case Con{+y, +t}:
      +h = h
      live_at.go(W.pt_eq(y, x), ks, x, y, t, {==}, and_l(W.live(ks, y), W.all_live(ks, t), h), hx,
        h2 => live_at(t, ks, x, and_r(W.live(ks, y), W.all_live(ks, t), h), h2))

def neq_succ_add(n: Nat, -k: Nat) -> {R.nat_eq(n, 1n+Nat.add(n, k)) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      neq_succ_add(m, k)

def below_ne(n: Nat, m: Nat, h: {W.below(m, n) == True{} : Bool}) -> {R.nat_eq(n, m) == False{} : Bool}:
  match n m:
    case 0n _:
      ft(h, {R.nat_eq(0n, m) == False{} : Bool})
    case 1n+k 0n:
      {==}
    case 1n+k 1n+q:
      below_ne(k, q, h)

def emem_app(+e: R.End, A: List<&2, R.End>, +B: List<&2, R.End>) -> {R.end_mem(e, List.append(&2, R.End, A, B)) == (R.end_mem(e, A) || R.end_mem(e, B)) : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Bool, R.end_mem(e, List.append(&2, R.End, t, B)), (R.end_mem(e, t) || R.end_mem(e, B)), emem_app(e, t, B)) : {(R.end_eq(x, e) || _) == ((R.end_eq(x, e) || R.end_mem(e, t)) || R.end_mem(e, B)) : Bool}
      or_assoc(R.end_eq(x, e), R.end_mem(e, t), R.end_mem(e, B))

def emem_il(+e: R.End, +A: List<&2, R.End>, +B: List<&2, R.End>, h: {R.end_mem(e, A) == True{} : Bool}) -> {R.end_mem(e, List.append(&2, R.End, A, B)) == True{} : Bool}:
  Equal.trans(Bool, R.end_mem(e, List.append(&2, R.End, A, B)), (R.end_mem(e, A) || R.end_mem(e, B)), True{}, emem_app(e, A, B), or_l(R.end_mem(e, A), R.end_mem(e, B), h))

def emem_ir(+e: R.End, +A: List<&2, R.End>, +B: List<&2, R.End>, h: {R.end_mem(e, B) == True{} : Bool}) -> {R.end_mem(e, List.append(&2, R.End, A, B)) == True{} : Bool}:
  Equal.trans(Bool, R.end_mem(e, List.append(&2, R.End, A, B)), (R.end_mem(e, A) || R.end_mem(e, B)), True{}, emem_app(e, A, B), or_r(R.end_mem(e, A), R.end_mem(e, B), h))

def emem_or(+e: R.End, +A: List<&2, R.End>, +B: List<&2, R.End>, h: {R.end_mem(e, List.append(&2, R.End, A, B)) == True{} : Bool}) -> {(R.end_mem(e, A) || R.end_mem(e, B)) == True{} : Bool}:
  Equal.trans(Bool, (R.end_mem(e, A) || R.end_mem(e, B)), R.end_mem(e, List.append(&2, R.End, A, B)), True{}, Equal.sym(Bool, R.end_mem(e, List.append(&2, R.End, A, B)), (R.end_mem(e, A) || R.end_mem(e, B)), emem_app(e, A, B)), h)

def emem_ff(+e: R.End, +A: List<&2, R.End>, +B: List<&2, R.End>, ha: {R.end_mem(e, A) == False{} : Bool}, hb: {R.end_mem(e, B) == False{} : Bool}) -> {R.end_mem(e, List.append(&2, R.End, A, B)) == False{} : Bool}:
  Equal.trans(Bool, R.end_mem(e, List.append(&2, R.End, A, B)), (R.end_mem(e, A) || R.end_mem(e, B)), False{}, emem_app(e, A, B), or_f(R.end_mem(e, A), R.end_mem(e, B), ha, hb))

def emem_left.go(a: Bool, b: Bool, h: {(a || b) == True{} : Bool}, hb: {b == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, MNat.internal_false_ne_true(Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, hb), h)))

# an end in A ++ B and not in B: in A
def emem_left(+e: R.End, +A: List<&2, R.End>, +B: List<&2, R.End>, h: {R.end_mem(e, List.append(&2, R.End, A, B)) == True{} : Bool}, hb: {R.end_mem(e, B) == False{} : Bool}) -> {R.end_mem(e, A) == True{} : Bool}:
  emem_left.go(R.end_mem(e, A), R.end_mem(e, B), emem_or(e, A, B, h), hb)

def emem_tr(+x: R.End, +e: R.End, +B: List<&2, R.End>, eq: {x == e : R.End}, h: {R.end_mem(e, B) == True{} : Bool}) -> {R.end_mem(x, B) == True{} : Bool}:
  %Equal.sym(R.End, x, e, eq) : {R.end_mem(_, B) == True{} : Bool}
  h

def in_at.go(c: Bool, +z: R.End, +x: R.End, +t: List<&2, R.End>, +Y: List<&2, R.End>, he: {R.end_eq(z, x) == c : Bool},
  hz: {R.end_mem(z, Y) == True{} : Bool}, hm: {(c || R.end_mem(x, t)) == True{} : Bool},
  ih: {R.end_mem(x, t) == True{} : Bool} -> {R.end_mem(x, Y) == True{} : Bool}) -> {R.end_mem(x, Y) == True{} : Bool}:
  match c:
    case True{}:
      %end_eqv(z, x, he) : {R.end_mem(_, Y) == True{} : Bool}
      hz
    case False{}:
      ih(hm)

# x in X, all of X in Y: x in Y
def in_at(X: List<&2, R.End>, +Y: List<&2, R.End>, +x: R.End, h: {R.all_in(X, Y) == True{} : Bool}, hx: {R.end_mem(x, X) == True{} : Bool}) -> {R.end_mem(x, Y) == True{} : Bool}:
  match X:
    case Nil{}:
      ft(hx, {R.end_mem(x, Y) == True{} : Bool})
    case Con{+z, +t}:
      +h = h
      in_at.go(R.end_eq(z, x), z, x, t, Y, {==}, and_l(R.end_mem(z, Y), R.all_in(t, Y), h), hx,
        h2 => in_at(t, Y, x, and_r(R.end_mem(z, Y), R.all_in(t, Y), h), h2))

def in_cons(X: List<&2, R.End>, +y: R.End, +Y: List<&2, R.End>, h: {R.all_in(X, Y) == True{} : Bool}) -> {R.all_in(X, Con{y, Y}) == True{} : Bool}:
  match X:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h = h
      and_i(R.end_mem(x, Con{y, Y}), R.all_in(t, Con{y, Y}),
        or_r(R.end_eq(y, x), R.end_mem(x, Y), and_l(R.end_mem(x, Y), R.all_in(t, Y), h)),
        in_cons(t, y, Y, and_r(R.end_mem(x, Y), R.all_in(t, Y), h)))

def in_refl(X: List<&2, R.End>) -> {R.all_in(X, X) == True{} : Bool}:
  match X:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      and_i(R.end_mem(x, Con{x, t}), R.all_in(t, Con{x, t}), or_l(R.end_eq(x, x), R.end_mem(x, t), end_refl(x)),
        in_cons(t, x, t, in_refl(t)))

def in_app_l(A: List<&2, R.End>, +B: List<&2, R.End>) -> {R.all_in(A, List.append(&2, R.End, A, B)) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      and_i(R.end_mem(x, Con{x, List.append(&2, R.End, t, B)}), R.all_in(t, Con{x, List.append(&2, R.End, t, B)}),
        or_l(R.end_eq(x, x), R.end_mem(x, List.append(&2, R.End, t, B)), end_refl(x)),
        in_cons(t, x, List.append(&2, R.End, t, B), in_app_l(t, B)))

def in_app_r(A: List<&2, R.End>, +B: List<&2, R.End>) -> {R.all_in(B, List.append(&2, R.End, A, B)) == True{} : Bool}:
  match A:
    case Nil{}:
      in_refl(B)
    case Con{+x, +t}:
      in_cons(B, x, List.append(&2, R.End, t, B), in_app_r(t, B))

def in_trans(X: List<&2, R.End>, +Y: List<&2, R.End>, +Z: List<&2, R.End>, h: {R.all_in(X, Y) == True{} : Bool}, +hyz: {R.all_in(Y, Z) == True{} : Bool}) -> {R.all_in(X, Z) == True{} : Bool}:
  match X:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h = h
      and_i(R.end_mem(x, Z), R.all_in(t, Z), in_at(Y, Z, x, hyz, and_l(R.end_mem(x, Y), R.all_in(t, Y), h)),
        in_trans(t, Y, Z, and_r(R.end_mem(x, Y), R.all_in(t, Y), h), hyz))

def node_no_ext(+i: Nat, +j: Nat, n: Nat, +p: Nat) -> {R.end_mem(R.Ext{i}, R.node_ends(j, n, p)) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+q:
      node_no_ext(i, j, q, 1n+p)

def new_no_ext(+i: Nat, xs: List<&2, R.Spec>, +j: Nat) -> {R.end_mem(R.Ext{i}, R.new_ends(xs, j)) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{R.Spec{+k, s}, +t}:
      emem_ff(R.Ext{i}, R.node_ends(j, R.arity(k), 0n), R.new_ends(t, 1n+j), node_no_ext(i, j, R.arity(k), 0n), new_no_ext(i, t, 1n+j))

def node_in(+j: Nat, n: Nat, +p0: Nat, p: Nat, h: {W.below(p, n) == True{} : Bool}) -> {R.end_mem(R.New{j, Nat.add(p0, p)}, R.node_ends(j, n, p0)) == True{} : Bool}:
  match n p:
    case 0n _:
      ft(h, {R.end_mem(R.New{j, Nat.add(p0, p)}, R.node_ends(j, 0n, p0)) == True{} : Bool})
    case 1n++q 0n:
      %Equal.sym(Nat, Nat.add(p0, 0n), p0, add_zero(p0)) : {R.end_mem(R.New{j, _}, R.node_ends(j, 1n+q, p0)) == True{} : Bool}
      or_l(R.end_eq(R.New{j, p0}, R.New{j, p0}), R.end_mem(R.New{j, p0}, R.node_ends(j, q, 1n+p0)), end_refl(R.New{j, p0}))
    case 1n++q 1n++r:
      %Equal.sym(Nat, Nat.add(p0, 1n+r), 1n+Nat.add(p0, r), succ_add(p0, r)) : {R.end_mem(R.New{j, _}, R.node_ends(j, 1n+q, p0)) == True{} : Bool}
      or_r(R.end_eq(R.New{j, p0}, R.New{j, 1n+Nat.add(p0, r)}), R.end_mem(R.New{j, 1n+Nat.add(p0, r)}, R.node_ends(j, q, 1n+p0)), node_in(j, q, 1n+p0, r, h))

# an end New m p0 + p of node_ends j n p0: p below n
def node_live(+j: Nat, n: Nat, +p0: Nat, +m: Nat, p: Nat, h: {R.end_mem(R.New{m, Nat.add(p0, p)}, R.node_ends(j, n, p0)) == True{} : Bool}) -> {W.below(p, n) == True{} : Bool}:
  match n p:
    case 0n _:
      ft(h, {W.below(p, 0n) == True{} : Bool})
    case 1n+q 0n:
      {==}
    case 1n++q 1n++r:
      +h1 = emem_tr(R.New{m, 1n+Nat.add(p0, r)}, R.New{m, Nat.add(p0, 1n+r)}, Con{R.New{j, p0}, R.node_ends(j, q, 1n+p0)},
        Equal.cong(Nat, R.End, (x => R.New{m, x}), 1n+Nat.add(p0, r), Nat.add(p0, 1n+r), Equal.sym(Nat, Nat.add(p0, 1n+r), 1n+Nat.add(p0, r), succ_add(p0, r))), h)
      node_live(j, q, 1n+p0, m, r, or_res(R.end_eq(R.New{j, p0}, R.New{m, 1n+Nat.add(p0, r)}), R.end_mem(R.New{m, 1n+Nat.add(p0, r)}, R.node_ends(j, q, 1n+p0)), h1,
        and_fr(R.nat_eq(j, m), R.nat_eq(p0, 1n+Nat.add(p0, r)), neq_succ_add(p0, r))))

# an end of a node below j1 is in no new_ends from j1
def node_low(+j1: Nat, n: Nat, +p0: Nat, +m: Nat, +p: Nat, h: {R.nat_eq(j1, m) == False{} : Bool}) -> {R.end_mem(R.New{m, p}, R.node_ends(j1, n, p0)) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++q:
      +h = h
      or_f(R.end_eq(R.New{j1, p0}, R.New{m, p}), R.end_mem(R.New{m, p}, R.node_ends(j1, q, 1n+p0)),
        and_fl(R.nat_eq(j1, m), R.nat_eq(p0, p), h), node_low(j1, q, 1n+p0, m, p, h))

def new_low(xs: List<&2, R.Spec>, +j1: Nat, +m: Nat, +p: Nat, h: {W.below(m, j1) == True{} : Bool}) -> {R.end_mem(R.New{m, p}, R.new_ends(xs, j1)) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{R.Spec{+k, s}, +t}:
      +h = h
      emem_ff(R.New{m, p}, R.node_ends(j1, R.arity(k), 0n), R.new_ends(t, 1n+j1), node_low(j1, R.arity(k), 0n, m, p, below_ne(j1, m, h)),
        new_low(t, 1n+j1, m, p, below_succ(j1, m, h)))

# port p of new node j, live by its kind, is an end the rule must link
def new_in(xs: List<&2, R.Spec>, +j0: Nat, j: Nat, +p: Nat, h: {W.below(p, R.arity(W.kind_at(W.kinds(xs), j))) == True{} : Bool}) ->
  {R.end_mem(R.New{Nat.add(j0, j), p}, R.new_ends(xs, j0)) == True{} : Bool}:
  match xs j:
    case Nil{} _:
      ft(h, {R.end_mem(R.New{Nat.add(j0, j), p}, R.new_ends(Nil{}, j0)) == True{} : Bool})
    case Con{R.Spec{+k, s}, +t} 0n:
      %Equal.sym(Nat, Nat.add(j0, 0n), j0, add_zero(j0)) : {R.end_mem(R.New{_, p}, R.new_ends(Con{R.Spec{k, s}, t}, j0)) == True{} : Bool}
      emem_il(R.New{j0, p}, R.node_ends(j0, R.arity(k), 0n), R.new_ends(t, 1n+j0), node_in(j0, R.arity(k), 0n, p, h))
    case Con{R.Spec{+k, s}, +t} 1n++r:
      %Equal.sym(Nat, Nat.add(j0, 1n+r), 1n+Nat.add(j0, r), succ_add(j0, r)) : {R.end_mem(R.New{_, p}, R.new_ends(Con{R.Spec{k, s}, t}, j0)) == True{} : Bool}
      emem_ir(R.New{1n+Nat.add(j0, r), p}, R.node_ends(j0, R.arity(k), 0n), R.new_ends(t, 1n+j0), new_in(t, 1n+j0, r, p, h))

# an end of new node j the rule must link: its port is live by its kind
def new_live(xs: List<&2, R.Spec>, +j0: Nat, j: Nat, +p: Nat, h: {R.end_mem(R.New{Nat.add(j0, j), p}, R.new_ends(xs, j0)) == True{} : Bool}) ->
  {W.below(p, R.arity(W.kind_at(W.kinds(xs), j))) == True{} : Bool}:
  match xs j:
    case Nil{} _:
      ft(h, {W.below(p, R.arity(W.kind_at(W.kinds(Nil{}), j))) == True{} : Bool})
    case Con{R.Spec{+k, s}, +t} 0n:
      +h1 = emem_tr(R.New{j0, p}, R.New{Nat.add(j0, 0n), p}, R.new_ends(Con{R.Spec{k, s}, t}, j0),
        Equal.cong(Nat, R.End, (x => R.New{x, p}), j0, Nat.add(j0, 0n), Equal.sym(Nat, Nat.add(j0, 0n), j0, add_zero(j0))), h)
      node_live(j0, R.arity(k), 0n, j0, p, emem_left(R.New{j0, p}, R.node_ends(j0, R.arity(k), 0n), R.new_ends(t, 1n+j0), h1,
        new_low(t, 1n+j0, j0, p, below_self(j0))))
    case Con{R.Spec{+k, s}, +t} 1n++r:
      +h1 = emem_tr(R.New{1n+Nat.add(j0, r), p}, R.New{Nat.add(j0, 1n+r), p}, R.new_ends(Con{R.Spec{k, s}, t}, j0),
        Equal.cong(Nat, R.End, (x => R.New{x, p}), 1n+Nat.add(j0, r), Nat.add(j0, 1n+r), Equal.sym(Nat, Nat.add(j0, 1n+r), 1n+Nat.add(j0, r), succ_add(j0, r))), h)
      new_live(t, 1n+j0, r, p, or_res(R.end_mem(R.New{1n+Nat.add(j0, r), p}, R.node_ends(j0, R.arity(k), 0n)), R.end_mem(R.New{1n+Nat.add(j0, r), p}, R.new_ends(t, 1n+j0)),
        emem_or(R.New{1n+Nat.add(j0, r), p}, R.node_ends(j0, R.arity(k), 0n), R.new_ends(t, 1n+j0), h1),
        node_low(j0, R.arity(k), 0n, 1n+Nat.add(j0, r), p, neq_succ_add(j0, r))))

def aux_no_new(+j: Nat, +p: Nat, n: Nat, +base: Nat) -> {R.end_mem(R.New{j, p}, R.aux_ends(n, base)) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+q:
      aux_no_new(j, p, q, 1n+base)

# Ports and kinds
def ports_has.go(c: Bool, +n: Nat, +q: Nat, +p: Nat, he: {R.nat_eq(q, p) == c : Bool}, h: {W.below(p, 1n+q) == True{} : Bool},
  ih: {W.below(p, q) == True{} : Bool} -> {W.mem(W.Pt{n, p}, W.ports(n, q)) == True{} : Bool}) ->
  {W.mem(W.Pt{n, p}, W.ports(n, 1n+q)) == True{} : Bool}:
  match c:
    case True{}:
      or_l(W.pt_eq(W.Pt{n, q}, W.Pt{n, p}), W.mem(W.Pt{n, p}, W.ports(n, q)), and_i(R.nat_eq(n, n), R.nat_eq(q, p), neq_refl(n), he))
    case False{}:
      or_r(W.pt_eq(W.Pt{n, q}, W.Pt{n, p}), W.mem(W.Pt{n, p}, W.ports(n, q)), ih(below_pred(q, p, h, he)))

# a port below k is among node n's ports below k
def ports_has(+n: Nat, k: Nat, +p: Nat, h: {W.below(p, k) == True{} : Bool}) -> {W.mem(W.Pt{n, p}, W.ports(n, k)) == True{} : Bool}:
  match k:
    case 0n:
      ft(h, {W.mem(W.Pt{n, p}, W.ports(n, 0n)) == True{} : Bool})
    case 1n++q:
      ports_has.go(R.nat_eq(q, p), n, q, p, {==}, h, h2 => ports_has(n, q, p, h2))

def ports_not(+n: Nat, k: Nat, +m: Nat, +p: Nat, +h: {R.nat_eq(n, m) == False{} : Bool}) -> {W.mem(W.Pt{m, p}, W.ports(n, k)) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++q:
      or_f(W.pt_eq(W.Pt{n, q}, W.Pt{m, p}), W.mem(W.Pt{m, p}, W.ports(n, q)), and_fl(R.nat_eq(n, m), R.nat_eq(q, p), h), ports_not(n, q, m, p, h))

def ka_free(ks: List<&2, R.NodeKind>, n: Nat) -> {W.kind_at(W.set(ks, n, R.KFree{}), n) == R.KFree{} : R.NodeKind}:
  match ks n:
    case Nil{} _:
      {==}
    case Con{k, t} 0n:
      {==}
    case Con{k, t} 1n+m:
      ka_free(t, m)

def ka_ne(ks: List<&2, R.NodeKind>, n: Nat, +v: R.NodeKind, m: Nat, h: {R.nat_eq(n, m) == False{} : Bool}) ->
  {W.kind_at(W.set(ks, n, v), m) == W.kind_at(ks, m) : R.NodeKind}:
  match ks n m:
    case Nil{} _ _:
      {==}
    case Con{k, t} 0n 0n:
      tf(h, {W.kind_at(W.set(Con{k, t}, 0n, v), 0n) == W.kind_at(Con{k, t}, 0n) : R.NodeKind})
    case Con{k, t} 0n 1n+q:
      {==}
    case Con{k, t} 1n+r 0n:
      {==}
    case Con{k, t} 1n+r 1n+q:
      ka_ne(t, r, v, q, h)

def klen_set(ks: List<&2, R.NodeKind>, n: Nat, +v: R.NodeKind) -> {List.length(&2, R.NodeKind, W.set(ks, n, v)) == List.length(&2, R.NodeKind, ks) : Nat}:
  match ks n:
    case Nil{} _:
      {==}
    case Con{k, t} 0n:
      {==}
    case Con{k, t} 1n+m:
      %klen_set(t, m, v) : {1n+List.length(&2, R.NodeKind, W.set(t, m, v)) == 1n+_ : Nat}
      {==}

def ka_lt(K1: List<&2, R.NodeKind>, +K2: List<&2, R.NodeKind>, m: Nat, h: {W.below(m, List.length(&2, R.NodeKind, K1)) == True{} : Bool}) ->
  {W.kind_at(List.append(&2, R.NodeKind, K1, K2), m) == W.kind_at(K1, m) : R.NodeKind}:
  match K1 m:
    case Nil{} _:
      ft(h, {W.kind_at(List.append(&2, R.NodeKind, Nil{}, K2), m) == W.kind_at(Nil{}, m) : R.NodeKind})
    case Con{k, t} 0n:
      {==}
    case Con{k, t} 1n+q:
      ka_lt(t, K2, q, h)

def ka_off(K1: List<&2, R.NodeKind>, +K2: List<&2, R.NodeKind>, -j: Nat) ->
  {W.kind_at(List.append(&2, R.NodeKind, K1, K2), Nat.add(List.length(&2, R.NodeKind, K1), j)) == W.kind_at(K2, j) : R.NodeKind}:
  match K1:
    case Nil{}:
      {==}
    case Con{k, t}:
      ka_off(t, K2, j)

def len_app(K1: List<&2, R.NodeKind>, +K2: List<&2, R.NodeKind>) ->
  {List.length(&2, R.NodeKind, List.append(&2, R.NodeKind, K1, K2)) == Nat.add(List.length(&2, R.NodeKind, K1), List.length(&2, R.NodeKind, K2)) : Nat}:
  match K1:
    case Nil{}:
      {==}
    case Con{k, t}:
      %len_app(t, K2) : {1n+List.length(&2, R.NodeKind, List.append(&2, R.NodeKind, t, K2)) == 1n+_ : Nat}
      {==}

# a live port's node is in range
def live_range(ks: List<&2, R.NodeKind>, n: Nat, +p: Nat, h: {W.live(ks, W.Pt{n, p}) == True{} : Bool}) -> {W.below(n, List.length(&2, R.NodeKind, ks)) == True{} : Bool}:
  match ks n:
    case Nil{} _:
      ft(h, {W.below(n, 0n) == True{} : Bool})
    case Con{k, t} 0n:
      {==}
    case Con{k, t} 1n+m:
      live_range(t, m, p, h)

# Placing the rule's ends
def ends_app(A: List<&2, W.Ln>, +B: List<&2, W.Ln>) -> {W.ends(List.append(&2, W.Ln, A, B)) == List.append(&2, W.Pt, W.ends(A), W.ends(B)) : List<&2, W.Pt>}:
  match A:
    case Nil{}:
      {==}
    case Con{W.Ln{+x, +y}, +t}:
      %Equal.sym(List<&2, W.Pt>, W.ends(List.append(&2, W.Ln, t, B)), List.append(&2, W.Pt, W.ends(t), W.ends(B)), ends_app(t, B)) : {Con{x, Con{y, _}} == Con{x, Con{y, List.append(&2, W.Pt, W.ends(t), W.ends(B))}} : List<&2, W.Pt>}
      {==}

def ends_links(+n0: Nat, +es: W.Peers, ls: List<&2, R.Link>) -> {W.ends(W.links(n0, es, ls)) == W.sigs(n0, es, R.ends(ls)) : List<&2, W.Pt>}:
  match ls:
    case Nil{}:
      {==}
    case Con{R.Link{+x, +y}, +t}:
      %Equal.sym(List<&2, W.Pt>, W.ends(W.links(n0, es, t)), W.sigs(n0, es, R.ends(t)), ends_links(n0, es, t)) : {Con{W.sig(n0, es, x), Con{W.sig(n0, es, y), _}} == Con{W.sig(n0, es, x), Con{W.sig(n0, es, y), W.sigs(n0, es, R.ends(t))}} : List<&2, W.Pt>}
      {==}

def sigs_app(+n0: Nat, +es: W.Peers, A: List<&2, R.End>, +B: List<&2, R.End>) -> {W.sigs(n0, es, List.append(&2, R.End, A, B)) == List.append(&2, W.Pt, W.sigs(n0, es, A), W.sigs(n0, es, B)) : List<&2, W.Pt>}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(List<&2, W.Pt>, W.sigs(n0, es, List.append(&2, R.End, t, B)), List.append(&2, W.Pt, W.sigs(n0, es, t), W.sigs(n0, es, B)), sigs_app(n0, es, t, B)) : {Con{W.sig(n0, es, x), _} == Con{W.sig(n0, es, x), List.append(&2, W.Pt, W.sigs(n0, es, t), W.sigs(n0, es, B))} : List<&2, W.Pt>}
      {==}

def app_assoc(A: List<&2, W.Pt>, +B: List<&2, W.Pt>, +C: List<&2, W.Pt>) -> {List.append(&2, W.Pt, List.append(&2, W.Pt, A, B), C) == List.append(&2, W.Pt, A, List.append(&2, W.Pt, B, C)) : List<&2, W.Pt>}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %app_assoc(t, B, C) : {Con{x, List.append(&2, W.Pt, List.append(&2, W.Pt, t, B), C)} == Con{x, _} : List<&2, W.Pt>}
      {==}

def mso.go(c: Bool, +n0: Nat, +es: W.Peers, +x: R.End, +y: R.End, +t: List<&2, R.End>, he: {R.end_eq(y, x) == c : Bool},
  hm: {(c || R.end_mem(x, t)) == True{} : Bool},
  ih: {R.end_mem(x, t) == True{} : Bool} -> {W.mem(W.sig(n0, es, x), W.sigs(n0, es, t)) == True{} : Bool}) ->
  {W.mem(W.sig(n0, es, x), W.sigs(n0, es, Con{y, t})) == True{} : Bool}:
  match c:
    case True{}:
      %end_eqv(y, x, he) : {W.mem(W.sig(n0, es, _), W.sigs(n0, es, Con{y, t})) == True{} : Bool}
      or_l(W.pt_eq(W.sig(n0, es, y), W.sig(n0, es, y)), W.mem(W.sig(n0, es, y), W.sigs(n0, es, t)), pt_refl(W.sig(n0, es, y)))
    case False{}:
      or_r(W.pt_eq(W.sig(n0, es, y), W.sig(n0, es, x)), W.mem(W.sig(n0, es, x), W.sigs(n0, es, t)), ih(hm))

# an end in Y lands among Y's placed ends
def mem_sigs_of(+n0: Nat, +es: W.Peers, +x: R.End, Y: List<&2, R.End>, h: {R.end_mem(x, Y) == True{} : Bool}) -> {W.mem(W.sig(n0, es, x), W.sigs(n0, es, Y)) == True{} : Bool}:
  match Y:
    case Nil{}:
      ft(h, {W.mem(W.sig(n0, es, x), W.sigs(n0, es, Nil{})) == True{} : Bool})
    case Con{+y, +t}:
      mso.go(R.end_eq(y, x), n0, es, x, y, t, {==}, h, h2 => mem_sigs_of(n0, es, x, t, h2))

def sub.go(c: Bool, +n0: Nat, +es: W.Peers, +x: R.End, +t: List<&2, R.End>, +Y: List<&2, R.End>, +q: W.Pt, he: {W.pt_eq(W.sig(n0, es, x), q) == c : Bool},
  hx: {R.end_mem(x, Y) == True{} : Bool}, hm: {(c || W.mem(q, W.sigs(n0, es, t))) == True{} : Bool},
  ih: {W.mem(q, W.sigs(n0, es, t)) == True{} : Bool} -> {W.mem(q, W.sigs(n0, es, Y)) == True{} : Bool}) -> {W.mem(q, W.sigs(n0, es, Y)) == True{} : Bool}:
  match c:
    case True{}:
      %pt_eqv(W.sig(n0, es, x), q, he) : {W.mem(_, W.sigs(n0, es, Y)) == True{} : Bool}
      mem_sigs_of(n0, es, x, Y, hx)
    case False{}:
      ih(hm)

# X's ends all in Y: X's placed ends are among Y's
def sigs_sub(+n0: Nat, +es: W.Peers, X: List<&2, R.End>, +Y: List<&2, R.End>, h: {R.all_in(X, Y) == True{} : Bool}, +q: W.Pt,
  hq: {W.mem(q, W.sigs(n0, es, X)) == True{} : Bool}) -> {W.mem(q, W.sigs(n0, es, Y)) == True{} : Bool}:
  match X:
    case Nil{}:
      ft(hq, {W.mem(q, W.sigs(n0, es, Y)) == True{} : Bool})
    case Con{+x, +t}:
      +h = h
      sub.go(W.pt_eq(W.sig(n0, es, x), q), n0, es, x, t, Y, q, {==}, and_l(R.end_mem(x, Y), R.all_in(t, Y), h), hq,
        h2 => sigs_sub(n0, es, t, Y, and_r(R.end_mem(x, Y), R.all_in(t, Y), h), q, h2))

def eeq_true(+x: R.End, +y: R.End, e: {x == y : R.End}) -> {R.end_eq(x, y) == True{} : Bool}:
  %e : {R.end_eq(x, _) == True{} : Bool}
  end_refl(x)

# z placed onto x, x onto y: z onto y; then z in t, a contradiction
def ij.c(c: Bool, +a: W.Pt, +b: W.Pt, +z: W.Pt, +T: List<&2, W.Pt>, he: {W.pt_eq(a, b) == c : Bool}, za: {z == a : W.Pt},
  hb: {W.mem(b, T) == True{} : Bool}, hz: {W.mem(z, T) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MNat.internal_false_ne_true(Equal.trans(Bool, False{}, W.mem(z, T), True{}, Equal.sym(Bool, W.mem(z, T), False{}, hz),
        mem_tr(z, b, T, Equal.trans(W.Pt, z, a, b, za, pt_eqv(a, b, he)), hb))))
    case False{}:
      {==}

def ij.c2(c: Bool, +a: W.Pt, +b: W.Pt, +z: W.Pt, +T: List<&2, W.Pt>, he: {W.pt_eq(a, b) == c : Bool}, zb: {z == b : W.Pt},
  ha: {W.mem(a, T) == True{} : Bool}, hz: {W.mem(z, T) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MNat.internal_false_ne_true(Equal.trans(Bool, False{}, W.mem(z, T), True{}, Equal.sym(Bool, W.mem(z, T), False{}, hz),
        mem_tr(z, a, T, Equal.trans(W.Pt, z, b, a, zb, Equal.sym(W.Pt, a, b, pt_eqv(a, b, he))), ha))))
    case False{}:
      {==}

def inj.go(cx: Bool, cy: Bool, +n0: Nat, +es: W.Peers, +x: R.End, +y: R.End, +z: R.End, +t: List<&2, R.End>,
  hex: {R.end_eq(z, x) == cx : Bool}, hey: {R.end_eq(z, y) == cy : Bool},
  hmx: {(cx || R.end_mem(x, t)) == True{} : Bool}, hmy: {(cy || R.end_mem(y, t)) == True{} : Bool},
  hz: {W.mem(W.sig(n0, es, z), W.sigs(n0, es, t)) == False{} : Bool}, hxy: {R.end_eq(x, y) == False{} : Bool},
  ih: {R.end_mem(x, t) == True{} : Bool} -> {R.end_mem(y, t) == True{} : Bool} -> {W.pt_eq(W.sig(n0, es, x), W.sig(n0, es, y)) == False{} : Bool}) ->
  {W.pt_eq(W.sig(n0, es, x), W.sig(n0, es, y)) == False{} : Bool}:
  match cx cy:
    case True{} True{}:
      Empty.absurd({W.pt_eq(W.sig(n0, es, x), W.sig(n0, es, y)) == False{} : Bool}, MNat.internal_false_ne_true(Equal.trans(Bool, False{}, R.end_eq(x, y), True{},
        Equal.sym(Bool, R.end_eq(x, y), False{}, hxy),
        eeq_true(x, y, Equal.trans(R.End, x, z, y, Equal.sym(R.End, z, x, end_eqv(z, x, hex)), end_eqv(z, y, hey))))))
    case True{} False{}:
      ij.c(W.pt_eq(W.sig(n0, es, x), W.sig(n0, es, y)), W.sig(n0, es, x), W.sig(n0, es, y), W.sig(n0, es, z), W.sigs(n0, es, t), {==},
        Equal.cong(R.End, W.Pt, (v => W.sig(n0, es, v)), z, x, end_eqv(z, x, hex)), mem_sigs_of(n0, es, y, t, hmy), hz)
    case False{} True{}:
      ij.c2(W.pt_eq(W.sig(n0, es, x), W.sig(n0, es, y)), W.sig(n0, es, x), W.sig(n0, es, y), W.sig(n0, es, z), W.sigs(n0, es, t), {==},
        Equal.cong(R.End, W.Pt, (v => W.sig(n0, es, v)), z, y, end_eqv(z, y, hey)), mem_sigs_of(n0, es, x, t, hmx), hz)
    case False{} False{}:
      ih(hmx)(hmy)

# placed ends no two alike: distinct ends of the list land apart
def inj(Xs: List<&2, R.End>, +n0: Nat, +es: W.Peers, +x: R.End, +y: R.End, hn: {W.nodup(W.sigs(n0, es, Xs)) == True{} : Bool},
  hx: {R.end_mem(x, Xs) == True{} : Bool}, hy: {R.end_mem(y, Xs) == True{} : Bool}, +hxy: {R.end_eq(x, y) == False{} : Bool}) ->
  {W.pt_eq(W.sig(n0, es, x), W.sig(n0, es, y)) == False{} : Bool}:
  match Xs:
    case Nil{}:
      ft(hx, {W.pt_eq(W.sig(n0, es, x), W.sig(n0, es, y)) == False{} : Bool})
    case Con{+z, +t}:
      +hn = hn
      inj.go(R.end_eq(z, x), R.end_eq(z, y), n0, es, x, y, z, t, {==}, {==}, hx, hy,
        not_true(W.mem(W.sig(n0, es, z), W.sigs(n0, es, t)), and_l(Bool.not(W.mem(W.sig(n0, es, z), W.sigs(n0, es, t))), W.nodup(W.sigs(n0, es, t)), hn)), hxy,
        h1 => h2 => inj(t, n0, es, x, y, and_r(Bool.not(W.mem(W.sig(n0, es, z), W.sigs(n0, es, t))), W.nodup(W.sigs(n0, es, t)), hn), h1, h2, hxy))

def pt_ne_new(y: W.Pt, +ks: List<&2, R.NodeKind>, +j: Nat, +p: Nat, hl: {W.live(ks, y) == True{} : Bool}) ->
  {W.pt_eq(y, W.Pt{Nat.add(List.length(&2, R.NodeKind, ks), j), p}) == False{} : Bool}:
  match y:
    case W.Pt{+m, +q}:
      and_fl(R.nat_eq(m, Nat.add(List.length(&2, R.NodeKind, ks), j)), R.nat_eq(q, p), below_ne_add(List.length(&2, R.NodeKind, ks), m, j, live_range(ks, m, q, hl)))

def pt_ne_new2(y: W.Pt, +ks: List<&2, R.NodeKind>, +j: Nat, +p: Nat, hl: {W.live(ks, y) == True{} : Bool}) ->
  {W.pt_eq(W.Pt{Nat.add(List.length(&2, R.NodeKind, ks), j), p}, y) == False{} : Bool}:
  match y:
    case W.Pt{+m, +q}:
      and_fl(R.nat_eq(Nat.add(List.length(&2, R.NodeKind, ks), j), m), R.nat_eq(p, q),
        Equal.trans(Bool, R.nat_eq(Nat.add(List.length(&2, R.NodeKind, ks), j), m), R.nat_eq(m, Nat.add(List.length(&2, R.NodeKind, ks), j)), False{},
          neq_comm(Nat.add(List.length(&2, R.NodeKind, ks), j), m), below_ne_add(List.length(&2, R.NodeKind, ks), m, j, live_range(ks, m, q, hl))))

def ext_in_X.go(c: Bool, +i: Nat, +ka: R.NodeKind, +kb: R.NodeKind, +xs: List<&2, R.Spec>, he: {R.end_mem(R.Ext{i}, W.aux_a(ka)) == c : Bool},
  h: {(c || R.end_mem(R.Ext{i}, List.append(&2, R.End, W.aux_b(kb), R.new_ends(xs, 0n)))) == True{} : Bool}) -> {R.end_mem(R.Ext{i}, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb))) == True{} : Bool}:
  match c:
    case True{}:
      emem_il(R.Ext{i}, W.aux_a(ka), W.aux_b(kb), he)
    case False{}:
      emem_ir(R.Ext{i}, W.aux_a(ka), W.aux_b(kb), emem_left(R.Ext{i}, W.aux_b(kb), R.new_ends(xs, 0n), h, new_no_ext(i, xs, 0n)))

# an Ext end the rule must link is a peer of the pair
def ext_in_X(+i: Nat, +ka: R.NodeKind, +kb: R.NodeKind, +xs: List<&2, R.Spec>, h: {R.end_mem(R.Ext{i}, R.expected(ka, kb, xs)) == True{} : Bool}) -> {R.end_mem(R.Ext{i}, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb))) == True{} : Bool}:
  ext_in_X.go(R.end_mem(R.Ext{i}, W.aux_a(ka)), i, ka, kb, xs, {==}, emem_or(R.Ext{i}, W.aux_a(ka), List.append(&2, R.End, W.aux_b(kb), R.new_ends(xs, 0n)), h))

# a New end the rule must link is in its new ends
def new_in_new(+j: Nat, +p: Nat, +ka: R.NodeKind, +kb: R.NodeKind, +xs: List<&2, R.Spec>, h: {R.end_mem(R.New{j, p}, R.expected(ka, kb, xs)) == True{} : Bool}) -> {R.end_mem(R.New{j, p}, R.new_ends(xs, 0n)) == True{} : Bool}:
  or_res(R.end_mem(R.New{j, p}, W.aux_b(kb)), R.end_mem(R.New{j, p}, R.new_ends(xs, 0n)),
    emem_or(R.New{j, p}, W.aux_b(kb), R.new_ends(xs, 0n),
      or_res(R.end_mem(R.New{j, p}, W.aux_a(ka)), R.end_mem(R.New{j, p}, List.append(&2, R.End, W.aux_b(kb), R.new_ends(xs, 0n))),
        emem_or(R.New{j, p}, W.aux_a(ka), List.append(&2, R.End, W.aux_b(kb), R.new_ends(xs, 0n)), h),
        aux_no_new(j, p, Nat.sub(R.arity(ka), 1n), 0n))),
    aux_no_new(j, p, Nat.sub(R.arity(kb), 1n), 2n))

def rf.ext(c: Bool, +i: Nat, +k: Nat, +ks: List<&2, R.NodeKind>, +es: W.Peers, +ka: R.NodeKind, +kb: R.NodeKind, +xs: List<&2, R.Spec>, +hX: {W.nodup(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb)))) == True{} : Bool}, +hL: {W.all_live(ks, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb)))) == True{} : Bool}, he: {R.nat_eq(i, k) == c : Bool},
  hx: {R.end_mem(R.Ext{i}, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb))) == True{} : Bool}, hy: {R.end_mem(R.Ext{k}, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb))) == True{} : Bool}) ->
  {W.pt_eq(W.sig(List.length(&2, R.NodeKind, ks), es, R.Ext{i}), W.sig(List.length(&2, R.NodeKind, ks), es, R.Ext{k})) == c : Bool}:
  match c:
    case True{}:
      %neq_eq(i, k, he) : {W.pt_eq(W.sig(List.length(&2, R.NodeKind, ks), es, R.Ext{i}), W.sig(List.length(&2, R.NodeKind, ks), es, R.Ext{_})) == True{} : Bool}
      pt_refl(W.sig(List.length(&2, R.NodeKind, ks), es, R.Ext{i}))
    case False{}:
      inj(List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb)), List.length(&2, R.NodeKind, ks), es, R.Ext{i}, R.Ext{k}, hX, hx, hy, he)

# the placement keeps the rule's ends apart: equal exactly when the ends are
def reflect(x: R.End, y: R.End, +ks: List<&2, R.NodeKind>, +es: W.Peers, +ka: R.NodeKind, +kb: R.NodeKind, +xs: List<&2, R.Spec>, +hX: {W.nodup(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb)))) == True{} : Bool}, +hL: {W.all_live(ks, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb)))) == True{} : Bool}, hx: {R.end_mem(x, R.expected(ka, kb, xs)) == True{} : Bool}, hy: {R.end_mem(y, R.expected(ka, kb, xs)) == True{} : Bool}) ->
  {W.pt_eq(W.sig(List.length(&2, R.NodeKind, ks), es, x), W.sig(List.length(&2, R.NodeKind, ks), es, y)) == R.end_eq(x, y) : Bool}:
  match x y:
    case R.Ext{+i} R.Ext{+k}:
      rf.ext(R.nat_eq(i, k), i, k, ks, es, ka, kb, xs, hX, hL, {==}, ext_in_X(i, ka, kb, xs, hx), ext_in_X(k, ka, kb, xs, hy))
    case R.Ext{+i} R.New{+j, +p}:
      pt_ne_new(W.sig(List.length(&2, R.NodeKind, ks), es, R.Ext{i}), ks, j, p, live_at(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb))), ks, W.sig(List.length(&2, R.NodeKind, ks), es, R.Ext{i}), hL, mem_sigs_of(List.length(&2, R.NodeKind, ks), es, R.Ext{i}, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb)), ext_in_X(i, ka, kb, xs, hx))))
    case R.New{+j, +p} R.Ext{+i}:
      pt_ne_new2(W.sig(List.length(&2, R.NodeKind, ks), es, R.Ext{i}), ks, j, p, live_at(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb))), ks, W.sig(List.length(&2, R.NodeKind, ks), es, R.Ext{i}), hL, mem_sigs_of(List.length(&2, R.NodeKind, ks), es, R.Ext{i}, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb)), ext_in_X(i, ka, kb, xs, hy))))
    case R.New{+j, +p} R.New{+j2, +p2}:
      %Equal.sym(Bool, R.nat_eq(Nat.add(List.length(&2, R.NodeKind, ks), j), Nat.add(List.length(&2, R.NodeKind, ks), j2)), R.nat_eq(j, j2), neq_add(List.length(&2, R.NodeKind, ks), j, j2)) : {(_ && R.nat_eq(p, p2)) == (R.nat_eq(j, j2) && R.nat_eq(p, p2)) : Bool}
      {==}

def msi(+x: R.End, t: List<&2, R.End>, +ks: List<&2, R.NodeKind>, +es: W.Peers, +ka: R.NodeKind, +kb: R.NodeKind, +xs: List<&2, R.Spec>, +hX: {W.nodup(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb)))) == True{} : Bool}, +hL: {W.all_live(ks, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb)))) == True{} : Bool}, +hx: {R.end_mem(x, R.expected(ka, kb, xs)) == True{} : Bool}, ht: {R.all_in(t, R.expected(ka, kb, xs)) == True{} : Bool}) ->
  {W.mem(W.sig(List.length(&2, R.NodeKind, ks), es, x), W.sigs(List.length(&2, R.NodeKind, ks), es, t)) == R.end_mem(x, t) : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      +ht = ht
      %Equal.sym(Bool, W.pt_eq(W.sig(List.length(&2, R.NodeKind, ks), es, y), W.sig(List.length(&2, R.NodeKind, ks), es, x)), R.end_eq(y, x), reflect(y, x, ks, es, ka, kb, xs, hX, hL, and_l(R.end_mem(y, R.expected(ka, kb, xs)), R.all_in(r, R.expected(ka, kb, xs)), ht), hx)) : {(_ || W.mem(W.sig(List.length(&2, R.NodeKind, ks), es, x), W.sigs(List.length(&2, R.NodeKind, ks), es, r))) == (R.end_eq(y, x) || R.end_mem(x, r)) : Bool}
      %Equal.sym(Bool, W.mem(W.sig(List.length(&2, R.NodeKind, ks), es, x), W.sigs(List.length(&2, R.NodeKind, ks), es, r)), R.end_mem(x, r), msi(x, r, ks, es, ka, kb, xs, hX, hL, hx, and_r(R.end_mem(y, R.expected(ka, kb, xs)), R.all_in(r, R.expected(ka, kb, xs)), ht))) : {(R.end_eq(y, x) || _) == (R.end_eq(y, x) || R.end_mem(x, r)) : Bool}
      {==}

# the rule's ends placed: no port twice
def nodup_sigs(Xs: List<&2, R.End>, +ks: List<&2, R.NodeKind>, +es: W.Peers, +ka: R.NodeKind, +kb: R.NodeKind, +xs: List<&2, R.Spec>, +hX: {W.nodup(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb)))) == True{} : Bool}, +hL: {W.all_live(ks, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb)))) == True{} : Bool}, hin: {R.all_in(Xs, R.expected(ka, kb, xs)) == True{} : Bool}, hd: {R.ends_distinct(Xs) == True{} : Bool}) ->
  {W.nodup(W.sigs(List.length(&2, R.NodeKind, ks), es, Xs)) == True{} : Bool}:
  match Xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hin = hin
      +hd = hd
      %Equal.sym(Bool, W.mem(W.sig(List.length(&2, R.NodeKind, ks), es, x), W.sigs(List.length(&2, R.NodeKind, ks), es, t)), R.end_mem(x, t), msi(x, t, ks, es, ka, kb, xs, hX, hL, and_l(R.end_mem(x, R.expected(ka, kb, xs)), R.all_in(t, R.expected(ka, kb, xs)), hin), and_r(R.end_mem(x, R.expected(ka, kb, xs)), R.all_in(t, R.expected(ka, kb, xs)), hin))) : {(Bool.not(_) && W.nodup(W.sigs(List.length(&2, R.NodeKind, ks), es, t))) == True{} : Bool}
      and_i(Bool.not(R.end_mem(x, t)), W.nodup(W.sigs(List.length(&2, R.NodeKind, ks), es, t)), and_l(Bool.not(R.end_mem(x, t)), R.ends_distinct(t), hd),
        nodup_sigs(t, ks, es, ka, kb, xs, hX, hL, and_r(R.end_mem(x, R.expected(ka, kb, xs)), R.all_in(t, R.expected(ka, kb, xs)), hin), and_r(Bool.not(R.end_mem(x, t)), R.ends_distinct(t), hd)))

# Transports: the peers placed as one list
def to_ex_nodup(+n0: Nat, +es: W.Peers, +xa: List<&2, R.End>, +xb: List<&2, R.End>, +C: List<&2, W.Pt>,
  h: {W.nodup(List.append(&2, W.Pt, W.sigs(n0, es, xa), List.append(&2, W.Pt, W.sigs(n0, es, xb), C))) == True{} : Bool}) ->
  {W.nodup(List.append(&2, W.Pt, W.sigs(n0, es, List.append(&2, R.End, xa, xb)), C)) == True{} : Bool}:
  %Equal.sym(List<&2, W.Pt>, W.sigs(n0, es, List.append(&2, R.End, xa, xb)), List.append(&2, W.Pt, W.sigs(n0, es, xa), W.sigs(n0, es, xb)), sigs_app(n0, es, xa, xb)) : {W.nodup(List.append(&2, W.Pt, _, C)) == True{} : Bool}
  %Equal.sym(List<&2, W.Pt>, List.append(&2, W.Pt, List.append(&2, W.Pt, W.sigs(n0, es, xa), W.sigs(n0, es, xb)), C), List.append(&2, W.Pt, W.sigs(n0, es, xa), List.append(&2, W.Pt, W.sigs(n0, es, xb), C)), app_assoc(W.sigs(n0, es, xa), W.sigs(n0, es, xb), C)) : {W.nodup(_) == True{} : Bool}
  h

def to_ex_live(+ks: List<&2, R.NodeKind>, +n0: Nat, +es: W.Peers, +xa: List<&2, R.End>, +xb: List<&2, R.End>, +C: List<&2, W.Pt>,
  h: {W.all_live(ks, List.append(&2, W.Pt, W.sigs(n0, es, xa), List.append(&2, W.Pt, W.sigs(n0, es, xb), C))) == True{} : Bool}) ->
  {W.all_live(ks, List.append(&2, W.Pt, W.sigs(n0, es, List.append(&2, R.End, xa, xb)), C)) == True{} : Bool}:
  %Equal.sym(List<&2, W.Pt>, W.sigs(n0, es, List.append(&2, R.End, xa, xb)), List.append(&2, W.Pt, W.sigs(n0, es, xa), W.sigs(n0, es, xb)), sigs_app(n0, es, xa, xb)) : {W.all_live(ks, List.append(&2, W.Pt, _, C)) == True{} : Bool}
  %Equal.sym(List<&2, W.Pt>, List.append(&2, W.Pt, List.append(&2, W.Pt, W.sigs(n0, es, xa), W.sigs(n0, es, xb)), C), List.append(&2, W.Pt, W.sigs(n0, es, xa), List.append(&2, W.Pt, W.sigs(n0, es, xb), C)), app_assoc(W.sigs(n0, es, xa), W.sigs(n0, es, xb), C)) : {W.all_live(ks, _) == True{} : Bool}
  h

def to_ex_out(+n0: Nat, +es: W.Peers, +xa: List<&2, R.End>, +xb: List<&2, R.End>, +C: List<&2, W.Pt>, +Z: List<&2, W.Pt>,
  h: {all_out(List.append(&2, W.Pt, W.sigs(n0, es, xa), List.append(&2, W.Pt, W.sigs(n0, es, xb), C)), Z) == True{} : Bool}) ->
  {all_out(List.append(&2, W.Pt, W.sigs(n0, es, List.append(&2, R.End, xa, xb)), C), Z) == True{} : Bool}:
  %Equal.sym(List<&2, W.Pt>, W.sigs(n0, es, List.append(&2, R.End, xa, xb)), List.append(&2, W.Pt, W.sigs(n0, es, xa), W.sigs(n0, es, xb)), sigs_app(n0, es, xa, xb)) : {all_out(List.append(&2, W.Pt, _, C), Z) == True{} : Bool}
  %Equal.sym(List<&2, W.Pt>, List.append(&2, W.Pt, List.append(&2, W.Pt, W.sigs(n0, es, xa), W.sigs(n0, es, xb)), C), List.append(&2, W.Pt, W.sigs(n0, es, xa), List.append(&2, W.Pt, W.sigs(n0, es, xb), C)), app_assoc(W.sigs(n0, es, xa), W.sigs(n0, es, xb), C)) : {all_out(_, Z) == True{} : Bool}
  h

def to_ex_mem(+n0: Nat, +es: W.Peers, +xa: List<&2, R.End>, +xb: List<&2, R.End>, +C: List<&2, W.Pt>, +q: W.Pt,
  h: {W.mem(q, List.append(&2, W.Pt, W.sigs(n0, es, xa), List.append(&2, W.Pt, W.sigs(n0, es, xb), C))) == True{} : Bool}) ->
  {W.mem(q, List.append(&2, W.Pt, W.sigs(n0, es, List.append(&2, R.End, xa, xb)), C)) == True{} : Bool}:
  %Equal.sym(List<&2, W.Pt>, W.sigs(n0, es, List.append(&2, R.End, xa, xb)), List.append(&2, W.Pt, W.sigs(n0, es, xa), W.sigs(n0, es, xb)), sigs_app(n0, es, xa, xb)) : {W.mem(q, List.append(&2, W.Pt, _, C)) == True{} : Bool}
  %Equal.sym(List<&2, W.Pt>, List.append(&2, W.Pt, List.append(&2, W.Pt, W.sigs(n0, es, xa), W.sigs(n0, es, xb)), C), List.append(&2, W.Pt, W.sigs(n0, es, xa), List.append(&2, W.Pt, W.sigs(n0, es, xb), C)), app_assoc(W.sigs(n0, es, xa), W.sigs(n0, es, xb), C)) : {W.mem(q, _) == True{} : Bool}
  h

def in_cat(A: List<&2, R.End>, +B: List<&2, R.End>, +Z: List<&2, R.End>, hA: {R.all_in(A, Z) == True{} : Bool}, +hB: {R.all_in(B, Z) == True{} : Bool}) ->
  {R.all_in(List.append(&2, R.End, A, B), Z) == True{} : Bool}:
  match A:
    case Nil{}:
      hB
    case Con{+x, +t}:
      +hA = hA
      and_i(R.end_mem(x, Z), R.all_in(List.append(&2, R.End, t, B), Z), and_l(R.end_mem(x, Z), R.all_in(t, Z), hA),
        in_cat(t, B, Z, and_r(R.end_mem(x, Z), R.all_in(t, Z), hA), hB))

# the peers' ends are ends the rule must link
def x_in_v(+ka: R.NodeKind, +kb: R.NodeKind, +xs: List<&2, R.Spec>) -> {R.all_in(List.append(&2, R.End, W.aux_a(ka), W.aux_b(kb)), R.expected(ka, kb, xs)) == True{} : Bool}:
  in_cat(W.aux_a(ka), W.aux_b(kb), R.expected(ka, kb, xs), in_app_l(W.aux_a(ka), List.append(&2, R.End, W.aux_b(kb), R.new_ends(xs, 0n))),
    in_trans(W.aux_b(kb), List.append(&2, R.End, W.aux_b(kb), R.new_ends(xs, 0n)), R.expected(ka, kb, xs), in_app_l(W.aux_b(kb), R.new_ends(xs, 0n)),
      in_app_r(W.aux_a(ka), List.append(&2, R.End, W.aux_b(kb), R.new_ends(xs, 0n)))))

def is_new(x: R.End) -> Bool:
  match x:
    case R.Ext{i}:
      False{}
    case R.New{j, p}:
      True{}

def all_new(xs: List<&2, R.End>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      is_new(x) && all_new(t)

def new_cat(A: List<&2, R.End>, +B: List<&2, R.End>, hA: {all_new(A) == True{} : Bool}, +hB: {all_new(B) == True{} : Bool}) -> {all_new(List.append(&2, R.End, A, B)) == True{} : Bool}:
  match A:
    case Nil{}:
      hB
    case Con{+x, +t}:
      +hA = hA
      and_i(is_new(x), all_new(List.append(&2, R.End, t, B)), and_l(is_new(x), all_new(t), hA), new_cat(t, B, and_r(is_new(x), all_new(t), hA), hB))

def node_new(+j: Nat, n: Nat, +p: Nat) -> {all_new(R.node_ends(j, n, p)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+q:
      node_new(j, q, 1n+p)

def news_new(xs: List<&2, R.Spec>, +j: Nat) -> {all_new(R.new_ends(xs, j)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{R.Spec{+k, s}, +t}:
      new_cat(R.node_ends(j, R.arity(k), 0n), R.new_ends(t, 1n+j), node_new(j, R.arity(k), 0n), news_new(t, 1n+j))

# a live port is no new node's
def far(Y: List<&2, R.End>, +ks: List<&2, R.NodeKind>, +es: W.Peers, +x: W.Pt, hy: {all_new(Y) == True{} : Bool}, +hl: {W.live(ks, x) == True{} : Bool}) ->
  {W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, Y)) == False{} : Bool}:
  match Y:
    case Nil{}:
      {==}
    case Con{R.Ext{i}, t}:
      ft(hy, {W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, Con{R.Ext{i}, t})) == False{} : Bool})
    case Con{R.New{+j, +p}, +t}:
      or_f(W.pt_eq(W.Pt{Nat.add(List.length(&2, R.NodeKind, ks), j), p}, x), W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, t)), pt_ne_new2(x, ks, j, p, hl), far(t, ks, es, x, hy, hl))

# Kinds after the rewrite
def len_k1(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat) -> {List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})) == List.length(&2, R.NodeKind, ks) : Nat}:
  Equal.trans(Nat, List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), List.length(&2, R.NodeKind, W.set(ks, a, R.KFree{})), List.length(&2, R.NodeKind, ks), klen_set(W.set(ks, a, R.KFree{}), b, R.KFree{}), klen_set(ks, a, R.KFree{}))

def rng(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +m: Nat, h: {W.below(m, List.length(&2, R.NodeKind, ks)) == True{} : Bool}) -> {W.below(m, List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), List.length(&2, R.NodeKind, ks), len_k1(ks, a, b)) : {W.below(m, _) == True{} : Bool}
  h

def rng_back(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +m: Nat, h: {W.below(m, List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}))) == True{} : Bool}) -> {W.below(m, List.length(&2, R.NodeKind, ks)) == True{} : Bool}:
  %len_k1(ks, a, b) : {W.below(m, _) == True{} : Bool}
  h

def kl.below(+ks: List<&2, R.NodeKind>, +a: Nat, +m: Nat, +p: Nat, eq: {a == m : Nat}, hl: {W.below(p, R.arity(W.kind_at(ks, m))) == True{} : Bool}) ->
  {W.below(p, R.arity(W.kind_at(ks, a))) == True{} : Bool}:
  %Equal.sym(Nat, a, m, eq) : {W.below(p, R.arity(W.kind_at(ks, _))) == True{} : Bool}
  hl

def kl.mem(+ks: List<&2, R.NodeKind>, +a: Nat, +m: Nat, +p: Nat, +eq: {a == m : Nat}, hl: {W.below(p, R.arity(W.kind_at(ks, m))) == True{} : Bool}) ->
  {W.mem(W.Pt{m, p}, W.ports(a, R.arity(W.kind_at(ks, a)))) == True{} : Bool}:
  %eq : {W.mem(W.Pt{_, p}, W.ports(a, R.arity(W.kind_at(ks, a)))) == True{} : Bool}
  ports_has(a, R.arity(W.kind_at(ks, a)), p, kl.below(ks, a, m, p, eq, hl))

# a live port off the pair's ports is not the pair's
def kl.ne(c: Bool, +ks: List<&2, R.NodeKind>, +a: Nat, +m: Nat, +p: Nat, he: {R.nat_eq(a, m) == c : Bool},
  hl: {W.below(p, R.arity(W.kind_at(ks, m))) == True{} : Bool}, hA: {W.mem(W.Pt{m, p}, W.ports(a, R.arity(W.kind_at(ks, a)))) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MNat.internal_false_ne_true(Equal.trans(Bool, False{}, W.mem(W.Pt{m, p}, W.ports(a, R.arity(W.kind_at(ks, a)))), True{},
        Equal.sym(Bool, W.mem(W.Pt{m, p}, W.ports(a, R.arity(W.kind_at(ks, a)))), False{}, hA), kl.mem(ks, a, m, p, neq_eq(a, m, he), hl))))
    case False{}:
      {==}

def keep.go(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +xs: List<&2, R.Spec>, +m: Nat, +p: Nat, hl: {W.below(p, R.arity(W.kind_at(ks, m))) == True{} : Bool},
  hma: {R.nat_eq(a, m) == False{} : Bool}, hmb: {R.nat_eq(b, m) == False{} : Bool}, hr: {W.below(m, List.length(&2, R.NodeKind, ks)) == True{} : Bool}) ->
  {W.below(p, R.arity(W.kind_at(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), m))) == True{} : Bool}:
  %Equal.sym(R.NodeKind, W.kind_at(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), m), W.kind_at(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), m), ka_lt(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs), m, rng(ks, a, b, m, hr))) : {W.below(p, R.arity(_)) == True{} : Bool}
  %Equal.sym(R.NodeKind, W.kind_at(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), m), W.kind_at(W.set(ks, a, R.KFree{}), m), ka_ne(W.set(ks, a, R.KFree{}), b, R.KFree{}, m, hmb)) : {W.below(p, R.arity(_)) == True{} : Bool}
  %Equal.sym(R.NodeKind, W.kind_at(W.set(ks, a, R.KFree{}), m), W.kind_at(ks, m), ka_ne(ks, a, R.KFree{}, m, hma)) : {W.below(p, R.arity(_)) == True{} : Bool}
  hl

# a live port off the pair's ports stays live
def keep(q: W.Pt, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +xs: List<&2, R.Spec>, hl: {W.live(ks, q) == True{} : Bool},
  hA: {W.mem(q, W.ports(a, R.arity(W.kind_at(ks, a)))) == False{} : Bool}, hB: {W.mem(q, W.ports(b, R.arity(W.kind_at(ks, b)))) == False{} : Bool}) -> {W.live(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), q) == True{} : Bool}:
  match q:
    case W.Pt{+m, +p}:
      +hl = hl
      keep.go(ks, a, b, xs, m, p, hl, kl.ne(R.nat_eq(a, m), ks, a, m, p, {==}, hl, hA), kl.ne(R.nat_eq(b, m), ks, b, m, p, {==}, hl, hB), live_range(ks, m, p, hl))

def live_new(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +xs: List<&2, R.Spec>, +j: Nat, +p: Nat, h: {W.below(p, R.arity(W.kind_at(W.kinds(xs), j))) == True{} : Bool}) ->
  {W.live(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.Pt{Nat.add(List.length(&2, R.NodeKind, ks), j), p}) == True{} : Bool}:
  %len_k1(ks, a, b) : {W.below(p, R.arity(W.kind_at(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), Nat.add(_, j)))) == True{} : Bool}
  %Equal.sym(R.NodeKind, W.kind_at(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), j)), W.kind_at(W.kinds(xs), j), ka_off(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs), j)) : {W.below(p, R.arity(_)) == True{} : Bool}
  h

def mem_or(+q: W.Pt, +A: List<&2, W.Pt>, +B: List<&2, W.Pt>, h: {W.mem(q, List.append(&2, W.Pt, A, B)) == True{} : Bool}) -> {(W.mem(q, A) || W.mem(q, B)) == True{} : Bool}:
  Equal.trans(Bool, (W.mem(q, A) || W.mem(q, B)), W.mem(q, List.append(&2, W.Pt, A, B)), True{}, Equal.sym(Bool, W.mem(q, List.append(&2, W.Pt, A, B)), (W.mem(q, A) || W.mem(q, B)), mem_app(q, A, B)), h)

# The old net's facts, from wired
def d_nec(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}) -> {W.nodup(List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c))) == True{} : Bool}:
  to_ex_nodup(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)), W.ends(c), nodup_r(W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c))),
    nodup_r(W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))), hn)))

def d_lec(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}) -> {W.all_live(ks, List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c))) == True{} : Bool}:
  to_ex_live(ks, List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)), W.ends(c), live_r(ks, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c))),
    live_r(ks, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))), hl)))

def d_oa(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}) -> {all_out(List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c)), W.ports(a, R.arity(W.kind_at(ks, a)))) == True{} : Bool}:
  to_ex_out(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)), W.ends(c), W.ports(a, R.arity(W.kind_at(ks, a))), out_snd(W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c))), W.ports(a, R.arity(W.kind_at(ks, a))),
    out_sym(W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))),
      nodup_out(W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))), hn))))

def d_ob(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}) -> {all_out(List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c)), W.ports(b, R.arity(W.kind_at(ks, b)))) == True{} : Bool}:
  to_ex_out(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)), W.ends(c), W.ports(b, R.arity(W.kind_at(ks, b))), out_sym(W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c))),
    nodup_out(W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c))),
      nodup_r(W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))), hn))))

def d_xl(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}) -> {R.all_in(List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b))), R.ends(ls)) == True{} : Bool}:
  in_trans(List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b))), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls), x_in_v(W.kind_at(ks, a), W.kind_at(ks, b), xs), hall)

# Goal one: no port twice
def ex_split(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +x: W.Pt, hox: {W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b))))) == False{} : Bool}) -> {W.mem(x, List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))))) == False{} : Bool}:
  %sigs_app(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b))) : {W.mem(x, _) == False{} : Bool}
  hox

def not_in_v(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +x: W.Pt, hlx: {W.live(ks, x) == True{} : Bool}, hox: {W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b))))) == False{} : Bool}) -> {W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs))) == False{} : Bool}:
  %Equal.sym(List<&2, W.Pt>, W.sigs(List.length(&2, R.NodeKind, ks), es, R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_b(W.kind_at(ks, b)), R.new_ends(xs, 0n)))),
    sigs_app(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a)), List.append(&2, R.End, W.aux_b(W.kind_at(ks, b)), R.new_ends(xs, 0n)))) : {W.mem(x, _) == False{} : Bool}
  %Equal.sym(List<&2, W.Pt>, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_b(W.kind_at(ks, b)), R.new_ends(xs, 0n))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.sigs(List.length(&2, R.NodeKind, ks), es, R.new_ends(xs, 0n))),
    sigs_app(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b)), R.new_ends(xs, 0n))) : {W.mem(x, List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), _)) == False{} : Bool}
  +hs = ex_split(ks, a, b, es, c, xs, ls, x, hox)
  mem_ff(x, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.sigs(List.length(&2, R.NodeKind, ks), es, R.new_ends(xs, 0n))), mem_fl(x, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), hs),
    mem_ff(x, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.sigs(List.length(&2, R.NodeKind, ks), es, R.new_ends(xs, 0n)), mem_fr(x, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), hs), far(R.new_ends(xs, 0n), ks, es, x, news_new(xs, 0n), hlx)))

def cn.go(cm: Bool, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, +x: W.Pt, he: {W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls))) == cm : Bool}, hno: {W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs))) == False{} : Bool}) -> {cm == False{} : Bool}:
  match cm:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MNat.internal_false_ne_true(Equal.trans(Bool, False{}, W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs))), True{},
        Equal.sym(Bool, W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs))), False{}, hno), sigs_sub(List.length(&2, R.NodeKind, ks), es, R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), hin, x, he))))
    case False{}:
      {==}

def c_out_n(C2: List<&2, W.Pt>, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, hl2: {W.all_live(ks, C2) == True{} : Bool}, ho: {all_out(C2, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b))))) == True{} : Bool}) -> {all_out(C2, W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls))) == True{} : Bool}:
  match C2:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hl2 = hl2
      +ho = ho
      and_i(Bool.not(W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))), all_out(t, W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls))),
        not_false(W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls))), cn.go(W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls))), ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, x, {==},
          not_in_v(ks, a, b, es, c, xs, ls, x, and_l(W.live(ks, x), W.all_live(ks, t), hl2), not_true(W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b))))), and_l(Bool.not(W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))))), all_out(t, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b))))), ho))))),
        c_out_n(t, ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, and_r(W.live(ks, x), W.all_live(ks, t), hl2), and_r(Bool.not(W.mem(x, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))))), all_out(t, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b))))), ho)))

def g_nodup(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}) -> {W.nodup(List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}:
  +nec = d_nec(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall)
  nodup_cat(W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)), nodup_r(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c), nec),
    nodup_sigs(R.ends(ls), ks, es, W.kind_at(ks, a), W.kind_at(ks, b), xs, nodup_l(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c), nec), live_l(ks, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c), d_lec(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall)), hin, hd),
    c_out_n(W.ends(c), ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, live_r(ks, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c), d_lec(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall)), out_sym(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c), nodup_out(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c), nec))))

# Goal two: every end live
def live_c(C2: List<&2, W.Pt>, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, hl2: {W.all_live(ks, C2) == True{} : Bool}, oa: {all_out(C2, W.ports(a, R.arity(W.kind_at(ks, a)))) == True{} : Bool}, ob: {all_out(C2, W.ports(b, R.arity(W.kind_at(ks, b)))) == True{} : Bool}) ->
  {W.all_live(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), C2) == True{} : Bool}:
  match C2:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hl2 = hl2
      +oa = oa
      +ob = ob
      and_i(W.live(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), x), W.all_live(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), t),
        keep(x, ks, a, b, xs, and_l(W.live(ks, x), W.all_live(ks, t), hl2), not_true(W.mem(x, W.ports(a, R.arity(W.kind_at(ks, a)))), and_l(Bool.not(W.mem(x, W.ports(a, R.arity(W.kind_at(ks, a))))), all_out(t, W.ports(a, R.arity(W.kind_at(ks, a)))), oa)),
          not_true(W.mem(x, W.ports(b, R.arity(W.kind_at(ks, b)))), and_l(Bool.not(W.mem(x, W.ports(b, R.arity(W.kind_at(ks, b))))), all_out(t, W.ports(b, R.arity(W.kind_at(ks, b)))), ob))),
        live_c(t, ks, a, b, es, c, xs, ls, and_r(W.live(ks, x), W.all_live(ks, t), hl2), and_r(Bool.not(W.mem(x, W.ports(a, R.arity(W.kind_at(ks, a))))), all_out(t, W.ports(a, R.arity(W.kind_at(ks, a)))), oa), and_r(Bool.not(W.mem(x, W.ports(b, R.arity(W.kind_at(ks, b))))), all_out(t, W.ports(b, R.arity(W.kind_at(ks, b)))), ob)))

def live_one(x: R.End, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, hx: {R.end_mem(x, R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}) -> {W.live(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.sig(List.length(&2, R.NodeKind, ks), es, x)) == True{} : Bool}:
  match x:
    case R.Ext{+i}:
      +hq = mem_sigs_of(List.length(&2, R.NodeKind, ks), es, R.Ext{i}, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b))), ext_in_X(i, W.kind_at(ks, a), W.kind_at(ks, b), xs, hx))
      keep(W.sig(List.length(&2, R.NodeKind, ks), es, R.Ext{i}), ks, a, b, xs, live_at(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), ks, W.sig(List.length(&2, R.NodeKind, ks), es, R.Ext{i}), live_l(ks, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c), d_lec(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall)), hq),
        out_at(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ports(a, R.arity(W.kind_at(ks, a))), W.sig(List.length(&2, R.NodeKind, ks), es, R.Ext{i}), out_fst(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c), W.ports(a, R.arity(W.kind_at(ks, a))), d_oa(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall)), hq),
        out_at(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ports(b, R.arity(W.kind_at(ks, b))), W.sig(List.length(&2, R.NodeKind, ks), es, R.Ext{i}), out_fst(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c), W.ports(b, R.arity(W.kind_at(ks, b))), d_ob(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall)), hq))
    case R.New{+j, +p}:
      live_new(ks, a, b, xs, j, p, new_live(xs, 0n, j, p, new_in_new(j, p, W.kind_at(ks, a), W.kind_at(ks, b), xs, hx)))

def live_n(Xs: List<&2, R.End>, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, h: {R.all_in(Xs, R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}) -> {W.all_live(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.sigs(List.length(&2, R.NodeKind, ks), es, Xs)) == True{} : Bool}:
  match Xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h = h
      and_i(W.live(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.sig(List.length(&2, R.NodeKind, ks), es, x)), W.all_live(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.sigs(List.length(&2, R.NodeKind, ks), es, t)),
        live_one(x, ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, and_l(R.end_mem(x, R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)), R.all_in(t, R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)), h)), live_n(t, ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, and_r(R.end_mem(x, R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)), R.all_in(t, R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)), h)))

def g_live(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}) -> {W.all_live(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}:
  live_cat(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)), live_c(W.ends(c), ks, a, b, es, c, xs, ls, live_r(ks, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c), d_lec(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall)), out_snd(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c), W.ports(a, R.arity(W.kind_at(ks, a))), d_oa(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall)), out_snd(W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c), W.ports(b, R.arity(W.kind_at(ks, b))), d_ob(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall))),
    live_n(R.ends(ls), ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, hin))

# Goal three: every live port present
def cov_at.go(c: Bool, +ks: List<&2, R.NodeKind>, +P: List<&2, W.Pt>, +k: Nat, +m: Nat, he: {R.nat_eq(k, m) == c : Bool},
  hh: {W.ports_in(k, R.arity(W.kind_at(ks, k)), P) == True{} : Bool}, hm: {W.below(m, 1n+k) == True{} : Bool},
  ih: {W.below(m, k) == True{} : Bool} -> {W.ports_in(m, R.arity(W.kind_at(ks, m)), P) == True{} : Bool}) -> {W.ports_in(m, R.arity(W.kind_at(ks, m)), P) == True{} : Bool}:
  match c:
    case True{}:
      %neq_eq(k, m, he) : {W.ports_in(_, R.arity(W.kind_at(ks, _)), P) == True{} : Bool}
      hh
    case False{}:
      ih(below_pred(k, m, hm, he))

def cov_at(+ks: List<&2, R.NodeKind>, n: Nat, +P: List<&2, W.Pt>, +m: Nat, hm: {W.below(m, n) == True{} : Bool}, h: {W.covered(ks, n, P) == True{} : Bool}) ->
  {W.ports_in(m, R.arity(W.kind_at(ks, m)), P) == True{} : Bool}:
  match n:
    case 0n:
      ft(hm, {W.ports_in(m, R.arity(W.kind_at(ks, m)), P) == True{} : Bool})
    case 1n++k:
      +h = h
      cov_at.go(R.nat_eq(k, m), ks, P, k, m, {==}, and_l(W.ports_in(k, R.arity(W.kind_at(ks, k)), P), W.covered(ks, k, P), h), hm,
        h2 => cov_at(ks, k, P, m, h2, and_r(W.ports_in(k, R.arity(W.kind_at(ks, k)), P), W.covered(ks, k, P), h)))

def port_tr.go(cE: Bool, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, +q: W.Pt, he: {W.mem(q, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b))))) == cE : Bool}, hm: {(cE || W.mem(q, W.ends(c))) == True{} : Bool}) -> {W.mem(q, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}:
  match cE:
    case True{}:
      mem_ir(q, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)), sigs_sub(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b))), R.ends(ls), d_xl(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall), q, he))
    case False{}:
      mem_il(q, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)), hm)

def port_tr(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, +m: Nat, +p: Nat, hm: {W.mem(W.Pt{m, p}, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, hma: {R.nat_eq(a, m) == False{} : Bool}, hmb: {R.nat_eq(b, m) == False{} : Bool}) ->
  {W.mem(W.Pt{m, p}, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}:
  +h2 = mem_res(W.Pt{m, p}, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c))),
    mem_res(W.Pt{m, p}, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))), hm, ports_not(a, R.arity(W.kind_at(ks, a)), m, p, hma)),
    ports_not(b, R.arity(W.kind_at(ks, b)), m, p, hmb))
  port_tr.go(W.mem(W.Pt{m, p}, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b))))), ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, W.Pt{m, p}, {==}, mem_or(W.Pt{m, p}, W.sigs(List.length(&2, R.NodeKind, ks), es, List.append(&2, R.End, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))), W.ends(c), to_ex_mem(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)), W.ends(c), W.Pt{m, p}, h2)))

def transfer(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, +m: Nat, kk: Nat, h: {W.ports_in(m, kk, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hma: {R.nat_eq(a, m) == False{} : Bool}, +hmb: {R.nat_eq(b, m) == False{} : Bool}) ->
  {W.ports_in(m, kk, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}:
  match kk:
    case 0n:
      {==}
    case 1n++p:
      +h = h
      and_i(W.mem(W.Pt{m, p}, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))), W.ports_in(m, p, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))), port_tr(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, m, p, and_l(W.mem(W.Pt{m, p}, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))), W.ports_in(m, p, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))), h), hma, hmb),
        transfer(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, m, p, and_r(W.mem(W.Pt{m, p}, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))), W.ports_in(m, p, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))), h), hma, hmb))

def cov_a.go(cc: Bool, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, +m: Nat, he: {R.nat_eq(a, m) == cc : Bool}, hmb: {R.nat_eq(b, m) == False{} : Bool}, hm0: {W.below(m, List.length(&2, R.NodeKind, ks)) == True{} : Bool}) ->
  {W.ports_in(m, R.arity(W.kind_at(W.set(ks, a, R.KFree{}), m)), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}:
  match cc:
    case True{}:
      %neq_eq(a, m, he) : {W.ports_in(m, R.arity(W.kind_at(W.set(ks, a, R.KFree{}), _)), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}
      %Equal.sym(R.NodeKind, W.kind_at(W.set(ks, a, R.KFree{}), a), R.KFree{}, ka_free(ks, a)) : {W.ports_in(m, R.arity(_), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}
      {==}
    case False{}:
      +he = he
      %Equal.sym(R.NodeKind, W.kind_at(W.set(ks, a, R.KFree{}), m), W.kind_at(ks, m), ka_ne(ks, a, R.KFree{}, m, he)) : {W.ports_in(m, R.arity(_), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}
      transfer(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, m, R.arity(W.kind_at(ks, m)), cov_at(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c))))), m, hm0, hc), he, hmb)

def cov_b.go(cc: Bool, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, +m: Nat, he: {R.nat_eq(b, m) == cc : Bool}, hm0: {W.below(m, List.length(&2, R.NodeKind, ks)) == True{} : Bool}) ->
  {W.ports_in(m, R.arity(W.kind_at(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), m)), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}:
  match cc:
    case True{}:
      %neq_eq(b, m, he) : {W.ports_in(m, R.arity(W.kind_at(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), _)), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}
      %Equal.sym(R.NodeKind, W.kind_at(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), b), R.KFree{}, ka_free(W.set(ks, a, R.KFree{}), b)) : {W.ports_in(m, R.arity(_), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}
      {==}
    case False{}:
      +he = he
      %Equal.sym(R.NodeKind, W.kind_at(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), m), W.kind_at(W.set(ks, a, R.KFree{}), m), ka_ne(W.set(ks, a, R.KFree{}), b, R.KFree{}, m, he)) : {W.ports_in(m, R.arity(_), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}
      cov_a.go(R.nat_eq(a, m), ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, m, {==}, he, hm0)

def old_port(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, +m: Nat, +hm: {W.below(m, List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}))) == True{} : Bool}) -> {W.ports_in(m, R.arity(W.kind_at(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), m)), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}:
  %Equal.sym(R.NodeKind, W.kind_at(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), m), W.kind_at(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), m), ka_lt(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs), m, hm)) : {W.ports_in(m, R.arity(_), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}
  cov_b.go(R.nat_eq(b, m), ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, m, {==}, rng_back(ks, a, b, m, hm))

def cov_old(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, n: Nat, hle: {W.below(n, 1n+List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}))) == True{} : Bool}) -> {W.covered(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), n, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      +hle = hle
      and_i(W.ports_in(m, R.arity(W.kind_at(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), m)), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))), W.covered(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), m, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))), old_port(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, m, hle),
        cov_old(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, m, below_succ(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), m, hle)))

def new_mem(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, +r: Nat, +p: Nat, hb: {W.below(p, R.arity(W.kind_at(W.kinds(xs), r))) == True{} : Bool}) -> {W.mem(W.Pt{Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), r), p}, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), List.length(&2, R.NodeKind, ks), len_k1(ks, a, b)) : {W.mem(W.Pt{Nat.add(_, r), p}, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}
  mem_ir(W.Pt{Nat.add(List.length(&2, R.NodeKind, ks), r), p}, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)), mem_sigs_of(List.length(&2, R.NodeKind, ks), es, R.New{r, p}, R.ends(ls), in_at(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls), R.New{r, p}, hall,
    emem_ir(R.New{r, p}, W.aux_a(W.kind_at(ks, a)), List.append(&2, R.End, W.aux_b(W.kind_at(ks, b)), R.new_ends(xs, 0n)),
      emem_ir(R.New{r, p}, W.aux_b(W.kind_at(ks, b)), R.new_ends(xs, 0n), new_in(xs, 0n, r, p, hb))))))

def new_ports(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, +r: Nat, kk: Nat, hk: {W.below(kk, 1n+R.arity(W.kind_at(W.kinds(xs), r))) == True{} : Bool}) -> {W.ports_in(Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), r), kk, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}:
  match kk:
    case 0n:
      {==}
    case 1n++p:
      +hk = hk
      and_i(W.mem(W.Pt{Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), r), p}, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))), W.ports_in(Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), r), p, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))), new_mem(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, r, p, hk),
        new_ports(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, r, p, below_succ(R.arity(W.kind_at(W.kinds(xs), r)), p, hk)))

def new_all(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, +r: Nat) -> {W.ports_in(Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), r), R.arity(W.kind_at(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), r))), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}:
  %Equal.sym(R.NodeKind, W.kind_at(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), r)), W.kind_at(W.kinds(xs), r), ka_off(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs), r)) : {W.ports_in(Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), r), R.arity(_), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}
  new_ports(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, r, R.arity(W.kind_at(W.kinds(xs), r)), below_self(R.arity(W.kind_at(W.kinds(xs), r))))

def cov_new(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}, j: Nat) -> {W.covered(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), j), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}:
  match j:
    case 0n:
      %Equal.sym(Nat, Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), 0n), List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), add_zero(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})))) : {W.covered(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), _, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}
      cov_old(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), below_self(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}))))
    case 1n++r:
      %Equal.sym(Nat, Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), 1n+r), 1n+Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), r), succ_add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), r)) : {W.covered(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), _, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}
      and_i(W.ports_in(Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), r), R.arity(W.kind_at(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), r))), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))), W.covered(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), r), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))),
        new_all(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, r), cov_new(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, r))

def g_cov(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}) -> {W.covered(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.length(&2, R.NodeKind, List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs))), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, R.NodeKind, List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs))), Nat.add(List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), List.length(&2, R.NodeKind, W.kinds(xs))), len_app(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs))) : {W.covered(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), _, List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) == True{} : Bool}
  cov_new(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall, List.length(&2, R.NodeKind, W.kinds(xs)))

# The rewrite keeps the net wired
def rw.go(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) == True{} : Bool}, +hall: {R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)) == True{} : Bool}) -> {W.wired(W.rw_kinds(ks, a, b, xs), W.ends(W.rw_links(ks, es, c, ls))) == True{} : Bool}:
  %Equal.sym(List<&2, W.Pt>, W.ends(List.append(&2, W.Ln, c, W.links(List.length(&2, R.NodeKind, ks), es, ls))), List.append(&2, W.Pt, W.ends(c), W.ends(W.links(List.length(&2, R.NodeKind, ks), es, ls))), ends_app(c, W.links(List.length(&2, R.NodeKind, ks), es, ls))) : {W.wired(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), _) == True{} : Bool}
  %Equal.sym(List<&2, W.Pt>, W.ends(W.links(List.length(&2, R.NodeKind, ks), es, ls)), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)), ends_links(List.length(&2, R.NodeKind, ks), es, ls)) : {W.wired(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.append(&2, W.Pt, W.ends(c), _)) == True{} : Bool}
  and_i(W.nodup(List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))), (W.all_live(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))) && W.covered(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.length(&2, R.NodeKind, List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs))), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls))))), g_nodup(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall),
    and_i(W.all_live(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))), W.covered(List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.length(&2, R.NodeKind, List.append(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs))), List.append(&2, W.Pt, W.ends(c), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)))), g_live(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall), g_cov(ks, a, b, es, c, xs, ls, hn, hl, hc, hd, hin, hall)))

def rw_wired(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hw: {W.wired(ks, W.fends(W.Foc{ks, a, b, es, c})) == True{} : Bool},
  +hr: {R.exact(W.kind_at(ks, a), W.kind_at(ks, b), R.RWire{xs, ls}) == True{} : Bool}) -> {W.wired(W.rw_kinds(ks, a, b, xs), W.ends(W.rw_links(ks, es, c, ls))) == True{} : Bool}:
  rw.go(ks, a, b, es, c, xs, ls,
    and_l(W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))), (W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) && W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c))))))), hw),
    and_l(W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))), W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))), and_r(W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))), (W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) && W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c))))))), hw)),
    and_r(W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))), W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))), and_r(W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))), (W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c)))))) && W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c))))))), hw)),
    and_l(R.ends_distinct(R.ends(ls)), (R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) && R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls))), hr),
    and_l(R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)), R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)), and_r(R.ends_distinct(R.ends(ls)), (R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) && R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls))), hr)),
    and_r(R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)), R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)), and_r(R.ends_distinct(R.ends(ls)), (R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) && R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls))), hr)))

def Laws.rewrite_wired(ks, a, b, es, c, xs, ls, hw, hr):
  rw_wired(ks, a, b, es, c, xs, ls, hw, hr)

def keep_wired.go(r: R.Rule, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>,
  +hw: {W.wired(ks, W.fends(W.Foc{ks, a, b, es, c})) == True{} : Bool}, hr: {R.exact(W.kind_at(ks, a), W.kind_at(ks, b), r) == True{} : Bool}) ->
  {W.wired(W.step_kinds(ks, a, b, r), W.step_ends(ks, a, b, es, c, r)) == True{} : Bool}:
  match r:
    case R.RWire{+xs, +ls}:
      rw_wired(ks, a, b, es, c, xs, ls, hw, hr)
    case R.RStuck{}:
      hw

def Laws.rules_keep_wired(ks, a, b, es, c, s, hw):
  keep_wired.go(R.rule(W.kind_at(ks, a), W.kind_at(ks, b), s), ks, a, b, es, c, hw, Laws.rules_exact(W.kind_at(ks, a), W.kind_at(ks, b), s))
