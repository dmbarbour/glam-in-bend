# The evaluator spike's proofs.

import Base
import ./LAWS.bend as Laws
import ./store.bend as S
import ./rules.bend as R
import ./net.bend as N
import ./val.bend as V
import ./ctl.bend as CT
import ./kprim.bend as P
import ./freelist.bend as FL
import ./wiring.bend as W
import ./kplace.bend as KP
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
      {==}

    case R.KCopyL{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
      {==}

    case R.KCopyL{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
      {==}

    case R.KCopyL{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
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
# about U32 in proofs"). So a closed power such as Nat.pow(2n, 22n) only
# ever meets itself: each lemma reasons under a variable bound, and is
# instantiated with the power where the forms match exactly.

# a below x * (1 + b) leaves a / (1 + b) below x
def div_lt(+a: Nat, +x: Nat, +b: Nat, h: MNat.lt(a, Nat.mul(x, 1n+b))) -> MNat.lt(Nat.div(a, 1n+b), x):
  MNat.lt_of_not_le(x, Nat.div(a, 1n+b),
    Equal.trans(Bool, Nat.is_le(x, Nat.div(a, 1n+b)), Nat.is_le(Nat.mul(x, 1n+b), a), False{},
      MNat.le_div_iff_mul_le(x, a, b),
      MNat.not_le_of_lt(a, Nat.mul(x, 1n+b), h)))

def pow_10() -> {Nat.pow(2n, 10n) == 1024n : Nat}:
  {==}

def sum_32() -> {32n == Nat.add(22n, 10n) : Nat}:
  {==}

# a U32 lies below 2^22 * 1024
def lt_32(+h: U32) -> MNat.lt(U32.to_nat(h), Nat.mul(Nat.pow(2n, 22n), 1024n)):
  %pow_10() : MNat.lt(U32.to_nat(h), Nat.mul(Nat.pow(2n, 22n), _))
  %MNat.pow_add(2n, 22n, 10n) : MNat.lt(U32.to_nat(h), _)
  %sum_32() : MNat.lt(U32.to_nat(h), Nat.pow(2n, _))
  MU.u32_to_nat_lt(h)

def fld_bits.go(+h: U32, +x: Nat, l: MNat.lt(Nat.div(U32.to_nat(h), 1n+1023n), x)) -> MNat.lt(U32.to_nat(P.fld(h)), x):
  %Equal.sym(Nat, U32.to_nat(U32.div(h, 1024)), Nat.div(U32.to_nat(h), 1n+1023n), UD.U32.to_nat_div(h, 1024)) : MNat.lt(_, x)
  l

def Laws.fld_bits(h):
  fld_bits.go(h, Nat.pow(2n, 22n), div_lt(U32.to_nat(h), Nat.pow(2n, 22n), 1023n, lt_32(h)))

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

def one_22() -> {one_at(32n, 22n) == UD.U32.word(P.lvl_cap()) : Word(32n)}:
  {==}

def u32_31() -> {U32.to_nat(2147483648) == Nat.pow(2n, 31n) : Nat}:
  %UD.U32.word_nat(2147483648) : {_ == Nat.pow(2n, 31n) : Nat}
  %one_31() : {Word.to_nat(32n, _) == Nat.pow(2n, 31n) : Nat}
  one_at_nat(32n, 31n, {==})

def u32_22() -> {U32.to_nat(P.lvl_cap()) == Nat.pow(2n, 22n) : Nat}:
  %UD.U32.word_nat(P.lvl_cap()) : {_ == Nat.pow(2n, 22n) : Nat}
  %one_22() : {Word.to_nat(32n, _) == Nat.pow(2n, 22n) : Nat}
  one_at_nat(32n, 22n, {==})

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

# a 22-bit level and a 31-bit amount sum within a U32
def fits_32(+a: Nat, +b: Nat, ha: MNat.lt(a, Nat.pow(2n, 22n)), hb: MNat.lt(b, Nat.pow(2n, 31n))) ->
  MNat.lt(Nat.add(a, b), Nat.pow(2n, 32n)):
  %MNat.two_pow_succ_sym(31n) : MNat.lt(Nat.add(a, b), _)
  %MNat.double_eq_add_sym(Nat.pow(2n, 31n)) : MNat.lt(Nat.add(a, b), _)
  sum_lt(a, b, Nat.pow(2n, 22n), Nat.pow(2n, 31n), ha, hb, MNat.pow_le_pow_right(1n, 22n, 31n, {==}))

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
  lift_fits.at(n, o, P.fld(h), Nat.pow(2n, 22n), up, ok, Laws.fld_bits(h), u32_22())

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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
      {==}



    case R.KCopyL{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
      {==}
# by cases again: under every pattern, each rule a constant the checker
# computes
def Laws.rules_pairs_exact(a, b, s):
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
      {==}
    case R.KCopyL{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
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

def is_ext(x: R.End) -> Bool:
  match x:
    case R.Ext{i}:
      True{}
    case R.New{j, p}:
      False{}

def all_ext(xs: List<&2, R.End>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      is_ext(x) && all_ext(t)

def ext_no_new(Y: List<&2, R.End>, +j: Nat, +p: Nat, hY: {all_ext(Y) == True{} : Bool}) -> {R.end_mem(R.New{j, p}, Y) == False{} : Bool}:
  match Y:
    case Nil{}:
      {==}
    case Con{R.Ext{+i}, +t}:
      or_f(R.end_eq(R.Ext{i}, R.New{j, p}), R.end_mem(R.New{j, p}, t), {==}, ext_no_new(t, j, p, hY))
    case Con{R.New{q, r}, t}:
      ft(hY, {R.end_mem(R.New{j, p}, Con{R.New{q, r}, t}) == False{} : Bool})

def ext_cat(A: List<&2, R.End>, +B: List<&2, R.End>, hA: {all_ext(A) == True{} : Bool}, +hB: {all_ext(B) == True{} : Bool}) -> {all_ext(List.append(&2, R.End, A, B)) == True{} : Bool}:
  match A:
    case Nil{}:
      hB
    case Con{+x, +t}:
      +hA = hA
      and_i(is_ext(x), all_ext(List.append(&2, R.End, t, B)), and_l(is_ext(x), all_ext(t), hA), ext_cat(t, B, and_r(is_ext(x), all_ext(t), hA), hB))

def aux_ext(n: Nat, +base: Nat) -> {all_ext(R.aux_ends(n, base)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+q:
      aux_ext(q, 1n+base)

def outer_ext.k(c: Bool, +e: R.End, +rest: List<&2, R.End>, he: {is_ext(e) == True{} : Bool}, hr: {all_ext(rest) == True{} : Bool}) -> {all_ext(R.outer.k(c, e, rest)) == True{} : Bool}:
  match c:
    case True{}:
      and_i(is_ext(e), all_ext(rest), he, hr)
    case False{}:
      hr

def outer_ext(+p: R.Pat, X: List<&2, R.End>, hX: {all_ext(X) == True{} : Bool}) -> {all_ext(R.outer(p, X)) == True{} : Bool}:
  match X:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      +hX = hX
      outer_ext.k(Bool.not(R.pat_in(p, e)), e, R.outer(p, t), and_l(is_ext(e), all_ext(t), hX), outer_ext(p, t, and_r(is_ext(e), all_ext(t), hX)))

# an Ext end the rule must link is an outside peer
def ext_in_Y(+i: Nat, +Y: List<&2, R.End>, +xs: List<&2, R.Spec>, h: {R.end_mem(R.Ext{i}, List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}) -> {R.end_mem(R.Ext{i}, Y) == True{} : Bool}:
  emem_left(R.Ext{i}, Y, R.new_ends(xs, 0n), h, new_no_ext(i, xs, 0n))

# a New end the rule must link is in its new ends
def new_in_new_g(+j: Nat, +p: Nat, +Y: List<&2, R.End>, +xs: List<&2, R.Spec>, hY: {all_ext(Y) == True{} : Bool}, h: {R.end_mem(R.New{j, p}, List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}) ->
  {R.end_mem(R.New{j, p}, R.new_ends(xs, 0n)) == True{} : Bool}:
  or_res(R.end_mem(R.New{j, p}, Y), R.end_mem(R.New{j, p}, R.new_ends(xs, 0n)), emem_or(R.New{j, p}, Y, R.new_ends(xs, 0n), h), ext_no_new(Y, j, p, hY))


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

def len_k1(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat) -> {List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})) == List.length(&2, R.NodeKind, ks) : Nat}:
  Equal.trans(Nat, List.length(&2, R.NodeKind, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{})), List.length(&2, R.NodeKind, W.set(ks, a, R.KFree{})), List.length(&2, R.NodeKind, ks), klen_set(W.set(ks, a, R.KFree{}), b, R.KFree{}), klen_set(ks, a, R.KFree{}))

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

def mem_or(+q: W.Pt, +A: List<&2, W.Pt>, +B: List<&2, W.Pt>, h: {W.mem(q, List.append(&2, W.Pt, A, B)) == True{} : Bool}) -> {(W.mem(q, A) || W.mem(q, B)) == True{} : Bool}:
  Equal.trans(Bool, (W.mem(q, A) || W.mem(q, B)), W.mem(q, List.append(&2, W.Pt, A, B)), True{}, Equal.sym(Bool, W.mem(q, List.append(&2, W.Pt, A, B)), (W.mem(q, A) || W.mem(q, B)), mem_app(q, A, B)), h)

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

def nth_ne(ss: List<&2, Nat>, j: Nat, +m: Nat, h: {W.below(j, List.length(&2, Nat, ss)) == True{} : Bool}, hn: {W.nat_in(m, ss) == False{} : Bool}) ->
  {R.nat_eq(W.nth(ss, j), m) == False{} : Bool}:
  match ss j:
    case Nil{} _:
      ft(h, {R.nat_eq(W.nth(Nil{}, j), m) == False{} : Bool})
    case Con{+s, +t} 0n:
      or_false_l(R.nat_eq(s, m), W.nat_in(m, t), hn)
    case Con{+s, +t} 1n+i:
      nth_ne(t, i, m, h, or_false_r(R.nat_eq(s, m), W.nat_in(m, t), hn))

def nth_inj(ss: List<&2, Nat>, j: Nat, k: Nat, hd: {W.nodup_nat(ss) == True{} : Bool}, hj: {W.below(j, List.length(&2, Nat, ss)) == True{} : Bool},
  hk: {W.below(k, List.length(&2, Nat, ss)) == True{} : Bool}) -> {R.nat_eq(W.nth(ss, j), W.nth(ss, k)) == R.nat_eq(j, k) : Bool}:
  match ss j k:
    case Nil{} _ _:
      ft(hj, {R.nat_eq(W.nth(Nil{}, j), W.nth(Nil{}, k)) == R.nat_eq(j, k) : Bool})
    case Con{+s, +t} 0n 0n:
      neq_refl(s)
    case Con{+s, +t} 0n 1n++q:
      Equal.trans(Bool, R.nat_eq(s, W.nth(t, q)), R.nat_eq(W.nth(t, q), s), False{}, neq_comm(s, W.nth(t, q)),
        nth_ne(t, q, s, hk, not_true(W.nat_in(s, t), and_l(Bool.not(W.nat_in(s, t)), W.nodup_nat(t), hd))))
    case Con{+s, +t} 1n++r 0n:
      nth_ne(t, r, s, hj, not_true(W.nat_in(s, t), and_l(Bool.not(W.nat_in(s, t)), W.nodup_nat(t), hd)))
    case Con{+s, +t} 1n+r 1n+q:
      nth_inj(t, r, q, and_r(Bool.not(W.nat_in(s, t)), W.nodup_nat(t), hd), hj, hk)

def ke_same(n: Nat, ks: List<&2, R.NodeKind>, +v: R.NodeKind) -> {W.kind_at(W.set_ext(n, ks, v), n) == v : R.NodeKind}:
  match n ks:
    case 0n Nil{}:
      {==}
    case 0n Con{k, t}:
      {==}
    case 1n+m Nil{}:
      ke_same(m, Nil{}, v)
    case 1n+m Con{k, t}:
      ke_same(m, t, v)

def ke_ne(n: Nat, ks: List<&2, R.NodeKind>, +v: R.NodeKind, m: Nat, h: {R.nat_eq(n, m) == False{} : Bool}) ->
  {W.kind_at(W.set_ext(n, ks, v), m) == W.kind_at(ks, m) : R.NodeKind}:
  match n ks m:
    case 0n Nil{} 0n:
      tf(h, {W.kind_at(W.set_ext(0n, Nil{}, v), 0n) == W.kind_at(Nil{}, 0n) : R.NodeKind})
    case 0n Nil{} 1n+q:
      {==}
    case 0n Con{k, t} 0n:
      tf(h, {W.kind_at(W.set_ext(0n, Con{k, t}, v), 0n) == W.kind_at(Con{k, t}, 0n) : R.NodeKind})
    case 0n Con{k, t} 1n+q:
      {==}
    case 1n+r Nil{} 0n:
      {==}
    case 1n+r Nil{} 1n+q:
      ke_ne(r, Nil{}, v, q, h)
    case 1n+r Con{k, t} 0n:
      {==}
    case 1n+r Con{k, t} 1n+q:
      ke_ne(r, t, v, q, h)

# a node off the placement keeps its kind
def pl_off(ss: List<&2, Nat>, +ks: List<&2, R.NodeKind>, kx: List<&2, R.NodeKind>, +m: Nat, hn: {W.nat_in(m, ss) == False{} : Bool}) ->
  {W.kind_at(W.place(ss, ks, kx), m) == W.kind_at(ks, m) : R.NodeKind}:
  match ss kx:
    case Con{+s, +st} Con{+k, +kt}:
      +hn = hn
      Equal.trans(R.NodeKind, W.kind_at(W.place(st, W.set_ext(s, ks, k), kt), m), W.kind_at(W.set_ext(s, ks, k), m), W.kind_at(ks, m),
        pl_off(st, W.set_ext(s, ks, k), kt, m, or_false_r(R.nat_eq(s, m), W.nat_in(m, st), hn)),
        ke_ne(s, ks, k, m, or_false_l(R.nat_eq(s, m), W.nat_in(m, st), hn)))
    case Con{s, st} Nil{}:
      {==}
    case Nil{} _:
      {==}

# a placed slot reads its node's kind
def pl_at(ss: List<&2, Nat>, +ks: List<&2, R.NodeKind>, kx: List<&2, R.NodeKind>, j: Nat, hd: {W.nodup_nat(ss) == True{} : Bool},
  hj: {W.below(j, List.length(&2, Nat, ss)) == True{} : Bool}, hk: {W.below(j, List.length(&2, R.NodeKind, kx)) == True{} : Bool}) ->
  {W.kind_at(W.place(ss, ks, kx), W.nth(ss, j)) == W.kind_at(kx, j) : R.NodeKind}:
  match ss kx j:
    case Nil{} _ _:
      ft(hj, {W.kind_at(W.place(Nil{}, ks, kx), W.nth(Nil{}, j)) == W.kind_at(kx, j) : R.NodeKind})
    case Con{s, st} Nil{} _:
      ft(hk, {W.kind_at(W.place(Con{s, st}, ks, Nil{}), W.nth(Con{s, st}, j)) == W.kind_at(Nil{}, j) : R.NodeKind})
    case Con{+s, +st} Con{+k, +kt} 0n:
      Equal.trans(R.NodeKind, W.kind_at(W.place(st, W.set_ext(s, ks, k), kt), s), W.kind_at(W.set_ext(s, ks, k), s), k,
        pl_off(st, W.set_ext(s, ks, k), kt, s, not_true(W.nat_in(s, st), and_l(Bool.not(W.nat_in(s, st)), W.nodup_nat(st), hd))), ke_same(s, ks, k))
    case Con{+s, +st} Con{+k, +kt} 1n+i:
      pl_at(st, W.set_ext(s, ks, k), kt, i, and_r(Bool.not(W.nat_in(s, st)), W.nodup_nat(st), hd), hj, hk)

# where m sits in the placement
def pos.k(c: Bool, r: Nat) -> Nat:
  match c:
    case True{}:
      0n
    case False{}:
      1n+r

def pos(ss: List<&2, Nat>, +m: Nat) -> Nat:
  match ss:
    case Nil{}:
      0n
    case Con{s, t}:
      pos.k(R.nat_eq(s, m), pos(t, m))

def pos_nth.go(c: Bool, +s: Nat, +t: List<&2, Nat>, +m: Nat, he: {R.nat_eq(s, m) == c : Bool}, h: {(c || W.nat_in(m, t)) == True{} : Bool},
  ih: {W.nat_in(m, t) == True{} : Bool} -> {R.nat_eq(W.nth(t, pos(t, m)), m) == True{} : Bool}) -> {R.nat_eq(W.nth(Con{s, t}, pos.k(c, pos(t, m))), m) == True{} : Bool}:
  match c:
    case True{}:
      he
    case False{}:
      ih(h)

def pos_nth(ss: List<&2, Nat>, +m: Nat, h: {W.nat_in(m, ss) == True{} : Bool}) -> {R.nat_eq(W.nth(ss, pos(ss, m)), m) == True{} : Bool}:
  match ss:
    case Nil{}:
      ft(h, {R.nat_eq(W.nth(Nil{}, pos(Nil{}, m)), m) == True{} : Bool})
    case Con{+s, +t}:
      pos_nth.go(R.nat_eq(s, m), s, t, m, {==}, h, h2 => pos_nth(t, m, h2))

def pos_lt.go(c: Bool, +t: List<&2, Nat>, +m: Nat, h: {(c || W.nat_in(m, t)) == True{} : Bool},
  ih: {W.nat_in(m, t) == True{} : Bool} -> {W.below(pos(t, m), List.length(&2, Nat, t)) == True{} : Bool}) -> {W.below(pos.k(c, pos(t, m)), 1n+List.length(&2, Nat, t)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      ih(h)

def pos_lt(ss: List<&2, Nat>, +m: Nat, h: {W.nat_in(m, ss) == True{} : Bool}) -> {W.below(pos(ss, m), List.length(&2, Nat, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      ft(h, {W.below(pos(Nil{}, m), 0n) == True{} : Bool})
    case Con{+s, +t}:
      pos_lt.go(R.nat_eq(s, m), t, m, h, h2 => pos_lt(t, m, h2))

def free_arity(k: R.NodeKind, +p: Nat, h: {W.is_free_kind(k) == True{} : Bool}) -> {W.below(p, R.arity(k)) == False{} : Bool}:
  match k:
    case R.KFree{}:
      {==}
    case R.KFn{}:
      ft(h, {W.below(p, R.arity(R.KFn{})) == False{} : Bool})
    case R.KAp{}:
      ft(h, {W.below(p, R.arity(R.KAp{})) == False{} : Bool})
    case R.KCopy{}:
      ft(h, {W.below(p, R.arity(R.KCopy{})) == False{} : Bool})
    case R.KMerge{}:
      ft(h, {W.below(p, R.arity(R.KMerge{})) == False{} : Bool})
    case R.KData{}:
      ft(h, {W.below(p, R.arity(R.KData{})) == False{} : Bool})
    case R.KEraN{}:
      ft(h, {W.below(p, R.arity(R.KEraN{})) == False{} : Bool})
    case R.KEraP{}:
      ft(h, {W.below(p, R.arity(R.KEraP{})) == False{} : Bool})
    case R.KRoot{}:
      ft(h, {W.below(p, R.arity(R.KRoot{})) == False{} : Bool})
    case R.KCall{}:
      ft(h, {W.below(p, R.arity(R.KCall{})) == False{} : Bool})
    case R.KLift{}:
      ft(h, {W.below(p, R.arity(R.KLift{})) == False{} : Bool})
    case R.KLiftC{}:
      ft(h, {W.below(p, R.arity(R.KLiftC{})) == False{} : Bool})
    case R.KCopyL{}:
      ft(h, {W.below(p, R.arity(R.KCopyL{})) == False{} : Bool})
    case R.KCopyR{}:
      ft(h, {W.below(p, R.arity(R.KCopyR{})) == False{} : Bool})
    case R.KMergeL{}:
      ft(h, {W.below(p, R.arity(R.KMergeL{})) == False{} : Bool})
    case R.KMergeR{}:
      ft(h, {W.below(p, R.arity(R.KMergeR{})) == False{} : Bool})

def slot_tr(+s: Nat, +m: Nat, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, eq: {s == m : Nat},
  hs: {(R.nat_eq(s, a) || (R.nat_eq(s, b) || W.is_free_kind(W.kind_at(ks, s)))) == True{} : Bool}) ->
  {(R.nat_eq(m, a) || (R.nat_eq(m, b) || W.is_free_kind(W.kind_at(ks, m)))) == True{} : Bool}:
  %eq : {(R.nat_eq(_, a) || (R.nat_eq(_, b) || W.is_free_kind(W.kind_at(ks, _)))) == True{} : Bool}
  hs

def sn.go(c: Bool, +s: Nat, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +m: Nat, +p: Nat, he: {R.nat_eq(s, m) == c : Bool},
  hs: {(R.nat_eq(s, a) || (R.nat_eq(s, b) || W.is_free_kind(W.kind_at(ks, s)))) == True{} : Bool},
  hma: {R.nat_eq(a, m) == False{} : Bool}, hmb: {R.nat_eq(b, m) == False{} : Bool}, hl: {W.below(p, R.arity(W.kind_at(ks, m))) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      +h1 = slot_tr(s, m, ks, a, b, neq_eq(s, m, he), hs)
      Empty.absurd({True{} == False{} : Bool}, MNat.internal_false_ne_true(Equal.trans(Bool, False{}, W.below(p, R.arity(W.kind_at(ks, m))), True{},
        Equal.sym(Bool, W.below(p, R.arity(W.kind_at(ks, m))), False{}, free_arity(W.kind_at(ks, m), p,
          or_res(R.nat_eq(m, b), W.is_free_kind(W.kind_at(ks, m)),
            or_res(R.nat_eq(m, a), (R.nat_eq(m, b) || W.is_free_kind(W.kind_at(ks, m))), h1, Equal.trans(Bool, R.nat_eq(m, a), R.nat_eq(a, m), False{}, neq_comm(m, a), hma)),
            Equal.trans(Bool, R.nat_eq(m, b), R.nat_eq(b, m), False{}, neq_comm(m, b), hmb)))), hl)))
    case False{}:
      {==}

# a live port's node, not the pair's, is no slot of the placement
def slot_not(ss: List<&2, Nat>, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +m: Nat, +p: Nat, hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool},
  +hma: {R.nat_eq(a, m) == False{} : Bool}, +hmb: {R.nat_eq(b, m) == False{} : Bool}, +hl: {W.below(p, R.arity(W.kind_at(ks, m))) == True{} : Bool}) ->
  {W.nat_in(m, ss) == False{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +hok = hok
      or_f(R.nat_eq(s, m), W.nat_in(m, t),
        sn.go(R.nat_eq(s, m), s, ks, a, b, m, p, {==}, and_l((R.nat_eq(s, a) || (R.nat_eq(s, b) || W.is_free_kind(W.kind_at(ks, s)))), W.slots_ok(ks, a, b, t), hok), hma, hmb, hl),
        slot_not(t, ks, a, b, m, p, and_r((R.nat_eq(s, a) || (R.nat_eq(s, b) || W.is_free_kind(W.kind_at(ks, s)))), W.slots_ok(ks, a, b, t), hok), hma, hmb, hl))

def ka_past(ks: List<&2, R.NodeKind>, m: Nat, h: {W.below(m, List.length(&2, R.NodeKind, ks)) == False{} : Bool}) -> {W.kind_at(ks, m) == R.KFree{} : R.NodeKind}:
  match ks m:
    case Nil{} _:
      {==}
    case Con{k, t} 0n:
      tf(h, {W.kind_at(Con{k, t}, 0n) == R.KFree{} : R.NodeKind})
    case Con{k, t} 1n+q:
      ka_past(t, q, h)

def njl.go(c: Bool, +K: List<&2, R.NodeKind>, +j: Nat, +p: Nat, he: {W.below(j, List.length(&2, R.NodeKind, K)) == c : Bool},
  hl: {W.below(p, R.arity(W.kind_at(K, j))) == True{} : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, MNat.internal_false_ne_true(Equal.trans(Bool, False{}, W.below(p, R.arity(W.kind_at(K, j))), True{},
        Equal.sym(Bool, W.below(p, R.arity(W.kind_at(K, j))), False{},
          Equal.cong(R.NodeKind, Bool, (k => W.below(p, R.arity(k))), W.kind_at(K, j), R.KFree{}, ka_past(K, j, he))), hl)))

# a New end the rule must link names a node it makes
def new_j_lt(+xs: List<&2, R.Spec>, +j: Nat, +p: Nat, h: {R.end_mem(R.New{j, p}, R.new_ends(xs, 0n)) == True{} : Bool}) ->
  {W.below(j, List.length(&2, R.NodeKind, W.kinds(xs))) == True{} : Bool}:
  njl.go(W.below(j, List.length(&2, R.NodeKind, W.kinds(xs))), W.kinds(xs), j, p, {==}, new_live(xs, 0n, j, p, h))

def bl_tr(+ss: List<&2, Nat>, +kx: List<&2, R.NodeKind>, +j: Nat, hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, kx) : Nat},
  h: {W.below(j, List.length(&2, R.NodeKind, kx)) == True{} : Bool}) -> {W.below(j, List.length(&2, Nat, ss)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Nat, ss), List.length(&2, R.NodeKind, kx), hlen) : {W.below(j, _) == True{} : Bool}
  h

def farp.one(y: R.End, +ss: List<&2, Nat>, +es: W.Peers, +xs: List<&2, R.Spec>, +m: Nat, +r: Nat, hy: {R.end_mem(y, R.new_ends(xs, 0n)) == True{} : Bool},
  hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, hn: {W.nat_in(m, ss) == False{} : Bool}) ->
  {W.pt_eq(W.sigp(ss, es, y), W.Pt{m, r}) == False{} : Bool}:
  match y:
    case R.Ext{+i}:
      Empty.absurd({W.pt_eq(W.sigp(ss, es, R.Ext{i}), W.Pt{m, r}) == False{} : Bool}, ne_tf(Equal.trans(Bool, True{}, R.end_mem(R.Ext{i}, R.new_ends(xs, 0n)), False{},
        Equal.sym(Bool, R.end_mem(R.Ext{i}, R.new_ends(xs, 0n)), True{}, hy), new_no_ext(i, xs, 0n))))
    case R.New{+j, +p}:
      and_fl(R.nat_eq(W.nth(ss, j), m), R.nat_eq(p, r), nth_ne(ss, j, m, bl_tr(ss, W.kinds(xs), j, hlen, new_j_lt(xs, j, p, hy)), hn))

# a live port off the pair and the slots is no new node's
def farp(Y2: List<&2, R.End>, +ss: List<&2, Nat>, +es: W.Peers, +xs: List<&2, R.Spec>, +m: Nat, +r: Nat, h: {R.all_in(Y2, R.new_ends(xs, 0n)) == True{} : Bool},
  +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nat_in(m, ss) == False{} : Bool}) ->
  {W.mem(W.Pt{m, r}, W.sigsp(ss, es, Y2)) == False{} : Bool}:
  match Y2:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +h = h
      or_f(W.pt_eq(W.sigp(ss, es, y), W.Pt{m, r}), W.mem(W.Pt{m, r}, W.sigsp(ss, es, t)),
        farp.one(y, ss, es, xs, m, r, and_l(R.end_mem(y, R.new_ends(xs, 0n)), R.all_in(t, R.new_ends(xs, 0n)), h), hlen, hn),
        farp(t, ss, es, xs, m, r, and_r(R.end_mem(y, R.new_ends(xs, 0n)), R.all_in(t, R.new_ends(xs, 0n)), h), hlen, hn))

def ends_linksp(+ss: List<&2, Nat>, +es: W.Peers, ls: List<&2, R.Link>) -> {W.ends(W.linksp(ss, es, ls)) == W.sigsp(ss, es, R.ends(ls)) : List<&2, W.Pt>}:
  match ls:
    case Nil{}:
      {==}
    case Con{R.Link{+x, +y}, +t}:
      %Equal.sym(List<&2, W.Pt>, W.ends(W.linksp(ss, es, t)), W.sigsp(ss, es, R.ends(t)), ends_linksp(ss, es, t)) : {Con{W.sigp(ss, es, x), Con{W.sigp(ss, es, y), _}} == Con{W.sigp(ss, es, x), Con{W.sigp(ss, es, y), W.sigsp(ss, es, R.ends(t))}} : List<&2, W.Pt>}
      {==}


def sigs_appp(+ss: List<&2, Nat>, +es: W.Peers, A: List<&2, R.End>, +B: List<&2, R.End>) -> {W.sigsp(ss, es, List.append(&2, R.End, A, B)) == List.append(&2, W.Pt, W.sigsp(ss, es, A), W.sigsp(ss, es, B)) : List<&2, W.Pt>}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(List<&2, W.Pt>, W.sigsp(ss, es, List.append(&2, R.End, t, B)), List.append(&2, W.Pt, W.sigsp(ss, es, t), W.sigsp(ss, es, B)), sigs_appp(ss, es, t, B)) : {Con{W.sigp(ss, es, x), _} == Con{W.sigp(ss, es, x), List.append(&2, W.Pt, W.sigsp(ss, es, t), W.sigsp(ss, es, B))} : List<&2, W.Pt>}
      {==}


def msop.go(c: Bool, +ss: List<&2, Nat>, +es: W.Peers, +x: R.End, +y: R.End, +t: List<&2, R.End>, he: {R.end_eq(y, x) == c : Bool},
  hm: {(c || R.end_mem(x, t)) == True{} : Bool},
  ih: {R.end_mem(x, t) == True{} : Bool} -> {W.mem(W.sigp(ss, es, x), W.sigsp(ss, es, t)) == True{} : Bool}) ->
  {W.mem(W.sigp(ss, es, x), W.sigsp(ss, es, Con{y, t})) == True{} : Bool}:
  match c:
    case True{}:
      %end_eqv(y, x, he) : {W.mem(W.sigp(ss, es, _), W.sigsp(ss, es, Con{y, t})) == True{} : Bool}
      or_l(W.pt_eq(W.sigp(ss, es, y), W.sigp(ss, es, y)), W.mem(W.sigp(ss, es, y), W.sigsp(ss, es, t)), pt_refl(W.sigp(ss, es, y)))
    case False{}:
      or_r(W.pt_eq(W.sigp(ss, es, y), W.sigp(ss, es, x)), W.mem(W.sigp(ss, es, x), W.sigsp(ss, es, t)), ih(hm))

# an end in Y lands among Y's placed ends

# an end in Y lands among Y's placed ends
def mem_sigs_ofp(+ss: List<&2, Nat>, +es: W.Peers, +x: R.End, Y: List<&2, R.End>, h: {R.end_mem(x, Y) == True{} : Bool}) -> {W.mem(W.sigp(ss, es, x), W.sigsp(ss, es, Y)) == True{} : Bool}:
  match Y:
    case Nil{}:
      ft(h, {W.mem(W.sigp(ss, es, x), W.sigsp(ss, es, Nil{})) == True{} : Bool})
    case Con{+y, +t}:
      msop.go(R.end_eq(y, x), ss, es, x, y, t, {==}, h, h2 => mem_sigs_ofp(ss, es, x, t, h2))


def subp.go(c: Bool, +ss: List<&2, Nat>, +es: W.Peers, +x: R.End, +t: List<&2, R.End>, +Y: List<&2, R.End>, +q: W.Pt, he: {W.pt_eq(W.sigp(ss, es, x), q) == c : Bool},
  hx: {R.end_mem(x, Y) == True{} : Bool}, hm: {(c || W.mem(q, W.sigsp(ss, es, t))) == True{} : Bool},
  ih: {W.mem(q, W.sigsp(ss, es, t)) == True{} : Bool} -> {W.mem(q, W.sigsp(ss, es, Y)) == True{} : Bool}) -> {W.mem(q, W.sigsp(ss, es, Y)) == True{} : Bool}:
  match c:
    case True{}:
      %pt_eqv(W.sigp(ss, es, x), q, he) : {W.mem(_, W.sigsp(ss, es, Y)) == True{} : Bool}
      mem_sigs_ofp(ss, es, x, Y, hx)
    case False{}:
      ih(hm)

# X's ends all in Y: X's placed ends are among Y's

# X's ends all in Y: X's placed ends are among Y's
def sigs_subp(+ss: List<&2, Nat>, +es: W.Peers, X: List<&2, R.End>, +Y: List<&2, R.End>, h: {R.all_in(X, Y) == True{} : Bool}, +q: W.Pt,
  hq: {W.mem(q, W.sigsp(ss, es, X)) == True{} : Bool}) -> {W.mem(q, W.sigsp(ss, es, Y)) == True{} : Bool}:
  match X:
    case Nil{}:
      ft(hq, {W.mem(q, W.sigsp(ss, es, Y)) == True{} : Bool})
    case Con{+x, +t}:
      +h = h
      subp.go(W.pt_eq(W.sigp(ss, es, x), q), ss, es, x, t, Y, q, {==}, and_l(R.end_mem(x, Y), R.all_in(t, Y), h), hq,
        h2 => sigs_subp(ss, es, t, Y, and_r(R.end_mem(x, Y), R.all_in(t, Y), h), q, h2))

# Ext ends only

def injp.go(cx: Bool, cy: Bool, +ss: List<&2, Nat>, +es: W.Peers, +x: R.End, +y: R.End, +z: R.End, +t: List<&2, R.End>,
  hex: {R.end_eq(z, x) == cx : Bool}, hey: {R.end_eq(z, y) == cy : Bool},
  hmx: {(cx || R.end_mem(x, t)) == True{} : Bool}, hmy: {(cy || R.end_mem(y, t)) == True{} : Bool},
  hz: {W.mem(W.sigp(ss, es, z), W.sigsp(ss, es, t)) == False{} : Bool}, hxy: {R.end_eq(x, y) == False{} : Bool},
  ih: {R.end_mem(x, t) == True{} : Bool} -> {R.end_mem(y, t) == True{} : Bool} -> {W.pt_eq(W.sigp(ss, es, x), W.sigp(ss, es, y)) == False{} : Bool}) ->
  {W.pt_eq(W.sigp(ss, es, x), W.sigp(ss, es, y)) == False{} : Bool}:
  match cx cy:
    case True{} True{}:
      Empty.absurd({W.pt_eq(W.sigp(ss, es, x), W.sigp(ss, es, y)) == False{} : Bool}, MNat.internal_false_ne_true(Equal.trans(Bool, False{}, R.end_eq(x, y), True{},
        Equal.sym(Bool, R.end_eq(x, y), False{}, hxy),
        eeq_true(x, y, Equal.trans(R.End, x, z, y, Equal.sym(R.End, z, x, end_eqv(z, x, hex)), end_eqv(z, y, hey))))))
    case True{} False{}:
      ij.c(W.pt_eq(W.sigp(ss, es, x), W.sigp(ss, es, y)), W.sigp(ss, es, x), W.sigp(ss, es, y), W.sigp(ss, es, z), W.sigsp(ss, es, t), {==},
        Equal.cong(R.End, W.Pt, (v => W.sigp(ss, es, v)), z, x, end_eqv(z, x, hex)), mem_sigs_ofp(ss, es, y, t, hmy), hz)
    case False{} True{}:
      ij.c2(W.pt_eq(W.sigp(ss, es, x), W.sigp(ss, es, y)), W.sigp(ss, es, x), W.sigp(ss, es, y), W.sigp(ss, es, z), W.sigsp(ss, es, t), {==},
        Equal.cong(R.End, W.Pt, (v => W.sigp(ss, es, v)), z, y, end_eqv(z, y, hey)), mem_sigs_ofp(ss, es, x, t, hmx), hz)
    case False{} False{}:
      ih(hmx)(hmy)

# placed ends no two alike: distinct ends of the list land apart

# placed ends no two alike: distinct ends of the list land apart
def injp(Xs: List<&2, R.End>, +ss: List<&2, Nat>, +es: W.Peers, +x: R.End, +y: R.End, hn: {W.nodup(W.sigsp(ss, es, Xs)) == True{} : Bool},
  hx: {R.end_mem(x, Xs) == True{} : Bool}, hy: {R.end_mem(y, Xs) == True{} : Bool}, +hxy: {R.end_eq(x, y) == False{} : Bool}) ->
  {W.pt_eq(W.sigp(ss, es, x), W.sigp(ss, es, y)) == False{} : Bool}:
  match Xs:
    case Nil{}:
      ft(hx, {W.pt_eq(W.sigp(ss, es, x), W.sigp(ss, es, y)) == False{} : Bool})
    case Con{+z, +t}:
      +hn = hn
      injp.go(R.end_eq(z, x), R.end_eq(z, y), ss, es, x, y, z, t, {==}, {==}, hx, hy,
        not_true(W.mem(W.sigp(ss, es, z), W.sigsp(ss, es, t)), and_l(Bool.not(W.mem(W.sigp(ss, es, z), W.sigsp(ss, es, t))), W.nodup(W.sigsp(ss, es, t)), hn)), hxy,
        h1 => h2 => injp(t, ss, es, x, y, and_r(Bool.not(W.mem(W.sigp(ss, es, z), W.sigsp(ss, es, t))), W.nodup(W.sigsp(ss, es, t)), hn), h1, h2, hxy))


# The rewrite, its new nodes placed
# =================================

def qd_nec(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}) -> {W.nodup(List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))) == True{} : Bool}:
  nodup_r(W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c)), nodup_r(W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))), hn))

def qd_lec(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}) -> {W.all_live(ks, List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))) == True{} : Bool}:
  live_r(ks, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c)), live_r(ks, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))), hl))

def qd_oa(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}) -> {all_out(List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c)), W.ports(a, R.arity(W.kind_at(ks, a)))) == True{} : Bool}:
  out_snd(W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c)), W.ports(a, R.arity(W.kind_at(ks, a))), out_sym(W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))), nodup_out(W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))), hn)))

def qd_ob(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}) -> {all_out(List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c)), W.ports(b, R.arity(W.kind_at(ks, b)))) == True{} : Bool}:
  out_sym(W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c)), nodup_out(W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c)), nodup_r(W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))), hn)))

def qd_xl(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}) -> {R.all_in(Y, R.ends(ls)) == True{} : Bool}:
  in_trans(Y, List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls), in_app_l(Y, R.new_ends(xs, 0n)), hall)

def bl_back(+ss: List<&2, Nat>, +kx: List<&2, R.NodeKind>, +j: Nat, hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, kx) : Nat},
  h: {W.below(j, List.length(&2, Nat, ss)) == True{} : Bool}) -> {W.below(j, List.length(&2, R.NodeKind, kx)) == True{} : Bool}:
  %hlen : {W.below(j, _) == True{} : Bool}
  h

# a live port off the pair's ports stays live
def keepq.go(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +m: Nat, +r: Nat, hl1: {W.below(r, R.arity(W.kind_at(ks, m))) == True{} : Bool},
  hma: {R.nat_eq(a, m) == False{} : Bool}, hmb: {R.nat_eq(b, m) == False{} : Bool}, hnm: {W.nat_in(m, ss) == False{} : Bool}) ->
  {W.below(r, R.arity(W.kind_at(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), m))) == True{} : Bool}:
  %Equal.sym(R.NodeKind, W.kind_at(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), m), W.kind_at(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), m), pl_off(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs), m, hnm)) : {W.below(r, R.arity(_)) == True{} : Bool}
  %Equal.sym(R.NodeKind, W.kind_at(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), m), W.kind_at(W.set(ks, a, R.KFree{}), m), ka_ne(W.set(ks, a, R.KFree{}), b, R.KFree{}, m, hmb)) : {W.below(r, R.arity(_)) == True{} : Bool}
  %Equal.sym(R.NodeKind, W.kind_at(W.set(ks, a, R.KFree{}), m), W.kind_at(ks, m), ka_ne(ks, a, R.KFree{}, m, hma)) : {W.below(r, R.arity(_)) == True{} : Bool}
  hl1

def keepq(q: W.Pt, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, hlq: {W.live(ks, q) == True{} : Bool}, hA: {W.mem(q, W.ports(a, R.arity(W.kind_at(ks, a)))) == False{} : Bool}, hB: {W.mem(q, W.ports(b, R.arity(W.kind_at(ks, b)))) == False{} : Bool}) ->
  {W.live(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), q) == True{} : Bool}:
  match q:
    case W.Pt{+m, +r}:
      +hl1 = hlq
      +hma = kl.ne(R.nat_eq(a, m), ks, a, m, r, {==}, hl1, hA)
      +hmb = kl.ne(R.nat_eq(b, m), ks, b, m, r, {==}, hl1, hB)
      keepq.go(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, m, r, hl1, hma, hmb, slot_not(ss, ks, a, b, m, r, hok, hma, hmb, hl1))

# a new node's port is live, its kind its own
def live_newq(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +j: Nat, +p: Nat, +hj: {W.below(j, List.length(&2, R.NodeKind, W.kinds(xs))) == True{} : Bool}, hb: {W.below(p, R.arity(W.kind_at(W.kinds(xs), j))) == True{} : Bool}) ->
  {W.live(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.Pt{W.nth(ss, j), p}) == True{} : Bool}:
  %Equal.sym(R.NodeKind, W.kind_at(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.nth(ss, j)), W.kind_at(W.kinds(xs), j), pl_at(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs), j, hss, bl_tr(ss, W.kinds(xs), j, hlen, hj), hj)) : {W.below(p, R.arity(_)) == True{} : Bool}
  hb

# Reflection, placed
def rfq.ext(cc: Bool, +i: Nat, +k: Nat, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, he: {R.nat_eq(i, k) == cc : Bool},
  hx: {R.end_mem(R.Ext{i}, Y) == True{} : Bool}, hy: {R.end_mem(R.Ext{k}, Y) == True{} : Bool}) ->
  {W.pt_eq(W.sigp(ss, es, R.Ext{i}), W.sigp(ss, es, R.Ext{k})) == cc : Bool}:
  match cc:
    case True{}:
      %neq_eq(i, k, he) : {W.pt_eq(W.sigp(ss, es, R.Ext{i}), W.sigp(ss, es, R.Ext{_})) == True{} : Bool}
      pt_refl(W.sigp(ss, es, R.Ext{i}))
    case False{}:
      injp(Y, ss, es, R.Ext{i}, R.Ext{k}, nodup_l(W.sigsp(ss, es, Y), W.ends(c), qd_nec(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)), hx, hy, he)

def q_vs_new(q: W.Pt, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +j: Nat, +p: Nat, hlq: {W.live(ks, q) == True{} : Bool}, hA: {W.mem(q, W.ports(a, R.arity(W.kind_at(ks, a)))) == False{} : Bool},
  hB: {W.mem(q, W.ports(b, R.arity(W.kind_at(ks, b)))) == False{} : Bool}, hj: {W.below(j, List.length(&2, R.NodeKind, W.kinds(xs))) == True{} : Bool}) -> {W.pt_eq(q, W.Pt{W.nth(ss, j), p}) == False{} : Bool}:
  match q:
    case W.Pt{+m, +r}:
      +hl1 = hlq
      +hma = kl.ne(R.nat_eq(a, m), ks, a, m, r, {==}, hl1, hA)
      +hmb = kl.ne(R.nat_eq(b, m), ks, b, m, r, {==}, hl1, hB)
      and_fl(R.nat_eq(m, W.nth(ss, j)), R.nat_eq(r, p), Equal.trans(Bool, R.nat_eq(m, W.nth(ss, j)), R.nat_eq(W.nth(ss, j), m), False{}, neq_comm(m, W.nth(ss, j)),
        nth_ne(ss, j, m, bl_tr(ss, W.kinds(xs), j, hlen, hj), slot_not(ss, ks, a, b, m, r, hok, hma, hmb, hl1))))

def new_vs_q(q: W.Pt, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +j: Nat, +p: Nat, hlq: {W.live(ks, q) == True{} : Bool}, hA: {W.mem(q, W.ports(a, R.arity(W.kind_at(ks, a)))) == False{} : Bool},
  hB: {W.mem(q, W.ports(b, R.arity(W.kind_at(ks, b)))) == False{} : Bool}, hj: {W.below(j, List.length(&2, R.NodeKind, W.kinds(xs))) == True{} : Bool}) -> {W.pt_eq(W.Pt{W.nth(ss, j), p}, q) == False{} : Bool}:
  match q:
    case W.Pt{+m, +r}:
      +hl1 = hlq
      +hma = kl.ne(R.nat_eq(a, m), ks, a, m, r, {==}, hl1, hA)
      +hmb = kl.ne(R.nat_eq(b, m), ks, b, m, r, {==}, hl1, hB)
      and_fl(R.nat_eq(W.nth(ss, j), m), R.nat_eq(p, r), nth_ne(ss, j, m, bl_tr(ss, W.kinds(xs), j, hlen, hj), slot_not(ss, ks, a, b, m, r, hok, hma, hmb, hl1)))

def reflectq(x: R.End, y: R.End, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, hx: {R.end_mem(x, List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, hy: {R.end_mem(y, List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}) ->
  {W.pt_eq(W.sigp(ss, es, x), W.sigp(ss, es, y)) == R.end_eq(x, y) : Bool}:
  match x y:
    case R.Ext{+i} R.Ext{+k}:
      rfq.ext(R.nat_eq(i, k), i, k, ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, {==}, ext_in_Y(i, Y, xs, hx), ext_in_Y(k, Y, xs, hy))
    case R.Ext{+i} R.New{+j, +p}:
      +hq = mem_sigs_ofp(ss, es, R.Ext{i}, Y, ext_in_Y(i, Y, xs, hx))
      q_vs_new(W.sigp(ss, es, R.Ext{i}), ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, j, p, live_at(W.sigsp(ss, es, Y), ks, W.sigp(ss, es, R.Ext{i}), live_l(ks, W.sigsp(ss, es, Y), W.ends(c), qd_lec(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)), hq),
        out_at(W.sigsp(ss, es, Y), W.ports(a, R.arity(W.kind_at(ks, a))), W.sigp(ss, es, R.Ext{i}), out_fst(W.sigsp(ss, es, Y), W.ends(c), W.ports(a, R.arity(W.kind_at(ks, a))), qd_oa(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)), hq),
        out_at(W.sigsp(ss, es, Y), W.ports(b, R.arity(W.kind_at(ks, b))), W.sigp(ss, es, R.Ext{i}), out_fst(W.sigsp(ss, es, Y), W.ends(c), W.ports(b, R.arity(W.kind_at(ks, b))), qd_ob(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)), hq),
        new_j_lt(xs, j, p, new_in_new_g(j, p, Y, xs, hY, hy)))
    case R.New{+j, +p} R.Ext{+i}:
      +hq = mem_sigs_ofp(ss, es, R.Ext{i}, Y, ext_in_Y(i, Y, xs, hy))
      new_vs_q(W.sigp(ss, es, R.Ext{i}), ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, j, p, live_at(W.sigsp(ss, es, Y), ks, W.sigp(ss, es, R.Ext{i}), live_l(ks, W.sigsp(ss, es, Y), W.ends(c), qd_lec(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)), hq),
        out_at(W.sigsp(ss, es, Y), W.ports(a, R.arity(W.kind_at(ks, a))), W.sigp(ss, es, R.Ext{i}), out_fst(W.sigsp(ss, es, Y), W.ends(c), W.ports(a, R.arity(W.kind_at(ks, a))), qd_oa(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)), hq),
        out_at(W.sigsp(ss, es, Y), W.ports(b, R.arity(W.kind_at(ks, b))), W.sigp(ss, es, R.Ext{i}), out_fst(W.sigsp(ss, es, Y), W.ends(c), W.ports(b, R.arity(W.kind_at(ks, b))), qd_ob(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)), hq),
        new_j_lt(xs, j, p, new_in_new_g(j, p, Y, xs, hY, hx)))
    case R.New{+j, +p} R.New{+j2, +p2}:
      %Equal.sym(Bool, R.nat_eq(W.nth(ss, j), W.nth(ss, j2)), R.nat_eq(j, j2), nth_inj(ss, j, j2, hss,
        bl_tr(ss, W.kinds(xs), j, hlen, new_j_lt(xs, j, p, new_in_new_g(j, p, Y, xs, hY, hx))),
        bl_tr(ss, W.kinds(xs), j2, hlen, new_j_lt(xs, j2, p2, new_in_new_g(j2, p2, Y, xs, hY, hy))))) : {(_ && R.nat_eq(p, p2)) == (R.nat_eq(j, j2) && R.nat_eq(p, p2)) : Bool}
      {==}

def msiq(+x: R.End, t: List<&2, R.End>, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +hx: {R.end_mem(x, List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, ht: {R.all_in(t, List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}) ->
  {W.mem(W.sigp(ss, es, x), W.sigsp(ss, es, t)) == R.end_mem(x, t) : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      +ht = ht
      %Equal.sym(Bool, W.pt_eq(W.sigp(ss, es, y), W.sigp(ss, es, x)), R.end_eq(y, x), reflectq(y, x, ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, and_l(R.end_mem(y, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), R.all_in(r, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), ht), hx)) : {(_ || W.mem(W.sigp(ss, es, x), W.sigsp(ss, es, r))) == (R.end_eq(y, x) || R.end_mem(x, r)) : Bool}
      %Equal.sym(Bool, W.mem(W.sigp(ss, es, x), W.sigsp(ss, es, r)), R.end_mem(x, r), msiq(x, r, ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, hx, and_r(R.end_mem(y, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), R.all_in(r, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), ht))) : {(R.end_eq(y, x) || _) == (R.end_eq(y, x) || R.end_mem(x, r)) : Bool}
      {==}

def nodup_sigsq(Xs: List<&2, R.End>, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, hin2: {R.all_in(Xs, List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, hd2: {R.ends_distinct(Xs) == True{} : Bool}) ->
  {W.nodup(W.sigsp(ss, es, Xs)) == True{} : Bool}:
  match Xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hin2 = hin2
      +hd2 = hd2
      %Equal.sym(Bool, W.mem(W.sigp(ss, es, x), W.sigsp(ss, es, t)), R.end_mem(x, t), msiq(x, t, ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, and_l(R.end_mem(x, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), R.all_in(t, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), hin2), and_r(R.end_mem(x, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), R.all_in(t, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), hin2))) : {(Bool.not(_) && W.nodup(W.sigsp(ss, es, t))) == True{} : Bool}
      and_i(Bool.not(R.end_mem(x, t)), W.nodup(W.sigsp(ss, es, t)), and_l(Bool.not(R.end_mem(x, t)), R.ends_distinct(t), hd2),
        nodup_sigsq(t, ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, and_r(R.end_mem(x, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), R.all_in(t, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), hin2), and_r(Bool.not(R.end_mem(x, t)), R.ends_distinct(t), hd2)))

# Goal one: no port twice
def not_in_vq(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +m: Nat, +r: Nat, hox: {W.mem(W.Pt{m, r}, W.sigsp(ss, es, Y)) == False{} : Bool}, hnm: {W.nat_in(m, ss) == False{} : Bool}) ->
  {W.mem(W.Pt{m, r}, W.sigsp(ss, es, List.append(&2, R.End, Y, R.new_ends(xs, 0n)))) == False{} : Bool}:
  %Equal.sym(List<&2, W.Pt>, W.sigsp(ss, es, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.sigsp(ss, es, R.new_ends(xs, 0n))), sigs_appp(ss, es, Y, R.new_ends(xs, 0n))) : {W.mem(W.Pt{m, r}, _) == False{} : Bool}
  mem_ff(W.Pt{m, r}, W.sigsp(ss, es, Y), W.sigsp(ss, es, R.new_ends(xs, 0n)), hox, farp(R.new_ends(xs, 0n), ss, es, xs, m, r, in_refl(R.new_ends(xs, 0n)), hlen, hnm))

def cnq.x(x: W.Pt, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, hlx: {W.live(ks, x) == True{} : Bool}, hox: {W.mem(x, W.sigsp(ss, es, Y)) == False{} : Bool},
  hA: {W.mem(x, W.ports(a, R.arity(W.kind_at(ks, a)))) == False{} : Bool}, hB: {W.mem(x, W.ports(b, R.arity(W.kind_at(ks, b)))) == False{} : Bool}) -> {W.mem(x, W.sigsp(ss, es, List.append(&2, R.End, Y, R.new_ends(xs, 0n)))) == False{} : Bool}:
  match x:
    case W.Pt{+m, +r}:
      +hl1 = hlx
      not_in_vq(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, m, r, hox, slot_not(ss, ks, a, b, m, r, hok, kl.ne(R.nat_eq(a, m), ks, a, m, r, {==}, hl1, hA), kl.ne(R.nat_eq(b, m), ks, b, m, r, {==}, hl1, hB), hl1))

def cnq.go(cm: Bool, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +x: W.Pt, he: {W.mem(x, W.sigsp(ss, es, R.ends(ls))) == cm : Bool}, hno: {W.mem(x, W.sigsp(ss, es, List.append(&2, R.End, Y, R.new_ends(xs, 0n)))) == False{} : Bool}) -> {cm == False{} : Bool}:
  match cm:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MNat.internal_false_ne_true(Equal.trans(Bool, False{}, W.mem(x, W.sigsp(ss, es, List.append(&2, R.End, Y, R.new_ends(xs, 0n)))), True{},
        Equal.sym(Bool, W.mem(x, W.sigsp(ss, es, List.append(&2, R.End, Y, R.new_ends(xs, 0n)))), False{}, hno), sigs_subp(ss, es, R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n)), hin, x, he))))
    case False{}:
      {==}

def c_out_nq(C2: List<&2, W.Pt>, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, hl2: {W.all_live(ks, C2) == True{} : Bool}, ho: {all_out(C2, W.sigsp(ss, es, Y)) == True{} : Bool},
  hoa: {all_out(C2, W.ports(a, R.arity(W.kind_at(ks, a)))) == True{} : Bool}, hob: {all_out(C2, W.ports(b, R.arity(W.kind_at(ks, b)))) == True{} : Bool}) -> {all_out(C2, W.sigsp(ss, es, R.ends(ls))) == True{} : Bool}:
  match C2:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hl2 = hl2
      +ho = ho
      +hoa = hoa
      +hob = hob
      and_i(Bool.not(W.mem(x, W.sigsp(ss, es, R.ends(ls)))), all_out(t, W.sigsp(ss, es, R.ends(ls))),
        not_false(W.mem(x, W.sigsp(ss, es, R.ends(ls))), cnq.go(W.mem(x, W.sigsp(ss, es, R.ends(ls))), ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, x, {==},
          cnq.x(x, ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, and_l(W.live(ks, x), W.all_live(ks, t), hl2), not_true(W.mem(x, W.sigsp(ss, es, Y)), and_l(Bool.not(W.mem(x, W.sigsp(ss, es, Y))), all_out(t, W.sigsp(ss, es, Y)), ho)),
            not_true(W.mem(x, W.ports(a, R.arity(W.kind_at(ks, a)))), and_l(Bool.not(W.mem(x, W.ports(a, R.arity(W.kind_at(ks, a))))), all_out(t, W.ports(a, R.arity(W.kind_at(ks, a)))), hoa)), not_true(W.mem(x, W.ports(b, R.arity(W.kind_at(ks, b)))), and_l(Bool.not(W.mem(x, W.ports(b, R.arity(W.kind_at(ks, b))))), all_out(t, W.ports(b, R.arity(W.kind_at(ks, b)))), hob))))),
        c_out_nq(t, ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, and_r(W.live(ks, x), W.all_live(ks, t), hl2), and_r(Bool.not(W.mem(x, W.sigsp(ss, es, Y))), all_out(t, W.sigsp(ss, es, Y)), ho),
          and_r(Bool.not(W.mem(x, W.ports(a, R.arity(W.kind_at(ks, a))))), all_out(t, W.ports(a, R.arity(W.kind_at(ks, a)))), hoa), and_r(Bool.not(W.mem(x, W.ports(b, R.arity(W.kind_at(ks, b))))), all_out(t, W.ports(b, R.arity(W.kind_at(ks, b)))), hob)))

def g_nodupq(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}) -> {W.nodup(List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  +nec = qd_nec(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)
  nodup_cat(W.ends(c), W.sigsp(ss, es, R.ends(ls)), nodup_r(W.sigsp(ss, es, Y), W.ends(c), nec), nodup_sigsq(R.ends(ls), ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, hin, hd),
    c_out_nq(W.ends(c), ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, live_r(ks, W.sigsp(ss, es, Y), W.ends(c), qd_lec(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)), out_sym(W.sigsp(ss, es, Y), W.ends(c), nodup_out(W.sigsp(ss, es, Y), W.ends(c), nec)),
      out_snd(W.sigsp(ss, es, Y), W.ends(c), W.ports(a, R.arity(W.kind_at(ks, a))), qd_oa(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)), out_snd(W.sigsp(ss, es, Y), W.ends(c), W.ports(b, R.arity(W.kind_at(ks, b))), qd_ob(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall))))

# Goal two: every end live
def live_cq(C2: List<&2, W.Pt>, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, hl2: {W.all_live(ks, C2) == True{} : Bool}, oa: {all_out(C2, W.ports(a, R.arity(W.kind_at(ks, a)))) == True{} : Bool}, ob: {all_out(C2, W.ports(b, R.arity(W.kind_at(ks, b)))) == True{} : Bool}) ->
  {W.all_live(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), C2) == True{} : Bool}:
  match C2:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hl2 = hl2
      +oa = oa
      +ob = ob
      and_i(W.live(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), x), W.all_live(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), t),
        keepq(x, ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, and_l(W.live(ks, x), W.all_live(ks, t), hl2), not_true(W.mem(x, W.ports(a, R.arity(W.kind_at(ks, a)))), and_l(Bool.not(W.mem(x, W.ports(a, R.arity(W.kind_at(ks, a))))), all_out(t, W.ports(a, R.arity(W.kind_at(ks, a)))), oa)),
          not_true(W.mem(x, W.ports(b, R.arity(W.kind_at(ks, b)))), and_l(Bool.not(W.mem(x, W.ports(b, R.arity(W.kind_at(ks, b))))), all_out(t, W.ports(b, R.arity(W.kind_at(ks, b)))), ob))),
        live_cq(t, ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, and_r(W.live(ks, x), W.all_live(ks, t), hl2), and_r(Bool.not(W.mem(x, W.ports(a, R.arity(W.kind_at(ks, a))))), all_out(t, W.ports(a, R.arity(W.kind_at(ks, a)))), oa), and_r(Bool.not(W.mem(x, W.ports(b, R.arity(W.kind_at(ks, b))))), all_out(t, W.ports(b, R.arity(W.kind_at(ks, b)))), ob)))

def live_oneq(x: R.End, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, hx: {R.end_mem(x, List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}) -> {W.live(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.sigp(ss, es, x)) == True{} : Bool}:
  match x:
    case R.Ext{+i}:
      +hq = mem_sigs_ofp(ss, es, R.Ext{i}, Y, ext_in_Y(i, Y, xs, hx))
      keepq(W.sigp(ss, es, R.Ext{i}), ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, live_at(W.sigsp(ss, es, Y), ks, W.sigp(ss, es, R.Ext{i}), live_l(ks, W.sigsp(ss, es, Y), W.ends(c), qd_lec(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)), hq),
        out_at(W.sigsp(ss, es, Y), W.ports(a, R.arity(W.kind_at(ks, a))), W.sigp(ss, es, R.Ext{i}), out_fst(W.sigsp(ss, es, Y), W.ends(c), W.ports(a, R.arity(W.kind_at(ks, a))), qd_oa(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)), hq),
        out_at(W.sigsp(ss, es, Y), W.ports(b, R.arity(W.kind_at(ks, b))), W.sigp(ss, es, R.Ext{i}), out_fst(W.sigsp(ss, es, Y), W.ends(c), W.ports(b, R.arity(W.kind_at(ks, b))), qd_ob(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)), hq))
    case R.New{+j, +p}:
      +hnn = new_in_new_g(j, p, Y, xs, hY, hx)
      live_newq(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, j, p, new_j_lt(xs, j, p, hnn), new_live(xs, 0n, j, p, hnn))

def live_nq(Xs: List<&2, R.End>, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, h: {R.all_in(Xs, List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}) -> {W.all_live(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.sigsp(ss, es, Xs)) == True{} : Bool}:
  match Xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h = h
      and_i(W.live(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.sigp(ss, es, x)), W.all_live(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.sigsp(ss, es, t)),
        live_oneq(x, ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, and_l(R.end_mem(x, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), R.all_in(t, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), h)), live_nq(t, ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, and_r(R.end_mem(x, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), R.all_in(t, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), h)))

def g_liveq(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}) -> {W.all_live(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  live_cat(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.ends(c), W.sigsp(ss, es, R.ends(ls)), live_cq(W.ends(c), ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, live_r(ks, W.sigsp(ss, es, Y), W.ends(c), qd_lec(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)), out_snd(W.sigsp(ss, es, Y), W.ends(c), W.ports(a, R.arity(W.kind_at(ks, a))), qd_oa(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall)), out_snd(W.sigsp(ss, es, Y), W.ends(c), W.ports(b, R.arity(W.kind_at(ks, b))), qd_ob(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall))),
    live_nq(R.ends(ls), ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, hin))

# Goal three: every live port present
def port_trq.go(cE: Bool, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +q: W.Pt, he: {W.mem(q, W.sigsp(ss, es, Y)) == cE : Bool}, hm: {(cE || W.mem(q, W.ends(c))) == True{} : Bool}) -> {W.mem(q, List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  match cE:
    case True{}:
      mem_ir(q, W.ends(c), W.sigsp(ss, es, R.ends(ls)), sigs_subp(ss, es, Y, R.ends(ls), qd_xl(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall), q, he))
    case False{}:
      mem_il(q, W.ends(c), W.sigsp(ss, es, R.ends(ls)), hm)

def port_trq(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +m: Nat, +p: Nat, hm: {W.mem(W.Pt{m, p}, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, hma: {R.nat_eq(a, m) == False{} : Bool}, hmb: {R.nat_eq(b, m) == False{} : Bool}) ->
  {W.mem(W.Pt{m, p}, List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  +h2 = mem_res(W.Pt{m, p}, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c)), mem_res(W.Pt{m, p}, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))), hm, ports_not(a, R.arity(W.kind_at(ks, a)), m, p, hma)), ports_not(b, R.arity(W.kind_at(ks, b)), m, p, hmb))
  port_trq.go(W.mem(W.Pt{m, p}, W.sigsp(ss, es, Y)), ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, W.Pt{m, p}, {==}, mem_or(W.Pt{m, p}, W.sigsp(ss, es, Y), W.ends(c), h2))

def transferq(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +m: Nat, kk: Nat, h: {W.ports_in(m, kk, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hma: {R.nat_eq(a, m) == False{} : Bool}, +hmb: {R.nat_eq(b, m) == False{} : Bool}) ->
  {W.ports_in(m, kk, List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  match kk:
    case 0n:
      {==}
    case 1n++p:
      +h = h
      and_i(W.mem(W.Pt{m, p}, List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))), W.ports_in(m, p, List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))), port_trq(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, m, p, and_l(W.mem(W.Pt{m, p}, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))), W.ports_in(m, p, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))), h), hma, hmb),
        transferq(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, m, p, and_r(W.mem(W.Pt{m, p}, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))), W.ports_in(m, p, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))), h), hma, hmb))

def cq_old.go(cc: Bool, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +m: Nat, he: {W.below(m, List.length(&2, R.NodeKind, ks)) == cc : Bool}, hma: {R.nat_eq(a, m) == False{} : Bool}, hmb: {R.nat_eq(b, m) == False{} : Bool}) ->
  {W.ports_in(m, R.arity(W.kind_at(ks, m)), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  match cc:
    case True{}:
      transferq(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, m, R.arity(W.kind_at(ks, m)), cov_at(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c)))), m, he, hc), hma, hmb)
    case False{}:
      %Equal.sym(R.NodeKind, W.kind_at(ks, m), R.KFree{}, ka_past(ks, m, he)) : {W.ports_in(m, R.arity(_), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}
      {==}

def cq_a.go(cc: Bool, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +m: Nat, he: {R.nat_eq(a, m) == cc : Bool}, hmb: {R.nat_eq(b, m) == False{} : Bool}) ->
  {W.ports_in(m, R.arity(W.kind_at(W.set(ks, a, R.KFree{}), m)), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  match cc:
    case True{}:
      %neq_eq(a, m, he) : {W.ports_in(m, R.arity(W.kind_at(W.set(ks, a, R.KFree{}), _)), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}
      %Equal.sym(R.NodeKind, W.kind_at(W.set(ks, a, R.KFree{}), a), R.KFree{}, ka_free(ks, a)) : {W.ports_in(m, R.arity(_), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}
      {==}
    case False{}:
      +he = he
      %Equal.sym(R.NodeKind, W.kind_at(W.set(ks, a, R.KFree{}), m), W.kind_at(ks, m), ka_ne(ks, a, R.KFree{}, m, he)) : {W.ports_in(m, R.arity(_), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}
      cq_old.go(W.below(m, List.length(&2, R.NodeKind, ks)), ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, m, {==}, he, hmb)

def cq_b.go(cc: Bool, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +m: Nat, he: {R.nat_eq(b, m) == cc : Bool}) -> {W.ports_in(m, R.arity(W.kind_at(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), m)), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  match cc:
    case True{}:
      %neq_eq(b, m, he) : {W.ports_in(m, R.arity(W.kind_at(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), _)), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}
      %Equal.sym(R.NodeKind, W.kind_at(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), b), R.KFree{}, ka_free(W.set(ks, a, R.KFree{}), b)) : {W.ports_in(m, R.arity(_), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}
      {==}
    case False{}:
      +he = he
      %Equal.sym(R.NodeKind, W.kind_at(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), m), W.kind_at(W.set(ks, a, R.KFree{}), m), ka_ne(W.set(ks, a, R.KFree{}), b, R.KFree{}, m, he)) : {W.ports_in(m, R.arity(_), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}
      cq_a.go(R.nat_eq(a, m), ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, m, {==}, he)

def cq_off(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +m: Nat, hnm: {W.nat_in(m, ss) == False{} : Bool}) -> {W.ports_in(m, R.arity(W.kind_at(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), m)), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  %Equal.sym(R.NodeKind, W.kind_at(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), m), W.kind_at(W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), m), pl_off(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs), m, hnm)) : {W.ports_in(m, R.arity(_), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}
  cq_b.go(R.nat_eq(b, m), ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, m, {==})

def new_memq(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +j: Nat, +p: Nat, hb: {W.below(p, R.arity(W.kind_at(W.kinds(xs), j))) == True{} : Bool}) -> {W.mem(W.Pt{W.nth(ss, j), p}, List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  mem_ir(W.Pt{W.nth(ss, j), p}, W.ends(c), W.sigsp(ss, es, R.ends(ls)), mem_sigs_ofp(ss, es, R.New{j, p}, R.ends(ls), in_at(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls), R.New{j, p}, hall,
    emem_ir(R.New{j, p}, Y, R.new_ends(xs, 0n), new_in(xs, 0n, j, p, hb)))))

def cq_newp(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +j: Nat, kk: Nat, hk: {W.below(kk, 1n+R.arity(W.kind_at(W.kinds(xs), j))) == True{} : Bool}) -> {W.ports_in(W.nth(ss, j), kk, List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  match kk:
    case 0n:
      {==}
    case 1n++p:
      +hk = hk
      and_i(W.mem(W.Pt{W.nth(ss, j), p}, List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))), W.ports_in(W.nth(ss, j), p, List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))), new_memq(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, j, p, hk),
        cq_newp(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, j, p, below_succ(R.arity(W.kind_at(W.kinds(xs), j)), p, hk)))

def cq_onj(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +j: Nat, +hj: {W.below(j, List.length(&2, Nat, ss)) == True{} : Bool}) -> {W.ports_in(W.nth(ss, j), R.arity(W.kind_at(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.nth(ss, j))), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  %Equal.sym(R.NodeKind, W.kind_at(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), W.nth(ss, j)), W.kind_at(W.kinds(xs), j), pl_at(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs), j, hss, hj, bl_back(ss, W.kinds(xs), j, hlen, hj))) : {W.ports_in(W.nth(ss, j), R.arity(_), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}
  cq_newp(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, j, R.arity(W.kind_at(W.kinds(xs), j)), below_self(R.arity(W.kind_at(W.kinds(xs), j))))

def cq_on(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +m: Nat, +hinm: {W.nat_in(m, ss) == True{} : Bool}) -> {W.ports_in(m, R.arity(W.kind_at(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), m)), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  %neq_eq(W.nth(ss, pos(ss, m)), m, pos_nth(ss, m, hinm)) : {W.ports_in(_, R.arity(W.kind_at(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), _)), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}
  cq_onj(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, pos(ss, m), pos_lt(ss, m, hinm))

def cq_m.go(cc: Bool, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, +m: Nat, he: {W.nat_in(m, ss) == cc : Bool}) -> {W.ports_in(m, R.arity(W.kind_at(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), m)), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  match cc:
    case True{}:
      cq_on(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, m, he)
    case False{}:
      cq_off(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, m, he)

def cov_allq(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}, n: Nat) -> {W.covered(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), n, List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      and_i(W.ports_in(m, R.arity(W.kind_at(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), m)), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))), W.covered(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), m, List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))), cq_m.go(W.nat_in(m, ss), ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, m, {==}), cov_allq(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, m))

def rw.goq(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}, +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hn: {W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hl: {W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hc: {W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool}, +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}) -> {W.wired(W.rp_kinds(ks, a, b, ss, xs), W.ends(W.rp_links(es, c, ss, ls))) == True{} : Bool}:
  %Equal.sym(List<&2, W.Pt>, W.ends(List.append(&2, W.Ln, c, W.linksp(ss, es, ls))), List.append(&2, W.Pt, W.ends(c), W.ends(W.linksp(ss, es, ls))), ends_app(c, W.linksp(ss, es, ls))) : {W.wired(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), _) == True{} : Bool}
  %Equal.sym(List<&2, W.Pt>, W.ends(W.linksp(ss, es, ls)), W.sigsp(ss, es, R.ends(ls)), ends_linksp(ss, es, ls)) : {W.wired(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.append(&2, W.Pt, W.ends(c), _)) == True{} : Bool}
  and_i(W.nodup(List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))), (W.all_live(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))) && W.covered(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.length(&2, R.NodeKind, W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs))), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls))))), g_nodupq(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall),
    and_i(W.all_live(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))), W.covered(W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.length(&2, R.NodeKind, W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs))), List.append(&2, W.Pt, W.ends(c), W.sigsp(ss, es, R.ends(ls)))), g_liveq(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall), cov_allq(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen, hn, hl, hc, hd, hin, hall, List.length(&2, R.NodeKind, W.place(ss, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs))))))

# the rewrite, its new nodes in any distinct slots each the pair's own or
# free, keeps the net wired
def wired_place(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +ss: List<&2, Nat>, +hY: {all_ext(Y) == True{} : Bool}, +hss: {W.nodup_nat(ss) == True{} : Bool}, +hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool},
  +hlen: {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}, +hw: {W.wired(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) == True{} : Bool},
  +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}) ->
  {W.wired(W.rp_kinds(ks, a, b, ss, xs), W.ends(W.rp_links(es, c, ss, ls))) == True{} : Bool}:
  rw.goq(ks, a, b, es, c, xs, ls, Y, ss, hY, hss, hok, hlen,
    and_l(W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))), (W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) && W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c)))))), hw),
    and_l(W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))), W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))), and_r(W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))), (W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) && W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c)))))), hw)),
    and_r(W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))), W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))), and_r(W.nodup(List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))), (W.all_live(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c))))) && W.covered(ks, List.length(&2, R.NodeKind, ks), List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(ss, es, Y), W.ends(c)))))), hw)),
    hd, hin, hall)


# The appended placement
# ======================

def set_ext_end(K: List<&2, R.NodeKind>, +v: R.NodeKind) -> {W.set_ext(List.length(&2, R.NodeKind, K), K, v) == List.append(&2, R.NodeKind, K, [v]) : List<&2, R.NodeKind>}:
  match K:
    case Nil{}:
      {==}
    case Con{+k, +t}:
      %set_ext_end(t, v) : {Con{k, W.set_ext(List.length(&2, R.NodeKind, t), t, v)} == Con{k, _} : List<&2, R.NodeKind>}
      {==}

def kapp_assoc(A: List<&2, R.NodeKind>, +B: List<&2, R.NodeKind>, +C: List<&2, R.NodeKind>) ->
  {List.append(&2, R.NodeKind, List.append(&2, R.NodeKind, A, B), C) == List.append(&2, R.NodeKind, A, List.append(&2, R.NodeKind, B, C)) : List<&2, R.NodeKind>}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %kapp_assoc(t, B, C) : {Con{x, List.append(&2, R.NodeKind, List.append(&2, R.NodeKind, t, B), C)} == Con{x, _} : List<&2, R.NodeKind>}
      {==}

def len_snoc(K: List<&2, R.NodeKind>, +v: R.NodeKind) -> {List.length(&2, R.NodeKind, List.append(&2, R.NodeKind, K, [v])) == 1n+List.length(&2, R.NodeKind, K) : Nat}:
  match K:
    case Nil{}:
      {==}
    case Con{+k, +t}:
      %len_snoc(t, v) : {1n+List.length(&2, R.NodeKind, List.append(&2, R.NodeKind, t, [v])) == 1n+_ : Nat}
      {==}

def app_nil(K: List<&2, R.NodeKind>) -> {List.append(&2, R.NodeKind, K, Nil{}) == K : List<&2, R.NodeKind>}:
  match K:
    case Nil{}:
      {==}
    case Con{+k, +t}:
      %app_nil(t) : {Con{k, List.append(&2, R.NodeKind, t, Nil{})} == Con{k, _} : List<&2, R.NodeKind>}
      {==}


# placing kx at the slots past K's end appends it
def place_range.go(kx: List<&2, R.NodeKind>, +K: List<&2, R.NodeKind>, +n0: Nat, e: {List.length(&2, R.NodeKind, K) == n0 : Nat}) ->
  {W.place(W.range(List.length(&2, R.NodeKind, kx), n0), K, kx) == List.append(&2, R.NodeKind, K, kx) : List<&2, R.NodeKind>}:
  match kx:
    case Nil{}:
      %Equal.sym(List<&2, R.NodeKind>, List.append(&2, R.NodeKind, K, Nil{}), K, app_nil(K)) : {W.place(Nil{}, K, Nil{}) == _ : List<&2, R.NodeKind>}
      {==}
    case Con{+k, +kt}:
      +e = e
      %e : {W.place(W.range(List.length(&2, R.NodeKind, kt), 1n+_), W.set_ext(_, K, k), kt) == List.append(&2, R.NodeKind, K, Con{k, kt}) : List<&2, R.NodeKind>}
      %Equal.sym(List<&2, R.NodeKind>, W.set_ext(List.length(&2, R.NodeKind, K), K, k), List.append(&2, R.NodeKind, K, [k]), set_ext_end(K, k)) : {W.place(W.range(List.length(&2, R.NodeKind, kt), 1n+List.length(&2, R.NodeKind, K)), _, kt) == List.append(&2, R.NodeKind, K, Con{k, kt}) : List<&2, R.NodeKind>}
      %kapp_assoc(K, [k], kt) : {W.place(W.range(List.length(&2, R.NodeKind, kt), 1n+List.length(&2, R.NodeKind, K)), List.append(&2, R.NodeKind, K, [k]), kt) == _ : List<&2, R.NodeKind>}
      place_range.go(kt, List.append(&2, R.NodeKind, K, [k]), 1n+List.length(&2, R.NodeKind, K), len_snoc(K, k))

def nth_range(k: Nat, +n0: Nat, j: Nat, h: {W.below(j, k) == True{} : Bool}) -> {W.nth(W.range(k, n0), j) == Nat.add(n0, j) : Nat}:
  match k j:
    case 0n _:
      ft(h, {W.nth(W.range(0n, n0), j) == Nat.add(n0, j) : Nat})
    case 1n+r 0n:
      %Equal.sym(Nat, Nat.add(n0, 0n), n0, add_zero(n0)) : {n0 == _ : Nat}
      {==}
    case 1n+r 1n++i:
      %Equal.sym(Nat, Nat.add(n0, 1n+i), 1n+Nat.add(n0, i), succ_add(n0, i)) : {W.nth(W.range(r, 1n+n0), i) == _ : Nat}
      nth_range(r, 1n+n0, i, h)

def range_len(k: Nat, +n0: Nat) -> {List.length(&2, Nat, W.range(k, n0)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++r:
      %Equal.sym(Nat, List.length(&2, Nat, W.range(r, 1n+n0)), r, range_len(r, 1n+n0)) : {1n+_ == 1n+r : Nat}
      {==}

# a slot of range k n0 is at least n0
def range_ge(k: Nat, +n0: Nat, +m: Nat, h: {W.below(m, n0) == True{} : Bool}) -> {W.nat_in(m, W.range(k, n0)) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++r:
      +h = h
      or_f(R.nat_eq(n0, m), W.nat_in(m, W.range(r, 1n+n0)), below_ne(n0, m, h), range_ge(r, 1n+n0, m, below_succ(n0, m, h)))

def range_nodup(k: Nat, +n0: Nat) -> {W.nodup_nat(W.range(k, n0)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++r:
      and_i(Bool.not(W.nat_in(n0, W.range(r, 1n+n0))), W.nodup_nat(W.range(r, 1n+n0)), not_false(W.nat_in(n0, W.range(r, 1n+n0)), range_ge(r, 1n+n0, n0, below_self(n0))), range_nodup(r, 1n+n0))

def below_le_self(n: Nat) -> {W.below(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      below_le_self(k)

def below_up(n: Nat, +m: Nat, h: {W.below(m, n) == False{} : Bool}) -> {W.below(1n+m, n) == False{} : Bool}:
  match n m:
    case 0n _:
      {==}
    case 1n+k 0n:
      tf(h, {W.below(1n, 1n+k) == False{} : Bool})
    case 1n+k 1n+q:
      below_up(k, q, h)

# the slots past ks's end are free
def range_ok(k: Nat, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +n0: Nat, h: {W.below(n0, List.length(&2, R.NodeKind, ks)) == False{} : Bool}) ->
  {W.slots_ok(ks, a, b, W.range(k, n0)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++r:
      +h = h
      and_i((R.nat_eq(n0, a) || (R.nat_eq(n0, b) || W.is_free_kind(W.kind_at(ks, n0)))), W.slots_ok(ks, a, b, W.range(r, 1n+n0)),
        or_r(R.nat_eq(n0, a), (R.nat_eq(n0, b) || W.is_free_kind(W.kind_at(ks, n0))), or_r(R.nat_eq(n0, b), W.is_free_kind(W.kind_at(ks, n0)),
          Equal.cong(R.NodeKind, Bool, W.is_free_kind, W.kind_at(ks, n0), R.KFree{}, ka_past(ks, n0, h)))),
        range_ok(r, ks, a, b, 1n+n0, below_up(List.length(&2, R.NodeKind, ks), n0, h)))

# an Ext end lands where its peer is, wherever new nodes are placed
def sigs_ext(Y: List<&2, R.End>, +n0: Nat, +es: W.Peers, +ss: List<&2, Nat>, hY: {all_ext(Y) == True{} : Bool}) -> {W.sigs(n0, es, Y) == W.sigsp(ss, es, Y) : List<&2, W.Pt>}:
  match Y:
    case Nil{}:
      {==}
    case Con{R.Ext{+i}, +t}:
      %sigs_ext(t, n0, es, ss, hY) : {Con{W.peer(i, es), W.sigs(n0, es, t)} == Con{W.peer(i, es), _} : List<&2, W.Pt>}
      {==}
    case Con{R.New{j, p}, t}:
      ft(hY, {W.sigs(n0, es, Con{R.New{j, p}, t}) == W.sigsp(ss, es, Con{R.New{j, p}, t}) : List<&2, W.Pt>})

# appended and placed by range, a must-link end lands alike
def sig_range(x: R.End, +n0: Nat, +es: W.Peers, +xs: List<&2, R.Spec>, +Y: List<&2, R.End>, +hY: {all_ext(Y) == True{} : Bool},
  hx: {R.end_mem(x, List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}) ->
  {W.sig(n0, es, x) == W.sigp(W.range(List.length(&2, R.NodeKind, W.kinds(xs)), n0), es, x) : W.Pt}:
  match x:
    case R.Ext{i}:
      {==}
    case R.New{+j, +p}:
      %Equal.sym(Nat, W.nth(W.range(List.length(&2, R.NodeKind, W.kinds(xs)), n0), j), Nat.add(n0, j),
        nth_range(List.length(&2, R.NodeKind, W.kinds(xs)), n0, j, new_j_lt(xs, j, p, new_in_new_g(j, p, Y, xs, hY, hx)))) : {W.Pt{Nat.add(n0, j), p} == W.Pt{_, p} : W.Pt}
      {==}

def sigs_range(X: List<&2, R.End>, +n0: Nat, +es: W.Peers, +xs: List<&2, R.Spec>, +Y: List<&2, R.End>, +hY: {all_ext(Y) == True{} : Bool},
  h: {R.all_in(X, List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}) ->
  {W.sigs(n0, es, X) == W.sigsp(W.range(List.length(&2, R.NodeKind, W.kinds(xs)), n0), es, X) : List<&2, W.Pt>}:
  match X:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h = h
      %sig_range(x, n0, es, xs, Y, hY, and_l(R.end_mem(x, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), R.all_in(t, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), h)) :
        {Con{W.sig(n0, es, x), W.sigs(n0, es, t)} == Con{_, W.sigsp(W.range(List.length(&2, R.NodeKind, W.kinds(xs)), n0), es, t)} : List<&2, W.Pt>}
      %sigs_range(t, n0, es, xs, Y, hY, and_r(R.end_mem(x, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), R.all_in(t, List.append(&2, R.End, Y, R.new_ends(xs, 0n))), h)) :
        {Con{W.sig(n0, es, x), W.sigs(n0, es, t)} == Con{W.sig(n0, es, x), _} : List<&2, W.Pt>}
      {==}

def wa_hw(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +hY: {all_ext(Y) == True{} : Bool}, hw: {W.wired(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, Y), W.ends(c))))) == True{} : Bool}) -> {W.wired(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigsp(W.range(List.length(&2, R.NodeKind, W.kinds(xs)), List.length(&2, R.NodeKind, ks)), es, Y), W.ends(c))))) == True{} : Bool}:
  %sigs_ext(Y, List.length(&2, R.NodeKind, ks), es, W.range(List.length(&2, R.NodeKind, W.kinds(xs)), List.length(&2, R.NodeKind, ks)), hY) : {W.wired(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, _, W.ends(c))))) == True{} : Bool}
  hw

# rewrite_wired's appended nodes are one placement: range(k, n0), the
# slots past the end
def wired_app(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +Y: List<&2, R.End>, +hY: {all_ext(Y) == True{} : Bool}, +hw: {W.wired(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, Y), W.ends(c))))) == True{} : Bool},
  +hd: {R.ends_distinct(R.ends(ls)) == True{} : Bool}, +hin: {R.all_in(R.ends(ls), List.append(&2, R.End, Y, R.new_ends(xs, 0n))) == True{} : Bool}, +hall: {R.all_in(List.append(&2, R.End, Y, R.new_ends(xs, 0n)), R.ends(ls)) == True{} : Bool}) ->
  {W.wired(W.rw_kinds(ks, a, b, xs), W.ends(W.rw_links(ks, es, c, ls))) == True{} : Bool}:
  %place_range.go(W.kinds(xs), W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), List.length(&2, R.NodeKind, ks), len_k1(ks, a, b)) : {W.wired(_, W.ends(List.append(&2, W.Ln, c, W.links(List.length(&2, R.NodeKind, ks), es, ls)))) == True{} : Bool}
  %Equal.sym(List<&2, W.Pt>, W.ends(List.append(&2, W.Ln, c, W.links(List.length(&2, R.NodeKind, ks), es, ls))), List.append(&2, W.Pt, W.ends(c), W.ends(W.links(List.length(&2, R.NodeKind, ks), es, ls))), ends_app(c, W.links(List.length(&2, R.NodeKind, ks), es, ls))) : {W.wired(W.place(W.range(List.length(&2, R.NodeKind, W.kinds(xs)), List.length(&2, R.NodeKind, ks)), W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), _) == True{} : Bool}
  %Equal.sym(List<&2, W.Pt>, W.ends(W.links(List.length(&2, R.NodeKind, ks), es, ls)), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)), ends_links(List.length(&2, R.NodeKind, ks), es, ls)) : {W.wired(W.place(W.range(List.length(&2, R.NodeKind, W.kinds(xs)), List.length(&2, R.NodeKind, ks)), W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.append(&2, W.Pt, W.ends(c), _)) == True{} : Bool}
  %Equal.sym(List<&2, W.Pt>, W.sigs(List.length(&2, R.NodeKind, ks), es, R.ends(ls)), W.sigsp(W.range(List.length(&2, R.NodeKind, W.kinds(xs)), List.length(&2, R.NodeKind, ks)), es, R.ends(ls)), sigs_range(R.ends(ls), List.length(&2, R.NodeKind, ks), es, xs, Y, hY, hin)) : {W.wired(W.place(W.range(List.length(&2, R.NodeKind, W.kinds(xs)), List.length(&2, R.NodeKind, ks)), W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.append(&2, W.Pt, W.ends(c), _)) == True{} : Bool}
  %ends_linksp(W.range(List.length(&2, R.NodeKind, W.kinds(xs)), List.length(&2, R.NodeKind, ks)), es, ls) : {W.wired(W.place(W.range(List.length(&2, R.NodeKind, W.kinds(xs)), List.length(&2, R.NodeKind, ks)), W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), List.append(&2, W.Pt, W.ends(c), _)) == True{} : Bool}
  %ends_app(c, W.linksp(W.range(List.length(&2, R.NodeKind, W.kinds(xs)), List.length(&2, R.NodeKind, ks)), es, ls)) : {W.wired(W.place(W.range(List.length(&2, R.NodeKind, W.kinds(xs)), List.length(&2, R.NodeKind, ks)), W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.kinds(xs)), _) == True{} : Bool}
  wired_place(ks, a, b, es, c, xs, ls, Y, W.range(List.length(&2, R.NodeKind, W.kinds(xs)), List.length(&2, R.NodeKind, ks)), hY, range_nodup(List.length(&2, R.NodeKind, W.kinds(xs)), List.length(&2, R.NodeKind, ks)),
    range_ok(List.length(&2, R.NodeKind, W.kinds(xs)), ks, a, b, List.length(&2, R.NodeKind, ks), below_le_self(List.length(&2, R.NodeKind, ks))), range_len(List.length(&2, R.NodeKind, W.kinds(xs)), List.length(&2, R.NodeKind, ks)),
    wa_hw(ks, a, b, es, c, xs, ls, Y, hY, hw), hd, hin, hall)

def oinot(x: Bool, y: Bool, h: {(x || Bool.not(y)) == True{} : Bool}, hy: {y == True{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ne_tf(Equal.trans(Bool, True{}, y, False{}, Equal.sym(Bool, y, True{}, hy), not_true(y, h))))

# the pattern's own clause of exact_pairs
def pinst(p: R.Pat, +a: R.NodeKind, +b: R.NodeKind, +r: R.Rule, h: {R.exact_pairs(a, b, r) == True{} : Bool}, hv: {R.pat_ok(a, b, p) == True{} : Bool}) ->
  {R.exact_in(a, b, p, r) == True{} : Bool}:
  match p:
    case R.PNone{}:
      oinot(R.exact_in(a, b, R.PNone{}, r), R.pat_ok(a, b, R.PNone{}), and_l((R.exact_in(a, b, R.PNone{}, r) || Bool.not(R.pat_ok(a, b, R.PNone{}))), ((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))) && ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))))), h), hv)
    case R.P01{}:
      oinot(R.exact_in(a, b, R.P01{}, r), R.pat_ok(a, b, R.P01{}), and_l((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))), ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))))), and_r((R.exact_in(a, b, R.PNone{}, r) || Bool.not(R.pat_ok(a, b, R.PNone{}))), ((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))) && ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))))), h)), hv)
    case R.P02{}:
      oinot(R.exact_in(a, b, R.P02{}, r), R.pat_ok(a, b, R.P02{}), and_l((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))), ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))), and_r((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))), ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))))), and_r((R.exact_in(a, b, R.PNone{}, r) || Bool.not(R.pat_ok(a, b, R.PNone{}))), ((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))) && ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))))), h))), hv)
    case R.P03{}:
      oinot(R.exact_in(a, b, R.P03{}, r), R.pat_ok(a, b, R.P03{}), and_l((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))), ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))), and_r((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))), ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))), and_r((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))), ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))))), and_r((R.exact_in(a, b, R.PNone{}, r) || Bool.not(R.pat_ok(a, b, R.PNone{}))), ((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))) && ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))))), h)))), hv)
    case R.P12{}:
      oinot(R.exact_in(a, b, R.P12{}, r), R.pat_ok(a, b, R.P12{}), and_l((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))), ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))), and_r((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))), ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))), and_r((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))), ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))), and_r((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))), ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))))), and_r((R.exact_in(a, b, R.PNone{}, r) || Bool.not(R.pat_ok(a, b, R.PNone{}))), ((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))) && ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))))), h))))), hv)
    case R.P13{}:
      oinot(R.exact_in(a, b, R.P13{}, r), R.pat_ok(a, b, R.P13{}), and_l((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))), ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))), and_r((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))), ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))), and_r((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))), ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))), and_r((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))), ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))), and_r((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))), ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))))), and_r((R.exact_in(a, b, R.PNone{}, r) || Bool.not(R.pat_ok(a, b, R.PNone{}))), ((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))) && ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))))), h)))))), hv)
    case R.P23{}:
      oinot(R.exact_in(a, b, R.P23{}, r), R.pat_ok(a, b, R.P23{}), and_l((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))), ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))), and_r((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))), ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))), and_r((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))), ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))), and_r((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))), ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))), and_r((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))), ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))), and_r((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))), ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))))), and_r((R.exact_in(a, b, R.PNone{}, r) || Bool.not(R.pat_ok(a, b, R.PNone{}))), ((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))) && ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))))), h))))))), hv)
    case R.P01_23{}:
      oinot(R.exact_in(a, b, R.P01_23{}, r), R.pat_ok(a, b, R.P01_23{}), and_l((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))), ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))), and_r((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))), ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))), and_r((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))), ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))), and_r((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))), ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))), and_r((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))), ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))), and_r((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))), ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))), and_r((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))), ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))))), and_r((R.exact_in(a, b, R.PNone{}, r) || Bool.not(R.pat_ok(a, b, R.PNone{}))), ((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))) && ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))))), h)))))))), hv)
    case R.P02_13{}:
      oinot(R.exact_in(a, b, R.P02_13{}, r), R.pat_ok(a, b, R.P02_13{}), and_l((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))), (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))), and_r((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))), ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))), and_r((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))), ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))), and_r((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))), ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))), and_r((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))), ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))), and_r((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))), ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))), and_r((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))), ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))), and_r((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))), ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))))), and_r((R.exact_in(a, b, R.PNone{}, r) || Bool.not(R.pat_ok(a, b, R.PNone{}))), ((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))) && ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))))), h))))))))), hv)
    case R.P03_12{}:
      oinot(R.exact_in(a, b, R.P03_12{}, r), R.pat_ok(a, b, R.P03_12{}), and_r((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))), (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))), and_r((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))), ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))), and_r((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))), ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))), and_r((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))), ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))), and_r((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))), ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))), and_r((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))), ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))), and_r((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))), ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))), and_r((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))), ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{})))))))))), and_r((R.exact_in(a, b, R.PNone{}, r) || Bool.not(R.pat_ok(a, b, R.PNone{}))), ((R.exact_in(a, b, R.P01{}, r) || Bool.not(R.pat_ok(a, b, R.P01{}))) && ((R.exact_in(a, b, R.P02{}, r) || Bool.not(R.pat_ok(a, b, R.P02{}))) && ((R.exact_in(a, b, R.P03{}, r) || Bool.not(R.pat_ok(a, b, R.P03{}))) && ((R.exact_in(a, b, R.P12{}, r) || Bool.not(R.pat_ok(a, b, R.P12{}))) && ((R.exact_in(a, b, R.P13{}, r) || Bool.not(R.pat_ok(a, b, R.P13{}))) && ((R.exact_in(a, b, R.P23{}, r) || Bool.not(R.pat_ok(a, b, R.P23{}))) && ((R.exact_in(a, b, R.P01_23{}, r) || Bool.not(R.pat_ok(a, b, R.P01_23{}))) && ((R.exact_in(a, b, R.P02_13{}, r) || Bool.not(R.pat_ok(a, b, R.P02_13{}))) && (R.exact_in(a, b, R.P03_12{}, r) || Bool.not(R.pat_ok(a, b, R.P03_12{}))))))))))), h))))))))), hv)

def eapp_assoc(A: List<&2, R.End>, +B: List<&2, R.End>, +C: List<&2, R.End>) -> {List.append(&2, R.End, List.append(&2, R.End, A, B), C) == List.append(&2, R.End, A, List.append(&2, R.End, B, C)) : List<&2, R.End>}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %eapp_assoc(t, B, C) : {Con{x, List.append(&2, R.End, List.append(&2, R.End, t, B), C)} == Con{x, _} : List<&2, R.End>}
      {==}

def hy0(+ka: R.NodeKind, +kb: R.NodeKind) -> {all_ext(R.ext_ends(ka, kb)) == True{} : Bool}:
  ext_cat(W.aux_a(ka), W.aux_b(kb), aux_ext(Nat.sub(R.arity(ka), 1n), 0n), aux_ext(Nat.sub(R.arity(kb), 1n), 2n))

# the focus with every peer outside, its peers placed as one list
def tr_hw0(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, hw: {W.wired(ks, W.fends(W.Foc{ks, a, b, es, c})) == True{} : Bool}) -> {W.wired(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), W.ends(c))))) == True{} : Bool}:
  %Equal.trans(List<&2, W.Pt>, List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c))), List.append(&2, W.Pt, List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b)))), W.ends(c)), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), W.ends(c)),
    Equal.sym(List<&2, W.Pt>, List.append(&2, W.Pt, List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b)))), W.ends(c)), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c))), app_assoc(W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b))), W.ends(c))),
    Equal.cong(List<&2, W.Pt>, List<&2, W.Pt>, (z => List.append(&2, W.Pt, z, W.ends(c))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b)))), W.sigs(List.length(&2, R.NodeKind, ks), es, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))),
      Equal.sym(List<&2, W.Pt>, W.sigs(List.length(&2, R.NodeKind, ks), es, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), List.append(&2, W.Pt, W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a))), W.sigs(List.length(&2, R.NodeKind, ks), es, W.aux_b(W.kind_at(ks, b)))), sigs_app(List.length(&2, R.NodeKind, ks), es, W.aux_a(W.kind_at(ks, a)), W.aux_b(W.kind_at(ks, b)))))) : {W.wired(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), _))) == True{} : Bool}
  hw

def tr_in0(+ka: R.NodeKind, +kb: R.NodeKind, +xs: List<&2, R.Spec>, +L: List<&2, R.End>, h: {R.all_in(L, R.expected(ka, kb, xs)) == True{} : Bool}) ->
  {R.all_in(L, List.append(&2, R.End, R.ext_ends(ka, kb), R.new_ends(xs, 0n))) == True{} : Bool}:
  %Equal.sym(List<&2, R.End>, List.append(&2, R.End, R.ext_ends(ka, kb), R.new_ends(xs, 0n)), R.expected(ka, kb, xs), eapp_assoc(W.aux_a(ka), W.aux_b(kb), R.new_ends(xs, 0n))) : {R.all_in(L, _) == True{} : Bool}
  h

def tr_all0(+ka: R.NodeKind, +kb: R.NodeKind, +xs: List<&2, R.Spec>, +L: List<&2, R.End>, h: {R.all_in(R.expected(ka, kb, xs), L) == True{} : Bool}) ->
  {R.all_in(List.append(&2, R.End, R.ext_ends(ka, kb), R.new_ends(xs, 0n)), L) == True{} : Bool}:
  %Equal.sym(List<&2, R.End>, List.append(&2, R.End, R.ext_ends(ka, kb), R.new_ends(xs, 0n)), R.expected(ka, kb, xs), eapp_assoc(W.aux_a(ka), W.aux_b(kb), R.new_ends(xs, 0n))) : {R.all_in(_, L) == True{} : Bool}
  h

# rewrite_wired: the peers all outside
def rw_wired(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +hw: {W.wired(ks, W.fends(W.Foc{ks, a, b, es, c})) == True{} : Bool},
  +hr: {R.exact(W.kind_at(ks, a), W.kind_at(ks, b), R.RWire{xs, ls}) == True{} : Bool}) -> {W.wired(W.rw_kinds(ks, a, b, xs), W.ends(W.rw_links(ks, es, c, ls))) == True{} : Bool}:
  wired_app(ks, a, b, es, c, xs, ls, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b)), hy0(W.kind_at(ks, a), W.kind_at(ks, b)), tr_hw0(ks, a, b, es, c, xs, ls, hw),
    and_l(R.ends_distinct(R.ends(ls)), (R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) && R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls))), hr),
    tr_in0(W.kind_at(ks, a), W.kind_at(ks, b), xs, R.ends(ls), and_l(R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)), R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)), and_r(R.ends_distinct(R.ends(ls)), (R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) && R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls))), hr))),
    tr_all0(W.kind_at(ks, a), W.kind_at(ks, b), xs, R.ends(ls), and_r(R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)), R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls)), and_r(R.ends_distinct(R.ends(ls)), (R.all_in(R.ends(ls), R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs)) && R.all_in(R.expected(W.kind_at(ks, a), W.kind_at(ks, b), xs), R.ends(ls))), hr))))

# the kernel's links under pattern p, exact by exact_in
def ein(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +p: R.Pat, +ls2: List<&2, R.Link>, hc: {R.contract(p, ls) == Some{ls2} : Maybe<&2, List<&2, R.Link>>},
  hr: {R.exact_in(W.kind_at(ks, a), W.kind_at(ks, b), p, R.RWire{xs, ls}) == True{} : Bool}) -> {R.exact_in.m(Some{ls2}, W.kind_at(ks, a), W.kind_at(ks, b), p, xs) == True{} : Bool}:
  %hc : {R.exact_in.m(_, W.kind_at(ks, a), W.kind_at(ks, b), p, xs) == True{} : Bool}
  hr

# a peer inside the pair: the rewrite by the links the kernel makes keeps
# the net wired, the outside peers those the pattern leaves
def wired_in(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +p: R.Pat, +ls2: List<&2, R.Link>, +hw: {W.wired(ks, W.fends_in(W.Foc{ks, a, b, es, c}, p)) == True{} : Bool},
  hc: {R.contract(p, ls) == Some{ls2} : Maybe<&2, List<&2, R.Link>>}, hr: {R.exact_in(W.kind_at(ks, a), W.kind_at(ks, b), p, R.RWire{xs, ls}) == True{} : Bool}) ->
  {W.wired(W.rw_kinds(ks, a, b, xs), W.ends(W.rw_links(ks, es, c, ls2))) == True{} : Bool}:
  +he = ein(ks, a, b, es, c, xs, ls, p, ls2, hc, hr)
  wired_app(ks, a, b, es, c, xs, ls2, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), outer_ext(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b)), hy0(W.kind_at(ks, a), W.kind_at(ks, b))), hw,
    and_l(R.ends_distinct(R.ends(ls2)), (R.all_in(R.ends(ls2), List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n))) && R.all_in(List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n)), R.ends(ls2))), he),
    and_l(R.all_in(R.ends(ls2), List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n))), R.all_in(List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n)), R.ends(ls2)), and_r(R.ends_distinct(R.ends(ls2)), (R.all_in(R.ends(ls2), List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n))) && R.all_in(List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n)), R.ends(ls2))), he)),
    and_r(R.all_in(R.ends(ls2), List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n))), R.all_in(List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n)), R.ends(ls2)), and_r(R.ends_distinct(R.ends(ls2)), (R.all_in(R.ends(ls2), List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n))) && R.all_in(List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n)), R.ends(ls2))), he)))

def kw.m(m: Maybe<&2, List<&2, R.Link>>, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +xs: List<&2, R.Spec>, +ls: List<&2, R.Link>, +p: R.Pat, hm: {R.contract(p, ls) == m : Maybe<&2, List<&2, R.Link>>},
  +hw: {W.wired(ks, W.fends_in(W.Foc{ks, a, b, es, c}, p)) == True{} : Bool}, hr: {R.exact_in(W.kind_at(ks, a), W.kind_at(ks, b), p, R.RWire{xs, ls}) == True{} : Bool}) ->
  {W.keeps_wired.m(m, ks, a, b, es, c, xs) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ls2}:
      wired_in(ks, a, b, es, c, xs, ls, p, ls2, hw, hm, hr)

def kw.r(r: R.Rule, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +p: R.Pat,
  +hw: {W.wired(ks, W.fends_in(W.Foc{ks, a, b, es, c}, p)) == True{} : Bool}, hr: {R.exact_in(W.kind_at(ks, a), W.kind_at(ks, b), p, r) == True{} : Bool}) ->
  {W.keeps_wired(ks, a, b, es, c, r, p) == True{} : Bool}:
  match r:
    case R.RWire{+xs, +ls}:
      kw.m(R.contract(p, ls), ks, a, b, es, c, xs, ls, p, {==}, hw, hr)
    case R.RStuck{}:
      {==}

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

def Laws.rewrite_pairs_wired(ks, a, b, es, c, xs, ls, p, ls2, hw, hc, hr):
  wired_in(ks, a, b, es, c, xs, ls, p, ls2, hw, hc, hr)

def Laws.rules_keep_wired_in(ks, a, b, es, c, s, p, hv, hw):
  kw.r(R.rule(W.kind_at(ks, a), W.kind_at(ks, b), s), ks, a, b, es, c, p, hw,
    pinst(p, W.kind_at(ks, a), W.kind_at(ks, b), R.rule(W.kind_at(ks, a), W.kind_at(ks, b), s), Laws.rules_pairs_exact(W.kind_at(ks, a), W.kind_at(ks, b), s), hv))

# by cases: under every pattern, each rule a constant the checker computes
def Laws.rules_pairs_total(a, b, s):
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
      {==}



    case R.KCopyL{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
      {==}
# by cases again: under every pattern, each rule a constant the checker
# computes

def len_kinds(xs: List<&2, R.Spec>) -> {List.length(&2, R.NodeKind, W.kinds(xs)) == List.length(&2, R.Spec, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{R.Spec{k, s}, t}:
      %len_kinds(t) : {1n+List.length(&2, R.NodeKind, W.kinds(t)) == 1n+_ : Nat}
      {==}

def len_tr(+ss: List<&2, Nat>, +xs: List<&2, R.Spec>, h: {List.length(&2, Nat, ss) == List.length(&2, R.Spec, xs) : Nat}) ->
  {List.length(&2, Nat, ss) == List.length(&2, R.NodeKind, W.kinds(xs)) : Nat}:
  Equal.trans(Nat, List.length(&2, Nat, ss), List.length(&2, R.Spec, xs), List.length(&2, R.NodeKind, W.kinds(xs)), h, Equal.sym(Nat, List.length(&2, R.NodeKind, W.kinds(xs)), List.length(&2, R.Spec, xs), len_kinds(xs)))

def wp_hw(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +es: W.Peers, +c: List<&2, W.Ln>, +p: R.Pat, +ss: List<&2, Nat>,
  hw: {W.wired(ks, W.fends_in(W.Foc{ks, a, b, es, c}, p)) == True{} : Bool}) ->
  {W.wired(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))),
    List.append(&2, W.Pt, W.sigsp(ss, es, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b)))), W.ends(c))))) == True{} : Bool}:
  %sigs_ext(R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), List.length(&2, R.NodeKind, ks), es, ss,
    outer_ext(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b)), hy0(W.kind_at(ks, a), W.kind_at(ks, b)))) :
    {W.wired(ks, List.append(&2, W.Pt, W.ports(a, R.arity(W.kind_at(ks, a))), List.append(&2, W.Pt, W.ports(b, R.arity(W.kind_at(ks, b))), List.append(&2, W.Pt, _, W.ends(c))))) == True{} : Bool}
  hw

def Laws.rewrite_placed_wired(ks, a, b, es, c, xs, ls, p, ls2, ss, hw, hc, hr, hss, hok, hlen):
  +he = ein(ks, a, b, es, c, xs, ls, p, ls2, hc, hr)
  wired_place(ks, a, b, es, c, xs, ls2, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), ss,
    outer_ext(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b)), hy0(W.kind_at(ks, a), W.kind_at(ks, b))), hss, hok, len_tr(ss, xs, hlen), wp_hw(ks, a, b, es, c, p, ss, hw),
    and_l(R.ends_distinct(R.ends(ls2)), (R.all_in(R.ends(ls2), List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n))) && R.all_in(List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n)), R.ends(ls2))), he),
    and_l(R.all_in(R.ends(ls2), List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n))), R.all_in(List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n)), R.ends(ls2)), and_r(R.ends_distinct(R.ends(ls2)), (R.all_in(R.ends(ls2), List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n))) && R.all_in(List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n)), R.ends(ls2))), he)),
    and_r(R.all_in(R.ends(ls2), List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n))), R.all_in(List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n)), R.ends(ls2)), and_r(R.ends_distinct(R.ends(ls2)), (R.all_in(R.ends(ls2), List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n))) && R.all_in(List.append(&2, R.End, R.outer(p, R.ext_ends(W.kind_at(ks, a), W.kind_at(ks, b))), R.new_ends(xs, 0n)), R.ends(ls2))), he)))

# The kernel's placement
# ======================
#
# Over kplace.bend: the free-list model's notions bridged to the wiring
# model's, the allocations as the ghost list's first entries, then the
# placement's conditions and the free list after.

def same_nat(a: Nat, b: Nat) -> {FL.same(a, b) == R.nat_eq(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      same_nat(x, y)

def fmem_nat(+i: Nat, l: List<&2, Nat>) -> {FL.mem(i, l) == W.nat_in(i, l) : Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Bool, FL.same(i, j), R.nat_eq(j, i), Equal.trans(Bool, FL.same(i, j), R.nat_eq(i, j), R.nat_eq(j, i), same_nat(i, j), neq_comm(i, j))) : {(_ || FL.mem(i, t)) == (R.nat_eq(j, i) || W.nat_in(i, t)) : Bool}
      %Equal.sym(Bool, FL.mem(i, t), W.nat_in(i, t), fmem_nat(i, t)) : {(R.nat_eq(j, i) || _) == (R.nat_eq(j, i) || W.nat_in(i, t)) : Bool}
      {==}

def fnodup_nat(l: List<&2, Nat>) -> {FL.nodup(l) == W.nodup_nat(l) : Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Bool, FL.mem(j, t), W.nat_in(j, t), fmem_nat(j, t)) : {(Bool.not(_) && FL.nodup(t)) == (Bool.not(W.nat_in(j, t)) && W.nodup_nat(t)) : Bool}
      %Equal.sym(Bool, FL.nodup(t), W.nodup_nat(t), fnodup_nat(t)) : {(Bool.not(W.nat_in(j, t)) && _) == (Bool.not(W.nat_in(j, t)) && W.nodup_nat(t)) : Bool}
      {==}

# the first n of l
def take(n: Nat, l: List<&2, Nat>) -> List<&2, Nat>:
  match n l:
    case 0n _:
      Nil{}
    case 1n+m Nil{}:
      Nil{}
    case 1n+m Con{j, t}:
      j <> take(m, t)

def tk_out(n: Nat, l: List<&2, Nat>, +x: Nat, h: {W.nat_in(x, l) == False{} : Bool}) -> {W.nat_in(x, take(n, l)) == False{} : Bool}:
  match n l:
    case 0n _:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n++m Con{+j, +t}:
      +h = h
      or_f(R.nat_eq(j, x), W.nat_in(x, take(m, t)), or_false_l(R.nat_eq(j, x), W.nat_in(x, t), h), tk_out(m, t, x, or_false_r(R.nat_eq(j, x), W.nat_in(x, t), h)))

def tk_nodup(n: Nat, l: List<&2, Nat>, h: {W.nodup_nat(l) == True{} : Bool}) -> {W.nodup_nat(take(n, l)) == True{} : Bool}:
  match n l:
    case 0n _:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n++m Con{+j, +t}:
      +h = h
      and_i(Bool.not(W.nat_in(j, take(m, t))), W.nodup_nat(take(m, t)),
        not_false(W.nat_in(j, take(m, t)), tk_out(m, t, j, not_true(W.nat_in(j, t), and_l(Bool.not(W.nat_in(j, t)), W.nodup_nat(t), h)))),
        tk_nodup(m, t, and_r(Bool.not(W.nat_in(j, t)), W.nodup_nat(t), h)))

def tk_len(n: Nat, l: List<&2, Nat>, h: {KP.has(n, l) == True{} : Bool}) -> {List.length(&2, Nat, take(n, l)) == n : Nat}:
  match n l:
    case 0n _:
      {==}
    case 1n+m Nil{}:
      ft(h, {List.length(&2, Nat, take(1n+m, Nil{})) == 1n+m : Nat})
    case 1n++m Con{j, t}:
      %Equal.sym(Nat, List.length(&2, Nat, take(m, t)), m, tk_len(m, t, h)) : {1n+_ == 1n+m : Nat}
      {==}

def same_b_t(a: Bool, +b: Bool, h: {KP.same_b(a, b) == True{} : Bool}, ha: {a == True{} : Bool}) -> {b == True{} : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      h
    case False{} _:
      ft(ha, {b == True{} : Bool})

def same_b_f(+a: Bool, b: Bool, h: {KP.same_b(a, b) == True{} : Bool}, hb: {b == False{} : Bool}) -> {a == False{} : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case True{} False{}:
      ft(h, {True{} == False{} : Bool})
    case _ True{}:
      tf(hb, {a == False{} : Bool})

# a slot free in the free list has a free kind
def free_kind(s: List<&2, FL.Slot>, ks: List<&2, R.NodeKind>, i: Nat, hs: {KP.in_step(s, ks) == True{} : Bool}, hf: {FL.is_free(FL.get(s, i)) == True{} : Bool}) ->
  {W.is_free_kind(W.kind_at(ks, i)) == True{} : Bool}:
  match s ks i:
    case Nil{} Nil{} _:
      ft(hf, {W.is_free_kind(W.kind_at(Nil{}, i)) == True{} : Bool})
    case Nil{} Con{k, u} _:
      ft(hs, {W.is_free_kind(W.kind_at(Con{k, u}, i)) == True{} : Bool})
    case Con{x, t} Nil{} _:
      ft(hs, {W.is_free_kind(W.kind_at(Nil{}, i)) == True{} : Bool})
    case Con{+x, +t} Con{+k, +u} 0n:
      +hs = hs
      same_b_t(FL.is_free(x), W.is_free_kind(k), and_l(KP.same_b(FL.is_free(x), W.is_free_kind(k)), KP.in_step(t, u), hs), hf)
    case Con{+x, +t} Con{+k, +u} 1n+q:
      free_kind(t, u, q, and_r(KP.same_b(FL.is_free(x), W.is_free_kind(k)), KP.in_step(t, u), hs), hf)

# a slot whose kind is live is in use in the free list
def live_use(s: List<&2, FL.Slot>, ks: List<&2, R.NodeKind>, i: Nat, hs: {KP.in_step(s, ks) == True{} : Bool}, hk: {W.is_free_kind(W.kind_at(ks, i)) == False{} : Bool}) ->
  {FL.in_use(s, i) == True{} : Bool}:
  match s ks i:
    case Nil{} Nil{} _:
      tf(hk, {FL.in_use(Nil{}, i) == True{} : Bool})
    case Nil{} Con{k, u} _:
      ft(hs, {FL.in_use(Nil{}, i) == True{} : Bool})
    case Con{x, t} Nil{} _:
      ft(hs, {FL.in_use(Con{x, t}, i) == True{} : Bool})
    case Con{+x, +t} Con{+k, +u} 0n:
      +hs = hs
      not_false(FL.is_free(x), same_b_f(FL.is_free(x), W.is_free_kind(k), and_l(KP.same_b(FL.is_free(x), W.is_free_kind(k)), KP.in_step(t, u), hs), hk))
    case Con{+x, +t} Con{+k, +u} 1n+q:
      live_use(t, u, q, and_r(KP.same_b(FL.is_free(x), W.is_free_kind(k)), KP.in_step(t, u), hs), hk)

def ga.go(c: FL.Slot, +s: List<&2, FL.Slot>, +j: Nat, +t: List<&2, Nat>, he: {FL.get(s, j) == c : FL.Slot}, hf: {FL.is_free(FL.get(s, j)) == True{} : Bool}) ->
  {KP.ghost(FL.alloc.go(c, s, j, Con{j, t})) == t : List<&2, Nat>}:
  match c:
    case FL.Used{}:
      Empty.absurd({KP.ghost(FL.alloc.go(FL.Used{}, s, j, Con{j, t})) == t : List<&2, Nat>}, MNat.internal_false_ne_true(
        Equal.trans(Bool, False{}, FL.is_free(FL.get(s, j)), True{}, Equal.cong(FL.Slot, Bool, FL.is_free, FL.Used{}, FL.get(s, j), Equal.sym(FL.Slot, FL.get(s, j), FL.Used{}, he)), hf)))
    case FL.Free{n}:
      {==}

# allocating from an exact list drops its head from the ghost
def ghost_alloc(+s: List<&2, FL.Slot>, +j: Nat, +t: List<&2, Nat>, hok: {FL.ok(FL.FL{s, 1n+j, Con{j, t}}) == True{} : Bool}) ->
  {KP.ghost(FL.alloc(FL.FL{s, 1n+j, Con{j, t}})) == t : List<&2, Nat>}:
  ga.go(FL.get(s, j), s, j, t, {==}, fl_head(s, j, Con{j, t}, hok))

def ok_tr(+s: List<&2, FL.Slot>, +fh: Nat, +j: Nat, +l: List<&2, Nat>, eq: {fh == 1n+j : Nat}, h: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}) ->
  {FL.ok(FL.FL{s, 1n+j, l}) == True{} : Bool}:
  %eq : {FL.ok(FL.FL{s, _, l}) == True{} : Bool}
  h

def has_tr(+m: Nat, +s: List<&2, FL.Slot>, +j: Nat, +t: List<&2, Nat>, hok: {FL.ok(FL.FL{s, 1n+j, Con{j, t}}) == True{} : Bool}, h: {KP.has(m, t) == True{} : Bool}) ->
  {KP.has(m, KP.ghost(FL.alloc(FL.FL{s, 1n+j, Con{j, t}}))) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, KP.ghost(FL.alloc(FL.FL{s, 1n+j, Con{j, t}})), t, ghost_alloc(s, j, t, hok)) : {KP.has(m, _) == True{} : Bool}
  h

def at.k(+s: List<&2, FL.Slot>, +fh: Nat, +j: Nat, +t: List<&2, Nat>, +m: Nat, +eq: {fh == 1n+j : Nat}, hf: {FL.ok(FL.FL{s, fh, Con{j, t}}) == True{} : Bool},
  hh: {KP.has(m, t) == True{} : Bool},
  ih: {FL.ok(FL.alloc(FL.FL{s, 1n+j, Con{j, t}})) == True{} : Bool} -> {KP.has(m, KP.ghost(FL.alloc(FL.FL{s, 1n+j, Con{j, t}}))) == True{} : Bool} ->
    {KP.allocs(m, FL.alloc(FL.FL{s, 1n+j, Con{j, t}})) == take(m, KP.ghost(FL.alloc(FL.FL{s, 1n+j, Con{j, t}}))) : List<&2, Nat>}) ->
  {KP.allocs(1n+m, FL.FL{s, fh, Con{j, t}}) == Con{j, take(m, t)} : List<&2, Nat>}:
  +hf2 = ok_tr(s, fh, j, Con{j, t}, eq, hf)
  %Equal.sym(Nat, fh, 1n+j, eq) : {KP.allocs(1n+m, FL.FL{s, _, Con{j, t}}) == Con{j, take(m, t)} : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, KP.allocs(m, FL.alloc(FL.FL{s, 1n+j, Con{j, t}})), take(m, KP.ghost(FL.alloc(FL.FL{s, 1n+j, Con{j, t}}))),
    ih(fl_alloc(FL.FL{s, 1n+j, Con{j, t}}, hf2), has_tr(m, s, j, t, hf2, hh))) : {Con{j, _} == Con{j, take(m, t)} : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, KP.ghost(FL.alloc(FL.FL{s, 1n+j, Con{j, t}})), t, ghost_alloc(s, j, t, hf2)) : {Con{j, take(m, _)} == Con{j, take(m, t)} : List<&2, Nat>}
  {==}

# n allocations from an exact list holding n take its first n
def allocs_take(n: Nat, f: FL.FL, hf: {FL.ok(f) == True{} : Bool}, hh: {KP.has(n, KP.ghost(f)) == True{} : Bool}) ->
  {KP.allocs(n, f) == take(n, KP.ghost(f)) : List<&2, Nat>}:
  match n f:
    case 0n _:
      {==}
    case 1n++m FL.FL{+s, +fh, l}:
      match l:
        case Nil{}:
          ft(hh, {KP.allocs(1n+m, FL.FL{s, fh, Nil{}}) == take(1n+m, KP.ghost(FL.FL{s, fh, Nil{}})) : List<&2, Nat>})
        case Con{+j, +t}:
          +hf = hf
          at.k(s, fh, j, t, m, same_eq(fh, 1n+j, and_l(FL.same(fh, 1n+j), (FL.is_free(FL.get(s, j)) && FL.walks(t, s, FL.next_of(FL.get(s, j)))), ok_w(s, fh, Con{j, t}, hf))),
            hf, hh, h1 => h2 => allocs_take(m, FL.alloc(FL.FL{s, 1n+j, Con{j, t}}), h1, h2))

# the ghost's first n slots have free kinds
def tk_slots(n: Nat, l: List<&2, Nat>, +s: List<&2, FL.Slot>, x: Nat, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, hw: {FL.walks(l, s, x) == True{} : Bool},
  +hs: {KP.in_step(s, ks) == True{} : Bool}) -> {W.slots_ok(ks, a, b, take(n, l)) == True{} : Bool}:
  match n l:
    case 0n _:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n++m Con{+j, +t}:
      +hr = and_r(FL.same(x, 1n+j), (FL.is_free(FL.get(s, j)) && FL.walks(t, s, FL.next_of(FL.get(s, j)))), hw)
      and_i((R.nat_eq(j, a) || (R.nat_eq(j, b) || W.is_free_kind(W.kind_at(ks, j)))), W.slots_ok(ks, a, b, take(m, t)),
        or_r(R.nat_eq(j, a), (R.nat_eq(j, b) || W.is_free_kind(W.kind_at(ks, j))), or_r(R.nat_eq(j, b), W.is_free_kind(W.kind_at(ks, j)),
          free_kind(s, ks, j, hs, and_l(FL.is_free(FL.get(s, j)), FL.walks(t, s, FL.next_of(FL.get(s, j))), hr)))),
        tk_slots(m, t, s, FL.next_of(FL.get(s, j)), ks, a, b, and_r(FL.is_free(FL.get(s, j)), FL.walks(t, s, FL.next_of(FL.get(s, j))), hr), hs))

# a live node's slot is on no exact free list
def live_off(+s: List<&2, FL.Slot>, +fh: Nat, +l: List<&2, Nat>, +ks: List<&2, R.NodeKind>, +i: Nat, hf: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool},
  hs: {KP.in_step(s, ks) == True{} : Bool}, hk: {W.is_free_kind(W.kind_at(ks, i)) == False{} : Bool}) -> {W.nat_in(i, l) == False{} : Bool}:
  Equal.trans(Bool, W.nat_in(i, l), FL.mem(i, l), False{}, Equal.sym(Bool, FL.mem(i, l), W.nat_in(i, l), fmem_nat(i, l)),
    walks_not_mem(l, s, fh, i, ok_w(s, fh, l, hf), in_use_not_free(s, i, live_use(s, ks, i, hs, hk))))

def len2_ok(+a: Nat, +b: Nat, +m: Nat, +l: List<&2, Nat>, h: {KP.has(m, l) == True{} : Bool}) ->
  {R.nat_eq(List.length(&2, Nat, Con{a, Con{b, take(m, l)}}), 2n+m) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Nat, take(m, l)), m, tk_len(m, l, h)) : {R.nat_eq(2n+_, 2n+m) == True{} : Bool}
  neq_refl(m)

def ksok2(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, +m: Nat, +s: List<&2, FL.Slot>, +fh: Nat, +l: List<&2, Nat>, +hf: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool},
  +hs: {KP.in_step(s, ks) == True{} : Bool}, +hab: {R.nat_eq(a, b) == False{} : Bool}, hla: {W.is_free_kind(W.kind_at(ks, a)) == False{} : Bool},
  hlb: {W.is_free_kind(W.kind_at(ks, b)) == False{} : Bool}, +hen: {KP.has(m, l) == True{} : Bool}) ->
  {(W.nodup_nat(Con{a, Con{b, take(m, l)}}) && (W.slots_ok(ks, a, b, Con{a, Con{b, take(m, l)}}) && R.nat_eq(List.length(&2, Nat, Con{a, Con{b, take(m, l)}}), 2n+m))) == True{} : Bool}:
  +ha = live_off(s, fh, l, ks, a, hf, hs, hla)
  +hb = live_off(s, fh, l, ks, b, hf, hs, hlb)
  and_i(W.nodup_nat(Con{a, Con{b, take(m, l)}}), (W.slots_ok(ks, a, b, Con{a, Con{b, take(m, l)}}) && R.nat_eq(List.length(&2, Nat, Con{a, Con{b, take(m, l)}}), 2n+m)),
    and_i(Bool.not(W.nat_in(a, Con{b, take(m, l)})), W.nodup_nat(Con{b, take(m, l)}),
      not_false(W.nat_in(a, Con{b, take(m, l)}), or_f(R.nat_eq(b, a), W.nat_in(a, take(m, l)), Equal.trans(Bool, R.nat_eq(b, a), R.nat_eq(a, b), False{}, neq_comm(b, a), hab), tk_out(m, l, a, ha))),
      and_i(Bool.not(W.nat_in(b, take(m, l))), W.nodup_nat(take(m, l)), not_false(W.nat_in(b, take(m, l)), tk_out(m, l, b, hb)),
        tk_nodup(m, l, Equal.trans(Bool, W.nodup_nat(l), FL.nodup(l), True{}, Equal.sym(Bool, FL.nodup(l), W.nodup_nat(l), fnodup_nat(l)), ok_n(s, fh, l, hf))))),
    and_i(W.slots_ok(ks, a, b, Con{a, Con{b, take(m, l)}}), R.nat_eq(List.length(&2, Nat, Con{a, Con{b, take(m, l)}}), 2n+m),
      and_i((R.nat_eq(a, a) || (R.nat_eq(a, b) || W.is_free_kind(W.kind_at(ks, a)))), W.slots_ok(ks, a, b, Con{b, take(m, l)}),
        or_l(R.nat_eq(a, a), (R.nat_eq(a, b) || W.is_free_kind(W.kind_at(ks, a))), neq_refl(a)),
        and_i((R.nat_eq(b, a) || (R.nat_eq(b, b) || W.is_free_kind(W.kind_at(ks, b)))), W.slots_ok(ks, a, b, take(m, l)),
          or_r(R.nat_eq(b, a), (R.nat_eq(b, b) || W.is_free_kind(W.kind_at(ks, b))), or_l(R.nat_eq(b, b), W.is_free_kind(W.kind_at(ks, b)), neq_refl(b))),
          tk_slots(m, l, s, fh, ks, a, b, ok_w(s, fh, l, hf), hs))),
      len2_ok(a, b, m, l, hen)))

def sub_zero(m: Nat) -> {Nat.sub(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      {==}

def has_sub(+m: Nat, +l: List<&2, Nat>, h: {KP.has(Nat.sub(m, 0n), l) == True{} : Bool}) -> {KP.has(m, l) == True{} : Bool}:
  %sub_zero(m) : {KP.has(_, l) == True{} : Bool}
  h

# the kernel's slots meet the placement law's conditions
def ksok(+ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, k: Nat, +s: List<&2, FL.Slot>, +fh: Nat, +l: List<&2, Nat>, +hf: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool},
  +hs: {KP.in_step(s, ks) == True{} : Bool}, +hab: {R.nat_eq(a, b) == False{} : Bool}, hla: {W.is_free_kind(W.kind_at(ks, a)) == False{} : Bool},
  hlb: {W.is_free_kind(W.kind_at(ks, b)) == False{} : Bool}, hen: {KP.has(Nat.sub(k, 2n), l) == True{} : Bool}) ->
  {KP.kslots_ok(ks, a, b, k, FL.FL{s, fh, l}) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n:
      and_i(W.nodup_nat([a]), (W.slots_ok(ks, a, b, [a]) && R.nat_eq(1n, 1n)), {==},
        and_i(W.slots_ok(ks, a, b, [a]), R.nat_eq(1n, 1n),
          and_i((R.nat_eq(a, a) || (R.nat_eq(a, b) || W.is_free_kind(W.kind_at(ks, a)))), W.slots_ok(ks, a, b, Nil{}),
            or_l(R.nat_eq(a, a), (R.nat_eq(a, b) || W.is_free_kind(W.kind_at(ks, a))), neq_refl(a)), {==}), {==}))
    case 2n++m:
      +hen = has_sub(m, l, hen)
      %Equal.sym(List<&2, Nat>, KP.allocs(m, FL.FL{s, fh, l}), take(m, l), allocs_take(m, FL.FL{s, fh, l}, hf, hen)) :
        {(W.nodup_nat(Con{a, Con{b, _}}) && (W.slots_ok(ks, a, b, Con{a, Con{b, _}}) && R.nat_eq(List.length(&2, Nat, Con{a, Con{b, _}}), 2n+m))) == True{} : Bool}
      ksok2(ks, a, b, m, s, fh, l, hf, hs, hab, hla, hlb, hen)

def after_ok(n: Nat, +f: FL.FL, hf: {FL.ok(f) == True{} : Bool}) -> {FL.ok(KP.after(n, f)) == True{} : Bool}:
  match n:
    case 0n:
      hf
    case 1n+m:
      after_ok(m, FL.alloc(f), fl_alloc(f, hf))

def in_use_ne(s: List<&2, FL.Slot>, i: Nat, +v: FL.Slot, j: Nat, h: {FL.same(i, j) == False{} : Bool}) -> {FL.in_use(FL.set(s, i, v), j) == FL.in_use(s, j) : Bool}:
  match s i j:
    case Nil{} _ _:
      {==}
    case Con{c, t} 0n 0n:
      tf(h, {FL.in_use(FL.set(Con{c, t}, 0n, v), 0n) == FL.in_use(Con{c, t}, 0n) : Bool})
    case Con{c, t} 0n 1n+k:
      {==}
    case Con{c, t} 1n+m 0n:
      {==}
    case Con{c, t} 1n+m 1n+k:
      in_use_ne(t, m, v, k, h)

# the free list after the kernel's placement is exact
def kfok(+a: Nat, +b: Nat, k: Nat, +s: List<&2, FL.Slot>, +fh: Nat, +l: List<&2, Nat>, +ks: List<&2, R.NodeKind>, +hf: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool},
  +hs: {KP.in_step(s, ks) == True{} : Bool}, hab: {R.nat_eq(a, b) == False{} : Bool}, hla: {W.is_free_kind(W.kind_at(ks, a)) == False{} : Bool},
  hlb: {W.is_free_kind(W.kind_at(ks, b)) == False{} : Bool}) -> {FL.ok(KP.kfree(a, b, k, FL.FL{s, fh, l})) == True{} : Bool}:
  match k:
    case 0n:
      fl_free(FL.set(s, b, FL.Free{fh}), 1n+b, Con{b, l}, a,
        Equal.trans(Bool, FL.in_use(FL.set(s, b, FL.Free{fh}), a), FL.in_use(s, a), True{},
          in_use_ne(s, b, FL.Free{fh}, a, Equal.trans(Bool, FL.same(b, a), R.nat_eq(b, a), False{}, same_nat(b, a), Equal.trans(Bool, R.nat_eq(b, a), R.nat_eq(a, b), False{}, neq_comm(b, a), hab))),
          live_use(s, ks, a, hs, hla)),
        fl_free(s, fh, l, b, live_use(s, ks, b, hs, hlb), hf))
    case 1n:
      fl_free(s, fh, l, b, live_use(s, ks, b, hs, hlb), hf)
    case 2n+m:
      after_ok(m, FL.FL{s, fh, l}, hf)


def Laws.kernel_slots_ok(s, fh, l, ks, a, b, k, hf, hs, hab, hla, hlb, hen):
  ksok(ks, a, b, k, s, fh, l, hf, hs, hab, hla, hlb, hen)

def Laws.kernel_free_ok(s, fh, l, ks, a, b, k, hf, hs, hab, hla, hlb):
  kfok(a, b, k, s, fh, l, ks, hf, hs, hab, hla, hlb)

def Laws.kernel_rewrite_wired(ks, a, b, es, c, xs, ls, p, ls2, s, fh, l, hw, hc, hr, hf, hs, hab, hla, hlb, hen):
  +ko = ksok(ks, a, b, List.length(&2, R.Spec, xs), s, fh, l, hf, hs, hab, hla, hlb, hen)
  Laws.rewrite_placed_wired(ks, a, b, es, c, xs, ls, p, ls2, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l}), hw, hc, hr,
    and_l(W.nodup_nat(KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})), (W.slots_ok(ks, a, b, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})) && R.nat_eq(List.length(&2, Nat, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})), List.length(&2, R.Spec, xs))), ko),
    and_l(W.slots_ok(ks, a, b, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})), R.nat_eq(List.length(&2, Nat, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})), List.length(&2, R.Spec, xs)), and_r(W.nodup_nat(KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})), (W.slots_ok(ks, a, b, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})) && R.nat_eq(List.length(&2, Nat, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})), List.length(&2, R.Spec, xs))), ko)),
    neq_eq(List.length(&2, Nat, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})), List.length(&2, R.Spec, xs), and_r(W.slots_ok(ks, a, b, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})), R.nat_eq(List.length(&2, Nat, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})), List.length(&2, R.Spec, xs)), and_r(W.nodup_nat(KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})), (W.slots_ok(ks, a, b, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})) && R.nat_eq(List.length(&2, Nat, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})), List.length(&2, R.Spec, xs))), ko))))

# The two models stay in step
# ---------------------------

def pair_set(s: List<&2, FL.Slot>, ks: List<&2, R.NodeKind>, i: Nat, +v: FL.Slot, +k: R.NodeKind, hs: {KP.in_step(s, ks) == True{} : Bool},
  +hp: {KP.same_b(FL.is_free(v), W.is_free_kind(k)) == True{} : Bool}) -> {KP.in_step(FL.set(s, i, v), W.set(ks, i, k)) == True{} : Bool}:
  match s ks i:
    case Nil{} Nil{} _:
      {==}
    case Nil{} Con{k0, u} _:
      ft(hs, {KP.in_step(FL.set(Nil{}, i, v), W.set(Con{k0, u}, i, k)) == True{} : Bool})
    case Con{x, t} Nil{} _:
      ft(hs, {KP.in_step(FL.set(Con{x, t}, i, v), W.set(Nil{}, i, k)) == True{} : Bool})
    case Con{+x, +t} Con{+k0, +u} 0n:
      and_i(KP.same_b(FL.is_free(v), W.is_free_kind(k)), KP.in_step(t, u), hp, and_r(KP.same_b(FL.is_free(x), W.is_free_kind(k0)), KP.in_step(t, u), hs))
    case Con{+x, +t} Con{+k0, +u} 1n++q:
      +hs = hs
      and_i(KP.same_b(FL.is_free(x), W.is_free_kind(k0)), KP.in_step(FL.set(t, q, v), W.set(u, q, k)), and_l(KP.same_b(FL.is_free(x), W.is_free_kind(k0)), KP.in_step(t, u), hs),
        pair_set(t, u, q, v, k, and_r(KP.same_b(FL.is_free(x), W.is_free_kind(k0)), KP.in_step(t, u), hs), hp))

def pair_ext(s: List<&2, FL.Slot>, ks: List<&2, R.NodeKind>, i: Nat, +v: FL.Slot, +k: R.NodeKind, hs: {KP.in_step(s, ks) == True{} : Bool},
  +hp: {KP.same_b(FL.is_free(v), W.is_free_kind(k)) == True{} : Bool}, hi: {W.below(i, List.length(&2, R.NodeKind, ks)) == True{} : Bool}) ->
  {KP.in_step(FL.set(s, i, v), W.set_ext(i, ks, k)) == True{} : Bool}:
  match s ks i:
    case Nil{} Nil{} _:
      ft(hi, {KP.in_step(FL.set(Nil{}, i, v), W.set_ext(i, Nil{}, k)) == True{} : Bool})
    case Nil{} Con{k0, u} _:
      ft(hs, {KP.in_step(FL.set(Nil{}, i, v), W.set_ext(i, Con{k0, u}, k)) == True{} : Bool})
    case Con{x, t} Nil{} _:
      ft(hs, {KP.in_step(FL.set(Con{x, t}, i, v), W.set_ext(i, Nil{}, k)) == True{} : Bool})
    case Con{+x, +t} Con{+k0, +u} 0n:
      and_i(KP.same_b(FL.is_free(v), W.is_free_kind(k)), KP.in_step(t, u), hp, and_r(KP.same_b(FL.is_free(x), W.is_free_kind(k0)), KP.in_step(t, u), hs))
    case Con{+x, +t} Con{+k0, +u} 1n++q:
      +hs = hs
      and_i(KP.same_b(FL.is_free(x), W.is_free_kind(k0)), KP.in_step(FL.set(t, q, v), W.set_ext(q, u, k)), and_l(KP.same_b(FL.is_free(x), W.is_free_kind(k0)), KP.in_step(t, u), hs),
        pair_ext(t, u, q, v, k, and_r(KP.same_b(FL.is_free(x), W.is_free_kind(k0)), KP.in_step(t, u), hs), hp, hi))

# a kind set where the free list already agrees
def kinds_ext(s: List<&2, FL.Slot>, ks: List<&2, R.NodeKind>, i: Nat, +k: R.NodeKind, hs: {KP.in_step(s, ks) == True{} : Bool},
  hp: {KP.same_b(FL.is_free(FL.get(s, i)), W.is_free_kind(k)) == True{} : Bool}, hi: {W.below(i, List.length(&2, R.NodeKind, ks)) == True{} : Bool}) ->
  {KP.in_step(s, W.set_ext(i, ks, k)) == True{} : Bool}:
  match s ks i:
    case Nil{} Nil{} _:
      ft(hi, {KP.in_step(Nil{}, W.set_ext(i, Nil{}, k)) == True{} : Bool})
    case Nil{} Con{k0, u} _:
      ft(hs, {KP.in_step(Nil{}, W.set_ext(i, Con{k0, u}, k)) == True{} : Bool})
    case Con{x, t} Nil{} _:
      ft(hs, {KP.in_step(Con{x, t}, W.set_ext(i, Nil{}, k)) == True{} : Bool})
    case Con{+x, +t} Con{+k0, +u} 0n:
      and_i(KP.same_b(FL.is_free(x), W.is_free_kind(k)), KP.in_step(t, u), hp, and_r(KP.same_b(FL.is_free(x), W.is_free_kind(k0)), KP.in_step(t, u), hs))
    case Con{+x, +t} Con{+k0, +u} 1n++q:
      +hs = hs
      and_i(KP.same_b(FL.is_free(x), W.is_free_kind(k0)), KP.in_step(t, W.set_ext(q, u, k)), and_l(KP.same_b(FL.is_free(x), W.is_free_kind(k0)), KP.in_step(t, u), hs),
        kinds_ext(t, u, q, k, and_r(KP.same_b(FL.is_free(x), W.is_free_kind(k0)), KP.in_step(t, u), hs), hp, hi))

# setting a slot free, then placing over it, is placing
def ext_over(i: Nat, K: List<&2, R.NodeKind>, +k: R.NodeKind) -> {W.set_ext(i, W.set(K, i, R.KFree{}), k) == W.set_ext(i, K, k) : List<&2, R.NodeKind>}:
  match i K:
    case 0n Nil{}:
      {==}
    case 0n Con{x, t}:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n+m Con{+x, +t}:
      %ext_over(m, t, k) : {Con{x, W.set_ext(m, W.set(t, m, R.KFree{}), k)} == Con{x, _} : List<&2, R.NodeKind>}
      {==}

# freeing one slot and placing at another commute
def ext_free(i: Nat, K: List<&2, R.NodeKind>, +k: R.NodeKind, j: Nat, h: {R.nat_eq(i, j) == False{} : Bool}) ->
  {W.set_ext(i, W.set(K, j, R.KFree{}), k) == W.set(W.set_ext(i, K, k), j, R.KFree{}) : List<&2, R.NodeKind>}:
  match i K j:
    case 0n Nil{} 0n:
      tf(h, {W.set_ext(0n, W.set(Nil{}, 0n, R.KFree{}), k) == W.set(W.set_ext(0n, Nil{}, k), 0n, R.KFree{}) : List<&2, R.NodeKind>})
    case 0n Nil{} 1n+q:
      {==}
    case 0n Con{x, t} 0n:
      tf(h, {W.set_ext(0n, W.set(Con{x, t}, 0n, R.KFree{}), k) == W.set(W.set_ext(0n, Con{x, t}, k), 0n, R.KFree{}) : List<&2, R.NodeKind>})
    case 0n Con{x, t} 1n+q:
      {==}
    case 1n+m Nil{} 0n:
      {==}
    case 1n+m Nil{} 1n+q:
      %ext_free(m, Nil{}, k, q, h) : {Con{R.KFree{}, W.set_ext(m, Nil{}, k)} == Con{R.KFree{}, _} : List<&2, R.NodeKind>}
      {==}
    case 1n+m Con{x, t} 0n:
      {==}
    case 1n+m Con{+x, +t} 1n+q:
      %ext_free(m, t, k, q, h) : {Con{x, W.set_ext(m, W.set(t, q, R.KFree{}), k)} == Con{x, _} : List<&2, R.NodeKind>}
      {==}

def free_comm(K: List<&2, R.NodeKind>, i: Nat, j: Nat, h: {R.nat_eq(i, j) == False{} : Bool}) ->
  {W.set(W.set(K, i, R.KFree{}), j, R.KFree{}) == W.set(W.set(K, j, R.KFree{}), i, R.KFree{}) : List<&2, R.NodeKind>}:
  match K i j:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      tf(h, {W.set(W.set(Con{x, t}, 0n, R.KFree{}), 0n, R.KFree{}) == W.set(W.set(Con{x, t}, 0n, R.KFree{}), 0n, R.KFree{}) : List<&2, R.NodeKind>})
    case Con{x, t} 0n 1n+q:
      {==}
    case Con{x, t} 1n+m 0n:
      {==}
    case Con{+x, +t} 1n+m 1n+q:
      %free_comm(t, m, q, h) : {Con{x, W.set(W.set(t, m, R.KFree{}), q, R.KFree{})} == Con{x, _} : List<&2, R.NodeKind>}
      {==}


def sa.go(c: FL.Slot, +s: List<&2, FL.Slot>, +j: Nat, +t: List<&2, Nat>, he: {FL.get(s, j) == c : FL.Slot}, hf: {FL.is_free(FL.get(s, j)) == True{} : Bool}) ->
  {KP.slots_of(FL.alloc.go(c, s, j, Con{j, t})) == FL.set(s, j, FL.Used{}) : List<&2, FL.Slot>}:
  match c:
    case FL.Used{}:
      Empty.absurd({KP.slots_of(FL.alloc.go(FL.Used{}, s, j, Con{j, t})) == FL.set(s, j, FL.Used{}) : List<&2, FL.Slot>}, MNat.internal_false_ne_true(
        Equal.trans(Bool, False{}, FL.is_free(FL.get(s, j)), True{}, Equal.cong(FL.Slot, Bool, FL.is_free, FL.Used{}, FL.get(s, j), Equal.sym(FL.Slot, FL.get(s, j), FL.Used{}, he)), hf)))
    case FL.Free{n}:
      {==}

# allocating sets the head's slot in use
def slots_alloc(+s: List<&2, FL.Slot>, +j: Nat, +t: List<&2, Nat>, hok: {FL.ok(FL.FL{s, 1n+j, Con{j, t}}) == True{} : Bool}) ->
  {KP.slots_of(FL.alloc(FL.FL{s, 1n+j, Con{j, t}})) == FL.set(s, j, FL.Used{}) : List<&2, FL.Slot>}:
  sa.go(FL.get(s, j), s, j, t, {==}, fl_head(s, j, Con{j, t}, hok))

def step_len(s: List<&2, FL.Slot>, ks: List<&2, R.NodeKind>, hs: {KP.in_step(s, ks) == True{} : Bool}) -> {List.length(&2, FL.Slot, s) == List.length(&2, R.NodeKind, ks) : Nat}:
  match s ks:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{k, u}:
      ft(hs, {List.length(&2, FL.Slot, Nil{}) == List.length(&2, R.NodeKind, Con{k, u}) : Nat})
    case Con{x, t} Nil{}:
      ft(hs, {List.length(&2, FL.Slot, Con{x, t}) == List.length(&2, R.NodeKind, Nil{}) : Nat})
    case Con{+x, +t} Con{+k, +u}:
      %step_len(t, u, and_r(KP.same_b(FL.is_free(x), W.is_free_kind(k)), KP.in_step(t, u), hs)) : {1n+List.length(&2, FL.Slot, t) == 1n+_ : Nat}
      {==}

def free_rng(s: List<&2, FL.Slot>, i: Nat, h: {FL.is_free(FL.get(s, i)) == True{} : Bool}) -> {W.below(i, List.length(&2, FL.Slot, s)) == True{} : Bool}:
  match s i:
    case Nil{} _:
      ft(h, {W.below(i, 0n) == True{} : Bool})
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+q:
      free_rng(t, q, h)

def lr.go(cc: Bool, +ks: List<&2, R.NodeKind>, +i: Nat, he: {W.below(i, List.length(&2, R.NodeKind, ks)) == cc : Bool}, hk: {W.is_free_kind(W.kind_at(ks, i)) == False{} : Bool}) -> {cc == True{} : Bool}:
  match cc:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ne_tf(Equal.trans(Bool, True{}, W.is_free_kind(W.kind_at(ks, i)), False{},
        Equal.sym(Bool, W.is_free_kind(W.kind_at(ks, i)), True{}, Equal.cong(R.NodeKind, Bool, W.is_free_kind, W.kind_at(ks, i), R.KFree{}, ka_past(ks, i, he))), hk)))

# a live node is within the kinds
def live_rng(+ks: List<&2, R.NodeKind>, +i: Nat, hk: {W.is_free_kind(W.kind_at(ks, i)) == False{} : Bool}) -> {W.below(i, List.length(&2, R.NodeKind, ks)) == True{} : Bool}:
  lr.go(W.below(i, List.length(&2, R.NodeKind, ks)), ks, i, {==}, hk)

def rng_step(+s: List<&2, FL.Slot>, +ks: List<&2, R.NodeKind>, +i: Nat, hs: {KP.in_step(s, ks) == True{} : Bool}, h: {W.below(i, List.length(&2, FL.Slot, s)) == True{} : Bool}) ->
  {W.below(i, List.length(&2, R.NodeKind, ks)) == True{} : Bool}:
  %step_len(s, ks, hs) : {W.below(i, _) == True{} : Bool}
  h

def sbff(x: Bool, y: Bool, hx: {x == False{} : Bool}, hy: {y == False{} : Bool}) -> {KP.same_b(x, y) == True{} : Bool}:
  match x y:
    case False{} False{}:
      {==}
    case True{} _:
      tf(hx, {KP.same_b(True{}, y) == True{} : Bool})
    case _ True{}:
      tf(hy, {KP.same_b(x, True{}) == True{} : Bool})

def len_ext(i: Nat, K: List<&2, R.NodeKind>, +k: R.NodeKind, hi: {W.below(i, List.length(&2, R.NodeKind, K)) == True{} : Bool}) ->
  {List.length(&2, R.NodeKind, W.set_ext(i, K, k)) == List.length(&2, R.NodeKind, K) : Nat}:
  match i K:
    case _ Nil{}:
      ft(hi, {List.length(&2, R.NodeKind, W.set_ext(i, Nil{}, k)) == 0n : Nat})
    case 0n Con{x, t}:
      {==}
    case 1n+m Con{x, t}:
      %len_ext(m, t, k, hi) : {1n+List.length(&2, R.NodeKind, W.set_ext(m, t, k)) == 1n+_ : Nat}
      {==}

# the first allocation's slot set in use, its kind placed
def ia.s(+s: List<&2, FL.Slot>, +j: Nat, +t: List<&2, Nat>, +K: List<&2, R.NodeKind>, +k: R.NodeKind, +hf2: {FL.ok(FL.FL{s, 1n+j, Con{j, t}}) == True{} : Bool},
  +hs: {KP.in_step(s, K) == True{} : Bool}, hk: {Bool.not(W.is_free_kind(k)) == True{} : Bool}) ->
  {KP.in_step(KP.slots_of(FL.alloc(FL.FL{s, 1n+j, Con{j, t}})), W.set_ext(j, K, k)) == True{} : Bool}:
  %Equal.sym(List<&2, FL.Slot>, KP.slots_of(FL.alloc(FL.FL{s, 1n+j, Con{j, t}})), FL.set(s, j, FL.Used{}), slots_alloc(s, j, t, hf2)) : {KP.in_step(_, W.set_ext(j, K, k)) == True{} : Bool}
  pair_ext(s, K, j, FL.Used{}, k, hs, sbff(False{}, W.is_free_kind(k), {==}, not_true(W.is_free_kind(k), hk)),
    rng_step(s, K, j, hs, free_rng(s, j, fl_head(s, j, Con{j, t}, hf2))))

def ia.k(+s: List<&2, FL.Slot>, +fh: Nat, +j: Nat, +t: List<&2, Nat>, +m: Nat, +K: List<&2, R.NodeKind>, +k: R.NodeKind, +kt: List<&2, R.NodeKind>,
  +eq: {fh == 1n+j : Nat}, hf: {FL.ok(FL.FL{s, fh, Con{j, t}}) == True{} : Bool}, hs: {KP.in_step(s, K) == True{} : Bool},
  hh: {KP.has(m, t) == True{} : Bool}, hk: {Bool.not(W.is_free_kind(k)) == True{} : Bool},
  ih: {FL.ok(FL.alloc(FL.FL{s, 1n+j, Con{j, t}})) == True{} : Bool} -> {KP.in_step(KP.slots_of(FL.alloc(FL.FL{s, 1n+j, Con{j, t}})), W.set_ext(j, K, k)) == True{} : Bool} ->
    {KP.has(m, KP.ghost(FL.alloc(FL.FL{s, 1n+j, Con{j, t}}))) == True{} : Bool} ->
    {KP.in_step(KP.slots_of(KP.after(m, FL.alloc(FL.FL{s, 1n+j, Con{j, t}}))), W.place(KP.allocs(m, FL.alloc(FL.FL{s, 1n+j, Con{j, t}})), W.set_ext(j, K, k), kt)) == True{} : Bool}) ->
  {KP.in_step(KP.slots_of(KP.after(m, FL.alloc(FL.FL{s, fh, Con{j, t}}))), W.place(KP.allocs(1n+m, FL.FL{s, fh, Con{j, t}}), K, Con{k, kt})) == True{} : Bool}:
  +hf2 = ok_tr(s, fh, j, Con{j, t}, eq, hf)
  %Equal.sym(Nat, fh, 1n+j, eq) : {KP.in_step(KP.slots_of(KP.after(m, FL.alloc(FL.FL{s, _, Con{j, t}}))), W.place(KP.allocs(1n+m, FL.FL{s, _, Con{j, t}}), K, Con{k, kt})) == True{} : Bool}
  ih(fl_alloc(FL.FL{s, 1n+j, Con{j, t}}, hf2),
    ia.s(s, j, t, K, k, hf2, hs, hk),
    has_tr(m, s, j, t, hf2, hh))


def zne(+m: Nat, e: {0n == 1n+m : Nat}) -> Empty:
  MNat.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, Equal.cong(Nat, Bool, (n => Nat.is_eq(n, 0n)), 0n, 1n+m, e)))

def pre(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+k:
      k

def succ_inj(+a: Nat, +b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, pre, 1n+a, 1n+b, e)

# n allocations, each slot set in use as place gives it its live kind
def in_step_allocs(n: Nat, f: FL.FL, +K: List<&2, R.NodeKind>, kt: List<&2, R.NodeKind>, hf: {FL.ok(f) == True{} : Bool},
  hs: {KP.in_step(KP.slots_of(f), K) == True{} : Bool}, hh: {KP.has(n, KP.ghost(f)) == True{} : Bool}, hk: {KP.kinds_live(kt) == True{} : Bool},
  hl: {List.length(&2, R.NodeKind, kt) == n : Nat}) -> {KP.in_step(KP.slots_of(KP.after(n, f)), W.place(KP.allocs(n, f), K, kt)) == True{} : Bool}:
  match n f:
    case 0n _:
      hs
    case 1n++m FL.FL{+s, +fh, l}:
      match l:
        case Nil{}:
          ft(hh, {KP.in_step(KP.slots_of(KP.after(1n+m, FL.FL{s, fh, Nil{}})), W.place(KP.allocs(1n+m, FL.FL{s, fh, Nil{}}), K, kt)) == True{} : Bool})
        case Con{+j, +t}:
          match kt:
            case Nil{}:
              Empty.absurd({KP.in_step(KP.slots_of(KP.after(1n+m, FL.FL{s, fh, Con{j, t}})), W.place(KP.allocs(1n+m, FL.FL{s, fh, Con{j, t}}), K, Nil{})) == True{} : Bool}, zne(m, hl))
            case Con{+k, +kt2}:
              +hf = hf
              +hk = hk
              ia.k(s, fh, j, t, m, K, k, kt2,
                same_eq(fh, 1n+j, and_l(FL.same(fh, 1n+j), (FL.is_free(FL.get(s, j)) && FL.walks(t, s, FL.next_of(FL.get(s, j)))), ok_w(s, fh, Con{j, t}, hf))),
                hf, hs, hh, and_l(Bool.not(W.is_free_kind(k)), KP.kinds_live(kt2), hk),
                h1 => h2 => h3 => in_step_allocs(m, FL.alloc(FL.FL{s, 1n+j, Con{j, t}}), W.set_ext(j, K, k), kt2, h1, h2, h3,
                  and_r(Bool.not(W.is_free_kind(k)), KP.kinds_live(kt2), hk), succ_inj(List.length(&2, R.NodeKind, kt2), m, hl)))

# the pair's node a in use, its new kind live: the two agree there
def hp_live(+s: List<&2, FL.Slot>, +ks: List<&2, R.NodeKind>, +i: Nat, +k: R.NodeKind, hs: {KP.in_step(s, ks) == True{} : Bool}, hl: {W.is_free_kind(W.kind_at(ks, i)) == False{} : Bool},
  hk: {Bool.not(W.is_free_kind(k)) == True{} : Bool}) -> {KP.same_b(FL.is_free(FL.get(s, i)), W.is_free_kind(k)) == True{} : Bool}:
  sbff(FL.is_free(FL.get(s, i)), W.is_free_kind(k), in_use_not_free(s, i, live_use(s, ks, i, hs, hl)), not_true(W.is_free_kind(k), hk))

def rng_ext(+i: Nat, +K: List<&2, R.NodeKind>, +k: R.NodeKind, +j: Nat, hi: {W.below(i, List.length(&2, R.NodeKind, K)) == True{} : Bool},
  hj: {W.below(j, List.length(&2, R.NodeKind, K)) == True{} : Bool}) -> {W.below(j, List.length(&2, R.NodeKind, W.set_ext(i, K, k))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, R.NodeKind, W.set_ext(i, K, k)), List.length(&2, R.NodeKind, K), len_ext(i, K, k, hi)) : {W.below(j, _) == True{} : Bool}
  hj

# after the kernel's placement, the free list and the kinds still agree
def kis(+s: List<&2, FL.Slot>, +fh: Nat, +l: List<&2, Nat>, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat, xs: List<&2, R.Spec>,
  +hf: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}, +hs: {KP.in_step(s, ks) == True{} : Bool}, +hab: {R.nat_eq(a, b) == False{} : Bool},
  +hla: {W.is_free_kind(W.kind_at(ks, a)) == False{} : Bool}, +hlb: {W.is_free_kind(W.kind_at(ks, b)) == False{} : Bool},
  hen: {KP.has(Nat.sub(List.length(&2, R.Spec, xs), 2n), l) == True{} : Bool}, hkl: {KP.kinds_live(W.kinds(xs)) == True{} : Bool}) ->
  {KP.in_step(KP.slots_of(KP.kfree(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})), W.rp_kinds(ks, a, b, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l}), xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      %Equal.sym(List<&2, R.NodeKind>, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), W.set(W.set(ks, b, R.KFree{}), a, R.KFree{}), free_comm(ks, a, b, hab)) :
        {KP.in_step(FL.set(FL.set(s, b, FL.Free{fh}), a, FL.Free{1n+b}), _) == True{} : Bool}
      pair_set(FL.set(s, b, FL.Free{fh}), W.set(ks, b, R.KFree{}), a, FL.Free{1n+b}, R.KFree{}, pair_set(s, ks, b, FL.Free{fh}, R.KFree{}, hs, {==}), {==})
    case Con{R.Spec{+k0, +src0}, Nil{}}:
      %Equal.sym(List<&2, R.NodeKind>, W.set_ext(a, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), k0), W.set(W.set_ext(a, W.set(ks, a, R.KFree{}), k0), b, R.KFree{}),
        ext_free(a, W.set(ks, a, R.KFree{}), k0, b, hab)) : {KP.in_step(FL.set(s, b, FL.Free{fh}), _) == True{} : Bool}
      %Equal.sym(List<&2, R.NodeKind>, W.set_ext(a, W.set(ks, a, R.KFree{}), k0), W.set_ext(a, ks, k0), ext_over(a, ks, k0)) :
        {KP.in_step(FL.set(s, b, FL.Free{fh}), W.set(_, b, R.KFree{})) == True{} : Bool}
      pair_set(s, W.set_ext(a, ks, k0), b, FL.Free{fh}, R.KFree{},
        kinds_ext(s, ks, a, k0, hs, hp_live(s, ks, a, k0, hs, hla, and_l(Bool.not(W.is_free_kind(k0)), KP.kinds_live(Nil{}), hkl)), live_rng(ks, a, hla)), {==})
    case Con{R.Spec{+k0, +src0}, Con{R.Spec{+k1, +src1}, +xt}}:
      +hkl = hkl
      %Equal.sym(List<&2, R.NodeKind>, W.set_ext(a, W.set(W.set(ks, a, R.KFree{}), b, R.KFree{}), k0), W.set(W.set_ext(a, W.set(ks, a, R.KFree{}), k0), b, R.KFree{}),
        ext_free(a, W.set(ks, a, R.KFree{}), k0, b, hab)) :
        {KP.in_step(KP.slots_of(KP.after(List.length(&2, R.Spec, xt), FL.FL{s, fh, l})), W.place(KP.allocs(List.length(&2, R.Spec, xt), FL.FL{s, fh, l}), W.set_ext(b, _, k1), W.kinds(xt))) == True{} : Bool}
      %Equal.sym(List<&2, R.NodeKind>, W.set_ext(a, W.set(ks, a, R.KFree{}), k0), W.set_ext(a, ks, k0), ext_over(a, ks, k0)) :
        {KP.in_step(KP.slots_of(KP.after(List.length(&2, R.Spec, xt), FL.FL{s, fh, l})), W.place(KP.allocs(List.length(&2, R.Spec, xt), FL.FL{s, fh, l}), W.set_ext(b, W.set(_, b, R.KFree{}), k1), W.kinds(xt))) == True{} : Bool}
      %Equal.sym(List<&2, R.NodeKind>, W.set_ext(b, W.set(W.set_ext(a, ks, k0), b, R.KFree{}), k1), W.set_ext(b, W.set_ext(a, ks, k0), k1), ext_over(b, W.set_ext(a, ks, k0), k1)) :
        {KP.in_step(KP.slots_of(KP.after(List.length(&2, R.Spec, xt), FL.FL{s, fh, l})), W.place(KP.allocs(List.length(&2, R.Spec, xt), FL.FL{s, fh, l}), _, W.kinds(xt))) == True{} : Bool}
      in_step_allocs(List.length(&2, R.Spec, xt), FL.FL{s, fh, l}, W.set_ext(b, W.set_ext(a, ks, k0), k1), W.kinds(xt), hf,
        kinds_ext(s, W.set_ext(a, ks, k0), b, k1,
          kinds_ext(s, ks, a, k0, hs, hp_live(s, ks, a, k0, hs, hla, and_l(Bool.not(W.is_free_kind(k0)), KP.kinds_live(Con{k1, W.kinds(xt)}), hkl)), live_rng(ks, a, hla)),
          hp_live(s, ks, b, k1, hs, hlb, and_l(Bool.not(W.is_free_kind(k1)), KP.kinds_live(W.kinds(xt)), and_r(Bool.not(W.is_free_kind(k0)), KP.kinds_live(Con{k1, W.kinds(xt)}), hkl))),
          rng_ext(a, ks, k0, b, live_rng(ks, a, hla), live_rng(ks, b, hlb))),
        has_sub(List.length(&2, R.Spec, xt), l, hen),
        and_r(Bool.not(W.is_free_kind(k1)), KP.kinds_live(W.kinds(xt)), and_r(Bool.not(W.is_free_kind(k0)), KP.kinds_live(Con{k1, W.kinds(xt)}), hkl)),
        len_kinds(xt))

def Laws.kernel_in_step(s, fh, l, ks, a, b, xs, hf, hs, hab, hla, hlb, hen, hkl):
  kis(s, fh, l, ks, a, b, xs, hf, hs, hab, hla, hlb, hen, hkl)

# The rule table's new kinds
# =========================

# by cases: every rule a constant the checker computes
def Laws.rules_kinds_live(a, b, s):
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
      {==}

    case R.KCopyL{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
      {==}
# a step of the table: a rule making nodes is kernel_in_step's, a stuck
# pair leaves the state as it was
def kris(r: R.Rule, +s: List<&2, FL.Slot>, +fh: Nat, +l: List<&2, Nat>, +ks: List<&2, R.NodeKind>, +a: Nat, +b: Nat,
  +hf: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}, +hs: {KP.in_step(s, ks) == True{} : Bool}, +hab: {R.nat_eq(a, b) == False{} : Bool},
  +hla: {W.is_free_kind(W.kind_at(ks, a)) == False{} : Bool}, +hlb: {W.is_free_kind(W.kind_at(ks, b)) == False{} : Bool},
  hen: {KP.step_has(r, l) == True{} : Bool}, hr: {KP.rule_live(r) == True{} : Bool}) ->
  {KP.in_step(KP.slots_of(KP.step_free(a, b, r, FL.FL{s, fh, l})), KP.step_kinds(ks, a, b, r, FL.FL{s, fh, l})) == True{} : Bool}:
  match r:
    case R.RWire{+xs, ls}:
      kis(s, fh, l, ks, a, b, xs, hf, hs, hab, hla, hlb, hen, hr)
    case R.RStuck{}:
      hs

def Laws.kernel_rules_in_step(s, fh, l, ks, a, b, t, hf, hs, hab, hla, hlb, hen):
  kris(R.rule(W.kind_at(ks, a), W.kind_at(ks, b), t), s, fh, l, ks, a, b, hf, hs, hab, hla, hlb, hen, Laws.rules_kinds_live(W.kind_at(ks, a), W.kind_at(ks, b), t))

# Growth
# ======
#
# Over kplace.bend's grow. Growing by 1+m is growing by m above one more
# slot, in use, then freeing it (grow_eq), so free_list_free carries the
# free list's exactness up from a slot appended in use (ok_used). The
# kinds grow by free nodes, which kind_at already gives past the end.

def len_snoc_s(A: List<&2, FL.Slot>, +v: FL.Slot) -> {List.length(&2, FL.Slot, List.append(&2, FL.Slot, A, [v])) == 1n+List.length(&2, FL.Slot, A) : Nat}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %len_snoc_s(t, v) : {1n+List.length(&2, FL.Slot, List.append(&2, FL.Slot, t, [v])) == 1n+_ : Nat}
      {==}

def app_nil_s(A: List<&2, FL.Slot>) -> {List.append(&2, FL.Slot, A, Nil{}) == A : List<&2, FL.Slot>}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %app_nil_s(t) : {Con{x, List.append(&2, FL.Slot, t, Nil{})} == Con{x, _} : List<&2, FL.Slot>}
      {==}

def app_assoc_s(A: List<&2, FL.Slot>, +B: List<&2, FL.Slot>, +C: List<&2, FL.Slot>) ->
  {List.append(&2, FL.Slot, List.append(&2, FL.Slot, A, B), C) == List.append(&2, FL.Slot, A, List.append(&2, FL.Slot, B, C)) : List<&2, FL.Slot>}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %app_assoc_s(t, B, C) : {Con{x, List.append(&2, FL.Slot, List.append(&2, FL.Slot, t, B), C)} == Con{x, _} : List<&2, FL.Slot>}
      {==}

# the slot just past A, replaced
def set_len(A: List<&2, FL.Slot>, +u: FL.Slot, +B: List<&2, FL.Slot>, +v: FL.Slot) ->
  {FL.set(List.append(&2, FL.Slot, A, Con{u, B}), List.length(&2, FL.Slot, A), v) == List.append(&2, FL.Slot, A, Con{v, B}) : List<&2, FL.Slot>}:
  match A:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %set_len(t, u, B, v) : {Con{x, FL.set(List.append(&2, FL.Slot, t, Con{u, B}), List.length(&2, FL.Slot, t), v)} == Con{x, _} : List<&2, FL.Slot>}
      {==}

def get_snoc(A: List<&2, FL.Slot>, +v: FL.Slot) -> {FL.get(List.append(&2, FL.Slot, A, [v]), List.length(&2, FL.Slot, A)) == v : FL.Slot}:
  match A:
    case Nil{}:
      {==}
    case Con{x, t}:
      get_snoc(t, v)

def in_use_snoc(A: List<&2, FL.Slot>) -> {FL.in_use(List.append(&2, FL.Slot, A, [FL.Used{}]), List.length(&2, FL.Slot, A)) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case Con{x, t}:
      in_use_snoc(t)

def in_use_app(A: List<&2, FL.Slot>, +B: List<&2, FL.Slot>, i: Nat, h: {FL.in_use(A, i) == True{} : Bool}) -> {FL.in_use(List.append(&2, FL.Slot, A, B), i) == True{} : Bool}:
  match A i:
    case Nil{} _:
      ft(h, {FL.in_use(List.append(&2, FL.Slot, Nil{}, B), i) == True{} : Bool})
    case Con{x, t} 0n:
      h
    case Con{x, t} 1n+j:
      in_use_app(t, B, j, h)

def get_app_lt(A: List<&2, FL.Slot>, +B: List<&2, FL.Slot>, j: Nat, h: {W.below(j, List.length(&2, FL.Slot, A)) == True{} : Bool}) ->
  {FL.get(List.append(&2, FL.Slot, A, B), j) == FL.get(A, j) : FL.Slot}:
  match A j:
    case Nil{} _:
      ft(h, {FL.get(List.append(&2, FL.Slot, Nil{}, B), j) == FL.get(Nil{}, j) : FL.Slot})
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+i:
      get_app_lt(t, B, i, h)

def get_app_free(A: List<&2, FL.Slot>, +B: List<&2, FL.Slot>, j: Nat, h: {FL.is_free(FL.get(A, j)) == True{} : Bool}) ->
  {FL.get(List.append(&2, FL.Slot, A, B), j) == FL.get(A, j) : FL.Slot}:
  match A j:
    case Nil{} _:
      ft(h, {FL.get(List.append(&2, FL.Slot, Nil{}, B), j) == FL.get(Nil{}, j) : FL.Slot})
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+i:
      get_app_free(t, B, i, h)

# a walk over A walks the same over A with slots after it
def walks_app(l: List<&2, Nat>, +A: List<&2, FL.Slot>, +B: List<&2, FL.Slot>, +x: Nat, h: {FL.walks(l, A, x) == True{} : Bool}) ->
  {FL.walks(l, List.append(&2, FL.Slot, A, B), x) == True{} : Bool}:
  match l:
    case Nil{}:
      h
    case Con{+j, +t}:
      +h = h
      %Equal.sym(FL.Slot, FL.get(List.append(&2, FL.Slot, A, B), j), FL.get(A, j),
        get_app_free(A, B, j, and_l(FL.is_free(FL.get(A, j)), FL.walks(t, A, FL.next_of(FL.get(A, j))), and_r(FL.same(x, 1n+j), (FL.is_free(FL.get(A, j)) && FL.walks(t, A, FL.next_of(FL.get(A, j)))), h)))) :
        {(FL.same(x, 1n+j) && (FL.is_free(_) && FL.walks(t, List.append(&2, FL.Slot, A, B), FL.next_of(_)))) == True{} : Bool}
      and_i(FL.same(x, 1n+j), (FL.is_free(FL.get(A, j)) && FL.walks(t, List.append(&2, FL.Slot, A, B), FL.next_of(FL.get(A, j)))),
        and_l(FL.same(x, 1n+j), (FL.is_free(FL.get(A, j)) && FL.walks(t, A, FL.next_of(FL.get(A, j)))), h),
        and_i(FL.is_free(FL.get(A, j)), FL.walks(t, List.append(&2, FL.Slot, A, B), FL.next_of(FL.get(A, j))),
          and_l(FL.is_free(FL.get(A, j)), FL.walks(t, A, FL.next_of(FL.get(A, j))), and_r(FL.same(x, 1n+j), (FL.is_free(FL.get(A, j)) && FL.walks(t, A, FL.next_of(FL.get(A, j)))), h)),
          walks_app(t, A, B, FL.next_of(FL.get(A, j)), and_r(FL.is_free(FL.get(A, j)), FL.walks(t, A, FL.next_of(FL.get(A, j))), and_r(FL.same(x, 1n+j), (FL.is_free(FL.get(A, j)) && FL.walks(t, A, FL.next_of(FL.get(A, j)))), h)))))

# every free slot of A below k listed, still so with slots after A
def listed_app(k: Nat, +A: List<&2, FL.Slot>, +B: List<&2, FL.Slot>, +l: List<&2, Nat>, hk: {W.below(k, 1n+List.length(&2, FL.Slot, A)) == True{} : Bool},
  h: {FL.listed(A, k, l) == True{} : Bool}) -> {FL.listed(List.append(&2, FL.Slot, A, B), k, l) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      +h = h
      +hk = hk
      %Equal.sym(FL.Slot, FL.get(List.append(&2, FL.Slot, A, B), j), FL.get(A, j), get_app_lt(A, B, j, hk)) :
        {((Bool.not(FL.is_free(_)) || FL.mem(j, l)) && FL.listed(List.append(&2, FL.Slot, A, B), j, l)) == True{} : Bool}
      and_i((Bool.not(FL.is_free(FL.get(A, j))) || FL.mem(j, l)), FL.listed(List.append(&2, FL.Slot, A, B), j, l),
        and_l((Bool.not(FL.is_free(FL.get(A, j))) || FL.mem(j, l)), FL.listed(A, j, l), h),
        listed_app(j, A, B, l, below_succ(List.length(&2, FL.Slot, A), j, hk), and_r((Bool.not(FL.is_free(FL.get(A, j))) || FL.mem(j, l)), FL.listed(A, j, l), h)))

# a slot appended in use keeps the free list exact
def ok_used(+s: List<&2, FL.Slot>, +fh: Nat, +l: List<&2, Nat>, +h: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}) ->
  {FL.ok(FL.FL{List.append(&2, FL.Slot, s, [FL.Used{}]), fh, l}) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, FL.Slot, List.append(&2, FL.Slot, s, [FL.Used{}])), 1n+List.length(&2, FL.Slot, s), len_snoc_s(s, FL.Used{})) :
    {(FL.walks(l, List.append(&2, FL.Slot, s, [FL.Used{}]), fh) && (FL.nodup(l) && FL.listed(List.append(&2, FL.Slot, s, [FL.Used{}]), _, l))) == True{} : Bool}
  %Equal.sym(FL.Slot, FL.get(List.append(&2, FL.Slot, s, [FL.Used{}]), List.length(&2, FL.Slot, s)), FL.Used{}, get_snoc(s, FL.Used{})) :
    {(FL.walks(l, List.append(&2, FL.Slot, s, [FL.Used{}]), fh) && (FL.nodup(l) && ((Bool.not(FL.is_free(_)) || FL.mem(List.length(&2, FL.Slot, s), l)) && FL.listed(List.append(&2, FL.Slot, s, [FL.Used{}]), List.length(&2, FL.Slot, s), l)))) == True{} : Bool}
  and_i(FL.walks(l, List.append(&2, FL.Slot, s, [FL.Used{}]), fh), (FL.nodup(l) && FL.listed(List.append(&2, FL.Slot, s, [FL.Used{}]), List.length(&2, FL.Slot, s), l)),
    walks_app(l, s, [FL.Used{}], fh, and_l(FL.walks(l, s, fh), (FL.nodup(l) && FL.listed(s, List.length(&2, FL.Slot, s), l)), h)),
    and_i(FL.nodup(l), FL.listed(List.append(&2, FL.Slot, s, [FL.Used{}]), List.length(&2, FL.Slot, s), l),
      and_l(FL.nodup(l), FL.listed(s, List.length(&2, FL.Slot, s), l), and_r(FL.walks(l, s, fh), (FL.nodup(l) && FL.listed(s, List.length(&2, FL.Slot, s), l)), h)),
      listed_app(List.length(&2, FL.Slot, s), s, [FL.Used{}], l, below_self(List.length(&2, FL.Slot, s)),
        and_r(FL.nodup(l), FL.listed(s, List.length(&2, FL.Slot, s), l), and_r(FL.walks(l, s, fh), (FL.nodup(l) && FL.listed(s, List.length(&2, FL.Slot, s), l)), h)))))

# growing by 1+m: growing by m above a slot in use, then freeing it
def grow_eq(+s: List<&2, FL.Slot>, +fh: Nat, +l: List<&2, Nat>, +m: Nat) ->
  {FL.free(KP.grow(FL.FL{List.append(&2, FL.Slot, s, [FL.Used{}]), fh, l}, m), List.length(&2, FL.Slot, s)) == KP.grow(FL.FL{s, fh, l}, 1n+m) : FL.FL}:
  %Equal.sym(Nat, List.length(&2, FL.Slot, List.append(&2, FL.Slot, s, [FL.Used{}])), 1n+List.length(&2, FL.Slot, s), len_snoc_s(s, FL.Used{})) :
    {FL.FL{FL.set(List.append(&2, FL.Slot, List.append(&2, FL.Slot, s, [FL.Used{}]), KP.threaded(m, _, fh)), List.length(&2, FL.Slot, s), FL.Free{KP.ghead(_, m, fh)}),
      1n+List.length(&2, FL.Slot, s), Con{List.length(&2, FL.Slot, s), List.append(&2, Nat, W.range(m, _), l)}} == KP.grow(FL.FL{s, fh, l}, 1n+m) : FL.FL}
  %Equal.sym(List<&2, FL.Slot>, List.append(&2, FL.Slot, List.append(&2, FL.Slot, s, [FL.Used{}]), KP.threaded(m, 1n+List.length(&2, FL.Slot, s), fh)),
    List.append(&2, FL.Slot, s, Con{FL.Used{}, KP.threaded(m, 1n+List.length(&2, FL.Slot, s), fh)}), app_assoc_s(s, [FL.Used{}], KP.threaded(m, 1n+List.length(&2, FL.Slot, s), fh))) :
    {FL.FL{FL.set(_, List.length(&2, FL.Slot, s), FL.Free{KP.ghead(1n+List.length(&2, FL.Slot, s), m, fh)}),
      1n+List.length(&2, FL.Slot, s), Con{List.length(&2, FL.Slot, s), List.append(&2, Nat, W.range(m, 1n+List.length(&2, FL.Slot, s)), l)}} == KP.grow(FL.FL{s, fh, l}, 1n+m) : FL.FL}
  %Equal.sym(List<&2, FL.Slot>, FL.set(List.append(&2, FL.Slot, s, Con{FL.Used{}, KP.threaded(m, 1n+List.length(&2, FL.Slot, s), fh)}), List.length(&2, FL.Slot, s), FL.Free{KP.ghead(1n+List.length(&2, FL.Slot, s), m, fh)}),
    List.append(&2, FL.Slot, s, Con{FL.Free{KP.ghead(1n+List.length(&2, FL.Slot, s), m, fh)}, KP.threaded(m, 1n+List.length(&2, FL.Slot, s), fh)}),
    set_len(s, FL.Used{}, KP.threaded(m, 1n+List.length(&2, FL.Slot, s), fh), FL.Free{KP.ghead(1n+List.length(&2, FL.Slot, s), m, fh)})) :
    {FL.FL{_, 1n+List.length(&2, FL.Slot, s), Con{List.length(&2, FL.Slot, s), List.append(&2, Nat, W.range(m, 1n+List.length(&2, FL.Slot, s)), l)}} == KP.grow(FL.FL{s, fh, l}, 1n+m) : FL.FL}
  {==}

# freeing a slot in use keeps an exact free list exact, whatever its form
def ok_free(g: FL.FL, +i: Nat, live: {FL.in_use(KP.slots_of(g), i) == True{} : Bool}, h: {FL.ok(g) == True{} : Bool}) -> {FL.ok(FL.free(g, i)) == True{} : Bool}:
  match g:
    case FL.FL{+s, +fh, +l}:
      Laws.free_list_free(s, fh, l, i, live, h)

def ok_grow(n: Nat, +s: List<&2, FL.Slot>, +fh: Nat, +l: List<&2, Nat>, +h: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}) -> {FL.ok(KP.grow(FL.FL{s, fh, l}, n)) == True{} : Bool}:
  match n:
    case 0n:
      %Equal.sym(List<&2, FL.Slot>, List.append(&2, FL.Slot, s, Nil{}), s, app_nil_s(s)) : {FL.ok(FL.FL{_, fh, l}) == True{} : Bool}
      h
    case 1n++m:
      %grow_eq(s, fh, l, m) : {FL.ok(_) == True{} : Bool}
      ok_free(KP.grow(FL.FL{List.append(&2, FL.Slot, s, [FL.Used{}]), fh, l}, m), List.length(&2, FL.Slot, s),
        in_use_app(List.append(&2, FL.Slot, s, [FL.Used{}]), KP.threaded(m, List.length(&2, FL.Slot, List.append(&2, FL.Slot, s, [FL.Used{}])), fh), List.length(&2, FL.Slot, s), in_use_snoc(s)),
        ok_grow(m, List.append(&2, FL.Slot, s, [FL.Used{}]), fh, l, ok_used(s, fh, l, h)))

def Laws.free_list_grow(s, fh, l, n, hf):
  ok_grow(n, s, fh, l, hf)

def in_step_app(A: List<&2, FL.Slot>, C: List<&2, R.NodeKind>, +B: List<&2, FL.Slot>, +D: List<&2, R.NodeKind>, h1: {KP.in_step(A, C) == True{} : Bool},
  +h2: {KP.in_step(B, D) == True{} : Bool}) -> {KP.in_step(List.append(&2, FL.Slot, A, B), List.append(&2, R.NodeKind, C, D)) == True{} : Bool}:
  match A C:
    case Nil{} Nil{}:
      h2
    case Nil{} Con{k, u}:
      ft(h1, {KP.in_step(List.append(&2, FL.Slot, Nil{}, B), List.append(&2, R.NodeKind, Con{k, u}, D)) == True{} : Bool})
    case Con{x, t} Nil{}:
      ft(h1, {KP.in_step(List.append(&2, FL.Slot, Con{x, t}, B), List.append(&2, R.NodeKind, Nil{}, D)) == True{} : Bool})
    case Con{+x, +t} Con{+k, +u}:
      +h1 = h1
      and_i(KP.same_b(FL.is_free(x), W.is_free_kind(k)), KP.in_step(List.append(&2, FL.Slot, t, B), List.append(&2, R.NodeKind, u, D)),
        and_l(KP.same_b(FL.is_free(x), W.is_free_kind(k)), KP.in_step(t, u), h1),
        in_step_app(t, u, B, D, and_r(KP.same_b(FL.is_free(x), W.is_free_kind(k)), KP.in_step(t, u), h1), h2))

def in_step_thr(n: Nat, +i: Nat, +x: Nat) -> {KP.in_step(KP.threaded(n, i, x), KP.frees(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      in_step_thr(m, 1n+i, x)

def Laws.grow_in_step(s, fh, l, ks, n, hs):
  in_step_app(s, ks, KP.threaded(n, List.length(&2, FL.Slot, s), fh), KP.frees(n), hs, in_step_thr(n, List.length(&2, FL.Slot, s), fh))

def ka_frees(n: Nat, i: Nat) -> {W.kind_at(KP.frees(n), i) == R.KFree{} : R.NodeKind}:
  match n i:
    case 0n _:
      {==}
    case 1n+m 0n:
      {==}
    case 1n+m 1n+j:
      ka_frees(m, j)

def ka_grow(ks: List<&2, R.NodeKind>, +n: Nat, i: Nat) -> {W.kind_at(KP.grow_kinds(ks, n), i) == W.kind_at(ks, i) : R.NodeKind}:
  match ks i:
    case Nil{} _:
      ka_frees(n, i)
    case Con{k, t} 0n:
      {==}
    case Con{k, t} 1n+j:
      ka_grow(t, n, j)

def Laws.grow_kind_at(ks, n, i):
  ka_grow(ks, n, i)

def live_grow(+ks: List<&2, R.NodeKind>, +n: Nat, xs: List<&2, W.Pt>) -> {W.all_live(KP.grow_kinds(ks, n), xs) == W.all_live(ks, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{W.Pt{+p0, +p1}, t}:
      %Equal.sym(R.NodeKind, W.kind_at(KP.grow_kinds(ks, n), p0), W.kind_at(ks, p0), ka_grow(ks, n, p0)) :
        {(W.below(p1, R.arity(_)) && W.all_live(KP.grow_kinds(ks, n), t)) == (W.below(p1, R.arity(W.kind_at(ks, p0))) && W.all_live(ks, t)) : Bool}
      %Equal.sym(Bool, W.all_live(KP.grow_kinds(ks, n), t), W.all_live(ks, t), live_grow(ks, n, t)) :
        {(W.below(p1, R.arity(W.kind_at(ks, p0))) && _) == (W.below(p1, R.arity(W.kind_at(ks, p0))) && W.all_live(ks, t)) : Bool}
      {==}

def cov_grow(+ks: List<&2, R.NodeKind>, +n: Nat, k: Nat, +xs: List<&2, W.Pt>) -> {W.covered(KP.grow_kinds(ks, n), k, xs) == W.covered(ks, k, xs) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      %Equal.sym(R.NodeKind, W.kind_at(KP.grow_kinds(ks, n), j), W.kind_at(ks, j), ka_grow(ks, n, j)) :
        {(W.ports_in(j, R.arity(_), xs) && W.covered(KP.grow_kinds(ks, n), j, xs)) == (W.ports_in(j, R.arity(W.kind_at(ks, j)), xs) && W.covered(ks, j, xs)) : Bool}
      %Equal.sym(Bool, W.covered(KP.grow_kinds(ks, n), j, xs), W.covered(ks, j, xs), cov_grow(ks, n, j, xs)) :
        {(W.ports_in(j, R.arity(W.kind_at(ks, j)), xs) && _) == (W.ports_in(j, R.arity(W.kind_at(ks, j)), xs) && W.covered(ks, j, xs)) : Bool}
      {==}

def cb.go(c: Bool, +ks: List<&2, R.NodeKind>, +j: Nat, +xs: List<&2, W.Pt>, he: {W.below(j, List.length(&2, R.NodeKind, ks)) == c : Bool},
  h: {W.covered(ks, List.length(&2, R.NodeKind, ks), xs) == True{} : Bool}) -> {W.ports_in(j, R.arity(W.kind_at(ks, j)), xs) == True{} : Bool}:
  match c:
    case True{}:
      cov_at(ks, List.length(&2, R.NodeKind, ks), xs, j, he, h)
    case False{}:
      %Equal.sym(R.NodeKind, W.kind_at(ks, j), R.KFree{}, ka_past(ks, j, he)) : {W.ports_in(j, R.arity(_), xs) == True{} : Bool}
      {==}

# covered up to its length, a net is covered up to any count: the nodes
# past the end are free
def cov_beyond(+ks: List<&2, R.NodeKind>, k: Nat, +xs: List<&2, W.Pt>, +h: {W.covered(ks, List.length(&2, R.NodeKind, ks), xs) == True{} : Bool}) ->
  {W.covered(ks, k, xs) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      and_i(W.ports_in(j, R.arity(W.kind_at(ks, j)), xs), W.covered(ks, j, xs), cb.go(W.below(j, List.length(&2, R.NodeKind, ks)), ks, j, xs, {==}, h), cov_beyond(ks, j, xs, h))

def Laws.grow_wired(ks, n, xs, hw):
  +hw = hw
  %Equal.sym(Bool, W.all_live(KP.grow_kinds(ks, n), xs), W.all_live(ks, xs), live_grow(ks, n, xs)) :
    {(W.nodup(xs) && (_ && W.covered(KP.grow_kinds(ks, n), List.length(&2, R.NodeKind, KP.grow_kinds(ks, n)), xs))) == True{} : Bool}
  %Equal.sym(Bool, W.covered(KP.grow_kinds(ks, n), List.length(&2, R.NodeKind, KP.grow_kinds(ks, n)), xs), W.covered(ks, List.length(&2, R.NodeKind, KP.grow_kinds(ks, n)), xs),
    cov_grow(ks, n, List.length(&2, R.NodeKind, KP.grow_kinds(ks, n)), xs)) :
    {(W.nodup(xs) && (W.all_live(ks, xs) && _)) == True{} : Bool}
  and_i(W.nodup(xs), (W.all_live(ks, xs) && W.covered(ks, List.length(&2, R.NodeKind, KP.grow_kinds(ks, n)), xs)),
    and_l(W.nodup(xs), (W.all_live(ks, xs) && W.covered(ks, List.length(&2, R.NodeKind, ks), xs)), hw),
    and_i(W.all_live(ks, xs), W.covered(ks, List.length(&2, R.NodeKind, KP.grow_kinds(ks, n)), xs),
      and_l(W.all_live(ks, xs), W.covered(ks, List.length(&2, R.NodeKind, ks), xs), and_r(W.nodup(xs), (W.all_live(ks, xs) && W.covered(ks, List.length(&2, R.NodeKind, ks), xs)), hw)),
      cov_beyond(ks, List.length(&2, R.NodeKind, KP.grow_kinds(ks, n)), xs,
        and_r(W.all_live(ks, xs), W.covered(ks, List.length(&2, R.NodeKind, ks), xs), and_r(W.nodup(xs), (W.all_live(ks, xs) && W.covered(ks, List.length(&2, R.NodeKind, ks), xs)), hw)))))

def has_rng(n: Nat, +i: Nat, +l: List<&2, Nat>) -> {KP.has(n, List.append(&2, Nat, W.range(n, i), l)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      has_rng(m, 1n+i, l)

def Laws.grow_has(s, fh, l, n):
  has_rng(n, List.length(&2, FL.Slot, s), l)

# Linear fans
# ===========
#
# By cases, as for the rule table's other laws: every rule a constant the
# checker computes, a linear fan's derived as rules.bend derives it.

def Laws.rules_linear_rewrites(a, b, s):
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
      {==}
    case R.KCopyL{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
      {==}

def Laws.rules_linear_fewer(a, b, s):
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
      {==}
    case R.KCopyL{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyR{}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
      {==}

# Events
# ======
#
# By cases, as for the rule table: every event a constant the checker
# computes, the port matched as far as 3; the composed laws as the rule
# table's.

def Laws.events_exact(a, b, p):
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMerge{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}

def Laws.events_polarized(a, b, p):
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMerge{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}

def Laws.events_shrink(a, b, p):
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMerge{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}

def Laws.events_kinds_live(a, b, p):
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMerge{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}

def Laws.events_side(a, b, p):
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMerge{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}

def Laws.events_erase_last(a, b, p):
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMerge{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}

def Laws.erasers_untested(k):
  match k:
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
    case R.KCopyL{}:
      {==}
    case R.KCopyR{}:
      {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
      {==}

def Laws.rules_no_self_links(a, b, t):
  match a:
    case R.KFree{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KFn{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KAp{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopy{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMerge{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KData{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KEraN{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KEraP{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KRoot{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCall{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KLift{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KLiftC{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyL{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyR{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeL{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeR{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}

def Laws.events_one_node(a, b, p):
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMerge{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}

def Laws.rules_base_sources(a, b, t):
  match a:
    case R.KFree{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KFn{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KAp{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopy{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMerge{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KData{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KEraN{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KEraP{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KRoot{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCall{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KLift{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KLiftC{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyL{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyR{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeL{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeR{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}

def Laws.events_base_sources(a, b, p):
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMerge{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}

# U32 equality reflexive, through the hub's lemma that it tests the
# values as Nats
def nis_refl(+n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nis_refl(p)

def u32_refl(+x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(x, x), Nat.is_eq(U32.to_nat(x), U32.to_nat(x)), MU.u32_is_eq_to_nat(x, x)) : {_ == True{} : Bool}
  nis_refl(U32.to_nat(x))

# by cases on the kinds; where the test compares, on the payload, each
# comparison of a value with itself rewritten to true
def Laws.tests_reflexive(a, b, p):
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
          u32_refl(V.pay_lvl(p))
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case V.PFan{f}:
              match f:
                case V.FanId{+s, +i, +l}:
                  %Equal.sym(Bool, U32.is_eq(s, s), True{}, u32_refl(s)) : {((_ && U32.is_eq(i, i)) && U32.is_eq(l, l)) == True{} : Bool}
                  %Equal.sym(Bool, U32.is_eq(i, i), True{}, u32_refl(i)) : {(_ && U32.is_eq(l, l)) == True{} : Bool}
                  u32_refl(l)
            case V.PNone{}:
              {==}
            case V.PVal{v}:
              {==}
            case V.PLvl{+n}:
              {==}
            case V.PLift{+n, up, +by}:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case V.PLift{+n, up, +by}:
              match up:
                case True{}:
                  %Equal.sym(Bool, U32.is_eq(n, n), True{}, u32_refl(n)) : {((_ && V.bool_eq(True{}, True{})) && U32.is_eq(by, by)) == True{} : Bool}
                  u32_refl(by)
                case False{}:
                  %Equal.sym(Bool, U32.is_eq(n, n), True{}, u32_refl(n)) : {((_ && V.bool_eq(False{}, False{})) && U32.is_eq(by, by)) == True{} : Bool}
                  u32_refl(by)
            case V.PNone{}:
              {==}
            case V.PVal{v}:
              {==}
            case V.PFan{f}:
              {==}
            case V.PLvl{+n}:
              {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
      {==}
    case R.KCopyL{}:
      {==}
    case R.KCopyR{}:
      {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
      {==}

# by cases on the kinds and the test; where the rule makes a control, on
# the payload it is made from
def Laws.rules_keep_fits(a, b, t, pa, pb):
  match a:
    case R.KFree{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KFn{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KAp{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              match pb:
                case V.PNone{}:
                  {==}
                case V.PVal{w}:
                  {==}
                case V.PFan{g}:
                  {==}
                case V.PLvl{m}:
                  {==}
                case V.PLift{m, vp, bz}:
                  {==}
            case False{}:
              match pb:
                case V.PNone{}:
                  {==}
                case V.PVal{w}:
                  {==}
                case V.PFan{g}:
                  {==}
                case V.PLvl{m}:
                  {==}
                case V.PLift{m, vp, bz}:
                  {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopy{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              match pb:
                case V.PNone{}:
                  {==}
                case V.PVal{w}:
                  {==}
                case V.PFan{g}:
                  {==}
                case V.PLvl{m}:
                  {==}
                case V.PLift{m, vp, bz}:
                  {==}
            case False{}:
              match pb:
                case V.PNone{}:
                  {==}
                case V.PVal{w}:
                  {==}
                case V.PFan{g}:
                  {==}
                case V.PLvl{m}:
                  {==}
                case V.PLift{m, vp, bz}:
                  {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMerge{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KData{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KEraN{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KEraP{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KRoot{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCall{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              match pb:
                case V.PNone{}:
                  {==}
                case V.PVal{w}:
                  {==}
                case V.PFan{g}:
                  {==}
                case V.PLvl{m}:
                  {==}
                case V.PLift{m, vp, bz}:
                  {==}
            case False{}:
              match pb:
                case V.PNone{}:
                  {==}
                case V.PVal{w}:
                  {==}
                case V.PFan{g}:
                  {==}
                case V.PLvl{m}:
                  {==}
                case V.PLift{m, vp, bz}:
                  {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KLift{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              match pa:
                case V.PNone{}:
                  {==}
                case V.PVal{v}:
                  {==}
                case V.PFan{f}:
                  {==}
                case V.PLvl{n}:
                  {==}
                case V.PLift{n, up, by}:
                  {==}
            case False{}:
              match pa:
                case V.PNone{}:
                  {==}
                case V.PVal{v}:
                  {==}
                case V.PFan{f}:
                  {==}
                case V.PLvl{n}:
                  {==}
                case V.PLift{n, up, by}:
                  {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              match pa:
                case V.PNone{}:
                  {==}
                case V.PVal{v}:
                  {==}
                case V.PFan{f}:
                  {==}
                case V.PLvl{n}:
                  {==}
                case V.PLift{n, up, by}:
                  {==}
            case False{}:
              match pa:
                case V.PNone{}:
                  {==}
                case V.PVal{v}:
                  {==}
                case V.PFan{f}:
                  {==}
                case V.PLvl{n}:
                  {==}
                case V.PLift{n, up, by}:
                  {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              match pa:
                case V.PNone{}:
                  match pb:
                    case V.PNone{}:
                      {==}
                    case V.PVal{w}:
                      {==}
                    case V.PFan{g}:
                      {==}
                    case V.PLvl{m}:
                      {==}
                    case V.PLift{m, vp, bz}:
                      {==}
                case V.PVal{v}:
                  match pb:
                    case V.PNone{}:
                      {==}
                    case V.PVal{w}:
                      {==}
                    case V.PFan{g}:
                      {==}
                    case V.PLvl{m}:
                      {==}
                    case V.PLift{m, vp, bz}:
                      {==}
                case V.PFan{f}:
                  match f:
                    case V.FanId{s, i, l}:
                      match pb:
                        case V.PNone{}:
                          {==}
                        case V.PVal{w}:
                          {==}
                        case V.PFan{g}:
                          {==}
                        case V.PLvl{m}:
                          {==}
                        case V.PLift{m, vp, bz}:
                          {==}
                case V.PLvl{n}:
                  match pb:
                    case V.PNone{}:
                      {==}
                    case V.PVal{w}:
                      {==}
                    case V.PFan{g}:
                      {==}
                    case V.PLvl{m}:
                      {==}
                    case V.PLift{m, vp, bz}:
                      {==}
                case V.PLift{n, up, by}:
                  match pb:
                    case V.PNone{}:
                      {==}
                    case V.PVal{w}:
                      {==}
                    case V.PFan{g}:
                      match g:
                        case V.FanId{s, i, l}:
                          {==}
                    case V.PLvl{m}:
                      {==}
                    case V.PLift{m, vp, bz}:
                      {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              match pa:
                case V.PNone{}:
                  {==}
                case V.PVal{v}:
                  {==}
                case V.PFan{f}:
                  {==}
                case V.PLvl{n}:
                  {==}
                case V.PLift{n, up, by}:
                  {==}
            case False{}:
              match pa:
                case V.PNone{}:
                  {==}
                case V.PVal{v}:
                  {==}
                case V.PFan{f}:
                  {==}
                case V.PLvl{n}:
                  {==}
                case V.PLift{n, up, by}:
                  {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              match pa:
                case V.PNone{}:
                  {==}
                case V.PVal{v}:
                  {==}
                case V.PFan{f}:
                  {==}
                case V.PLvl{n}:
                  {==}
                case V.PLift{n, up, by}:
                  {==}
            case False{}:
              match pa:
                case V.PNone{}:
                  {==}
                case V.PVal{v}:
                  {==}
                case V.PFan{f}:
                  {==}
                case V.PLvl{n}:
                  {==}
                case V.PLift{n, up, by}:
                  {==}
    case R.KLiftC{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyL{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              match pb:
                case V.PNone{}:
                  {==}
                case V.PVal{w}:
                  {==}
                case V.PFan{g}:
                  {==}
                case V.PLvl{m}:
                  {==}
                case V.PLift{m, vp, bz}:
                  {==}
            case False{}:
              match pb:
                case V.PNone{}:
                  {==}
                case V.PVal{w}:
                  {==}
                case V.PFan{g}:
                  {==}
                case V.PLvl{m}:
                  {==}
                case V.PLift{m, vp, bz}:
                  {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyR{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              match pb:
                case V.PNone{}:
                  {==}
                case V.PVal{w}:
                  {==}
                case V.PFan{g}:
                  {==}
                case V.PLvl{m}:
                  {==}
                case V.PLift{m, vp, bz}:
                  {==}
            case False{}:
              match pb:
                case V.PNone{}:
                  {==}
                case V.PVal{w}:
                  {==}
                case V.PFan{g}:
                  {==}
                case V.PLvl{m}:
                  {==}
                case V.PLift{m, vp, bz}:
                  {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeL{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeR{}:
      match b:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}

# by the event table's cases, as events_one_node: none makes a control
def Laws.events_keep_fits(a, b, p, pa):
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMerge{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KLiftC{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KCopyR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
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
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeL{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}
    case R.KMergeR{}:
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
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+r:
                  match r:
                    case 0n:
                      {==}
                    case 1n+t:
                      {==}
        case R.KRoot{}:
          {==}
        case R.KCall{}:
          {==}
        case R.KLift{}:
          {==}
        case R.KLiftC{}:
          {==}
        case R.KCopyL{}:
          {==}
        case R.KCopyR{}:
          {==}
        case R.KMergeL{}:
          {==}
        case R.KMergeR{}:
          {==}

# by cases on the control's kind, the partner and the test, each a closed
# graph normalized
def Laws.runs_as_units(k, v, t):
  match k:
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
      match v:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KLiftC{}:
      match v:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyL{}:
      {==}
    case R.KCopyR{}:
      {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
      {==}

def Laws.copy_identity():
  {==}

def Laws.aux_loops(k):
  match k:
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
    case R.KCopyL{}:
      {==}
    case R.KCopyR{}:
      {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
      {==}

def Laws.fused_polarity(k):
  match k:
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
    case R.KCopyL{}:
      {==}
    case R.KCopyR{}:
      {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
      {==}

def Laws.beta_loops():
  {==}

def Laws.linear_as_components(f, v, t):
  match f:
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
    case R.KCopyL{}:
      match v:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KCopyR{}:
      match v:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeL{}:
      match v:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.KMergeR{}:
      match v:
        case R.KFree{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KFn{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KAp{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopy{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMerge{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KData{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraN{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KEraP{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KRoot{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCall{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLift{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KLiftC{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KCopyR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeL{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
        case R.KMergeR{}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}

def Laws.events_as_components(a, p, v, t):
  match a:
    case R.KFree{}:
      {==}
    case R.KFn{}:
      {==}
    case R.KAp{}:
      {==}
    case R.KCopy{}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              match v:
                case R.KFree{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KFn{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KAp{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopy{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMerge{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KData{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraN{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraP{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KRoot{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCall{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLift{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLiftC{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case 1n+r:
              match r:
                case 0n:
                  match v:
                    case R.KFree{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KFn{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KAp{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopy{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMerge{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KData{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraN{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraP{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KRoot{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCall{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLift{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLiftC{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case 1n+s:
                  {==}
    case R.KMerge{}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              match v:
                case R.KFree{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KFn{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KAp{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopy{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMerge{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KData{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraN{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraP{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KRoot{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCall{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLift{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLiftC{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case 1n+r:
              match r:
                case 0n:
                  match v:
                    case R.KFree{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KFn{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KAp{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopy{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMerge{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KData{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraN{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraP{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KRoot{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCall{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLift{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLiftC{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case 1n+s:
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
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              match v:
                case R.KFree{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KFn{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KAp{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopy{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMerge{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KData{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraN{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraP{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KRoot{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCall{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLift{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLiftC{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case 1n+r:
              match r:
                case 0n:
                  match v:
                    case R.KFree{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KFn{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KAp{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopy{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMerge{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KData{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraN{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraP{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KRoot{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCall{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLift{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLiftC{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case 1n+s:
                  {==}
    case R.KLiftC{}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              match v:
                case R.KFree{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KFn{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KAp{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopy{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMerge{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KData{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraN{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraP{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KRoot{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCall{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLift{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLiftC{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case 1n+r:
              match r:
                case 0n:
                  match v:
                    case R.KFree{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KFn{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KAp{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopy{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMerge{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KData{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraN{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraP{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KRoot{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCall{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLift{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLiftC{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case 1n+s:
                  {==}
    case R.KCopyL{}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              match v:
                case R.KFree{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KFn{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KAp{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopy{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMerge{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KData{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraN{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraP{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KRoot{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCall{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLift{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLiftC{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case 1n+r:
              match r:
                case 0n:
                  match v:
                    case R.KFree{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KFn{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KAp{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopy{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMerge{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KData{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraN{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraP{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KRoot{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCall{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLift{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLiftC{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case 1n+s:
                  {==}
    case R.KCopyR{}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              match v:
                case R.KFree{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KFn{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KAp{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopy{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMerge{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KData{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraN{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraP{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KRoot{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCall{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLift{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLiftC{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case 1n+r:
              match r:
                case 0n:
                  match v:
                    case R.KFree{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KFn{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KAp{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopy{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMerge{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KData{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraN{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraP{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KRoot{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCall{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLift{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLiftC{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case 1n+s:
                  {==}
    case R.KMergeL{}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              match v:
                case R.KFree{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KFn{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KAp{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopy{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMerge{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KData{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraN{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraP{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KRoot{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCall{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLift{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLiftC{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case 1n+r:
              match r:
                case 0n:
                  match v:
                    case R.KFree{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KFn{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KAp{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopy{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMerge{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KData{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraN{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraP{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KRoot{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCall{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLift{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLiftC{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case 1n+s:
                  {==}
    case R.KMergeR{}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              match v:
                case R.KFree{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KFn{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KAp{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopy{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMerge{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KData{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraN{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KEraP{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KRoot{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCall{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLift{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KLiftC{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KCopyR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeL{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case R.KMergeR{}:
                  match t:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case 1n+r:
              match r:
                case 0n:
                  match v:
                    case R.KFree{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KFn{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KAp{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopy{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMerge{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KData{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraN{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KEraP{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KRoot{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCall{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLift{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KLiftC{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KCopyR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeL{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case R.KMergeR{}:
                      match t:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case 1n+s:
                  {==}

def Laws.events_keep_wired_in(ks, a, b, es, c, q, p, hv, hw):
  kw.r(R.event(W.kind_at(ks, a), W.kind_at(ks, b), q), ks, a, b, es, c, p, hw,
    pinst(p, W.kind_at(ks, a), W.kind_at(ks, b), R.event(W.kind_at(ks, a), W.kind_at(ks, b), q), Laws.events_exact(W.kind_at(ks, a), W.kind_at(ks, b), q), hv))

def Laws.kernel_events_in_step(s, fh, l, ks, a, b, q, hf, hs, hab, hla, hlb, hen):
  kris(R.event(W.kind_at(ks, a), W.kind_at(ks, b), q), s, fh, l, ks, a, b, hf, hs, hab, hla, hlb, hen, Laws.events_kinds_live(W.kind_at(ks, a), W.kind_at(ks, b), q))
