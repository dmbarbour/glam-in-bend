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
