# u32_eq_of_is_eq, from bend-mathlib 0.8.1.0's string.bend (hub package
# 0x8ae61ec3a6615abd35f196c07232ad28; Apache-2.0, ./LICENSE), with the
# helpers it needs. Changed here: copied into a file of their own, and
# the lemma's law and def written as one typed def; the bodies are
# bend-mathlib's. Why, and what uses it: ./SOURCE.md.
#
# The source file's notice:
# bend-mathlib/string.bend: String append, reverse and length, and comparison.

import Base
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MBool

def internal_false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

def internal_fin_head(ab: Bool, bb: Bool, c: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}) -> {ab == bb : Bool}:
  match c:
    case LT{}:
      Empty.absurd({ab == bb : Bool}, internal_false_ne_true(h))
    case EQ{}:
      MBool.eq_of_cmp_eq(ab, bb, h)
    case GT{}:
      Empty.absurd({ab == bb : Bool}, internal_false_ne_true(h))

def internal_fin_tail(ab: Bool, bb: Bool, c: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == True{} : Bool}, internal_false_ne_true(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == True{} : Bool}, internal_false_ne_true(h))

def internal_word_eq(n: Nat, a: Word(n), b: Word(n), +h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %internal_fin_head(ab, bb, Word.cmp(p, at, bt), h) : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
          %internal_word_eq(p, at, bt, internal_fin_tail(ab, bb, Word.cmp(p, at, bt), h)) : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
          {==}

# two U32s that U32.is_eq calls equal are equal
def u32_eq_of_is_eq(a: U32, b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      %internal_word_eq(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}
