# Blend's own proofs, of the laws LAWS.bend states.

import Base
import ./LAWS.bend as Laws
import ./blend.bend as B
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MNat
import 0x8ae61ec3a6615abd35f196c07232ad28/u32.bend as MU
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import 0x8ae61ec3a6615abd35f196c07232ad28/list.bend as ML

# Bytes
# -----

def u32_is_eq_refl(+a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  %MU.u32_is_eq_to_nat_sym(a, a) : {_ == True{} : Bool}
  MNat.is_eq_refl(U32.to_nat(a))

def u32_nat_is_eq(+a: U32, +b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}:
  %MU.u32_is_eq_to_nat(a, b) : {_ == True{} : Bool}
  h

def u32_eq_of_is_eq(+a: U32, +b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  MU.u32_to_nat_inj(a, b, MNat.eq_of_is_eq(U32.to_nat(a), U32.to_nat(b), u32_nat_is_eq(a, b, h)))

# Names
# -----

# by induction over both names: the heads equal by U32.is_eq, the tails by
# the hypothesis; a name and a longer one are never the same
def Laws.names.same_eq(a, b, h):
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case Con{bh, bt}:
          Empty.absurd({Nil{} == Con{bh, bt} : List<&2, U32>}, MB.false_ne_true()(h))
    case Con{ah, at}:
      match b:
        case Nil{}:
          Empty.absurd({Con{ah, at} == Nil{} : List<&2, U32>}, MB.false_ne_true()(h))
        case Con{bh, bt}:
          %u32_eq_of_is_eq(ah, bh, MB.eq_true_of_and_left(U32.is_eq(ah, bh), B.same(at, bt), h)) : {Con{ah, at} == Con{_, bt} : List<&2, U32>}
          %Laws.names.same_eq(at, bt, MB.eq_true_of_and_right(U32.is_eq(ah, bh), B.same(at, bt), h)) : {Con{ah, at} == Con{ah, _} : List<&2, U32>}
          {==}

def Laws.names.same_refl(a):
  match a:
    case Nil{}:
      {==}
    case Con{ah, at}:
      %Equal.sym(Bool, U32.is_eq(ah, ah), True{}, u32_is_eq_refl(ah)) : {Bool.and(_, B.same(at, at)) == True{} : Bool}
      Laws.names.same_refl(at)

# Dotted names
# ------------
#
# parts.go splits a name at its dots, the part so far reversed in cur and
# the parts done reversed in out; its spec: the parts done, each with its
# dot (dp), then the part so far, then what is left, are what the parts
# it returns join to. The lemmas run simple == complex, so that a
# rewrite turns the complex form in a goal into the simple.

# parts in order, each followed by its dot
def dp(ps: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, r}:
      List.append(&2, U32, p, Con{46, dp(r)})

def assoc_r(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) ->
    {List.append(&2, U32, a, List.append(&2, U32, b, c)) == List.append(&2, U32, List.append(&2, U32, a, b), c) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, a, b), c), List.append(&2, U32, a, List.append(&2, U32, b, c)),
    ML.append_assoc(&2, U32, a, b, c))

def rev_snoc(+xs: List<&2, U32>, +y: U32) -> {List.append(&2, U32, List.reverse(&2, U32, xs), [y]) == List.reverse.go(&2, U32, xs, [y]) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, List.reverse.go(&2, U32, xs, [y]), List.append(&2, U32, List.reverse(&2, U32, xs), [y]),
    ML.reverse_go_spec(&2, U32, xs, [y]))

def revs_snoc(+xs: List<&2, List<&2, U32>>, +y: List<&2, U32>) ->
    {List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, xs), [y]) == List.reverse.go(&2, List<&2, U32>, xs, [y]) : List<&2, List<&2, U32>>}:
  Equal.sym(List<&2, List<&2, U32>>, List.reverse.go(&2, List<&2, U32>, xs, [y]), List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, xs), [y]),
    ML.reverse_go_spec(&2, List<&2, U32>, xs, [y]))

# a part appended: its dot after it
def dp_snoc(ps: List<&2, List<&2, U32>>, +x: List<&2, U32>) ->
    {List.append(&2, U32, dp(ps), List.append(&2, U32, x, [46])) == dp(List.append(&2, List<&2, U32>, ps, [x])) : List<&2, U32>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +r}:
      %dp_snoc(r, x) : {List.append(&2, U32, List.append(&2, U32, p, Con{46, dp(r)}), List.append(&2, U32, x, [46])) == List.append(&2, U32, p, Con{46, _}) : List<&2, U32>}
      ML.append_assoc(&2, U32, p, Con{46, dp(r)}, List.append(&2, U32, x, [46]))

# a part appended, the parts joined
def dots_snoc(ps: List<&2, List<&2, U32>>, +c: List<&2, U32>) ->
    {List.append(&2, U32, dp(ps), c) == B.dots(List.append(&2, List<&2, U32>, ps, [c])) : List<&2, U32>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, r}:
      match r:
        case Nil{}:
          ML.append_assoc(&2, U32, p, [46], c)
        case Con{+q, +r2}:
          %dots_snoc(Con{q, r2}, c) : {List.append(&2, U32, List.append(&2, U32, p, Con{46, dp(Con{q, r2})}), c) == List.append(&2, U32, p, Con{46, _}) : List<&2, U32>}
          ML.append_assoc(&2, U32, p, Con{46, dp(Con{q, r2})}, c)

# a byte after the part so far, a dot or not, b its test (the step's two
# hypotheses, for the tail after a dot and after another byte)
def parts_step(+h: U32, +t: List<&2, U32>, +cur: List<&2, U32>, +out: List<&2, List<&2, U32>>, b: Bool, +e: {b == U32.is_eq(h, 46) : Bool},
    ih1: {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, Con{List.reverse(&2, U32, cur), out})), List.append(&2, U32, List.reverse(&2, U32, Nil{}), t)) ==
      B.dots(B.parts.go(t, Nil{}, Con{List.reverse(&2, U32, cur), out})) : List<&2, U32>},
    ih2: {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, Con{h, cur}), t)) ==
      B.dots(B.parts.go(t, Con{h, cur}, out)) : List<&2, U32>}) ->
    {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{h, t})) ==
      B.dots(B.when(List<&2, List<&2, U32>>, b, u => B.parts.go(t, Nil{}, Con{List.reverse(&2, U32, cur), out}), u => B.parts.go(t, Con{h, cur}, out))) : List<&2, U32>}:
  match b:
    case True{}:
      %Equal.sym(U32, h, 46, u32_eq_of_is_eq(h, 46, Equal.sym(Bool, True{}, U32.is_eq(h, 46), e))) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{_, t})) ==
          B.dots(B.parts.go(t, Nil{}, Con{List.reverse(&2, U32, cur), out})) : List<&2, U32>}
      %ih1 : {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{46, t})) == _ : List<&2, U32>}
      %revs_snoc(out, List.reverse(&2, U32, cur)) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{46, t})) == List.append(&2, U32, dp(_), t) : List<&2, U32>}
      %dp_snoc(List.reverse(&2, List<&2, U32>, out), List.reverse(&2, U32, cur)) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{46, t})) == List.append(&2, U32, _, t) : List<&2, U32>}
      %assoc_r(dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), [46]), t) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{46, t})) == _ : List<&2, U32>}
      %assoc_r(List.reverse(&2, U32, cur), [46], t) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{46, t})) ==
          List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), _) : List<&2, U32>}
      {==}
    case False{}:
      %ih2 : {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{h, t})) == _ : List<&2, U32>}
      %rev_snoc(cur, h) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{h, t})) ==
          List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, _, t)) : List<&2, U32>}
      %assoc_r(List.reverse(&2, U32, cur), [h], t) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{h, t})) ==
          List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), _) : List<&2, U32>}
      {==}

# parts.go's spec, by induction over what is left
def parts_spec(xs: List<&2, U32>, +cur: List<&2, U32>, +out: List<&2, List<&2, U32>>) ->
    {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), xs)) == B.dots(B.parts.go(xs, cur, out)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      %revs_snoc(out, List.reverse(&2, U32, cur)) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) == B.dots(_) : List<&2, U32>}
      %dots_snoc(List.reverse(&2, List<&2, U32>, out), List.reverse(&2, U32, cur)) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) == _ : List<&2, U32>}
      %ML.append_nil(&2, U32, List.reverse(&2, U32, cur)) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) ==
          List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), _) : List<&2, U32>}
      {==}
    case Con{+h, +t}:
      parts_step(h, t, cur, out, U32.is_eq(h, 46), {==}, parts_spec(t, Nil{}, Con{List.reverse(&2, U32, cur), out}), parts_spec(t, Con{h, cur}, out))

def Laws.names.dots_parts(x):
  Equal.sym(List<&2, U32>, x, B.dots(B.parts(x)), parts_spec(x, Nil{}, Nil{}))
