# Blend's own proofs, of the laws LAWS.bend states.
#
# Lessons, for the next proof (docs/BendIssues.md has Bend's side):
# - A byte's match (`case 46:` ... `case _:`) leaves a proof stuck, a
#   U32 being a word of bits: code a law follows tests its bytes
#   (`U32.is_eq(h, 46)`) and branches on the Bool, in `when` or in a
#   named helper matching its Bool parameters (`rr.mark.k`); a class of
#   bytes is a datatype (`Cl`), its tests Bools.
# - A recursive proof never matches a computed value: a non-recursive
#   step lemma takes the Bool as a parameter, with both induction
#   hypotheses, and splits it (`parts_step`, `while_step_s`); Bend has
#   no mutual recursion, so the split lives in the step, the recursion in
#   the caller.
# - A lemma's type names a `when`'s branches through a helper def that
#   mirrors them (`while_k`, `lines_k`): Bend infers no lambda.
# - Lemmas run simple == complex, so that `%e : P` (the goal is P with
#   e's right side, and becomes P with its left) rewrites the complex form
#   away; the hub's lemmas run the other way, so wrap them in
#   `Equal.sym` once (`assoc_r`, `rev_snoc`).
# - A result read twice is Data, read by projections (`Rn`, `rn.xs`), not
#   destructured in a lambda (`on.rn`), which sticks a proof.
# - A bound of 2^32 is reasoned under a variable N with {N == 2^32}, the
#   power met only against a symbolic count or where both forms match
#   exactly (`to32`, `top_bound`): Bend unfolds the power otherwise, and
#   its checker overflows.
# - Templates prove as code does: a proof def may take `~p` (`while_s`).
# - Mutate the code after a proof passes: a law that survives a mutation
#   claims less than meant.

import Base
import ./LAWS.bend as Laws
import ./blend.bend as B
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MNat
import 0x8ae61ec3a6615abd35f196c07232ad28/u32.bend as MU
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import 0x8ae61ec3a6615abd35f196c07232ad28/list.bend as ML
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME

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

# Locals
# ------

def list_disc(xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{c, cs}:
      Empty

def cons_ne_nil(+c: U32, +cs: List<&2, U32>, e: {Con{c, cs} == Nil{} : List<&2, U32>}) -> Empty:
  %Equal.sym(List<&2, U32>, Con{c, cs}, Nil{}, e) : list_disc(_)
  Unit{}

def Laws.locals.not_name(cx, o, q, locals, t, no, h):
  match t:
    case B.TName{x}:
      match x:
        case Nil{}:
          {==}
        case Con{c, cs}:
          Empty.absurd({B.rr.of(cx, o, q, locals, B.TName{Con{c, cs}}, no) == B.rr.tok(B.TName{Con{c, cs}}) : B.Rr}, cons_ne_nil(c, cs, h))
    case B.TNum{x}:
      {==}
    case B.TStr{x}:
      {==}
    case B.TCom{x}:
      {==}
    case B.TSp{x}:
      {==}
    case B.TSym{c}:
      {==}

# the middle of three, true, makes them true
def or3_mid(+a: Bool, +b: Bool, +c: Bool, e: {b == True{} : Bool}) -> {Bool.or(Bool.or(a, b), c) == True{} : Bool}:
  %Equal.sym(Bool, b, True{}, e) : {Bool.or(Bool.or(a, _), c) == True{} : Bool}
  %MB.or_true_sym(a) : {Bool.or(_, c) == True{} : Bool}
  {==}

# a local, found, is kept: rr.plain's test and rr.under's, each a Bool
# the hypothesis says is True
def plain_kept(+local: Bool, +e: {local == True{} : Bool}, +cx: B.Cx, +o: U32, +q: U32, +mark: U32, +n: List<&2, U32>, +t: B.Tok, +no: U32) ->
    {B.rr.plain.k(local, cx, o, q, mark, n, t, no) == B.rr.tok(t) : B.Rr}:
  match local:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({B.rr.plain.k(False{}, cx, o, q, mark, n, t, no) == B.rr.tok(t) : B.Rr}, MB.false_ne_true()(e))

def under_kept(+local: Bool, +e: {local == True{} : Bool}, +cx: B.Cx, +o: U32, +q: U32, +r: List<&2, U32>, +t: B.Tok, +no: U32) ->
    {B.rr.under(local, cx, o, q, r, t, no) == B.rr.tok(t) : B.Rr}:
  match local:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({B.rr.under(False{}, cx, o, q, r, t, no) == B.rr.tok(t) : B.Rr}, MB.false_ne_true()(e))

# a plain name or `_n`, its first byte's tests split: `^` and `~` false
# by the hypotheses, `_` either way
def mark_kept(+up: Bool, a: {up == False{} : Bool}, +tpl: Bool, b: {tpl == False{} : Bool}, +under: Bool,
    +cx: B.Cx, +o: U32, +q: U32, +locals: List<&2, List<&2, U32>>, +h: U32, +r: List<&2, U32>, +no: U32,
    +l: {B.names.has(locals, Con{h, r}) == True{} : Bool}) ->
    {B.rr.mark.k(up, tpl, under, cx, o, q, locals, h, r, B.TName{Con{h, r}}, no) == B.rr.tok(B.TName{Con{h, r}}) : B.Rr}:
  match up:
    case True{}:
      Empty.absurd({B.rr.mark.k(True{}, tpl, under, cx, o, q, locals, h, r, B.TName{Con{h, r}}, no) == B.rr.tok(B.TName{Con{h, r}}) : B.Rr},
        MB.true_ne_false()(a))
    case False{}:
      match tpl:
        case True{}:
          Empty.absurd({B.rr.mark.k(False{}, True{}, under, cx, o, q, locals, h, r, B.TName{Con{h, r}}, no) == B.rr.tok(B.TName{Con{h, r}}) : B.Rr},
            MB.true_ne_false()(b))
        case False{}:
          match under:
            case True{}:
              under_kept(Bool.or(Bool.or(B.blank(r), B.names.has(locals, Con{h, r})), B.is.root(B.cx.obs(cx), o)),
                or3_mid(B.blank(r), B.names.has(locals, Con{h, r}), B.is.root(B.cx.obs(cx), o), l), cx, o, q, r, B.TName{Con{h, r}}, no)
            case False{}:
              plain_kept(B.names.has(locals, Con{h, r}), l, cx, o, q, 0, Con{h, r}, B.TName{Con{h, r}}, no)

def Laws.locals.kept(cx, o, q, locals, h, r, no, a, b, l):
  mark_kept(U32.is_eq(h, 94), a, U32.is_eq(h, 126), b, U32.is_eq(h, 95), cx, o, q, locals, h, r, no, l)

def Laws.locals.template(cx, o, q, locals, r, no, l):
  plain_kept(B.names.has(locals, r), l, cx, o, q, 126, r, B.TName{Con{126, r}}, no)

# Tokens
# ------
#
# toks.go takes a token a turn, the fuel the line's length, the classes
# in step with the bytes: what the tokens so far spell, then what is
# left, is what the tokens it returns spell. A run's lemmas: what it took
# reversed back, then what it left, is what it was given after what it
# had (spelt); its classes stay in step (len); it leaves no more than it
# was given (le). The run's choice, a Bool, is split by a step lemma.

def len_classes(xs: List<&2, U32>) -> {List.length(&2, B.Cl, B.classes(xs)) == List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      ME.cong_succ(List.length(&2, B.Cl, B.classes(t)), List.length(&2, U32, t), len_classes(t))

def text_append(a: List<&2, B.Tok>, +b: List<&2, B.Tok>) ->
    {List.append(&2, U32, B.toks.text(a), B.toks.text(b)) == B.toks.text(List.append(&2, B.Tok, a, b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %text_append(r, b) : {List.append(&2, U32, List.append(&2, U32, B.tok.bytes(x), B.toks.text(r)), B.toks.text(b)) == List.append(&2, U32, B.tok.bytes(x), _) : List<&2, U32>}
      ML.append_assoc(&2, U32, B.tok.bytes(x), B.toks.text(r), B.toks.text(b))

def text_snoc(+out: List<&2, B.Tok>, +x: B.Tok) ->
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), B.tok.bytes(x)) == B.toks.text(List.reverse(&2, B.Tok, Con{x, out})) : List<&2, U32>}:
  %Equal.sym(List<&2, B.Tok>, List.reverse.go(&2, B.Tok, out, [x]), List.append(&2, B.Tok, List.reverse(&2, B.Tok, out), [x]), ML.reverse_go_spec(&2, B.Tok, out, [x])) :
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), B.tok.bytes(x)) == B.toks.text(_) : List<&2, U32>}
  %text_append(List.reverse(&2, B.Tok, out), [x]) :
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), B.tok.bytes(x)) == _ : List<&2, U32>}
  %ML.append_nil(&2, U32, B.tok.bytes(x)) :
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), _) == List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), List.append(&2, U32, B.tok.bytes(x), Nil{})) : List<&2, U32>}
  {==}

# what a run spells
def spelt(+r: B.Rn) -> List<&2, U32>:
  List.append(&2, U32, List.reverse(&2, U32, B.rn.acc(r)), B.rn.xs(r))

# a byte taken after acc: what is left after it, so spelt
def took(+acc: List<&2, U32>, +h: U32, +t: List<&2, U32>) ->
    {List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t}) == List.append(&2, U32, List.reverse(&2, U32, Con{h, acc}), t) : List<&2, U32>}:
  %rev_snoc(acc, h) : {List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t}) == List.append(&2, U32, _, t) : List<&2, U32>}
  %assoc_r(List.reverse(&2, U32, acc), [h], t) : {List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t}) == _ : List<&2, U32>}
  {==}

# Runs while a class test holds

def while_k(~p: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, +b: Bool) -> B.Rn:
  B.when(B.Rn, b, u => B.run.while(~p, t, ct, Con{h, acc}), u => B.Rn{acc, Con{h, t}, Con{c, ct}})

def while_step_s(~p: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, b: Bool,
    ih: {List.append(&2, U32, List.reverse(&2, U32, Con{h, acc}), t) == spelt(B.run.while(~p, t, ct, Con{h, acc})) : List<&2, U32>}) ->
    {List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t}) == spelt(while_k(~p, h, t, c, ct, acc, b)) : List<&2, U32>}:
  match b:
    case True{}:
      Equal.trans(List<&2, U32>, List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t}), List.append(&2, U32, List.reverse(&2, U32, Con{h, acc}), t),
        spelt(B.run.while(~p, t, ct, Con{h, acc})), took(acc, h, t), ih)
    case False{}:
      {==}

def while_s(~p: B.Cl -> Bool, t: List<&2, U32>, ct: List<&2, B.Cl>, +acc: List<&2, U32>, +al: {List.length(&2, B.Cl, ct) == List.length(&2, U32, t) : Nat}) ->
    {List.append(&2, U32, List.reverse(&2, U32, acc), t) == spelt(B.run.while(~p, t, ct, acc)) : List<&2, U32>}:
  match t:
    case Nil{}:
      match ct:
        case Nil{}:
          {==}
        case Con{+c, +ct2}:
          Empty.absurd({List.append(&2, U32, List.reverse(&2, U32, acc), Nil{}) == spelt(B.run.while(~p, Nil{}, Con{c, ct2}, acc)) : List<&2, U32>},
            MNat.succ_ne_zero(List.length(&2, B.Cl, ct2))(al))
    case Con{+h, +t2}:
      match ct:
        case Nil{}:
          Empty.absurd({List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t2}) == spelt(B.run.while(~p, Con{h, t2}, Nil{}, acc)) : List<&2, U32>},
            MNat.zero_ne_succ(List.length(&2, U32, t2))(al))
        case Con{+c, +ct2}:
          while_step_s(~p, h, t2, c, ct2, acc, p(c),
            while_s(~p, t2, ct2, Con{h, acc}, MNat.succ_inj(List.length(&2, B.Cl, ct2), List.length(&2, U32, t2), al)))

def while_step_a(~p: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, b: Bool,
    al: {List.length(&2, B.Cl, Con{c, ct}) == List.length(&2, U32, Con{h, t}) : Nat},
    ih: {List.length(&2, B.Cl, B.rn.cs(B.run.while(~p, t, ct, Con{h, acc}))) == List.length(&2, U32, B.rn.xs(B.run.while(~p, t, ct, Con{h, acc}))) : Nat}) ->
    {List.length(&2, B.Cl, B.rn.cs(while_k(~p, h, t, c, ct, acc, b))) == List.length(&2, U32, B.rn.xs(while_k(~p, h, t, c, ct, acc, b))) : Nat}:
  match b:
    case True{}:
      ih
    case False{}:
      al

def while_a(~p: B.Cl -> Bool, t: List<&2, U32>, ct: List<&2, B.Cl>, +acc: List<&2, U32>, +al: {List.length(&2, B.Cl, ct) == List.length(&2, U32, t) : Nat}) ->
    {List.length(&2, B.Cl, B.rn.cs(B.run.while(~p, t, ct, acc))) == List.length(&2, U32, B.rn.xs(B.run.while(~p, t, ct, acc))) : Nat}:
  match t:
    case Nil{}:
      match ct:
        case Nil{}:
          {==}
        case Con{+c, +ct2}:
          Empty.absurd({List.length(&2, B.Cl, B.rn.cs(B.run.while(~p, Nil{}, Con{c, ct2}, acc))) == List.length(&2, U32, B.rn.xs(B.run.while(~p, Nil{}, Con{c, ct2}, acc))) : Nat},
            MNat.succ_ne_zero(List.length(&2, B.Cl, ct2))(al))
    case Con{+h, +t2}:
      match ct:
        case Nil{}:
          Empty.absurd({List.length(&2, B.Cl, B.rn.cs(B.run.while(~p, Con{h, t2}, Nil{}, acc))) == List.length(&2, U32, B.rn.xs(B.run.while(~p, Con{h, t2}, Nil{}, acc))) : Nat},
            MNat.zero_ne_succ(List.length(&2, U32, t2))(al))
        case Con{+c, +ct2}:
          while_step_a(~p, h, t2, c, ct2, acc, p(c), al,
            while_a(~p, t2, ct2, Con{h, acc}, MNat.succ_inj(List.length(&2, B.Cl, ct2), List.length(&2, U32, t2), al)))

def while_step_p(~p: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, b: Bool,
    ih: MNat.le(List.length(&2, U32, B.rn.xs(B.run.while(~p, t, ct, Con{h, acc}))), List.length(&2, U32, t))) ->
    MNat.le(List.length(&2, U32, B.rn.xs(while_k(~p, h, t, c, ct, acc, b))), List.length(&2, U32, Con{h, t})):
  match b:
    case True{}:
      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.while(~p, t, ct, Con{h, acc}))), List.length(&2, U32, t), List.length(&2, U32, Con{h, t}),
        ih, MNat.le_succ(List.length(&2, U32, t)))
    case False{}:
      MNat.le_refl(List.length(&2, U32, Con{h, t}))

def while_p(~p: B.Cl -> Bool, t: List<&2, U32>, ct: List<&2, B.Cl>, +acc: List<&2, U32>) ->
    MNat.le(List.length(&2, U32, B.rn.xs(B.run.while(~p, t, ct, acc))), List.length(&2, U32, t)):
  match t:
    case Nil{}:
      match ct:
        case Nil{}:
          MNat.le_refl(0n)
        case Con{c, ct2}:
          MNat.le_refl(0n)
    case Con{+h, +t2}:
      match ct:
        case Nil{}:
          MNat.zero_le(List.length(&2, U32, Con{h, t2}))
        case Con{+c, +ct2}:
          while_step_p(~p, h, t2, c, ct2, acc, p(c), while_p(~p, t2, ct2, Con{h, acc}))

# Quoted runs, to a closing quote

def quoted_k(~shut: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, +esc: Bool, +b: Bool) -> B.Rn:
  B.when(B.Rn, b, u => B.Rn{Con{h, acc}, t, ct}, u => B.run.quoted(~shut, t, ct, Con{h, acc}, B.cl.back(c) && Bool.not(esc)))

def quoted_step_s(~shut: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, +esc: Bool, b: Bool,
    ih: {List.append(&2, U32, List.reverse(&2, U32, Con{h, acc}), t) == spelt(B.run.quoted(~shut, t, ct, Con{h, acc}, B.cl.back(c) && Bool.not(esc))) : List<&2, U32>}) ->
    {List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t}) == spelt(quoted_k(~shut, h, t, c, ct, acc, esc, b)) : List<&2, U32>}:
  match b:
    case True{}:
      took(acc, h, t)
    case False{}:
      Equal.trans(List<&2, U32>, List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t}), List.append(&2, U32, List.reverse(&2, U32, Con{h, acc}), t),
        spelt(B.run.quoted(~shut, t, ct, Con{h, acc}, B.cl.back(c) && Bool.not(esc))), took(acc, h, t), ih)

def quoted_s(~shut: B.Cl -> Bool, t: List<&2, U32>, ct: List<&2, B.Cl>, +acc: List<&2, U32>, +esc: Bool, +al: {List.length(&2, B.Cl, ct) == List.length(&2, U32, t) : Nat}) ->
    {List.append(&2, U32, List.reverse(&2, U32, acc), t) == spelt(B.run.quoted(~shut, t, ct, acc, esc)) : List<&2, U32>}:
  match t:
    case Nil{}:
      match ct:
        case Nil{}:
          {==}
        case Con{+c, +ct2}:
          Empty.absurd({List.append(&2, U32, List.reverse(&2, U32, acc), Nil{}) == spelt(B.run.quoted(~shut, Nil{}, Con{c, ct2}, acc, esc)) : List<&2, U32>},
            MNat.succ_ne_zero(List.length(&2, B.Cl, ct2))(al))
    case Con{+h, +t2}:
      match ct:
        case Nil{}:
          Empty.absurd({List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t2}) == spelt(B.run.quoted(~shut, Con{h, t2}, Nil{}, acc, esc)) : List<&2, U32>},
            MNat.zero_ne_succ(List.length(&2, U32, t2))(al))
        case Con{+c, +ct2}:
          quoted_step_s(~shut, h, t2, c, ct2, acc, esc, shut(c) && Bool.not(esc),
            quoted_s(~shut, t2, ct2, Con{h, acc}, B.cl.back(c) && Bool.not(esc), MNat.succ_inj(List.length(&2, B.Cl, ct2), List.length(&2, U32, t2), al)))

def quoted_step_a(~shut: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, +esc: Bool, b: Bool,
    al: {List.length(&2, B.Cl, ct) == List.length(&2, U32, t) : Nat},
    ih: {List.length(&2, B.Cl, B.rn.cs(B.run.quoted(~shut, t, ct, Con{h, acc}, B.cl.back(c) && Bool.not(esc)))) ==
      List.length(&2, U32, B.rn.xs(B.run.quoted(~shut, t, ct, Con{h, acc}, B.cl.back(c) && Bool.not(esc)))) : Nat}) ->
    {List.length(&2, B.Cl, B.rn.cs(quoted_k(~shut, h, t, c, ct, acc, esc, b))) == List.length(&2, U32, B.rn.xs(quoted_k(~shut, h, t, c, ct, acc, esc, b))) : Nat}:
  match b:
    case True{}:
      al
    case False{}:
      ih

def quoted_a(~shut: B.Cl -> Bool, t: List<&2, U32>, ct: List<&2, B.Cl>, +acc: List<&2, U32>, +esc: Bool, +al: {List.length(&2, B.Cl, ct) == List.length(&2, U32, t) : Nat}) ->
    {List.length(&2, B.Cl, B.rn.cs(B.run.quoted(~shut, t, ct, acc, esc))) == List.length(&2, U32, B.rn.xs(B.run.quoted(~shut, t, ct, acc, esc))) : Nat}:
  match t:
    case Nil{}:
      match ct:
        case Nil{}:
          {==}
        case Con{+c, +ct2}:
          Empty.absurd({List.length(&2, B.Cl, B.rn.cs(B.run.quoted(~shut, Nil{}, Con{c, ct2}, acc, esc))) == List.length(&2, U32, B.rn.xs(B.run.quoted(~shut, Nil{}, Con{c, ct2}, acc, esc))) : Nat},
            MNat.succ_ne_zero(List.length(&2, B.Cl, ct2))(al))
    case Con{+h, +t2}:
      match ct:
        case Nil{}:
          Empty.absurd({List.length(&2, B.Cl, B.rn.cs(B.run.quoted(~shut, Con{h, t2}, Nil{}, acc, esc))) == List.length(&2, U32, B.rn.xs(B.run.quoted(~shut, Con{h, t2}, Nil{}, acc, esc))) : Nat},
            MNat.zero_ne_succ(List.length(&2, U32, t2))(al))
        case Con{+c, +ct2}:
          quoted_step_a(~shut, h, t2, c, ct2, acc, esc, shut(c) && Bool.not(esc), MNat.succ_inj(List.length(&2, B.Cl, ct2), List.length(&2, U32, t2), al),
            quoted_a(~shut, t2, ct2, Con{h, acc}, B.cl.back(c) && Bool.not(esc), MNat.succ_inj(List.length(&2, B.Cl, ct2), List.length(&2, U32, t2), al)))

def quoted_step_p(~shut: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, +esc: Bool, b: Bool,
    ih: MNat.le(List.length(&2, U32, B.rn.xs(B.run.quoted(~shut, t, ct, Con{h, acc}, B.cl.back(c) && Bool.not(esc)))), List.length(&2, U32, t))) ->
    MNat.le(List.length(&2, U32, B.rn.xs(quoted_k(~shut, h, t, c, ct, acc, esc, b))), List.length(&2, U32, Con{h, t})):
  match b:
    case True{}:
      MNat.le_succ(List.length(&2, U32, t))
    case False{}:
      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.quoted(~shut, t, ct, Con{h, acc}, B.cl.back(c) && Bool.not(esc)))), List.length(&2, U32, t), List.length(&2, U32, Con{h, t}),
        ih, MNat.le_succ(List.length(&2, U32, t)))

def quoted_p(~shut: B.Cl -> Bool, t: List<&2, U32>, ct: List<&2, B.Cl>, +acc: List<&2, U32>, +esc: Bool) ->
    MNat.le(List.length(&2, U32, B.rn.xs(B.run.quoted(~shut, t, ct, acc, esc))), List.length(&2, U32, t)):
  match t:
    case Nil{}:
      match ct:
        case Nil{}:
          MNat.le_refl(0n)
        case Con{c, ct2}:
          MNat.le_refl(0n)
    case Con{+h, +t2}:
      match ct:
        case Nil{}:
          MNat.zero_le(List.length(&2, U32, Con{h, t2}))
        case Con{+c, +ct2}:
          quoted_step_p(~shut, h, t2, c, ct2, acc, esc, shut(c) && Bool.not(esc), quoted_p(~shut, t2, ct2, Con{h, acc}, B.cl.back(c) && Bool.not(esc)))

# The tokens

# a symbol's token, a byte alone
def sym_step(+out: List<&2, B.Tok>, +h: U32, +t: List<&2, U32>, +k: Nat, +ct: List<&2, B.Cl>,
    ih: {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, Con{B.TSym{h}, out})), t) == B.toks.text(B.toks.go(k, t, ct, Con{B.TSym{h}, out})) : List<&2, U32>}) ->
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == B.toks.text(B.toks.go(k, t, ct, Con{B.TSym{h}, out})) : List<&2, U32>}:
  %ih : {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == _ : List<&2, U32>}
  %text_snoc(out, B.TSym{h}) : {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == List.append(&2, U32, _, t) : List<&2, U32>}
  %assoc_r(B.toks.text(List.reverse(&2, B.Tok, out)), [h], t) : {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == _ : List<&2, U32>}
  {==}

# a run's token, mk making it of the bytes the run took: those bytes
# spelt by the run (s), the rest by the hypothesis
def run_step(~mk: List<&2, U32> -> B.Tok, +out: List<&2, B.Tok>, +h: U32, +t: List<&2, U32>, +k: Nat, +r: B.Rn,
    +s: {Con{h, t} == spelt(r) : List<&2, U32>},
    mb: {B.tok.bytes(mk(List.reverse(&2, U32, B.rn.acc(r)))) == List.reverse(&2, U32, B.rn.acc(r)) : List<&2, U32>},
    ih: {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, Con{mk(List.reverse(&2, U32, B.rn.acc(r))), out})), B.rn.xs(r)) ==
      B.toks.text(B.toks.go(k, B.rn.xs(r), B.rn.cs(r), Con{mk(List.reverse(&2, U32, B.rn.acc(r))), out})) : List<&2, U32>}) ->
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) ==
      B.toks.text(B.toks.go(k, B.rn.xs(r), B.rn.cs(r), Con{mk(List.reverse(&2, U32, B.rn.acc(r))), out})) : List<&2, U32>}:
  %ih : {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == _ : List<&2, U32>}
  %text_snoc(out, mk(List.reverse(&2, U32, B.rn.acc(r)))) :
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == List.append(&2, U32, _, B.rn.xs(r)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.tok.bytes(mk(List.reverse(&2, U32, B.rn.acc(r)))), List.reverse(&2, U32, B.rn.acc(r)), mb) :
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) ==
      List.append(&2, U32, List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), _), B.rn.xs(r)) : List<&2, U32>}
  %assoc_r(B.toks.text(List.reverse(&2, B.Tok, out)), List.reverse(&2, U32, B.rn.acc(r)), B.rn.xs(r)) :
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == _ : List<&2, U32>}
  %s : {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), _) : List<&2, U32>}
  {==}

# what the tokens so far spell, then what is left, is what the tokens
# returned spell, given fuel for each byte left and classes in step
def toks_spell(n: Nat, xs: List<&2, U32>, cs: List<&2, B.Cl>, +out: List<&2, B.Tok>,
    +al: {List.length(&2, B.Cl, cs) == List.length(&2, U32, xs) : Nat}, +f: MNat.le(List.length(&2, U32, xs), n)) ->
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), xs) == B.toks.text(B.toks.go(n, xs, cs, out)) : List<&2, U32>}:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          ML.append_nil(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)))
        case Con{+h, +t}:
          Empty.absurd({List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == B.toks.text(B.toks.go(0n, Con{h, t}, cs, out)) : List<&2, U32>},
            MB.false_ne_true()(f))
    case 1n+(+k):
      match xs:
        case Nil{}:
          match cs:
            case Nil{}:
              ML.append_nil(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)))
            case Con{c, ct}:
              ML.append_nil(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)))
        case Con{+h, +t}:
          match cs:
            case Nil{}:
              Empty.absurd({List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == B.toks.text(B.toks.go(1n+k, Con{h, t}, Nil{}, out)) : List<&2, U32>},
                MNat.zero_ne_succ(List.length(&2, U32, t))(al))
            case Con{c, +ct}:
              match c:
                case B.CSp{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  run_step(~(x => B.TSp{x}), out, h, t, k, B.run.while(~B.cl.sp, t, ct, [h]), while_s(~B.cl.sp, t, ct, [h], al1), {==},
                    toks_spell(k, B.rn.xs(B.run.while(~B.cl.sp, t, ct, [h])), B.rn.cs(B.run.while(~B.cl.sp, t, ct, [h])), Con{B.TSp{List.reverse(&2, U32, B.rn.acc(B.run.while(~B.cl.sp, t, ct, [h])))}, out},
                      while_a(~B.cl.sp, t, ct, [h], al1),
                      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.while(~B.cl.sp, t, ct, [h]))), List.length(&2, U32, t), k, while_p(~B.cl.sp, t, ct, [h]), f1)))
                case B.CAlpha{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  run_step(~(x => B.TName{x}), out, h, t, k, B.run.while(~B.cl.name, t, ct, [h]), while_s(~B.cl.name, t, ct, [h], al1), {==},
                    toks_spell(k, B.rn.xs(B.run.while(~B.cl.name, t, ct, [h])), B.rn.cs(B.run.while(~B.cl.name, t, ct, [h])), Con{B.TName{List.reverse(&2, U32, B.rn.acc(B.run.while(~B.cl.name, t, ct, [h])))}, out},
                      while_a(~B.cl.name, t, ct, [h], al1),
                      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.while(~B.cl.name, t, ct, [h]))), List.length(&2, U32, t), k, while_p(~B.cl.name, t, ct, [h]), f1)))
                case B.CDigit{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  run_step(~(x => B.TNum{x}), out, h, t, k, B.run.while(~B.cl.alnum, t, ct, [h]), while_s(~B.cl.alnum, t, ct, [h], al1), {==},
                    toks_spell(k, B.rn.xs(B.run.while(~B.cl.alnum, t, ct, [h])), B.rn.cs(B.run.while(~B.cl.alnum, t, ct, [h])), Con{B.TNum{List.reverse(&2, U32, B.rn.acc(B.run.while(~B.cl.alnum, t, ct, [h])))}, out},
                      while_a(~B.cl.alnum, t, ct, [h], al1),
                      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.while(~B.cl.alnum, t, ct, [h]))), List.length(&2, U32, t), k, while_p(~B.cl.alnum, t, ct, [h]), f1)))
                case B.CQuote{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  run_step(~(x => B.TStr{x}), out, h, t, k, B.run.quoted(~B.cl.quote, t, ct, [h], False{}), quoted_s(~B.cl.quote, t, ct, [h], False{}, al1), {==},
                    toks_spell(k, B.rn.xs(B.run.quoted(~B.cl.quote, t, ct, [h], False{})), B.rn.cs(B.run.quoted(~B.cl.quote, t, ct, [h], False{})), Con{B.TStr{List.reverse(&2, U32, B.rn.acc(B.run.quoted(~B.cl.quote, t, ct, [h], False{})))}, out},
                      quoted_a(~B.cl.quote, t, ct, [h], False{}, al1),
                      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.quoted(~B.cl.quote, t, ct, [h], False{}))), List.length(&2, U32, t), k, quoted_p(~B.cl.quote, t, ct, [h], False{}), f1)))
                case B.CHash{}:
                  text_snoc(out, B.TCom{Con{h, t}})
                case B.CCaret{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  run_step(~(x => B.TName{x}), out, h, t, k, B.run.host(B.run.while(~B.cl.caret, t, ct, [h])),
                    Equal.trans(List<&2, U32>, Con{h, t}, spelt(B.run.while(~B.cl.caret, t, ct, [h])), spelt(B.run.host(B.run.while(~B.cl.caret, t, ct, [h]))), while_s(~B.cl.caret, t, ct, [h], al1),
                      while_s(~B.cl.name, B.rn.xs(B.run.while(~B.cl.caret, t, ct, [h])), B.rn.cs(B.run.while(~B.cl.caret, t, ct, [h])), B.rn.acc(B.run.while(~B.cl.caret, t, ct, [h])), while_a(~B.cl.caret, t, ct, [h], al1))), {==},
                    toks_spell(k, B.rn.xs(B.run.host(B.run.while(~B.cl.caret, t, ct, [h]))), B.rn.cs(B.run.host(B.run.while(~B.cl.caret, t, ct, [h]))), Con{B.TName{List.reverse(&2, U32, B.rn.acc(B.run.host(B.run.while(~B.cl.caret, t, ct, [h]))))}, out},
                      while_a(~B.cl.name, B.rn.xs(B.run.while(~B.cl.caret, t, ct, [h])), B.rn.cs(B.run.while(~B.cl.caret, t, ct, [h])), B.rn.acc(B.run.while(~B.cl.caret, t, ct, [h])), while_a(~B.cl.caret, t, ct, [h], al1)),
                      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.host(B.run.while(~B.cl.caret, t, ct, [h])))), List.length(&2, U32, B.rn.xs(B.run.while(~B.cl.caret, t, ct, [h]))), k,
                        while_p(~B.cl.name, B.rn.xs(B.run.while(~B.cl.caret, t, ct, [h])), B.rn.cs(B.run.while(~B.cl.caret, t, ct, [h])), B.rn.acc(B.run.while(~B.cl.caret, t, ct, [h]))),
                        MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.while(~B.cl.caret, t, ct, [h]))), List.length(&2, U32, t), k, while_p(~B.cl.caret, t, ct, [h]), f1))))
                case B.CTilde{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  run_step(~(x => B.TName{x}), out, h, t, k, B.run.while(~B.cl.name, t, ct, [h]), while_s(~B.cl.name, t, ct, [h], al1), {==},
                    toks_spell(k, B.rn.xs(B.run.while(~B.cl.name, t, ct, [h])), B.rn.cs(B.run.while(~B.cl.name, t, ct, [h])), Con{B.TName{List.reverse(&2, U32, B.rn.acc(B.run.while(~B.cl.name, t, ct, [h])))}, out},
                      while_a(~B.cl.name, t, ct, [h], al1),
                      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.while(~B.cl.name, t, ct, [h]))), List.length(&2, U32, t), k, while_p(~B.cl.name, t, ct, [h]), f1)))
                case B.CTick{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  run_step(~(x => B.TStr{x}), out, h, t, k, B.run.quoted(~B.cl.tick, t, ct, [h], False{}), quoted_s(~B.cl.tick, t, ct, [h], False{}, al1), {==},
                    toks_spell(k, B.rn.xs(B.run.quoted(~B.cl.tick, t, ct, [h], False{})), B.rn.cs(B.run.quoted(~B.cl.tick, t, ct, [h], False{})), Con{B.TStr{List.reverse(&2, U32, B.rn.acc(B.run.quoted(~B.cl.tick, t, ct, [h], False{})))}, out},
                      quoted_a(~B.cl.tick, t, ct, [h], False{}, al1),
                      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.quoted(~B.cl.tick, t, ct, [h], False{}))), List.length(&2, U32, t), k, quoted_p(~B.cl.tick, t, ct, [h], False{}), f1)))
                case B.CDot{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  sym_step(out, h, t, k, ct, toks_spell(k, t, ct, Con{B.TSym{h}, out}, al1, f1))
                case B.CBack{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  sym_step(out, h, t, k, ct, toks_spell(k, t, ct, Con{B.TSym{h}, out}, al1, f1))
                case B.COther{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  sym_step(out, h, t, k, ct, toks_spell(k, t, ct, Con{B.TSym{h}, out}, al1, f1))

def Laws.tokens.spell(xs):
  Equal.sym(List<&2, U32>, xs, B.toks.text(B.toks(xs)),
    toks_spell(List.length(&2, U32, xs), xs, B.classes(xs), Nil{}, len_classes(xs), MNat.le_refl(List.length(&2, U32, xs))))

# Lines
# -----
#
# lines.go keeps the line so far reversed in cur and the lines done
# reversed in out: the lines done, each with its newline (jl), then the
# line so far, then what is left less its carriage returns, are what the
# lines it returns join to. A line's indentation is counted in a Nat and
# kept in a U32, exact for a file shorter than 2^32 bytes (lim).

def lim_left(+a: Nat, +b: Nat, +N: Nat, h: MNat.lt(Nat.add(a, b), N)) -> MNat.lt(a, N):
  MNat.lt_of_le_of_lt(a, Nat.add(a, b), N, MNat.le_add_right(a, b), h)

def lim_right(+a: Nat, +b: Nat, +N: Nat, h: MNat.lt(Nat.add(a, b), N)) -> MNat.lt(b, N):
  MNat.lt_of_le_of_lt(b, Nat.add(a, b), N,
    ME.subst(Nat, x => MNat.le(b, x), Nat.add(b, a), Nat.add(a, b), MNat.add_comm(b, a), MNat.le_add_right(b, a)), h)

def lim_succ(+a: Nat, +m: Nat, +N: Nat, h: MNat.lt(Nat.add(a, 1n+m), N)) -> MNat.lt(1n+Nat.add(a, m), N):
  ME.subst(Nat, x => MNat.lt(x, N), Nat.add(a, 1n+m), 1n+Nat.add(a, m), MNat.add_succ(a, m), h)

def lim_pred(+x: Nat, +N: Nat, h: MNat.lt(1n+x, N)) -> MNat.lt(x, N):
  MNat.lt_of_le_of_lt(x, 1n+x, N, MNat.le_succ(x), h)

def lim_zero(+a: Nat, +N: Nat, h: MNat.lt(Nat.add(a, 0n), N)) -> MNat.lt(a, N):
  ME.subst(Nat, x => MNat.lt(x, N), Nat.add(a, 0n), a, MNat.add_zero(a), h)

def lim_rev(+cur: List<&2, U32>, +N: Nat, h: MNat.lt(List.length(&2, U32, cur), N)) -> MNat.lt(List.length(&2, U32, List.reverse(&2, U32, cur)), N):
  ME.subst(Nat, x => MNat.lt(x, N), List.length(&2, U32, cur), List.length(&2, U32, List.reverse(&2, U32, cur)),
    Equal.sym(Nat, List.length(&2, U32, List.reverse(&2, U32, cur)), List.length(&2, U32, cur), ML.length_reverse(&2, U32, cur)), h)

# a bound abstract, known to be 2^32: a concrete bound behind a successor
# makes Bend unfold 2^32 when it compares, overflowing its stack
def to32(+n: Nat, +N: Nat, +hN: {N == Nat.pow(2n, 32n) : Nat}, h: MNat.lt(n, N)) -> MNat.lt(n, Nat.pow(2n, 32n)):
  ME.subst(Nat, M => MNat.lt(n, M), N, Nat.pow(2n, 32n), hN, h)

# a space after spaces
def sp_snoc(n: Nat, +t: List<&2, U32>) ->
    {List.append(&2, U32, List.replicate(U32, n, 32), Con{32, t}) == Con{32, List.append(&2, U32, List.replicate(U32, n, 32), t)} : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %sp_snoc(k, t) : {Con{32, List.append(&2, U32, List.replicate(U32, k, 32), Con{32, t})} == Con{32, _} : List<&2, U32>}
      {==}

def line_step(+c: U32, +t: List<&2, U32>, +n: Nat, +no: U32, +N: Nat, +hN: {N == Nat.pow(2n, 32n) : Nat}, b: Bool, +e: {b == U32.is_eq(c, 32) : Bool},
    +h: MNat.lt(Nat.add(n, 1n+List.length(&2, U32, t)), N),
    ih: {List.append(&2, U32, List.replicate(U32, 1n+n, 32), t) == B.ln.text(B.line.of(t, 1n+n, no)) : List<&2, U32>}) ->
    {List.append(&2, U32, List.replicate(U32, n, 32), Con{c, t}) ==
      B.ln.text(B.when(B.Ln, b, u => B.line.of(t, 1n+n, no), u => B.Ln{no, U32.from_nat(n), Con{c, t}})) : List<&2, U32>}:
  match b:
    case True{}:
      %Equal.sym(U32, c, 32, u32_eq_of_is_eq(c, 32, Equal.sym(Bool, True{}, U32.is_eq(c, 32), e))) :
        {List.append(&2, U32, List.replicate(U32, n, 32), Con{_, t}) == B.ln.text(B.line.of(t, 1n+n, no)) : List<&2, U32>}
      %ih : {List.append(&2, U32, List.replicate(U32, n, 32), Con{32, t}) == _ : List<&2, U32>}
      sp_snoc(n, t)
    case False{}:
      %MU.u32_to_nat_from_nat_sym(n, to32(n, N, hN, lim_left(n, 1n+List.length(&2, U32, t), N, h))) :
        {List.append(&2, U32, List.replicate(U32, n, 32), Con{c, t}) == List.append(&2, U32, List.replicate(U32, _, 32), Con{c, t}) : List<&2, U32>}
      {==}

# a line read: its spaces counted, then its text, are its bytes
def line_text(xs: List<&2, U32>, +n: Nat, +no: U32, +N: Nat, +hN: {N == Nat.pow(2n, 32n) : Nat}, +h: MNat.lt(Nat.add(n, List.length(&2, U32, xs)), N)) ->
    {List.append(&2, U32, List.replicate(U32, n, 32), xs) == B.ln.text(B.line.of(xs, n, no)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      %MU.u32_to_nat_from_nat_sym(n, to32(n, N, hN, lim_zero(n, N, h))) :
        {List.append(&2, U32, List.replicate(U32, n, 32), Nil{}) == List.append(&2, U32, List.replicate(U32, _, 32), Nil{}) : List<&2, U32>}
      {==}
    case Con{+c, +t}:
      line_step(c, t, n, no, N, hN, U32.is_eq(c, 32), {==}, h, line_text(t, 1n+n, no, N, hN, lim_succ(n, List.length(&2, U32, t), N, h)))

# lines in order, each followed by its newline
def jl(ls: List<&2, B.Ln>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, r}:
      List.append(&2, U32, B.ln.text(l), Con{10, jl(r)})

def revsl_snoc(+xs: List<&2, B.Ln>, +y: B.Ln) ->
    {List.append(&2, B.Ln, List.reverse(&2, B.Ln, xs), [y]) == List.reverse.go(&2, B.Ln, xs, [y]) : List<&2, B.Ln>}:
  Equal.sym(List<&2, B.Ln>, List.reverse.go(&2, B.Ln, xs, [y]), List.append(&2, B.Ln, List.reverse(&2, B.Ln, xs), [y]),
    ML.reverse_go_spec(&2, B.Ln, xs, [y]))

def jl_snoc(ls: List<&2, B.Ln>, +x: B.Ln) ->
    {List.append(&2, U32, jl(ls), List.append(&2, U32, B.ln.text(x), [10])) == jl(List.append(&2, B.Ln, ls, [x])) : List<&2, U32>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+p, +r}:
      %jl_snoc(r, x) : {List.append(&2, U32, List.append(&2, U32, B.ln.text(p), Con{10, jl(r)}), List.append(&2, U32, B.ln.text(x), [10])) ==
        List.append(&2, U32, B.ln.text(p), Con{10, _}) : List<&2, U32>}
      ML.append_assoc(&2, U32, B.ln.text(p), Con{10, jl(r)}, List.append(&2, U32, B.ln.text(x), [10]))

def text_lsnoc(ls: List<&2, B.Ln>, +x: B.Ln) ->
    {List.append(&2, U32, jl(ls), B.ln.text(x)) == B.lines.text(List.append(&2, B.Ln, ls, [x])) : List<&2, U32>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+p, r}:
      match r:
        case Nil{}:
          ML.append_assoc(&2, U32, B.ln.text(p), [10], B.ln.text(x))
        case Con{+q, +r2}:
          %text_lsnoc(Con{q, r2}, x) : {List.append(&2, U32, List.append(&2, U32, B.ln.text(p), Con{10, jl(Con{q, r2})}), B.ln.text(x)) ==
            List.append(&2, U32, B.ln.text(p), Con{10, _}) : List<&2, U32>}
          ML.append_assoc(&2, U32, B.ln.text(p), Con{10, jl(Con{q, r2})}, B.ln.text(x))

def uncr_k(+b: U32, +t: List<&2, U32>, +b2: Bool) -> List<&2, U32>:
  B.when(List<&2, U32>, b2, u => B.uncr(t), u => Con{b, B.uncr(t)})

def lines_k(+b: U32, +t: List<&2, U32>, +cur: List<&2, U32>, +no: U32, +out: List<&2, B.Ln>, +b1: Bool, +b2: Bool) -> List<&2, B.Ln>:
  B.when(List<&2, B.Ln>, b1, u => B.lines.go(t, Nil{}, (no + 1 : U32), Con{B.lines.line(cur, no), out}),
    u => B.when(List<&2, B.Ln>, b2, v => B.lines.go(t, cur, no, out), v => B.lines.go(t, Con{b, cur}, no, out)))

# the last line
def lines_end(+cur: List<&2, U32>, +no: U32, +out: List<&2, B.Ln>, +N: Nat, +hN: {N == Nat.pow(2n, 32n) : Nat}, +hl: MNat.lt(List.length(&2, U32, List.reverse(&2, U32, cur)), N)) ->
    {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) ==
      B.lines.text(B.lines.go(Nil{}, cur, no, out)) : List<&2, U32>}:
  %revsl_snoc(out, B.lines.line(cur, no)) :
    {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) == B.lines.text(_) : List<&2, U32>}
  %text_lsnoc(List.reverse(&2, B.Ln, out), B.lines.line(cur, no)) :
    {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) == _ : List<&2, U32>}
  %line_text(List.reverse(&2, U32, cur), 0n, no, N, hN, hl) :
    {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) == List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), _) : List<&2, U32>}
  %ML.append_nil(&2, U32, List.reverse(&2, U32, cur)) :
    {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) == List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), _) : List<&2, U32>}
  {==}

# a byte after the line so far: a newline, a carriage return, or another
def lines_step(+b: U32, +t: List<&2, U32>, +cur: List<&2, U32>, +no: U32, +out: List<&2, B.Ln>, +N: Nat, +hN: {N == Nat.pow(2n, 32n) : Nat},
    b1: Bool, +e1: {b1 == U32.is_eq(b, 10) : Bool}, b2: Bool, +e2: {b2 == U32.is_eq(b, 13) : Bool},
    +hl: MNat.lt(List.length(&2, U32, List.reverse(&2, U32, cur)), N),
    ih_nl: {List.append(&2, U32, jl(List.reverse(&2, B.Ln, Con{B.lines.line(cur, no), out})), List.append(&2, U32, List.reverse(&2, U32, Nil{}), B.uncr(t))) ==
      B.lines.text(B.lines.go(t, Nil{}, (no + 1 : U32), Con{B.lines.line(cur, no), out})) : List<&2, U32>},
    ih_cr: {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), B.uncr(t))) ==
      B.lines.text(B.lines.go(t, cur, no, out)) : List<&2, U32>},
    ih_ch: {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, Con{b, cur}), B.uncr(t))) ==
      B.lines.text(B.lines.go(t, Con{b, cur}, no, out)) : List<&2, U32>}) ->
    {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), uncr_k(b, t, b2))) ==
      B.lines.text(lines_k(b, t, cur, no, out, b1, b2)) : List<&2, U32>}:
  match b1:
    case True{}:
      match b2:
        case True{}:
          Empty.absurd({List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), uncr_k(b, t, True{}))) ==
              B.lines.text(lines_k(b, t, cur, no, out, True{}, True{})) : List<&2, U32>},
            MB.true_ne_false()(ME.subst(U32, x => {True{} == U32.is_eq(x, 13) : Bool}, b, 10,
              u32_eq_of_is_eq(b, 10, Equal.sym(Bool, True{}, U32.is_eq(b, 10), e1)), e2)))
        case False{}:
          %Equal.sym(U32, b, 10, u32_eq_of_is_eq(b, 10, Equal.sym(Bool, True{}, U32.is_eq(b, 10), e1))) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{_, B.uncr(t)})) ==
              B.lines.text(B.lines.go(t, Nil{}, (no + 1 : U32), Con{B.lines.line(cur, no), out})) : List<&2, U32>}
          %ih_nl : {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{10, B.uncr(t)})) == _ : List<&2, U32>}
          %revsl_snoc(out, B.lines.line(cur, no)) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{10, B.uncr(t)})) == List.append(&2, U32, jl(_), B.uncr(t)) : List<&2, U32>}
          %jl_snoc(List.reverse(&2, B.Ln, out), B.lines.line(cur, no)) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{10, B.uncr(t)})) == List.append(&2, U32, _, B.uncr(t)) : List<&2, U32>}
          %line_text(List.reverse(&2, U32, cur), 0n, no, N, hN, hl) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{10, B.uncr(t)})) ==
              List.append(&2, U32, List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, _, [10])), B.uncr(t)) : List<&2, U32>}
          %assoc_r(jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), [10]), B.uncr(t)) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{10, B.uncr(t)})) == _ : List<&2, U32>}
          %assoc_r(List.reverse(&2, U32, cur), [10], B.uncr(t)) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{10, B.uncr(t)})) == List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), _) : List<&2, U32>}
          {==}
    case False{}:
      match b2:
        case True{}:
          ih_cr
        case False{}:
          %ih_ch : {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{b, B.uncr(t)})) == _ : List<&2, U32>}
          %rev_snoc(cur, b) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{b, B.uncr(t)})) ==
              List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, _, B.uncr(t))) : List<&2, U32>}
          %assoc_r(List.reverse(&2, U32, cur), [b], B.uncr(t)) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{b, B.uncr(t)})) == List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), _) : List<&2, U32>}
          {==}

def lines_spec(bs: List<&2, U32>, +cur: List<&2, U32>, +no: U32, +out: List<&2, B.Ln>, +N: Nat, +hN: {N == Nat.pow(2n, 32n) : Nat}, +h: MNat.lt(Nat.add(List.length(&2, U32, cur), List.length(&2, U32, bs)), N)) ->
    {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), B.uncr(bs))) ==
      B.lines.text(B.lines.go(bs, cur, no, out)) : List<&2, U32>}:
  match bs:
    case Nil{}:
      lines_end(cur, no, out, N, hN, lim_rev(cur, N, lim_zero(List.length(&2, U32, cur), N, h)))
    case Con{+b, +t}:
      lines_step(b, t, cur, no, out, N, hN, U32.is_eq(b, 10), {==}, U32.is_eq(b, 13), {==},
        lim_rev(cur, N, lim_left(List.length(&2, U32, cur), 1n+List.length(&2, U32, t), N, h)),
        lines_spec(t, Nil{}, (no + 1 : U32), Con{B.lines.line(cur, no), out}, N, hN,
          lim_pred(List.length(&2, U32, t), N, lim_right(List.length(&2, U32, cur), 1n+List.length(&2, U32, t), N, h))),
        lines_spec(t, cur, no, out, N, hN, lim_pred(Nat.add(List.length(&2, U32, cur), List.length(&2, U32, t)), N, lim_succ(List.length(&2, U32, cur), List.length(&2, U32, t), N, h))),
        lines_spec(t, Con{b, cur}, no, out, N, hN, lim_succ(List.length(&2, U32, cur), List.length(&2, U32, t), N, h)))

# the law's bound in the form lines_spec takes, the bound abstract: Bend
# compares forms that differ by normalizing them, which unfolds 2^32
def top_bound(+bs: List<&2, U32>, +N: Nat, h: {Nat.is_lt(List.length(&2, U32, bs), N) == True{} : Bool}) ->
    MNat.lt(Nat.add(List.length(&2, U32, Nil{}), List.length(&2, U32, bs)), N):
  h

def Laws.lines.join(bs, h):
  Equal.sym(List<&2, U32>, B.uncr(bs), B.lines.text(B.lines(bs)),
    lines_spec(bs, Nil{}, (0 + 1 : U32), Nil{}, Nat.pow(2n, 32n), {==}, top_bound(bs, Nat.pow(2n, 32n), h)))

# The walk's order
# ----------------
#
# A unit joins the order only once its callees have (ds.done.k), so the
# order is callee-first after every step: each step keeps it or adds a
# unit whose callees are in it. Each step's choices are Bools its helpers
# match, which the lemmas split.

def call_keeps(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +h: {B.ordered(order, cal) == True{} : Bool}) ->
    {B.ordered(B.ds.order(B.ds.call.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us)), cal) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      match cyc:
        case True{}:
          h
        case False{}:
          h

def done_keeps(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +e: {ok == B.all.in(B.ids.at(cal, u), order) : Bool}, +h: {B.ordered(order, cal) == True{} : Bool}) ->
    {B.ordered(B.ds.order(B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us)), cal) == True{} : Bool}:
  match ok:
    case True{}:
      %e : {Bool.and(_, B.ordered(order, cal)) == True{} : Bool}
      h
    case False{}:
      h

def root_keeps(+seen: Bool, +r: U32, +rt: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>,
    +cal: List<&2, List<&2, U32>>, +h: {B.ordered(order, cal) == True{} : Bool}) ->
    {B.ordered(B.ds.order(B.ds.root.k(seen, r, rt, done, order, ers, cal)), cal) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      h

def step_keeps(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +h: {B.ordered(B.ds.order(s), cal) == True{} : Bool}) ->
    {B.ordered(B.ds.order(B.ds.step(s, cal, obs, us)), cal) == True{} : Bool}:
  match s:
    case B.Ds{stack, +roots, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              h
            case Con{+r, +rt}:
              root_keeps(B.has(done, r), r, rt, done, order, ers, cal, h)
        case Con{f, +st}:
          match f:
            case B.Fm{+u, rest}:
              match rest:
                case Nil{}:
                  done_keeps(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, cal, obs, us, {==}, h)
                case Con{+c, rs}:
                  call_keeps(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us, h)

def go_keeps(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +h: {B.ordered(B.ds.order(s), cal) == True{} : Bool}) ->
    {B.ordered(B.ds.order(B.ds.go(n, s, cal, obs, us)), cal) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+k:
      go_keeps(k, B.ds.step(s, cal, obs, us), cal, obs, us, step_keeps(s, cal, obs, us, h))

def Laws.order.callees_first(roots, cal, obs, us):
  go_keeps(Nat.add(Nat.add(List.length(&2, U32, roots), B.lens(cal)), Nat.add(List.length(&2, B.Un, us), List.length(&2, B.Un, us))),
    B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us, {==})

# The walk's order, each unit once
# --------------------------------
#
# The invariant: the order is distinct, every unit in it walked; the
# units on the stack distinct, none walked. A unit is pushed only when
# neither walked nor on the stack, and joins the order when popped, so
# once.

def and_intro(+a: Bool, +b: Bool, pa: {a == True{} : Bool}, pb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, pa) : {Bool.and(_, b) == True{} : Bool}
  pb

def or_false_l(+a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MB.true_ne_false()(h))
    case False{}:
      {==}

def or_false_r(+a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, MB.true_ne_false()(h))
    case False{}:
      h

def not_true(+b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MB.false_ne_true()(h))
    case False{}:
      {==}

def u32_is_eq_comm(+a: U32, +b: U32) -> {U32.is_eq(a, b) == U32.is_eq(b, a) : Bool}:
  Equal.trans(Bool, U32.is_eq(a, b), Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), U32.is_eq(b, a), MU.u32_is_eq_to_nat(a, b),
    Equal.trans(Bool, Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), Nat.is_eq(U32.to_nat(b), U32.to_nat(a)), U32.is_eq(b, a),
      MNat.is_eq_comm(U32.to_nat(a), U32.to_nat(b)), MU.u32_is_eq_to_nat_sym(b, a)))

def has_self(+done: List<&2, U32>, +u: U32) -> {B.has(Con{u, done}, u) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(u, u), True{}, u32_is_eq_refl(u)) : {Bool.or(_, B.has(done, u)) == True{} : Bool}
  {==}

def has_mono(+xs: List<&2, U32>, +u: U32, +x: U32, h: {B.has(xs, x) == True{} : Bool}) -> {B.has(Con{u, xs}, x) == True{} : Bool}:
  %Equal.sym(Bool, B.has(xs, x), True{}, h) : {Bool.or(U32.is_eq(u, x), _) == True{} : Bool}
  MB.or_true(U32.is_eq(u, x))

def all_in_mono(ys: List<&2, U32>, +done: List<&2, U32>, +u: U32, +h: {B.all.in(ys, done) == True{} : Bool}) -> {B.all.in(ys, Con{u, done}) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      and_intro(B.has(Con{u, done}, y), B.all.in(t, Con{u, done}),
        has_mono(done, u, y, MB.eq_true_of_and_left(B.has(done, y), B.all.in(t, done), h)),
        all_in_mono(t, done, u, MB.eq_true_of_and_right(B.has(done, y), B.all.in(t, done), h)))

def none_in(xs: List<&2, U32>, +done: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(Bool.not(B.has(done, x)), none_in(t, done))

# a unit not walked is not in the order, which holds only units walked
def sub_step(+y: U32, +t: List<&2, U32>, +done: List<&2, U32>, +u: U32, b: Bool, +e: {b == U32.is_eq(y, u) : Bool},
    hy: {B.has(done, y) == True{} : Bool}, +hn: {B.has(done, u) == False{} : Bool}, ih: {B.has(t, u) == False{} : Bool}) ->
    {Bool.or(b, B.has(t, u)) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.or(True{}, B.has(t, u)) == False{} : Bool},
        MB.true_ne_false()(Equal.trans(Bool, True{}, B.has(done, u), False{},
          Equal.sym(Bool, B.has(done, u), True{},
            ME.subst(U32, x => {B.has(done, x) == True{} : Bool}, y, u, u32_eq_of_is_eq(y, u, Equal.sym(Bool, True{}, U32.is_eq(y, u), e)), hy)),
          hn)))
    case False{}:
      ih

def not_in_of_sub(ys: List<&2, U32>, +done: List<&2, U32>, +u: U32, +hsub: {B.all.in(ys, done) == True{} : Bool}, +hn: {B.has(done, u) == False{} : Bool}) ->
    {B.has(ys, u) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      sub_step(y, t, done, u, U32.is_eq(y, u), {==}, MB.eq_true_of_and_left(B.has(done, y), B.all.in(t, done), hsub), hn,
        not_in_of_sub(t, done, u, MB.eq_true_of_and_right(B.has(done, y), B.all.in(t, done), hsub), hn))

# units none walked, u not among them: none walked once u is
def none_in_extend(xs: List<&2, U32>, +done: List<&2, U32>, +u: U32, +hn: {none_in(xs, done) == True{} : Bool}, +hu: {B.has(xs, u) == False{} : Bool}) ->
    {none_in(xs, Con{u, done}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.trans(Bool, False{}, U32.is_eq(x, u), U32.is_eq(u, x),
          Equal.sym(Bool, U32.is_eq(x, u), False{}, or_false_l(U32.is_eq(x, u), B.has(t, u), hu)), u32_is_eq_comm(x, u)) :
        {Bool.and(Bool.not(Bool.or(_, B.has(done, x))), none_in(t, Con{u, done})) == True{} : Bool}
      %Equal.sym(Bool, B.has(done, x), False{}, not_true(B.has(done, x), MB.eq_true_of_and_left(Bool.not(B.has(done, x)), none_in(t, done), hn))) :
        {Bool.and(Bool.not(Bool.or(False{}, _)), none_in(t, Con{u, done})) == True{} : Bool}
      none_in_extend(t, done, u, MB.eq_true_of_and_right(Bool.not(B.has(done, x)), none_in(t, done), hn), or_false_r(U32.is_eq(x, u), B.has(t, u), hu))

def inv4(+order: List<&2, U32>, +done: List<&2, U32>, +st: List<&2, B.Fm>) -> Bool:
  Bool.and(B.distinct(order), Bool.and(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)))))

def inv(s: B.Ds) -> Bool:
  match s:
    case B.Ds{stack, roots, done, order, ers}:
      inv4(order, done, stack)

def mk4(+order: List<&2, U32>, +done: List<&2, U32>, +st: List<&2, B.Fm>,
    pa: {B.distinct(order) == True{} : Bool}, pb: {B.all.in(order, done) == True{} : Bool},
    pc: {none_in(B.fms.units(st), done) == True{} : Bool}, pd: {B.distinct(B.fms.units(st)) == True{} : Bool}) -> {inv4(order, done, st) == True{} : Bool}:
  and_intro(B.distinct(order), Bool.and(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)))), pa,
    and_intro(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st))), pb,
      and_intro(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)), pc, pd)))

def get_a(+order: List<&2, U32>, +done: List<&2, U32>, +st: List<&2, B.Fm>, h: {inv4(order, done, st) == True{} : Bool}) -> {B.distinct(order) == True{} : Bool}:
  MB.eq_true_of_and_left(B.distinct(order), Bool.and(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)))), h)

def get_bcd(+order: List<&2, U32>, +done: List<&2, U32>, +st: List<&2, B.Fm>, h: {inv4(order, done, st) == True{} : Bool}) ->
    {Bool.and(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)))) == True{} : Bool}:
  MB.eq_true_of_and_right(B.distinct(order), Bool.and(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)))), h)

def get_b(+order: List<&2, U32>, +done: List<&2, U32>, +st: List<&2, B.Fm>, h: {inv4(order, done, st) == True{} : Bool}) -> {B.all.in(order, done) == True{} : Bool}:
  MB.eq_true_of_and_left(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st))), get_bcd(order, done, st, h))

def get_c(+order: List<&2, U32>, +done: List<&2, U32>, +st: List<&2, B.Fm>, h: {inv4(order, done, st) == True{} : Bool}) -> {none_in(B.fms.units(st), done) == True{} : Bool}:
  MB.eq_true_of_and_left(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)),
    MB.eq_true_of_and_right(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st))), get_bcd(order, done, st, h)))

def get_d(+order: List<&2, U32>, +done: List<&2, U32>, +st: List<&2, B.Fm>, h: {inv4(order, done, st) == True{} : Bool}) -> {B.distinct(B.fms.units(st)) == True{} : Bool}:
  MB.eq_true_of_and_right(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)),
    MB.eq_true_of_and_right(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st))), get_bcd(order, done, st, h)))

def root_once(+seen: Bool, +r: U32, +rt: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>,
    +e: {seen == B.has(done, r) : Bool}, +h: {inv4(order, done, Nil{}) == True{} : Bool}) ->
    {inv(B.ds.root.k(seen, r, rt, done, order, ers, cal)) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      mk4(order, done, [B.Fm{r, B.ids.at(cal, r)}], get_a(order, done, Nil{}, h), get_b(order, done, Nil{}, h),
        and_intro(Bool.not(B.has(done, r)), True{}, Equal.sym(Bool, True{}, Bool.not(B.has(done, r)),
          ME.subst(Bool, x => {True{} == Bool.not(x) : Bool}, False{}, B.has(done, r), e, {==})), {==}),
        {==})

def call_once(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +e1: {seen == B.has(done, c) : Bool}, +e2: {cyc == B.has(Con{u, B.fms.units(st)}, c) : Bool},
    +h: {inv4(order, done, Con{B.Fm{u, Con{c, rs}}, st}) == True{} : Bool}) ->
    {inv(B.ds.call.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us)) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      match cyc:
        case True{}:
          h
        case False{}:
          mk4(order, done, Con{B.Fm{c, B.ids.at(cal, c)}, Con{B.Fm{u, rs}, st}},
            get_a(order, done, Con{B.Fm{u, Con{c, rs}}, st}, h), get_b(order, done, Con{B.Fm{u, Con{c, rs}}, st}, h),
            and_intro(Bool.not(B.has(done, c)), none_in(Con{u, B.fms.units(st)}, done),
              ME.subst(Bool, x => {Bool.not(x) == True{} : Bool}, False{}, B.has(done, c), e1, {==}),
              get_c(order, done, Con{B.Fm{u, Con{c, rs}}, st}, h)),
            and_intro(Bool.not(B.has(Con{u, B.fms.units(st)}, c)), B.distinct(Con{u, B.fms.units(st)}),
              ME.subst(Bool, x => {Bool.not(x) == True{} : Bool}, False{}, B.has(Con{u, B.fms.units(st)}, c), e2, {==}),
              get_d(order, done, Con{B.Fm{u, Con{c, rs}}, st}, h)))

# a unit popped: walked now, and joined to the order or held back
def done_once.k(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +ha: {B.distinct(order) == True{} : Bool}, +hb: {B.all.in(order, done) == True{} : Bool}, +hu: {B.has(done, u) == False{} : Bool},
    +hst: {none_in(B.fms.units(st), done) == True{} : Bool}, +hnu: {B.has(B.fms.units(st), u) == False{} : Bool},
    +hds: {B.distinct(B.fms.units(st)) == True{} : Bool}) ->
    {inv(B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us)) == True{} : Bool}:
  match ok:
    case True{}:
      mk4(Con{u, order}, Con{u, done}, st,
        and_intro(Bool.not(B.has(order, u)), B.distinct(order),
          ME.subst(Bool, x => {Bool.not(x) == True{} : Bool}, False{}, B.has(order, u),
            Equal.sym(Bool, B.has(order, u), False{}, not_in_of_sub(order, done, u, hb, hu)), {==}), ha),
        and_intro(B.has(Con{u, done}, u), B.all.in(order, Con{u, done}), has_self(done, u), all_in_mono(order, done, u, hb)),
        none_in_extend(B.fms.units(st), done, u, hst, hnu),
        hds)
    case False{}:
      mk4(order, Con{u, done}, st, ha, all_in_mono(order, done, u, hb), none_in_extend(B.fms.units(st), done, u, hst, hnu), hds)

def done_once(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +h: {inv4(order, done, Con{B.Fm{u, Nil{}}, st}) == True{} : Bool}) ->
    {inv(B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us)) == True{} : Bool}:
  +hc = get_c(order, done, Con{B.Fm{u, Nil{}}, st}, h)
  +hd = get_d(order, done, Con{B.Fm{u, Nil{}}, st}, h)
  +hu = not_true(B.has(done, u), MB.eq_true_of_and_left(Bool.not(B.has(done, u)), none_in(B.fms.units(st), done), hc))
  +hst = MB.eq_true_of_and_right(Bool.not(B.has(done, u)), none_in(B.fms.units(st), done), hc)
  +hnu = not_true(B.has(B.fms.units(st), u), MB.eq_true_of_and_left(Bool.not(B.has(B.fms.units(st), u)), B.distinct(B.fms.units(st)), hd))
  +hds = MB.eq_true_of_and_right(Bool.not(B.has(B.fms.units(st), u)), B.distinct(B.fms.units(st)), hd)
  +hb = get_b(order, done, Con{B.Fm{u, Nil{}}, st}, h)
  done_once.k(ok, u, st, roots, done, order, ers, obs, us, get_a(order, done, Con{B.Fm{u, Nil{}}, st}, h), hb, hu, hst, hnu, hds)

def step_once(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {inv(s) == True{} : Bool}) ->
    {inv(B.ds.step(s, cal, obs, us)) == True{} : Bool}:
  match s:
    case B.Ds{stack, +roots, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              h
            case Con{+r, +rt}:
              root_once(B.has(done, r), r, rt, done, order, ers, cal, {==}, h)
        case Con{f, +st}:
          match f:
            case B.Fm{+u, rest}:
              match rest:
                case Nil{}:
                  done_once(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us, h)
                case Con{+c, +rs}:
                  call_once(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us, {==}, {==}, h)

def go_once(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {inv(s) == True{} : Bool}) ->
    {inv(B.ds.go(n, s, cal, obs, us)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+k:
      go_once(k, B.ds.step(s, cal, obs, us), cal, obs, us, step_once(s, cal, obs, us, h))

def inv_order(s: B.Ds, h: {inv(s) == True{} : Bool}) -> {B.distinct(B.ds.order(s)) == True{} : Bool}:
  match s:
    case B.Ds{stack, roots, +done, +order, ers}:
      get_a(order, done, stack, h)

def Laws.order.once(roots, cal, obs, us):
  inv_order(B.walk(roots, cal, obs, us),
    go_once(Nat.add(Nat.add(List.length(&2, U32, roots), B.lens(cal)), Nat.add(List.length(&2, B.Un, us), List.length(&2, B.Un, us))),
      B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us, {==}))

# The walk's order, nothing walked lost
# -------------------------------------
#
# The invariant: an error is reported, or every unit walked is in the
# order. A unit held back reports an error where none was, and errors
# are never taken back.

def jinv(s: B.Ds) -> Bool:
  match s:
    case B.Ds{stack, roots, done, order, ers}:
      Bool.or(Bool.not(List.is_empty(&2, B.Er, ers)), B.all.in(done, order))

def done_walked(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +h: {Bool.or(Bool.not(List.is_empty(&2, B.Er, ers)), B.all.in(done, order)) == True{} : Bool}) ->
    {jinv(B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us)) == True{} : Bool}:
  match ok:
    case True{}:
      match ers:
        case Nil{}:
          and_intro(B.has(Con{u, order}, u), B.all.in(done, Con{u, order}), has_self(order, u), all_in_mono(done, order, u, h))
        case Con{e, es}:
          {==}
    case False{}:
      match ers:
        case Nil{}:
          {==}
        case Con{e, es}:
          {==}

def root_walked(+seen: Bool, +r: U32, +rt: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>,
    +h: {Bool.or(Bool.not(List.is_empty(&2, B.Er, ers)), B.all.in(done, order)) == True{} : Bool}) ->
    {jinv(B.ds.root.k(seen, r, rt, done, order, ers, cal)) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      h

def call_walked(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +h: {Bool.or(Bool.not(List.is_empty(&2, B.Er, ers)), B.all.in(done, order)) == True{} : Bool}) ->
    {jinv(B.ds.call.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us)) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      match cyc:
        case True{}:
          {==}
        case False{}:
          h

def step_walked(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {jinv(s) == True{} : Bool}) ->
    {jinv(B.ds.step(s, cal, obs, us)) == True{} : Bool}:
  match s:
    case B.Ds{stack, +roots, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              h
            case Con{+r, +rt}:
              root_walked(B.has(done, r), r, rt, done, order, ers, cal, h)
        case Con{f, +st}:
          match f:
            case B.Fm{+u, rest}:
              match rest:
                case Nil{}:
                  done_walked(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us, h)
                case Con{+c, +rs}:
                  call_walked(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us, h)

def go_walked(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {jinv(s) == True{} : Bool}) ->
    {jinv(B.ds.go(n, s, cal, obs, us)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+k:
      go_walked(k, B.ds.step(s, cal, obs, us), cal, obs, us, step_walked(s, cal, obs, us, h))

# no error reported: every unit walked in the order
def jinv_out(s: B.Ds, h: {jinv(s) == True{} : Bool}, +e: {List.is_empty(&2, B.Er, B.ds.ers(s)) == True{} : Bool}) ->
    {B.all.in(B.ds.walked(s), B.ds.order(s)) == True{} : Bool}:
  match s:
    case B.Ds{stack, roots, +done, +order, +ers}:
      ME.subst(Bool, x => {Bool.or(Bool.not(x), B.all.in(done, order)) == True{} : Bool}, List.is_empty(&2, B.Er, ers), True{}, e, h)

def Laws.order.walked(roots, cal, obs, us, h):
  jinv_out(B.walk(roots, cal, obs, us),
    go_walked(Nat.add(Nat.add(List.length(&2, U32, roots), B.lens(cal)), Nat.add(List.length(&2, B.Un, us), List.length(&2, B.Un, us))),
      B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us, {==}), h)
