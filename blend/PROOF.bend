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
# - Termination by a potential (`pot`): each step lowers it (`step_desc`),
#   the fuel is its value at the start (`fuel_pot`), and induction on the
#   fuel ends the walk (`ends`). Each unit's calls count once, by its
#   position (`taken`, `psw_drop`), so that the fuel is linear.
# - A fast walk proved against the walk (`order.fast`): a state lifted
#   with the tries its lists make, a step from it the lifted step
#   (`step_lift`); the tries on U32's own bits (`has_put`, `put_comm`).
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
  go_keeps(B.walk.fuel(roots, cal),
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
    go_once(B.walk.fuel(roots, cal),
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
    go_walked(B.walk.fuel(roots, cal),
      B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us, {==}), h)

# The walk's roots, every one walked
# ----------------------------------
#
# The invariant: every root is among the units on the stack, those
# walked and the roots left (cov); each step keeps every unit of the one
# among the next's. Containment is a Bool (all.in), reusable where a
# proof function is not.

def or_cases(+a: Bool, +b: Bool, +c: Bool, h: {Bool.or(a, b) == True{} : Bool},
    fa: {a == True{} : Bool} -> {c == True{} : Bool}, fb: {b == True{} : Bool} -> {c == True{} : Bool}) -> {c == True{} : Bool}:
  match a:
    case True{}:
      fa({==})
    case False{}:
      fb(h)

def has_sub(xs: List<&2, U32>, +ys: List<&2, U32>, +x: U32, +hs: {B.all.in(xs, ys) == True{} : Bool}, hx: {B.has(xs, x) == True{} : Bool}) ->
    {B.has(ys, x) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({B.has(ys, x) == True{} : Bool}, MB.false_ne_true()(hx))
    case Con{+y, +t}:
      +hy = MB.eq_true_of_and_left(B.has(ys, y), B.all.in(t, ys), hs)
      +ht = MB.eq_true_of_and_right(B.has(ys, y), B.all.in(t, ys), hs)
      or_cases(U32.is_eq(y, x), B.has(t, x), B.has(ys, x), hx,
        e => ME.subst(U32, z => {B.has(ys, z) == True{} : Bool}, y, x, u32_eq_of_is_eq(y, x, e), hy),
        hh => has_sub(t, ys, x, ht, hh))

def sub_trans(r: List<&2, U32>, +xs: List<&2, U32>, +ys: List<&2, U32>, +h1: {B.all.in(r, xs) == True{} : Bool}, +h2: {B.all.in(xs, ys) == True{} : Bool}) ->
    {B.all.in(r, ys) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      and_intro(B.has(ys, a), B.all.in(t, ys), has_sub(xs, ys, a, h2, MB.eq_true_of_and_left(B.has(xs, a), B.all.in(t, xs), h1)),
        sub_trans(t, xs, ys, MB.eq_true_of_and_right(B.has(xs, a), B.all.in(t, xs), h1), h2))

def sub_refl(xs: List<&2, U32>) -> {B.all.in(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      and_intro(B.has(Con{a, t}, a), B.all.in(t, Con{a, t}), has_self(t, a), all_in_mono(t, t, a, sub_refl(t)))

def sub_cons(+xs: List<&2, U32>, +u: U32) -> {B.all.in(xs, Con{u, xs}) == True{} : Bool}:
  all_in_mono(xs, xs, u, sub_refl(xs))

def sub_l(p: List<&2, U32>, +q: List<&2, U32>) -> {B.all.in(p, List.append(&2, U32, p, q)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      and_intro(B.has(Con{a, List.append(&2, U32, t, q)}, a), B.all.in(t, Con{a, List.append(&2, U32, t, q)}),
        has_self(List.append(&2, U32, t, q), a), all_in_mono(t, List.append(&2, U32, t, q), a, sub_l(t, q)))

def sub_r(p: List<&2, U32>, +q: List<&2, U32>) -> {B.all.in(q, List.append(&2, U32, p, q)) == True{} : Bool}:
  match p:
    case Nil{}:
      sub_refl(q)
    case Con{+a, +t}:
      all_in_mono(q, List.append(&2, U32, t, q), a, sub_r(t, q))

def sub_app(p: List<&2, U32>, +q: List<&2, U32>, +ys: List<&2, U32>, +hp: {B.all.in(p, ys) == True{} : Bool}, +hq: {B.all.in(q, ys) == True{} : Bool}) ->
    {B.all.in(List.append(&2, U32, p, q), ys) == True{} : Bool}:
  match p:
    case Nil{}:
      hq
    case Con{+a, +t}:
      and_intro(B.has(ys, a), B.all.in(List.append(&2, U32, t, q), ys), MB.eq_true_of_and_left(B.has(ys, a), B.all.in(t, ys), hp),
        sub_app(t, q, ys, MB.eq_true_of_and_right(B.has(ys, a), B.all.in(t, ys), hp), hq))

# a unit in p is in p ++ q
def in_l(+p: List<&2, U32>, +q: List<&2, U32>, +x: U32, +h: {B.has(p, x) == True{} : Bool}) -> {B.has(List.append(&2, U32, p, q), x) == True{} : Bool}:
  has_sub(p, List.append(&2, U32, p, q), x, sub_l(p, q), h)

def cov(s: B.Ds) -> List<&2, U32>:
  match s:
    case B.Ds{stack, roots, done, order, ers}:
      List.append(&2, U32, B.fms.units(stack), List.append(&2, U32, done, roots))

def root_roots(+seen: Bool, +r: U32, +rt: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>,
    +e: {seen == B.has(done, r) : Bool}, +rs0: List<&2, U32>, +h: {B.all.in(rs0, List.append(&2, U32, done, Con{r, rt})) == True{} : Bool}) ->
    {B.all.in(rs0, cov(B.ds.root.k(seen, r, rt, done, order, ers, cal))) == True{} : Bool}:
  match seen:
    case True{}:
      sub_trans(rs0, List.append(&2, U32, done, Con{r, rt}), List.append(&2, U32, done, rt), h,
        sub_app(done, Con{r, rt}, List.append(&2, U32, done, rt), sub_l(done, rt),
          and_intro(B.has(List.append(&2, U32, done, rt), r), B.all.in(rt, List.append(&2, U32, done, rt)),
            in_l(done, rt, r, Equal.sym(Bool, True{}, B.has(done, r), e)), sub_r(done, rt))))
    case False{}:
      sub_trans(rs0, List.append(&2, U32, done, Con{r, rt}), Con{r, List.append(&2, U32, done, rt)}, h,
        sub_app(done, Con{r, rt}, Con{r, List.append(&2, U32, done, rt)},
          all_in_mono(done, List.append(&2, U32, done, rt), r, sub_l(done, rt)),
          and_intro(B.has(Con{r, List.append(&2, U32, done, rt)}, r), B.all.in(rt, Con{r, List.append(&2, U32, done, rt)}),
            has_self(List.append(&2, U32, done, rt), r), all_in_mono(rt, List.append(&2, U32, done, rt), r, sub_r(done, rt)))))

def call_roots(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +rs0: List<&2, U32>, +h: {B.all.in(rs0, Con{u, List.append(&2, U32, B.fms.units(st), List.append(&2, U32, done, roots))}) == True{} : Bool}) ->
    {B.all.in(rs0, cov(B.ds.call.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us))) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      match cyc:
        case True{}:
          h
        case False{}:
          sub_trans(rs0, Con{u, List.append(&2, U32, B.fms.units(st), List.append(&2, U32, done, roots))},
            Con{c, Con{u, List.append(&2, U32, B.fms.units(st), List.append(&2, U32, done, roots))}}, h,
            sub_cons(Con{u, List.append(&2, U32, B.fms.units(st), List.append(&2, U32, done, roots))}, c))

# a unit popped: from the stack to those walked
def pop_sub(+u: U32, +a: List<&2, U32>, +d: List<&2, U32>) ->
    {B.all.in(Con{u, List.append(&2, U32, a, d)}, List.append(&2, U32, a, Con{u, d})) == True{} : Bool}:
  and_intro(B.has(List.append(&2, U32, a, Con{u, d}), u), B.all.in(List.append(&2, U32, a, d), List.append(&2, U32, a, Con{u, d})),
    has_sub(Con{u, d}, List.append(&2, U32, a, Con{u, d}), u, sub_r(a, Con{u, d}), has_self(d, u)),
    sub_app(a, d, List.append(&2, U32, a, Con{u, d}), sub_l(a, Con{u, d}),
      sub_trans(d, Con{u, d}, List.append(&2, U32, a, Con{u, d}), sub_cons(d, u), sub_r(a, Con{u, d}))))

def done_roots(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +rs0: List<&2, U32>, +h: {B.all.in(rs0, Con{u, List.append(&2, U32, B.fms.units(st), List.append(&2, U32, done, roots))}) == True{} : Bool}) ->
    {B.all.in(rs0, cov(B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us))) == True{} : Bool}:
  match ok:
    case True{}:
      sub_trans(rs0, Con{u, List.append(&2, U32, B.fms.units(st), List.append(&2, U32, done, roots))},
        List.append(&2, U32, B.fms.units(st), Con{u, List.append(&2, U32, done, roots)}), h,
        pop_sub(u, B.fms.units(st), List.append(&2, U32, done, roots)))
    case False{}:
      sub_trans(rs0, Con{u, List.append(&2, U32, B.fms.units(st), List.append(&2, U32, done, roots))},
        List.append(&2, U32, B.fms.units(st), Con{u, List.append(&2, U32, done, roots)}), h,
        pop_sub(u, B.fms.units(st), List.append(&2, U32, done, roots)))

def step_roots(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +rs0: List<&2, U32>,
    +h: {B.all.in(rs0, cov(s)) == True{} : Bool}) -> {B.all.in(rs0, cov(B.ds.step(s, cal, obs, us))) == True{} : Bool}:
  match s:
    case B.Ds{stack, +roots, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              h
            case Con{+r, +rt}:
              root_roots(B.has(done, r), r, rt, done, order, ers, cal, {==}, rs0, h)
        case Con{f, +st}:
          match f:
            case B.Fm{+u, rest}:
              match rest:
                case Nil{}:
                  done_roots(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us, rs0, h)
                case Con{+c, +rs}:
                  call_roots(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us, rs0, h)

def go_roots(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +rs0: List<&2, U32>,
    +h: {B.all.in(rs0, cov(s)) == True{} : Bool}) -> {B.all.in(rs0, cov(B.ds.go(n, s, cal, obs, us))) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+k:
      go_roots(k, B.ds.step(s, cal, obs, us), cal, obs, us, rs0, step_roots(s, cal, obs, us, rs0, h))

# finished: no stack, no roots, so every root walked
def roots_out(s: B.Ds, +rs0: List<&2, U32>, +h: {B.all.in(rs0, cov(s)) == True{} : Bool}, e: {B.ds.finished(s) == True{} : Bool}) ->
    {B.all.in(rs0, B.ds.walked(s)) == True{} : Bool}:
  match s:
    case B.Ds{stack, roots, +done, order, ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              sub_trans(rs0, List.append(&2, U32, done, Nil{}), done, h, sub_app(done, Nil{}, done, sub_refl(done), {==}))
            case Con{r, rt}:
              Empty.absurd({B.all.in(rs0, done) == True{} : Bool}, MB.false_ne_true()(e))
        case Con{f, st}:
          Empty.absurd({B.all.in(rs0, done) == True{} : Bool}, MB.false_ne_true()(e))

def Laws.order.roots(roots, cal, obs, us, h):
  roots_out(B.walk(roots, cal, obs, us), roots,
    go_roots(B.walk.fuel(roots, cal),
      B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us, roots, sub_refl(roots)), h)

# The walk's calls, every one walked
# ----------------------------------
#
# The invariant, c the stack's units then those walked: every walked
# unit's callees among c; each frame's callees among c or still to follow
# (its rest). A call followed joins c (walked, on the stack, or pushed);
# a unit popped has followed all, so its callees are among c.

def frames_ok(st: List<&2, B.Fm>, +cal: List<&2, List<&2, U32>>, +c: List<&2, U32>) -> Bool:
  match st:
    case Nil{}:
      True{}
    case Con{f, t}:
      match f:
        case B.Fm{+u, rest}:
          Bool.and(B.all.in(B.ids.at(cal, u), List.append(&2, U32, c, rest)), frames_ok(t, cal, c))

def kinv4(+cal: List<&2, List<&2, U32>>, +done: List<&2, U32>, +stack: List<&2, B.Fm>) -> Bool:
  Bool.and(B.calls.in(done, cal, List.append(&2, U32, B.fms.units(stack), done)), frames_ok(stack, cal, List.append(&2, U32, B.fms.units(stack), done)))

def kinv(+cal: List<&2, List<&2, U32>>, s: B.Ds) -> Bool:
  match s:
    case B.Ds{stack, roots, done, order, ers}:
      kinv4(cal, done, stack)

def calls_mono(d: List<&2, U32>, +cal: List<&2, List<&2, U32>>, +x: List<&2, U32>, +y: List<&2, U32>,
    +h: {B.calls.in(d, cal, x) == True{} : Bool}, +s: {B.all.in(x, y) == True{} : Bool}) -> {B.calls.in(d, cal, y) == True{} : Bool}:
  match d:
    case Nil{}:
      {==}
    case Con{+v, +t}:
      and_intro(B.all.in(B.ids.at(cal, v), y), B.calls.in(t, cal, y),
        sub_trans(B.ids.at(cal, v), x, y, MB.eq_true_of_and_left(B.all.in(B.ids.at(cal, v), x), B.calls.in(t, cal, x), h), s),
        calls_mono(t, cal, x, y, MB.eq_true_of_and_right(B.all.in(B.ids.at(cal, v), x), B.calls.in(t, cal, x), h), s))

def app_mono(+x: List<&2, U32>, +y: List<&2, U32>, +r: List<&2, U32>, +s: {B.all.in(x, y) == True{} : Bool}) ->
    {B.all.in(List.append(&2, U32, x, r), List.append(&2, U32, y, r)) == True{} : Bool}:
  sub_app(x, r, List.append(&2, U32, y, r), sub_trans(x, y, List.append(&2, U32, y, r), s, sub_l(y, r)), sub_r(y, r))

def frames_mono(st: List<&2, B.Fm>, +cal: List<&2, List<&2, U32>>, +x: List<&2, U32>, +y: List<&2, U32>,
    +h: {frames_ok(st, cal, x) == True{} : Bool}, +s: {B.all.in(x, y) == True{} : Bool}) -> {frames_ok(st, cal, y) == True{} : Bool}:
  match st:
    case Nil{}:
      {==}
    case Con{f, +t}:
      match f:
        case B.Fm{+u, +rest}:
          and_intro(B.all.in(B.ids.at(cal, u), List.append(&2, U32, y, rest)), frames_ok(t, cal, y),
            sub_trans(B.ids.at(cal, u), List.append(&2, U32, x, rest), List.append(&2, U32, y, rest),
              MB.eq_true_of_and_left(B.all.in(B.ids.at(cal, u), List.append(&2, U32, x, rest)), frames_ok(t, cal, x), h), app_mono(x, y, rest, s)),
            frames_mono(t, cal, x, y, MB.eq_true_of_and_right(B.all.in(B.ids.at(cal, u), List.append(&2, U32, x, rest)), frames_ok(t, cal, x), h), s))

# a call followed, its unit among c already
def follow_sub(+c: List<&2, U32>, +x: U32, +rs: List<&2, U32>, +hc: {B.has(c, x) == True{} : Bool}) ->
    {B.all.in(List.append(&2, U32, c, Con{x, rs}), List.append(&2, U32, c, rs)) == True{} : Bool}:
  sub_app(c, Con{x, rs}, List.append(&2, U32, c, rs), sub_l(c, rs),
    and_intro(B.has(List.append(&2, U32, c, rs), x), B.all.in(rs, List.append(&2, U32, c, rs)), in_l(c, rs, x, hc), sub_r(c, rs)))

# a call followed, its unit pushed
def push_sub(+c: List<&2, U32>, +x: U32, +rs: List<&2, U32>) ->
    {B.all.in(List.append(&2, U32, c, Con{x, rs}), Con{x, List.append(&2, U32, c, rs)}) == True{} : Bool}:
  sub_app(c, Con{x, rs}, Con{x, List.append(&2, U32, c, rs)}, all_in_mono(c, List.append(&2, U32, c, rs), x, sub_l(c, rs)),
    and_intro(B.has(Con{x, List.append(&2, U32, c, rs)}, x), B.all.in(rs, Con{x, List.append(&2, U32, c, rs)}),
      has_self(List.append(&2, U32, c, rs), x), all_in_mono(rs, List.append(&2, U32, c, rs), x, sub_r(c, rs))))

def root_closed(+seen: Bool, +r: U32, +rt: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>,
    +h: {kinv4(cal, done, Nil{}) == True{} : Bool}) ->
    {kinv(cal, B.ds.root.k(seen, r, rt, done, order, ers, cal)) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      and_intro(B.calls.in(done, cal, Con{r, done}), frames_ok([B.Fm{r, B.ids.at(cal, r)}], cal, Con{r, done}),
        calls_mono(done, cal, done, Con{r, done}, MB.eq_true_of_and_left(B.calls.in(done, cal, done), frames_ok(Nil{}, cal, done), h), sub_cons(done, r)),
        and_intro(B.all.in(B.ids.at(cal, r), List.append(&2, U32, Con{r, done}, B.ids.at(cal, r))), True{}, sub_r(Con{r, done}, B.ids.at(cal, r)), {==}))

def call_closed.k(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +e1: {seen == B.has(done, c) : Bool}, +e2: {cyc == B.has(Con{u, B.fms.units(st)}, c) : Bool},
    +hcalls: {B.calls.in(done, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}) == True{} : Bool},
    +hu: {B.all.in(B.ids.at(cal, u), List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, Con{c, rs})) == True{} : Bool},
    +hst: {frames_ok(st, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}) == True{} : Bool}) ->
    {kinv(cal, B.ds.call.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us)) == True{} : Bool}:
  match seen:
    case True{}:
      and_intro(B.calls.in(done, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}),
        frames_ok(Con{B.Fm{u, rs}, st}, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}), hcalls,
        and_intro(B.all.in(B.ids.at(cal, u), List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, rs)),
          frames_ok(st, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}),
          sub_trans(B.ids.at(cal, u), List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, Con{c, rs}),
            List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, rs), hu,
            follow_sub(Con{u, List.append(&2, U32, B.fms.units(st), done)}, c, rs,
              has_sub(done, Con{u, List.append(&2, U32, B.fms.units(st), done)}, c,
                all_in_mono(done, List.append(&2, U32, B.fms.units(st), done), u, sub_r(B.fms.units(st), done)),
                Equal.sym(Bool, True{}, B.has(done, c), e1)))),
          hst))
    case False{}:
      match cyc:
        case True{}:
          and_intro(B.calls.in(done, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}),
            frames_ok(Con{B.Fm{u, rs}, st}, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}), hcalls,
            and_intro(B.all.in(B.ids.at(cal, u), List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, rs)),
              frames_ok(st, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}),
              sub_trans(B.ids.at(cal, u), List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, Con{c, rs}),
                List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, rs), hu,
                follow_sub(Con{u, List.append(&2, U32, B.fms.units(st), done)}, c, rs,
                  in_l(Con{u, B.fms.units(st)}, done, c, Equal.sym(Bool, True{}, B.has(Con{u, B.fms.units(st)}, c), e2)))),
              hst))
        case False{}:
          and_intro(B.calls.in(done, cal, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}),
            frames_ok(Con{B.Fm{c, B.ids.at(cal, c)}, Con{B.Fm{u, rs}, st}}, cal, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}),
            calls_mono(done, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}, hcalls,
              sub_cons(Con{u, List.append(&2, U32, B.fms.units(st), done)}, c)),
            and_intro(B.all.in(B.ids.at(cal, c), List.append(&2, U32, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}, B.ids.at(cal, c))),
              frames_ok(Con{B.Fm{u, rs}, st}, cal, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}),
              sub_r(Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}, B.ids.at(cal, c)),
              and_intro(B.all.in(B.ids.at(cal, u), List.append(&2, U32, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}, rs)),
                frames_ok(st, cal, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}),
                sub_trans(B.ids.at(cal, u), List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, Con{c, rs}),
                  Con{c, List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, rs)}, hu,
                  push_sub(Con{u, List.append(&2, U32, B.fms.units(st), done)}, c, rs)),
                frames_mono(st, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}, hst,
                  sub_cons(Con{u, List.append(&2, U32, B.fms.units(st), done)}, c)))))

def call_closed(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +e1: {seen == B.has(done, c) : Bool}, +e2: {cyc == B.has(Con{u, B.fms.units(st)}, c) : Bool},
    +h: {kinv4(cal, done, Con{B.Fm{u, Con{c, rs}}, st}) == True{} : Bool}) ->
    {kinv(cal, B.ds.call.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us)) == True{} : Bool}:
  +cc = {Con{u, List.append(&2, U32, B.fms.units(st), done)} : List<&2, U32>}
  +hcalls = MB.eq_true_of_and_left(B.calls.in(done, cal, cc), frames_ok(Con{B.Fm{u, Con{c, rs}}, st}, cal, cc), h)
  +hfr = MB.eq_true_of_and_right(B.calls.in(done, cal, cc), frames_ok(Con{B.Fm{u, Con{c, rs}}, st}, cal, cc), h)
  +hu = MB.eq_true_of_and_left(B.all.in(B.ids.at(cal, u), List.append(&2, U32, cc, Con{c, rs})), frames_ok(st, cal, cc), hfr)
  +hst = MB.eq_true_of_and_right(B.all.in(B.ids.at(cal, u), List.append(&2, U32, cc, Con{c, rs})), frames_ok(st, cal, cc), hfr)
  call_closed.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us, e1, e2, hcalls, hu, hst)

def done_closed.k(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +cal: List<&2, List<&2, U32>>,
    +hu: {B.all.in(B.ids.at(cal, u), List.append(&2, U32, B.fms.units(st), Con{u, done})) == True{} : Bool},
    +hd: {B.calls.in(done, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})) == True{} : Bool},
    +hf: {frames_ok(st, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})) == True{} : Bool}) ->
    {kinv(cal, B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us)) == True{} : Bool}:
  match ok:
    case True{}:
      and_intro(B.calls.in(Con{u, done}, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})), frames_ok(st, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})),
        and_intro(B.all.in(B.ids.at(cal, u), List.append(&2, U32, B.fms.units(st), Con{u, done})), B.calls.in(done, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})), hu, hd),
        hf)
    case False{}:
      and_intro(B.calls.in(Con{u, done}, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})), frames_ok(st, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})),
        and_intro(B.all.in(B.ids.at(cal, u), List.append(&2, U32, B.fms.units(st), Con{u, done})), B.calls.in(done, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})), hu, hd),
        hf)

# a unit popped: its callees among c, all followed; c the same units
def done_closed(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +cal: List<&2, List<&2, U32>>,
    +h: {kinv4(cal, done, Con{B.Fm{u, Nil{}}, st}) == True{} : Bool}) ->
    {kinv(cal, B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us)) == True{} : Bool}:
  +cc = {Con{u, List.append(&2, U32, B.fms.units(st), done)} : List<&2, U32>}
  +cn = List.append(&2, U32, B.fms.units(st), Con{u, done})
  +sb = pop_sub(u, B.fms.units(st), done)
  +hcalls = MB.eq_true_of_and_left(B.calls.in(done, cal, cc), frames_ok(Con{B.Fm{u, Nil{}}, st}, cal, cc), h)
  +hfr = MB.eq_true_of_and_right(B.calls.in(done, cal, cc), frames_ok(Con{B.Fm{u, Nil{}}, st}, cal, cc), h)
  +hu = MB.eq_true_of_and_left(B.all.in(B.ids.at(cal, u), List.append(&2, U32, cc, Nil{})), frames_ok(st, cal, cc), hfr)
  +hst = MB.eq_true_of_and_right(B.all.in(B.ids.at(cal, u), List.append(&2, U32, cc, Nil{})), frames_ok(st, cal, cc), hfr)
  done_closed.k(ok, u, st, roots, done, order, ers, obs, us, cal,
    sub_trans(B.ids.at(cal, u), List.append(&2, U32, cc, Nil{}), cn, hu, sub_app(cc, Nil{}, cn, sb, {==})),
    calls_mono(done, cal, cc, cn, hcalls, sb),
    frames_mono(st, cal, cc, cn, hst, sb))

def step_closed(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {kinv(cal, s) == True{} : Bool}) ->
    {kinv(cal, B.ds.step(s, cal, obs, us)) == True{} : Bool}:
  match s:
    case B.Ds{stack, +roots, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              h
            case Con{+r, +rt}:
              root_closed(B.has(done, r), r, rt, done, order, ers, cal, h)
        case Con{f, +st}:
          match f:
            case B.Fm{+u, rest}:
              match rest:
                case Nil{}:
                  done_closed(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us, cal, h)
                case Con{+c, +rs}:
                  call_closed(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us, {==}, {==}, h)

def go_closed(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {kinv(cal, s) == True{} : Bool}) ->
    {kinv(cal, B.ds.go(n, s, cal, obs, us)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+k:
      go_closed(k, B.ds.step(s, cal, obs, us), cal, obs, us, step_closed(s, cal, obs, us, h))

# finished: no stack, so every walked unit's callees walked
def closed_out(s: B.Ds, +cal: List<&2, List<&2, U32>>, +h: {kinv(cal, s) == True{} : Bool}, e: {B.ds.finished(s) == True{} : Bool}) ->
    {B.calls.in(B.ds.walked(s), cal, B.ds.walked(s)) == True{} : Bool}:
  match s:
    case B.Ds{stack, roots, +done, order, ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              MB.eq_true_of_and_left(B.calls.in(done, cal, done), frames_ok(Nil{}, cal, done), h)
            case Con{r, rt}:
              Empty.absurd({B.calls.in(done, cal, done) == True{} : Bool}, MB.false_ne_true()(e))
        case Con{f, st}:
          Empty.absurd({B.calls.in(done, cal, done) == True{} : Bool}, MB.false_ne_true()(e))

def Laws.order.closed(roots, cal, obs, us, h):
  closed_out(B.walk(roots, cal, obs, us), cal,
    go_closed(B.walk.fuel(roots, cal),
      B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us, {==}), h)

# The walk ends within its fuel
# -----------------------------
#
# A potential: two turns for each root left; a turn for each frame and
# two for each of its calls left; and two for each call of each unit,
# counted at the unit's position among the calls, while no unit walked
# or on the stack has that position. Each step lowers it by one at least,
# a push freeing its unit's turns, which the frame it pushes takes back
# less one; the fuel is the potential at the start. Counted by position,
# each unit's calls count once, so that the fuel is linear in the calls.

def cost(+b: Bool, +n: Nat) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      n

def cost_le(+b: Bool, +n: Nat) -> MNat.le(cost(b, n), n):
  match b:
    case True{}:
      MNat.zero_le(n)
    case False{}:
      MNat.le_refl(n)

def cost_mono(+a: Bool, +b: Bool, +n: Nat) -> MNat.le(cost(Bool.or(a, b), n), cost(b, n)):
  match a:
    case True{}:
      MNat.zero_le(cost(b, n))
    case False{}:
      MNat.le_refl(cost(b, n))

# whether a unit of x has the position i
def taken(x: List<&2, U32>, +i: Nat) -> Bool:
  match x:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Nat.is_eq(U32.to_nat(h), i), taken(t, i))

def has_taken(x: List<&2, U32>, +c: U32) -> {B.has(x, c) == taken(x, U32.to_nat(c)) : Bool}:
  match x:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %MU.u32_is_eq_to_nat(h, c) : {Bool.or(U32.is_eq(h, c), B.has(t, c)) == Bool.or(_, taken(t, U32.to_nat(c))) : Bool}
      %has_taken(t, c) : {Bool.or(U32.is_eq(h, c), B.has(t, c)) == Bool.or(U32.is_eq(h, c), _) : Bool}
      {==}

def taken_sub.k(+b: Bool, +a: U32, +t: List<&2, U32>, +y: List<&2, U32>, +j: Nat, +e: {b == Nat.is_eq(U32.to_nat(a), j) : Bool},
    +hs: {B.all.in(Con{a, t}, y) == True{} : Bool}, +h: {Bool.or(b, taken(t, j)) == True{} : Bool},
    ih: {taken(t, j) == True{} : Bool} -> {taken(y, j) == True{} : Bool}) -> {taken(y, j) == True{} : Bool}:
  match b:
    case True{}:
      %MNat.eq_of_is_eq(U32.to_nat(a), j, Equal.sym(Bool, True{}, Nat.is_eq(U32.to_nat(a), j), e)) : {taken(y, _) == True{} : Bool}
      %has_taken(y, a) : {_ == True{} : Bool}
      MB.eq_true_of_and_left(B.has(y, a), B.all.in(t, y), hs)
    case False{}:
      ih(h)

# a position x takes, any list x is among takes
def taken_sub(x: List<&2, U32>, +y: List<&2, U32>, +j: Nat, +hs: {B.all.in(x, y) == True{} : Bool}, +h: {taken(x, j) == True{} : Bool}) ->
    {taken(y, j) == True{} : Bool}:
  match x:
    case Nil{}:
      Empty.absurd({taken(y, j) == True{} : Bool}, MB.false_ne_true()(h))
    case Con{+a, +t}:
      taken_sub.k(Nat.is_eq(U32.to_nat(a), j), a, t, y, j, {==}, hs, h,
        g => taken_sub(t, y, j, MB.eq_true_of_and_right(B.has(y, a), B.all.in(t, y), hs), g))

# the turns of the calls at positions j on not taken by x
def psw(cal: List<&2, List<&2, U32>>, +x: List<&2, U32>, +j: Nat) -> Nat:
  match cal:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(cost(taken(x, j), B.walk.turns(h)), psw(t, x, 1n+j))

def psw_nil(cal: List<&2, List<&2, U32>>, +j: Nat) -> {psw(cal, Nil{}, j) == B.walk.calls(cal) : Nat}:
  match cal:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %psw_nil(t, 1n+j) : {Nat.add(B.walk.turns(h), psw(t, Nil{}, 1n+j)) == Nat.add(B.walk.turns(h), _) : Nat}
      {==}

# more taken, no more turns
def psw_mono(cal: List<&2, List<&2, U32>>, +x: List<&2, U32>, +c: U32, +j: Nat) -> MNat.le(psw(cal, Con{c, x}, j), psw(cal, x, j)):
  match cal:
    case Nil{}:
      MNat.le_refl(0n)
    case Con{+h, +t}:
      MNat.add_le_add(cost(Bool.or(Nat.is_eq(U32.to_nat(c), j), taken(x, j)), B.walk.turns(h)), psw(t, Con{c, x}, 1n+j), cost(taken(x, j), B.walk.turns(h)), psw(t, x, 1n+j),
        cost_mono(Nat.is_eq(U32.to_nat(c), j), taken(x, j), B.walk.turns(h)), psw_mono(t, x, c, 1n+j))

def cost_sub(+x: List<&2, U32>, +y: List<&2, U32>, +j: Nat, +h: {B.all.in(x, y) == True{} : Bool}, +n: Nat, b: Bool, +e: {b == taken(x, j) : Bool}) ->
    MNat.le(cost(taken(y, j), n), cost(b, n)):
  match b:
    case True{}:
      %Equal.sym(Bool, taken(y, j), True{}, taken_sub(x, y, j, h, Equal.sym(Bool, True{}, taken(x, j), e))) : MNat.le(cost(_, n), 0n)
      MNat.le_refl(0n)
    case False{}:
      cost_le(taken(y, j), n)

def psw_sub(cal: List<&2, List<&2, U32>>, +x: List<&2, U32>, +y: List<&2, U32>, +j: Nat, +h: {B.all.in(x, y) == True{} : Bool}) ->
    MNat.le(psw(cal, y, j), psw(cal, x, j)):
  match cal:
    case Nil{}:
      MNat.le_refl(0n)
    case Con{+w, +t}:
      MNat.add_le_add(cost(taken(y, j), B.walk.turns(w)), psw(t, y, 1n+j), cost(taken(x, j), B.walk.turns(w)), psw(t, x, 1n+j),
        cost_sub(x, y, j, h, B.walk.turns(w), taken(x, j), {==}), psw_sub(t, x, y, 1n+j, h))

def succ_add_ne(+k: Nat, j: Nat) -> {Nat.is_eq(1n+Nat.add(k, j), j) == False{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+(+i):
      %MNat.add_succ_sym(k, i) : {Nat.is_eq(_, i) == False{} : Bool}
      succ_add_ne(k, i)

def at_self(+c: U32, +j: Nat, +e: {U32.to_nat(c) == j : Nat}) -> {Nat.is_eq(U32.to_nat(c), j) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(c), j, e) : {Nat.is_eq(_, j) == True{} : Bool}
  MNat.is_eq_refl(j)

def at_other(+c: U32, +k: Nat, +j: Nat, +e: {U32.to_nat(c) == 1n+Nat.add(k, j) : Nat}) -> {Nat.is_eq(U32.to_nat(c), j) == False{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(c), 1n+Nat.add(k, j), e) : {Nat.is_eq(_, j) == False{} : Bool}
  succ_add_ne(k, j)

# a unit c at position d + j, which x does not take: taking it frees the
# turns of its calls
def psw_drop(cal: List<&2, List<&2, U32>>, +x: List<&2, U32>, +c: U32, d: Nat, +j: Nat,
    +e: {U32.to_nat(c) == Nat.add(d, j) : Nat}, +hn: {taken(x, Nat.add(d, j)) == False{} : Bool}) ->
    MNat.le(Nat.add(B.walk.turns(B.ids.or(List.get(&2, List<&2, U32>, cal, d))), psw(cal, Con{c, x}, j)), psw(cal, x, j)):
  match cal:
    case Nil{}:
      MNat.le_refl(0n)
    case Con{+h, +t}:
      match d:
        case 0n:
          %Equal.sym(Bool, Nat.is_eq(U32.to_nat(c), j), True{}, at_self(c, j, e)) :
            MNat.le(Nat.add(B.walk.turns(h), Nat.add(cost(Bool.or(_, taken(x, j)), B.walk.turns(h)), psw(t, Con{c, x}, 1n+j))), Nat.add(cost(taken(x, j), B.walk.turns(h)), psw(t, x, 1n+j)))
          %Equal.sym(Bool, taken(x, j), False{}, hn) :
            MNat.le(Nat.add(B.walk.turns(h), psw(t, Con{c, x}, 1n+j)), Nat.add(cost(_, B.walk.turns(h)), psw(t, x, 1n+j)))
          MNat.add_le_add_left(psw(t, Con{c, x}, 1n+j), psw(t, x, 1n+j), B.walk.turns(h), psw_mono(t, x, c, 1n+j))
        case 1n+(+k):
          %Equal.sym(Bool, Nat.is_eq(U32.to_nat(c), j), False{}, at_other(c, k, j, e)) :
            MNat.le(Nat.add(B.walk.turns(B.ids.or(List.get(&2, List<&2, U32>, t, k))), Nat.add(cost(Bool.or(_, taken(x, j)), B.walk.turns(h)), psw(t, Con{c, x}, 1n+j))), Nat.add(cost(taken(x, j), B.walk.turns(h)), psw(t, x, 1n+j)))
          %MNat.add_left_comm(cost(taken(x, j), B.walk.turns(h)), B.walk.turns(B.ids.or(List.get(&2, List<&2, U32>, t, k))), psw(t, Con{c, x}, 1n+j)) :
            MNat.le(_, Nat.add(cost(taken(x, j), B.walk.turns(h)), psw(t, x, 1n+j)))
          MNat.add_le_add_left(Nat.add(B.walk.turns(B.ids.or(List.get(&2, List<&2, U32>, t, k))), psw(t, Con{c, x}, 1n+j)), psw(t, x, 1n+j), cost(taken(x, j), B.walk.turns(h)),
            psw_drop(t, x, c, k, 1n+j,
              Equal.trans(Nat, U32.to_nat(c), 1n+Nat.add(k, j), Nat.add(k, 1n+j), e, MNat.add_succ_sym(k, j)),
              ME.subst(Nat, z => {taken(x, z) == False{} : Bool}, 1n+Nat.add(k, j), Nat.add(k, 1n+j), MNat.add_succ_sym(k, j), hn)))

def untaken(+x: List<&2, U32>, +c: U32, +h: {B.has(x, c) == False{} : Bool}) -> {taken(x, Nat.add(U32.to_nat(c), 0n)) == False{} : Bool}:
  %MNat.add_zero_sym(U32.to_nat(c)) : {taken(x, _) == False{} : Bool}
  %has_taken(x, c) : {_ == False{} : Bool}
  h

# a unit neither walked nor on the stack, pushed: its calls' turns freed
def drop_at(+cal: List<&2, List<&2, U32>>, +x: List<&2, U32>, +c: U32, +h: {B.has(x, c) == False{} : Bool}) ->
    MNat.le(Nat.add(B.walk.turns(B.ids.at(cal, c)), psw(cal, Con{c, x}, 0n)), psw(cal, x, 0n)):
  psw_drop(cal, x, c, U32.to_nat(c), 0n, MNat.add_zero_sym(U32.to_nat(c)), untaken(x, c, h))

# a turn for each frame and two for each of its calls left
def frs(st: List<&2, B.Fm>) -> Nat:
  match st:
    case Nil{}:
      0n
    case Con{f, t}:
      match f:
        case B.Fm{+u, rest}:
          1n+Nat.add(B.walk.turns(rest), frs(t))

def pot(+cal: List<&2, List<&2, U32>>, s: B.Ds) -> Nat:
  match s:
    case B.Ds{+stack, roots, done, order, ers}:
      Nat.add(B.walk.turns(roots), Nat.add(frs(stack), psw(cal, List.append(&2, U32, B.fms.units(stack), done), 0n)))

# The arithmetic of each step's descent

def ar_succ(+l: Nat, +y: Nat) -> MNat.le(1n+Nat.add(l, y), Nat.add(l, 1n+y)):
  %MNat.add_succ(l, y) : MNat.le(_, Nat.add(l, 1n+y))
  MNat.le_refl(Nat.add(l, 1n+y))

def ar_root(+t: Nat, +g: Nat, +s1: Nat, +s: Nat, +h: MNat.le(Nat.add(g, s1), s)) ->
    MNat.le(1n+Nat.add(t, 1n+Nat.add(Nat.add(g, 0n), s1)), 1n+1n+Nat.add(t, s)):
  %MNat.add_zero_sym(g) : MNat.le(1n+Nat.add(t, 1n+Nat.add(_, s1)), 1n+1n+Nat.add(t, s))
  %MNat.add_succ_sym(t, Nat.add(g, s1)) : MNat.le(1n+_, 1n+1n+Nat.add(t, s))
  MNat.succ_le_succ(1n+Nat.add(t, Nat.add(g, s1)), 1n+Nat.add(t, s),
    MNat.succ_le_succ(Nat.add(t, Nat.add(g, s1)), Nat.add(t, s), MNat.add_le_add_left(Nat.add(g, s1), s, t, h)))

def ar_seen(+l: Nat, +y: Nat) -> MNat.le(1n+Nat.add(l, 1n+y), Nat.add(l, 1n+1n+1n+y)):
  MNat.le_trans(1n+Nat.add(l, 1n+y), Nat.add(l, 1n+1n+y), Nat.add(l, 1n+1n+1n+y),
    ar_succ(l, 1n+y), MNat.add_le_add_left(1n+1n+y, 1n+1n+1n+y, l, MNat.le_succ(1n+1n+y)))

def ar_push.k(+g: Nat, +k: Nat, +s1: Nat, +s: Nat, +h: MNat.le(Nat.add(g, s1), s)) -> MNat.le(Nat.add(Nat.add(g, 1n+k), s1), 1n+Nat.add(k, s)):
  %MNat.add_succ_sym(g, k) : MNat.le(Nat.add(_, s1), 1n+Nat.add(k, s))
  %MNat.add_assoc_sym(g, k, s1) : MNat.le(1n+_, 1n+Nat.add(k, s))
  %MNat.add_left_comm(k, g, s1) : MNat.le(1n+_, 1n+Nat.add(k, s))
  MNat.succ_le_succ(Nat.add(k, Nat.add(g, s1)), Nat.add(k, s), MNat.add_le_add_left(Nat.add(g, s1), s, k, h))

def ar_push(+l: Nat, +g: Nat, +k: Nat, +s1: Nat, +s: Nat, +h: MNat.le(Nat.add(g, s1), s)) ->
    MNat.le(1n+Nat.add(l, 1n+Nat.add(Nat.add(g, 1n+k), s1)), Nat.add(l, 1n+1n+1n+Nat.add(k, s))):
  MNat.le_trans(1n+Nat.add(l, 1n+Nat.add(Nat.add(g, 1n+k), s1)), Nat.add(l, 1n+1n+Nat.add(Nat.add(g, 1n+k), s1)), Nat.add(l, 1n+1n+1n+Nat.add(k, s)),
    ar_succ(l, 1n+Nat.add(Nat.add(g, 1n+k), s1)),
    MNat.add_le_add_left(1n+1n+Nat.add(Nat.add(g, 1n+k), s1), 1n+1n+1n+Nat.add(k, s), l,
      MNat.succ_le_succ(1n+Nat.add(Nat.add(g, 1n+k), s1), 1n+1n+Nat.add(k, s),
        MNat.succ_le_succ(Nat.add(Nat.add(g, 1n+k), s1), 1n+Nat.add(k, s), ar_push.k(g, k, s1, s, h)))))

def has_app(p: List<&2, U32>, +q: List<&2, U32>, +x: U32) -> {Bool.or(B.has(p, x), B.has(q, x)) == B.has(List.append(&2, U32, p, q), x) : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      %has_app(t, q, x) : {Bool.or(Bool.or(U32.is_eq(a, x), B.has(t, x)), B.has(q, x)) == Bool.or(U32.is_eq(a, x), _) : Bool}
      MB.or_assoc(U32.is_eq(a, x), B.has(t, x), B.has(q, x))

def not_in_app(+p: List<&2, U32>, +q: List<&2, U32>, +x: U32, +hp: {B.has(p, x) == False{} : Bool}, +hq: {B.has(q, x) == False{} : Bool}) ->
    {B.has(List.append(&2, U32, p, q), x) == False{} : Bool}:
  %has_app(p, q, x) : {_ == False{} : Bool}
  %Equal.sym(Bool, B.has(p, x), False{}, hp) : {Bool.or(_, B.has(q, x)) == False{} : Bool}
  hq

# Each step lowers the potential

def root_desc(+seen: Bool, +r: U32, +rt: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>,
    +cal: List<&2, List<&2, U32>>, +e: {seen == B.has(done, r) : Bool}) ->
    MNat.le(1n+pot(cal, B.ds.root.k(seen, r, rt, done, order, ers, cal)), pot(cal, B.Ds{Nil{}, Con{r, rt}, done, order, ers})):
  match seen:
    case True{}:
      MNat.le_succ(1n+Nat.add(B.walk.turns(rt), psw(cal, done, 0n)))
    case False{}:
      ar_root(B.walk.turns(rt), B.walk.turns(B.ids.at(cal, r)), psw(cal, Con{r, done}, 0n), psw(cal, done, 0n),
        drop_at(cal, done, r, Equal.sym(Bool, False{}, B.has(done, r), e)))

def call_desc(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +e1: {seen == B.has(done, c) : Bool}, +e2: {cyc == B.has(Con{u, B.fms.units(st)}, c) : Bool}) ->
    MNat.le(1n+pot(cal, B.ds.call.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us)), pot(cal, B.Ds{Con{B.Fm{u, Con{c, rs}}, st}, roots, done, order, ers})):
  match seen:
    case True{}:
      ar_seen(B.walk.turns(roots), Nat.add(Nat.add(B.walk.turns(rs), frs(st)), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n)))
    case False{}:
      match cyc:
        case True{}:
          ar_seen(B.walk.turns(roots), Nat.add(Nat.add(B.walk.turns(rs), frs(st)), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n)))
        case False{}:
          ar_push(B.walk.turns(roots), B.walk.turns(B.ids.at(cal, c)), Nat.add(B.walk.turns(rs), frs(st)), psw(cal, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}, 0n), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n),
            drop_at(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, c,
              not_in_app(Con{u, B.fms.units(st)}, done, c, Equal.sym(Bool, False{}, B.has(Con{u, B.fms.units(st)}, c), e2),
                Equal.sym(Bool, False{}, B.has(done, c), e1))))

def pop_desc(+u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +cal: List<&2, List<&2, U32>>) ->
    MNat.le(1n+Nat.add(B.walk.turns(roots), Nat.add(frs(st), psw(cal, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n))), Nat.add(B.walk.turns(roots), 1n+Nat.add(frs(st), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n)))):
  MNat.le_trans(1n+Nat.add(B.walk.turns(roots), Nat.add(frs(st), psw(cal, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n))), Nat.add(B.walk.turns(roots), 1n+Nat.add(frs(st), psw(cal, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n))), Nat.add(B.walk.turns(roots), 1n+Nat.add(frs(st), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n))),
    ar_succ(B.walk.turns(roots), Nat.add(frs(st), psw(cal, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n))),
    MNat.add_le_add_left(1n+Nat.add(frs(st), psw(cal, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n)), 1n+Nat.add(frs(st), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n)), B.walk.turns(roots),
      MNat.succ_le_succ(Nat.add(frs(st), psw(cal, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n)), Nat.add(frs(st), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n)),
        MNat.add_le_add_left(psw(cal, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n), frs(st), psw_sub(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n, pop_sub(u, B.fms.units(st), done))))))

def done_desc(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +cal: List<&2, List<&2, U32>>) ->
    MNat.le(1n+pot(cal, B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us)), pot(cal, B.Ds{Con{B.Fm{u, Nil{}}, st}, roots, done, order, ers})):
  match ok:
    case True{}:
      pop_desc(u, st, roots, done, cal)
    case False{}:
      pop_desc(u, st, roots, done, cal)

def step_desc(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +nf: {B.ds.finished(s) == False{} : Bool}) ->
    MNat.le(1n+pot(cal, B.ds.step(s, cal, obs, us)), pot(cal, s)):
  match s:
    case B.Ds{stack, +roots, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              Empty.absurd(MNat.le(1n+pot(cal, B.Ds{Nil{}, Nil{}, done, order, ers}), pot(cal, B.Ds{Nil{}, Nil{}, done, order, ers})),
                MB.true_ne_false()(nf))
            case Con{+r, +rt}:
              root_desc(B.has(done, r), r, rt, done, order, ers, cal, {==})
        case Con{f, +st}:
          match f:
            case B.Fm{+u, rest}:
              match rest:
                case Nil{}:
                  done_desc(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us, cal)
                case Con{+c, +rs}:
                  call_desc(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us, {==}, {==})

# a finished walk stays finished
def step_fin(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {B.ds.finished(s) == True{} : Bool}) ->
    {B.ds.finished(B.ds.step(s, cal, obs, us)) == True{} : Bool}:
  match s:
    case B.Ds{stack, roots, done, order, ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              {==}
            case Con{r, rt}:
              Empty.absurd({B.ds.finished(B.ds.step(B.Ds{Nil{}, Con{r, rt}, done, order, ers}, cal, obs, us)) == True{} : Bool}, MB.false_ne_true()(h))
        case Con{f, st}:
          Empty.absurd({B.ds.finished(B.ds.step(B.Ds{Con{f, st}, roots, done, order, ers}, cal, obs, us)) == True{} : Bool}, MB.false_ne_true()(h))

def go_fin(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {B.ds.finished(s) == True{} : Bool}) ->
    {B.ds.finished(B.ds.go(n, s, cal, obs, us)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+k:
      go_fin(k, B.ds.step(s, cal, obs, us), cal, obs, us, step_fin(s, cal, obs, us, h))

# a walk unfinished at the bound 0: its potential is not 0
def pot_pos(s: B.Ds, +cal: List<&2, List<&2, U32>>, +hf: MNat.le(pot(cal, s), 0n)) -> {B.ds.finished(s) == True{} : Bool}:
  match s:
    case B.Ds{stack, roots, done, order, ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              {==}
            case Con{r, rt}:
              Empty.absurd({B.ds.finished(B.Ds{Nil{}, Con{r, rt}, done, order, ers}) == True{} : Bool}, MB.false_ne_true()(hf))
        case Con{f, st}:
          match f:
            case B.Fm{u, rest}:
              Empty.absurd({B.ds.finished(B.Ds{Con{B.Fm{u, rest}, st}, roots, done, order, ers}) == True{} : Bool},
                MB.false_ne_true()(ME.subst(Nat, z => MNat.le(z, 0n),
                  Nat.add(B.walk.turns(roots), 1n+Nat.add(Nat.add(B.walk.turns(rest), frs(st)), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n))),
                  1n+Nat.add(B.walk.turns(roots), Nat.add(Nat.add(B.walk.turns(rest), frs(st)), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n))),
                  MNat.add_succ(B.walk.turns(roots), Nat.add(Nat.add(B.walk.turns(rest), frs(st)), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n))), hf)))

def ends_k(+fin: Bool, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +k: Nat,
    +e: {fin == B.ds.finished(s) : Bool}, +hf: MNat.le(pot(cal, s), 1n+k),
    ih: MNat.le(pot(cal, B.ds.step(s, cal, obs, us)), k) -> {B.ds.finished(B.ds.go(k, B.ds.step(s, cal, obs, us), cal, obs, us)) == True{} : Bool}) ->
    {B.ds.finished(B.ds.go(k, B.ds.step(s, cal, obs, us), cal, obs, us)) == True{} : Bool}:
  match fin:
    case True{}:
      go_fin(k, B.ds.step(s, cal, obs, us), cal, obs, us, step_fin(s, cal, obs, us, Equal.sym(Bool, True{}, B.ds.finished(s), e)))
    case False{}:
      ih(MNat.le_of_succ_le_succ(pot(cal, B.ds.step(s, cal, obs, us)), k,
        MNat.le_trans(1n+pot(cal, B.ds.step(s, cal, obs, us)), pot(cal, s), 1n+k,
          step_desc(s, cal, obs, us, Equal.sym(Bool, False{}, B.ds.finished(s), e)), hf)))

# within fuel no less than its potential, the walk finishes
def ends(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +hf: MNat.le(pot(cal, s), n)) ->
    {B.ds.finished(B.ds.go(n, s, cal, obs, us)) == True{} : Bool}:
  match n:
    case 0n:
      pot_pos(s, cal, hf)
    case 1n+(+k):
      ends_k(B.ds.finished(s), s, cal, obs, us, k, {==}, hf, q => ends(k, B.ds.step(s, cal, obs, us), cal, obs, us, q))

# the fuel is the potential at the start
def fuel_pot(+roots: List<&2, U32>, +cal: List<&2, List<&2, U32>>) -> MNat.le(pot(cal, B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}), B.walk.fuel(roots, cal)):
  %Equal.sym(Nat, psw(cal, Nil{}, 0n), B.walk.calls(cal), psw_nil(cal, 0n)) : MNat.le(Nat.add(B.walk.turns(roots), _), B.walk.fuel(roots, cal))
  MNat.le_refl(B.walk.fuel(roots, cal))

def walk_ends(+roots: List<&2, U32>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>) ->
    {B.ds.finished(B.walk(roots, cal, obs, us)) == True{} : Bool}:
  ends(B.walk.fuel(roots, cal), B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us, fuel_pot(roots, cal))

def Laws.order.ends(roots, cal, obs, us):
  walk_ends(roots, cal, obs, us)

# The walk the tool runs
# ----------------------
#
# The fast walk (`walk.fast`) is the walk above with each set its lists
# make kept beside them: lifted, a state gains those sets (`lift`), and
# from a lifted state a step of the fast walk is the lifted step of the
# walk, whatever the state, so that walking the lifted start is lifting
# the walk. The sets are tries on the units' bits: a word put is found
# where it equals the word asked for (`has_put`), whatever was there.

# an empty trie holds no word
def has_none(n: Nat, c: Word(n)) -> {B.wt.has(n, c, B.WtNone{}) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match c:
        case WCon{b, r}:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}

# words equal: their tails, and their last bits
def fin_eq(+a: Bool, +b: Bool, k: Cmp) -> {Bool.and(Cmp.is_eq(k), Cmp.is_eq(Bool.cmp(a, b))) == Cmp.is_eq(Word.cmp.fin(a, b, k)) : Bool}:
  match k:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def has_put.k(a: Bool, b: Bool, +p: Nat, +xr: Word(p), +cr: Word(p), t: B.Wt,
    ih: @s:B.Wt -> {B.wt.has(p, cr, B.wt.put(p, xr, s)) == Bool.or(Cmp.is_eq(Word.cmp(p, xr, cr)), B.wt.has(p, cr, s)) : Bool}) ->
    {B.wt.has(1n+p, WCon{b, cr}, B.wt.put(1n+p, WCon{a, xr}, t)) ==
      Bool.or(Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), Cmp.is_eq(Bool.cmp(a, b))), B.wt.has(1n+p, WCon{b, cr}, t)) : Bool}:
  match a b:
    case True{} True{}:
      match t:
        case B.WtNode{f, tt}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{True{}, cr}, B.wt.put(1n+p, WCon{True{}, xr}, B.WtNode{f, tt})) == Bool.or(_, B.wt.has(1n+p, WCon{True{}, cr}, B.WtNode{f, tt})) : Bool}
          ih(tt)
        case B.WtNone{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{True{}, cr}, B.wt.put(1n+p, WCon{True{}, xr}, B.WtNone{})) == Bool.or(_, B.wt.has(1n+p, WCon{True{}, cr}, B.WtNone{})) : Bool}
          %has_none(p, cr) : {B.wt.has(p, cr, B.wt.put(p, xr, B.WtNone{})) == Bool.or(Cmp.is_eq(Word.cmp(p, xr, cr)), _) : Bool}
          ih(B.WtNone{})
        case B.WtLeaf{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{True{}, cr}, B.wt.put(1n+p, WCon{True{}, xr}, B.WtLeaf{})) == Bool.or(_, B.wt.has(1n+p, WCon{True{}, cr}, B.WtLeaf{})) : Bool}
          %has_none(p, cr) : {B.wt.has(p, cr, B.wt.put(p, xr, B.WtNone{})) == Bool.or(Cmp.is_eq(Word.cmp(p, xr, cr)), _) : Bool}
          ih(B.WtNone{})
    case True{} False{}:
      match t:
        case B.WtNode{f, tt}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{False{}, cr}, B.wt.put(1n+p, WCon{True{}, xr}, B.WtNode{f, tt})) == Bool.or(_, B.wt.has(1n+p, WCon{False{}, cr}, B.WtNode{f, tt})) : Bool}
          {==}
        case B.WtNone{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{False{}, cr}, B.wt.put(1n+p, WCon{True{}, xr}, B.WtNone{})) == Bool.or(_, B.wt.has(1n+p, WCon{False{}, cr}, B.WtNone{})) : Bool}
          has_none(p, cr)
        case B.WtLeaf{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{False{}, cr}, B.wt.put(1n+p, WCon{True{}, xr}, B.WtLeaf{})) == Bool.or(_, B.wt.has(1n+p, WCon{False{}, cr}, B.WtLeaf{})) : Bool}
          has_none(p, cr)
    case False{} True{}:
      match t:
        case B.WtNode{f, tt}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{True{}, cr}, B.wt.put(1n+p, WCon{False{}, xr}, B.WtNode{f, tt})) == Bool.or(_, B.wt.has(1n+p, WCon{True{}, cr}, B.WtNode{f, tt})) : Bool}
          {==}
        case B.WtNone{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{True{}, cr}, B.wt.put(1n+p, WCon{False{}, xr}, B.WtNone{})) == Bool.or(_, B.wt.has(1n+p, WCon{True{}, cr}, B.WtNone{})) : Bool}
          has_none(p, cr)
        case B.WtLeaf{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{True{}, cr}, B.wt.put(1n+p, WCon{False{}, xr}, B.WtLeaf{})) == Bool.or(_, B.wt.has(1n+p, WCon{True{}, cr}, B.WtLeaf{})) : Bool}
          has_none(p, cr)
    case False{} False{}:
      match t:
        case B.WtNode{f, tt}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{False{}, cr}, B.wt.put(1n+p, WCon{False{}, xr}, B.WtNode{f, tt})) == Bool.or(_, B.wt.has(1n+p, WCon{False{}, cr}, B.WtNode{f, tt})) : Bool}
          ih(f)
        case B.WtNone{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{False{}, cr}, B.wt.put(1n+p, WCon{False{}, xr}, B.WtNone{})) == Bool.or(_, B.wt.has(1n+p, WCon{False{}, cr}, B.WtNone{})) : Bool}
          %has_none(p, cr) : {B.wt.has(p, cr, B.wt.put(p, xr, B.WtNone{})) == Bool.or(Cmp.is_eq(Word.cmp(p, xr, cr)), _) : Bool}
          ih(B.WtNone{})
        case B.WtLeaf{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{False{}, cr}, B.wt.put(1n+p, WCon{False{}, xr}, B.WtLeaf{})) == Bool.or(_, B.wt.has(1n+p, WCon{False{}, cr}, B.WtLeaf{})) : Bool}
          %has_none(p, cr) : {B.wt.has(p, cr, B.wt.put(p, xr, B.WtNone{})) == Bool.or(Cmp.is_eq(Word.cmp(p, xr, cr)), _) : Bool}
          ih(B.WtNone{})

# a word put, then one asked for: found where they are equal, or where it
# was found before
def has_put(n: Nat, x: Word(n), c: Word(n), t: B.Wt) ->
    {B.wt.has(n, c, B.wt.put(n, x, t)) == Bool.or(Cmp.is_eq(Word.cmp(n, x, c)), B.wt.has(n, c, t)) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match x:
        case WCon{+a, +xr}:
          match c:
            case WCon{+b, +cr}:
              %fin_eq(a, b, Word.cmp(p, xr, cr)) :
                {B.wt.has(1n+p, WCon{b, cr}, B.wt.put(1n+p, WCon{a, xr}, t)) == Bool.or(_, B.wt.has(1n+p, WCon{b, cr}, t)) : Bool}
              has_put.k(a, b, p, xr, cr, t, s => has_put(p, xr, cr, s))

def vs_put(+t: B.Wt, x: U32, c: U32) -> {B.vs.has(B.vs.put(t, x), c) == Bool.or(U32.is_eq(x, c), B.vs.has(t, c)) : Bool}:
  match x c:
    case U32{xw} U32{cw}:
      has_put(32n, xw, cw, t)

# the set a list makes holds what the list has
def vs_of(xs: List<&2, U32>, +c: U32) -> {B.vs.has(B.vs.of(xs), c) == B.has(xs, c) : Bool}:
  match xs:
    case Nil{}:
      match c:
        case U32{w}:
          has_none(32n, w)
    case Con{+x, +t}:
      %Equal.sym(Bool, B.vs.has(B.vs.put(B.vs.of(t), x), c), Bool.or(U32.is_eq(x, c), B.vs.has(B.vs.of(t), c)), vs_put(B.vs.of(t), x, c)) :
        {_ == Bool.or(U32.is_eq(x, c), B.has(t, c)) : Bool}
      %vs_of(t, c) : {Bool.or(U32.is_eq(x, c), B.vs.has(B.vs.of(t), c)) == Bool.or(U32.is_eq(x, c), _) : Bool}
      {==}

def vs_all(xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.vs.all(xs, B.vs.of(ys)) == B.all.in(xs, ys) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %vs_of(ys, x) : {Bool.and(B.vs.has(B.vs.of(ys), x), B.vs.all(r, B.vs.of(ys))) == Bool.and(_, B.all.in(r, ys)) : Bool}
      %vs_all(r, ys) : {Bool.and(B.vs.has(B.vs.of(ys), x), B.vs.all(r, B.vs.of(ys))) == Bool.and(B.vs.has(B.vs.of(ys), x), _) : Bool}
      {==}

# words put in either order make one trie: its shape is its set's
def put_comm.k(a: Bool, b: Bool, +p: Nat, +xr: Word(p), +yr: Word(p), t: B.Wt,
    ih: @s:B.Wt -> {B.wt.put(p, xr, B.wt.put(p, yr, s)) == B.wt.put(p, yr, B.wt.put(p, xr, s)) : B.Wt}) ->
    {B.wt.put(1n+p, WCon{a, xr}, B.wt.put(1n+p, WCon{b, yr}, t)) == B.wt.put(1n+p, WCon{b, yr}, B.wt.put(1n+p, WCon{a, xr}, t)) : B.Wt}:
  match a b:
    case True{} True{}:
      match t:
        case B.WtNode{+f, tt}:
          Equal.cong(B.Wt, B.Wt, z => B.WtNode{f, z}, B.wt.put(p, xr, B.wt.put(p, yr, tt)), B.wt.put(p, yr, B.wt.put(p, xr, tt)), ih(tt))
        case B.WtNone{}:
          Equal.cong(B.Wt, B.Wt, z => B.WtNode{B.WtNone{}, z}, B.wt.put(p, xr, B.wt.put(p, yr, B.WtNone{})), B.wt.put(p, yr, B.wt.put(p, xr, B.WtNone{})), ih(B.WtNone{}))
        case B.WtLeaf{}:
          Equal.cong(B.Wt, B.Wt, z => B.WtNode{B.WtNone{}, z}, B.wt.put(p, xr, B.wt.put(p, yr, B.WtNone{})), B.wt.put(p, yr, B.wt.put(p, xr, B.WtNone{})), ih(B.WtNone{}))
    case True{} False{}:
      match t:
        case B.WtNode{f, tt}:
          {==}
        case B.WtNone{}:
          {==}
        case B.WtLeaf{}:
          {==}
    case False{} True{}:
      match t:
        case B.WtNode{f, tt}:
          {==}
        case B.WtNone{}:
          {==}
        case B.WtLeaf{}:
          {==}
    case False{} False{}:
      match t:
        case B.WtNode{f, +tt}:
          Equal.cong(B.Wt, B.Wt, z => B.WtNode{z, tt}, B.wt.put(p, xr, B.wt.put(p, yr, f)), B.wt.put(p, yr, B.wt.put(p, xr, f)), ih(f))
        case B.WtNone{}:
          Equal.cong(B.Wt, B.Wt, z => B.WtNode{z, B.WtNone{}}, B.wt.put(p, xr, B.wt.put(p, yr, B.WtNone{})), B.wt.put(p, yr, B.wt.put(p, xr, B.WtNone{})), ih(B.WtNone{}))
        case B.WtLeaf{}:
          Equal.cong(B.Wt, B.Wt, z => B.WtNode{z, B.WtNone{}}, B.wt.put(p, xr, B.wt.put(p, yr, B.WtNone{})), B.wt.put(p, yr, B.wt.put(p, xr, B.WtNone{})), ih(B.WtNone{}))

def put_comm(n: Nat, x: Word(n), y: Word(n), t: B.Wt) -> {B.wt.put(n, x, B.wt.put(n, y, t)) == B.wt.put(n, y, B.wt.put(n, x, t)) : B.Wt}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match x:
        case WCon{a, +xr}:
          match y:
            case WCon{b, +yr}:
              put_comm.k(a, b, p, xr, yr, t, s => put_comm(p, xr, yr, s))

def vs_comm(t: B.Wt, x: U32, y: U32) -> {B.vs.put(B.vs.put(t, y), x) == B.vs.put(B.vs.put(t, x), y) : B.Wt}:
  match x y:
    case U32{xw} U32{yw}:
      put_comm(32n, xw, yw, t)

# a unit moved within the list: the same set
def of_app(a: List<&2, U32>, +u: U32, +d: List<&2, U32>) ->
    {B.vs.of(List.append(&2, U32, a, Con{u, d})) == B.vs.put(B.vs.of(List.append(&2, U32, a, d)), u) : B.Wt}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(B.Wt, B.vs.put(B.vs.of(List.append(&2, U32, t, Con{u, d})), h), B.vs.put(B.vs.put(B.vs.of(List.append(&2, U32, t, d)), u), h),
        B.vs.put(B.vs.put(B.vs.of(List.append(&2, U32, t, d)), h), u),
        Equal.cong(B.Wt, B.Wt, z => B.vs.put(z, h), B.vs.of(List.append(&2, U32, t, Con{u, d})), B.vs.put(B.vs.of(List.append(&2, U32, t, d)), u), of_app(t, u, d)),
        vs_comm(B.vs.of(List.append(&2, U32, t, d)), h, u))

# The calls by position: a list split in two, its even positions first,
# read back as the list at double the position, and one more

def e_cons(+x: List<&2, U32>, p: B.Eo) -> {Con{x, B.eo.o(p)} == B.eo.e(B.eo.cons(x, p)) : List<&2, List<&2, U32>>}:
  match p:
    case B.Eo{e, o}:
      {==}

def o_cons(+x: List<&2, U32>, p: B.Eo) -> {B.eo.e(p) == B.eo.o(B.eo.cons(x, p)) : List<&2, List<&2, U32>>}:
  match p:
    case B.Eo{e, o}:
      {==}

def e_get.k(+x: List<&2, U32>, +y: List<&2, U32>, +r: List<&2, List<&2, U32>>, i: Nat,
    ih: @j:Nat -> {List.get(&2, List<&2, U32>, B.eo.e(B.eo.split(r)), j) == List.get(&2, List<&2, U32>, r, Nat.double(j)) : Maybe<&2, List<&2, U32>>}) ->
    {List.get(&2, List<&2, U32>, Con{x, B.eo.e(B.eo.split(r))}, i) == List.get(&2, List<&2, U32>, Con{x, Con{y, r}}, Nat.double(i)) : Maybe<&2, List<&2, U32>>}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      ih(j)

def e_get(xs: List<&2, List<&2, U32>>, i: Nat) -> {List.get(&2, List<&2, U32>, B.eo.e(B.eo.split(xs)), i) == List.get(&2, List<&2, U32>, xs, Nat.double(i)) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      match t:
        case Nil{}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              {==}
        case Con{+y, +r}:
          %e_cons(x, B.eo.cons(y, B.eo.split(r))) :
            {List.get(&2, List<&2, U32>, _, i) == List.get(&2, List<&2, U32>, Con{x, Con{y, r}}, Nat.double(i)) : Maybe<&2, List<&2, U32>>}
          %o_cons(y, B.eo.split(r)) :
            {List.get(&2, List<&2, U32>, Con{x, _}, i) == List.get(&2, List<&2, U32>, Con{x, Con{y, r}}, Nat.double(i)) : Maybe<&2, List<&2, U32>>}
          e_get.k(x, y, r, i, j => e_get(r, j))

def o_get(xs: List<&2, List<&2, U32>>, +i: Nat) -> {List.get(&2, List<&2, U32>, B.eo.o(B.eo.split(xs)), i) == List.get(&2, List<&2, U32>, xs, 1n+Nat.double(i)) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %o_cons(x, B.eo.split(t)) :
        {List.get(&2, List<&2, U32>, _, i) == List.get(&2, List<&2, U32>, Con{x, t}, 1n+Nat.double(i)) : Maybe<&2, List<&2, U32>>}
      e_get(t, i)

# the calls table answers as the list at the position the word reads
def ct_at(n: Nat, w: Word(n), xs: List<&2, List<&2, U32>>) -> {B.ct.at(n, w, B.ct.build(n, xs)) == B.ids.or(List.get(&2, List<&2, U32>, xs, Word.to_nat(n, w))) : List<&2, U32>}:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{x, t}:
          {==}
    case 1n+(+p):
      match w:
        case WCon{b, +r}:
          match b:
            case True{}:
              match xs:
                case Nil{}:
                  {==}
                case Con{+x, +t}:
                  %o_get(Con{x, t}, Word.to_nat(p, r)) : {B.ct.at(p, r, B.ct.build(p, B.eo.o(B.eo.split(Con{x, t})))) == B.ids.or(_) : List<&2, U32>}
                  ct_at(p, r, B.eo.o(B.eo.split(Con{x, t})))
            case False{}:
              match xs:
                case Nil{}:
                  {==}
                case Con{+x, +t}:
                  %e_get(Con{x, t}, Word.to_nat(p, r)) : {B.ct.at(p, r, B.ct.build(p, B.eo.e(B.eo.split(Con{x, t})))) == B.ids.or(_) : List<&2, U32>}
                  ct_at(p, r, B.eo.e(B.eo.split(Con{x, t})))

# the calls table answers as ids.at
def cs_at(+cal: List<&2, List<&2, U32>>, c: U32) -> {B.cs.at(B.ct.of(cal), c) == B.ids.at(cal, c) : List<&2, U32>}:
  match c:
    case U32{w}:
      ct_at(32n, w, cal)

# The walk and the fast walk, step by step

# a state with the sets its lists make: those walked, those ordered, and
# those entered (the stack's units, then those walked)
def lift(s: B.Ds) -> B.Df:
  match s:
    case B.Ds{+stack, roots, +done, +order, ers}:
      B.Df{stack, roots, done, order, ers, B.vs.of(done), B.vs.of(order), B.vs.of(List.append(&2, U32, B.fms.units(stack), done))}

def ds_lift(s: B.Ds) -> {B.df.ds(lift(s)) == s : B.Ds}:
  match s:
    case B.Ds{stack, roots, done, order, ers}:
      {==}

def root_lift.k(seen: Bool, +r: U32, +rt: List<&2, U32>, +d: List<&2, U32>, +o: List<&2, U32>, +e: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>) ->
    {B.df.root.k(seen, r, rt, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.of(d), B.ct.of(cal)) == lift(B.ds.root.k(seen, r, rt, d, o, e, cal)) : B.Df}:
  match seen:
    case True{}:
      {==}
    case False{}:
      %cs_at(cal, r) : {B.df.root.k(False{}, r, rt, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.of(d), B.ct.of(cal)) ==
        B.Df{[B.Fm{r, _}], rt, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.put(B.vs.of(d), r)} : B.Df}
      {==}

# the lifted state a unit held back leaves, its entered set given
def lift.done.f(+u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +d: List<&2, U32>, +o: List<&2, U32>, +e: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, ve: B.Wt) -> B.Df:
  B.Df{st, roots, Con{u, d}, o,
    B.when(List<&2, B.Er>, List.is_empty(&2, B.Er, e),
      w => [B.Er{B.node.no(B.un.node(B.un.at(us, u))), B.text(B.un.name(obs, us, u)) ++ ": Blend's walk reached it before its callees, a fault of Blend's"}],
      w => e), B.vs.put(B.vs.of(d), u), B.vs.of(o), ve}

def done_lift.k(ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +d: List<&2, U32>, +o: List<&2, U32>, +e: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>) ->
    {B.df.done.k(ok, u, st, roots, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), d)}), obs, us) == lift(B.ds.done.k(ok, u, st, roots, d, o, e, obs, us)) : B.Df}:
  match ok:
    case True{}:
      %Equal.sym(B.Wt, B.vs.of(List.append(&2, U32, B.fms.units(st), Con{u, d})), B.vs.put(B.vs.of(List.append(&2, U32, B.fms.units(st), d)), u), of_app(B.fms.units(st), u, d)) :
        {B.df.done.k(True{}, u, st, roots, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), d)}), obs, us) ==
          B.Df{st, roots, Con{u, d}, Con{u, o}, e, B.vs.put(B.vs.of(d), u), B.vs.put(B.vs.of(o), u), _} : B.Df}
      {==}
    case False{}:
      %Equal.sym(B.Wt, B.vs.of(List.append(&2, U32, B.fms.units(st), Con{u, d})), B.vs.put(B.vs.of(List.append(&2, U32, B.fms.units(st), d)), u), of_app(B.fms.units(st), u, d)) :
        {B.df.done.k(False{}, u, st, roots, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), d)}), obs, us) ==
          lift.done.f(u, st, roots, d, o, e, obs, us, _) : B.Df}
      {==}

def call_lift.k(seen: Bool, cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +d: List<&2, U32>, +o: List<&2, U32>,
    +e: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>) ->
    {B.df.call.k(seen, Bool.or(cyc, seen), c, u, rs, st, roots, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), d)}), B.ct.of(cal), obs, us) ==
      lift(B.ds.call.k(seen, cyc, c, u, rs, st, roots, d, o, e, cal, obs, us)) : B.Df}:
  match seen cyc:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      %cs_at(cal, c) : {B.df.call.k(False{}, False{}, c, u, rs, st, roots, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), d)}), B.ct.of(cal), obs, us) ==
        B.Df{Con{B.Fm{c, _}, Con{B.Fm{u, rs}, st}}, roots, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.put(B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), d)}), c)} : B.Df}
      {==}

# from a lifted state, a step of the fast walk is the lifted step of the
# walk: each of its lookups answers as the search it stands for
def step_lift(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>) ->
    {B.df.step(lift(s), B.ct.of(cal), obs, us) == lift(B.ds.step(s, cal, obs, us)) : B.Df}:
  match s:
    case B.Ds{stack, +roots, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              {==}
            case Con{+r, +rt}:
              %Equal.sym(Bool, B.vs.has(B.vs.of(done), r), B.has(done, r), vs_of(done, r)) :
                {B.df.root.k(_, r, rt, done, order, ers, B.vs.of(done), B.vs.of(order), B.vs.of(done), B.ct.of(cal)) ==
                  lift(B.ds.root.k(B.has(done, r), r, rt, done, order, ers, cal)) : B.Df}
              root_lift.k(B.has(done, r), r, rt, done, order, ers, cal)
        case Con{f, +st}:
          match f:
            case B.Fm{+u, rest}:
              match rest:
                case Nil{}:
                  %Equal.sym(List<&2, U32>, B.cs.at(B.ct.of(cal), u), B.ids.at(cal, u), cs_at(cal, u)) :
                    {B.df.done.k(B.vs.all(_, B.vs.of(order)), u, st, roots, done, order, ers, B.vs.of(done), B.vs.of(order), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), done)}), obs, us) ==
                      lift(B.ds.done.k(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us)) : B.Df}
                  %Equal.sym(Bool, B.vs.all(B.ids.at(cal, u), B.vs.of(order)), B.all.in(B.ids.at(cal, u), order), vs_all(B.ids.at(cal, u), order)) :
                    {B.df.done.k(_, u, st, roots, done, order, ers, B.vs.of(done), B.vs.of(order), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), done)}), obs, us) ==
                      lift(B.ds.done.k(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us)) : B.Df}
                  done_lift.k(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us)
                case Con{+c, +rs}:
                  %Equal.sym(Bool, B.vs.has(B.vs.of(done), c), B.has(done, c), vs_of(done, c)) :
                    {B.df.call.k(_, B.vs.has(B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), done)}), c), c, u, rs, st, roots, done, order, ers, B.vs.of(done), B.vs.of(order), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), done)}), B.ct.of(cal), obs, us) ==
                      lift(B.ds.call.k(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us)) : B.Df}
                  %Equal.sym(Bool, B.vs.has(B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), done)}), c), B.has(Con{u, List.append(&2, U32, B.fms.units(st), done)}, c), vs_of(Con{u, List.append(&2, U32, B.fms.units(st), done)}, c)) :
                    {B.df.call.k(B.has(done, c), _, c, u, rs, st, roots, done, order, ers, B.vs.of(done), B.vs.of(order), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), done)}), B.ct.of(cal), obs, us) ==
                      lift(B.ds.call.k(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us)) : B.Df}
                  %has_app(Con{u, B.fms.units(st)}, done, c) :
                    {B.df.call.k(B.has(done, c), _, c, u, rs, st, roots, done, order, ers, B.vs.of(done), B.vs.of(order), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), done)}), B.ct.of(cal), obs, us) ==
                      lift(B.ds.call.k(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us)) : B.Df}
                  call_lift.k(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us)

# walking a lifted state is lifting the walk
def go_lift(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>) ->
    {B.df.go(n, lift(s), B.ct.of(cal), obs, us) == lift(B.ds.go(n, s, cal, obs, us)) : B.Df}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      %Equal.sym(B.Df, B.df.step(lift(s), B.ct.of(cal), obs, us), lift(B.ds.step(s, cal, obs, us)), step_lift(s, cal, obs, us)) :
        {B.df.go(k, _, B.ct.of(cal), obs, us) == lift(B.ds.go(k, B.ds.step(s, cal, obs, us), cal, obs, us)) : B.Df}
      go_lift(k, B.ds.step(s, cal, obs, us), cal, obs, us)

def Laws.order.fast(roots, cal, obs, us):
  %Equal.sym(B.Df, B.df.go(B.walk.fuel(roots, cal), lift(B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}), B.ct.of(cal), obs, us),
      lift(B.ds.go(B.walk.fuel(roots, cal), B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us)),
      go_lift(B.walk.fuel(roots, cal), B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us)) :
    {B.df.ds(_) == B.walk(roots, cal, obs, us) : B.Ds}
  ds_lift(B.ds.go(B.walk.fuel(roots, cal), B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us))

# What is emitted
# ---------------
#
# The writer and the names check, each a loop of its own over the order,
# against one list of the definitions emitted (`defs.of`).

def defs_app(a: List<&2, B.Dp>, +c: List<&2, B.Dp>, +e: B.Ec, b: B.Tb) ->
    {B.defs.put(List.append(&2, B.Dp, a, c), e, b) == B.defs.put(c, e, B.defs.put(a, e, b)) : B.Tb}:
  match a:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case B.Dp{+x, +j}:
          defs_app(t, c, e, B.unit.put(e, x, j, b))

def defs_copies(n: Nat, +e: B.Ec, +x: U32, +j: U32, b: B.Tb) -> {B.defs.put(B.dps.copies(n, x, j), e, b) == B.copies.put(n, e, x, j, b) : B.Tb}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      defs_copies(k, e, x, (j + 1 : U32), B.unit.put(e, x, j, b))

def unit_all(+e: B.Ec, +x: U32, mu: B.Mu, b: B.Tb) ->
    {B.copies.put(U32.to_nat(B.mu.m(mu)), e, x, 1, B.unit.put(e, x, 0, b)) == B.unit.all(e, x, mu, b) : B.Tb}:
  match mu:
    case B.Mu{+m, +kind}:
      {==}

def Laws.emit.defs(xs, e, b):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %unit_all(e, x, B.ec.mu(e, x), b) :
        {B.order.put(t, e, _) == B.defs.put(B.defs.of(Con{x, t}, e), e, b) : B.Tb}
      %Equal.sym(B.Tb, B.defs.put(List.append(&2, B.Dp, B.dps.copies(U32.to_nat(B.mu.m(B.ec.mu(e, x))), x, 1), B.defs.of(t, e)), e, B.unit.put(e, x, 0, b)), B.defs.put(B.defs.of(t, e), e, B.defs.put(B.dps.copies(U32.to_nat(B.mu.m(B.ec.mu(e, x))), x, 1), e, B.unit.put(e, x, 0, b))), defs_app(B.dps.copies(U32.to_nat(B.mu.m(B.ec.mu(e, x))), x, 1), B.defs.of(t, e), e, B.unit.put(e, x, 0, b))) :
        {B.order.put(t, e, B.copies.put(U32.to_nat(B.mu.m(B.ec.mu(e, x))), e, x, 1, B.unit.put(e, x, 0, b))) == _ : B.Tb}
      %Equal.sym(B.Tb, B.defs.put(B.dps.copies(U32.to_nat(B.mu.m(B.ec.mu(e, x))), x, 1), e, B.unit.put(e, x, 0, b)), B.copies.put(U32.to_nat(B.mu.m(B.ec.mu(e, x))), e, x, 1, B.unit.put(e, x, 0, b)), defs_copies(U32.to_nat(B.mu.m(B.ec.mu(e, x))), e, x, 1, B.unit.put(e, x, 0, b))) :
        {B.order.put(t, e, B.copies.put(U32.to_nat(B.mu.m(B.ec.mu(e, x))), e, x, 1, B.unit.put(e, x, 0, b))) == B.defs.put(B.defs.of(t, e), e, _) : B.Tb}
      Laws.emit.defs(t, e, B.copies.put(U32.to_nat(B.mu.m(B.ec.mu(e, x))), e, x, 1, B.unit.put(e, x, 0, b)))

def names_app(a: List<&2, B.Dp>, +c: List<&2, B.Dp>, +e: B.Ec) ->
    {List.append(&2, B.Nm, B.defs.names(a, e), B.defs.names(c, e)) == B.defs.names(List.append(&2, B.Dp, a, c), e) : List<&2, B.Nm>}:
  match a:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case B.Dp{+x, +j}:
          %names_app(t, c, e) : {Con{B.Nm{B.own.name(e, x, j), x, B.node.no(B.un.node(B.ec.un(e, x)))}, List.append(&2, B.Nm, B.defs.names(t, e), B.defs.names(c, e))} ==
            Con{B.Nm{B.own.name(e, x, j), x, B.node.no(B.un.node(B.ec.un(e, x)))}, _} : List<&2, B.Nm>}
          {==}

def names_copies(n: Nat, +e: B.Ec, +x: U32, +j: U32) -> {B.names.copies(n, e, x, j) == B.defs.names(B.dps.copies(n, x, j), e) : List<&2, B.Nm>}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %names_copies(k, e, x, (j + 1 : U32)) : {Con{B.Nm{B.own.name(e, x, j), x, B.node.no(B.un.node(B.ec.un(e, x)))}, B.names.copies(k, e, x, (j + 1 : U32))} ==
        Con{B.Nm{B.own.name(e, x, j), x, B.node.no(B.un.node(B.ec.un(e, x)))}, _} : List<&2, B.Nm>}
      {==}

def Laws.emit.names(xs, e):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(List<&2, B.Nm>, B.names.copies(1n+U32.to_nat(B.mu.m(B.ec.mu(e, x))), e, x, 0), B.defs.names(B.dps.copies(1n+U32.to_nat(B.mu.m(B.ec.mu(e, x))), x, 0), e), names_copies(1n+U32.to_nat(B.mu.m(B.ec.mu(e, x))), e, x, 0)) :
        {List.append(&2, B.Nm, _, B.names.all(t, e)) == B.defs.names(B.defs.of(Con{x, t}, e), e) : List<&2, B.Nm>}
      %Equal.sym(List<&2, B.Nm>, B.names.all(t, e), B.defs.names(B.defs.of(t, e), e), Laws.emit.names(t, e)) :
        {List.append(&2, B.Nm, B.defs.names(B.dps.copies(1n+U32.to_nat(B.mu.m(B.ec.mu(e, x))), x, 0), e), _) == B.defs.names(B.defs.of(Con{x, t}, e), e) : List<&2, B.Nm>}
      names_app(B.dps.copies(1n+U32.to_nat(B.mu.m(B.ec.mu(e, x))), x, 0), B.defs.of(t, e), e)
