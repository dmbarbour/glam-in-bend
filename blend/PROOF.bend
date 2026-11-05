# Blend's own proofs, of the laws LAWS.bend states.

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
