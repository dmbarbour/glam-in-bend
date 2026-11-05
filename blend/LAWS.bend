# Blend's own laws (docs/plans/Blend_2026-11-04.md, `blend-laws`), the
# guarantees a user sees first. PROOF.bend proves them.

import Base
import ./blend.bend as B

# LAW: `same` says two names are the same only where they are equal, so a
# reference binds to the definition it names and no other.
# Record: blend-namespaces-as-bends
law names.same_eq:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +h: {B.same(a, b) == True{} : Bool}
  {a == b : List<&2, U32>}

# LAW: and every name is the same as itself.
# Record: blend-namespaces-as-bends
law names.same_refl:
  for +a: List<&2, U32>
  {B.same(a, a) == True{} : Bool}

# LAW: a dotted name split into its parts and joined back is itself, so a
# path names what its writer wrote (`Outer.Inner.f`).
# Record: blend-namespaces-as-bends
law names.dots_parts:
  for +x: List<&2, U32>
  {B.dots(B.parts(x)) == x : List<&2, U32>}

# LAW: a token that names nothing, a number, a string, a comment, a space,
# a symbol or an empty name, is emitted as it is written: a body is Bend,
# its references aside.
# Record: blend-adds-no-bend-logic
law locals.not_name:
  for +cx: B.Cx
  for +o: U32
  for +q: U32
  for +locals: List<&2, List<&2, U32>>
  for +t: B.Tok
  for +no: U32
  for h: {B.tok.txt(t) == Nil{} : List<&2, U32>}
  {B.rr.of(cx, o, q, locals, t, no) == B.rr.tok(t) : B.Rr}

# LAW: a name a local binds, a parameter or a binding of the body, is
# emitted as it is written, bound to no definition; a name beginning `^`
# (a host's) or `~` (a template's argument) aside.
# Record: blend-no-shadowing
law locals.kept:
  for +cx: B.Cx
  for +o: U32
  for +q: U32
  for +locals: List<&2, List<&2, U32>>
  for +h: U32
  for +r: List<&2, U32>
  for +no: U32
  for a: {U32.is_eq(h, 94) == False{} : Bool}
  for b: {U32.is_eq(h, 126) == False{} : Bool}
  for +l: {B.names.has(locals, Con{h, r}) == True{} : Bool}
  {B.rr.of(cx, o, q, locals, B.TName{Con{h, r}}, no) == B.rr.tok(B.TName{Con{h, r}}) : B.Rr}

# LAW: and a local passed on as a template's argument, `~f`, likewise.
# Record: blend-no-shadowing
law locals.template:
  for +cx: B.Cx
  for +o: U32
  for +q: U32
  for +locals: List<&2, List<&2, U32>>
  for +r: List<&2, U32>
  for +no: U32
  for l: {B.names.has(locals, r) == True{} : Bool}
  {B.rr.of(cx, o, q, locals, B.TName{Con{126, r}}, no) == B.rr.tok(B.TName{Con{126, r}}) : B.Rr}

# LAW: a line's tokens spell it exactly, every byte in a token, in order,
# none dropped and none added: a body is emitted as written, its
# references aside.
# Record: blend-adds-no-bend-logic
law tokens.spell:
  for +xs: List<&2, U32>
  {B.toks.text(B.toks(xs)) == xs : List<&2, U32>}

# LAW: a file's lines, each its indentation's spaces then its text,
# joined back by newlines, are the file's bytes less carriage returns:
# Blend reads every byte of a file but those. For a file shorter than
# 2^32 bytes, as every file Blend reads is (its size a U32).
# Record: blend-adds-no-bend-logic
law lines.join:
  for +bs: List<&2, U32>
  for h: {Nat.is_lt(List.length(&2, U32, bs), Nat.pow(2n, 32n)) == True{} : Bool}
  {B.lines.text(B.lines(bs)) == B.uncr(bs) : List<&2, U32>}

# LAW: the walk's order, emitted reversed, puts each unit after the units
# it calls, as Bend requires a definition after those it calls; whatever
# the roots and the calls, a cycle among them reported, never emitted.
# Record: blend-adds-no-bend-logic
law order.callees_first:
  for +roots: List<&2, U32>
  for +cal: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  {B.ordered(B.ds.order(B.walk(roots, cal, obs, us)), cal) == True{} : Bool}

# LAW: the walk's order holds each unit once at most: with
# order.callees_first, each definition is emitted after its callees and
# none twice.
# Record: blend-adds-no-bend-logic
law order.once:
  for +roots: List<&2, U32>
  for +cal: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  {B.distinct(B.ds.order(B.walk(roots, cal, obs, us))) == True{} : Bool}

# LAW: where the walk reports no error, every unit it walked is in its
# order: the order's guard (a unit joins once its callees have) held none
# back, and nothing walked is lost.
# Record: blend-adds-no-bend-logic
law order.walked:
  for +roots: List<&2, U32>
  for +cal: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for h: {List.is_empty(&2, B.Er, B.ds.ers(B.walk(roots, cal, obs, us))) == True{} : Bool}
  {B.all.in(B.ds.walked(B.walk(roots, cal, obs, us)), B.ds.order(B.walk(roots, cal, obs, us))) == True{} : Bool}

# LAW: once the walk has finished, its stack and its roots spent, every
# root has been walked.
# Record: blend-adds-no-bend-logic
law order.roots:
  for +roots: List<&2, U32>
  for +cal: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for h: {B.ds.finished(B.walk(roots, cal, obs, us)) == True{} : Bool}
  {B.all.in(roots, B.ds.walked(B.walk(roots, cal, obs, us))) == True{} : Bool}

# LAW: once the walk has finished, every unit a walked unit calls has been
# walked: with order.roots, every unit a root reaches, so that nothing a
# definition calls is left out.
# Record: blend-adds-no-bend-logic
law order.closed:
  for +roots: List<&2, U32>
  for +cal: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for h: {B.ds.finished(B.walk(roots, cal, obs, us)) == True{} : Bool}
  {B.calls.in(B.ds.walked(B.walk(roots, cal, obs, us)), cal, B.ds.walked(B.walk(roots, cal, obs, us))) == True{} : Bool}

# LAW: the walk finishes within its fuel, whatever its roots and calls,
# so that `order.roots` and `order.closed` hold always: every root and
# every unit one reaches is walked, each in its order once
# (`order.once`), after its callees (`order.callees_first`), and in it
# where no error is reported (`order.walked`).
# Record: blend-adds-no-bend-logic
law order.ends:
  for +roots: List<&2, U32>
  for +cal: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  {B.ds.finished(B.walk(roots, cal, obs, us)) == True{} : Bool}

# LAW: the walk the tool runs is the walk the laws above follow: with
# its sets dropped, its state is walk's, so that each of those laws holds
# of the order Blend emits (`blend-scale.walk`).
# Record: blend-adds-no-bend-logic
law order.fast:
  for +roots: List<&2, U32>
  for +cal: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  {B.df.ds(B.walk.fast(roots, cal, obs, us)) == B.walk(roots, cal, obs, us) : B.Ds}

# LAW: the writer writes each unit of an order by its own name, then
# once for each copy its sharing asks for, and nothing else, in order:
# with the order's laws, each definition once, after its callees.
# Record: blend-copies-keep-their-name
law emit.defs:
  for xs: List<&2, U32>
  for +e: B.Ec
  for +b: B.Tb
  {B.order.put(xs, e, b) == B.defs.put(B.defs.of(xs, e), e, b) : B.Tb}

# LAW: and the names the check of names emitted twice examines are the
# names of those definitions, so that it checks what is written.
# Record: blend-copies-keep-their-name
law emit.names:
  for xs: List<&2, U32>
  for +e: B.Ec
  {B.names.all(xs, e) == B.defs.names(B.defs.of(xs, e), e) : List<&2, B.Nm>}
