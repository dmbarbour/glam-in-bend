# `::=` is disabled

`prior-update-disabled` · maintainer · rev 42da1ff

**Context.** `name ::= \prior -> Expr` was the non-observing update: it
passed the prior definition without asserting one existed. The Rust side
since eliminated the undefined value: reading what is undefined is an error,
and `{}` is a value like any other. That leaves `::=` nothing to pass where
the name is undefined, so it needs a redesign to stay.

**Decision.** Disable `::=` for now. The token stays reserved, and a
definition using it is a compile error saying it is disabled.

**Consequences.**
- An update is `name := Expr` with `_name`, which asserts the prior exists.
- A write that may introduce or replace, as at an expression path inside
  `with`, uses `dict.insert`.
- Samples using `::=` are rewritten, and docs mark it disabled.
