# `::=` is disabled

`prior-update-disabled` · maintainer · rev 9433be0

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
- Samples that exist for `::=` are removed: `hello/hello_update.g`, and the
  `::=` line of `syntax/definitions.g`. Docs mark it disabled.
