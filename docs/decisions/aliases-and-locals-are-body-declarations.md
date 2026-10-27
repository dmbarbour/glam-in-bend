# Aliases and locals are body declarations

`aliases-and-locals-are-body-declarations` · maintainer · rev 79fd435

**Context.** `as Name` in object and `extend` headers named a body's alias
outside the body, and helpers needing it leaked into results as members.
Carried over from the Rust decision log (2026-10-17).

**Decision.**
- `alias Name` may stand only as the first member of a `with` body (object,
  `extend` or update). Only `alias self` binds `self` and localizes the
  body's names: a bare `foo` is `self.foo`, and the host's names take
  `^name`. `alias _` leaves no way to reference the body. Objects default to
  `self`, updates to `_`; a module has `alias self` too.
- `using Dict` localizes as `alias self` does, hiding the host's locals
  behind `^`.
- `let` groups, as body members or file declarations, are private
  bindings, not entries of the result: each is recursive within itself and
  seen only by what follows it.
- `let` hinders extensibility by hiding logic, so it is not encouraged; a
  lint may flag it.

**Reasons.** In every scope, `foo` is a visible local or `self.foo`, and
each `^` steps out of the innermost `self`, which restores the intended
reading after drift.

**Consequences.** Headers lose `as Name`; `alias` is reserved. Shadowing
rules: `shadowing-is-an-error`.

**Rule lives in:** Syntax.md, "Objects", "Local Definitions" and "Using
Scopes".
