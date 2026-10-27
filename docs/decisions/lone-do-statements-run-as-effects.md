# A lone `do` statement still runs as an effect

`lone-do-statements-run-as-effects` · maintainer · rev 79fd435

**Context.** A `do` block with only a final statement once lowered to that
expression, so `do 42` was `42`, and nothing checked that the final
statement expressed an effect. Carried over from the Rust decision log
(2026-10-17).

**Decision.** A lone statement lowers as `.r () >>= \_ -> X`. For an effect
that is `X` by left identity; anything else fails when the block runs.

**Reasons.** Asserting that a value is an effect belongs to a typechecker
or an annotation; this lowering stands in until one exists.

**Consequences.** A linter may flag a redundant `do X` (Lints.md).

**Rule lives in:** Syntax.md, "Effects".
