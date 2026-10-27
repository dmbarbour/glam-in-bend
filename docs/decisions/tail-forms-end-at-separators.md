# Tail forms run to the end of their region, which separators end

`tail-forms-end-at-separators` · maintainer · rev 79fd435

**Context.** An earlier rule let only a closer, a separator or a line end
follow a tail form (prefix `if` and `try`, `match`, `do`, lambdas, `let`,
`using`, `object`). That rejected forms with one valid reading, such as
`if a then if b then c else d else e`. Carried over from the Rust decision
log (2026-10-16).

**Decision.** A tail form runs to the end of its region. A region ends at a
closer, `,` or `;`, the end of its statement, or a separator keyword, one
no expression continues with: `then`, `else`, `in`, `where`, `=>`, `=>?`,
and a binding's or view's `->`. A tail form never ends at a token that
could continue it, such as an `and` between guard clauses. A tail form is
never an application's argument.

**Reasons.** Parentheses only where a reader could misread the form; a
linter, not the grammar, flags what parses but reads poorly.

**Consequences.** Nested inline `if`s and a conditional or lambda before a
binding's `->` are legal; a linter may flag them (Lints.md).

**Rule lives in:** Syntax.md, "Tail Position".
