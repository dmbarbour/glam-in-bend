# A nested match's arrows may share its arm's line

`nested-arrows-share-an-arms-line` · maintainer · rev 79fd435

**Context.** An early parser split match arms by scanning, so it allowed
one `=>` on an arm's first line. Once a `{` after `with` delimited arms, a
later arrow on that line could only belong to a nested match. Carried over
from the Rust decision log (2026-10-17).

**Decision.** `P => match E as Q => R` nests a one-arm match in the outer
arm's result. A second arrow of one arm, as in `P => 1 => 2`, is still an
error.

**Consequences.** A linter may flag same-line nesting (Lints.md).

**Rule lives in:** Syntax.md, "Match".
