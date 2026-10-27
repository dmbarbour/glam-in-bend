# Dict literals introduce their members in order

`dict-literals-introduce-in-order` · maintainer · rev 79fd435

**Context.** A dict literal was once the hierarchical union of its items,
merging dicts at shared keys recursively, which forced both. Carried over
from the Rust decision log (2026-10-24).

**Decision.** A literal introduces its members in written order, the
inverse of a dict pattern's takes. A tag member `path:V` introduces `V` at
`path`, an error where defined, creating the dicts on the way. An optional
member `path?:L` introduces `V` where `L` is `[V]` and nothing where `[]`.
Any other member is a dict whose keys join the root, each new, so
`{D1, D2}` is a shallow union. Order is the writer's, never sorted: the
compiler reports conflicts it sees and suggests the order.

**Reasons.** Symmetry with patterns: what a literal introduces, the same
pattern written deepest first takes back. Insertion knows a conflict from
keys, never values, where deep merges forced values and hid conflicts.

**Rule lives in:** Syntax.md, "Dicts".
