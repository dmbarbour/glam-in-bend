# Lambdas are a front-end concept, lowered to nets; the core has none

`lambdas-lower-to-nets` · maintainer · rev b1d0be5

**Context.** glam's toplevel semantics, as a `.g` programmer sees it, is a
lazy, untyped lambda calculus, and interaction nets are also a feature
users reach through `interaction_net` (Design.md, "Interaction Nets").
The standing docs read two ways on how the lambda calculus is evaluated:
as a lazy machine of its own, nets a performance tool behind lambda-style
interfaces, or through nets ("Lambda calculus becomes a design pattern
within interaction nets"). The spike took the second reading
(EvalSpike), as the Rust bootstrap had, and the direction review asked
which was meant (`docs/reviews/Direction_2026-11-09.md`, F9). The Rust
bootstrap also made lambdas part of its core, for a convenient start,
and took a week to disentangle and undo that.

**Decision.** The maintainer (2026-11-09): lambdas are a `.g` compiler
concept, a front end's, lowered through `interaction_net` at compile
time. The core has no lambda: it evaluates nets over the kernel's data
types, and a lambda is never presented as a core data type. The `.g`
front end lowers a lambda, an application, a `let`, a `where` to the
net construction `interaction_net` gives every user (`.bind`, `.copy`,
`.data`, `.wire`), as glam code could.

**Consequences.**
- No lambda term type in the core, and no evaluator of lambda terms: the
  front end's output is net construction and data.
- Pairing must be right for every net the front end makes, not only for
  user nets: NetPairing's verdict decides for `.g`'s own code, and
  `spike-lowering` is on the critical path, since it shows which nets
  the front end makes.
- Laziness, sharing and fixpoints are net matters: cells hold nets
  (HeapModel), a function is a net with its arity
  (`functions-are-nets-with-arity`), a thunk a net waiting at its
  interface.
- The kernel's data types (lists, dicts, numbers, texts) are built to be
  adopted directly into the final evaluator: a matured model of them is
  not throwaway, though reaching maturity may throw a lot away (the
  maintainer, 2026-11-09).
- The kernel is the evaluator, in more than one form: most likely a lazy
  one for ordinary evaluation and an eager one for a JIT (the maintainer,
  2026-11-09, a leaning; `spike-verdict` records the ruling).
- Design.md's sentence about nets as a performance tool describes what
  users write by hand, not how the assembler evaluates; DistilledDesign's
  "interaction nets ... available for performance-critical dataflow" is
  read the same way.

**Rule lives in:** `docs/Design.md`, Interaction Nets ("Lambda calculus
becomes a design pattern within interaction nets").
