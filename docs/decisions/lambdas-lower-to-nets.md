# The lambda calculus is evaluated by lowering to interaction nets

`lambdas-lower-to-nets` · maintainer · rev a4acbdc

**Context.** glam's toplevel semantics is a lazy, untyped lambda calculus,
and interaction nets are also a feature users reach through
`interaction_net` (Design.md, "Interaction Nets"). The standing docs read
two ways on how the lambda calculus itself is evaluated: as a lazy
machine of its own, nets a performance tool behind lambda-style
interfaces ("Initially, we'll mostly use interaction nets as a
performance tool for difficult dataflows"), or through nets ("Lambda
calculus becomes a design pattern within interaction nets"). The spike
took the second reading (EvalSpike), as the Rust bootstrap had, and the
direction review asked which was meant
(`docs/reviews/Direction_2026-11-09.md`, F9).

**Decision.** The maintainer (2026-11-09): the intention is to lower
lambdas to nets for evaluation. Every lowered term runs on the kernel's
nets; a lazy machine over thunks is not the toplevel's evaluator.

**Consequences.**
- Pairing must be right for every lowered term, not only for user nets:
  NetPairing's verdict decides for glam's code, and `spike-lowering` is on
  the critical path, since it shows which nets lowering makes.
- Laziness, sharing and fixpoints are net matters: cells hold nets
  (HeapModel), a function is a net with its arity
  (`functions-are-nets-with-arity`), a thunk a net waiting at its
  interface.
- The kernel is the evaluator, in more than one form: most likely a lazy
  one for ordinary evaluation and an eager one for a JIT (the maintainer,
  2026-11-09, a leaning; `spike-verdict` records the ruling).
- The sentence in Design.md about nets as a performance tool describes
  what users write, not how the assembler evaluates; DistilledDesign's
  "interaction nets ... available for performance-critical dataflow" is
  read the same way.

**Rule lives in:** `docs/Design.md`, Interaction Nets ("Lambda calculus
becomes a design pattern within interaction nets").
