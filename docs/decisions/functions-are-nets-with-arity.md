# A function is a net and its remaining arity

`functions-are-nets-with-arity` · maintainer · rev e7899c5

**Context.** The architecture sketch first modeled a function as a closed
template plus captured values, instantiated afresh at each application. That
loses work: whatever a partial application has reduced would be redone by
every copy.

**Decision.** A function value is a net plus its remaining arity, as in the
Rust bootstrap. Applying it copies the net logically, and a pair that reduces
in the source net reduces once there, for every copy. Partial application
binds an argument into the net and yields a function of one less arity.

**Consequences.**
- A function's net is shared, mutable and must be reclaimed, like a lazy
  value: both need the shared store the sketch's "The store" section weighs.
- glam nets are interpreted by glam-in-bend. Bend 2 has no net runtime to
  target, and glam's rules (polarity, copy-copy pairing by duplication
  identity) differ from HVM's; compiling a net to Bend code is at most a
  narrow JIT opportunity.
