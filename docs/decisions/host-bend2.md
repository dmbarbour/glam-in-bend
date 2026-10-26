# glam is implemented in Bend 2

`host-bend2` · maintainer · rev 9433be0

**Context.** The Rust bootstrap (github.com/dmbarbour/glam, 2026-02 to
2026-10) slowed under long compiles, concurrency bugs in its runtime and
collector, and regressions. Bend 2 is pure, affine and termination-checked;
it states laws that `bend PROOF.bend` enforces, checks fast, and compiles to
C or JS.

**Decision.** Reimplement glam in Bend 2 rather than port the Rust code. The
Rust repository and its implementation docs are reference, not
specification. The design docs and samples came over verbatim from Rust
glam 21912fc9 in 42da1ff and are edited here.

**Consequences.**
- glam cannot borrow Bend's evaluation: glam is untyped, lazy and shared,
  Bend typed, affine and eager. The assembler is an interpreter with its own
  value universe.
- Bend recursion must terminate, so evaluation and parsing are fuel-driven
  step machines over explicit state, never host recursion.
- Bend has only `Nat`, `U32` and `F32`; glam's exact rationals are built on
  `U32` limbs. Strings are character lists, bytes `List<U32>`.
- Foreign code serves IO effects only; any accelerator is pure Bend.
- Bend is young: pin its version, and be ready to report compiler issues
  upstream (github.com/bendlang/bend/issues). Keep a minimal reproduction of
  each issue we hit, and note any workaround beside the code it shapes.
