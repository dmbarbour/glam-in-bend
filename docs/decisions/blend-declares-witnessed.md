# A typed declaration is checked by a witness Bend checks

`blend-declares-witnessed` · maintainer · rev c4d2f09

**Context.** `declare foo` said only that a concrete family must define
`foo`, with no way to say its type, while types may be overridden (the
maintainer, 2026-11-04, `blend-typed-declares`). Blend has no type
checker and adds no Bend logic of its own (`blend-adds-no-bend-logic`).

**Decision.** As planned with the maintainer:
1. `declare def push(st: S(), +x: U32) -> S()`, a header with no body,
   or `declare push(...) -> S()` for short, as `upd` alone is for
   `upd def`; `declare type S: Data`, its kind stated; an untyped
   `declare after` as before.
2. The signature is bound in each concrete object against its own final
   types, so that an overridden type flows into it (Haskell's class
   methods over associated types, Rust's trait methods over `Self::S`),
   fixed where first made: a second declaration of the name below is an
   error, the families varying through their type members.
3. Bend checks it: for each concrete object a witness,
   `def Listed.push.as_declared(st: Blend_0.Listed.S(), +x: U32) ->
   Blend_0.Listed.S(): Blend_0.Listed.push(st, x)`, or for a kind
   `def Listed.S.as_declared() -> Data: Blend_0.Listed.S()`, its marker
   naming the declaration, in the module's proofs' file beside its code
   (`blend-proofs-beside-code`), never in the program: a witness is a
   second caller, which would make Bend split the definition into a
   segment of its own. `--verdict` accepts a witness as any total def
   (tried 2026-11-05).

**Consequences.**
- A misfit is Bend's error at the witness, expected and observed types
  printed, found by the gate's proof step; the samples Blend emits and
  Bend refuses live in `blend/samples/refused/`, held to Bend's output.
- A module with witnesses and no laws writes its proofs' file alone.
- The samples `declares`, `declare-twice`, `declare-no-type`,
  `declare-misfit`, `declare-kind`.

**Rule lives in:** `blend/README.md`, The model.
