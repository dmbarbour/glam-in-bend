# Net Pairing — 2026-10-26

How copy fans pair, cheaply and provably: when two fans meet, annihilate
if they are residuals of one duplication, commute otherwise. **Drafted for
the maintainer's review before building.** The maintainer wants the GAL
adaptation early but is not yet confident in it, and asks whether Lean
could prove it, and prove that every reduction preserves polarity.

## Background

- **The rule** (Design.md, "Interaction Nets"): copy-copy joins the paired
  residuals of one duplication process and duplicates otherwise; pairing
  follows complete dynamic duplication identity, not equality of one
  permanent node identifier.
- **The Rust bootstrap** pairs by history: a fan's identity carries its
  complete dynamic duplication context, commutation extends it, and only
  identical identities annihilate. Its notes call this "a correctness
  reference, not Lamping's optimal bookkeeping", and warn that replacing
  it with brackets and croissants must replace identity construction and
  fan rules together, not just the comparison. Polarity preservation was
  checked at run time, in debug builds.
- **HVM5's labels** are static: a duplication meeting a superposition
  annihilates when their labels are equal and commutes otherwise
  (`dup_sup_if` in `demos/pure_hvm5_mini`). That is sound only where no two
  duplication processes meet under one label, which holds for some
  functions and not others.
- **GAL** (Gonthier, Abadi and Lévy, 1992) tracks levels to cheapen
  Lamping's algorithm. Adapting it to polarized nets would let a bind's
  auxiliary polarity stand in for the direction lambda terms provide.
- **No mechanized proof** of Lamping's algorithm or of GAL turned up
  (searched 2026-10-26): the proofs are on paper, through context semantics
  and the geometry of interaction.

## Steps

1. `pairing-polarity-law` — polarity preservation as a Bend law over our
   own rewrite rules: each rule maps a polarized redex to a polarized
   result. It is a finite case analysis over the rule table, checked on the
   implementation itself rather than a model. Needed by `spike-net-rules`.
   Built 2026-10-27 as `rules_polarized` in `spike/LAWS.bend`, over the
   rule table the spike's reducer interprets.
2. `pairing-histories` — the reference: fans carry complete duplication
   histories, as in the Rust bootstrap. Laws: commutation extends a
   history; annihilation happens only on identical histories. The spike
   runs on this.
   Tried 2026-10-27 in the spike (`spike-net-rules` has the numbers),
   once strict calls distribute over superposed arguments: extending both
   fans' histories on commutation, the Rust bootstrap's scheme, diverges
   on every Church exponentiation, `two two succ 0` included. That is
   wrong pairing, not growth. When an outer fan commutes through an inner
   one, the outer fan's residuals record a step their partner never
   takes, so where they meet they commute instead of annihilating, and
   the copies multiply. Extending only the inner fan is right wherever a
   test-specific oracle could name it: every `m n succ 0`, and
   `(\t -> t t) two`. Static labels are right on `m n` and diverge on
   self-application. The Rust bootstrap's tests cover single
   commutations, never a fan duplicating a function that holds fans.
   So histories are a correct reference only with a bit two meeting fans
   do not carry, which of them is inner: GAL's levels record it. Where
   live functions holding fans are duplicated, levels are needed for
   correctness, not only for constant-time pairing. glam's lowered code
   may avoid such nets (functions are data, instantiated per call),
   leaving user-built nets.
3. `pairing-labels` — where labels suffice: run workloads under both
   histories and labels, and report every fan pair they decide
   differently; characterize the functions that never differ.
4. `pairing-gal` — adapt GAL's levels to polarized nets, then test it
   against histories on generated nets, differentially.
5. `pairing-lean` — a time-boxed study in Lean 4. Formalize polarized nets
   and their rules, prove polarity preservation as a warm-up, then state
   the adaptation's correctness as levels pairing fans exactly when
   histories do, on every net reachable from a well-formed construction.
   Attempt it, or find the restriction under which it holds.
6. `pairing-verdict` — choose how each kind of net pairs (labels, levels,
   histories), and record it.

## Feasibility (assessed 2026-10-26)

- **Polarity preservation** is local: each rule is checked alone, and the
  rewiring lemma is short. Days at most in Lean, and doable as a Bend law
  on the real rules, which is the stronger guarantee.
- **The GAL adaptation's correctness** is research. Proving it from context
  semantics would mean mechanizing what took the literature a book. Stated
  instead as a simulation of the history reference ("equal levels exactly
  when equal histories", an invariant over reachable nets), it reduces to
  rule-by-rule preservation of that invariant: still likely weeks, and the
  invariant may hold only for a class of nets. Learning that class is
  itself useful, since histories remain the fallback beyond it.
- Differential testing comes first: cheap evidence before a proof
  investment.

## Open questions

- Lean in the devcontainer, if `pairing-lean` proceeds; Mathlib only if
  the formalization needs it.
- Proofs in Lean about a model, or Bend laws about the implementation?
  Polarity can be both; GAL's invariant may be practical only in Lean.
