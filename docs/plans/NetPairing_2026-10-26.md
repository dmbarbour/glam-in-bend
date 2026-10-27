# Net Pairing — 2026-10-26

How copy fans pair, cheaply and provably: when two fans meet, annihilate
if they are residuals of one duplication, commute otherwise. Approved by
the maintainer 2026-10-27 and put ahead of EvalSpike's remaining steps:
pairing by duplication histories, the Rust bootstrap's scheme, turned out
wrong (`pairing-histories`), so this is a bug there too. The maintainer
wants the GAL adaptation tested amply, then proved, in Lean if it can be;
they hold an earlier design discussion of it, to compare with a
derivation made here first.

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
   leaving user-built nets. Retired as the reference: the spike pairs by
   static labels since 2026-10-27, its history code removed.
3. `pairing-trace` — reduction made inspectable: a run logs each
   interaction as the reducer met it, and lists the live net at any step.
   Built 2026-10-27 (`spike/trace.bend`, over `reduce_log` in
   `spike/net.bend`, which shares the reducer's interaction function).
   On `(\t -> t t) two` it shows the failure at interaction 12: the two
   copies of `two` carry one label, so one copy's fan joins the other's
   partner; a call then distributes around the ring of merges that join
   made, without end. Since: nodes are named by serial number, never
   reused, and each interaction lists the nodes it made; a window prints
   only the interactions from a given one on; the net's listing counts
   node kinds (`spike/tracelib.bend`). `spike/tools/terms.py` lowers
   lambda terms to nets as optimal reduction does (a live function per
   lambda, a copy per extra use of a variable), evaluates each term
   directly for the value its net must reach, and writes a Bend program
   that tests the terms or traces one; it also generates random numeral
   expressions.
4. `pairing-labels` — where labels suffice. The spike's scheme meanwhile:
   one label per lowering site and instantiation. Right on `m n succ 0`
   for distinct numerals; wrong on self-application, where two copies of
   one duplication meet under one label. Of 60 random numeral
   expressions (`terms.py gen`, seed 7), 49 reduce to their value and 11
   do not, every one of them a self-application (`self`, `\x. pow x x`,
   `\n. n n`): some diverge, some halt with no value. Characterize the
   nets that never meet so, and whether lowering can guarantee it.
5. `pairing-gal-derive` — derive a level discipline for polarized nets:
   what a level means without lambda terms' boxes, which nodes carry one,
   how levels change (brackets and croissants or GAL's simplification),
   and the rules. Derived here independently, then compared with the
   maintainer's earlier discussion (summarized in the Rust bootstrap's
   NetPolarityChecker plan, "Background: polarity, GAL, and Lafont").
6. `pairing-gal` — build levels in the spike and test them amply: the
   numeral and self-application nets, then generated lambda terms checked
   against a direct evaluator of the same terms, traced where they differ.
7. `pairing-lean` — after that testing, a time-boxed study in Lean 4.
   Formalize polarized nets and their rules, prove polarity preservation
   as a warm-up, then state the adaptation's correctness: a net built from
   a term reduces to the term's normal form, read back. Attempt it, or
   find the restriction under which it holds.
8. `pairing-verdict` — choose how each kind of net pairs (labels, levels),
   and record it.
9. `pairing-docs` — revise the standing docs to the verdict. Design.md's
   copy-copy rule says pairing follows complete dynamic duplication
   identity and that duplication history distinguishes residual fans;
   histories pair wrongly, so say what does, and check the other docs for
   the same claim.

## Feasibility (assessed 2026-10-26)

- **Polarity preservation** is local: each rule is checked alone, and the
  rewiring lemma is short. Days at most in Lean, and doable as a Bend law
  on the real rules, which is the stronger guarantee.
- **The GAL adaptation's correctness** is research. Proving it from context
  semantics would mean mechanizing what took the literature a book. With
  no correct local reference to simulate (histories pair wrongly), the
  statement is against the lambda calculus itself, which makes it harder:
  likely weeks, and it may hold only for a class of nets. Learning that
  class is itself useful.
- Testing comes first: cheap evidence before a proof investment.

## Open questions

- Lean in the devcontainer, if `pairing-lean` proceeds; Mathlib only if
  the formalization needs it.
- Proofs in Lean about a model, or Bend laws about the implementation?
  Polarity can be both; GAL's invariant may be practical only in Lean.
