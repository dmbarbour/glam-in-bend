# Proving in Bend

What the laws and proofs written so far have taught, generic across proof
files. Bend's own shortfalls, with their upstream issues, are in
[BendIssues.md](BendIssues.md); a proof file records in its header what
it alone taught. Add to this file what a new proof teaches.

## What to claim

- **The guarantees a user sees first**: what is emitted, kept or refused.
- **A weaker law, and its missing pieces.** A full claim can cost far more
  than it buys. It is often enough to prove that each step keeps some
  property under a reasonable precondition, then prove the precondition,
  or broaden it where that is not too hard. When you weaken a law, list
  what it no longer claims, and the separate laws that would bring it
  close enough, in the plan beside the law. A law that an order is
  callee-first wants laws that the order loses and duplicates nothing; a
  law that every item receives a disposition wants a law that every
  disposition is carried out (where no error is reported).
- **Confidence, not only cheapness.** A guard that makes a law hold by
  computation (AGENTS.md, Laws) is a fine shape, but prove too that the
  guard never fires where it should not, or say plainly that the law does
  not claim it. Once a stronger law proves a guard never fires, the guard
  is redundant work, not a boundary: remove it, and prove its law from
  the stronger one.
- **Termination where feasible.** A walk bounded by fuel can carry a law
  that a walk cut short reports an error; a proof that the fuel suffices
  is stronger, and often feasible by a potential (below). Try it before
  settling for the weaker law.
- **Mutate the code after a proof passes**: break what the law is about
  in a copy, and see the proofs fail. A law that survives the mutation
  claims less than meant. Keep the mutations in a `MUTANTS.txt` beside
  the proof file, each naming the laws it should fail, and try them with
  `scripts/one_law.py` (below) when the proof or its code changes.

## Shaping the code a law follows

- **Test values; do not match literals.** A `U32` is a word of bits to
  Bend's proofs, so a match on literals (`case 46:` ... `case _:`)
  leaves the `_` case a word partly known, on which the function's own
  match is stuck. Test (`U32.is_eq(h, 46)`) and branch on the `Bool`.
- **A class of values is a datatype**, its tests `Bool`s: constructors
  match in proofs, literals do not.
- **Branch in a named helper matching its `Bool` parameters**
  (`f.k(+test: Bool, ...)`), the tests computed by its caller, so that a
  lemma about the helper splits the `Bool`s without restating lambdas,
  which Bend does not infer. A `when` with lambdas serves too, at the
  cost of a helper def in the proof file mirroring them.
- **A result read twice is a datatype read by projections**, not
  destructured in a lambda (`on.r(r, a => b => ...)`), which sticks a
  proof until the result reduces.
- **State whose invariant holds by computation**: then the law costs a
  case split per step.

## Writing proofs

- **A recursive proof never matches a computed value.** A non-recursive
  step lemma takes the `Bool` as a parameter, an equation tying it to its
  test, and every induction hypothesis the cases need, and splits it; the
  recursion stays in the caller, Bend having no mutual recursion.
- **`%e : P` rewrites with `e : {a == b}`**: the goal is `P` with `b`
  where `_` stands, and becomes `P` with `a`. State lemmas so that `a` is
  the simple form and `b` the complex one, so that a rewrite turns the
  complex form in a goal into the simple; wrap a lemma that runs the
  other way in `Equal.sym` once: `Equal.sym(T, a, b, e)` takes
  `e : {a == b}` and gives `{b == a}`.
- **Mark what a proof reuses**: `+` on a law's `for` binders, a proof's
  parameters and its patterns (`case Con{+h, +t}`, `case 1n+(+k)`).
- **An absurd case names its type**: `Empty.absurd(T, e)`, `T` written
  out; refute a clash of constructors through a motive sending one to
  `Unit` and the other to `Empty`.
- **A big constant is reasoned under a variable** `N` with
  `{N == Nat.pow(2n, 32n)}`, the power met only against a symbolic value
  or where both forms match exactly (BendIssues.md, "Big constants in
  proofs").
- **A proof function is used once.** A function cannot be `+`-marked, so
  a lemma taking one (`@x:A -> P(x)`, Bend's dependent function) cannot
  both use it and pass it on. State a reusable fact as a `Bool`
  equation instead (containment as `all.in(xs, ys) == True`), and keep
  function arguments to a case split, each branch used once
  (`or_cases(a, b, c, h, fa, fb)`).
- **Several invariants as one `Bool`**: a conjunction `inv(s) == True`,
  with a lemma building it from its parts and one taking each part out
  (the hub's `eq_true_of_and_left`, `eq_true_of_and_right`), so that a
  step lemma takes and returns one equation.
- **Termination by a potential**: a `Nat` the state determines, what is
  left to do each counted by what it will cost, that each step lowers by
  one at least, under an invariant the steps keep. Give the walk that
  potential at the start as its fuel, and prove by induction on the fuel,
  from `le(pot(s), n)`, that it finishes: at `0n` the potential's being
  positive refutes the unfinished states. Over-approximate where exact
  costs more: a list of candidates, duplicates and all, each counted
  while not yet done, only overcounts, and makes a step's descent a lemma
  on one removal.
- **Templates prove as code does**: a proof def may take `~p`, and
  template parameters come first.
- **Lemmas on the hub**: the package `0x8ae61ec3a6615abd35f196c07232ad28`
  (bend-mathlib) proves lists, `U32`, `Nat`, `Bool` and equality
  (`list.bend`, `u32.bend`, `nat.bend`, `bool.bend`, `equal.bend`).
- **Find a failing lemma by bisecting** the proof file into prefixes,
  each its own file, checked in turn: Bend reports the first failure, or
  only that its stack overflowed.
- **Check one law at a time**: Bend reports only the first failure,
  often of an earlier law a mutation breaks too, and a whole proof file
  is slow to recheck while one law is being written.
  `python3 -I scripts/one_law.py PROOF LAW` checks a copy cut to the law,
  its proof and the defs it reaches; with `--mutants FILE`, the copy
  unmutated and then each mutation naming the law, each expected to fail
  it, and where.
