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
- **State a law over what the program builds, by the names it calls.**
  A law should hold however it is proved: `A -> B` by `not A`, by `B`,
  or by `not (A and not B)` (the maintainer, 2026-11-07). A guard ("where
  no error is reported", an arm true where a step fails) must not stand
  in for a premise the law leaves out, such as that a state is one the
  program builds: then a guard proved dead cannot go without the law
  turning false (`heap-laws-align.contract-none`; Blend's
  `copies.defined`). Check the domain both ways: broader than the
  program builds forces defensive code; narrower says nothing of a real
  case (`heap-laws-align.statics`). And name the construction by the
  function the program itself calls, never a copy of its body: a law
  over a copy proves the copy, and a fault in the program's wiring
  survives it (`heap-laws-align.named`).
- **Termination where feasible.** A walk bounded by fuel can carry a law
  that a walk cut short reports an error; a proof that the fuel suffices
  is stronger, and often feasible by a potential (below). Try it before
  settling for the weaker law.
- **Mutate the code after a proof passes**: break what the law is about
  in a copy, and see the proofs fail, by a refutation: a mutant that
  only overflows the checker's stack (`RangeError: Maximum call stack
  size exceeded`) is not caught, its run ending with no verdict, and no
  stack setting lets the report finish (`ulimit -s`, Bun's JSC options).
  `scripts/one_law.py` reports such a run as a crash. Where a mutated
  proof crashes so, as the `raise_*` laws' do while reporting a mismatch
  over symbolic words, give the mutation a witness: the law's statement
  at a small instance, proved by `{==}`, which checks unmutated (so the
  instance meets the premises left out) and is refuted mutated. A
  witness is the stronger evidence: it shows the statement excludes the
  fault, however the proof is built. A law that survives the mutation
  claims less than meant. Keep the mutations in a `MUTANTS.txt` beside
  the proof file (`X_MUTANTS.txt` beside `X_PROOF.bend`), each naming the
  laws it should fail: the gate tries each against them
  (`scripts/one_law.py`, below), its pass kept while its inputs are
  unchanged.

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
- **A goal holding a big constant changes only by a rewrite under a
  hole.** Where two forms must be reconciled by conversion (`lift_lvl`
  against the arm it reduces to, `lvl_of(PLvl{j})` against `j`), the
  checker normalizes the whole type, the power with it, and overflows its
  stack. State each such step as an equation proved by `{==}` in a lemma
  where no power appears (`lift_unfold`, `lvl_cast` in
  `spike/PROOF.bend`), and rewrite with it, the rest of the goal matching
  exactly.
- **A closed fact between big values enters as a `U32` comparison.** Prove
  the lemma over variables (`ne_lt`) and pass the closed fact as
  `{U32.is_lt(2147483648, V.nolvl()) == True}`, checked by `{==}` on the
  words. Stated between their `Nat` values, 2^31 below 2^32 - 1, it
  exhausted the checker's memory.
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
  on one removal. But an overcount can make the fuel superlinear, and a
  walk run to its fuel pays all of it: count each item once by its
  index where an index exists, the index of a `U32` its `U32.to_nat`
  (the hub's `u32_is_eq_to_nat` ties `U32.is_eq` to it), and the
  potential needs no invariant naming the candidates.
- **Prove a fast version against a proved one.** Where a state's lists
  must become lookups, keep the proved code as the specification and
  run a version beside it that adds its indexes, then prove one law:
  dropping the indexes, its result is the specification's. Lift a
  specification state with the indexes its lists make; show that a step
  from a lifted state is the lifted step, for every state, no
  hypothesis; induct on the fuel. An index whose shape is a function of
  its set (a trie on a key's bits) makes the lift a computation, the
  lists' order aside: prove that putting commutes.
- **A trie on a `U32`'s own word** (`U32{Word(32n)}`, the lowest bit
  first) is structural all the way down: a lookup and a put recurse on
  the word, and `Word.cmp`'s last step splits into the tails and the
  bits, so that no arithmetic, and no bound of 2^32, is met. A table by
  position is the same trie over a list split by its positions' bits:
  `List.get(xs, double(i))` and `List.get(xs, 1+double(i))`.
- **A specification sharing the decisions**: where a law pins an
  optimization, write the specification beside the code to share every
  function the optimization left alone, so that the law claims what
  changed and no more, and list what the shared functions decide among
  its missing pieces.
- **A law's proof may call another law's** (`Laws.x(...)`, typed by its
  law), so that a law for the case the tool meets composes the general
  law with the laws of what feeds it.
- **Induct with the accumulator a definition has**: a list reversed
  onto an accumulator (`List.reverse.go(rest, q)`) steps by computation
  (`reverse.go(Con{x, r}, q)` is `reverse.go(r, Con{x, q})`), where the
  reversal of an append wants lemmas.
- **A rewrite is a local statement**: no `match` may follow it. Match
  first, then rewrite in each branch.
- **Templates prove as code does**: a proof def may take `~p`, and
  template parameters come first.
- **A linear value a proof names often is mirrored as data.** A goal
  over an `Array` (a `Type`) may name it once only in a proof's terms,
  where a rewrite and a law's arguments want it several times. Take it
  erased (`-w`) in a helper with its mirror, a tree that is `Data` and an
  equation back (lawful-arrays' `Mirror`, `mirror`, `fromT`), rewrite
  the goal onto the tree's array with that equation, and name
  `fromT(t)` as often as needed; the law's def passes the array to the
  erased parameter and to `mirror` (`rd_wr_same.go` in
  `spike/PROOF.bend`).
- **A function destructuring a pair reduces once the pair is a
  literal**: rewrite `Array.get(...)` with the law that gives it as
  `(a, snd(...))` (lawful-arrays' `get_pair`) under a hole at the
  destructuring function (`P.rd.fin(KM.m_get.fin(_), a)`), and the goal
  reduces to the array law's own.
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
