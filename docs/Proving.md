# Proving in Bend

What the laws and proofs written so far have taught, generic across proof
files. Bend's own shortfalls, with their upstream issues, are in
[BendIssues.md](BendIssues.md); a proof file records in its header what
it alone taught. Add to this file what a new proof teaches.

## What to claim

- **Prove what is important, and what is easy** (the maintainer,
  2026-11-22: "prove what's important (whether for correctness or
  performance) and prove what's easy"): a law earns its place by what
  it protects or by what little it costs.
- **A law rather than a test** for such a property (`laws-over-tests`,
  the maintainer, 2026-11-23): a test stays where no law can yet say it,
  and for what it measures; a run-time check added meanwhile names the
  law meant to replace it.
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
- **Scaffolding, named** (`laws-across-steps-iterative`): what a law
  cannot yet show, such as an invariant across the kernel's steps,
  stands as a premise only with what discharges it named in the law's
  comment and a plan step owning the discharge.
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
- **A law that a function commutes with another does not pin it.**
  `raise_lift_drop` says a drop commutes with raising a level, and an
  unclamped drop commutes too: the mutation that removed the clamp left
  the law true, its proof alone broken (measured by a witness, 2026-11-18).
  Claim what a function computes against a model (`lift_lvl_drop`,
  `CT.drop`), and let the commutation laws claim the commuting.
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
  over symbolic words, give the mutation a witness: the law at a small
  instance, a term for each of its binders (`NAME = TERM`, a premise
  left out proved by `{==}`). `scripts/one_law.py` writes from the
  law's own text a def per binder and the conclusion last, so that the
  premises checked are the law's, and asks them all to check unmutated
  and, mutated, the premises to hold and the conclusion to be refuted:
  the mutated code then a counterexample. A witness is the stronger
  evidence: it shows the statement excludes the fault, however the
  proof is built. A mutation counted caught by its proof shows only
  that the proof broke: one that changes the steps a proof follows
  breaks it even where the law stays true of the mutated code (an
  unlink that also clears its predecessor's position breaks
  `join_keeps`'s proof, which allows that word;
  `docs/reviews/JoinLaws_2026-11-14.md`, F1). So a mutation with a
  witness is caught by its witness alone, which the tool runs every
  time, a broken proof beside a witness that holds reported not
  caught. A witness whose mutated code walks out a fuel far past the
  instance (the climb's million steps) does not finish in the checker
  within fifteen minutes: run the code on the same instance instead,
  the premises still checked by `{==}`; a walk fuelled by the heap's
  size runs out within the instance's words. A witness's heap may be
  built, not spelled: by the kernel's own writes and named references
  (`glam/witness.bend`, a face by `P.link`, a reference by `KMd.ref`),
  so that it follows a change of encoding; but only by code no mutation
  in its file touches, since a heap built by the mutated function
  changes with it (a ring built by `R.cursor`, under a mutation of the
  cursor). A proof file whose witnesses build so imports the builders,
  since a witness sees the proof file's imports but its laws' and
  proofs' (`glam/SERVE_PROOF.bend` imports `glam/witness.bend`). A
  witness must leave something for the fault to break: a ring exact
  after the served cursor leaves holds of a lone `s` whatever the leave
  wrote elsewhere, so the witness of `serve_map_unwritten` keeps a
  second cursor in the ring, its word 3 where the stale root sends the
  write. A mutation that widens a premise's predicate has no witness:
  an instance that breaks the law fails the premise unmutated
  (`range_doubled`, `glam/LOOP_MUTANTS.txt`), so its proof is the only
  catch. A law that survives the mutation claims less than meant. A law
  that only regroups facts over an append (`lx_extend`), each a premise
  or a per-node fold, survives every mutation of the folds, premise and
  conclusion changing alike: say so where it is planned rather than
  invent a mutant. Keep the mutations in a `MUTANTS.txt` beside
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
  Where each arm's hypothesis needs terms only that arm computes (a
  mirror destructured, a list matched), the recursion itself may take
  the `Bool` as a parameter with its equation, `+e: Bool, +he: {e ==
  f(ts)}`, declared before every binder matched after it: match the
  list, then `e`, then the rest; in each arm rewrite the goal with `he`
  (`%he`, its `Bool` first so that the test turns into the constant)
  after the matches; the recursive call passes `f(rest)` and `{==}`
  (`glam/SPLICE_PROOF.bend`'s `nodes_go`, an eraser making no node).
- **`%e : P` rewrites with `e : {a == b}`**: the goal is `P` with `b`
  where `_` stands, and becomes `P` with `a`. State lemmas so that `a` is
  the simple form and `b` the complex one, so that a rewrite turns the
  complex form in a goal into the simple; wrap a lemma that runs the
  other way in `Equal.sym` once: `Equal.sym(T, a, b, e)` takes
  `e : {a == b}` and gives `{b == a}`.
- **Mark what a proof reuses**: `+` on a law's `for` binders, a proof's
  parameters and its patterns (`case Con{+h, +t}`, `case 1n+(+k)`). A
  pattern's variable used twice wants its matched parameter marked:
  `case 1n+r` of a `p` without `+`, `r` passed twice, fails at `r`
  with no goal named (`above_add` in `spike/PROOF.bend`, 2026-11-22).
- **A name already defined fails at the second definition's name**, the
  report saying nothing more: search the proof file before naming a
  lemma (`above_succ`, taken, 2026-11-22).
- **An absurd case names its type**: `Empty.absurd(T, e)`, `T` written
  out; refute a clash of constructors through a motive sending one to
  `Unit` and the other to `Empty`.
- **Two functions of one body do not convert**, nor does `x + 0` for
  a U32 x: `RG.pl.of(m)` against `KMd.word.m(m)` wants a lemma matching
  `m`, and `x + 0` the sum's value through `U32.to_nat`
  (`glam/SERVE_PROOF.bend`'s `plof`, `u32_add0`). A function without a
  match (`KMd.nw`, `RG.nw`) unfolds and converts.
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
- **A recursive definition reads its arguments left to right**: each
  passed unchanged until one shrinks, so put the list that shrinks
  before any argument that changes (`RG.chain(v, d, ys, a, b)`, not
  `chain(v, d, a, ys, b)`).
- **A rewrite is a local statement**: no `match` may follow it, nor may
  one follow a let (`+h = ...`). Match
  first, then rewrite in each branch. A pair destructured (`(+t, +e) =
  m`, a mirror) is a match: it too goes before every let.
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
  `spike/PROOF.bend`). An erased array named in a proof's terms without
  its mirror fails with an error naming the definition and nothing more
  (`cr_map` in `glam/SERVE_PROOF.bend`, 2026-11-20).
- **Lessons learned on the ring's proofs keep their names.** The
  ring's laws and proofs retired with it (2026-11-23,
  `cells-freeze.sharing.cursors.index.ring.retire`); lemmas the lessons
  below name from them (`crs.go`, `crfi.go`, `crl_keeps.m`,
  `serve_exact.m`, `cursor_keeps.m`, `join_keeps.go`, `join_exact.m`)
  are in git before ebc5887.
- **A fold's twin is derived from its text.** Where a new conclusion
  follows the same recursion as a proved fold, the generator reads the
  fold from its proof file, swaps the goal (a call matched by its
  arguments, not by a pattern over the text) and adds the step lemma's
  let, so that the twin keeps every rewrite the original needed: `crfi.go`
  from `crs.go`, and `crl_keeps.m` from `serve_exact.m`'s lets, both
  checked on the first run (`glam/SERVE_PROOF.bend`, 2026-11-21). Choose
  the fold whose model matches the conclusion's: `crk.go` and `crs.go`
  recurse alike over the crossings, but only `crs.go` follows `RG.cr`,
  which finds positions through a fixed view.
- **A function destructuring a pair reduces once the pair is a
  literal**: rewrite `Array.get(...)` with the law that gives it as
  `(a, snd(...))` (lawful-arrays' `get_pair`) under a hole at the
  destructuring function (`P.rd.fin(KM.m_get.fin(_), a)`), and the goal
  reduces to the array law's own.
- **A chain of steps composes through each step's parts.** Laws over a
  heap are stated on its parts (`P.H{KM.MG{w}, a}`); a step's result is
  not syntactically so. Give each step a lemma restating its result in
  parts, `P.H{KM.MG{words(op(h))}, a} == op(h)`, and rewrite the chain
  from the inside out, so that each next law applies with `w` the
  previous step's `words(...)`; take that `w` erased with its mirror, so
  that the composition names it freely, and each term grows by one step,
  not by the copies a step's explicit words would make (`join_keeps.go`
  in `glam/PROOF.bend`, five steps, checked in seconds). One lemma over
  a heap variable restates any heap in its parts (`heta`: match the
  heap, then its memory, `P.H{KM.MG{words(h)}, vals(h)} == h`), which
  replaces a parts lemma per operation (`glam/SPLICE_PROOF.bend`; the
  per-operation ones of `glam/PROOF.bend` came before it).
- **A step that branches before a common operation is put in one form
  first.** The node pass's step is an error counted, a value put or
  nothing, then a pop: one lemma matching the template node rewrites it
  as `P.node(pre, header, payload)` (`nf`), and each fact of the pop is
  proved of that form once; the branches stay only where the form's
  parts differ (`pre_rd`, `pre_full`).
- **Cite another proof file's laws with its proofs.** A file importing a
  `LAWS.bend` alone owes every law there a proof (Bend counted spike's
  101 as TODOs); import its `PROOF.bend` beside it, as glam's proofs do
  the hub's (`LA` with `LAP`). `spike/PROOF.bend` so imported costs
  seconds.
- **An invariant renaming one test in another is built by its twins.**
  `faced.in` is `faces` with `port.ok(N, d, r)` replaced by membership
  `has(N, r)`: `faces`' lemmas, the join's and the cursor's steps among
  them, copied with the test and their names renamed, checked unchanged
  (`faced_keep`, `join1_faced.go`, `cur_faced` in `glam/PROOF.bend`). A
  fold's frame is then carried by an invariant over the region fixed at
  its start (the ports faced then), not by a model of the fold.
- **A fact on views reads back as a word**: `get_view` on both heaps and
  `Some`'s injectivity (`some_inj`, by `Maybe.default`) turn
  `List.get(view(w1), slot(j)) == List.get(view(w2), slot(j))` into
  `snd(rd(H{w1}, j)) == snd(rd(H{w2}, j))` (`cursor_keeps.m`). Over two
  computed heaps it is written out where the heaps are `Data` terms,
  not as a function over two arrays, which cannot be `+`.
- **Before calling a model's fact an accident, read its neighbours.** A
  review read `RG.port.ok` as holding of the eraser only because all
  ones plus one wraps to the head; it holds of every static, because
  `bases` and `layout`, conjuncts beside it, make a member's words 2 and
  3 end in `10` and `11` and a static's `r + 1` ends in `00`
  (`docs/reviews/Refs_2026-11-18.md`, Corrections). What a predicate's
  other conjuncts give decides what a change to one of them changes.
- **A step whose middle does not reduce is crossed by a lemma over its
  result.** The value table's put matches on a word it reads
  (`dt_put`), so it never reduces over symbolic words, and the pair it
  returns is never a literal for the next function to take apart. A
  lemma taking that pair as a variable and matching it
  (`match r: case (tb, i):`), then the record inside (`P.DT{...}`),
  states the step's frame whatever the middle computed (`dto_keeps`,
  `dtb_keeps` in `spike/PROOF.bend`).
- **A proof's match reduces the code's only at a constructor.** A
  `case _` in a proof refines its scrutinee to "not the others" (the
  checker shows `List - Nil{}`), which reduces none of the code's own
  matches; name each constructor the code's `_` covers, nine for a
  `V.Val` (`put_k`, `put2_k`).
- **32-bit addition associates, proved over the modulus.** A word
  computed as `(base + port) + 1` is the node's word `base + (port + 1)`
  only by associativity, which the hub lacks: `u32_assoc` in
  `glam/SPLICE_PROOF.bend` takes `to_nat` of both sides through the
  hub's `u32_add_wrap`, two `mod` lemmas of its own (`mod_add_l`,
  `mod_add_r`) and `add_assoc`, then `u32_to_nat_inj`; the modulus a
  variable `m` with the equation `Nat.pow(2n, 32n) == m`, so that 2^32
  is never computed. Hub candidates, all three.
- **A tree in the heap is proved against a tree as a value**
  (glam/INDEX_PROOF.bend): the model a data type passed as the law's
  parameter, its realization a recursion on the model reading the words'
  view, its layout stated on the model too, so that a split of its nodes
  is a computation; a step's walk proved to write exactly what a model
  function names, then the realization after those writes, both by
  induction along the model; the bit facts proved on the U32's Word,
  generic in its width, the free list's round trip too (a node freed is
  the next taken, for every word, by its bits: no 2^32 enters, which the
  checker would unfold in unary). Its header lists what it cost to find
  out.
- **A heap is not Data**: a lemma over any heap `h` may use it once, so
  one that needs its words and values too (a free's frame on whatever
  heap a removal leaves) is written as text at each call site on the
  heap's term, taking its parts by an eta lemma (`heta3`), not as a
  lemma over `h`. To chain laws over heaps the code computes, prove the
  fold over any words and values and rebuild the heap from its parts at
  each step; no lemma that the value table is kept is then needed.
- **A law needing a fact only an earlier proof reaches**: when the next
  law needs something only an intermediate heap's facts give (the words
  full after a join, which the index's laws take there), widen that
  proof's goal by a conjunct and have its law project, rather than
  derive the intermediate facts a second time.
- **`one_law` cuts by every name a definition's text mentions**, its
  trailing comments too: a comment naming a retired lemma pulls that
  lemma, and its failure, into the cut.
- **A new section is checked in seconds** against the cut proof file of
  a law that already passes, its long chains left out and the few
  helpers it needs copied in (`results/index_bits/kp/harness.py`), not
  through the whole file.
- **A propositional case analysis is searched out, not written**
  (glam/JOIN_PROOF.bend): where a law's cases reduce to Bool atoms (here,
  which port's link word lies in which node's word 1), state each as a
  lemma whose parameters are the atoms and whose premises are the facts
  among them, and let an authoring aid check it by every assignment and
  write the case tree: split on the next atom in parameter order (Bend
  matches binders in the order bound) until the goal computes or a
  premise computes false. A dependent premise (`@z: U32 -> ...`) is used
  once, so a fact for every member is an induction of its own instead.
- **A lemma over any heap's parts mirrors both.** `jnk2`
  (`glam/PROOF.bend`, the join's frame below its first removal) takes the
  words and the value table erased, each with its mirror: an erased
  value table passed to a law whose table is relevant
  (`XL.remove_keeps`) is refused, its mirror's `LAT.fromT(V.Val, ta2)`
  is not. A parameter a lemma's terms use twice takes `+`; the checker
  points at the parameter alone (`jnk2`'s index `J`).
- **A frame read at the word it wrote gives the write's value.**
  `cursor_head` is the cursor's frame chain (`cfr_case`) with `j` the
  cursor's own word 0: the insert's frame law keeps it, the array's
  `get_set_same` closes the chain (`ch.*` in `glam/PROOF.bend`).
- **A witness checks without its proof file.** one_law's witness file
  imports the code and the models, never a proof, so a law's premises
  are shown met together (each by `{==}`) while its proof file fails:
  `results/index_bits/retire/wcheck.py` runs a mutants file's witnesses
  unmutated and mutated so, and showed the serve's four laws
  non-vacuous before the ring's proofs were retired.
- **A survey by name reads words in comments.** Reachability collected
  from definitions' text counts a word in a comment as a use (`ring`,
  `chain` in `glam/ring_model.bend`'s comments kept their defs alive);
  strip comment lines first (`results/index_bits/retire/retire.py`).
- **Retire laws by disposition, mutants first.** Before deleting a law,
  classify each mutant naming it by whether its mutated code is reachable
  from the code's callers and which surviving law catches it
  (`results/index_bits/retire/live.py`): a live mutant left with no law
  marks a law to restate (`cursor_head`, `join_keeps` over the index),
  a dead one goes with its code, naming its counterpart if any.
- **A lone call in parentheses parses as an annotation.** A goal
  `{(f(x)) && b == True{} : Bool}` fails, "expected ':'": Bend reads
  `(` then a term as `(term : Type)`. A conjunction in parentheses
  parses (`(a && b) && c`), so a generator that widens a goal
  parenthesizes a conjunction alone
  (`glam/proofgen/gen_compose.py`).
- **A bit fact goes through lawful-words.** A low mask is a remainder
  (`to_nat_and_mask`: `r & 3` is `r mod 4`); a high one is shown bit by
  bit (`bit_and`, `bit_not`, `bit_ext`: `(y & ~3) & 3` is 0, a Bool
  lemma closing each bit). A slot of a heap of depth 2 or more keeps a
  word's residue modulo 4 (`nat_mod_mod_pow`), and a residue moves
  through a sum by `nat_div_mod`, `nat_add_assoc` and `nat_mul_mod`:
  `st_off`, `glam/PROOF.bend`'s "Alignment". `Nat.cmp` matches both
  arguments, so an absurd case `1n+p < 1n` matches `p` down to a
  constructor before the comparison computes. `Nat.sub` does too:
  `Nat.sub(1n+a, 1n)` stops at `Nat.sub(a, 0n)` for a symbolic `a`,
  rewritten by a two-case lemma (`sub0`, `glam/FREEZE_PROOF.bend`).
- **A def is opaque before its definition.** A lemma whose premise
  names a def written later in the file sees it unreduced ("expected
  `FM.lks.far(...)`, observed `inv.jl(...)`"): define the predicate
  before the first lemma that uses it (`glam/FREEZE_PROOF.bend`).
- **A word's parity is its head bit.** `(i << 1n) + 1` exposes its low
  bit after one match on the word, its tail an add-with-carry against
  zeros, so `to_nat` is `1n+Nat.double(_)` whatever the tail. Read the
  head with a function (`hd`) so that the tail need never be written,
  and keep the parity through a slot by `nat_mod_mod_pow`
  (`odd_hd`, `odd_slot`, `glam/FREEZE_PROOF.bend`).
- **A ladder of step lemmas is written once, as a template.** A proof
  def may take an invariant (`~I`), a context (`~C`) and its leaf
  lemmas as `~` parameters, and it checks with them abstract. Each
  instance passes top-level defs. Rules that make it work:
  - an arrow over a `+` parameter is written `@+x:A -> B`; a plain
    arrow is refused against a def whose parameter is `+`;
  - a template passes its own `~` parameters down to another template;
  - a template is callable only below its definition;
  - a leaf named like a pattern variable is shadowed inside the match
    (`~l_root`, not `~root`, beside `Fl{..., +root, ...}`).

  `--verdict` accepts templates, and `scripts/one_law.py`'s cut
  follows `~` references (`em_T`, `glam/FREEZE_PROOF.bend`). A type
  parameter (`~X: Data`) lets an instance pick its invariant's argument
  (a `Nat` count for `emits_len`), and an invariant that changes at one
  step enters the template below it, at the level that step's lemma
  feeds (`emt_T`, the count one more). An invariant kept as
  `I(f, n0) -> I(step(f), n0)` at one fixed argument is closed under
  repeating a step. So nothing such can say that two ports' pushes
  differ (the crossings' positions): the argument has to move between
  ports, by a parameter `~nx(n0, p)` that each port advances to
  `p + 1`. The identity serves an invariant no port moves, its leaves
  standing by conversion. A count of ports done is matched as the ladder
  matches its arity (`pd`), since `U32.from_nat(a)` stays symbolic for a
  "three or more" case. A proof
  file's plain check is far cheaper than its verdict, 3.6 s against
  35 s there: iterate with the plain check.
- **A read-only audit bridges like a read-only phase.** `KN.wired_ok`
  walks the heap reading only, so on a mirrored heap it is a model over
  the words' tree. Write the model to accumulate the verdict as the code
  does (`ok && check`, left to right), so that the bridge needs no
  reassociation. A false verdict stays false, which gives each step of a
  true one. A mutant of an audit cannot be refuted by a witness, since
  the witness must pass the original audit: the bridge failing on it is
  what catches it (`spike/WIRED_PROOF.bend`).
- **A composed law rewrites the code's inputs in the order it reads
  them.** The serve's end (`glam/MATERIALIZE_PROOF.bend`) takes four
  rewrites, the demand's end, the find, the find's answer and the
  check, each motive the goal with that read a hole; the code between
  reduces. An equation over a `Type` (`Q.Pd`'s) may be marked `+` and
  named twice, as one over `Data`.
- **A verdict's cost is mostly its imports'.** Time a file of the
  imports alone, with one trivial def, before blaming the proofs. The
  hub's `string.bend` costs about 75 s (2026-11-24, Bend 2.0.39), which
  the proof files took for one lemma, `u32_eq_of_is_eq`, now copied into
  `vendor/bend-mathlib/u32_eq.bend`; `glam/materialize.bend`'s closure costs 85 s, the
  floor of any law over the serve's code.
- **A law over code's writes is proved over the view's list form.** The
  heap the code leaves is equated to sets on its words, each set's view a
  `List.set` of the one before (`LA.set_view`), and the invariant proved
  over that list as a lemma of its own with no heap in it; a conjunct
  that reads a written word is proved at the value and carried back by
  substitution (`glam/LOOP_PROOF.bend`'s `px_sv`, `situate_pend`).
- **A loop's step is settled at the ends it makes.** For a loop
  `loop.r(step(h), more)`, one lemma walks `step`'s branches to the end
  each makes and settles it there: an end by its own lemma, a "go
  again" by the induction passed as a function of the next state. A
  lemma about `step(h)`'s result plus a match on it would name the heap
  twice. The induction itself can be a lambda calling the lemma on the
  smaller count (`front_loop`, `glam/POSITION_PROOF.bend`).
- **A mutant's witness must reach the end it breaks.** Moving a read
  every path shares moved the witness off the path it tested, so the
  law held on it. Mutate the read at the end the law is about.
- **A parameter named as a def shadows it.** A premise `hw` hid the word
  function `hw` ("expected a function type"): name premises apart from
  the file's defs.
- **Keep a frame on the state as it is, not against where it began.**
  The write phase's reads after an error's count come from the updated
  words. Rather than relate them to the original words, the list's
  invariant is a fact about the current tree (full at `d`, each base
  left with a good header in its view), and one lemma shows that an
  error's write keeps it (`et_keeps`, `glam/FREEZE_PROOF.bend`). Where
  a rewrite is not allowed after lets, carry a hypothesis across by
  `ME.subst` (`ems_n`).
- **A let does not infer a constructor's type.** `+l = T.TL{...}` is
  refused as "an annotated term (cannot infer)", and an ascription
  `(T.TL{...} : T.TLink)` does not take: name the term inline where a
  parameter's type checks it (`push_k`, `glam/FREEZE_PROOF.bend`).
- **A record holding a heap is chained by equations, not
  implications.** A step lemma `inv(z) -> inv(step(z))` over a record
  with a heap or an array in it chains only by naming the record twice
  (`step(z)` and the lemma's own `z`). That is refused three ways: as
  "consumed more than once"; `+z` because its type is not `Data`; and
  `-z` because an erased scrutinee "matches only in a dead region".
  State each step as an equation instead, the heap and the map mirrored
  (`P.H{KM.MG{fromT(t0)}, fromT(ta)}`, `fromT(tm)`, the trees `Data`):
  `step(mk(H, M, f)) == mk(H', M, model(f, ...))`, the result in the
  same form, so that steps chain by rewriting. Each read hands its
  array back (`get_pair`, `size_pair` for a probe's size), and a write
  keeps the mirror (`set_tree_eq`, lawful-arrays' `proof_index.bend`).
  A law called from a proof needs its filling even so: "an unfilled law
  is a dead claim" (`cursor-laws.materializer.template.emit`,
  2026-11-24).
- **Keep a big bound on words, and bound from above.** A premise
  `U32.is_le(n, 2147483648)` is computed on words, as is a power doubled
  thirty-one times (`dbl`), where `2^31` as a `Nat` would be expanded in
  unary. An invariant `to_nat(pw) <= 2^d`, not an equation, carries a
  doubling through `to_nat_mul` without an overflow argument: a
  remainder is at most its argument (`map_depth`,
  `glam/SPLICE_PROOF.bend`).
- **2^32 stays out of a comparison.** The checker expands a power it must
  normalize: `WL.to_nat_add(i, 1)`'s type holds `U32.to_nat(1)`, and a
  motive written with `1n` there sets the two side by side under
  `Nat.mod(..., Nat.pow(2n, 32n))`, overflowing the machine's stack.
  Write the lemma's own form in the motive and turn `U32.to_nat(1)` into
  `1n` apart, where no power stands beside it; bound an index below
  2^32 by a word above it (`WL.to_nat_lt(c)`), never by a power's order
  (`MN.pow_lt_pow_right` states its base as `2n+a`, which meets
  `Nat.pow(2n, 32n)` only by expansion; `tn1`,
  `spike/GROW_PROOF.bend`).
- **Bound a power below 2^32 by the hub's `pow_lt`.** Its base is
  written `2n`, so that `pow_lt(j, 32n, h)` names `Nat.pow(2n, 32n)` as
  the words' laws do; `MN.pow_lt_pow_right` names `Nat.pow(2n+0n, 32n)`,
  which meets the words' form only by expansion. Keep 2^32 abstract as
  `m` while reasoning (`+m`, `+em: {Nat.pow(2n, 32n) == m}`), and put it
  back only for a word law's premise, written in that law's own form
  (`tnm.k`, `spike/GROW_PROOF.bend`).
- **A closed heap's law by computation.** `h_new()`'s 512-word heap, 121
  nodes threaded, normalizes in the checker in about 2 s, so a law about
  it is `{==}` (`shape_new`, `spike/GROW_PROOF.bend`). A law about the
  largest store, 2^30 words, has no witness a run could build: its
  mutants are caught by the proof only (`shape_max`).
- **A U32 literal's case is 32 matches.** `match cap: case 1:` compiles
  to a match on each of the word's bits (`bend x.bend -o x.bendtt` shows
  it), which a symbolic word never passes, and no premise rewrites it.
  Test `U32.is_eq(cap, 1)` instead and match the Bool, carried as a
  parameter where the function recurses, so that a proof rewrites the
  test by its premise (`KM.depth`, `spike/kmem_grow.bend`).
- **A Nat matched binds its predecessor once.** `case 1n+p:` gives a
  linear `p`; a proof that uses it twice (a recursive call and a bound)
  takes the matched parameter `+k`, which makes `p` copyable.
- **No forward references, so no mutual recursion.** A proof that would
  recurse through a helper passes the recursive call to the helper as a
  closure (`ih: {..} -> {..}`, the binder `@y:U32 -> ..` where it is
  dependent), and code loops through a step type, as `KM.ens` does
  (`glam/materialize.bend`'s `rm.loop`).
- **Prototype a family of lemmas in a file of its own.** A lemma checked
  in `glam/proofgen/align/ALIGN.bend`, importing what the proof
  files import, costs seconds where the proof file costs a minute, and
  `glam/proofgen/align/bisect.py` checks growing prefixes, naming
  the lemma whose prefix fails: Bend reports a stack overflow with no
  place (docs/BendIssues.md, Big constants in proofs).
- **State a law over the code's own composition.** A law that copies
  the code's sequence by hand misses a change to the code. Stated over
  the code's function instead (`SC.serve`, `glam/serve.bend`), it is
  proved by unfold lemmas generic in the values the function matches on
  (`serve_false`, `serve_true`: the splice's result, then the pair the
  crossings return, each matched in a helper, as `case (map, h):` does
  for a pair), and each entry rewrites the function to the old form once
  (`%Equal.sym(...)`), the old proof running on.
- **Laws compose as functions.** A law of an imported laws file is
  called like a definition (`GL.crossings_pend` in `glam/SERVE_PROOF.bend`'s
  `sp.go`, `Laws.copy_pend` in its own file). Once each law concludes
  what the next one's premises ask (the words and the map full, the
  layout and bases of the nodes after), a caller chains them with
  nothing from the proof files but the heap's eta (`SPP.heta`) and the
  arrays' mirrors, a linear array read twice taking one.
- **Before writing a basic lemma, look for it.** The proofs had copies
  of facts the hub proves, some in six files (`not_true`): Bool's `and`
  and `or` splits, `Nat.sub(n, 0n) == n`, `0 <= n`, `le` transitive. Run
  `python3 -I scripts/proof_dups.py --detail` over a new proof file: it
  names any lemma whose statement another file or the hub already proves,
  the parameters renamed by position. The hub's laws it found restated
  (2026-11-25, `cursor-laws.proofs.dups`), each callable where its file
  is imported (`_0`, `_1` the parameters in order; `{x}` for
  `{x == True{}}`):

  | Law | Where | Statement, parameters by position |
  |---|---|---|
  | `bool_or_left_comm` | bend-mathlib `algebra.bend` | `Bool , Bool , Bool -> {Bool.or(_0, Bool.or(_1, _2)) == Bool.or(_1, Bool.or(_0, _2))}` |
  | `and_eq_true` | bend-mathlib `bool.bend` | `Bool , Bool , {_0} , {_1} -> {Bool.and(_0, _1)}` |
  | `and_false` | bend-mathlib `bool.bend` | `Bool -> {Bool.and(_0, False{}) == False{}}` |
  | `and_true` | bend-mathlib `bool.bend` | `Bool -> {Bool.and(_0, True{}) == _0}` |
  | `eq_false_of_not_eq_true` | bend-mathlib `bool.bend` | `Bool , {Bool.not(_0)} -> {_0 == False{}}` |
  | `eq_true_of_and_left` | bend-mathlib `bool.bend` | `Bool , Bool , {Bool.and(_0, _1)} -> {_0}` |
  | `eq_true_of_and_right` | bend-mathlib `bool.bend` | `Bool , Bool , {Bool.and(_0, _1)} -> {_1}` |
  | `or_assoc` | bend-mathlib `bool.bend` | `Bool , Bool , Bool -> {Bool.or(Bool.or(_0, _1), _2) == Bool.or(_0, Bool.or(_1, _2))}` |
  | `or_true` | bend-mathlib `bool.bend` | `Bool -> {Bool.or(_0, True{})}` |
  | `add_assoc_sym` | bend-mathlib `nat.bend` | `Nat , Nat , Nat -> {Nat.add(_0, Nat.add(_1, _2)) == Nat.add(Nat.add(_0, _1), _2)}` |
  | `add_succ` | bend-mathlib `nat.bend` | `Nat , Nat -> {Nat.add(_0, 1n+_1) == 1n+Nat.add(_0, _1)}` |
  | `add_succ_sym` | bend-mathlib `nat.bend` | `Nat , Nat -> {1n+Nat.add(_0, _1) == Nat.add(_0, 1n+_1)}` |
  | `add_zero` | bend-mathlib `nat.bend` | `Nat -> {Nat.add(_0, 0n) == _0}` |
  | `is_eq_refl` | bend-mathlib `nat.bend` | `Nat -> {Nat.is_eq(_0, _0)}` |
  | `mod_one` | bend-mathlib `nat.bend` | `Nat -> {Nat.mod(_0, 1n) == 0n}` |
  | `sub_zero` | bend-mathlib `nat.bend` | `Nat -> {Nat.sub(_0, 0n) == _0}` |
  | `succ_inj` | bend-mathlib `nat.bend` | `Nat , Nat , {1n+_0 == 1n+_1} -> {_0 == _1}` |
  | `lt_one` | lawful-arrays `proof_base.bend` | `Nat , {Nat.is_lt(_0, 1n)} -> {_0 == 0n}` |
  | `true_ne_false` | lawful-arrays `proof_base.bend` | `{True{} == False{}} -> Empty` |
  | `le0` | lawful-arrays `proof_index.bend` | `Nat -> {Nat.is_le(0n, _0)}` |
  | `nat_le_trans` | lawful-words `LAWS.bend` | `Nat , Nat , Nat , {Nat.is_le(_0, _1)} , {Nat.is_le(_1, _2)} -> {Nat.is_le(_0, _2)}` |
  | `bit_zero` | lawful-words `proof_bytes.bend` | `Nat -> {bit(0, _0) == False{}}` |
  | `add_one` | lawful-words `proof_nat.bend` | `Nat -> {Nat.add(_0, 1n) == 1n+_0}` |
  | `le_add_mono_l` | lawful-words `proof_nat.bend` | `Nat , Nat , Nat , {Nat.is_le(_1, _2)} -> {Nat.is_le(Nat.add(_0, _1), Nat.add(_0, _2))}` |
  | `le_ne` | lawful-words `proof_nat.bend` | `Nat , Nat , {Nat.is_le(_0, _1)} , {Nat.is_eq(_0, _1) == False{}} -> {Nat.is_le(1n+_0, _1)}` |
  | `le_refl` | lawful-words `proof_nat.bend` | `Nat -> {Nat.is_le(_0, _0)}` |
  | `lt_to_le` | lawful-words `proof_nat.bend` | `Nat , Nat , {Nat.is_lt(_0, _1)} -> {Nat.is_le(_0, _1)}` |
  | `mod_add_mod_l` | lawful-words `proof_nat.bend` | `Nat , Nat , Nat -> {Nat.mod(Nat.add(Nat.mod(_0, _2), _1), _2) == Nat.mod(Nat.add(_0, _1), _2)}` |
  | `mod_add_mod_r` | lawful-words `proof_nat.bend` | `Nat , Nat , Nat -> {Nat.mod(Nat.add(_0, Nat.mod(_1, _2)), _2) == Nat.mod(Nat.add(_0, _1), _2)}` |
  | `zero_ne_succ` | lawful-words `proof_nat.bend` | `Nat , {0n == 1n+_0} -> Empty` |
  | `u32_eq_of_is_eq` | `vendor/bend-mathlib/u32_eq.bend` | `U32 , U32 , {U32.is_eq(_0, _1)} -> {_0 == _1}` |

  Import `vendor/bend-mathlib/u32_eq.bend` for `u32_eq_of_is_eq`, never
  the hub's `string.bend`, whose import costs a verdict about 75 s.
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
  it, and where, a mutation with a witness by its witness alone, every
  witness unmutated in one run. A run is kept while the files it checks
  are unchanged, so that a witness, which checks the code's modules and
  not the proof file, reruns only when the code or its law's statement
  changes. The runs go in parallel,
  as many as the available memory holds at the cap (1500 MB, the
  largest run near 380 MB), at most half the processors (`--jobs N`
  to choose), reported in order.
