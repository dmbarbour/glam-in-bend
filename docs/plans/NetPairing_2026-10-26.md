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
   Built 2026-10-27, after the derivation below and its correction:
   fans, functions and applications carry levels; `Lift` and `LiftC`
   control nodes, their rules in the table under the polarity and
   linearity laws; a level mismatch at beta counts as an error;
   `terms.py` lowers with boxes. All eight hand-picked terms reduce to
   their values, self-applications included (`self #3`,
   `twice (\n. n n) #2`), and 458 of 460 random ones (seeds 7, 11, 23);
   the other two run out of fuel with no level mismatch, one computing a
   number its result discards (the reducer is not demand-driven), one
   piling up control nodes, 24,000 of them with indices up to 54. The
   price is bookkeeping: 4 to 20 times the interactions of static labels
   where both are right (`two two`, 114 against 27). The hand-built nets
   in `spike/nets.bend` have no levels, so they still pair as static
   labels.
   Fused since, with the maintainer's leave: a control carries an index
   and an offset, so a run of brackets ending in a croissant is one
   control. Lowering emits at most one per edge of a variable's paths,
   none for a shift of 0. After each rewrite, a control merges with one
   facing the same way beside it when `V.compose` finds a single control
   acting as both: when the first crossed moves up by k and the second's
   index lies within k above the first's. Then levels, and the indices
   of controls crossing them in that order, move as through the two
   (checked exhaustively on small ranges: 176 of 560 pairs fuse, none
   differs). On 600 random terms 599 reduce to their value, against 597
   unfused and 506 under static labels. On the 506, levels cost 2.8
   times the interactions of labels, against 19 times unfused; beta
   rose from 7% to 11% of all interactions. Fusion is tried only where
   controls can become adjacent: a rule's new controls, and the external
   peers a rule joins to each other (beta's crossed join, a fan join,
   cancelling controls); the same fusions happen as when every node was
   tried, at about 6% of time on the throughput chain rather than 13%.
   Since narrowed to one try per link a rewrite makes that may join two
   controls (EvalSpike's spike-node-layout).
   Since the comparison below: a copy meeting a function at a level not
   below its own, and two fans meeting at one level with different
   sites, count as errors (assertions; the rewrite proceeds), as does a
   control raising a level past the top of `U32`. None fires on the 611
   terms (600 random, 11 picked). The root takes the place of a control facing it, and the
   result is read off the live root. A raise checked only the lift's
   side when a lift met a liftc, though each raises the other's index;
   both are checked since (`spike/test_levels.bend`).
   Down offsets fuse only as a croissant after a raise. The maintainer
   expects more, with the right framing; a symmetric one: a control
   (n, k) leaves levels up to n alone and moves those above to
   max(n, j + k), so a raise opens a gap of k above n and a drop closes
   one, n being the floor after (two croissants at n are (n, -2)). In a
   model, every fusion, the current one included, changes how a facing
   control equal to the first of the pair comes out: the pair cancels it,
   the fused control crosses it. The results look equivalent, the shift
   between values and consumers agreeing, but the criterion is semantic
   (properness, below), not structural. Wider fusion waits on it.
7. `pairing-nets` — levels for nets not built from lambda terms: every
   term lowers to a net, but not every net is a term's, and the
   maintainer's earlier discussion generalized through polarity. Settle
   which discipline glam's own net construction follows (levels assigned
   as it builds, or boxes inferred from polarity), and test hand-built
   nets against a reference whose correctness needs no levels: a copy
   that duplicates the whole subnet behind its input, after the Rust
   bootstrap's whole copies.
   glam's nets, as the maintainer describes them: users build them
   monadically with four effects. `copy N` makes balanced fans (a tunnel
   for 1, an eraser for 0); `data` embeds data; `bind` makes a function
   or an application, as polarity decides; `wire` joins two ports. copy,
   data and bind return lists of ports, and the net returns one port,
   positive by fiat, as its interface. Users assign neither levels nor
   polarity, so both are inferred: polarity first (bind's role, by
   parity over the wires, the root pinning it), then levels.
   Sketch (2026-10-27, before reading the earlier discussion's take).
   Polarity fixes which way values flow, so the subnet that produces a
   value is well defined: walk upstream from a negative port to the
   producing node, then from its negative ports on. A box is that
   upstream region for every value that may be duplicated, the input of
   a copy or the argument of an application, closed under two rules:
   reaching a function through its argument port does not take it in (a
   free variable, so a bracket on that edge) unless it is in by its
   principal; and a copy is in only if both its outputs' consumers are
   (else it is shared from outside, a bracket again). Depth is the
   number of boxes around a node; fans take the depth of where they
   sit, and every value leaving a box to be used, through a copy's
   outputs or a variable's uses, crosses a croissant. Lambda-built nets
   give boxes that nest, which is all Lamping's theorem needs. A net
   whose boxes overlap without nesting has no levels of this kind: a
   function whose argument is used outside its body's region (scope
   extruded), for instance. Such nets would be refused, or paired some
   other way. Open: whether glam's monadic construction can assign
   levels as it builds, which would make inference needless for its own
   nets.
8. `pairing-lean` — after that testing, a time-boxed study in Lean 4.
   Formalize polarized nets and their rules, prove polarity preservation
   as a warm-up, then state the adaptation's correctness as Guerrini's
   properness: nets as built are proper, every rule preserves properness,
   and a proper net's reduction is simulated on its unfolding. The
   properties to prove first: a copy meets only deeper nodes, and fans
   meeting at one level are residuals of one duplication. Attempt it, or
   find the restriction under which it holds.
9. `pairing-verdict` — choose how each kind of net pairs (labels, levels),
   and record it.
10. `pairing-docs` — revise the standing docs to the verdict. Design.md's
    copy-copy rule says pairing follows complete dynamic duplication
    identity and that duplication history distinguishes residual fans;
    histories pair wrongly, so say what does, and check the other docs
    for the same claim.

## Derivation (`pairing-gal-derive`, 2026-10-27)

Derived before reading the maintainer's earlier discussion; compared with
it below.

**What must be known.** A duplication process is the set of fans bearing
one identity. Its copies take values from the region being duplicated and
hand a copy to each side; its merges take a value from each side and hand
a superposition into the region. Its fans move into the region and
annihilate where they meet. When a fan of process D meets a fan of
another process E, they commute, and one is being copied by the other: E
is inner if it lies in the region D duplicates. Then D must pass
unchanged, since its partners are still ahead, while E's two residuals
become two processes, one in each copy. At the meeting each fan sits in
the other's region, so nothing local says which region holds which.
Labels record neither; histories record both, which breaks D.

**Levels.** Lamping's answer: every node has a level, the number of
boxes (duplicable arguments) around it. A fan duplicates boxes deeper
than itself, so of two meeting fans the deeper is inner. Fans annihilate
exactly when their levels are equal: residuals of one process share a
level, and in nets built from terms two processes never meet at one
level (Lamping's theorem). Copies of an inner process share a level too,
yet never meet wrongly: whichever later enters the other's box has its
levels raised on the way in. Levels make the history needless.

**Levels move.** A box's contents sit a level deeper than the context
that uses them, so a value's levels shift as it crosses a box boundary.
Lamping shifts them lazily, with control nodes on the wires values
cross. In a polarized net a control node is unary, `[- in, + out]`, its
principal toward the value's source, so it meets only what flows down
the wire: functions, merges, data and error values. Two kinds, after
Lamping's brackets and croissants:

    Br n: a level j > n becomes j + 1
    Cr n: a level j > n becomes j - 1
    (Cr n undoes Br n: Cr n after Br n is the identity)

The rules with levels (L is Br n or Cr n; L' is the other kind, index n):

    L >< Data, L >< EraP   the value passes unchanged: data hold no fans
    L >< Merge m           a Merge at L(m); an L on each of its inputs
    L >< Fn f              an Fn at L(f); an L on its body wire; an L' on
                           its argument wire, since arguments flow from
                           the outer frame back into the body
    Copy c >< Fn f         two Fn f; a Copy c on the body, a Merge c on
                           the argument (as now)
    Copy c >< Merge m      annihilate when c = m and site and
                           instantiation agree; else commute, both
                           keeping their levels
    Ap a >< Fn f           beta; a = f in a well-formed net, so anything
                           else counts as an error (a check)
    Ap a >< Merge m        as now: the Aps at a, the Copy and Merge at m
    Call, Data, erasers    no levels

**Lowering assigns them.** A term lowered at level n:

    \x. M        an Fn at n; M at n
    M N          an Ap at n; M at n; N at n + 1 (a box)
    x            bound at level b, used at depth d >= b: its path from
                 the Fn's argument port crosses Br b, ..., Br (d - 1),
                 one per box entered, then Cr d at the use, so a value
                 made at level b + 1 arrives at level d
    several uses paths share their common prefix; where they split, at
                 depth k, a copy fan at level k (a chain for more than
                 two)
    no use       an eraser on the argument port
    data         no level

glam's own nets: a template (a function as data) carries levels from 0;
a call at an Ap of level a instantiates it at its levels plus a, in a
fresh fan namespace. Data, function values included, carry no levels, so
copying them needs none.

**On the failing case** `(\t -> t t) two`: t's fan sits at level 0, one
use behind Cr 0, the other inside the argument box behind Br 0 and Cr 1.
`two` arrives as an argument, level 1, with its own fan G at level 1.
The copy used as the function drops to level 0 as it passes Cr 0; the
copy used as the argument goes up through Br 0 and back down through
Cr 1. When the function copy's fan duplicates the argument copy, the
argument's nodes have crossed the Br 0 on its argument wire and stand a
level above it, so the two residuals of G meet at different levels and
commute, where one label made them join.

**Costs and risks.**

- Every control crossing is an interaction: Lamping's bookkeeping, which
  can outweigh the beta steps themselves (Asperti and Mairson). Data pay
  one interaction per crossing.
- Control nodes all face their source, so they never meet each other:
  the face-to-face annihilations of unpolarized presentations do not
  happen, and chains build up on wires until a value passes; unused
  paths keep theirs until collection. Fusing a chain into one node that
  maps levels by offsets (as BOHM's indexed brackets and Guerrini's
  multiplexers do) is the obvious optimization.
- Correctness rests on Lamping's theorem, for nets built from terms.
  glam's monadic nets, strict calls and data need an argument of their
  own: data hold no fans, and calls distribute merges without touching
  levels.
- Levels are `U32`; depth grows with nesting and with unfolding, so the
  lowering and the rules guard against wrapping.
- What GAL adds to this, its cheaper level tracking, is not
  reconstructed here.

**Corrected in building it.** Two claims above are wrong. Control nodes
do not all face their source, and a function passing one does not take
the inverse onto its argument wire. A croissant maps level n + 1 onto
n, so the inverse loses a level: in `two two` a merge at level 1 passed
the croissant to 0 on the way into a body, came back out through the
bracket on the body wire still at 0, and met its partner copy, at 1, as
a stranger. As in Lamping, a function passing a control takes the same
control onto both its wires, because both lead back into the same box;
on the argument wire it faces the variable's uses. So there are two
orientations:

    Lift  [- in, + out]   faces the source: values pass it going down
    LiftC [+ out, - in]   faces the consumers: copies, applications and
                          calls pass it going up, their level adjusted,
                          the control copied onto their other wires;
                          an eraser takes its place
    Lift >< LiftC         facing each other: one kind and index cancel;
                          else each crosses the other, the higher index
                          adjusted by the lower one's map

A control reaching the root is stuck; no test reaches it.

## Compared with the earlier discussion (2026-10-27)

A sub-agent read the maintainer's earlier discussion of this
adaptation, saved from its share page, and compared it with the
derivation and its correction; its quotes were checked against the
saved text.

- **Agreed:** levels are box depth; fans annihilate at equal levels and
  keep theirs when commuting; brackets and croissants move levels above
  their index by one; facing controls of one kind and index cancel,
  others cross with the higher index adjusted; a template is
  instantiated at the level where it is applied; `(\t -> t t) two`
  traces the same way; the cost is controls, and the cure is fusing runs
  into controls with offsets.
- **Ours, not there:** the two orientations of controls, a function
  taking the same control onto both wires (the discussion never settles
  orientation); the rule table under laws; testing against a direct
  evaluator; fusion at run time.
- **There, not ours:** Guerrini's general theory as the target, with two
  obligations (nets are built proper; each rule preserves properness),
  which covers hand-built nets; the invariant that a copy meets only
  deeper nodes, and labels kept as an assertion (both now checked);
  polarity inference for a bind of either role, then level inference,
  rejecting nets that have none (non-polarizable nets, inconsistent level
  cycles, variables escaping their box); argument-position cycles
  excluded; safe nodes and pre-normalized templates against bookkeeping.
- **Different:** our fans sit where a variable's uses split, theirs at
  the binder's level with the brackets after them; both should be
  proper, and which costs less is to be measured. Levels live on `Fn`
  and `Ap` here, on the function datum there; equivalent while a wire
  joins nodes of one level.
- **Doubtful there:** a croissant once at the binder is not equivalent
  to one per use (a use deeper than its binder arrives at the wrong
  level); what sits at a box's root changes three times; level inference
  is called a function where it is a constraint problem in general.
- **Unverified on both sides:** GAL's actual rule table. The `j > n`
  boundary and same-kind cancellation are recollections; check them
  against GAL's and Guerrini's papers.

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
