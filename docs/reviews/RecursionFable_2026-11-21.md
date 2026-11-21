# The Scott walk's quadratic: advice (Fable, 2026-11-21)

The second reviewer's advice on `cells-recursion.depth`, by a Fable
sub-agent, kept as written. Checked after against a trace of every
interaction at lengths 0 to 6 (the Cells plan's step records how): each
row of its whole-run table in section 1 matches the traced counts by
pair kind, and every control met is a unit drop, at one index but for
the one each splice brings at its own, no raise and no fusion, as its H1
predicts.

Read-only advice: nothing was built or run. "Checked" means read in the
code or docs at the cited line; "inferred" means traced by hand from the
rules and not observed.

## 1. Hypotheses, ranked

### The arithmetic first

The three counts fit I(n) = 6n² + 15n + 9 exactly (15,759; 61,509;
243,009). Three points always fit a quadratic, so sizes 1 to 4 must
confirm it: 30, 63, 108, 165 if it holds. If it does, step k costs
12k + 9 interactions, each step exactly 12 more than the last. Any
mechanism must explain a second difference of 12.

### The nets, lowered by hand (inferred from glam/lower.bend)

Assuming the desugarer curries (`cons = \h -> \t -> \c -> \n -> c h t`;
not checked in glam/desugar.bend):

- `use_edge.k` (glam/lower.bend:258-263): a use one box below its binder
  gets no control (d - k - 1 = 0); a use at its binder's depth gets a
  drop by one at index k.
- `cons` at depth 0: Fn h, Fn t, Fn c, FnD n (unused, lower.bend:372);
  B1 = Ap(c, h), B2 = Ap(B1, t), all at level 0. `h` and `t` sit in
  argument boxes at 1: no control. `c` is used at its binder's depth:
  one drop, D_c = Lift(0, down, 1). No fan.
- `walk` at depth 0: Fn l; A1 = Ap(l, K), A2 = Ap(A1, ""), level 0;
  K = FnD h, Fn t, Ap_K(leaf walk, t) at level 1; `t` used at depth 2
  from a binder at 1: no control. `l` at its binder's depth: one drop,
  D_w = Lift(0, down, 1). No fan.

So the only static controls are two unit drops, one per template, and
there are no copy fans and no raises anywhere in the program.

### H1 (lead). Unit drops at index 0 pile up, one more per step, and never fuse

Mechanism, traced by hand against spike/rules.bend (rule.ap :402-436,
rule.lift :489-513):

1. A Lift meeting a Fn crosses it and leaves a Lift on the body wire and
   a LiftC on the variable's wire (rules.bend:499-502). An Ap meeting a
   LiftC crosses it and leaves a Lift on its argument and a LiftC on its
   result (rules.bend:428-432). A control whose principal faces an
   auxiliary port waits there.
2. Step 1: D_w(0) meets cons_1's `Fn c`; its LiftC crosses D_c, lowers
   B1 and B2, and B2 leaves a Lift(0, down) on the `t` wire, facing the
   tail. D_c, now at index 0, crosses K's FnD h and Fn t and leaves a
   LiftC(0, down) on K's `t` wire, facing Ap_K's argument port, and a
   Lift on Ap_K's result. Ap_K itself is never lowered: both controls
   wait at its auxiliaries, so it is still at level 1 when demand
   reaches its leaf, and `sp.by` is 1.
3. Step k (walk_k spliced at by = k - 1): Ap_K's argument wire holds
   k - 1 LiftC(0, down, 1) in series, then k - 1 Lift(0, down, 1) facing
   cons_k; its result wire holds k - 1 Lifts. After the beta of walk_k's
   `Fn l`, D_w (index k - 1) crosses the k - 1 LiftCs, ending at index 0;
   each LiftC then walks walk_k's body; then the k - 1 Lifts and D_w walk
   cons_k's body. Each leaves its residue on the next tail wire: k
   controls of each kind for step k + 1.
4. Only raises fuse (spike/kprim.bend:1162-1165, checked;
   docs/decisions/fuse-control-runs.md:22-29), so the pile stays unit
   drops. A drop at index 0 that meets a node already at level 0 changes
   nothing (V.lift_lvl, spike/val.bend:720) yet still costs the
   interaction.

Predicted per step k, by pair kind:

    pair                      walk_k body          cons_k body        sum
    Lift.LiftC, crossing      k - 1  (D_w)         k      (D_c)       2k - 1
    Ap.LiftC                  2(k-1) (A1, A2)      2k     (B1, B2)    4k - 2
    Lift.Fn                   k      (K's Fn t)    k      (Fn c)      2k
    Lift.FnD                  k      (K's FnD h)   k      (FnD n)     2k
    Lift.LiftC, cancelling    k - 1  (result)      k      (B2 result) 2k - 1
                                                                      12k - 6

(K's two rows are k - 1 from A1's argument Lifts plus one from D_c.)
The second difference is 12, split 2 crossings, 4 Ap.LiftC, 2 Lift.Fn,
2 Lift.FnD, 2 cancellations.

The tally closes on the measurement. Each step adds 7 betas (Fn l;
cons's h, t, c, n; K's h, t). `nil` takes no argument, so it is a bare
leaf on the tail wire: the n Lifts and D_w pass it as data (n + 1
Lift.Data), and it is spliced unraised at the lowered A1. The last walk
costs 6n + 5: 3 betas, n crossings, 2n Ap.LiftC, n cancellations, and
n + 1 more Lift.Data as "" returns through A2's argument Lifts and
nil's own drop; its K is erased, never crossed. `++` costs 4. Whole run:

    Ap.LiftC                               2n² + 2n     4  12  24  40
    Lift.LiftC crossing                    n² + n       2   6  12  20
    Lift.LiftC cancelling                  n² + n       2   6  12  20
    Lift.Fn                                n² + n       2   6  12  20
    Lift.FnD                               n² + n       2   6  12  20
    betas (Ap.Fn, Ap.FnD)                  7n + 3      10  17  24  31
    Lift.Data                              2n + 2       4   6   8  10
    `++` (Ap.Data, Op.Data)                4            4   4   4   4
    total                                  6n²+15n+9   30  63 108 165

(columns: sizes 1 to 4). The same trace of the one-step variant gives
its measured 20. Two totals matching is strong evidence, still not
observation: the rows are what the histogram tests.

Elsewhere a "" argument lands on an FnD binder, whose beta puts a
static eraser on it (spike/krules.bend:1714, checked) that demand never
visits. Copy and Merge pairs are zero; no fusion succeeds; no peel
fires.

Fit to the caller's controls:

- Church-built and live-source lists: the cost does not need cons_k to
  sit at level k. The k drops cross cons_k's nodes whether or not they
  move a level, so half the 12 survives any list; the other half is
  walk's own, independent of the list.
- The fold (`c h (t c n)`): the consumer passes down through a box with
  no control and no template is spliced inside a climbing box, so no
  wire collects more than a constant number of drops (inferred, not
  traced).
- One step, 20: no pile yet.

### H2. The splice's raise climbs, and the climb itself is the cost

`sp.by` reads the application's level (glam/splice.bend:44-52) and
grows by one per walk (0, 1, 2, ...): inferred, consistent with
docs/plans/Cells_2026-11-09.md:143-144. This is H1's precondition, not a
rival: the k - 1 pending drops are exactly what would lower Ap_K from
k - 1 to 0, had they reached its principal. A rival form, "a raise grows
and raise controls accumulate", predicts raises (up = true) in the
census and fusions succeeding; H1 predicts none of either. The raise
itself is arithmetic in the copy (glam/splice_copy.bend:64-69), no
interaction, so it cannot show in the count by itself.

A correctness consequence either way: at depth 2^24 the raise passes
`P.lvl_cap` (spike/kprim.bend:36, :1878) and the walk answers an error
(splice_copy.bend:54-58). A fix to the cost that leaves the climb leaves
this limit.

### H3. The literal's nesting (cons_k lowered at depth k)

The literal puts cons_k's applications at level k, so each needs k drops
to reach 0. True of the literal, and it coincides with H1's count on it,
but the Church and live-source lists refute it as the cause. Cheap test:
bind the list flat, each cell applied at one level (the Church build
already is); H3 predicts linear, H1 the same 12 with cons levels
constant in the log.

### H4. Fans duplicating per step

Refuted on reading: neither template has a copy fan. Confirm by zero
Copy.* and *.Merge rows in the histogram.

### H5. A beta stuck on a level mismatch until controls arrive

rule.ap gives RStuck on unequal levels (rules.bend:406-411). In H1 the
controls always arrive before the beta is tried, because demand walks
through them first. Refuted if the log never shows an Ap.Fn pair with
unequal fields; if it does, that is a fault of its own, not a cost.

## 2. Tracing plan, sizes 1 to 4

### Cheapest first: a histogram, no log

The plan step already asks for "the counts by kind"
(docs/plans/Cells_2026-11-09.md:2843). A 2-D counter by (A's kind, B's
kind, rule variant) at sizes 1 to 6 decides most of this before any
per-interaction log exists. Split Lift.LiftC into its three variants:
cancel (`rw.Lift.LiftC.yes`, spike/krules.bend:1978), cross (`.no`,
:1981-1985) and peeled (:1992). Take first and second differences across
sizes. H1 predicts the second difference of every row constant from size
2 or 3 on, summing to 12, split 4 / 2 / 2 / 2 / 2 as in the table above,
all other rows' second differences zero.

### Where to count

The interaction count is incremented at four sites, not one, in each of
the two generated demands: spike/kdemand.bend:239, :369 (the one through
`Demand.go`), :598 (the interface) and :619 (a static erase), and the
same four under `DemandEv` (:773, :903, :1132, :1153). A log taken only
in `Demand.go` will not sum to `--count`. Instrument in Blend's
kdemand.blend (:256-284 and the two later sites), since kdemand.bend is
generated; and check the log's length against `--count` at every size
before reading it. Fusions are no interactions: count `P.fuse`'s
successes (spike/kprim.bend:1320, called where rewrites link, e.g.
krules.bend:1637, :1670) separately. H1 predicts zero.

### Per interaction, record

- sequence number, and the splice count so far (which step it is in);
- A and B: kind, header field (level, or a control's index), and for a
  control its word 3 (up or down, amount: `P.lift_word`,
  glam/splice_copy.bend:58);
- the rule variant taken (cancel, cross, peel; beta or stuck);
- both nodes' bases. The base lets one follow a single control or a
  single Ap through its life. Bases are reused after a free, so pair a
  base with the sequence number at which it was made if the free list
  recycles within a run this small;
- demand's depth at the pair (the path's length): H1 predicts it grows
  with the number of controls demand has walked through to find the
  pair, which is a walking cost beside the interactions, uncounted.

### At each splice, record

- which template (walk, cons, nil), `sp.by` (glam/splice.bend:52), and
  the application's base;
- a census of every live Lift and LiftC: (kind, index, up, amount),
  as a multiset;
- two chain lengths, walked from the spliced application: the controls
  in series on its argument wire (from port 1 outward, through each
  control's far port, until a node that is no control), with their kinds
  in order; and the same on its result wire (port 2).

H1 predicts, at the k-th walk splice: by = k - 1; argument chain k - 1
LiftC then k - 1 Lift, every one (0, down, 1); result chain k - 1 Lift
(0, down, 1); census all unit drops at index 0 except the freshly
spliced D_w or D_c at index `by`. At the k-th cons splice on the
literal: by = k, k - 1 Lifts and then D_w between the application's
result and A1 (D_w has by then crossed to index 0). Splice order: walk,
cons, walk, cons, ..., walk, nil: 2n + 2, as measured.

### Comparisons, and what each decides

1. Second differences by row (above). Sum 12 with the 4/2/2/2/2 split:
   H1. A nonzero Copy or Merge row: H4 is alive. A nonzero second
   difference in Lift.Data or betas (both grow linearly), or any row off
   its closed form in section 1: my trace is wrong there; read that
   step's log.
2. The census: all drops, one index, in series, unfused: the "workload
   where drops pile up" that `pairing-fusion.drops.kernel` waits for
   (docs/plans/NetPairing_2026-10-26.md:257-262). Raises mixed with
   drops, or indices spread: accumulation of the kind only safe
   operators contain (:297-300), and drop fusion will not help.
3. `sp.by` by step: climbing by one per walk confirms H2's precondition
   and the 2^24 limit. Constant `by` with growing chains would mean the
   pile is not the unlowered application's missing drops, and H1's
   account of where they come from needs rereading.
4. Step k's log against step k + 1's, aligned by pair kind and by
   template node (which Ap, by its position in the copy: the copy
   allocates in template order, so base minus the first fresh base is
   the template index if allocation is contiguous; else carry the
   template index in a side table for the trace). H1: each of A1, A2,
   B1, B2, Fn c, FnD n, K's Fn t and FnD h is crossed exactly one more
   time at step k + 1 than at step k, and D_w and D_c each cross one
   more control.
5. No-op crossings: count the interactions in which a control crosses a
   leveled node and leaves its field unchanged. H1 predicts most
   crossings of cons's nodes are no-ops on the Church-built list, and
   about half overall on the literal. This number says how much a
   remedy that only skips no-ops could recover, against one that fuses.
6. The controls: run the same trace on (a) the Church-built list, where
   H3 predicts a different shape and H1 the same 12 with cons's fields
   constant; (b) the fold, to confirm chains of constant length; (c) a
   walk that recurses outside the lambda if one can be written (for
   example through a pair of selectors), to see whether `by` stays 0.

### Reading sizes 1 to 4

Sizes 1 and 2 are boundary: step 1 has no pile. The mechanism shows
first at size 2 (one LiftC and one Lift on the tail wire at the second
walk splice) and is unambiguous at 3 and 4, where the chains are 2 and
3. With exact rows predicted, sizes 0 to 2 are the cheapest refutation:
size 0 should be 9 (5 and the `++`), size 1 the column above. A row
that misses there names the step I traced wrongly; take 5 and 6 too.

### Cautions for the instrumentation

- The value table as a log is state the kernel's laws frame
  (glam/SPLICE_LAWS.bend's write sets): keep the measurement build in a
  worktree, as AGENTS.md's Measuring asks, with results/ symlinked.
- Prefer the histogram for the family at n, 2n, 4n; keep the full log
  for sizes 0 to 6, and check it changes no count.
- The census walk must read, not demand: it must not reduce pairs.

## 3. Where each hypothesis lives, and what a fix would cost

### Where

- The two static drops: `use_edge.k`, glam/lower.bend:258-263 (the
  `same` arm), from `job`, :299-306. Nothing else in these templates
  makes a control.
- The climb: `sp.by`, glam/splice.bend:44-52, reading the application's
  field; the raise in `sp.node`, glam/splice_copy.bend:64-69, through
  `V.raise_pay` (spike/val.bend:763). The need met at
  glam/core.bend:830-835 (`needed.e`, `ETpl`, `S.splice`) and again in
  frames at :913-922.
- The pile's growth: `rule.lift` on KFn (spike/rules.bend:499-502;
  rewrite `rw.Lift.Fn`, spike/krules.bend:1938-1951, and `rw.Lift.FnD`,
  :2023-2031) and `rule.ap` on KLiftC (rules.bend:428-432;
  `rw.Ap.LiftC`, krules.bend:1668-1681). Each copies the control onto
  every auxiliary wire.
- Why it stays units: `P.compose`, spike/kprim.bend:1162-1165, requires
  `off_up` of both; `V.compose`, spike/val.bend:821-829, the model.
- Crossing and cancelling: `rw.Lift.LiftC.yes` / `.no` / `.peeled`,
  krules.bend:1978-1992; `peel.amt`, kprim.bend:1341-1348, which peels
  raises only.
- The limit: `P.lvl_cap`, kprim.bend:36; `P.too_big`, :1878.

### Fix A (first choice if the census is unit drops at one index): drop runs in the kernel

This is `pairing-fusion.drops.kernel`
(docs/plans/NetPairing_2026-10-26.md:257-262), parked "for a workload
that shows drops piling up" (:254-256). This workload is that one, if
the census agrees. The model and two laws exist (:222-239).

What it buys, by H1's table (inferred): the pile on each wire is made
one control at a time in series, each new one linked beside the last
(`P.fuse` runs at those links, krules.bend:1670), so each wire holds one
run of amount about k. Then:

- Ap.LiftC, Lift.Fn, Lift.FnD: one crossing a node a step, not k. Eight
  of the twelve go.
- Cancellations: a run facing an equal run cancels in one; unequal
  splits peel once. Two of the twelve go.
- Crossings: the model's rule is that a drop run facing a control it
  does not equal gives up one unit at a time (:226-232). D_w at index
  k - 1 facing a run of k - 1 units at index 0 then still costs k - 1
  interactions a step. Two of the twelve stay: n² in place of 6n².

So drop fusion as modelled leaves a quadratic, six times smaller. To
remove it the crossing must take a run whole where that is exact. A
control at index m crossing p unit drops at index 0 ends at m - p and
meets its own index (the model's failing case, :227-229) only if
m < p; when m >= p no unit along the way equals it, so one crossing to
index m - p should agree with the units. Here m = p at every step
(inferred). That is a new rule shape: put it through
`spike/tools/ctlwire.py --drops` exhaustively before anything else, and
expect the clamp of `drops-stop-at-index` to matter exactly at m < p.

Cost to the laws (spike/LAWS.bend):

- `drop_units_are_run` (:127) and `drop_run_splits` (:137) hold over the
  model already; `runs_as_units` covers drop runs
  (NetPairing :234-238). These become load-bearing for the kernel.
- `raise_compose` (:323) is stated over `V.compose`: changing compose to
  admit drops changes what it claims, so it is a law changed on main,
  needing the maintainer's approval and a `Law:` trailer.
- `peel_pairs_units` (:147): peeling extends from raises to drop runs at
  any index (NetPairing :258-260); a new or widened law, with mutants.
- `lift_drop` (:199) and `raise_lift_drop` (:310) already hold for any
  amount (docs/decisions/drops-stop-at-index.md:27-30): untouched.
- `marked_unfused` (:341) must keep holding. Note what it implies for
  the live-source variant: a rewrite copies the control's form bits
  into the controls it leaves (`P.form(hb)` in krules.bend:1674, :1678,
  checked), so the descendants of a marked control are marked
  (inferred), and fusion refuses them (kprim.bend:1180-1185). A list in
  a live source may keep its quadratic after fix A. Check with the
  census: count marked controls in the pile.
- The `fusions-as-components` laws (:834 on) for the generated rewrite.
- `fuse-control-runs` (docs/decisions/fuse-control-runs.md:22-29,
  "Nothing else fuses until a safety criterion licenses it") needs
  amending or a successor; the whole-run crossing is a further rule
  beyond what the maintainer asked for on 2026-11-13.

Fix A leaves the climb: `by` and the runs' amounts still grow by one a
call, so a recursion 2^24 deep errors, and demand still walks each chain
(now of length one).

### Fix B: do not let the application go stale (absorb waiting controls at a splice)

The k - 1 LiftCs on Ap_K's argument and k - 1 Lifts on its result are
the right-hand side of Ap.LiftC, k - 1 times over. Reading the rule
backwards where demand stops at a leaf would lower Ap_K to level 0,
free the controls, and splice walk at `by` 0: no climb, no cap, and
walk's half of the cost gone at its source. cons's half remains (the
Lifts on the tail wire are not around an application of a leaf in the
same way on the literal, where cons_k really is k deep), so B wants A
beside it.

Cost: high. A backward rule is no interaction; its soundness is a
safe-operator argument (NetPairing :297-300), not in the model. It
changes what `sp.by` means (`templates-spliced-at-level`), touches L3's
premise (ii) in docs/reviews/LevelsFable_2026-11-12.md:22, and widens
the splice's write set, which glam/SPLICE_LAWS.bend frames exactly
(:17-26, :82-90): `nodes_keeps` and the links' frame law would need new
premises. I would not start here.

### Fix C: avoid the controls where a function needs none

`pairing-overhead.stratify` and `.lowering` (NetPairing :292-306):
neither template has a fan, so their drops only keep levels consistent
with nets that have. An unleveled template spliced into a leveled box
breaks L3's premise (i), so this is research, not a step; it is the
only remedy that would remove the linear overhead too.

Skipping no-op crossings is no fix: the control must still reach what
lies behind the node.

### Order

1. Histogram and census at sizes 1 to 6: an afternoon, and it decides
   between A and "accumulation needing safe operators".
2. If unit drops at one index: ctlwire.py with the whole-run crossing;
   then `pairing-fusion.drops.kernel` on a side branch with its laws;
   re-measure this family at n, 2n, 4n and the differential corpus.
   Predicted second difference: 12 now, 2 with drop runs, 0 with the
   whole crossing.
3. Add the shrunk walk (size 3 or 4) to `spike/library.txt` or
   `glam/ladder.txt` with its count, as the fault's regression.

## 4. What the docs already anticipate

- docs/plans/Cells_2026-11-09.md:143-144: "recursion through splices
  climbs a box at a time", given as the reason the raise is guarded. The
  climb was known; its cost in controls was not drawn from it.
- docs/plans/Cells_2026-11-09.md:2831-2844, `cells-recursion.depth`: the
  finding itself, with "the levels it raises, and the controls they
  bring" as first suspects. H1 sharpens it: drops, not raises; brought
  by the two croissants, not by the raise.
- docs/decisions/fuse-control-runs.md:42-45: "The loss sits where
  controls accumulate ... Recovering it is the safe operators' work".
- docs/decisions/drops-stop-at-index.md:31-33: "A drop by more than one
  now means something: b unit drops at one index, which drop fusion
  would make ... Drops still do not fuse".
- docs/plans/NetPairing_2026-10-26.md:239-256: drops met only 239 times
  in 357,956 interactions on the random corpus, so drop fusion was
  parked "for a workload that shows drops piling up". The random corpus
  has no recursion through templates; this family is the missing
  workload. :263-270 and :276-289 (`pairing-overhead.profile`): in the
  costliest terms "controls crossing controls (Lift·LiftC) make 45% to
  57%", "bookkeeping is 97%". H1 predicts a different profile here
  (crossings 2 of 12, Ap.LiftC 4 of 12), which the histogram can check.
- docs/decisions/templates-spliced-at-level.md:46-47: "A splice is no
  interaction: counts of interactions miss its cost"; and :14-19, every
  level raised by the application's level, the experiment this finding
  bears on.
- docs/decisions/lowering-uses-levels.md:22-25: "the controls'
  interactions are part of every count", and dropping levels where a
  function needs none "a later optimization".
- docs/reviews/LevelsFable_2026-11-12.md:22 (L3): the splice is right
  only if the application's level equals the net's root level after the
  controls the handle crossed. H1's Ap_K is the case where the controls
  wait at the application's auxiliaries and the application keeps its
  level: correct by L3, and the source of the climb.
Nothing I read states that a recursion through a lambda piles one
unfusable drop per call, or gives the 12 per step.

## 5. Checked and inferred

Checked in the code:

- the edge rule and where controls are emitted (glam/lower.bend:258-263,
  :299-306), FnD for an unused variable (:369-372);
- `sp.by` and the raise (glam/splice.bend:44-52,
  glam/splice_copy.bend:50-69);
- the rule table for Ap and Lift against Fn, LiftC, Data
  (spike/rules.bend:402-436, :489-513) and that the generated rewrites
  exist under those names (spike/krules.bend:1636, :1668-1681, :1714,
  :1938-1992, :2023-2031);
- only raises fuse (spike/kprim.bend:1162-1165); marked controls refuse
  fusion (:1180-1185); peeling peels raises (:1341-1348);
- the drop's arithmetic (spike/val.bend:697-721); the cap
  (spike/kprim.bend:36);
- the four counting sites (spike/kdemand.bend:239, :369, :598, :619);
- the law names and lines in spike/LAWS.bend and the frame laws'
  headers in glam/SPLICE_LAWS.bend.

Inferred, not observed:

- that the desugarer curries definitions and multi-argument lambdas;
- the whole hand trace: the order demand takes, which wire each control
  waits on, the chain lengths k - 1 and k, the indices all 0, the table
  by kind. Its totals match the measurement at every size and the
  one-step 20, which is evidence, not proof: an error that moved
  interactions between rows would not show in a total;
- that Ap_K is spliced at level k - 1 (I did not read
  `hello_recursion_levels.g` or its counts);
- the account of the fold's linearity;
- that controls descended from a marked control stay marked;
- every claim about what fix A saves, and the m >= p crossing rule,
  which no model has checked.

Not read: spike/kdemand.bend's walk beyond its counting sites,
glam/desugar.bend, spike/net.bend, the body of docs/Proving.md and
docs/BendIssues.md (required before any proof for fix A), and
docs/reviews/Levels_2026-11-12.md beyond a skim.
