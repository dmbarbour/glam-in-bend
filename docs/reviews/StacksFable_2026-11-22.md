# Raise stacks in the walk of an exponent-built list: advice (Fable, 2026-11-22)

The second reviewer's advice on `pairing-overhead.stacks`, by a Fable
sub-agent at 5868e59, kept as written; the maintainer asked for a
brainstorm, to pursue an obvious, simple remedy now or else record the
most promising candidates. Checked after by the agent: every raise
meeting a raise in the traces at 4 to 64 elements meets one equal to it
(4, 12, 44, 172 and 684 pairs, none unequal); the n = 16 stack moves
levels 0 to 40 exactly as `2+7` does; `ctlwire.py --peel --shapes 0,1
exhaustive 3 2 4` fails 552 of 154,350 starts; and an application
meeting a LiftC copies the control onto its argument (`rule.ap`,
`spike/rules.bend`), the tail here. The traces and the two model
scripts it cites (`ctlword.py`, `sortswap.py`) are under `results/`,
out of git: `results/trace/fix/` and `results/advice/stacks/`.

Advice only: nothing in the repository was changed but this file and two
model scripts under `results/advice/stacks/`.

**Short answer.** No: there is no obvious, simple, sound remedy. The stack
is a real word of unit brackets that no single run stands for, and ctlwire
shows that every cheap way of collapsing it reads wrong values. One remedy
is sound by construction (a control that holds the word, idea 1), and it
makes the walk linear, but it is days of kernel work, not hours.

Each claim below is marked **checked** (read at the cited place, or run)
or **inferred**.

## 1. The mechanism

### What your reading gets right

- The growth is in the four pairs you name. **Checked**, pair counts of
  `dnw_N.txt`:

  | n | Lift·LiftC | Ap·LiftC | Lift·Fn | Lift·FnD | all |
  |---|---|---|---|---|---|
  | 16 | 192 | 180 | 95 | 90 | 783 |
  | 32 | 553 | 532 | 272 | 266 | 2049 |
  | 64 | 1786 | 1748 | 881 | 874 | 6107 |

- The controls cross one at a time, and the copies cancel pair by pair
  after crossing a unit drop and two applications each. **Checked**,
  `dnw_16.txt` lines 440-480.

### Three corrections

**A period is one element, not two.** **Checked**: in `dnw_16.txt` each
period of the last phase is 41 lines, and there are eight of them for
elements 9 to 16 (lines 440, 481, 522, ... 727).

**The function crossed is the cons cell, not the walk's function.**
`cons h t` partly applied is `\c n -> c h t`: a `Fn` (c) over a `FnD` (n,
never used, so the dead kind) over two `Ap`. One period, lines 439-480 of
`dnw_16.txt`, reads (**checked**):

- 440-444: the stack `2+3 3+1 2+2 2+1`, then the walk's drop run `1-9`,
  cross `Fn[3]`, each leaving a `Lift` on the body and a `LiftC` on `c`.
- 446-450: the body's copies cross `FnD[3]` the same way.
- 445, 451: the walk's two applications beta the cell.
- 452-471: each `LiftC` on `c`, in turn, crosses the unit drop lowering
  put on `c`'s use (`Lift[3-1]`), then the two `Ap` of `c h t`, and
  cancels its twin under the `FnD`.

**The stack is not carried by a function into each beta: it is a pending
level shift of the rest of the list, pushed down the spine a cell at a
time.** `Ap x LiftC` leaves a `Lift` on the application's argument
(`rule.ap`, `spike/rules.bend` 421-426, **checked**). The second `Ap`'s
argument is the tail `t`. So line 454 (`Ap[3]@324 x LiftC[2+3]@464`)
makes the `Lift[2+3]@464` that line 481 puts across the next cell's
`Fn[4]`; 458 makes 482's `@56`; and so on (**checked** by base). The
head `h` gets a copy of every control too (the first `Ap`, `@256`),
never paid for only because this walk ignores heads. A walk that read
them would pay something for each control on each head (**inferred**:
one interaction each on data, more on a structured head).

So per cell, per control, six interactions: `Lift·Fn`, `Lift·FnD`, the
drop on `c` crossing the `LiftC`, `Ap·LiftC` twice, and the cancel. That
is the whole cost of moving one control past one cons cell, and the
literal list pays it too, for a stack of one.

### Where the stack comes from

**Checked** by listing every stack that crosses a `Fn` in `dnw_16.txt`
and `dnw_32.txt`. For n = 32:

| elements | raises crossing each cell |
|---|---|
| 1-2 | none |
| 3-4 | `5+1` |
| 5-8 | `4+2 4+1` |
| 9-16 | `3+3 4+1 3+2 3+1` |
| 17-32 | `2+4 4+1 3+2 3+1 2+3 3+1 2+2 2+1` |

The stack doubles at each power-of-two seam, by one rule (**checked**
on every row above and on the n = 64 stack): the next block's word is
the last block's word with one unit a level lower fused onto its front,
then the last block's word again, every index one lower. `4+2 4+1`
gives `3+3 4+1 | 3+2 3+1`, which gives `2+4 4+1 3+2 3+1 | 2+3 3+1 2+2
2+1`. The junction is never contiguous: the second half starts below
where the first ends, so no pair there is a run. Why: these are the
seams of `two g x = g (g x)`; the inner `g x` arrives through the outer
`g`'s parameter carrying its own pending raise, and the outer `g`'s
uses add theirs behind it (**inferred**; I did not trace the seam's
interactions). The
raise runs number n/4 on the last n/2 cells, n/8 on the n/4 before, and
so on: about n²/6 control-cell crossings, times six, is n² interactions.
At n = 64 the trace has 684 raise cancellations (682 predicted) and
6,107 interactions, 4,092 of them the raises' (**checked** count,
**inferred** split).

It is **not an artifact of where lowering places controls**. Lowering
emits one control per use, a single run or a unit drop
(`glam/lower.bend` 258-264, **checked**), and a list written out or
built by `cn` keeps single runs. The stack is assembled at run time, by
substitution through the exponent, and its shape records the order in
which the boxes were entered: inner first, then outer at the same
index. A different static placement would meet the same composition
(**inferred**).

### Two facts that decide the candidates

**As a map on levels the whole stack is one raise.** `2+3 3+1 2+2 2+1`
moves every level as `2+7` does, and the n = 64 stack as `2+31`: after
the first run every level above 2 is above every later index.
**Checked** for n = 16 (`ctlword.py replay`: levels 0..6 go to 0, 1, 2,
10, 11, 12, 13 either way) and for n = 64 (the 31 units against `2+31`
on levels 0 to 199, and `compose` folding the 16 runs to `(2, +31)`). The old fusion's
`compose` (`n1 <= n2 <= n1 + b1`) would fold either stack, left to
right, into that one control.

**No raise in these runs ever meets a raise it does not equal.**
**Checked** at every n from 2 to 64: `Lift·LiftC` pairs with both sides
raising are equal every time (4, 12, 44, 172, 684 pairs, none unequal).
Raises meet only their own twins, made at a `Lift·Fn`, and drops, which
they swap with.

Together: on this workload the quadratic is the cost of remembering a
split that no partner ever asks about. That is why fusing looks so
tempting, and section 2 shows why it is still not licensed.

The walk's drop also undoes the stack at once: each cell is raised by
n/2 - 1 and then dropped to level 1 by `1-k`. As maps, raise then drop
is one smaller drop. That is the raise-drop fusion (shapes 4 and 5)
`fuse-control-runs` withdrew.

## 2. Candidates, judged

Model runs are `python3 -I` under `scripts/capped.sh 2000 300`. The two
scripts are `results/advice/stacks/ctlword.py` (controls holding words)
and `results/advice/stacks/sortswap.py` (reordering); both import
`spike/tools/ctlwire.py` and change nothing in it.

### Idea 2. Fuse same-index and overlapping raises

**Idea.** Let `compose` take shapes 1 and 2 again, so the stack becomes
`2+(n/2-1)`: one control, linear walk.

**Sound?** No, not without a criterion nobody has yet. **Checked**:

- `ctlwire.py --peel --shapes 0,1 exhaustive 3 2 4`: 552 of 154,350
  starts fail. `--shapes 0,2`: 40 fail. Smallest: `C(0,+1) C(0,+1)
  L(0,+1)`, consumer at 1, ends at 2 unfused and at 1 fused.
- On the real stack (`ctlword.py replay`): the stack's `LiftC` copy
  facing a foreign `L(2,+1)`. The units leave `3 4 3 2 3 2`, which
  raises level 3 to 6. The composite `2+7`, peeled as the kernel peels,
  leaves `3+6`, which leaves level 3 alone. The composite has forgotten
  that its first unit at 2 is followed by another at 2 two runs later.

So the stack and `2+7` are equal as maps and different as words, and
one foreign raise at index 2 tells them apart. Fact two of section 1
says none arrives *here*; nothing local to the two controls says none
can.

**Could a criterion be found?** This is `pairing-overhead.safe-ops`.
From memory, not checked against the paper: Asperti and Chroboczek's
safe tag is lost by the copy that goes to a lambda's variable. Here
every control of the stack descends from such copies: the `Lift` on the
tail is made by `Ap x LiftC` from the variable-side `LiftC`, cell after
cell, long before the halves meet at a seam (**checked** in the trace
that the `3+2 3+1` of elements 5-8, n = 16, cross four cells before
joining the last block's stack). A one-bit taint would mark all of them
unsafe, and license nothing. What is true of them is finer: each
`LiftC` twin is dead by the time its `Lift` moves on. Tracking that
needs a count of live partners, not a bit.

**Changes.** `compose`, a safety bit or count in the control's offset
word, its upkeep in every rule that copies a control, new laws.
**Difficulty.** The rule itself is an hour; finding and trusting the
criterion is days, with a real chance of none. **Check first.** The
one-wire model cannot say where partners come from; it needs a tag per
control and the lambda's copying modelled, a larger model than ctlwire.

### Reordering into a canonical form (new, rejected)

**Idea.** Sort the units (`L(p) L(a)`, p > a, becomes `L(a) L(p+1)`:
the same map) and hope the sorted word is a few runs.

**Sound?** No. **Checked**, `sortswap.py 4 3 5`: 36 of 346,032
reordered starts end differently, each with a drop among the partners (all 36 read)
(`C(0,+1) C(0,-1) L(1,+1) L(0,+1)` against `... L(0,+1) L(2,+1)`). And
it would not have helped: the junctions are descending, and sorting a
descending pair does not make a run. The word's order is part of what
it means.

### Idea 4. Not copying the stack across the lambda

Fails on the mechanism. The copy is the payload: the tail needs the
shift, the head needs it, and the four nodes of the cell need their
levels moved. No rule lets an application climb past a control facing
the source, so the stack must cross the cell before the beta
(**checked**, `rule.ap` and `rule.lift` have no such case). At best it
could trim the constant, six per control per cell; I have no rule to
propose for that.

### Raise then drop into one drop (new, rejected)

The walk drops each cell to level 1 right after the stack raised it. As
maps, `2+7` then `1-9` is `1-2`. Shapes 3 to 5 do this, and fail in
ctlwire for the reason `fuse-control-runs` gives: the raise's partner
finds nothing to cancel (**checked** there, not rerun). Same missing
criterion as idea 2.

### Idea 3. Stratification at lowering

**Idea.** Type the term in elementary affine logic and box only where
the typing says; such terms need no controls.

**Judgment.** Split the program. The builder (`ck two (cons "") nil`)
is the textbook elementary term, and in such a typing a cons cell uses
`c` once and boxes nothing, so the list is flat and no stack forms
(**inferred**, from recall of Coppola and Martini, not checked). `walk`
is general recursion by splicing, which that logic does not type; it
would stay as it is. So this needs a mixed regime: inferred boxes for
part of a program, the general translation for the rest, and a sound
interface between them. That is a research step
(`pairing-overhead.stratify` is rightly tentative), **days to weeks**,
and it changes lowering, not the kernel. The one-wire model says
nothing about it.

### Idea 1. A control holding a word

**Idea.** Where two raises of one kind meet and may not fuse, join them
into one control that holds the word of both: a list of runs, in the
order crossed. It is a packed chain, and every rule on it is the
chain's rules run to the end in arithmetic:

- Crossing a function, application, fan or value: one interaction; the
  node's level moves by the word's map, the control is copied whole.
- Facing an equal word: both gone, one interaction.
- Facing a control whose index stays above every unit as it climbs
  (the unit drop on `c` here), or below all: they swap whole.
- Facing anything else: cancel the common prefix, or unpack into the
  chain it stands for and let today's rules run.

**Sound?** Yes, by construction: the word *is* its units, so nothing a
partner needs is lost. Modelled and checked: joining, crossing, and the
two facing rules below. Designed only, not yet in the model: the cheap
test for swapping whole, the map's summary, and indices kept relative.
**Checked**, `ctlword.py`, starts of up to three
controls (runs of 1 and 2, raises and drops, indices to 2, levels to
4), fusion by concatenation of any shape, outcomes and logical
interactions against the unit system:

- `norm` (two facing words reduced against each other in one move):
  0 of 360,600 fail; 0 of 3,000 samples of six controls.
- `prefix` (common prefix cancels, else one unit each is peeled):
  the same, 0 and 0.
- `stale` (equal words cancel, else swap by their maps, which is what a
  composite without its word must do): 45,100 fail. The check can fail.

For swapping whole there is direct evidence, not yet a rule:
`ctlword.py replay` puts the unit drop `L(3,-1)` against the n = 16
word, and it leaves the word as it was and comes out at 10, in seven
unit steps, as the trace does in four (lines 452-468: 3, 6, 7, 9, 10).

What the check pins: the orientation of equality (a `LiftC`'s word is
read from the consumer, so twins are equal as crossing orders, not as
wire orders), and that a prefix may cancel before the rest is looked at.

**What it buys.** Per cell the raise word costs six interactions and
the drop run six, whatever n: the walk is linear in interactions
(**inferred**; the one-wire model has no lambda to replay it on).

**Where the word lives.** A control uses all four words: header with
the index, two links, the offset (`spike/kprim.bend` 10-17, **checked**).
Two homes:

- *The data table.* The offset word, flagged, holds an entry; the entry
  is a Bend value, a list of runs with the map's summary `(n, +K)`. A
  copy shares the Bend value (`kprim.bend` 133, **checked** comment
  only). Simplest to build. But twins get different entries, so
  equality is a walk of both words: interactions go linear,
  instructions stay proportional to the stack per cancel (a compare of
  n/4 runs instead of 4·n/4 interactions: a constant of perhaps a
  hundred, not the order).
- *Cells in the node store, counted.* The offset word holds a reference
  to a chain of cells with a reference count; indices are kept relative
  to the header's, so a uniform shift touches the header alone. Twins
  share the reference, and equal references cancel at once. For
  instructions to be linear too, the word must also store the least
  index that swaps whole with it (one compare for the drop on `c`,
  which meets the word at every cell), or that test walks the word.
  More to build: a count to keep, cells the audit and
  the collector must know.

The map's summary matters either way: a `Lift·Fn` must not walk the
word. For any word `compose` once folded, the summary is one run.

**Changes.** A flag on the control (or two new kinds), the pack at the
link where fusion is tried now, the rules above in `rules.bend`,
`net.bend`, `kprim.bend` and the generated rewrites, erasure and
duplication of the word, the profile's logical count, laws (`word is
its units`; the whole-crossing test), mutants, library nets.
**Difficulty.** Three to five days for an agent, a guess: the model is
done in an afternoon, the kernel and its laws are the cost. The hot path pays a
flag test on control pairs only, as peeling does.

**Check first.** Extend `ctlword.py`: words as runs with relative
indices, the whole-crossing test as arithmetic, mixed raise and drop
words or raises only (decide by the model). Then the default bounds of
`drop-runs-fuse`.

### A cheaper cut of idea 1: twins only

Pack as above, but give the packed control just three behaviours: cross
a node, cancel a twin of the same reference, and otherwise unpack. No
prefix rule, no whole-crossing. It would not fix this walk: each
`LiftC` word meets lowering's unit drop on `c` before its twin, and
would unpack every cell. Whole-crossing is the least that pays here
(**checked** in the trace: 683 drop-raise swaps at n = 64, one per
raise per cell).

## 3. Verdict and next step

### Is there an obvious, simple, sound solution?

**No.** I am confident of that for everything that works by folding the
stack into fewer ordinary controls, and less sure only about one door.

- The stack is a word of unit brackets that differs from every run, and
  the unit system can tell: one foreign raise at its index (idea 2,
  shown on the real n = 16 stack), or a drop among the partners
  (reordering). Fusing, sorting and raise-drop cancelling are each
  simple, and each is refuted in ctlwire.
- Nothing about placement causes it. Lowering's controls are already
  single runs; the exponent composes them at run time.
- Not copying it is not available: the copy is the shift the rest of
  the list is waiting for.
- The one remedy that is sound without a criterion, a control that
  holds its word, is clear in the model and passes it, but is three to
  five days in the kernel, its laws and the generated rewrites.

The door I cannot close from here: a safety criterion that licenses the
old fusion on this stack. The trace says the stack never needs its
split, so a criterion that saw that would give the cheapest remedy of
all (one line in `compose`, one tag). My recall of Asperti and
Chroboczek's rule says their tag would be lost on every control of this
stack, but that is recall. **What settles it:** read their rule for the
lambda and the application, then replay the lineage of one stack
control in `dnw_16.txt` (say the `3+2` first seen at line 265) and see
whether it is still safe when the seam at line 429 puts it under
`3+3 4+1`. An hour or two. If it is unsafe there, as I expect,
safe operators are out for this workload and only a finer account
(live partners counted) could license fusion: research, not a build.

### What I would record in `pairing-overhead.stacks`

1. The mechanism as corrected in section 1: a pending shift of the
   list's tail, six interactions per control per cons cell, the stack
   doubling at the exponent's seams; one raise as a map, a word as
   brackets; raises meeting only their twins on this workload.
2. Refuted, with the runs: shapes 1 and 2 (552 and 40 failures at
   three controls), reordering (36 failures), and the n = 16
   counterexample for the composite.
3. Candidates in order:
   - **Word controls** (idea 1): sound, modelled
     (`results/advice/stacks/ctlword.py`), days. Whole-crossing by a
     control that stays above the word is required, not optional.
   - **A safety criterion** for the old fusion: cheapest if it exists;
     the one-bit tag probably fails here; settle by the reading above.
   - **Stratified lowering** of the builder: removes the stack at its
     source for elementary terms; a mixed regime, research.

### Next step I recommend

Do not build now. First count, as `AGENTS.md` asks before building for
a situation in the kernel: in a measurement build, count each link
where two raises of one kind meet and `compose` refuses them, over the
library and the differential corpus, and how long such chains get.
`fuse-control-runs` already hints the answer is not only this walk: one
random term in 600 carried 41% of the cost after fusion was narrowed,
25.8 times its old count. If refused pairs concentrate the cost there
too, word controls recover it and earn their days; if this walk is
alone, the plan's present line stands (glam's own lists, literal or
recursive, do not meet it) and the step can wait.

If it is built, the order is: `ctlword.py` extended to runs with
relative indices and the whole-crossing arithmetic, checked at
`drop-runs-fuse`'s bounds; the data-table home first, since it is the
smaller change and already makes interactions linear; shared cells
only if instructions per cancel then show in `scripts/count.sh`.

### Summary, as the repository asks

- **Did:** read the two decisions, the rules, lowering's `use_edge`,
  the plan step; classified every pair of the six traces; listed each
  stack crossing a function; wrote and ran two model scripts under
  `results/advice/stacks/`; ran ctlwire on shapes 1 and 2.
- **Judgments I am less sure of:** the six-per-control cost under words
  (inferred, no lambda in the model); that the builder is elementary
  and its cells then flat (recall); the safe tag's rule (recall); the
  split of n = 64's count between raises and the rest.
- **Ideas:** the `prefix` rule (cancel a common prefix before peeling)
  is checked and is the natural form of peeling for words. A summary
  `(n, +K)` beside a word keeps node crossings at one arithmetic step.
  A walk that reads heads should show the stack's cost on each head
  (inferred): a second sample worth having before sizing the remedy.
- **Next:** the count of refused pairs; the hour with Asperti and
  Chroboczek's rule; then decide between words and waiting.
