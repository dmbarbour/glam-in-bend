# Demand for copying and fusion — 2026-11-11

Written by a Fable sub-agent on 2026-11-11 at the agent's request, as a second, independent opinion on demand for copying and fusion; kept as written.

The question (the maintainer, 2026-11-11): whether demand should continue through a bind or a control, "demand flows through negative aux", to support partial evaluation of function bodies; and what demand through a fan would mean. Claims from the repository carry their path; inferences are marked as such.

## 1. What demand does today, by polarity

The walk is `spike/kdemand.blend` (`wk.q`, `wk.down`, `wk.pair`, `wk.root`). It starts at the interface, the Root, whose one port is negative, and at each step reads what the path's last node's principal port faces, `q`:

- `q` is an auxiliary port: the node behind it is pushed and the walk goes on from that node's principal (`wk.down`, `dn.can`). Every principal the walk follows is negative, so `q` is positive: an output. **Demand enters a node by an output and leaves by its negative principal.**
- `q` is a principal port: a pair. It is rewritten unless its rule leaves it (`KR.stuck_by`), or it is an application or strict call meeting a lazy handle, a need, state 2 (`may_need`, `nd.lz`).
- the interface itself faces a principal: a LiftC is crossed by the root's rule (`wk.root.go`, kind 11; `rule.root` in `spike/rules.bend`), an EraP is a void, state 8; anything else is done, state 1.

By kind, from the port table at the top of `spike/rules.bend`:

| kind | principal | outputs | how demand meets it |
|---|---|---|---|
| Ap | − ap | + result | entered by result, left by ap |
| Copy, CopyL, CopyR | − input | + left, + right | entered by an output, left by input: the shared value is forced once |
| Op | − arg | + result | entered by result, left by arg |
| Lift | − in | + out | walked through |
| EraN, DOp, Root | − | none | never entered |
| Fn | + fn | + arg | by fn: done at the interface, else the B of a pair; by arg: state 7 |
| FnD | + fn | none | done, or a pair's B |
| Merge, MergeL, MergeR | + out | none | done at the interface ("a superposition reads as none", header comment), else a pair's B |
| LiftC | + out | none | crossed at the interface; a pair's B elsewhere |
| Data, EraP | + | none | the value; a void |

Demand never enters a node by its principal. It stops at the interface facing any positive principal but a LiftC's. Fn is the only kind with a positive principal *and* a positive auxiliary port, so state 7, "a variable demanded outside its function's body", is exactly "the walk entered a Fn by its variable", found by `fw.scan` as the earliest positive-principal node on the path (checked at a stop, not per push: the per-push check cost 1.5% to 5%, header comment).

Stuck pairs (`stuck_of`, `test_by` in `spike/krules.bend`): rule 0, a pair with no rule, always; three rules (1, 3, 8) when a payload test fails, beta at unequal levels and applying data that is not a builtin among them (`rule.ap` in `spike/rules.bend`); I did not read `rule_no`'s table to name the third, nor verify the rows for the linear kinds (`FnD`, `MergeL`, `MergeR`) against every negative kind. None of the tested rules is a control's: a Lift facing a LiftC is peeled, not tested (`test.k`'s header comment).

Off the path nothing is reduced: pairs and erasures elsewhere stay (`net-demand-whnf`; header comment, the maintainer 2026-10-28). The collection relies on the walk never stepping forward through an output's consumer except at a Fn's variable (`net-scoped-arguments`).

**On the maintainer's wording.** Under `spike/rules.bend` the application's principal is negative (`−ap`), and demand walks through applications every day; the node whose principal is positive is the function bind, Fn. If "ap" names the application node, the polarity is the other way round here; if it names the position of the applied function, it agrees. "Demand stops on a bind (lam)": yes, at the interface, and only there. "And on some control nodes": I found no control at which demand stops. A LiftC facing the interface is crossed, a Lift on the path is walked through, and every pair of a control with a base kind has a rule (`rule.lift`, `rule.ap KLiftC`, `rule.copy KLiftC`, `rule.op KLiftC`). What looks like a stop at a control is the lift the lowering puts under a variable (`glam/lower.bend`, header; its principal faces the variable side): demand walks through it to the bind's variable port, and stops there with state 7.

## 2. Demand through a negative auxiliary port

The tweak is the dual of today's move. Today the walk enters a node by a positive auxiliary port and leaves by its negative principal. The tweak enters a node by its positive principal, from the interface or a position, and leaves by a negative auxiliary port: the node is passed as a value's constructor rather than reduced. That is a read-back walk interleaved with reduction, the shape of Lamping's and BOHM's read-back (I believe), and "demand flows through negative aux" describes it exactly. By kind:

| kind reached by its principal | port followed | what it means | new stop |
|---|---|---|---|
| Fn | − result | demand the body under the binder | its own + arg: a head variable |
| FnD | − result | the same, no variable | none |
| LiftC | − in | pass a control, offset recorded | none; no Root to cross it, so a walk-through, not a rewrite |
| MergeL, MergeR | − in | a wire with a fan identity | none |
| Merge | − left, − right | both sides of a superposition | section 3 |
| Data, EraP | none | the value; a void | as today |
| Ap, Op (for full normal form) | − arg | demand the arguments too | full normal form |

Following Fn's result only computes **head normal form**: the walk stops when the head of the spine is a variable, data, or a need. Head reduction is normalizing for terms that have a head normal form (the standardization theorem; confident). Following Ap's and Op's inputs as well gives full normal form.

**What the walk sees under a binder.** From Fn's result port the peer is either a principal (data, an inner Fn, which the walk enters in turn, a Merge) or an output of an Ap, Copy, Op or Lift, entered as today. The walk is the ordinary walk with the result port as its interface. Reaching a Fn's `+arg` is a head variable if that Fn is on the path, else state 7 as now; the test is a scan of the path at the stop, as `fw.scan` already does, so it costs no per-push check. A shared body is handled by the rules: in `\x. x y` copied twice, the Ap meets the Merge of the two variables (`rule.ap KMerge`), is copied onto each side, and each copy's Ap then faces its own Fn's variable. The collection's invariant survives: the walk stops at `+arg` and never passes forward through `+fn`.

**The common-prefix argument** (my inference). Beta links the Ap's argument peer to Fn's `+arg` peer and the Ap's result peer to Fn's `−result` peer (`rule.ap KFn`). So the WHNF walk of any application, after beta, is the same walk body-demand makes from the result port, up to where it meets the variable. Head-demand under a binder therefore reduces exactly the pairs every demanded application of that function must reduce; it is wasted only if the function is never applied and demanded. Under copying it moves per-copy work into the source, done once.

**Costs and risks.**

- *Termination.* `f y = f (g y)` has a WHNF, `\y. f (g y)`, and no HNF: head-demand splices `f`'s template under its own binder without end. HeapModel foresaw it: "Local reduction before freezing reduces build-only pairs only, never calls (reducing a call there could unroll recursion without end)", the Rust bound 4 reductions a node, 256 nodes (`docs/plans/HeapModel_2026-10-27.md`, "Local reduction before freezing"). So body-demand is never the semantics: `net-demand-whnf` keeps `\x. loop x` a value, and `early-evaluation-optimization` admits deeper reduction only under fuel, stopping before a reflection task. A cheap extra stop: no splice of the source's own template, or a splice budget.
- *Needs.* A body may meet a lazy handle, state 2. Serving it forces another cell ahead of demand, a wait on another task (`bounded-duplication`'s context). I would not serve needs in a body pass: leave the Ap facing the handle; it becomes a cursor and is served when a copy's real demand arrives.
- *Reflection.* A task `meta_refl` emits must not be emitted early (`early-evaluation-optimization`); the pass stops before one, as it stops at a need.
- *Duplication.* Driving fans in a shared body makes structure, not work, per copy, which copying makes anyway. Work is never duplicated: the source reduces once.
- *Work never needed.* Head-demand is still demand-driven: `\x. K 0 expensive` reduces to `\x. 0` without touching `expensive`. Only full normal form would evaluate arguments nobody needs. The waste is a function never applied, which fuel bounds.
- *Levels.* Pairs inside a body lie at the body's level and beta tests levels agree (`rule.ap KFn`, `test.k` 1); the lifts under variables are walked through. I expect no new mismatch, but the differential test should say so (section 5).

## 3. Demand and fans

**A Copy, reached from an output.** This is today's case and it is what sharing means: the walk enters the copy by the output it needs, follows the input to the shared provider, forces it once, and when a value's principal arrives at the copy's input the pair fires: data is shared (`rule.copy KData`), a function is split into two with a copy on its body's result and a merge of the two variables (`rule.copy KFn`), a merge annihilates or commutes by identity (`rule.fans`), a LiftC is passed with the control copied onto both outputs. Nothing changes here under either tweak. Note that the walk then returns to the Fn it was entering by and, today, stops: a copied function is split on demand but its body is not entered. Body-demand would enter the split function's result, meet the body's copy fan, and go on: Lamping-style lazy copying driven by the read-back, which is right.

**A Merge, reached by its positive principal.** A Merge takes a value from each side and hands a superposition to its consumer. In the walk's terms demand never *reaches* a merge: its `+out` faces a consumer, and it is the consumer's rule that distributes over the merge, copying the consumer onto both sides, an application (`rule.ap KMerge`), an operator (`rule.op KMerge`), a control (`rule.lift KMerge`), a copy (`rule.fans`). So the walk already does the right thing with a merge inside a net: it forces whichever side the consumer's copy then needs, one at a time, as it needs it.

"Demanding both sides" would mean entering the merge by `+out` and walking down `−left` and `−right`: normalizing both branches of a superposition. That is right only when the consumer is strict in the value whichever branch it comes from, which is exactly what the distribution rule gives without any new strategy; in every other case it is speculation on both sides of a duplication, work one branch may never ask for. I would never demand through a merge's inputs. HVM, I believe, does normalize both sides of a `SUP` under its full `normal` mode, because superpositions are values there; glam has no superposed value in its design (`docs/DistilledDesign.md`), so there is nothing for a user to read from one.

**At the interface.** There is no Root–Merge rule (`rule.root` is LiftC only), so a merge facing the interface ends demand with state 1 and the result reads as none. In a well-levelled closed net I believe a fan-in cannot reach the root; where it does, the net's sharing is unbalanced, as in the dead function's merge `kstrat.bend` describes ("A function's principal, the function reached by its variable alone", lines 607 to 620), or a user's hand-built net. I found no library entry (`spike/library.txt`) that expects a superposition at the root. As `net-void-demanded` did for voids, I would make a superposition demanded an outcome of its own, so that it is reported, not read as a value with no data.

**With and without levels.** Levels decide only whether two fans annihilate or commute and what controls do when they cross a merge (`rule.lift KMerge`: the merge passes with its level adjusted, the control copied onto each wire behind it). The walk's path through a fan is the same either way; what differs is how many control interactions it pays (NetPairing's counts, `docs/plans/NetPairing_2026-10-26.md`, `pairing-gal`).

**Other meanings.**

- *Driving the fan's propagation.* A copy fan facing a function is driven exactly as far as demand pulls: split at the Fn, then the body fan moves only when a copy's result is demanded. Body-demand pushes it one spine further. The two-stack strategy (`kstrat.bend`, "Two stacks") does the opposite, deferring every pair that grows; it is the eager strategy's concern, not demand's.
- *Choosing a context.* Which side of a merge is wanted is decided by the consumer's rule, not by demand; a strategy that chose a side would have to know the consumer's strictness, which the rule already encodes.
- *Speculation as a spark.* The other output of a copy, or the other application after a merge is distributed, is a natural spark: a task on that port, ahead of demand, under `early-evaluation-optimization`'s stops (fuel, no reflection, no need served). It never changes an outcome and competes only for the source's one demand task (the Fable cursors review, question 4, `docs/reviews/CursorsFable_2026-11-10.md`).

## 4. Live templates, cursors and fusion

**Positioned demand.** A negative cursor sits at a finished node's input whose peer is an unfinished node's output (`docs/plans/Cells_2026-11-09.md`, `cells-freeze.cursors`; `docs/reviews/Cursors_2026-11-10.md`, C2). Demand from it is today's walk with that input port as the interface: enter the unfinished node by its output, follow principals, rewrite pairs. Its stops are simpler than the root's: a value's principal facing the position is finished structure to materialize, a LiftC, a Merge or a Fn included, so nothing is crossed and the root rule is not needed; a need is a wait; stuck and cycle are errors.

**The frontier.** With finished as the fixpoint (the interface's principal tree, both cursors reviews), a residue node's principal never faces a finished node's auxiliary port, or it would be finished. So a walk from a cursor meets finished nodes only after a rewrite links a pair's peers to finished ports, the cursor positions. The identity shows the simplest case: beta links the Fn's result to its variable, aux to aux, and the walk from the result port enters the Fn by its variable, state 7. But it is wider than Fn (my inference): in `\x. f x x` a Copy whose input faces the variable is finished, and once `f`'s beta links a use of `f`'s own variable to that Copy's output, a residue Op whose principal is that output enters the finished Copy, climbs through it to the variable, and ends in state 7 as well. Every such climb ends in state 7 or facing the source's Root, since finished nodes never pair, so the stop needs no per-push test: at the stop, scan the path for the earliest finished node, as `fw.scan` scans for the earliest positive one. That position is where the walk's result meets the copy; whether the copy joins a placeholder it holds there or materializes new structure is its own table's call, since "finished" and "held by this copy" differ when a node became finished after the copy was taken (finishedness is monotone, so it only grows).

What the scan needs is a finished set per source. A bitmap, a word per 32 nodes as the collection's marks are (`kstrat.bend`, "The walk"), built by the finished-fixpoint walk and extended at each materialization, fits; the header has no free bit for this on every kind, since fans and functions use a form bit for `unlev` and data uses both (`spike/kprim.bend`, header; `P.unlev`). Only controls have both form bits clear, which is what `copied-controls-unfused` relies on.

**What deeper demand buys.** Run the bounded head-demand of section 2 on a function-valued cell's net when its task ends, before the first copy is taken. Then:

- the head spine of the body reduces once in the source; the Aps along it come to face the variable through its lifts, so they join the finished tree;
- cursors are fewer: `\x. (\y. y) x` becomes a wire, `\x. (g c) x` with `g c` closed becomes finished structure, no cursor, no anchor;
- the frozen part is larger, and the copy's own demand after application starts where the source's left off, having already done the common prefix.

Its costs: fuel spent on functions never applied; a long head spine unrolled through template leaves (bounded by the splice budget); and the source grows by what the reduction builds, which a copy would otherwise build in its own net. Nothing is lost in sharing: a pair reduced before any copy exists reduces once, as a pair in the residue reduces once by a cursor's demand; only the moment differs.

**Fusion and the marks.** Fusing after a rewrite in a source can fold a new control into a finished one a copy already holds; `copied-controls-unfused` marks copied controls and refuses them. Head-demand before the first copy sets no marks, so fusion is free during it, and the Cells plan already notes that fusions done while a cell is forced are harmless (`cells-freeze.fusion`, "Which nets"). This is also the maintainer's condition for boundary nodes being acceptable: "if a source were driven by demand before anything is copied". After copies exist, positioned demand's rewrites link to cursor positions and fusion at those links meets marked controls and refuses; a control finished but not yet copied is unmarked, and fusing into it is sound, since no copy holds it. The only interaction to check: head-demand run on a source that *already* has copies must respect the marks like any other rewrite, which it does if it uses the chain's `after` as demand does.

**Anchors.** Body-demand never passes forward through `+fn`, so a copy's argument never enters the shared source through demand; the positive cursor, the anchor, stays in the copy, as both reviews proposed and the maintainer wished ("I'd hesitate to modify the source nets").

## 5. Recommendation

Three strategies, one walk, differing in where they start and where they stop.

| strategy | start | stops | status |
|---|---|---|---|
| WHNF demand | the interface | a positive principal but a LiftC's (value, function, void, superposition); need; stuck; cycle; state 7 | the semantics (`net-demand-whnf`); as today, with a superposition made an outcome of its own |
| positioned demand | a cursor's position in a source | a principal facing the position: materialize; a finished node entered: frontier, join or materialize; need: the copy's task waits; stuck, cycle | needed by `cells-freeze.cursors`; the state 7 reinterpretation, wider than Fn |
| bounded head-demand | the interface, then each Fn's and FnD's result, through LiftC and linear merges | a head variable (the Fn on the path); need, not served; a reflection task; a splice of the source's own template or the splice budget; fuel; never into a Merge's sides or an Ap's argument | an optimization under `early-evaluation-optimization`, run on a function-valued cell when its task ends, before the first copy |

Do not make head-demand the semantics, and do not compute full normal form anywhere: a function with no head normal form is a value, and arguments nobody needs are the user's to leave. Do not demand through a merge's inputs; the consumer's rule distributes. Serve needs only under real demand.

**Cheap experiments.**

1. *The finished fraction.* Once the finished-fixpoint walk exists, count on each family in `glam/sharing.txt` (`closed_work.g`, `partial_in_cell.g`, `partial_in_net.g`, `data_in_cell.g`) the finished nodes, cursors and anchors of the function's net, with and without head-demand before the first copy, at 1, 2, 4 and 8 uses. The ladder's check already compares interactions and splices; add the two counts. Head-demand earns its keep if `closed_work.g`'s 147 interactions a use fall to the linked 19 with no cursor left.
2. *The common prefix.* On `terms.py`'s random terms, for each function-valued subterm, compare head-demand then apply and WHNF against apply and WHNF alone: the same value, and the first's interactions never more than the second's plus the fan interactions the merge distribution adds. `spike/tools/differential.sh` records every term; a disagreement is a level or scoping case to shrink into `spike/library.txt`.
3. *Divergent heads.* Library entries for `\x. f (g x)` with `f y = f (g y)`, and for a body whose head is a strict call on the variable: the first must stop by the splice budget leaving the function a value, the second at the variable at once.
4. *A superposition at the root.* Grep the differential store for runs where demand ended on a Merge, and run the ladder with the new outcome: if nothing reaches it, it costs one test; if something does, it was a silent wrong answer.
5. *Marked controls under head-demand.* Run head-demand on a source after a copy was taken, on `partial_in_net.g`, and check with `copied-controls-unfused`'s mark that no fusion touches a marked control; this is the one order in which the two features meet.

**Questions for the maintainer.**

1. In "demand cannot enter a port with a positive principal (ap)", does "ap" name the application node, whose principal is negative in `spike/rules.bend`, or the applied function's position? Is the Rust bootstrap's polarity the dual of the spike's?
2. Head-demand as an optimization only, with WHNF the semantics: agreed? Then a function with no head normal form stays a value and fuel is the only guarantee.
3. Where does the fuel come from: an annotation on the function, a global budget, the Rust bootstrap's 4 reductions a node and 256 nodes, or a profile-tuned heuristic as `bounded-duplication` allows?
4. Should a body pass serve needs, forcing other cells ahead of demand, or stop at them as I advise?
5. A superposition reaching the interface: an outcome of its own, as a void is, or a value with no data as today?
6. The frontier test as a finished bitmap per source, scanned at the stop, rather than a header bit on every kind: acceptable, given the form bits are taken on fans, functions and data?
7. Sparks on the other side of a fan, under the same stops as early evaluation: wanted now, or after cursors?

<!-- end -->
