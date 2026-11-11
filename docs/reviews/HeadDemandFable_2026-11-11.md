# Head demand without fuel — 2026-11-11

Written by a Fable sub-agent on 2026-11-11 at the agent's request, on removing the fuel bound from head demand; kept as written.

The question (the maintainer, 2026-11-11): what removing the fuel bound from bounded head demand implies, "diverging in a few more cases, but predictably and controlled by user code" being preferred to a budget; and whether a body pass should serve needs. Repository claims carry their path; inferences are marked.

## 1. Which programs diverge, by trigger and depth

Head demand is the walk of `spike/kdemand.blend` started at a Fn's result port instead of the interface, following principals, rewriting pairs on its path, and stopping at the function's own variable (state 7 on a Fn on the path, `fw.scan`). Two choices decide which terminating programs it newly diverges on.

**The common-prefix argument, with its guarantee.** Beta links the Ap's result peer to the Fn's result peer and the Ap's argument peer to the Fn's variable peer (`rule.ap KFn`, `spike/rules.bend`). The result dominates the variable (`net-scoped-arguments`), so a walk from the result port meets the argument only at the variable; a rewrite is local to its pair and only relinks external peers, so every rewrite before the variable is the same for every argument. Hence the WHNF walk of any demanded application `h a` is beta, then head demand's walk up to the variable, then work depending on `a`. Head demand's walk is a prefix of every demanded application's, and diverges only where every demanded application diverges. The argument covers rewrites, needs, reflection tasks and stuck pairs alike: they lie on the same path in the same order.

**Depth.** The walk meets a nested Fn at its own interface in `\x -> \y -> B`. Stopping there is WHNF of the body, the prefix of `h a`. Entering it is HNF through binders, the prefix of `h a b`, a saturated application that `h a` does not promise. So HNF through binders newly diverges on every partial application taken as a value and never saturated: `(\x -> \y -> Ω) 1` stored in a dict, a CPS continuation built and dropped, a callback never called. Ordinary programs; this depth must not be the default. It buys no sharing either: a nested body sits behind a cursor and positioned demand reduces it once when the nested function is first applied (section 2).

**Trigger (a): eagerly, when a function-valued cell's task ends.** With WHNF of the body, the pass newly diverges only on a function forced but never applied, whose head diverges before touching its argument. A cell is forced when demand stops needing its handle at an application or a strict call (`may_need` in `spike/kdemand.blend`: an Ap or an Op meeting a handle), or when the cell is a demand's root result (the Cells plan, "The model proposed"). The class is then a strict builtin given a function (I could not verify that any builtin is strict in a function argument; `net-error-values` leaves an operator stuck on a function, inference: such builtins are rare or absent), an annotation that sequences evaluation, or a function returned and inspected without application. Small, and user-visible: "a forced function evaluates its body as if applied to an unknown argument".

**Trigger (b): the first demanded application.** With WHNF of the body, no terminating program diverges: the pass is the prefix of the application that triggered it. Section 2.

**Trigger (c): a user annotation.** Divergence is the user's: section 3.

**The named examples, under (b) with WHNF of the body.**
- `\x -> \y -> Ω`: stops at the nested Fn; a value, as `h a` is.
- A never-applied function in a dict: never triggered; under (a), only if forced without application.
- `f y = f (g y)`: `f a` diverges under WHNF; head demand diverges the same way, in the source (section 2 on how it is reported).
- `\x -> x + Ω`: applying the builtin makes an Op whose principal is on the first argument (`rule.ap KData`); the walk reaches `x` and stops, `Ω` untouched. `\x -> Ω + x` diverges, as every application does.
- A reflection task independent of the variable: on the prefix; emitted when an application is demanded, never without one.
- A need on another cell, `\x -> c + x`: forced by every application; forced by the prefix.
- Mutual recursion `f x = g x; g x = f x`: diverges as `f a` does. `even`/`odd` by cases on `n`: strict in the variable; the pass stops at once.
- A function applied but its result never demanded: the Ap is on no path, the cell is never forced, the pass never runs.

Under (a) each reads the same with forcing for applying; under HNF depth the first diverges.

## 2. Head demand as a prefix of the program's own demand

**It is positioned demand.** Under live templates a copy takes the source's finished nodes and leaves a cursor at each unfinished position; demand at a cursor is a task on the source from that position (`copy-reduced-function-nets`; the Cells plan, `cells-freeze.cursors`). A body is unfinished wherever its head is an application or operator, so the first copy's beta leaves the copy's root facing a cursor at the Fn's result port in the source, and the copy's demand there is exactly the walk of section 1. Head demand triggered by the first demanded application, to WHNF of the body, is therefore not early evaluation: it is `net-demand-whnf`'s demand started at a position, reaching the frontier once for every copy. No fuel is needed because nothing is speculated; `early-evaluation-optimization`'s "under fuel" is left to the eager trigger and the deeper depth, which do speculate. The only freedom is timing: run the walk *before* materializing the Fn (call it b'), or after, when the cursor's demand arrives. Both do the same rewrites; section 4 gives why b' is cheaper.

**Needs.** Every need on the prefix is one the application's own walk meets, in the same order: a Func cell's leaf, spliced where it stands (`templates-spliced-at-level`); a Recipe cell, forced on the needing task's chain; a reflection task, emitted. So the maintainer's question, whether a body pass serves needs, becomes *when*: in the pre-materialization pass, or by the cursor's demand a moment later. Outcomes agree either way. Splices must be served by whichever does the work, since nearly every head in glam code is a top-level name and a pass stopping at leaves would reduce nothing; only cost is measured (section 4).

**Reflection tasks.** Emitted at most once per source position, and only because a copy demanded them. One consequence belongs to live templates and head demand surfaces it: a task inside a body that does not depend on the parameter lies on the shared prefix, so it is emitted once per *function* under live templates, once per *application* under today's whole-template splices, which copy the annotation node each time. Evaluation cannot tell (`docs/DistilledDesign.md`, Annotations); reflection's log can. If per-application emission is wanted, a reflection node is a frontier for the source's walk: never reduced in a source, materialized into each copy. The same question applies to `'scope_unique` minting (`bounded-duplication`, its open question).

**Cycle detection, and its granularity.** Two findings.

First, a true divergence through the source's own template is reported as a cycle under live sources and as out of fuel under whole splices. `f y = f (g y)` applied: the walk at position P, the Fn's result, meets the leaf for `f`, materializes `f`'s finished part into its own source, and beta links P's peer to the new Fn's result peer, a cursor to P. The task at P needs P: a cycle on its own chain (the Cells plan, item 6), cached as an error. Under `cells-splice.templates`, the built mechanism, the splice copies the template whole, the walk unrolls without end, and the run ends out of fuel, never cached (`machine-limits-not-errors`). Both are acceptable: item 6 holds that an error for a cycle is sound while errors cannot be caught, and DistilledDesign rules divergence unobservable; the cycle is the better diagnostic, a refinement of the same bottom. The detector is exact (inference): a walk at P blocked on a cursor to P can proceed only with P's own value.

Second, busy must be per *position*, not per source. Take a fold `len = \xs -> xs (\x -> \r -> 1 + len r) 0`. The walk at P_len stops at `xs` at once. The inner lambda is finished, copied; its body is behind a cursor at P_c, inside `len`'s source. The first copy's demand at P_c meets `+`, then `len r`: the leaf for `len`, spliced, beta, and a cursor to P_len, another position in the same source, whose walk terminates at `xs`. With one demand task per source (CursorsFable, question 4) and item 6's ancestor test, P_c's task re-entering a busy source on its own chain would report a cycle where WHNF terminates. So a cursor's position carries its own state, Recipe, Busy with owner, materialized, as a cell does, with the ancestor test on positions. This is the finding most likely to change `cells-freeze.cursors`.

The kernel's own cycle, state 5, is a vicious circle of principals each facing an auxiliary port, detected when the path repeats and nothing changes (`spike/kdemand.blend`); it is a wiring deadlock, independent of these.

## 3. Predictability and user control

**What a user can reason about without annotations.** Under trigger (b) with WHNF of the body, the rule is one sentence: applying a function evaluates its body as if to an unknown argument, up to the first use of the argument, once and shared by every application; the rest is per application. A program diverges exactly where call-by-need diverges. Sharing changes cost and space, never which programs terminate. A reflection task on the shared prefix runs once per function or once per application, whichever the maintainer decides (section 2), and never without an application. That is the whole contract; fuel would have added "unless the prefix is longer than a budget, in which case it is shared later and with fewer fusions", which no user can plan around.

Under live templates fuel's unpredictability was in fact smaller than the earlier review said: it would have bounded *when* the prefix is shared, not whether, since what the pass leaves reduces once at a cursor anyway (`copy-reduced-function-nets`). Its cost was marks and cursors, not duplicated work. Removing it removes a knob with no semantic content.

**Annotations that ask for more.** Each makes the user responsible for divergence it may add, which is the maintainer's "controlled by user code":
- `anno 'hnf f`, or `'head N`: evaluate through N nested binders, or all, when the function is forced. Diverges on `\x -> \y -> Ω` forced. For partial applications whose saturated head is known to terminate and whose prefix is expensive.
- `anno 'eager f`: run head demand when the cell's task ends, without an application; and as a spark where tasks exist (`bridge-parallel`). Diverges on a forced, never-applied function with a divergent head.
- `anno 'nf x`: full normal form, into operators' and applications' arguments; never into a merge's sides, which the consumer's rule distributes. EvalSpike's `spike-materialize` is the precedent `net-demand-whnf` cites.
- `anno 'per_application f` or the reverse, if reflection emission is to be chosen per function rather than globally.
- `anno 'strict` on an argument stays what it is; it does not interact.

**What must not be a configuration knob.** Depth and trigger decide which programs terminate, so they belong in the program, as annotations, never in `conf.*`: a build that terminates on one machine's configuration and not another's breaks "same sources, same binaries" in the only way worse than a wrong binary. Timing, whether the walk runs before or after the first materialization, and any bound on how far a *spark* runs, change cost only and may be configuration, as `bounded-duplication` allows for its heuristics.

**Diagnostics.** With no fuel, a long prefix shows as a long first application, which is what the program asked for. The cell protocol already slices work under the run's fuel (the Cells plan, "What cells must give": out of fuel ends a slice and the cell stays busy), so the walk must be resumable across slices as demand is today (`KS.resume`, `spike/kstrat.bend`), and a runaway shows up as a cell or position busy for many slices, which a report can name.

## 4. Costs

**Work moved into the source.** The prefix's rewrites, the splices on the head path and the materializations they imply are done once in the source instead of once per copy. Under live templates this happens with or without a pass; the pass only moves it before the first copy. `\x -> g 1000 + x` computes `g 1000` once in the source, which is what HeapModel wanted lowering to hoist (`docs/plans/HeapModel_2026-10-27.md`, "Local reduction before freezing"); `\x -> x + g 1000` reaches the variable first, and `g 1000` is reduced once anyway, at a cursor, by the first copy whose operator meets it.

**Wasted work.** None under trigger (b): every rewrite is one the triggering application makes. Under (a), the forced-never-applied class of section 1. Under HNF depth, every unsaturated partial application's body.

**Retention.** What the prefix builds stays in the source as long as the source lives, for every copy: a shared prefix that builds a large structure, `\x -> bigList ++ x`, keeps it. This is GHC's full-laziness space leak (confident prior art: floating argument-independent expressions out of a lambda shares them across calls and retains them). It belongs to live templates, not to head demand, and the fix is the same as GHC's: an annotation to opt a function out of sharing its prefix, or a collection that frees a source's residue when no copy can reach it (`store-collection`).

**Copying, cursors and marks: why the pass runs before materializing (b').** Under plain positioned demand the first copy takes the Fn and the lift under its variable, which are finished, and marks the lift (`copied-controls-unfused`). The walk at the result position then ends at that lift, the frontier, and its last rewrites link to it; fusion at those links is refused, so every later copy takes an unfused run of controls at the frontier. Under b' the walk runs before any copy exists, nothing is marked, and the fused control is what every copy takes. Inference, to measure: count fusions refused in the first walk on the sharing families with and without the pre-pass. The pass also leaves the first copy with fewer cursors, as the earlier review counted; nothing else differs.

**Source growth.** Each callee on the head path is materialized into the source once, and a recursion through the frontier unrolls once there (section 2's fold). Bounded by the prefix's length, which is the program's.

**Time.** The first application pays the prefix; it would have anyway. Later applications pay materialization of a larger finished part instead of rewrites; the splice blind spot applies (`cells-freeze.sharing`: a splice is no interaction), so count copied nodes beside interactions.

**What to measure.**
1. *Exact prefix, as a law of the differential run.* On `terms.py`'s random terms, for each function-valued subterm: head-demand-then-apply against apply alone give the same value, and the same interaction count up to the root's crossings of LiftC (`rule.root` rewrites what the pass walks through). A difference is a bug, not a cost; shrink it into `spike/library.txt`.
2. *The finished fraction and marks.* On `glam/sharing.txt`'s families at 1, 2, 4 and 8 uses: finished nodes, cursors, copied nodes, fusions refused, with b', with plain positioned demand, and with whole splices. `closed_work.g`'s 147 interactions a use should fall toward the linked 19 under both live forms; b' should show fewer refused fusions.
3. *Needs, when.* The same families with needs served in the pre-pass against deferred to cursors: interactions and copied nodes must agree; time and the number of tasks or waits may not.
4. *Retention.* Peak nodes of the source over the uses, on a family whose prefix builds structure; this decides whether an opt-out annotation is needed early.
5. *Library entries.* `f y = f (g y)` applied, expecting a position cycle under live sources and out of fuel under whole splices; the fold of section 2, expecting termination and no cycle; `\x -> Ω` forced without application, expecting a value; `\x -> \y -> Ω` applied once, expecting a value; a body with a reflection annotation applied twice, expecting the decided count.

## 5. Recommendation and questions

**Recommendation.** Drop the fuel, and change the trigger with it. Head demand runs when a function-valued source is first applied with its result demanded, before its finished part is materialized: the walk from the Fn's result port, to WHNF of the body, through LiftC, serving splices, needs and reflection tasks as the application's own demand would, stopping at the variable, at a nested Fn or a Merge facing the position, and at nothing else. So defined it is demand at a position, not early evaluation, and `early-evaluation-optimization`'s fuel clause does not apply to it; nothing in `net-demand-whnf` changes. Eager head demand (at a cell's task end, or as a spark) and deeper depth (through binders, full normal form) are early evaluation; they need no fuel either, but an annotation, so that the programs they add to the divergent set are the user's choice. "A few more cases, predictably, controlled by user code" is then exact: zero more cases by default, each annotation naming its own.

The earlier review's extra stops go with the fuel: no stop at a splice of the source's own template (it is either the program's own divergence, reported as a cycle, or a legitimate re-entry at another position), no stop at needs, no stop at reflection tasks, each of them on the prefix of the demanded application. What remains is positioned demand with a position-level busy state, which `cells-freeze.cursors` needs regardless.

**Decisions worth recording now.**
1. Head demand triggered by a demanded application is demand, not early evaluation; `early-evaluation-optimization`'s fuel is scoped to eager and deeper passes, which are requested by annotation.
2. A cursor position carries the cell protocol's states, and a cycle is a position needing itself on its own chain; a busy position on another chain is a wait.
3. Where a reflection task on a function's shared prefix is emitted: once per source or once per application.

**Questions for the maintainer.**
1. Is a function ever forced without an application, by a builtin strict in a function argument or by an annotation? If not, trigger (a) and trigger (b) coincide, and the eager annotation can wait.
2. Per-position busy state, with item 6's ancestor test on positions: agreed? It decides CursorsFable's question 4 against one task per source.
3. A reflection task inside a body, independent of the parameter: emitted once per function under live templates, or kept per application by treating it as a frontier? The same for `'scope_unique` minting.
4. Should the pre-materialization pass serve Recipe needs, waiting on other cells before the first copy exists, or stop at them and let the first copy's cursor serve them? Same outcome; the measurement of section 4, item 3, decides the cost.
5. An opt-out annotation for sharing a function's prefix, against the retention of section 4: wanted at once, or after measurement?
6. Does `anno 'hnf` through all binders, with the user owning divergence, cover the partial-evaluation cases the maintainer had in mind, or is a depth-N form needed?

<!-- end -->
