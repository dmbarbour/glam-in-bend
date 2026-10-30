# Evaluator Spike — 2026-10-26

Find out how well Bend 2 hosts glam's evaluation before committing to a
representation: lazy, shared evaluation through monadically constructed
interaction nets (Design.md, "Interaction Nets"), on the split heap
(`split-heap`, `store-pages`) run in rounds (`rounds-of-coarse-work`).
Approved by the maintainer 2026-10-27, after a revision following their
first reading; skip a step (and its dependents) and say so here if it
sprawls. Paused the same day after `spike-net-rules`, for
[NetPairing](NetPairing_2026-10-26.md). The code lives in `spike/`, with
its own `LAWS.bend` and `PROOF.bend`. The code is throwaway; what it
learns becomes decision records. How fans pair has a plan of its
own, [NetPairing](NetPairing_2026-10-26.md).

## Known (2026-10-26, Bend 2.0.39, native unless noted)

- A scattered `Array<U32>` read and write costs about 1.5 ns; the JS target
  is 3–5× slower.
- `pure_hvm5_mini`, an interaction-calculus evaluator in Bend, runs about
  14M interactions/s on one thread.
- Array indexes wrap silently: that demo answers wrongly, without error,
  once its live cells outgrow its fixed environment.
- The checker takes about 0.5 s for 3K lines; a native build about 1 s.
- Bend has no laziness and no shared mutable state outside `@unsafe` forked
  arrays; the maintainer chose the split heap (the
  [architecture sketch](Architecture_2026-10-26.md), "The store").
- Pages of a store can be owned linearly by parallel workers in safe Bend:
  2.3–2.7× on this 4-core machine with cache-sized pages, 8–19 µs a round
  (the sketch's "Pages and rounds").
- A parallel call reached deep inside a task still runs in parallel: eight
  branches, each forking only after sequential work, ran 3.7× faster on 8
  threads than on 1; a fork tree at the surface, about 5.5×.
- An array cell of a small constructor costs 4 bytes for one `U32`
  field, 8 for two, 16 for three (`Bool` counting as one); in a sum type
  with a variant holding a list, as the store's payloads are, every cell
  costs 32 bytes whatever its variant holds (2026-10-27, 1M to 4M cells,
  linear). So shrinking one variant saves nothing there; a control, with
  two ports, could instead keep its index and offset in its node's free
  fourth word.
- Bend generates no code at run time. In-process fast paths are therefore
  specialized loops (an HVM5-style interaction loop, operator steps); a
  heavy, stable kernel could also be compiled out of process and run
  through the shell, as an accelerator.

## Questions

- Throughput and memory of glam's own node set (Bind, Copy N, Data, eraser)
  as a Bend step machine, against the hvm5 baseline.
- Whether the split heap holds up: ground data as Bend data; lazies,
  function nets and non-ground structure nodes in the store; marking that
  visits each non-ground node once and grounds what has been forced.
- How lazy fields inside data meet net sharing: memo cells in the store, or
  ports shared through `Copy` fans.
- How logical copies work over pages, after the Rust bootstrap's cursors: a
  copy materializes its source frontier by frontier, and a source pair
  reduces once, in its source, for every copy.
- When a net, or part of one, has no evaluation left, and how compactly it
  can then be held: like a forced thunk, as ground data outside the traced
  heap, copied whole without handle indirection, or compiled to operator
  steps.
- **Fixpoints**, the maintainer's chief worry: what object knots, recursive
  binding groups, recursive functions and `.fix` cost, and how recursion
  avoids unfolding through fans.
- Which nets, or parts, an HVM5-style interaction loop could run faster:
  the lowest-level fast path in-process.
- Where parallelism hides inside tasks, and how it reaches the cores:
  nested parallel calls within a worker, or new tasks for the coordinator.
- What growing the store costs, and whether laws guard capacity, linearity
  and free-list conservation cheaply.
- What rounds recover in parallelism for real evaluation, and which
  heuristics (round length, placing pages and tasks, when a needed thunk
  becomes a task of its own) serve it best.

## Steps

The core:

1. `spike-net-store` — the store as pages: cells in fixed-size `Array`s,
   a free list per page, handles of page and slot in one `U32`, growth by
   adding pages. Laws: allocation stays in bounds; allocating and freeing
   conserve cells.
   Built 2026-10-27 (`spike/store.bend`, `spike/bench_store.bend`). Laws
   `alloc_conserves` and `free_conserves` hold of the allocator's own
   metadata, a free list and `Nat` counts. "In bounds" got runtime guards
   instead: Bend cannot prove even `h & 4095 < 4096`, its `U32` facts
   being bit-level, so numeric laws must be stated over `Nat` models.
   Measured (1M nodes, native): allocate and write a node's four words
   76 ns, read 9 ns, free 14 ns; linear to 4M. Accessors cost 10–15 ns
   against 1.5 ns raw, rebuilding the store record each time: batching
   work on the current page is the obvious fix. Freed slots in old pages
   are not reused yet, since allocation draws only from the current page.
2. `spike-net-rules` — Bind, Copy, Data and eraser interactions as one
   fuel-driven loop over a stack of active pairs, fans paired by complete
   duplication histories (`pairing-histories`). Laws: a rewrite keeps
   every live port wired exactly once, and keeps the net polarized
   (`pairing-polarity-law`).
   Built 2026-10-27 (`spike/rules.bend`, `spike/net.bend`,
   `spike/tpl.bend`, `spike/test_net.bend`). Rules are data, a recipe of
   new nodes and links per kind pair, which the reducer interprets; laws
   `rules_polarized` and `rules_linear` hold of that table, so polarity
   and linearity are proven of the rules that run. Fans meet as copy
   against merge, the only polarity-compatible pair. Externals that are
   ports of the redex itself (the identity function's result wired to its
   own argument) are joined through the rule's links. An application
   meeting a builtin (`succ`, `add`) becomes a strict call node, its
   principal on the argument: it computes once the argument is data,
   distributes over a superposed argument (two calls, their results
   merged under the argument's fan identity) and passes an error value
   on, by rules in the table under its laws. It was first a list of calls
   polled until their arguments were data, which had no answer for a
   superposed argument: every pairing scheme then seemed to halt with no
   value.
   Found: identity, K, a function used twice and an n-fold chain reduce
   correctly. Where a fan duplicates a live function that holds fans,
   pairing decides the answer (native, 2026-10-27): extending both fans'
   histories on commutation, as the Rust bootstrap does, diverges on every
   Church exponentiation, `two two succ 0` included; static labels, one
   per lowering site and instantiation, are right on `m n succ 0` for
   distinct numerals (27 interactions for `two two`, 99 for `three
   three`) and diverge on self-application `(\t -> t t) n`; extending
   only the inner fan's history is right on all of those and on
   `(\t -> t t) two`, wherever a test-specific oracle could name the
   inner fan. Two meeting fans do not show which is inner; GAL's levels
   record it ([NetPairing](NetPairing_2026-10-26.md)). glam's own
   lowering may avoid the question: a function is data, copies share it,
   and each call instantiates a fresh net with a fresh fan namespace, so
   `spike-lowering` tests that. The spike has paired by static labels
   since, and `spike/trace.bend` traces its reductions
   (`pairing-trace`). The reducer works every active pair, needed or
   not: `K 5 (#3 #3 #3 succ 0)` grinds on the argument K discards.
   Reduction driven by demand, as glam's evaluation is, remains to be
   built, perhaps eager for erasure (the maintainer); `spike-lazy-data`
   meets it at the latest. One of 600 random terms still runs out of fuel
   this way under fused levels.
   Also found: allocating in whatever page was focused opened a page per
   allocation once reduction focused full pages (2944 pages for 5000
   interactions, gigabytes, a crashed session); allocation now tries the
   current page, then an allocation page, then a new page.
3. `spike-node-layout` — nodes as the maintainer pictures them, after
   Victor Taelin's earlier nets: four `U32` words, the first holding the
   kind and the level (24 bits), the other three references to ports
   (two low bits for the port) or, in nodes with fewer ports, an index
   into a data table or a word of metadata (a control's offset). Payloads
   shrink to that data table, the only part reference counted; fan sites
   become a debug side table, serials a tracing one. And a fast path that
   keeps the laws: the rule table stays the specification, and the
   rewrites that run are either Bend's specialization of the table's
   interpreter or code generated from it, checked against it on the
   test corpora. First, a benchmark on one workload and one rule set:
   the table interpreter, dispatch on the kind pair with each rule a
   constant, and rewrites written by hand, at n, 2n and 4n.
   Benchmarked 2026-10-27 (`spike/bench_rules.bend`, the variants in
   `spike/tools/rewrites/`; i7-6700, Bend 2.0.39, native, best of three).
   The workload, `k 2 succ 0` built by hand, takes 131K, 262K and 525K
   interactions at k 16, 17, 18, 84% of them calls computing or
   distributing over merges. Per interaction:

       k    table    constants    by hand    by hand, no checks
       16   0.97 us  1.02 us      0.80 us    0.83 us
       17   0.98 us  1.00 us      0.59 us    0.62 us
       18   0.98 us  1.01 us      0.61 us    0.64 us

   Values and interaction counts are identical in all four, and all
   scale linearly. Bend does not specialize the interpreter when handed
   a constant rule: dispatching on the kind pair gains nothing. Rewrites
   written by hand are 1.6 times faster; done for real, they would be
   generated from the table and checked against it, so the laws keep
   covering what runs. The level assertions and fusion checks cost
   nothing measurable. What remains, about 0.6 us an interaction against
   `pure_hvm5_mini`'s 0.07, is the store and the interaction's own
   reads: accessors that rebuild the store record each time, and boxed
   payloads. That is the layout this step is for, measured next the
   same way.
   Then the layout, as `spike/kernel.bend`: one flat page of four-word
   nodes, the header holding the kind and a 24-bit field (a level; for
   this workload's hand-built nets, a fan's site, which pairs them the
   same way), data and a call's function inline in spare words, free list
   and active pairs as arrays, the nine rules written by hand in the
   table's order. It reduces the workload step for step as the spike
   does (identical values and interaction counts at every k), at about
   40 to 60 ns an interaction after some 40 ms spent allocating its
   arrays (56 MB): k 19, 1.05M interactions, in 99 ms; k 20, 2.1M, in
   121 to 145 ms, against 2.1 s for the table interpreter and 1.3 s for
   hand-written rewrites on the paged store. That is
   `pure_hvm5_mini`'s speed, 15 to 20 times the interpreter's. Past its
   capacity (2^21 nodes or active pairs, at k 21) it reports errors and
   no value, as it should. It too rebuilds its eight-field state record
   at every access, so that is not what made the store slow; the paged
   store's focus switching and the boxed payloads are left. Still to
   come in this step: the rewrites generated from the rule table rather
   than written by hand, so the laws keep covering them; levels,
   controls and fusion in the kernel; a net as a value in the heap,
   taken whole by the worker reducing it; a data table, local to the
   net, for values that do not fit a word.
   Allocating incrementally (the maintainer's suggestion): the kernel's
   words, free list and active pairs now sit behind one storage interface
   with three implementations, preallocated (`spike/kmem_flat.bend`),
   doubled when full (`kmem_grow.bend`) and paged, 4,096 nodes a page in
   a page table, pages made as needed, one held out as the focus
   (`kmem_paged.bend`); `spike/tools/kmem_run.sh` times them. The heap
   here peaks at about 2^k nodes (pending calls in a chain), so it does
   grow. Best of three, results identical throughout:

       k    flat           doubling       paged
       4    40 ms, 56 MB   0 ms, 0 MB     0 ms, 0 MB
       18   89 ms, 56 MB   52 ms, 16 MB   119 ms, 5 MB
       19   106 ms         118 ms, 32 MB  205 ms, 10 MB
       20   143 ms         208 ms, 64 MB  424 ms, 20 MB

   Both incremental forms drop the start-up; paging needs the least
   memory, close to the 16 MB a million nodes take, but costs about four
   times as much an interaction. Not for page switches: pages of 4K to
   1M nodes, even one page holding the whole heap, take the same time.
   The cost is on every access: the page check and the extra layer of
   calls, several nanoseconds each in Bend against 1.5 for the array
   access itself; a five-field storage record alone, padded flat, costs
   45 of the 280 ms. So the page check belongs outside the per-word
   path: a rewrite checking once that its nodes lie in the focused page,
   then working on that page's array directly. The maintainer chose
   doubling (`net-nodes-double`): a net is a value in the heap, usually
   lazy, reduced by one worker at a time, so its nodes need no pages of
   their own, and the median net is small. The kernel now doubles.
   Rewrites generated from the table, 2026-10-27. The kernel's
   primitives are in `spike/kprim.bend`, with a data table local to the
   net, a value word holding a number below 2^31 inline or else an
   index. `spike/kernel.bend` interprets `R.rule` on the layout, as the
   reference and for redexes joined through their own ports, and
   otherwise runs `spike/krules.bend`, which `spike/tools/gen_krules.bend`
   writes from `R.rule`: the rewrites, and tables of ports and
   polarity by kind code. `scripts/check.sh` fails if `krules.bend`
   differs from what the generator writes, and `terms.py --kernel`
   writes a differential test. On 1,200 random terms, 600 with levels
   and 600 without, the generated rewrites match the interpreted table
   exactly, in value, interactions and errors, and every value matches
   the spike's; without levels the interaction counts match the spike's
   too, with levels about three in four differ, the spike fusing
   controls the kernel does not yet. At k 20 the interpreted table takes
   1.27 s, the generated rewrites 0.35 s, the hand-written ones 0.21 s:
   those kept numbers inline and called `succ` directly, where the
   generated steps pass ten context parameters each and call builtins
   in general. Tuning that is left for later. Counted with `perf`
   (`scripts/count.sh`): 1,376 user instructions an interaction for the
   generated rewrites, 5,190 for the interpreted table, exactly linear
   at k 18, 19, 20 and the same to eight digits from run to run.
   Next, the maintainer's directions (2026-10-27):
   - Immediate data told apart by the header's kind, not a flag bit,
     using as much of the node as common values need: a data node's
     words 2 and 3, 64 bits or two values, beside the header's 24.
   - The data table kept linear: each entry owned by one node, so it is
     freed or handed on as soon as its owner is reduced. A rule using a
     source's payload once hands the entry over; using it twice
     duplicates it (the Bend value shared, as Bend does); not using it
     frees it; computing frees both inputs.
   - The payload test that compares levels stays written by hand: perhaps
     the best there is, to be watched.
   Built the first two the same day. The header's kind code holds the
   rule kind in its low 4 bits and the value form in its high 4: 0 an
   entry in the table, 1 a number, 2 a builtin with no argument yet, its
   op in the field. A data node keeps its value in words 2 and 3 (word
   2 so far). The table has a free list, and the generator counts how a
   rule uses a data node's or a call's payload: the first use takes the
   entry over, a later one duplicates it, none drops it, computing takes
   both; the interpreted table does the same as it goes. `terms.py`
   gains a curried builtin, `plus`, and `--plus`, ending terms in
   `(plus 1) 0` so that a partial application is an entry the copies
   share, and the kernel checks at the end that the live entries match
   the nodes holding them (a duplication broken on purpose is caught).
   On 2,400 random terms, with and without levels, ending in either:
   no difference between generated and interpreted, none in value from
   the spike, no mismatch in the table. The generality costs 1,547
   instructions an interaction against 1,376 before.
   Tried and dropped: a reference to a data node's principal carrying
   port 3, so that nothing links into a data node and all three words
   hold its value. It cost 55 instructions an interaction (1,602 against
   1,547) for room glam does not need yet; the maintainer chose 64 bits
   without it. Of the rest, the linear table's duplicating step costs
   84 (on the 42% of interactions that distribute a call over a merge,
   immediate values included) and value forms the other 87. Folding
   the duplication and the computing into one primitive each cost 110
   more, not less: Bend charges for function layers, which pass the
   state record and return pairs, at around a hundred instructions each,
   while a comparison or an arithmetic step is native and costs about
   one. Fewer, larger functions on the hot path are the tuning to do.
   Tuning so far: the state keeps how many nodes and active pairs fit,
   so allocating and pushing check a counter and call the storage only
   to grow it: 1,488 instructions an interaction, from 1,547. Profiling
   showed the general compute path (rebuilding a builtin's value from
   its form, `V.apply_fn`, a `PW` record, one more layer) costing about
   475 instructions a compute; `succ` on an inline number done directly
   brought the whole kernel to 1,348. Builtins on immediates are to run
   natively, a few operators specialized by header, their arity implied
   by the op so that a call's spare word can hold a collected argument
   (the maintainer). And workers cost nothing here: on 1, 2, 4 or 8
   threads the kernel runs the same instructions, within 20, and the
   same cycles within 1%, since it does not fork; the cost of more
   workers is the barrier per round where work forks (`Known`, above).
   Free lists made intrusive, one at a time, against a second workload,
   `k 2 (plus 1) 0` (`kernel <k> plus`), whose partial application is a
   table entry every copy duplicates and every call consumes. First the
   nodes': a free node's word 1 links the next, the state keeps only the
   head, the separate stack and its capacity gone: 1,328 instructions an
   interaction on `succ`, from 1,488, and 1,703 on `plus`, from 1,869.
   Then the data table's: a freed entry holds `VNum{next}`, the one swap
   that takes a value out leaving the link in its place, and the one swap
   that puts a value in returning the link: 1,674 on `plus`, 1,313 on
   `succ`. `succ` never touches the table; its 15 come from the compiler
   splitting functions differently (the profile's shares of `run`,
   `interact` and `kprim_apply` moved by several points each), so the
   table's own gain is about 14 an interaction on `plus`. The wrapper
   costs nothing measurable: a constructor with one `U32` field packs.
   The audit's live count now walks the free list. The link then got its
   own constructor, `VFree{next}`, never a glam value, so that a scan can
   tell a free entry from a live number: the audit also checks that the
   free list holds every `VFree` entry, none leaked off it nor freed twice.
   About 1.5 instructions an interaction on `plus`, none on `succ`.
   Builtins on immediates then ran natively: a value form 3, a builtin
   needing one more argument after one number (the field its op, the word
   the number), and a builtin of form 2 or 3 meeting a number computed by
   `V.num1` or `V.num2`, the arithmetic `V.builtin` itself now calls, with
   no Bend value built: 1,192 on `succ`, from 1,313, and 1,193 on `plus`,
   from 1,676, its partial application no longer in the table. Against the
   Python evaluator's values too, the kernel agrees on every term with
   levels but one that runs out of fuel everywhere, as before.
   Then levels, checks and fusion, so that the kernel reduces what the
   spike reduces step for step. A fan, function or application built
   without levels carries value form 1, which the rewrites keep, so that
   the checks pass it by; fans pair, and an application meets its
   function, when form and field agree. Both paths make the spike's level
   checks but one: a copy meeting a function at a level not below its
   own, and a control raising a level or an index past the field's 24
   bits (the spike's own check of a lift meeting a liftc missed one side,
   now fixed). The check that two fans meeting at one level share a site
   needs the site, which a leveled fan here does not keep. The generator
   writes each pair's check into its rewrite and the same table as a
   `check` for the interpreter. After its links, each rewrite tries to
   fuse its new controls and the external peers it joins, in the spike's
   order (`P.fuse`, net.bend's fusion on this layout); the interpreter
   tries the spike's own `fuse_tried`. Interaction counts now equal the
   spike's on all 2,400 terms, leveled ones included (459 of the 600
   leveled differed before), and on `kernel <k> lvl`, a new workload:
   `k 2 succ 0` built with levels as terms.py lowers `#k #2 succ 0`
   (`X.t_pow_lvl`). The loader counts an error for a level, site or
   index past 24 bits or an offset past 31, which the header would cut
   short, and a builtin whose op does not fit the field goes to the
   table; `spike/test_levels.bend` exercises each check and guard.
   What fusion buys, against the same build with `P.fuse` a no-op, at
   k 18 on the leveled workload: interactions 1,573,450 to 1,180,272
   (-25%), nodes at most 524,295 to 393,225 (-25%), instructions 1,617M
   to 1,373M (-15%), time 180 to 151 ms; an interaction costs more,
   1,163 instructions against 1,028, for the attempts. On the 506 random
   terms all three modes get right, fusion cuts the kernel's interactions
   from 195,330 to 122,574 (-37%): levels cost 2.76 times the
   interactions of static labels, against 4.40 without fusion at run
   time (2026-10-28: the random terms' cut rested partly on fusion that
   is wrong in other orders; the leveled workload's fusions all remain,
   NetPairing's `pairing-fusion`). The attempts cost nothing measurable
   where nothing fuses: 1,181
   instructions an interaction on `succ` and 1,182 on `plus`, slightly
   fewer than before them, the compiler's splitting moving again. The
   leveled workload costs 2.25 times the interactions of `succ` and 2.2
   times the instructions. Bend 2.0.39, i7-6700.
   Then where to try fusion (the maintainer's observation): a new node's
   principal faces outward and its auxiliaries face new nodes of another
   kind, so a rewrite can newly join two controls only on a link it makes
   with an external end, or between two new controls of one kind. Each
   such link is now tried once, from its external end (`N.fuse_ends`,
   computed from the rule table for the generator and the interpreter
   alike), where both sides of every candidate node were tried before.
   The other sides were old links, fusable only when another fusion in
   the same rewrite had changed them, or when the template was loaded
   so. On 600 random leveled terms that lost one fusion, two interactions
   in one term; retrying at the link each fusion makes recovered it and
   found nothing else, at 1.2% more instructions on the leveled workload
   than before; a pass fusing the loaded template found nothing, terms.py
   emitting fused controls. Kept: one try per link, no retry, no pass, in
   the spike too, so counts still match. On the leveled workload
   (k 18), 1,373M instructions to 1,324M, the same interactions; on the
   unleveled ones half the tries on beta and fan joins, yet 0.5% more
   instructions, within the compiler's variation between builds.
   Skipping fusion and checks for a net without controls, as a second
   rule set chosen when it loads, was measured by generating the rewrites
   without them: 0.6% more instructions on all three unleveled
   workloads. What tries cost is below what a build varies by; whatever
   a net known to lack levels gains will come from larger transforms of
   it, not from leaving these out.
   The data table had dropped out of every workload once builtins on
   immediates ran natively, so a third builtin, `fma` (a * b + c), puts
   it back: `k 2 (fma 1 1) 0` (`kernel <k> fma`) holds a partial
   application with two numbers, too many for a node, which every copy
   duplicates and every call consumes; terms.py's `--fma` ends random
   terms so. It costs 1,944 instructions an interaction against 1,188 on
   `succ`, about 1,500 more a call.
   Where the cost goes. Bend passes a record's fields one by one through
   every function that takes it, and the kernel's state flattened to 20
   words, the two store records (4 words each) and the data table's (5)
   among them: each word cost about 30 instructions an interaction. The
   stores became bare arrays (the state already kept their capacities),
   and the rest left the flat state step by step: the table and the error
   count into one cold record, which a recursive variant (never built)
   keeps Bend from flattening, so it travels as one word and is opened
   only to use the table, count an error or grow; the interaction count
   too, now taken from the run's fuel; the pair stack's capacity, since
   an active pair holds two live nodes and a node is in one at most, so
   the stack grows with the node store and a push checks nothing; and
   the fresh-node mark and node capacity, since growing now threads the
   new nodes onto the free list, so making a node is a pop. Five words
   remain: the two stores, the free list's head, the pair count, the cold
   record. Reading a pair's six words in one pass of the store
   (`m_get6`), to cut layers, cost 1.6% more and was dropped.
   Bend leaves inlining to clang, whose heuristics flip with small
   changes: each word removed after the ninth made the default build
   slower (by up to 17%, `link` and `node` left out of line), while a
   build of the emitted C with every compiled Bend function forced
   inline (`spike/tools/inline_build.sh`) got faster each time. At k 18,
   instructions as `bend` builds / forced inline:

                       k 2 succ 0      k 2 (fma 1 1) 0   with levels
       start (ac8869c) 623M / 535M     1,020M / 918M     1,324M / 1,100M
       9 words         428M / 400M     813M / 753M       916M / 823M
       5 words, kept   449M / 363M     810M / 710M       964M / 721M

   Growing the stores is 14 to 18% of that (62 to 67M at k 18), most of
   it zeroing new arrays, which Bend fills word by word at 8
   instructions a word (`bench/bend/zero_fill.bend`); without it an
   interaction costs 716 instructions, 541 forced inline. A primitive at
   a time (`spike/bench_kprim.bend`, forced inline, against 85 for a bare
   word read): an immediate number's put and take cost nothing more, a
   native apply about 100, a table read 130, a put and take 230, a
   duplicate and drop 300, whether an entry is a function 215, and
   `V.apply_fn` alone 500. An `fma` call's extra 1,300 or so is a
   duplicate (300), the function check (215) and the general apply
   (about 630, `V.apply_fn`'s list building most of it). `perf annotate`
   printed nothing for these binaries; `spike/tools/hotins.py` joins
   `perf script`'s samples with `objdump` instead.
   The pair stack then kept one node of each active pair, the other being
   its principal port's peer (the maintainer's observation): half the
   stack, a write less a push, a read more a pop, from the node store; at
   k 18 on `succ` 447M as built, 355M forced inline (449M, 363M before).
   The stores start at 256 words, 64 nodes and 256 pairs, and double up to
   2^23 and 2^22 words; at k 18 the node store reaches 2^21. Doubling's
   cost is the last doublings', so a larger start would save little;
   growing faster was not tried. Profile-guided builds, clang inlining by
   a training run's profile (`spike/tools/inline_build.sh` given training
   runs, here k 14 on all four workloads), at k 18, millions of
   instructions:

                              succ    fma     levels
       as bend builds it      447     809     963
       forced inline          355     702     712
       profile-guided         363     691     835
       both                   348     670     711

   Bend's JavaScript output, run by Node 20, took 2.0 s at k 18 against
   40 to 70 ms natively, and did not follow the native changes: the
   narrower state ran slightly slower there (1.8 s at the start), so it
   checks portability, not native cost. gcc 14 cannot build Bend's C,
   which needs `musttail`.
   The table path then, judged across the four builds. A builtin given
   its last argument no longer appends it to the collected list for
   `V.builtin` to match again: `V.builtin_last` matches the collected
   arguments where they lie (a law, `builtin_last_agrees`, proves it
   computes what `V.builtin` does on the appended list): `V.apply_fn`
   from about 500 instructions to 150, `fma` at k 18 from 809M to 722M
   as built and 702M to 619M forced inline. Duplicating an entry opens
   the cold record once rather than twice (`tab_dup`): 712M and 599M.
   A form marking entries that hold functions, so that applying one
   needs no table read, lost again (worse in three builds of four), and
   was dropped. An `fma` call now costs about 870 instructions more than
   a `succ` call in the best build, from 1,300: the table's operations
   themselves and the check that the entry is a function. At k 18,
   millions of instructions:

                              succ    fma
       as bend builds it      458     712
       forced inline          355     599
       profile-guided         355     582
       both                   343     571

   GCC 16.2 (built from source, `scripts/gcc-setup.sh`; it has
   `musttail`) builds the same C 25 to 35% slower: `succ` 517M -O3, 460M
   forced inline, 453M forced inline and profile-guided (GCC's profiling
   cannot instrument around `musttail` out of line). Bend's C is written
   for clang: without `preserve_none` its out-of-line steps take the
   usual calling convention. It serves as a second opinion.
   What the table's remaining cost was. Holding the cold state in the
   table's own first slots, as packed values, so that no table operation
   opens a box, ran slower in all four builds (`fma` 604M against 571M in
   the best), so the box stays. A profile of `fma` (forced inline) found a
   quarter of all instructions in Bend's handling of shared values:
   `term_drop` 11%, `span_fade` 8.6%, `blk_keep` 5.1%, against under 0.2%
   on `succ`. Every copy of `fma 1 1` shares one boxed `VFun`, a table
   read keeps it (a count up), and matching a shared node copies its
   fields, bumping each boxed one, then drops it: the `VFun`, then each
   cell of its argument list. So a builtin given one or two numbers now
   goes into the table flat, as `VP1{op, need, a}` or `VP2{op, need, a,
   b}`, constructors of plain fields that `V.apply_fn` applies directly;
   they are never glam values, and `V.norm` turns them back into the
   `VFun` they stand for, which the kernel does to every value it hands
   out. Two laws, `vp1_agrees` and `vp2_agrees`, prove that applying a
   flat form computes what applying its `VFun` does, through `V.norm`. At
   k 18, `fma` takes 639M instructions as built, 520M forced inline, 509M
   profile-guided, 493M both (from 712M, 599M, 582M, 571M); a call costs
   about 584 instructions more than a `succ` call, from 870.
   Placeholders (`VFree`, `VP1`, `VP2`, never glam values) were then held
   out of glam values by laws, at the maintainer's asking. A flat form
   could escape nested: `fma (fma 1 2)` collected the flat `fma 1 2` into
   an argument list that `V.norm`, looking only at the top, left alone.
   Now `V.apply_fn` collects each argument normalized, and three laws
   state the rest: `V.norm` leaves no placeholder at the top but a free
   slot (`norm_not_placeholder`); applying a value whose collected
   arguments hold no placeholder, to anything but a free slot, yields one
   whose arguments hold none (`apply_keeps_clean`); normalizing keeps
   that (`norm_keeps_clean`). A free slot read as a value is a kernel
   fault, which `take` and `peek` count as an error rather than hand on
   (`V.free_chk`, passing the value through untouched). The builtins'
   arithmetic tests its op by a Bool, which proofs can split. About 1%
   on `fma` in three builds of four.
   Toward a net as a value in the heap, the maintainer decided how far a
   forced net reduces (`net-demand-whnf`), how a function's net is copied
   (`copy-reduced-function-nets`) and how small a net starts: 128 nodes,
   2 KB (`net-nodes-double`), with a 64-word pair stack; the stores now
   start so. Open before the store holds nets: nets are first-class glam
   values, bound directly unless wrapped as functions (`net_arity N`) or
   thunks (`net_arity 0`), and shared, so a net may be a cell of its own
   rather than owned by a thunk or a function; the cell model needs a
   careful review first. For collection, values holding handles to cells
   are told apart from ground ones, so marking visits each cell once
   (`split-heap`, step 8); marking a net would scan only its data table,
   skipping ground entries.
4. `spike-lowering` — a tiny untyped lambda calculus with numbers, lists and
   dicts, built as Bend values (no parser), lowered to nets. Functions are
   nets with arity (`functions-are-nets-with-arity`).

Sharing:

5. `spike-materialize` — find nets, and parts of nets, with no evaluation
   left, and hold them compactly: ground data outside the traced heap,
   with no handle indirection, copied whole. Normalize under fuel when an
   annotation asks, and compile a net that only builds values to operator
   steps, after the Rust bootstrap's compiled nets.
6. `spike-cursors` — logical copies after the Rust bootstrap's cursors: a
   call copies its function's net lazily, frontier by frontier, and a
   source pair reduces once, in the source, for every copy, so partial
   applications share their work. Over pages, a copy may need its source's
   pages, or only the compact form of the parts it reads.
7. `spike-fixpoints` — object-self knots over mixins (one cell per knot,
   entries capturing its handle; linearization computed once per spec),
   recursive binding groups, self-recursive functions (each call
   instantiating a compact template through a reference, never unfolding
   through fans), and `.fix` with forward references. Strict recursive
   demand is a dependency cycle, found also across tasks' waits.
   Workloads: deep mixin chains, repeated `with` and `extend`, recursive
   functions, recursive do over assembly labels. Law: unfolding a knot
   once changes no observation. To try (the maintainer, 2026-10-30): knots as
   promises, lazies filled by mutation, as the Rust bootstrap favoured,
   against the library's mixins tied by `Y` and `Z`, which demand reads
   at a cost superlinear in the chain's depth where call-by-need is
   linear (`pairing-library.programs`).
8. `spike-lazy-data` — the split heap with a stop-the-world collector
   (the sketch's "Collection"), against lazy fields as ports, on workloads
   that share a field many times, copy a large mostly unread dict, keep
   many persistent versions of a large lazy dict (the case where careless
   marking revisits shared structure), and churn a nursery beside a
   long-lived namespace.

Parallelism:

9. `spike-page-rounds` — a coordinator running independent tasks on
   workers that own their pages, in rounds (`rounds-of-coarse-work`),
   against a heap that doubles instead, the coordinator taking each
   task's working set out for a round and rebuilding the array after
   (the maintainer, 2026-10-27). Rebuilding need not be literal: with
   virtual memory, the coordinator keeps a mapping from addresses to
   where their cells are, in its array or in a working set, and working
   sets may survive rounds; fast random access to the heap is traded for
   simpler, focused workers:
   tasks report the pages and thunks they need, thunk waiters are restored
   only when ready, and fuel is one unit per logical step. Then marking as
   tasks in the same rounds. Laws: a round loses or duplicates no page and
   no task.
10. `spike-deep-parallelism` — parallelism found inside a task: nested
    parallel calls for pure work over what its worker holds (its pages,
    split between the calls, and ground data), and new tasks for the
    coordinator where work needs pages or thunks held elsewhere. Deep
    parallelism may simplify the coordinator by making it recursive: a
    worker coordinates subtasks over the pages it holds.

Speed:

11. `spike-hvm5-jit` — find the nets, or parts, that fit an HVM5-style
    interaction loop (lambda-shaped, fans that labels pair correctly, data
    limited to its constructors), translate them, and run them on such a
    loop; measure the speedup and how much of real workloads qualifies.
    `pure_hvm5_mini` is a demo, not a built-in: the loop would be ours,
    perhaps a finally tagless interpreter specialized by Bend's `~`
    templates at compile time.
12. `spike-measure` — interactions/s, peak cells, check and build times, JS
    against native, parallel speedup, at n, 2n and 4n; record the numbers
    here.
13. `spike-refinement` — the kernel proved to refine the models: its
    `U32` words (`spike/kprim.bend`, `spike/knet.bend`) read back as the
    models in `Nat` (`spike/freelist.bend`, `spike/wiring.bend`,
    `spike/kplace.bend`), each kernel operation shown to do there what the
    model's does, so that the models' laws hold of the kernel itself and
    not only where the audits check it at run time. Wanted within the
    spike, but it may wait until after it (the maintainer, 2026-10-29);
    placed here for now, though its work belongs to whichever kernel the
    verdict keeps. It needs laws relating `U32` to `Nat`, a path to which
    is vendored (`vendored-sources`) and not gone deep into yet. Its
    laws, drafted, close `spike/LAWS.bend`.
14. `spike-verdict` — decide the representation, record it in
    `docs/decisions/`, and retire this plan.

## Open questions

- Which stand-in workloads represent real assemblies well enough, before a
  parser exists?
