# Allocation choices: representation, room, and who owes it (second reviewer)

Written for `cursor-laws.alloc` (`docs/plans/CursorLaws_2026-11-23.md`),
a second round after the maintainer's answers of 2026-11-26, beside the
lead reviewer's analysis of the same questions and independent of it.
Findings are numbered C1 onward; F and A numbers are round one's
(`AllocFable_2026-11-26.md`).

## Scope

Read in full: both round-one reviews; the records `free-list-sound`,
`laws-across-steps-iterative`, `splice-frame-premises`, `store-pages`;
`docs/plans/KernelRefine_2026-11-24.md`; `glam/loop_model.bend`;
`spike/HEAP_LAWS.bend`; `spike/kprim.bend` lines 150-265 and 430-740
(the header, `thread`, `alloc`, `free`, `grow_more`, `frees`,
`reserve`); `spike/kstrat.bend` lines 800-830 and 1205-1410 (the
collection's growth, the reserve, the collecting demand, `d.start`);
`glam/materialize.bend` lines 47-90 and its comments.

Read in part: `spike/kdemand.bend` (its outline, and the bodies of
`d.go`, the walk's pops, `wk.rw`, `nd.*`, `wk.ori`, `wk.root*`,
`wk.sn`, `wk.q*`, `dn.*`, `demand.go`; not `wk.push`, `fw.scan`, the
rules or the static erase's bodies); `glam/core.bend` (`host.go`,
`frame.ok.k`, `sliced`, `step`, `lowered`, `frame.push`, the `Hb` and
`Cn` types); `glam/splice_copy.bend` lines 1-112;
`glam/index.bend`'s `ix.put.p`; `glam/ring.bend`'s comments and its
allocation sites; `spike/kmem_grow.bend` lines 40-105;
`spike/kmodel.bend`'s `at_idx` and `chain`; `spike/wired_model.bend`
lines 15-36; `spike/net.bend`'s `kcode`; the header constructors in
`spike/kprim.bend` (`hd`, `hd2`, `bare_hd`).

Sampled by pattern only: the callers of `P.reserve`, `P.grow_more`,
`P.frees` and the readers and writers of `P.at_rsv()` over `spike/` and
`glam/`; the `KS.` names `glam/` uses; how many law files spell the
free list's encoding. No proof file was read.

Nothing was built, typechecked or run, and no measurement was taken:
every cost below is an estimate from reading, and is marked so. Claims
that one predicate implies another are from their definitions, not
checked by Bend.

## Between serves

Round one left two points open. Both can be settled by reading, as the
code stands today.

### C1. Between two serves a host runs plain demand: walks, rewrites, static erasures; and it may run no rewrite at all

`host.go` (`glam/core.bend:985-992`) rebuilds the host's demand with
state 0 (`KD.d.go`, `spike/kdemand.bend:30`, which only sets the
state). The next move is `step` (`glam/core.bend:1353-1356`):
`KD.Demand.demand(slice(), d)`, up to 2^20 steps (`:238`) of the plain
family, not `DemandEv` and not the collecting `KS.demand.c`. Each step
is `Demand.wk.q` (`spike/kdemand.bend:682`), which does one of:

- a descent (`wk.down`, `dn.step`, `:658-676`): it reads the net and
  writes the path, an array of its own (`KM.m_set(path, ...)`). No word
  of the net is written. (`wk.push`, which grows the path, I read by
  name only.)
- a rewrite (`wk.rw`, `:366-373`, and `wk.root.go`, `:595-600`):
  `Demand.go` into the generated rules, which pop the free list, free
  the pair and relink.
- a static erasure (`wk.sn`, `:616-623`, `static_erase`), which frees.
- a stop: a need (state 2) at a lazy handle (`nd.lz`, `:376-383`) or
  at a cursor, kind 18 (`nd.cur`, `:403-408`; `wk.root.cur`,
  `:437-442`); stuck, a cycle, a variable, the end.

A stop at a cursor writes nothing, and a descent writes only the path.
So a host can go from one serve to the next having written no word of
its net: the walk descends from the served position to another cursor.
`serve_next`, two serves with nothing between, is then not an empty
case. How often it arises I cannot say by reading; a count would tell
(see Q3, what to measure). In general, though, any number of rewrites
lies between, as round one's F9 said.

Three more things reach a net between its serves as host, none traced
to its end:

- It may be a source. `M.serve` runs positioned demand in the source
  (rewrites there) before it freezes; a nested source is served into
  first (`glam/materialize.bend:39-41`).
- `KS.resume` (`glam/core.bend:837`, `:924`, `:1237`) writes a value
  that arrived. Whether it takes a node I did not read.
- In a one-net serve (`M.serve1`, `glam/materialize.bend:253-260`) the
  host is the source, so positioned demand's rewrites run in the host
  *inside* the call, before the splice.

The last matters for Q3 and Q5. What the laws call a serve (the splice
and the crossings) is the tail of `M.serve`. The kernel's steps come
before it within the same call, and the tree to copy is not known
until the freeze returns. So the point where the per-serve contract is
asked is not the core's call of `M.serve`; it is `mz.fz.t`
(`glam/materialize.bend:72-75`) and its one-net twin (`:275`).

### C2. No net glam runs keeps a reserve, and none is collected

`P.at_rsv()` is written in two places: `rsv.link`
(`spike/kprim.bend`, under `reserve`), which sets it, and `alloc.tap`
(`:494-500`), which clears it. `P.reserve` has one caller, `rs.k`
(`spike/kstrat.bend:1240`), reached only through `dc.reserve`,
`dc.pk`, `dc.chunk` and `dc.loop` from `KS.demand.c` and `KS.demand.s`
(`:1370-1376`). `glam/`'s modules, tests included, use five names of
`KS`: `d.at`, `d.start`, `need`, `resume`, `d.path` (by pattern). The
core's demand is `KD.Demand.demand`. A new net has word 10 zero
(`h_new`, `spike/kprim.bend:257-258`: a zero-filled store, and
`hdr_new` writes words 0, 3, 6 and 7); `spike/knet.bend` only reads
the word (`:1473`).

So on every net glam runs, as the code stands, the reserve's word is 0,
`alloc.tap` always doubles, and `collect_cycle` (called only from
`dc.loop`, `:1363`) never runs. That agrees with the materializer's
own note (`glam/materialize.bend:43-45`: "a source must run no events,
fusion or collection near copied nodes").

Two consequences.

- For now the laws can take "the reserve's word is 0" as one standing
  premise at a word, kept by frame: nothing the materializer or a
  rewrite calls writes word 10 but the tap, which writes 0. Round
  one's A5 asked for this check "before any reserve law is written";
  the answer is that none is needed yet.
- It is a fact of how the core is wired today, not a ruling. The
  collecting demand is the kernel's own (`heap-strategies`), and a host
  that collects will keep a reserve. So the premise should stand under
  its name, with the reserve's law as its discharger, and nothing else
  should be built on it. In particular a reserve "kept for serves"
  (Q5) would be the reserve's first use in glam, and would later share
  one word, and the taking's flag, with the collector.

### C3. A serve that cannot grow writes over the host's interface before the run stops

`grow.done` (`spike/kprim.bend:466-473`), where the store is at its
greatest size, counts an error and answers "the interface's reference
as the node, so that nothing writes the header". The caller then
writes that node: `node.fin` (`:536-538`) puts a header and a payload
word in the interface, and the node pass goes on, each later node the
interface again. The run stops at the serve's end, where the error
count is read (`frame.ok.k`, `glam/core.bend:1061-1068`). Under
`implementation-errors-stop` that is sound for the run's result. But
on that path the splice's exact write list is breached, and no law of
a serve can be stated. It needs 2^28 nodes to reach, so it is a
question of what the laws can say, not a fault to reproduce.

### C4. A serve's allocations are bounded before its first write

At `mz.fz.t` the template and the crossings are in hand
(`T.Tpl{nodes, links, root, size}` and `curs`). The node pass makes
`SM.made(nodes)` nodes, one for each node not an eraser, always fresh
(`sp.node_k`, `glam/splice_copy.bend:87-96`). A crossing's cursor is
its placeholder, a template node already made (`glam/ring.bend:60`).
A crossing put in the index takes at most one branch (`ix.put.p`,
`glam/index.bend:238`), and one joined frees nodes
(`glam/ring.bend:71`, `:84`, `:140`). I found no other allocation in
`glam/serve.bend`, `glam/ring.bend` or the index; `R.situate`
(`glam/ring.bend:54`) allocates, but at a use, outside a serve. So a
serve takes at most `SM.made(nodes) + length(curs)` nodes, a number
known before the node pass. Unchecked beyond those greps.

## Q2. Laws relying on the representation

### C5. The representation is three facts of different kinds, and two are already behind names

"The free list's encoding" covers three things.

1. *How a link names a node*: the index plus one, 0 for none, the next
   link in word 1. For the materializer's laws this already has one
   owner, `KMd.at_idx` and `KMd.chain` (`spike/kmodel.bend:80-90`).
   Seventeen premises in the index's, the splice's and the loop's laws
   cite `KMd.chain`, and none spells a shift (by pattern). Only the
   three allocation laws of `spike/HEAP_LAWS.bend` (`node_keeps`,
   `node_next`, `node_index`) write `(fh - 1) << 2n` and
   `U32.is_eq(fh, 0)` themselves.
2. *Where a node's words are*: four words, a base a multiple of 4.
   Spread over `KMd.nw`, `RG.bases`, `IM.nd.ok` and `disj4`; round
   one's per-node range predicate (F6) would make it one definition.
3. *The mark*: a free node's header is 0, a node in use has another.
   Spelled once in a model, inline: `U32.is_ne(KMd.word(v, d,
   P.base(y)), 0)` (`spike/wired_model.bend:22`), which `wired_port`
   stands on. No law says it of the free list.

Facts 1 and 2 say how to find things. Fact 3 gives a word's value a
meaning, and it is the only one the 2026-11-13 remark touches. That
remark was about the words `free` leaves stale (2 and 3), and about
frame laws promising to preserve a node's own words. A law that relies
on the mark relies on the two words `free` *writes* (the header, the
link) and on nothing it leaves. `KMd.chain` already relies on word 1.
So the mark asks for one more word under the same kind of promise,
made by a law about `free` (after it, the node is marked), not by a
frame law. I read the two as compatible; that is my reading, for the
maintainer to confirm.

### C6. "In use means a nonzero header" has a hole at the splice

`R.KFree` is a constructor of `R.NodeKind` with code 0
(`spike/net.bend:14-17`). The node pass writes
`P.bare_hd(N.kcode(k))` for a template node's kind
(`glam/splice_copy.bend:60`), and `bare_hd(0)` is `hd(0, 0)`, which is
0 (`spike/kprim.bend:1943-1951`, `:744`). So a template that held a
node of kind `KFree` would make a node in use whose header reads free.
Whether `SM.tpl.ok` or freeze's laws exclude it I did not check (the
name does not occur in `glam/splice_model.bend`). Any option below
that reads the mark owes this: a template premise, or a law that
freeze emits no such node. The lead's F5 checked that no code writes
`hd2(0` or `hd(0` literally; this is the non-literal path.

### The options

**R1. Rely on it directly.** Laws spell `word(...) == 0` and the shift
where they need them, as `HEAP_LAWS` and `wired_model` do now.

**R2. Named predicates own it.** In `spike/kmodel.bend`, beside
`at_idx`: `free_at(v, d, n)` (today: the header reads 0),
`used_at(v, d, n)` (today: it does not), and the sound list defined
through them. Laws cite the names. The representation is unfolded only
in a handful of lemmas: `free` marks its node; a node made with a
header of a kind in use is `used_at`; a zero-filled range is `free_at`;
the two exclude each other. `wired_model.at` cites `used_at`. This is
`net-obvious-errors`' pattern, `KN.wired_ok` the one definition of
wired.

**R3. A ghost list, no header read.** "Free" is membership in a ghost
list; "in use" must then be ghost too, or the two cannot be shown
disjoint, since today's "live" is itself a header read (fact 3). So
this is two ghost sets, and every law of every write carries both.

**R4. An abstraction function.** A function from the words to a model:
the list read by a walk, each node classified free or in use with its
kind, landing in `FL` and `KA` (`kernel-refine`). Laws are stated on
the model; the group A laws in `Nat` apply through it.

**R5 (mine). R2 for the mark, a reading for the list, the head a
parameter.** The mark and the layout by named predicates (R2); the
list's nodes read from the words by a walk (round one's F7), with a
ghost list only to say its length and that it ends; and the sound
list taking *the word its head is in* as an argument,
`fs.ok(v, d, hw, l)`, not the constant `P.at_fh()`.

### Pros and cons

| | Simplicity | Extensibility | Modularity | Runtime |
|---|---|---|---|---|
| R1 direct | least to write now | worst: each law restated when the encoding moves | none: the allocator's encoding leaks into the index's, the ring's, the wiring's laws | none; fixes the header's zeroing in every law |
| R2 named | two definitions, four lemmas | a change of mark is a change of `free_at` and its lemmas | good: one owner, as `chain` is for links | none; fixes the zeroing in one place |
| R3 ghost | statements short, proofs long: two sets through every write | best against a change of mark; no help to the audit, which must read words | poor: every writer's law knows both sets | none, and none fixed |
| R4 abstraction | heaviest: `listed` over every slot, `Nat` against `U32` | best for a second store refining one model | best in the end | none |
| R5 | R2's, plus one walk | R2's, and lists at other heads for nothing | R2's | as R2 |

Some of these cells need their reasons.

*Simplicity.* R3's cost is hidden. A ghost free list alone cannot
discharge `LM.ext.ok`'s faced-port conjunct, because the wiring's
"links a live node" is a header read (round one's F8). To avoid
headers altogether the live set must be ghost too, and then each of
some 58 link sites in the rules carries two sets where it now carries
none. R4 is R2 plus the model's exactness, which `free-list-sound`
has just ruled the materializer does not need.

*Runtime.* No option costs an instruction today: `free` already zeroes
the header (`spike/kprim.bend:581`), beside the link it writes in the
same node. What R1, R2 and R5 do is *commit* the kernel to that write.
Its cost, if the kernel ever wanted it gone, is one store a free into
a node whose word 1 is written anyway; I would guess well under one
percent of a rewrite, unmeasured. To know: a measurement build without
the store, audits off, the four builds counted
(`spike/tools/count_builds.sh`). The kernel's own audits commit it
already: `KN.free_ok` counts zero headers, `KN.wired_ok` reads them.

*Extensibility*, by the changes named in the brief:

- *Not zeroing at free, zeroing later (batched or lazy frees).* Sound
  under R2 and R5 with no law restated, if the zero is written before
  the node is *listed*: freed nodes wait on a list of their own, as
  the reserve's do, and soundness says only that listed nodes are
  marked. `free_at` is unchanged; the leaks law
  (`kernel-refine.leaks`) gains a third place a node may be. Under R1,
  each law of `free` changes.
- *No mark at all* (membership the only truth). Then "in use" cannot
  be a header read either; the wiring's model and both audits change.
  That is R3, a restatement under every other option. I see no reason
  the kernel would want it, since parallel reduction prefers a mark in
  the node to a list read across workers.
- *A different mark* (the kind field 0 with other header bits used, as
  a collector's marks might want). R2 and R5: `free_at` and its four
  lemmas. R1: every law.
- *Lists at several heads*: the reserve today, lists a page
  (`store-pages`: "recycling needs free lists per page"), lists a
  worker under parallel reduction. With the head's word a parameter
  (R5) each is the same predicate at another word, and "two lists
  share no node" is one more predicate. With `P.at_fh()` built in,
  each is a copy of the definition. This is the cheapest piece of
  extensibility on offer, and it is free now and a restatement later.
- *Another link encoding* (a page number in a handle's high bits).
  The store's cells are another structure with another cell size, so
  this is a second representation, not a change to the first: its own
  `at_idx` and `chain`. What the two could share is the model in
  `Nat`, which is R4's worth, and a reason to keep `FL` as the common
  model when the second arrives (`kernel-refine.align`), not a reason
  to build R4 for the materializer first.
- *Statics.* A static has no header; `WR.lk` already splits on
  `P.is_static` before any header read. More statics change
  `port.ok`, one definition, under every option.

### Recommendation

R5: let laws rely on the mark, through names. Concretely:

1. `KMd.free_at` and `KMd.used_at`, the mark's only definitions, with
   `wired_model.at` citing `used_at`. Record it as
   `net-obvious-errors` records wired: what "free" and "in use" mean
   at the words, the one place that says so, and that words 2 and 3 of
   a free node stay unpromised.
2. The sound list (`free-list-sound`) defined over them, its head's
   word an argument.
3. A law of `free` that it marks, and of each header constructor that
   it does not; with C6's premise on templates named where it is owed.
4. `HEAP_LAWS`' three laws left as they are until they are next
   touched, then stated through `KMd.at_idx`. That is a change of
   statement to an equal term, so it wants approval, and is not worth
   a round on its own.

Confidence: high that a named mark beats both direct reliance and a
ghost-only list, on all four criteria. Moderate on the head as a
parameter: it is cheap, but I have not seen how Bend's unifier treats
the extra argument in the existing chain proofs. The claim that no
node in use is ever written with a zero header rests on the lead's
grep and on C6's open premise, not on a law.

## Q3. Growth during a serve

The code's choice is between room made before a serve (G1) and growth
wherever a serve allocates, as now (G0). The maintainer asks a
different thing of the laws: that they hold whichever the code does,
where feasible. So the question is at what grain a law can be
indifferent.

### C7. The step laws are already indifferent; coverage is what differs

Every law of an allocating step takes room as a premise: `hl`
(`SM.made(ts) == List.length(&2, U32, ns)`) with `KMd.chain` over the
nodes taken (`glam/SPLICE_LAWS.bend:42-43`; the serve's six; the
loop's). Under that premise `alloc.k`'s test is false at every pop, so
the law is true of code that would have grown and of code that never
needs to. Nothing in those statements says when growth happens. What
changes with the code is which runs a law reaches: under G0 a serve
that outgrows the list is outside every law; under G1 none is, but the
one that cannot grow, which then refuses before any write (C3).

So the first tier of indifference costs nothing and is in place: keep
room a premise of the step laws, and put the choice in whatever
discharges it.

### C8. Growth is a step of its own, and `alloc` on an empty list is that step and a pop

Reading `alloc.double`, `grow.done` and `grow_more`
(`spike/kprim.bend:466-486`, `:606-631`) with the list empty and no
reserve: `grow_more` then `alloc` leaves the heap `alloc` alone
leaves, at every word but one. Both double the store, thread nodes
`wcap0 + 1` to `wcap - 1`, leave the head at node `wcap0 + 1` and
answer node `wcap0`. `grow_more` pushes node `wcap0` back before the
pop takes it again, which writes that node's word 1; `alloc` alone
leaves it 0. That word is a taken node's stale word, which
`node_keeps` already declines to claim. (By hand from the definitions;
not checked by Bend.)

With that equation as a law (`alloc_dry`, a pointwise read law off one
word), growth inside a step is not a new case of each step's law. It
is the growth law followed by the pop-path law. So the second tier:

- one law of growth, about `grow_more` alone: the old words read as
  before, the new range is zero but its links, the list is the new
  nodes then the old list. Round one's `px_grow` composes it with the
  invariant;
- invariants that survive it: the per-node range predicate (F6), under
  which layout and apartness are kept at `d + 1` (slots distinct mod
  2^d are distinct mod 2^(d+1)) and a word below 2^d reads the same;
- `alloc_dry`, wanted only if the code keeps G0.

Laws in this form are indifferent to growth *between any two steps a
law covers*: between serves, between the node pass and the crossings,
between two crossings. The grain is the step, not the serve.

### C9. Where indifference stops

Three places, each for a reason of its own.

1. *Inside a pass whose law names its nodes by the chain.* The node
   pass's laws quantify over `ns`, chained from the head of the heap
   the pass starts on. If the pass grows at its m-th node, the later
   nodes are not on that chain; at depth `d` they do not exist. The
   statement has no instance. Covering it needs the pass split at the
   growth (the pass over an append of templates, the map carried
   across), which is new lemmas and a new law over the split, not a
   weaker reading of the old one. The seventeen chain premises are
   all of this kind.
2. *The exact write list* (`splice-frame-premises`: "growth, when it
   enters, widens the list, a law change"). A serve that grows also
   writes the capacity's word, the head, and word 1 of every new
   node, on a store that was replaced. One frame statement cannot be
   exact for both: either the list is a function of the path taken,
   which is two laws under one name, or it is the union, which
   stops refuting a stray header write on the common path.
3. *The index's insert between crossings.* `ix.put.p` allocates inside
   `R.crossings`' fold, where the invariant has cursors pending. For
   growth there, the growth law must keep the invariant with a
   pending list, at every step of the fold: each of the twelve
   crossings' and leaves' laws gains a depth it returns. `px_grow` at
   "nothing pending" does not serve.

And at the top no single statement is indifferent, because the two
codes take *different nodes*. `grow_more` puts the new nodes ahead of
what was free; `alloc.double` runs only on an empty list. Under G1 a
serve that had to grow copies into the new range first; under G0 it
uses the old list up, then the new range. The heaps differ. A
top-level law would have to say "some fresh nodes", and in Bend "some"
is a function that computes them, one function a code.

So: the step laws, the growth law and the invariant can be written
once, for both. The law that composes a whole serve, and says it is
covered, is written for the code that exists. Under G1 that law is
short (a guard, then the serve on the pop path). Under G0 it needs
growth-stability of three intermediate states (mid node pass, mid
crossings, between serves) where G1 needs one.

### Pros and cons of the code's choice

| | G1 room first | G0 growth where allocated |
|---|---|---|
| Simplicity | a serve's depth is fixed; one growth-stable state | no guard in the code; three growth-stable states and pass splits in the laws |
| Extensibility | a collector or a reserve can be asked for room at one site (C2); a serve that cannot have room refuses whole | each new source of room is a new path inside every allocating step |
| Modularity | the materializer owns its room; `alloc`'s growth path is the kernel's alone | the splice's and the index's laws know the allocator's three paths |
| Runtime | a walk a serve, and growth up to k allocations early | none added |

One more for G1: C3. With room first, a store that cannot grow is
found before the first write, and the serve can end with an error and
an untouched host. Under G0 it is found mid-pass.

### Runtime: what the walk costs, and how to know

Estimates from reading; none measured.

*The walk.* `P.frees(k, h)` reads k - 1 links (`fl.walk`,
`spike/kprim.bend:640-657`). The copy it guards then, for each node,
reads the head and the node's link, writes the head, the header and a
payload word (`alloc.pop`, `node.fin`), writes two or three links and
a map slot; and the freeze before it read the same tree from the
source. One read against some ten heap accesses a node on the host's
side alone, so a few percent of a serve's cost, less of a run's. The
materializer's note that each freeze still takes "scratch the size of
the source" (`glam/materialize.bend:45`) suggests the walk is far from
the largest term today.

*Growth.* Doubling copies the store and threads the new half, the same
work under either choice, amortized over the allocations. G1 moves a
doubling earlier by at most k allocations. It adds a doubling only
where a run would have ended inside that margin: at most one extra
doubling a net, twice the net's memory at its peak in that case.

*Where it would show.* In families that serve much: the sharing
families of the Cells plan (a prefix applied 1, 2, 4 and 8 times;
`hello_lazy_list.g`), in two shapes. Many small serves, where the
guard's fixed cost a serve matters and the walk is nothing; and few
large ones (a whole source copied), where the walk is k reads.
Workloads that copy nothing cannot show it.

*What to measure, in order.*

1. Count first, with no new build. The core already counts serves and
   nodes copied (`Cn`'s `serves` and `copies`, `glam/core.bend:112`).
   Over the sample ladder and the sharing families at n, 2n and 4n:
   copies against interactions bounds the reads the walk could add,
   and copies over serves gives k. If copies are a few percent of
   interactions, the walk cannot matter and step 2 is a formality. A
   counter for serves with no rewrite since the last would answer C1's
   open point in the same run, counted as AGENTS.md's Measuring has
   it.
2. A measurement build in a worktree, the guard at `mz.fz.t` and its
   one-net twin: `P.frees` for `SM.made(nodes) + length(curs)` (C4),
   `P.grow_more` while it fails. Instructions by `scripts/count.sh`
   under names of one length, the default and forced-inline builds
   (`spike/tools/spot.sh`), then the four (`count_builds.sh`); each
   family fitted to a + b·n^k, watching the exponent; judged case by
   case. `sharing.py compare` first, though `P.grow_more` has two
   callers already (`spike/kstrat.bend:824`, `:1258`) and `P.frees`
   none that I found, so no segment should move.
3. Exact signals: results and interactions must be identical (the
   guard interacts with nothing), which makes the differential test a
   check of the spike; the final capacity differs exactly where a
   doubling moved. Record the run ids in the analysis store.

Each run capped (`scripts/capped.sh`), one at a time.

### Recommendation

For the laws: keep room a premise of every step law (C7); state growth
once, as `grow_more`'s law, and make the invariant stable under it
(C8); do not write `alloc_dry` or the pass splits unless the code
keeps G0. That is as indifferent as the laws can be, and it is what
`cursor-laws.loop.shape.grow` already plans, narrowed.

For the code: G1, at `mz.fz.t`, adopted on the measurement above. The
laws do not wait for it; only the top-level law of a covered serve
does.

Confidence: high in the laws' form, and in C9's three limits as
readings of the statements. Moderate that G1's cost is a few percent
of a serve at most; it is the estimate most worth replacing with a
count.

## Q5. Who owes the room

### C10. Only the materializer can know how much room a serve needs

The count is `SM.made(nodes) + length(curs)` (C4), and it exists only
after the freeze, inside `M.serve`, after positioned demand has run;
in a one-net serve those rewrites ran in the host itself (C1). The
core, calling `M.serve`, cannot know it, and room it made beforehand
could be used up before the splice. So "a premise the caller owes"
cannot be the final answer if the caller is the core. It can only be
the form of the step laws, discharged at `mz.fz.t`.

### The options

**W1. A premise the caller owes.** As now: `hl` and the chain.
- For: nothing to build; it is the indifferent form of Q3.
- Against: nobody outside the materializer can discharge it (C10).
  Under `laws-across-steps-iterative` a premise with no discharger
  named "is a claim left out, not scaffolding". So W1 stands only with
  one of the others named beside it.

**W2. A check the materializer makes.** At `mz.fz.t`: `P.frees` for
the bound, `P.grow_more` while it fails, the serve refused if the
store cannot grow.
- Simplicity: one guard, one read-only law (`frees_room`: where
  `frees(k, h)` answers true, the walk of k links from the head
  returns k nodes, which is the chain and `hl` together, round one's
  F7).
- Extensibility: the one site is where a later policy goes, such as
  collecting before doubling (C2).
- Modularity: the materializer's debt, paid by the materializer. It
  discharges length only; that the nodes are free stays the kernel's
  (the sound list).
- Runtime: Q3's walk.
- `docs/Proving.md` warns that a guard must not stand in for a premise
  a law leaves out. Here the law keeps the premise and the guard's own
  law discharges it, which is the permitted use.

**W3. Construction.** Four forms.

- *(a) A batch taken, the pass placing into it.* Walk k links once,
  write the head once, and let the node pass place each node in the
  next slot taken. The splice has that path: `sp.place` with
  `fresh` false calls `P.renode` (`glam/splice_copy.bend:24-29`).
  Room then holds by construction, and the walk *replaces* the pops'
  traffic instead of adding to it: k reads and one write where k pops
  make 2k reads and k writes. So it may run faster than today
  (unmeasured). Its cost is in the laws: the node pass's term changes,
  so the splice's four laws, the serve's six and the loop's are
  restated, though with fewer premises (the chain moves to the batch's
  law). The index's branches would still come by `P.node`, under W2's
  guard.
- *(b) A reserve kept for serves.* It bounds nothing, since k has no
  bound (a whole source); refilling it is the same walk; and it would
  share the collector's word (C2). Against.
- *(c) Headroom kept by the kernel*, or a count of free nodes in the
  header: a write on every allocation and free, on the hot path, for
  the materializer's convenience. Against.
- *(d) Copies into never-used nodes past a mark* (round one's A4):
  room is a subtraction, no walk. But it is a second allocator, and
  recycled nodes go unused by copies. Only on a measured need.

**W4. Nobody: the allocator grows.** As the code now does. Room is
never owed, and Q3's G0 is the price.

### How each fits Q3 and Q4

| | With Q3 | As Q4's scaffolding |
|---|---|---|
| W1 | the indifferent form; needs a discharger | scaffolding only if W2, W3 or W4 is named |
| W2 | is G1 | the room premise's discharger is `frees_room`, at a named site, now |
| W3a | G1, and the guard's cost becomes a saving | the same discharger, by construction; restates the serve's laws |
| W4 | is G0 | the discharger is `alloc_dry` and the pass splits (C9) |

The point for Q4: room is the one part of the per-serve contract whose
discharger is *not* `kernel-refine`. The sound list and the wiring
wait on the kernel's refinement. The length can be discharged by the
materializer, by a read-only law about a walk. Paying it early leaves
the scaffolding that remains purely the kernel's.

### Recommendation

W1 as the form of the step laws, W2 as its discharger, W3a held as the
optimization to try if Q3's measurement shows the walk, or the pops'
head traffic, worth removing. Not W3b to W3d.

Confidence: high that the materializer must own it (C10 is a fact of
where the count becomes known). Moderate to high on a check before
construction: W3a is attractive, but it trades a measured cost I
expect to be small for a restatement of some seventeen laws.

## Recommendations together

The three answers are one design, with Q1's and Q4's rulings.

- **What "free" means** (Q2, Q1): one definition of the mark in
  `spike/kmodel.bend`; the sound list over it, at a head given as an
  argument. Soundness uses the mark one way (listed nodes are
  marked). No leaks (`kernel-refine.leaks`) uses it the other way
  (marked nodes are listed), and should cite the same definition, as
  the audit `KN.free_ok` should.
- **What a serve asks** (Q4): the sound list and the wiring, the
  kernel's, scaffolding until `kernel-refine.rewrite` and
  `.discharge`; and the room, the materializer's, discharged by its
  guard (Q5). With the reserve's word 0 as a named premise while no
  glam host collects (C2).
- **What growth is** (Q3): a step between steps, with one law, under
  an invariant that survives it. After `grow_more` the new range
  satisfies the sound list by arithmetic and the zero fill, with no
  kernel invariant; so growth is also the one case where the
  contract's kernel half is discharged today.

Each premise, its owner and its discharger:

| Premise at a serve | Owner | Discharged by |
|---|---|---|
| the first k nodes are chained, k of them | the materializer | `frees_room`, at the guard |
| they are in range, apart, past the header | the kernel | the sound list's range predicate |
| none is in use | the kernel | the mark, with the sound list |
| no live port links one | the kernel | the wiring and the mark together (F8) |
| the reserve's word is 0 | the core's wiring | by frame now; the reserve's law later |
| no node in use is marked free | freeze, the templates | C6's premise |

An order of work, each step small:

1. Record the mark (Q2) and name the two predicates; settle C6.
2. The range predicate and `grow_more`'s law (`.loop.shape.grow`).
3. Count serves and copies over the families (Q3, step 1); then the
   guard's spike, measured.
4. `frees_room` and the law of a covered serve.
5. The sound list and the primitives' laws, before
   `kernel-refine.align`.

What I am least sure of: the runtime estimates, all unmeasured; that
C6 is a real hole and not excluded by a premise I did not read; and
whether the maintainer's "ambivalent" asks for more than the step
grain, which C9 argues is where it stops.

## Questions for the maintainer

1. **What does the mark mean?** Is a free node one whose header word
   is 0, or one whose *kind* is the free kind, the header's other
   bits left open for later use (a collector's marks, say)? And should
   a node of the free kind be something no template can carry, so
   that "in use" always shows in the header?
2. **A serve the store cannot make room for.** Should it be refused
   whole, the host untouched and an error reported, or is it enough
   that the run stops, as now, whatever the host's net then holds?
3. **Collection in a host that serves copy into.** When hosts come to
   collect, should a serve short of room be able to ask for a
   collection before the store doubles? If so, room is a policy with
   one home, which favours the materializer asking for it over the
   allocator growing unasked.
4. **An early doubling.** Making room first can double a net up to
   one serve's nodes sooner, and in the worst case once more than the
   run needed. Is that memory an acceptable price for a serve that
   never grows under its own writes, or is a net's footprint the
   tighter constraint?
