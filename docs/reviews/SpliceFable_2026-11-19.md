# The splice's frame law: three questions, advice (Fable, 2026-11-18)

Read-only review of `glam/splice.bend`, `glam/materialize.bend`,
`spike/kprim.bend`, `spike/knet.bend`, `glam/freeze.bend`,
`spike/kmodel.bend`, `spike/freelist.bend`, the laws named, the plan
step `cells-freeze.nested.host.splice` and its neighbours, the ruling
`serve-write-sets-hybrid`. Line numbers are of the tree at `1e64883`.

## 1. What the splice writes, as I read it

The law's subject is the three passes
`S.sp.statics(size, S.sp.links(links, S.sp.nodes(nodes, 0, S.Sp{h, map}, by)), 0)`
(`glam/materialize.bend:81`, and again at `:231`; `glam/splice.bend:172`
runs the same three before `sp.walk`).

**The node pass** (`sp.nodes`, `splice.bend:91`): one `P.node` per
template node, `fresh` always `True{}` here (`sp.node_at`, `:86`), so
`sp.place` is `P.node(h, hd, w)` (`:38`), never `renode`. A pop writes
the head (`alloc.pop`, `kprim.bend:482`), the node's header and its
payload word, 2 for a data node and 3 for any other (`node.fin`, `:547`;
`node.word`, `:534`). Two kinds of write happen *before* the pop, on the
heap the pop then takes:

- a value: `sp.place_pw(fresh, P.put(h, v), r, N.kcode(k))` (`:64`).
  `P.put` (`:953`) writes nothing for a number or a small builtin, and
  otherwise `tab_put` (`:850`), whose `dt_back` (`:837`) writes all of
  `at_tfh`, `at_tn`, `at_tcap`, `at_td` (words 4 to 7) and the value
  array `a`;
- an error: `P.err_if(KN.fan_too_big(..), h)` in `sp.fan` (`:58`) and
  `P.err_if(KN.too_big(l), h)` for a bind or a lift (`:66`, `:68`):
  `h_err` (`:264`) reads and writes `at_errs`, word 1.

So the node pass alone touches: the head (word 0), word 1, words 4 to 7,
the value array, and for each node taken its words 0 and 2 or 3.
Word 1 of a taken node is *not* written: it keeps the free list's
"next" (an index plus one; `thread`, `:240`; `free.fh`, `:579`). This
leftover is what makes the statics pass dangerous (below).

**The links pass** (`sp.links`, `:125`): for each `T.TL{a, b}`, both
ends resolved through the map, `sp.ref` adding the port to the node's
base (`:101`), then `P.link(h, x, y)` (`:112`), which is
`wr(wr(h, x + 1, y), y + 1, x)` unconditionally (`kprim.bend:385`): no
static test, unlike `link_xx` (`:441`). The two writes are the link
words of two fresh ports *if* each end's node index was set in the map
(an unset entry is 0: node 0, words 0 to 3 of the header) and each port
is below 3 (port 3's "link word" is the next node's header).

**The statics pass** (`sp.statics`, `:137`): for `i` from 0 below
`size`, `KN.ld.hd(P.rd(h, x), x)` with `x = map[i]` (`:134`). `ld.hd`
(`knet.bend:1292`) reads the header at `x`; if its kind is 6 or 7
(`(rk .|. 1) == 7`), `ld.era` reads word `x + 1`, the port the eraser
faces (`:1285`), `ld.q` reads the header at `P.base(q)` (`:1281`), and
`ld.hq` (`:1277`) decides: unless that peer is an eraser too or `q` is
static, `ld.put` writes `P.era()` at `q + 1` and frees `x` (`:1270`):
words `x`, `x + 1`, the head (`free.fh`). The write at `q + 1` goes
*through a word the pass reads*: it lands on a fresh node's link word
only if word `x + 1` holds what the links pass put there. If the
eraser's principal was never linked, `x + 1` holds the pop's leftover,
an index plus one, which may test static (low bits 11: nothing written)
or not (a write at an arbitrary word: `12` gives word 13, a header
word; `100` gives word 101, a live node's link word). This is the hazard
the plan names (`Cells_2026-11-09.md:1783-1794`), confirmed in the code.

**The exact list, then.** Writing `ns` for the k nodes taken, in order:

    concat(nw(n) for n in ns) ++ [P.at_fh()]
      ++ [P.at_errs(), P.at_tfh(), P.at_tn(), P.at_tcap(), P.at_td()]

plus the value array, which the words-laws do not claim (as
`.host.words` already lists, `Cells:1214-1228`). Every write of the
three passes is in it, given the premises of sections 2 and 3. The
list is plain data: the nodes from the premise on the free list, the
header words constants. No walk decides anything in it, which is why
the ruling wants this step exact and the joins by regions
(`serve-write-sets-hybrid.md`, Decision).

**The shape to state it in**: as `crossings_keeps` is stated
(`glam/LAWS.bend:393`): heap in parts `P.H{KM.MG{w}, a}`, `AD.full(w, d)`,
`d < 32`, the map with its own `full`/depth (`hfm`, `hdm` in
`serve_exact`, `:422`), and per word `j` a premise `RG.off(list, d, j)`
(`ring_model.bend:214`) giving `rd(after, j) == rd(before, j)`. Each
pass is an induction over its list with the heap restated in parts per
step (`*_parts`, as `join_keeps.go` does; `docs/Proving.md`, "A chain of
steps composes through each step's parts"), each step one of the frame
laws already on main: `node_keeps`/`node_next`/`node_index`
(`spike/LAWS.bend:406-460`) for a pop, `rd_wr_other` for the link's two
writes (or `link_keeps` lifted to `P.link`, which has no static test),
`free_keeps` (`:485`) and `rd_wr_other` for the static's write.

One lemma is positive, not a frame: for the statics pass to write
inside the list, "after `sp.links`, every link word it wrote holds a
fresh port `map[m] + p`, `p < 3`". It is an induction over the links
with that as invariant; a later write to the same word also puts a fresh
port there, so it needs no uniqueness of ports (section 3).

Two findings on the way, carried into section 3: a premise the plan's
list lacks (the node list's length against `size`), and an ordering
difference between the splice and the loader that makes the root's
eraser a hole, not a premise.

## 2. Question 1: the fresh nodes

**Q1.1 What the proof actually consumes.** Pop `i` reads the head and
node `n_i`'s word 1 (`alloc.k`, `kprim.bend:513-517`), writes the head,
`n_i`'s word 0 and its word 2 or 3. Pop `i + 1` then reads the head
(fine, the pop wrote it: `node_next`) and `n_{i+1}`'s word 1, which must
still be what the list spelled. So the premise the chain induction
needs is exactly the plan's `KMd.chain(v, d, fh, ns)`
(`Cells:1770-1782`): the head holds `n_0`'s index plus one, each
`n_i`'s word 1 the next's; plus, from `RG.layout(ns, d)`
(`ring_model.bend:243`), that no node's words 0, 2, 3 share a slot with
another's word 1 (`cross`) and none with the head's (`off(nw(a), d,
P.at_fh())`), which `node_next`'s `hn1`, `hn2` ask step by step. Note
what is *not* needed by the frame itself: that `ns` is apart from live
nodes. Whether the fresh nodes overlap the ring or the walk's path is
the composition's problem (`pend.ok`'s `layout(L)`, `.host.path`), not
the splice's, and the splice law should not carry it.

**Q1.2 Where Q3 enters the node pass.** Between two pops, `P.put`
writes words 4 to 7 and `err_if` word 1 (section 1). `chain` must
survive them: the header's written words must be off the head's slot
(true: words 1, 4 to 7 against 0, for `d >= 3`) and off every
`n_i`'s word 1. The second is a premise on `ns` against the header,
the same fact Q3 wants of the ring's nodes. In the law, state it as
`RG.off(nw(n), d, h)` for each `n` in `ns` and each `h` of the header
list (one predicate over two lists, `off.nodes(ns, d, h)` folded over
the header list), or as "every node of `ns` at or past `P.iface()` and
below the capacity", from which the slot facts follow by a lemma. I
prefer the second as the *premise*, the first as what the proof uses:
it is the fact the allocator will discharge (Q3.4).

**Q1.3 Option (a): take the premise, bridge later.** Law:
`chain(v, d, fh, ns) && layout(ns, d) && past_hdr(ns)` (names to taste,
in `spike/kmodel.bend` beside `KMd.lw`), `List.length(nodes) == k`,
and the conclusion over the exact list. Costs, from the existing proofs:
`node_keeps.go` is one lemma of three `get_set_other`s
(`spike/PROOF.bend:32511-32541`); the node pass is that lemma applied k
times under an induction over `nodes` carrying `chain`, `layout`, `full`
and the map's `full`, with one step lemma per template-node shape
(`sp.tn`'s four arms, `sp.fan`), each a `put_keeps`/`err_keeps` (section
4) before a `node_keeps`. Comparable to `crossings_keeps`'s induction
(`Cells:1636-1660`), simpler for having no ring: I would expect it the
size of `join_keeps`'s composition and steps (47 + 199 lines,
`JoinLaws_2026-11-14.md`, the table), not `crossings_pend`'s 239 defs.
What it leaves missing, to list in the plan: the premise itself (the
free list's words spell `ns`, `ns` laid out, past the header), growth
(`alloc.grow`, `:506`: the reserve tap writes `at_rsv` and `at_tap`,
words 10 and 11, and doubling changes `d`, which breaks `AD.full(w, d)`
for every law in the chain, not this one alone). Runtime cost: none.
Commits later steps to: a lemma from the allocator's invariant to this
premise, which is a prefix fact (below). Fits the directions: the law
is over what the program builds, by the names it calls
(`docs/Proving.md:26-38`); the premise is on heap words through a model
name, the encoding `(fh - 1) << 2` moving into `chain`'s definition and
its proof lemmas rather than the law's text (direction 2; the review's
B2, `laws-name-link-words.md`, Consequences).

**Q1.4 Option (b): the free list exact over `P.alloc` first.** What it
would be: `FL.ok` (`spike/freelist.bend:106`) is `walks && nodup &&
listed`, over a model with a freeness tag per slot (`Used`/`Free`). The
heap has no such tag: a freed node's header is zeroed (`free.fh`,
`kprim.bend:581`) but nothing in `alloc` reads it, so a heap-level
`listed` ("every free slot is on the list") has no referent; it would
have to be carried as ghost state (a list `l`, as `L` is carried in
`pend.ok`, `ring_model.bend:315-324`) with `walks(l, v, d, fh)` and
`nodup(l)`, and `live` as a separate carried list with `none.in(live,
l)`. Laws: `P.alloc` pops `l`'s head (keeps `walks`, `nodup`), `P.free`
of a live node pushes it. That is three laws the size of the `node_*`
family plus list lemmas (the hub's pigeonhole `ph` and `removeN` in
`glam/PROOF.bend` are already there for `nodup` on a prefix,
`Cells:2030-2040`). Then the bridge to Q1.3's premise: `walks` on a
prefix of `k` gives `chain`; `nodup` plus every index below the
capacity gives `layout` (distinct bases, four words apart, below `2^d`);
every index at or past `P.first()` gives `past_hdr`. The cost is
moderate, days not weeks. But it does not *discharge* anything for the
serve until the invariant is shown of the heap the serve is given, which
means every rewrite in `krules.bend` (`fresh2`, `renode`, the reserve,
growth) keeps it: `kernel_free_ok` (`spike/LAWS.bend:685`) is over
`KP`'s model in Nat, not over `P.H`, and bridging that is the heap-model
programme, not this step. So (b) first moves the premise from "`ns` is
the list's prefix, laid out" to "the heap's free list is exact with `l`
and `live`", equally a premise today, and delays the splice law for no
gain in what the serve can claim now. (b)'s `listed` conjunct is also
irrelevant to the splice: only `walks` and `nodup` of the prefix matter.

**Q1.5 A sharper target for `.host.alloc` than (b) as asked.** Name the
allocator's law to come as the *prefix* fact the splice and the serve
both consume: "the free list's first k nodes are distinct, laid out
apart, at or past `P.iface()` and below the capacity, and none of them
is in `live`", for a carried `live`. That is `walks` and `nodup` on a
prefix plus bounds, which `hdr_new` (`kprim.bend:249`, threading from
`first()`), `grow.done` (`:466`, from `wcap0 + 1`) and `free` of a live
node (its base already past the header) all keep. It discharges Q1.3's
premise, Q3's premise on `L`, and `.host.path`'s "fresh nodes off the
path" in one law, and it is what `FL.free_list_takes_free`
(`spike/LAWS.bend:525`) says in Nat. Put it in the plan as the bridge,
with `FL` kept as the model it refines.

**Q1.6 Recommendation.** (a): take `chain && layout && past_hdr` as the
premise, state the law now, list the premise and growth as missing
pieces, and name Q1.5 as the allocator step that discharges it. Order
the proof: node pass first over templates without values (the plan's
first slice, `Cells:1815-1818`), but write `put_keeps` and `err_keeps`
first so that the step lemma for `sp.tn` is uniform.

**Q1.7 What would change my mind.** (i) If the maintainer wants the
splice law free of any heap premise: then `ns` would have to be
*computed* by walking the free list (`fl.walk`, `kprim.bend:640`), the
list sharing the walk's reads, which is the JoinLaws lesson the ruling
cites ("a list computed by the code's own reads claims nothing of those
reads"); I would still argue for the premise. (ii) If `.host.path` turns
out to be next and needs "fresh nodes off the path" soon: then Q1.5 is
on the critical path and should start right after the splice law, but
still after it, since the splice law is the consumer that fixes Q1.5's
statement. (iii) If growth is reachable in the serve's tests often
(`sp.nodes` on a list longer than the free list): then the frame over
the pop path alone claims little of real runs, and growth's frame
(`m_ensure` keeping words, `kmem_grow.bend:102`) rises in priority;
count it first, as `AGENTS.md` asks ("count how often it arises").

## 3. Question 2: the template's premises

**Q2.1 First, the premise set itself, checked against the writes.** Of
the plan's three (`Cells:1783-1794`), the frame needs two and a half,
and lacks one:

- (i) each link end's node index below the number of nodes, so the map
  entry was set (`sp.put`, `splice.bend:82-84`): needed, else node 0.
- (ii) each port below 3: needed, else `x + 1` is the next node's
  header (`sp.link2`, `:110-112`).
- (iii) "each port in at most one link": *not* a frame premise. Two
  links at one port write its link word twice, each time a fresh port;
  the eraser's word 1 then still holds a fresh port and the static lands
  inside the list. It belongs to the content law (the copy is the
  template's net), where the ruling's exact list is not the subject.
  Dropping it makes the frame law stronger and leaves freeze less to
  prove.
- (iv) each eraser's principal an end of some link: needed (section 1).
  With one sharpening in Q2.3.
- (v) missing: `size <= List.length(nodes)` (equality is what both
  producers build). `sp.statics` reads `map[i]` for every `i < size`
  (`:137-144`); for an index no node filled, the entry is 0 and
  `ld.hd(P.rd(h, 0), 0)` reads the free list's head as a header: if
  `fh .&. 63` is 6 or 7 it reads word 1, the error count, as a port and
  writes through it. Freeze gives equality by construction (`fz.tpl`,
  `freeze.bend:357-360`: `nodes ++ reverse(eras)`, size `ne`); so does
  `tg.done` in `glam/lower.bend:686-690` (`size` the leaves' count
  added). State it, do not assume it.

Also, the map's depth: `T.depth_for(31n, size, 0n)` (`materialize.bend:81`)
must give `2^dm >= size`; take `size <= 2^dm` as a premise with `hdm`,
or prove `depth_for`'s bound once (a big-constant hazard at `2^31`,
`docs/BendIssues.md`; a premise is cheaper now).

**Q2.2 Option (a): a law on what freeze builds.** The serve's only
source of templates is `F.freeze_tree` (`materialize.bend:87`;
`:231` the same through `materialize1`). Parts (i), (ii), (v) hold by
construction with *no premise on the source heap*: indices come from
`ne`, which grows with each eraser or hole (`fz.peer.v`, `:278-283`;
`fz.peer.k`, `:291-297`), and from the map, set to indices below `n`
(`fz.mark`); ports are 0, 1, 2 from `fz.peers` (`:319-332`) or `q .&. 3`
of a non-static `q` (`:283`, under `fz.peer.k`'s `st` test), hence
below 3. (iv) holds for every eraser *freeze makes* (`fz.era`, `:247`,
always with its link, `:297`). The proof is an induction over
`fz.emits` carrying "every end so far below `ne`, every eraser so far
linked", about the size of `crossings_pend`'s (the freezer's state is a
seven-field record, `FzE`, `:243`, threaded through a dozen helpers;
each helper wants a parts lemma). Days. It covers only frozen templates;
the compiler's (`core.bend:826`, `:904`, from `book.tk`, `:1556`) and
the test rows (`spike/load.bend:236`, `spike/nets.bend`) are other
producers, each its own law or check. Had (iii) been kept, (a) would
also need the source wired (`spike/wiring.bend`, a model in Nat, no law
over `P.H`); dropping (iii) removes that premise entirely.

**Q2.3 A hole the law would expose: the root's eraser.** `KN.load` links
the root to the interface *before* `ld.statics` (`knet.bend:1307-1310`,
`load.root` at `:1261`), so an eraser at the root faces the interface
when the pass reads it and is made static on the interface's link word.
The splice runs statics *before* the root is linked: `sp.copy`
(`splice.bend:171-173`) and `mz.fz` then `mz.root` (`materialize.bend:81`,
`:51-57`). A template whose root is an eraser node's principal gets
`T.TE{i, p}` as root and no link at all (`fz.peer.k`'s `rt` arm,
`:300-303`), so (iv) fails of it and the statics pass writes through the
pop's leftover. Rules do make eraser *nodes* (kinds 6 and 7:
`P.renode(.., P.hd(6, 0), 0)` and `P.hd(7, 0)`, `spike/krules.bend:2393-2442`),
and freeze reads them back as `TN` nodes (`fz.node.c`'s `_` arm,
`freeze.bend:224`). The compiler emits none (no `KEra` in `lower.bend`).
For the other reviewer to check: whether `glam/position.bend` can stop
a serve at a finished tree whose root node is an eraser. If it can, this
is a fault to fix in the order (link the root before the statics, as the
loader does: for `splice`, `P.link(h, top, x)` first; for the
materializer, the root's `leave` first would reshape `serve_exact`, so
rather exclude the root's node from the statics pass: the eraser stays a
node where the loader makes a static, which counts alike,
`static-links-count-as-nodes`), not a premise to assume. If it cannot, state "the root's node is no eraser" in the
predicate and let freeze discharge it by one header read where it sets
the root. Either way the law found it; a check at entry would only have
reported it.

**Q2.4 Option (b): a check where templates arrive.** A pass over the
links (bounds) and the nodes (an eraser's principal linked: a bit per
node, or a count), `O(nodes + links)`, no heap writes. Where: at
`book.tk` (`core.bend:1556`), once per module, negligible, refusing with
a `BkErr` (a front end's output refused, the right boundary shape); at
`fz.tpl`, once per materialization, which is also once per splice of
that template, so a constant factor on the host side of every
materialization, perhaps a fifth of the splice's own walk (measure as a
family, `AGENTS.md`, Measuring). It makes the law hold by computation,
which `docs/Proving.md:20-25` allows, with the rule that a guard a law
later proves dead is removed. Against direction 1: it *is* a dynamic
check standing where a law could be; for it: it checks plain data, not
heap words, and reports rather than hopes, which is the pattern the
maintainer objected to.

**Q2.5 A shape that would make (i), (ii), (v) hold by type.** A template
whose links are stored per node and port (an array of `3 * size`
entries, each a peer or none) cannot name a port twice or out of range,
and `size` is the array's size; only (iv) and the root remain as data
facts. It is the "state shapes in which an invariant holds by
computation" rule (`AGENTS.md`, Laws), but it rewrites `T.Tpl` across
`lower`, `freeze`, `KN.load`, `tpl.bend`'s instantiation and the test
nets; not for this step. Record as a lean, if at all.

**Q2.6 Recommendation.** State the premises as one `Bool` model
predicate over the template, `TM.ok(t)` (in `spike/tpl.bend` or a
`spike/tplmodel.bend` no code calls, as `kmodel.bend` is), with exactly
(i), (ii), (iv), (v), plus the root clause pending Q2.3. Take
`TM.ok(t) == True{}` as the splice law's premise. Discharge it for the
serve by a law on `freeze_tree` (option (a)), which needs no premise on
the source once (iii) is out; list it in the plan as the next step
after the splice law, since the serve is this plan's subject and freeze
its only producer. For the compiler's templates, which reach the same
passes through `S.splice` and not through this step, a check at
`book.tk` once per module is cheap and a boundary; mark it a stopgap
under direction 1, to be replaced by a law over `lower.bend`'s `size`
counter when `splice`'s own law is written. No check inside the splice
or the freezer: that is paid per materialization and a law can replace
it.

**Q2.7 What would change my mind.** If the freezer law turns out to need
a premise on the source after all (for instance that `map` entries read
by `fz.peer.j` were set by `fz.mark`, which is the walk's own
invariant), its cost rises toward `crossings_pend`'s; then the check at
`fz.tpl` is the honest interim, measured, with the law listed as the
missing piece. And if Q2.3's hole is reachable, fix the order first:
no premise set should paper over a write the loader gets right.

## 4. Question 3: the header's words

**Q3.1 What is written, exactly.** The head, `at_fh`, word 0, by every
pop and every free (`alloc.pop`, `kprim.bend:482-484`; `free.fh`,
`:579-581`). The error count, `at_errs`, word 1, by `h_err` (`:264-267`)
under `err_if` (`:269`), only on an oversized level, site or offset
(`sp.fan`, `sp.tn`). The table's four words, `at_tfh`, `at_tn`,
`at_tcap`, `at_td`, words 4 to 7, by `dt_back` (`:837-840`), all four
on every `tab_put` whatever path `dt_put` takes (`:120-127`), and
`tab_put` only for a value that is neither a number nor a builtin that
fits (`put`, `:953-962`). Nothing else of the header: not `at_itrs`
(2), `at_wcap` (3), `at_cyc`, `at_scan` (8, 9), the reserve's words
(10, 11) nor the events (12 to 27, `at_evk`). Growth, which is not in
the law, would add 3, 10 and 11 (`grow.done`, `:466-470`; `alloc.tap`,
`:494-500`).

**Q3.2 Option (a): one class, "the header's words below `P.iface()`".**
A model name `KMd.hdr(d, j)` meaning `AD.slot(j, d) < 28`. Pros: one
premise, robust to growth's later words, and the shape the serve wants
of the ring ("every node of `L` past the header", `Cells:1795-1802`).
Cons: it over-approximates by 22 words, so a mutation writing `at_itrs`
or an event word from inside the splice (a `P.bump` or `ev_count`
slipped in) is not refuted, and an out-of-range link's writes to words
1 to 3 through node 0 (Q2.1 (i)) would sit inside the class, hiding
that the template premise is load-bearing there. It is also not what
the ruling says: "an exact list of words".

**Q3.3 Option (b): the exact words, as a named list.** `KMd.hdr_words()`
`= [P.at_errs(), P.at_tfh(), P.at_tn(), P.at_tcap(), P.at_td()]`, the
head listed beside it as it already is (`crossings_keeps`'s `hjh`,
`glam/LAWS.bend:393-421`), and the premise `KMd.off.words(KMd.hdr_words(),
d, j)`, a list-`off` in `spike/kmodel.bend` (spike cannot import
`glam/ring_model.bend`'s `RG.off`; glam imports spike, never the
reverse), of which `RG.off` becomes a consumer. Pros: exact, as the ruling asks; the list is constants, so it
composes by appending with no reasoning; it refutes the mutations (a)
lets pass; the proof costs the same, each `dt_back` step four
`get_set_other`s as `free_keeps` has three (`PROOF.bend:32628-32649`),
each `h_err` one. Cons: growth, when it comes, changes the list, a law
change for the maintainer to approve (it would anyway: growth changes
`d`, so every premise `AD.full(w, d)` of the chain changes shape). The
representation detail (which words) sits in `kmodel.bend`, as `KMd.lw`
holds the link word's (`laws-name-link-words.md`), so the law's text
names a class and the proof unfolds it: direction 2 is met either way.

**Q3.4 The serve's premise on the ring, which both options need.** The
serve's composition must show no node of `L` has a word among the
header's written words (else `pend.ok`'s `layout`, `faces` are not kept
through `P.put`). Today `layout` keeps each node off the head only
(`off(nw(a), d, P.at_fh())`, `ring_model.bend:243-249`). Do not widen
`layout` for this: every law over `ring.ok`, `node.ok`, `enter.ok` and
`pend.ok` would change meaning, as `faces` did (`Cells:1715-1735`).
Take a new premise in the new composed law instead, "every node of `L`
at or past `P.iface()` and below `2^d`" (`KMd.past_hdr(L, d)`), and a
lemma from it to `off.nodes(L, d, h)` for each `h` of `hdr_words` and
to `off(nw(a), d, P.at_fh())`. This is the same fact Q1.2 needs of
`ns`, and the same the allocator discharges later (Q1.5): the header's
nodes 0 to 6 are never threaded (`hdr_new`, `kprim.bend:249`), the
situating node is a `P.node` (`core.bend:785`), the cursors are
placeholders the splice made (`R.cursor` rewrites one in place,
`ring.bend:158-159`). Fold `past_hdr` into `layout` later, if the
maintainer wants one predicate, with the approval that entails.

**Q3.5 The value array.** `tab_put` writes `a` too, and may grow it
(`dt_grow`, `:88-92`). The words-laws take `a` as a parameter and claim
`P.rd` on words only; keep it so and list "the value table" among the
missing pieces, as `.host.words` does (`Cells:1224-1228`). No ring law
reads `a`.

**Q3.6 Recommendation.** (b): two small laws in `spike/LAWS.bend` in
`link_keeps`'s shape, `put_keeps` (every word off `hdr_words` and the
head reads as before after `P.put`; its witness a `VLazy` or a list
value, which takes the table path) and `err_keeps` (one word), each with
a mutation that writes one word off (`at_itrs` for `at_tn`, say); the
splice law's premise `KMd.off.words(KMd.hdr_words(), d, j)` beside the
head's (or, in the two spike laws alone, one slot premise per written
word as `free_keeps` has them, `spike/LAWS.bend:485-504`);
the serve's premise on `L` as `past_hdr`, discharged from Q1.5. Use the
class of (a) nowhere in a law's conclusion; it is a premise shape, not a
write set.

**Q3.7 What would change my mind.** If growth is to enter the splice law
within this plan (Q1.7 (iii)), the list changes once more and a class
"below `iface()`" spares one approval; even then I would list the words
and widen the list, since the class hides the events' words. If the
maintainer prefers fewer names in `kmodel.bend`, `hdr_words` can be
spelled in the law as `at_*` calls, which are already names, not
numbers.

## 5. How they interact, and an order

**5.1 One allocator fact serves all three.** Q1's premise (`chain`,
`layout`, `past_hdr` of `ns`), Q3's premise on the ring (`past_hdr` of
`L`) and the composition's need that `ns` is apart from `L` and from
the walk's path are all consequences of one future law: the free list's
first k nodes are distinct, laid out apart, at or past `P.iface()`,
below the capacity, and none of them live (Q1.5). Q2's premise is of a
different kind, plain data about the template, discharged by a law on
its producer and needing nothing of the heap. Keep the two kinds apart
in the law's statement: heap premises in `KMd`, template premises in a
template model; the law's text then reads as the ruling does, "fixed by
the template and the fresh nodes it is given".

**5.2 Q3 inside Q1's proof.** The node pass interleaves `P.put` and
`err_if` with pops (`sp.tn`, `splice.bend:61-72`), so `chain` must be
shown kept across header writes: that is `past_hdr(ns)` used inside the
node-pass induction, not only by the serve. Build `put_keeps` and
`err_keeps` before the node pass, or its step lemma has nowhere to turn.

**5.3 Q2 inside the statics pass.** The positive lemma of section 1
("every link word the links pass wrote holds a fresh port") is where
(i), (ii) and (v) are consumed, and (iv) where the eraser's word 1 is
read; the uniqueness of ports (iii) is consumed nowhere. If Q2.3's hole
is real, the order fix comes before the statics law, since a law over
the current order would need a premise the producer cannot keep.

**5.4 Order, by waypoint (each a plan step name, as the plan's practice
asks):**

1. `splice.put`: `put_keeps`, `err_keeps`, `KMd.hdr_words`; tiny, and
   they unblock the node pass.
2. `splice.pops`: `KMd.chain`, `past_hdr`; the node pass's frame over
   the exact list, `layout(ns, d)` the premise; witnesses on
   `WB.empty(10)` (`glam/witness.bend:19-20`, 64 words; `P.h_new()`'s
   512 are heavy for an instance) with two `P.wr`s for the plan's
   example (node 36's word 1 holding 11, node 40's 0,
   `Cells:1780-1782`), built not spelled.
3. `splice.tpl`: `TM.ok` with (i), (ii), (iv), (v) and the root clause;
   Q2.3 checked and, if reachable, the order fixed first (a fault, with
   a library entry, `AGENTS.md`, Gate).
4. `splice.links`: the links pass's frame and the fresh-ports lemma.
5. `splice.statics`: the statics pass's frame under `TM.ok`.
6. `splice`: the three composed by appending; its mutations: a link
   written without `+ 1`, a static put at `q` instead of `q + 1`, the
   statics pass run to `size + 1`, a `bump` in the node pass (refuted
   only by the exact header list).
7. After: the freezer's `TM.ok` law (`.host.terms`); the allocator's
   prefix law (`.host.alloc`, restated as Q1.5), which discharges 2's
   and the serve's premises together; the `book.tk` check for the
   compiler's templates, marked a stopgap.

Growth stays missing throughout, listed beside each law, until
`KM.m_ensure`'s frame exists.
