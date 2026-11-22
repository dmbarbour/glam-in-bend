# Indexing a copy's cursors: a brainstorm (Fable, 2026-11-22)

The second reviewer's brainstorm for `cells-freeze.sharing.cursors.ring`
(option A of `cells-freeze.sharing.cursors.erased`), by a Fable
sub-agent at 2437be3, kept as written; the maintainer asked for it beside
the agent's own ideas, for discussion (`docs/reviews/RingIndex_2026-11-22.md`).
Checked after by the agent: the situating node's word 1 holds the static
eraser (`use.situ`, `glam/core.bend`), so it is not free with the ring
kept; no law names `rg.situ`; `find_exact` promises `RG.first`, the
first member in walk order, and no law makes positions distinct;
`rg.situ` runs in the core and again in the serve.

Advice for discussion; nothing built, nothing measured anew. A claim is
marked **[checked]** where I read it at the place cited, **[inferred]**
where I reasoned from what I read. Costs are counts of reads and writes,
all inferred: I built no Bend program.

## 1. What the ring is used for

### Three walks, not one

The ring is walked by three functions, and a position index removes only
the first. [checked, `glam/ring.bend`]

| walk | where called | steps on a ring of r | reads a step |
|---|---|---|---|
| `rg.find(situ, far)` | each crossing (`cross`, `:238`); the frontier (`sv.front.m`, `materialize.bend:217`); each level of the materializer's climb (`cl.f`, `:151`); the same three in one net (`cl1.f`, `sv1.front.m`) | r on a miss, the hit's distance from the situating node otherwise | 2 (word 2, word 3) |
| `rg.pred(x)` | every `rg.unlink`: twice in `join`, once in `join1`, once in `leave` | always r + 1: it walks from x round to x | 1 |
| `rg.situ(x)` | each serve (`sv.pos`, `sv.from.pos`, `sv1.pos`, `sv1.from.pos`), and the core before it, when a host stops at a cursor (`core.bend:815`) or a source at a nested one (`:1029`) | the members from x on to the situating node | 2 (header, word 3) |

Insertion is O(1), after the situating node (`rg.insert`), so the ring
runs newest first: situ, newest, ..., oldest, situ. Hence
[inferred]: `rg.situ` from a cursor passes every member *older* than it.
In the fold over cells of m heads, the cursor served next is the tail's,
among the newest, and everything older is the dead heads of the cells
before: the situ walk is near r too, twice a serve.

### One serve, counted

A serve of a tree with c crossings into a ring of r, off the root
[inferred from `mz.sp`, `crossings`, `cross.k`, `join1`; the root
placeholder is B6 of `docs/reviews/FreezeFable_2026-11-21.md`]:

- 2 situ walks (core, then serve): up to 2r steps;
- c finds, of which the root's hole hits the served cursor and the rest
  mostly miss: about (c − 1)·r steps;
- 1 `join1` on the hit: one `pred`, r steps;
- at the source's root instead: c misses and one `leave`, r steps;
- a frontier: one find, then a `join` (two `pred`s, 2r) or a climb with a
  find a level.

For a cell of m heads and a tail, c is about m + 2, so a serve walks
about (m + 4)·r members. With m − 1 dead a cell, r grows by m − 1 an
element. The measurement agrees in order [inferred]: 6 heads, 538K to
734K an element over 100 to 400, is about 650 instructions an element
for each element added, 130 a ring member added; at two serves an
element and ten walks a serve, 6 or 7 instructions a member visited.

Two consequences for the brainstorm:

- **An index of positions alone leaves the cost growing.** It removes
  (c − 1)·r of (m + 4)·r. The `pred` walk (always the whole ring) and
  the two `situ` walks stay, 3r a serve: the slope falls by two thirds
  or so, and the curve is still a line in n. Option A, read as "an
  element's cost flat in the list", needs all three walks gone.
- **A sorted ring is not option A either.** The merged walk of
  `cells-freeze.sharing.cursors.ring` is O(r + c log c) a serve where
  it is O(c·r): one walk past every dead cursor a serve, not none. It
  divides the slope by about m + 4 and leaves it. The two pointers
  (find hands back the predecessor) remove one `pred` of two or three
  walks. Both are worth their cost only if the measured slope after
  them is tolerable; neither makes it zero.

### What else reads or writes the ring

- **Made outside `ring.bend`**: a use of a live source writes a ring of
  two by hand, situ and the leaf made a cursor (`use.cursor`, `use.situ`,
  `core.bend:775-779`) [checked]; `glam/witness.bend` and the tests
  build rings likewise. An index must be established at each.
- **Nobody walks all members today** [checked by grep: outside
  `ring.bend` only `rg.situ`, `rg.find`, `join`, `leave`, `crossings`
  are called]. Enumeration is a need to come: a ring freed whole when
  unmarked and a collector marking a ring from one cursor (the Cells
  plan, `cells-freeze.cursors.ring`, "Liveness"); an audit; a rehash
  if the index is a hash. None is on a serve's path.
- **The kernel** knows a cursor only by its kind, 18
  (`kdemand.bend:414`) [checked], and stops; that it reads no cursor's
  word 3 is inferred from that.
- **Cursors are not frozen**: positioned demand serves a cursor of the
  source as a cursor (`PdCur`, the nested serve first), and
  `serve_model.bend`'s `root.ok` notes the value's node "neither a
  cursor nor an eraser". So an index never travels into a template
  [inferred from those two places].

### What the laws say of it

- `find_exact`: on an exact ring, `rg.find` hands the heap back
  unchanged and equals `RG.first(t, view, d, far)`, the *first member in
  walk order* at that position [checked, `LAWS.bend:140-156`]. **No law
  says positions are distinct in a ring** [checked: `ring.ok`, `pend.ok`
  hold no such conjunct; `RG.unfound` speaks of the served cursor
  alone]. A map from position to cursor equals `RG.first` only under
  distinctness, a new invariant wanting an owner, or if it keeps the
  ring's order among equals (newest first).
- The upper proofs take the walks as lemmas: `cross`, `crossings` and
  the serve rewrite `R.rg.find(...)` by `find_exact`'s equation
  (`PROOF.bend:3326`, `:3431`, `:3694`, `:4311`); `join`, `join1` and
  `leave` cite `pred_exact.go` and `unlink_exact.go` (`:1080`, `:1960`,
  `:2104`, `:2181`) [checked]. So a `find` computed another way needs
  one law, the same equation; an `unlink` computed another way needs
  `unlink_exact` again, and the proofs above stand.
- The frame laws (`join_keeps`, `join1_keeps`, `leave_keeps`,
  `cursor_keeps`, `crossings_keeps`, and `SERVE_LAWS`' `serve_keeps`,
  `serve_root_keeps`) conclude on **words alone**: `P.rd(after, j) ==
  P.rd(before, j)` for j off the named regions; the table `a` is
  carried, never read [checked, `LAWS.bend:66-88`, `:393-412`]. An
  index in the words adds a region to every one of them; an index
  outside the words adds none.
- **No law mentions `rg.situ`** [checked by grep over the three law
  files]. Changing how a cursor finds its situating node rewrites no
  proof.
- The model is a list in walk order (`RG.ring`: `chain` and
  `apart.all`), on purpose: "a cycle holds by computation and a member
  taken out leaves the list" (`ring_model.bend:101-103`). The list `t`
  is what `ring.ok`, `pend.ok`, `cross.t` and `cr` step. A design that
  keeps `t` as the model's state keeps those laws' statements.

## 2. The designs, brainstormed

### Where an index can live at all

Bend and the kernel leave four places, and "a side array per copy" has
none of its own between serves:

- **H1, nodes in the words.** The allocator pops single four-word nodes
  off a free list; there are no contiguous blocks [checked,
  `kprim.bend:482-532`]. So an index in the store is pointer-linked
  nodes: a tree, a list of buckets, a companion node a cursor. Free
  words are scarce: a cursor has its header's 24-bit field (too small
  for a node reference in a store of 2^28 nodes) and word 3; the
  situating node's word 1 holds the static eraser (`core.bend:779`).
- **H2, the data table.** `H{w, a}`, `a: Array<V.Val>`, and `Val` is
  `Data` [checked, `val.bend:4`], so a table entry holds a persistent
  Bend value, not a linear `Array` [inferred from `docs/BendIssues.md`,
  "Arrays of linear values"]: a trie, under a constructor of `Val` that
  is never a glam value, as `VFree` is. No law anywhere reads the data
  table (`dt_get`, `dt_put`, `dt_take` appear in no law file)
  [checked]; 49 matches name `VFree` and would meet a new constructor.
- **H3, a third field of `H`**, a second word array. Every function of
  the kernel and every law of `spike/LAWS.bend` opens `H{w, a}`;
  records flatten into every call (`BendIssues.md`). The widest ripple.
- **H4, beside the heap, in glam's own state.** A value the core keeps
  with each net that hosts rings and hands to a serve; the kernel never
  sees it. It may be a linear array (a hash) or a `Data` trie. Wherever
  the heap goes it must go too (`Hx`, `Cx`, `Srcs` in `core.bend`), and
  a host at rest in a cell has only H2 to put it in.
- **H5, in the source.** One source, many copies: a slot a position
  cannot hold each copy's cursor. The source can hold what copies
  share: a dense number for each position that ever became a cursor's,
  beside the marks bitmap (`copied-nodes-untouched`) and the tree cache
  (`finished-trees-cached`), both keyed by position too.

### Designs that keep the ring as the only structure

- **D0, two pointers and a handed situ.** `find` hands back the
  predecessor its walk already carries (`Rw`'s `p`), so `join1` on a hit
  unlinks with no `pred` walk; the core hands the situating node it
  found to the serve (`core.bend:815` then `sv.pos`), one `situ` walk
  for two. No index. Removes two of about m + 4 walks.
- **D1, the sorted ring**, crossings sorted, one merged walk a serve
  (the plan's). O(r) a serve.
- **D2, tail insertion.** The situating node keeps the ring's last
  member, new cursors go last, so a `situ` walk from a new cursor is
  short. A heuristic; finds unchanged.
- **D3, buckets of rings.** A directory on position bits, each leaf an
  exact ring with a situating node of its own. Each walk falls by the
  bucket count; today's laws hold of each bucket. The frontier's `join`
  may take cursors of two buckets, a two-ring law; a fixed directory is
  still linear, a growing one rehashes. The directory needs a host (H1
  as a tree of nodes, so already D6 below).

### Designs with an index beside the ring (the ring stays the truth)

- **D4, a position index for `find` alone.** Position to cursor,
  maintained at `cursor` and at each unlink (the position is the
  cursor's word 2, read before it is freed). `pred` and `situ` still
  walk, less D0's savings.
- **D5, the ring fully indexed.** Beside D4, a map by cursor base to
  its predecessor and its situating node: a doubly linked ring whose
  back links and home links live outside the node, there being no word
  for them. Every heap write is the walking code's own (an unlink still
  writes the predecessor's word 3), so the heap after each operation is
  the specification's, word for word. Three maps to keep, and the map
  by cursor cannot be a copy's own: reaching a copy's index from a
  cursor needs the situating node, the walk it is there to remove. It
  is one a heap, and the heap's header has no spare word to name it
  (12 named words and 16 of events fill its 28) [inferred from
  `kprim.bend:171-209`].
- **Where D4 and D5 rest.** With the ring kept the situating node is
  full: the offset, the eraser, the handle, next. Its index can rest in
  the core alone, or in its word 1 if the eraser written there may go
  (`cells-freeze.nested.host.situ`, deferred; I did not trace what
  reads it). Only the star frees a word.

### Designs in which the index replaces the ring

- **D6, the star.** Word 3 of every cursor holds its situating node:
  "next" becomes "home". `situ` is a read. Membership and lookup are
  the index's: `find` a lookup, `unlink` a removal by the cursor's own
  position, `insert` a put; no `pred` exists. Nothing in a serve needs
  the ring's order (section 1), so nothing is lost but enumeration,
  which becomes a fold over the index. The heap's invariant becomes a
  fact a member, "word 3 holds s", with no order in it. The index is
  then one map, position to cursor, a copy; its host is a separate
  choice:
  - **D6a, a crit-bit trie of nodes in the words (H1).** A branch node
    of the cursor kind, a new form: the bit it tests in its field, two
    children, word 3 the situating node; leaves the cursors; the root in
    the situating node's word 3. One branch a cursor after the first, 8
    words a cursor where 4. Lookup at most 30 levels, about log2 r
    typically, two reads each. The shape is a function of the key set.
  - **D6b, a persistent trie in the data table (H2)**, on the
    position's bits, lowest first, the entry's index in the situating
    node's word 3. It travels with the heap by construction.
  - **D6c, a hash in a linear array beside the heap (H4)**: open
    addressing as `freeze.bend`'s `hm.*`, two words a slot, one array a
    heap keyed by situating node and position, or one a copy. Fastest
    per lookup. Removal wants tombstones or back-shifting; growth
    rehashes by scanning itself.
  - **D6d, a persistent trie beside the heap through a serve (H4), at
    rest in the data table (H2)**: taken out once at the serve's start,
    threaded through the crossings as the node map is, put back at its
    end. The ring's operations and laws see `(h, ix)`; the table is the
    glue's affair.
- **D7, cursor pairs.** A companion node a cursor holding previous,
  next and home: a doubly linked ring with O(1) unlink and situ, all in
  the words, 8 words a cursor. `find` still walks; it needs D4 anyway.

### Keys

- **K1, the position**, a source reference (node base and port), stable
  while the source lives (`copied-nodes-untouched`). Stored once, in the
  cursor's word 2, as now; an index may hold it again (a trie spells it
  by its path, a hash stores it).
- **K2, the cursor**: an index holding cursor bases alone, the key read
  through the cursor's word 2 (a hash of one word a slot; a sorted
  array with binary search). Halves a hash's memory at a heap read a
  probe. A sorted array inserts by shifting, r writes: linear again.
- **K3, direct-mapped over the source's references**, one array a copy
  as large as the source's words. Lookup is one read. A function of
  1,000 nodes copied 1,000 times, each copy touching ten, pays a million
  words; array creation fills word by word (`BendIssues.md`), which is
  what the freeze's source-sized map cost (the Freeze review's F1). A
  two-level table mends the memory and is a radix trie by another name.
- **K4, the source's dense numbering (H5)**: the source maps each
  position that became a cursor's to a small number, shared by every
  copy, the cache and the marks; a copy's index is keyed by the number.
  Shorter keys, shallower tries; a lookup in the source before each
  lookup in the copy, and a coupling of three designs not yet built.
- **Equal positions.** `RG.first` is the newest among equal positions
  and no law makes positions distinct (section 1). A map either takes
  distinctness as a new invariant, which the serve and freeze must then
  discharge ("no node copied twice into one copy"), or holds at each
  key the list of its cursors, newest first, which equals `RG.first`
  with no new premise and is the form `docs/Proving.md` already names:
  "a table by position is the same trie over a list split by its
  positions' bits".

### Bend's constraints, as they bear on these

- Arrays fill word by word at creation, so anything sized to the
  source is paid at each copy (K3), and a hash pays at each doubling.
- A linear array cannot sit in `Data`, so the table holds persistent
  structures only (H2); a persistent trie's put copies a path, and a
  value read out of the table and put back is counted, not moved,
  unless it is taken (the cost review found half the machinery's
  instructions in reference counting).
- No mutual recursion and fuel for every loop: a trie on the key's
  bits recurses on the word, needing neither; a hash's probe and a
  tree in the words want fuel and a bound (the key's 30 bits for a
  crit-bit tree; the table's size for a hash).
- Proofs over `U32` arithmetic are dear, over a word's bits cheap
  (`docs/Proving.md`): a hash function or a binary search meets the
  first, a bitwise trie the second.

### Not indexes, for completeness

Fewer cursors made (coarser materialization, the maintainer's "bigger
win"), or dead cursors removed under a criterion: the plan's other two
options, outside A. A split into live and dead rings fails on its own
terms: nothing is written at erasure (a dead cursor is one whose port
holds a static), so nothing can move it, and a find must reach the dead
all the same.

## 3. The designs judged

### The laws, in five groups

27 laws stand on the ring today: 23 in `glam/LAWS.bend`, 4 in
`glam/SERVE_LAWS.bend` [checked by `grep '^law '`].

| group | laws | what they lean on |
|---|---|---|
| chain | `pred_in_ring`, `insert_closed`, `pred_exact`, `unlink_exact`, `insert_exact` | word 3 as next, the list's order; about lines 240 to 1,060 of `PROOF.bend`'s 4,607 and the wrappers at 1,530 to 1,562, a fifth [inferred from where the defs stand] |
| find | `find_exact` | the walk equals `RG.first` |
| members | `insert_ok`, `cursor_ok`, `cursor_head`, `cursor_pos`, `join_exact`, `join1_exact`, `leave_exact` | `ring.ok` kept; cite `unlink_exact.go`, `pred_exact.go` as lemmas |
| frames | `join_keeps`, `join1_keeps`, `cursor_keeps`, `leave_keeps`, `crossings_keeps`, `serve_keeps`, `serve_root_keeps` | which words are written; "the members' word 3" is a region of each |
| the serve | `cursor_pend`, `join1_pend`, `cross_pend`, `crossings_pend`, `serve_exact`, `copy_pend`, `serve_ring_exact` | `pend.ok`, the model's fold `RG.cr` over `RG.first`; cite `find_exact`'s equation |

Three routes through them:

- **R-beside: the fast code proved equal to the walking code.** The
  walking code stays as the specification, called by no serve; each
  fast operation gets one law, "under the index's invariant, its heap
  is the specification's and the invariant is kept". All 27 laws stand
  as written, and compose with the new ones by rewriting; but they
  then describe code no serve calls, and the equality has to be carried
  up through `cross`, `crossings` and the materializer's composition
  that `SERVE_LAWS` names (one law an operation, then one a fold and
  one for the serve), with the mutants and the witness moved to the
  fast code. Cheap to state, not free. This is
  `docs/Proving.md`'s "Prove a fast version against a proved one", with
  its remark that an index whose shape is a function of its set makes
  the lift a computation. It requires the heap to be written exactly as
  now, so only D4 and D5 qualify.
- **R-model: the list `t` kept as the model, the chain dropped.**
  `RG.ring`'s `chain` and `apart.all` give way to "each member's word 3
  holds s" (D6). The chain group retires, five laws and their proofs,
  a put and a removal in their place. `find_exact`
  keeps its statement with the index's invariant for premise. The
  members group keeps its statements, `ring.ok` meaning something new
  (so approved again, as when `faces` was strengthened); its proofs
  lose their hardest lemmas, the walks over a split list. The frames
  shrink: an unlink writes no other member's word, so the region "the
  members' word 3" goes. The serve's group gains the index in `pend.ok`
  or beside it; `RG.cr`, already a fold over a view of positions,
  stands.
- **R-new: a new model.** A tree in the words (D6a), buckets (D3), a
  sorted ring (D1), cursor pairs (D7): the model's state changes shape,
  every group is restated, and the frames gain a region (branch or
  companion nodes) in every law, `SERVE_LAWS` included.

### Each design

Costs are per serve of c crossings on a ring of r, inferred from
section 1's counts.

| design | walks left a serve | memory a cursor | route | verdict |
|---|---|---|---|---|
| D0 two pointers, situ handed | about (c + 1)·r | 4 words | one law beside `find_exact` (the predecessor it hands back is `RG.before`), `unlink` given its predecessor | cheap, worth doing with anything; not A |
| D1 sorted ring | about 3r | 4 words | R-new: an order in the model, the crossings' fold restated for a pass | most rewriting for a line that still rises; drop |
| D2 tail insertion | finds unchanged | 4 words | `insert_exact` restated | drop |
| D3 buckets | all, over the bucket count | 4 words and a directory | R-new, a two-ring join | linear unless it grows, and then it is D6a; drop |
| D4 position index beside | about 2r (one `pred`, one `situ`, with D0) | 4 words and an entry | R-beside: no law restated; `find`, `cursor`, `unlink` each gain a refinement law | not A alone, and no word to rest in (section 2) |
| D5 ring fully indexed | none | 4 words and three entries | R-beside: no law restated | A with no law restated; a map a heap, resting in the core; the most machinery kept for ever |
| D6 star, one map | none | 4 words and an entry | R-model | A; the proofs shrink |
| D7 pairs | finds | 8 words | R-new | drop |

### Hosting the map (D4, D5, D6)

| host | lookup | growth, moving | several copies, nesting | collector, death | laws |
|---|---|---|---|---|---|
| H1 crit-bit nodes (D6a) | 2 reads a level, at most 30 levels | none: nodes never move (`net-nodes-double`); the store doubles sooner | one tree a copy, in the ring's own net, so nested and self copies need nothing | every branch is a node the collector must know as it knows a cursor; death walks the tree | R-new; a region in every frame law; the fuel is the key's bits, no heap bound |
| H2 trie in the data table (D6b) | a table read, then a level a bit that splits | none | an entry a copy; travels with the net | to be freed with the situating node: work to do, nothing frees an entry named from a cursor-kind node today [inferred]; enumeration a fold | the table enters laws that so far carry `a` erased, and no table law exists to build on |
| H4 hash array beside (D6c) | one or two probes | rehash on doubling, its own scan | one array a heap needs the situating node in the key, and a purge at a ring's death lest a reused node inherit entries | must be scanned at death | open addressing with removal is the dearest proof here; `hm.*` has no laws to reuse |
| H4 trie through a serve, H2 at rest (D6d) | a level a bit that splits; one take and one put a serve | none | as H2 | as H2 | the ring's laws see `(h, ix)`: heap lemmas and pure trie lemmas, the table in neither; the take and put are the materializer's glue, "not claimed" as its other glue is |
| H3 third field | best | as the words | as H1 | as H1 | every kernel law restated; drop |
| H5 the source | — | — | cannot hold a cursor a copy | — | only as K4's numbering, later, with the marks and the cache |

Points the table compresses:

- **A trie against a hash.** Proving decides it. A trie on the
  position's own bits is structural recursion with no arithmetic
  (`docs/Proving.md`, "A trie on a `U32`'s own word"); its shape is a
  function of its keys, so "the index of the list without y is the
  index with y removed" is a computation and a commuting lemma. A
  hash's shape depends on insertion history; its invariant is about
  probe sequences. The hash is perhaps three to five times faster a
  lookup [inferred]; at 200K instructions an element and under twenty
  lookups an element, either is a per cent or two.
- **Short rings.** A walk costs 6 or 7 instructions a member (section
  1); a persistent trie's put allocates a path. Below some ring length,
  twenty to fifty members by my guess, the ring wins [inferred,
  unmeasured]. Most copies may well be that short. This argues for
  measuring ring lengths over the ladder before choosing, and against a
  hybrid (two code paths, two sets of laws): pay the small constant.
- **Memory.** A dead cursor costs 4 words now. A trie adds a leaf and
  about one branch a key, Bend cells of size I did not measure; D6a
  adds exactly 4 words. The 6-head fold keeps 5 dead a cell either way:
  the index makes them cheap to pass, not cheap to keep. If their
  memory becomes the complaint, that is the plan's other option (a
  criterion for removal), and D6 does not obstruct it: a removal is one
  call.
- **Equal positions.** With lists at the leaves, newest first, every
  host above equals `RG.first` with no new invariant. I would still
  state distinctness as a law to come, since a second cursor at one
  position is the fault the dead cursors are kept to prevent.
- **Who else must set it up.** `use.cursor` and `use.situ`
  (`core.bend:775-779`), `glam/witness.bend`, the tests: each builds a
  ring by hand and would build the index, or call one constructor that
  does. Under D6 the hand-built ring is simpler than now (two home
  words).
- **The kernel.** Unchanged in every design but H3: it stops at kind 18
  and reads no word 3. Under D6a it must also never be led to a branch
  node, which holds since nothing links to one [inferred].
- **The sorted ring, once more.** Under D6 sorting has no object; the
  maintainer's "we might not need to abandon the simple ring" is
  answered by D4 and D5 (the ring kept, indexed) at the price of
  carrying both for ever.

## 4. Recommendation, and a slice to build first

### The end state I would aim at

**D6d: the star, with one map a copy.** A cursor's word 3 names its
situating node. The copy's cursors are indexed by a persistent trie on
the position's bits, lists at its leaves, newest first. The trie is
threaded beside the heap through a serve's copy, as the splice's node
map is, and rests between serves in the host's data table, its entry
named by the situating node's word 3, which the star frees. It is taken
out after positioned demand has returned, not at the serve's start (a
serve may end in a stop, and a self copy's demand runs in the same
net), by a swap that leaves a placeholder holding the slot
(`BendIssues.md`'s pattern for linear elements), so that the put
restores the table exactly.

Why this one:

- It is option A in full: no walk is left, by the dead or the living
  (`deep`'s growth, all its cursors live, is the same finds). Every
  dead cursor is kept, the lifecycle untouched.
- The words' invariant gets simpler, not different in kind: a fact a
  member, order-free, of the sort `AGENTS.md` asks for ("state shapes in
  which an invariant holds by computation"). The list `t` stays the
  model's state, so `ring.ok`, `pend.ok`, `cross.t`, `RG.cr` keep their
  shape.
- The proofs shrink: the chain group, about a fifth of `PROOF.bend`
  [inferred], retires; the frames lose a region; what is added is pure
  data, a trie's algebra, the cheapest kind of proof here.
- It adds no words to a cursor, no node kind, no kernel change, no
  field to `H`.
- Nested copies, self copies and several copies of one source need
  nothing: the index is the copy's own and lies in the copy's net.

What it costs: the maintainer's approval of a restated `ring.ok` and
five retired laws; a `Val` constructor that is never a glam value
(about 49 matches meet it), or another resting place; a constant paid
by short rings.

If no law may be restated, **D5** is the alternative: the ring kept
exactly, three maps beside it, one a heap and resting in the core; 27
laws untouched, a refinement law an operation (find, cursor, unlink,
situ), then one each for `cross`, `crossings` and the serve. It reaches
the same cost and keeps two structures in step for ever. I would not
choose it.

### The path

1. **Measure before building** (`AGENTS.md`, Measuring). In a worktree,
   count the steps of each walk by kind (find hit, find miss, `pred`,
   `situ`) and the ring's length at each serve, over the 6-head fold,
   `deep`, and the whole ladder; record the run. It tests section 1's
   arithmetic (about (m + 4)·r a serve, three walks not one) and shows
   how long ordinary rings are, which sets the constant a trie may
   cost. Half a day; no law.
2. **The trie as pure data**, a module of its own with its laws and
   mutants, on a side branch: get, put, remove a cursor at a position;
   the index of a list, `ix.of(t, positions)`; and three facts: a get
   on `ix.of` is `RG.first`; a put is `ix.of` of the list with the
   cursor first; a remove is `ix.of` of `RG.without`. No heap in it.
   Every indexed design wants it, so it is the slice with no regret,
   the place a new proof lesson would appear, and, with a native spike
   run of it, the measure of what a persistent trie costs in Bend.
3. **The star, on the same side branch, approved whole at its merge.**
   Word 3 becomes home; `find`, `cursor`, `join`, `join1`, `leave` go
   through the index; `rg.pred`, `rg.unlink`, `rg.situ` and the walk's
   fuel go (`ring-walks-fueled-by-heap` retires with them, a decision
   record to supersede); the chain laws retire, `ring.ok` is restated;
   `use.cursor`, the witness and the tests build stars. Acceptance: an
   element's instructions flat at n, 2n, 4n, for the heads and for
   `deep`, and the ladder's short rings no dearer than step 1 allows.

I would not stage through D4 (the index for finds, the ring kept): it
has no word to rest in, so it needs the core's plumbing or the
`.host.situ` ruling for a stage the star then discards. Likewise **D0**
(find handing back the predecessor, the core handing on the situating
node) is scaffolding: two small laws the star throws away. It is worth
building only if the star is refused or far off, and then it is the
cheapest fifth of the gain.

A gate on instructions an element
(`cells-freeze.sharing.cursors.growth.gate`) would hold the result.

### For the maintainer to decide

1. **Is "next" worth keeping once nothing walks it?** That is D5
   against D6. I see no use for a ring's order; an audit or a collector
   can fold the index. If a ring that can be walked with no index in
   hand has a value I have missed (a corrupt index reported by a walk,
   say), D5 keeps it.
2. **Where the index rests**, a question the star opens by freeing
   word 3. In the data table under a constructor that is no glam value,
   as `VFree` is: it travels with the net, and the table gains a second
   non-value, whose freeing with its ring is to be built. Or in the
   core beside each hosting net: no `Val` touched, every holder of a
   host gains a sibling. I lean to the table.
3. **Distinct positions in a ring**: a law to come, with its owner
   (freeze: no node copied twice into a copy), or lists at the leaves
   and no claim. I suggest both: the lists now, the law when freeze's
   are written.
4. **Dead cursors' memory.** A makes them cheap to pass and keeps
   every one. Is 4 words and a trie leaf a dropped field acceptable
   until a removal criterion or coarser copies come?

### What I am not confident of

- That a `Val` cannot hold a linear array, so that the table's index
  must be persistent [inferred from `BendIssues.md`, not tried].
- The persistent trie's cost in Bend, in instructions and in bytes,
  and so the ring length at which it wins. Steps 1 and 2 settle it.
- That no host rests with open cursors anywhere but where its data
  table rests too; I did not trace the core's holders of a host.
- Section 1's serve count comes from reading the code, not from a run.

### Ideas beside the question

- B6 of the Freeze review (no root placeholder) removes a find, a join
  and a free a serve under any design, and shortens `serve_exact`'s
  premises (`RG.unfound`).
- K4, one numbering of cursor positions in the source shared by the
  marks, the tree cache and the copies' indexes, is worth a paragraph
  in `cells-freeze.fragments`' design before either is built: three
  tables keyed by position, one hosting question.
- The climb's find a level (`cl.f`) becomes a lookup a level; with the
  marks (`.growth.marks`) it stops at the first copied node and the
  lookups go too.
