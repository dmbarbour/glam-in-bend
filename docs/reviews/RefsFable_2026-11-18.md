# References: the encoding and how far the laws state it

Second reviewer (Fable), 2026-11-18, for `cells-freeze.nested.host.repr`
(`docs/plans/Cells_2026-11-09.md:1884-1893`). Read-only; every claim is
checked against the tree at 526baad. Findings are F1, F2, …; a quoted
line is `file:line`.

## 1. The encoding today

`spike/kprim.bend:10-15`: "A node n is words 4n .. 4n + 3. Word 0, the
header … Words 1 .. 3: the links of ports 0 .. 2, a reference being
n * 4 + port."

`spike/kprim.bend:379-386`:

    def port(+r: U32) -> U32:
      (r .&. 3 : U32)
    # link two ports (word n * 4 + 1 + p is port p's link: the reference plus
    # one); …
    def link(h: H, +x: U32, +y: U32) -> H:
      wr(wr(h, (x + 1 : U32), y), (y + 1 : U32), x)

`spike/kprim.bend:404-409`: `era()` is `nil()`; `is_static(r)` is
`U32.is_eq((r .&. 3 : U32), 3)`. `spike/kprim.bend:31-32`: `nil()` is
4294967295. `spike/kprim.bend:425-426`: `pri(r)` is
`U32.is_eq(((r + 1 : U32) .&. 2 : U32), 0)`, true of port 0 and of a
static. `spike/kprim.bend:576-577`: `base(r)` is `r .&. 4294967292`.
`spike/kprim.bend:171-172, 213-217`: `at_fh()` is 0, `first()` 7,
`iface()` 28: the header is nodes 0 to 6, words 0 to 27. The free list
holds "a node's index plus one, 0 for none; each free node's word 1 the
next" (`kprim.bend:524-526`; `alloc.k` 518 reads
`((fh - 1 : U32) << 2n : U32) + 1`).

Three facts of this encoding carry the rest of the review.

(i) A node's base, its principal port's reference and its header's
address are one number, `b + 0`. The code uses the pun everywhere: the
kernel reads a pair's headers through the pair's references,
`int.x(…, P.rd(h, x), …)` (`spike/knet.bend:1147`); `P.node` answers
"its reference, port 0" (`kprim.bend:553`), and the generated rewrites
link a new node by its bare name, `P.link_x(h, n0, e2)`
(`spike/krules.bend:1660`); a cursor is both a ring member (a base,
`RG.bases`) and the port its peer links back to.

(ii) The eraser's "link word", `era + 1`, wraps to 0, the free list's
head. `glam/ring_model.bend:266-270`: "a static eraser (all ones) has its
link word on the head's word, off them all". `RG.port.ok` holds of the
eraser for that reason alone.

(iii) Zero words. `KM.m_new` zero-fills; a zero link word reads as node 0
port 0, inside the header, which the audit rejects
(`spike/knet.bend:1557`, `wa.at`: `(y >> 2n) >= P.first()`), and which no
immediate in the planned layout can ever equal, since every static there
carries suffix 11 (`docs/plans/NetData_2026-11-02.md:102-118`).

The other representation in the tree, `spike/store.bend`'s paged store
(`mk_ref(page, slot, port)` at 99-104, `nil` all ones at 83, the link word
`ref_port + 1` at `spike/net.bend:148-149`), is the oracle of
`spike/tools/differential.sh` (through `runterms.bend`). It is a separate
encoding and is left out of every count below; a differing oracle is a
feature of a differential test.

## 2. The proposal's bit work (A)

Call the proposal P: low bits 00 static; a node's ports at 01, 10, 11;
the header at word 0. Two ways to name ports in code follow from it:
P-a keeps the abstract ports 0 to 2 (`port(r)` becomes `(r .&. 3) - 1`,
port p's reference `b + 1 + p`); P-b renumbers ports 1 to 3 throughout.
The template layer is 0-based either way (`T.TE{n, p}`; `tref` at
`knet.bend:1252`, `sp.ref` at `glam/splice.bend:104`, `fz.peer.v` at
`glam/freeze.bend:281-283`), so under P-b a translation appears at those
boundaries.

**F1. The link word's place is not open: it is the reference itself.**
With ports at 01..11 and the header at word 0, port p's link word can
only be word `b + p`, the reference; "the reference plus one" would put
port 11's link word at `b + 4`, the next node's header. The plan's "to
settle" (`Cells_2026-11-09.md:1888-1889`) is settled by arithmetic. (A
header at word 3 with link word `r - 1` is the one alternative; it loses
`P.rd(h, base)` for headers and gains nothing.)

Operation by operation, today → under P:

- `base`: `r .&. ~3` → unchanged.
- `port`: `r .&. 3` → P-a `(r .&. 3) - 1`, a subtraction that folds into
  a comparison (`port(q) == 0` is `(q .&. 3) == 1`) but not into table
  indexing (`KR.ev_by(P.rk(hn), P.port(n))`, `knet.bend:693`); P-b
  unchanged, every table and comparison renumbered (§3).
- static test: `(r .&. 3) == 3` → `(r .&. 3) == 0`. An and and a compare
  either way; clang may emit `test r, 3` for the second. Negligible.
- `pri`: `((r + 1) .&. 2) == 0` → `(r .&. 2) == 0`, true of 00 and 01.
  One add fewer; `pri` runs twice per link noted (`P.note`,
  `kprim.bend:1471-1472`).
- the pair's either-static test (`knet.bend:1154`, `kchain.blend:278`):
  `((x .|. y) .&. 3) == 3` → `((x .&. y) .&. 1) == 0`, exact, since a
  pair holds only 01 and 00. Same ops.
- `link`: `wr(wr(h, x + 1, y), y + 1, x)` → `wr(wr(h, x, y), y, x)`.
  Textually simpler, and one instruction fewer per link word addressed
  by a reference: Bend masks every array index before addressing (the
  emitted C's `blk_at`, `((u32)i & ((1ull << (blk_cls(a) - lgs)) - 1))
  << lgs`, checked for this review by `bend -o x.c` on a two-line
  program in the scratchpad), and the add runs before the mask
  (`blk_at(_a_1, U32_BIN(_i_2, +, 1ull), 0)`), so it cannot fold into a
  displacement.
- a header read through a principal reference: `P.rd(h, x)` →
  `P.rd(h, P.base(x))`, one and more at each such site (§3, bucket B).
- `lw.mw` (`kstrat.bend:283`), the all-ones mask for a static,
  `0 - ((((l .&. 3) + 1) >> 2n))` → `0 - (((l .&. 3) - 1) >> 31n)`: same
  count. `lw.pair` (342), `(o1 .|. ((l1 + 1) .&. 2)) == 0` →
  `(o1 .|. (l1 .&. 2)) == 0`: one fewer. `lw.lev` (423),
  `((src .&. 3) + 3) >> 2n` ("aux or static", today the adjacent values
  1, 2, 3) → static 0 is no longer adjacent to the auxiliaries 2, 3:
  `(((src .&. 3) ^ 1) + 3) >> 2n`, one more. The two tricks that lean on
  adjacency trade places.

**F2. The eraser and nil need new values.** All ones has port bits 11:
under P it is port 3 of node 2^30 - 1, a port. Candidates: 0, or
0xFFFFFFFC (all ones above the tag). The choice decides F3.

**F3. Zero-initialized words change meaning.** Today 0 is node 0 port 0,
never valid, caught by the audit (§1 iii). Under P, 0 is a static. With
era = 0 a never-linked word reads as erased, silently. With era ≠ 0 it is
"a static other than the eraser, a fault, counted" on the rewrite path
(`knet.bend:1130-1131`; `se.go` tests `U32.is_eq(s, P.era())` at 1111),
and the audit still demands `y == P.era()` of a static (`wa.lk`, 1555).
But four readers branch on `is_static` alone and would take 0 for the
eraser: `fz.peer.k` (`freeze.bend:310`), `value.ps` (`knet.bend:1345`),
`pd.q.k` (`position.bend:131`), `wk.q.go` (`kdemand.blend:444`). So the
recommendation, if P is taken: era ≠ 0; nil may become 0 (zero is
"none", as the free list already has it), at the cost of the maintainer's
aside that the eraser shares nil's value (`kprim.bend:394-396`).

- word 0, the free list's head: P leaves it alone; the head is a header
  word, not a reference. What P removes is coincidence (ii): with
  era = 0xFFFFFFFC and the link word the reference itself, a law that
  reasoned about "era's link word" would slot it to 2^d - 4, the last
  node's header, a real word; with era = 0 to word 0 again. Either way
  the laws must stop reasoning through it (§5).
- immediates and packed values: the `netdata-refs` table
  (`NetData_2026-11-02.md:102-118`) hangs every static class under suffix
  11. Under P the table flips (static 00, classes in bits 3..2 and up);
  payload widths are unchanged. One genuine gain is available only under
  P: a 00 tag with the integer class at 0000 makes tagged small integers
  add, subtract and compare without untagging (n stored as n << 4; the
  tag is closed under addition), where today's integers at `bit 2 = 0`
  under 11 shift in and out. It costs F3 twice over: a zero word is then
  the integer 0. `capacity_leaves_tags` (`spike/LAWS.bend:1115`) is
  untouched: it bounds port references below 2^30 for the walk's tag
  bits, and the walk tags only port references (`kstrat.bend:402, 423`).

Verdict on the bit work: a modest textual gain (`link` and `pri` lose an
add; the static test may fuse), offset by `base()` at every header read
through a reference, by an add wherever a node's principal reference is
stored (it is no longer the base), and by the loss of the pun (i). In
instructions, a few either way per rewrite (§4); the simplification is
mostly in reading the code.

## 3. Migration cost, counted

Method. Every expression that touches the encoding in the non-generated
sources (`.blend` counted, their `.bend` outputs not; `krules.bend`
counted through `spike/tools/gen_krules.bend`) was read in context and
put in a bucket. The raw grep count of `+ 1 : U32` (kprim 38, knet 32,
kstrat 26, kdemand.blend 15, …) is not the migration count: most are
counters, or `base + 1`, port 0's link word, which is the same physical
word under both encodings (P-a).

**Bucket A, the encoding's definitions**, `spike/kprim.bend`: `nil` 31,
`era` 404, `is_static` 408, `pri` 425, `port` 379 (P-a), `link` 385,
`link.to` 433, `link_x` 438; the comments at 10-17 and 388-403. 8 defs.

**F4. Bucket B, the pun: a base used as a principal reference, or a
header read through one.** These are the sites grep cannot find, since
both are `U32`; the ones below come from reading the hot paths and the
glam modules, and are a lower bound.

- `spike/knet.bend`: `int.x(…, P.rd(h, x), …)` 1147, `int.y(…,
  P.rd(h, y), …)` 1038, `se.hx(…, P.rd(h, x), …)` 1133; `load.root`
  linking `root` from `P.node` 1263; `is_id` 978, `e2 == b + 2`,
  `e3 == b + 1` (ports by base). 5.
- `spike/kchain.blend`: header reads 162, 257, 271; `is_id` 102. 4.
- `spike/kdemand.blend`: `wk.hy(P.rd(h, y), …)` 343, `wk.root(P.rd(h, y),
  …)` 378, `interact.f(h, …, P.iface(), y)` 367. 3.
- `spike/kstrat.bend`: `scan.push(…, st, i)` 33 (a base pushed as the
  pair's reference); `lw.p2o`'s note `(b + oth) .|. 1073741824` 402;
  `lin.mv`'s `P.link_x(h, (b + 1 : U32), l2)` 647 (port 1 by base). 3.
- `spike/kprim.bend`: `pe.at` 1357, `(x + 1)` and `(rest + 1)` as port-1
  references. 1.
- `glam/splice.bend`: `P.link(h, top, x)` 152. `glam/core.bend`:
  `P.put_st(h, situ, P.era())` 780. Positions are port references
  (`RN.FzC{ne, (b + p : U32), …}`, `freeze.bend:281`), so `P.iface()` as a
  position at `core.bend:776` and `U32.is_eq(pos, P.iface())` at
  `materialize.bend:165, 295` move too. 5.
- `spike/tools/gen_krules.bend`: `new_end` 130-135 emits a bare `nJ` for
  port 0; one generator site, every generated rewrite follows
  (`P.link_x(h, n0, e2)`, `note(st, n0, e2)`, `krules.bend:1641-1777`).
  1.

B: 22 sites found.

**Bucket C, the link word of an arbitrary port reference** (`r + 1` →
`r`): `kprim.bend` `fa.ctl` 1298, `pop.x` 1485, `p2.y` 1552, `pq.y` 1687
(`KM.m_get(w, (x + 1 : U32))`, the popped principal's partner);
`knet.bend` `ev.y` 777, `se.put.go` 1055, `ld.put` 1273, `wa.live` 1536,
`wa.ports` 1573; `kchain.blend` 179; `kstrat.bend` `bd.era` 686;
`glam/ring_model.bend` `port.ok` 272, `off.ports` 429. 13.

**Bucket D, port-index semantics and inline bit tests**: `knet.bend:1154`
and `kchain.blend:278` (either-static); `kstrat.bend:283, 342, 423`;
`freeze.bend:46` (`(q .&. 3) == 0`), 283 (`(q .&. 3)` against a template
port); `position.bend:80, 131`; the 0-based template boundaries `tref`
(`knet.bend:1252`), `sp.ref` (`splice.bend:104`), `fz.peer.v`
(`freeze.bend:281`). 12 under P-a. P-b adds every `P.port` caller
compared with 0 or an arity (16: knet 8, kstrat 6, kdemand 1, plus
`fa.go`'s match on ports, `kprim.bend:1261-1270`), the generated tables
`kind_dir`, `walk_oth`, `ev_by` ("3 for none", `gen_krules.bend:1219-1225,
1595`), `lw.p2.o`'s and `lw.p2`'s `case 3` (`kstrat.bend:399, 414`),
`fz.port`'s literal ports (`freeze.bend:95-97`), `rc.ports`
(`knet.bend:1649-1653`), `wa.ports(…, 0, …)` 1578, `lin.side`
(`kstrat.bend:637`): about 30 more.

**Bucket E, looks sensitive, unchanged under P-a**: the free list's
`((fh - 1) << 2n) + 1` (7 sites in kprim: word 1 stays port 0's link
word); reads by base and port, `b + 1 + p` (`fz.port` freeze 76,
`rc.port` knet 1644, `nd.hd` kstrat 296, `lw.p2o`'s read 402, `sd.y`
498); `(top + 1)`, `(i4 + 1)`, `(root + 1)`, `(P.iface() + 1)`;
`glam/ring.bend`'s `(x + 1)`, `(y + 1)`, `(c + 1)` on cursor bases
(208-279: none change) and its `+ 2`, `+ 3`; `mine`'s `>> 2n`;
`lw.mw`'s `>> 7n`; `rc.see`'s `>> 2n`; `P.base`; `is_static`'s 37 callers
by name.

Tests: `glam/test_materialize.bend:70` writes a position 28 at word 34
(→ 29); `test_position`, `test_mark`, `bench_kprim` one or two each.
About 5.

Code total under P-a: 8 + 22 + 13 + 12 + 5 ≈ 60 sites in 14 files
(kprim, knet, kchain.blend, kdemand.blend, kstrat, gen_krules, freeze,
position, splice, core, materialize, ring_model, two tests). Under P-b
about 90. Excluded: `store.bend`/`net.bend` (§1); Blend, which knows
nothing of the encoding (no hit in `blend/`); the Nat models `kplace`,
`freelist`, `wiring`, `ctl` (no hit).

**Laws and proofs.**

- `glam/LAWS.bend`: `join_keeps` 83-84, `join1_keeps` 112-113,
  `leave_keeps` 501-502 state a faced port's link word as
  `… + 1 : U32` (bucket C). 3 laws, 6 premises. The `m + 1`, `m + 2`,
  `m + 3` and `P.at_fh()` forms are unchanged by P.
- `spike/LAWS.bend`: `link_keeps` 472-473 (`(y + 1)`, `(z + 1)`). 1 law.
  `node_keeps`, `node_next`, `node_index` (418-455) spell
  `((fh - 1) << 2n) + k`: word 1 stays, unchanged by P.
- `glam/PROOF.bend` (4,470 lines): 34 lemmas name a link word in
  reference form (`r`, `p`, `f`, `z`, `u` or `q` plus one): `fm_add`,
  `fm_sub`, `j1_faced.p`, `join1_exact.m`, `join1_keeps.m`,
  `join1_keeps.ms`, `join1_pend.m`, `join_exact.go`, `join_exact.m`,
  `join_keeps.m`, `l2_step`, `leave_exact.m`, `leave_keeps.m`,
  `links_out0-2`, `lol_step0-1`, `lx_faced`, `lx_faces`, `lx_full`,
  `lx_keeps`, `lx_keeps.s`, `lx_ring`, `o0_step`, `o2_step`, `o3_step`,
  `ones_out0-2`, `ones_z0-1`, `port_sub`, `ports_at`. Every one unfolds
  `P.link.to` or `RG.port.ok`. `spike/PROOF.bend`: `link2` (32621) and
  `link_keeps`'s few.
- Witnesses. `glam/MUTANTS.txt`: 38 mutations, 64 witnesses; 28 witness
  heaps hold the eraser literal (`9, 4294967295`: s at 8 faces the
  eraser) and all hold port references as words (`13, 41`, `17, 52`,
  `21, 44`, `25, 48`): every glam witness heap is re-derived under P.
  `spike/MUTANTS.txt`: 25 mutations, 34 witnesses, none holding the
  eraser; those over `alloc`/`free` use `((fh - 1) << 2n)` forms,
  unchanged.
- Docs: the `netdata-refs` table (`NetData_2026-11-02.md:102-118`);
  `static-links-count-as-nodes.md:7` ("port bits are 3", a record's
  context, superseded by a new record rather than edited);
  `Cells_2026-11-09.md:1661`; the kprim comments.

**F5. The real cost is bucket B, not the count.** Each B site is an
off-by-one of a whole word if missed: a header read where a link was
meant, a link written into a header. Nothing in the language flags it.
The nets that catch it are the audit (`wa.*`, `knet.bend:1525-1592`), the
differential test against the old store (an oracle with a different
encoding, which is why it should stay as it is), the library
(`spike/library.txt`) and the witnesses. The migration's budget is
therefore: the ~60 edits in a day, then the four checks, then the
proofs' 34 lemmas and 64 witnesses, which is the larger part.

## 4. Performance

Baselines. A rewrite on plain demand costs 1,182 to 1,944 user
instructions (`docs/plans/EvalSpike_2026-10-26.md:248-397`,
`scripts/count.sh`); the dead-port read that `erasure-at-write` rejected
cost 40 to 100 of them, "5% to 10% on plain demand"
(`docs/decisions/erasure-at-write.md`). Measured facts the review relies
on: U32 compare and arithmetic compile to about one instruction each; a
`+ k` on an array index is a real add, since Bend masks the index before
addressing (§2, `blk_at`); clang's inlining swings a build by up to 15%
and a change moves counts about 1% on paths it never touches
(`AGENTS.md`, Measuring; the Bend notes). So anything under ten or
fifteen instructions a rewrite is below what one build can show.

Per rewrite under P-a, from the code of `interact.f` → `go` → a
generated rewrite making two nodes and linking four external peers:

- either-static test (`knet.bend:1154`): 0.
- headers through the pair's references, `int.x`, `int.y`
  (`knet.bend:1147, 1038`): `P.base` once each, +2; passed down as bases,
  `go`'s `(a + 2)`, `(b + 3)` reads stay.
- external links `e_i + 1` → `e_i` (`P.link_x`, `P.link_xx`): one add
  each, -4.
- the new nodes' principal references stored into link words
  (`P.link_x(h, n0, e2)` → `n0 + 1`): a stored value, not an index, so the
  add is real: +2 to +4. (`P.node` answering `b + 1` moves the add to
  `renode`'s and `node.fin`'s header writes instead.)
- `pri` in `note` (`kprim.bend:1472`), twice per link, 2 to 4 links: -4
  to -8; the `n0 + 1` above gives one back per new-node link: net 0 to -4.
- `is_static(e_i)`, four times: 0 to -4 if clang fuses the compare.
- `pop.x`'s `m_get(w, x + 1)` → `m_get(w, x)` (`kprim.bend:1485`): -1.

Net: between -13 and +2 instructions a rewrite, on 1,200 to 1,900, a
saving more likely than a cost, and under 1% either way. The
collection's walk is the same story: `lw.pair` -1, `lw.lev` +1,
`scan.push`'s `i + 1` +1, `lw.mw` 0 (`kstrat.bend:33, 283, 342, 423`).
Demand's walk: `dn.can`'s `pri` -1, `wk.hy`'s header read +1,
`wk.q.go`'s `port(q) == 0` folds (`kdemand.blend:343, 419, 444`). Node
layout, words per node and cache behaviour are unchanged.

**F6. The encoding change is not a performance decision.** Its
instruction effect is within the noise of one build, in both directions.
If it is attempted, the gate is `spike/tools/count_builds.sh` four ways
and `gcbench.py compare` case by case (`AGENTS.md`, Measuring), with the
rule that no case may move beyond the forced-inline, profile-guided
build's noise. The honest reading of "simplify the bit work": the gain in
cycles is a few instructions in more than a thousand; the gain is in
reading `link`, `pri` and the laws.

One risk is not in the op count. `P.base` would gain 14 callers (bucket
B); `base` already has some 44 in the sources, so no segment splits. But `P.lw`, if
named as §5 asks, becomes a leaf def on the rewrite's path: the precedent
(`P.base`, `P.port`, `P.is_static`, all leaves called from the generated
rewrites) says clang inlines them to the arithmetic. Check with
`spike/tools/spot.sh` the day it lands, as for any hot-path edit.

## 5. Laws and representation (B)

### Where the encoding shows in the laws and their model

`glam/LAWS.bend`:

- `join_keeps` 83-84, `join1_keeps` 112-113: a faced port's link word as
  `(Pair.snd(…, Array.get(U32, w, (x + 1 : U32))) + 1 : U32)`; the free
  list's head as `AD.slot(P.at_fh(), d)` (82, 111, 408, 500).
- `leave_keeps` 501-502: `(p + 1 : U32)` and the face's `+ 1`.
- `cursor_keeps` 288: `(s + 3 : U32)`; `cursor_pos` 269: `(x + 2 : U32)`;
  `cursor_head` 251: word `x` and `P.hd2(18, R.cur.form(neg), 0)`.
- The rest state the heap through `RG.*` names; good.

`glam/ring_model.bend`: `m + 3` (`link.in` 31, `link.is` 113, `apart` 84,
`off.links` 98); `m + 1` (`faces` 287, `node.ok` 299, `enter.ok` 308,
`faced` 412); `y + 2` (`pos.is` 191, `off.pos` 264, `agree` 360, `cr.pv`
388); `r + 1` (`port.ok` 272); `P.is_static(f) || … (f + 1 : U32)`
(`off.ports` 429); `nw` 210; `P.base(m) == m` (`bases` 255); `P.at_fh()`
(`layout` 247).

`spike/LAWS.bend`: `node_keeps` 418-421, `node_next` 440-442,
`node_index` 455 spell `((fh - 1 : U32) << 2n : U32) + k`; `link_keeps`
472-473 `(y + 1)`, `(z + 1)`, unconditionally; `free_keeps` 492-495
`P.base(r) + k`; `capacity_leaves_tags` 1115 and the header laws
(`P.fld`, `P.lift`, `R.ev_header`) go through names and are fine.

### Findings

**F7. `RG.port.ok` holds of the eraser by an accident of its value.**
`ring_model.bend:266-272`:

    # … and a static eraser (all ones)
    # has its link word on the head's word, off them all
    def port.ok(+M: List<&2, U32>, +d: Nat, +r: U32) -> Bool:
      off.links(M, d, (r + 1 : U32)) && off.pos(M, d, (r + 1 : U32))

For `r = era`, `r + 1` wraps to 0 = `P.at_fh()`, and `layout` keeps
members off the head (247). So every member facing the eraser satisfies
`faces` only because 4294967295 + 1 = 0. The maintainer's rule
(`static-links-count-as-nodes`: "no code relies on where statics lie
among references") is kept by the code and broken by the model. Any
other eraser value changes what `ring.ok`, `node.ok`, `enter.ok` and
`pend.ok` mean, and `leave_exact`'s premise `hp` on `p = P.era()`
(`LAWS.bend:474`, used at `materialize.bend:171, 301`) would demand a
slot of a real word. `off.ports` (429) already has the right shape,
`P.is_static(f) || …`; `port.ok` wants the same guard.

**F8. Four frame laws state a static's link word, which nothing
writes.** `join_keeps`, `join1_keeps`, `leave_keeps` (above) and
`link_keeps` (`spike/LAWS.bend:457-475`, whose comment says "unless y is
static" but whose premises `hy`, `hz` do not) exclude from their
guarantee the slot of `face + 1` for a static face. Today that slot is
the head's, excluded by `hjh` anyway (`JoinLawsFable_2026-11-14.md`, F3:
"harmless"), so the laws are weaker than meant but not wrong; under any
other era they would exclude a real word. `crossings_keeps` got the fix
(`RG.off.ports`, 90b9d3c); the proofs already carry the guarded form,
`lx_keeps.s` (`glam/PROOF.bend:4121-4139`, premise
`Bool.or(sy, Bool.not(Nat.is_eq(AD.slot((y + 1 : U32), d), AD.slot(j, d))))`)
and `join1_keeps.ms` (4183).

**F9. Word offsets and the free list's arithmetic are spelled where a
name would do.** `m + 3` appears in four model defs and three code defs
(`rg.next` `ring.bend:18`, `rg.unlink.set` 128, `rg.insert.r` 141);
`((fh - 1) << 2n)` in three laws, seven code sites (`kprim.bend:499-701`)
and 39 lines of `spike/PROOF.bend`. Proving.md asks that a law name "the
function the program itself calls": a def the code calls and the law
names satisfies it; a bare `+ 3` in both is a copy of a body.

### Proposal: few definitions, the rest lemmas

Code names (the program calls them, so the laws may):

- `spike/kprim.bend`: `lw(+r) = r + 1`, "the link word of port r; a
  static has none, and no caller asks" — used by `link`, `link.to`,
  `link_x` and bucket C's sites; `node_at(+fh) = (fh - 1) << 2n`, used by
  `alloc.k`, `alloc.tap`, `free.fh` (its `(r >> 2n) + 1` inverse too),
  `gm.link`, `fl.step`, `fs.go`, `rsv.*`. Leaves, like `base` and `port`
  (§4).
- `glam/ring.bend`: `facew(x) = x + 1`, `posw(x) = x + 2`,
  `nxw(x) = x + 3`, used by `rg.next`, `rg.unlink.set`, `rg.insert.r`,
  `cursor`, `jn.u`, `jn.w`, `jn1.*`, `lv.w`.

Model names (no code calls them; laws and proofs do):

- a heap-level model both LAWS files can import — `spike/LAWS.bend`
  cannot import glam's `RG`, so a `spike/kmodel.bend`, say `KMd`:
  `lw(r) : Maybe<U32>`, `None{}` where `P.is_static(r)`, else
  `Some{P.lw(r)}`: "a port's link word, none for a static";
  `off.port(d, r, j)`: `lw(r)` none, or its slot not `j`'s;
  `off.ports(rs, d, j)`; `nw(b)` and `off.node(d, b, j)`, defined here
  and kept in `RG` as one-line aliases, since `glam/PROOF.bend` names
  `RG.nw` and `RG.off.node` throughout its 4,470 lines and a rename
  would move them all and recheck the file.
- `glam/ring_model.bend` restated through them: `port.ok(M, d, r)` =
  `off.port`-style over `lw(r)` for the links and the positions (static
  ports faceable by all, by computation); `faces.m`, `node.ok`,
  `enter.ok` unchanged in text; `off.ports` = `KMd.off.ports`; `face(v,
  d, m)`, `pos(v, d, m)`, `nxt(v, d, m) : Maybe<U32>` reading
  `R.facew(m)`, `R.posw(m)`, `R.nxw(m)`, so that `link.in`, `link.is`,
  `pos.is`, `agree`, `cr.pv`, `faced`, `apart`, `off.links`, `off.pos`
  carry no `+ k`.

Laws that change, and how:

- `join_keeps`, `join1_keeps`, `leave_keeps`: `hju`, `hjw`, `hjp` become
  `KMd.off.port(d, <the face>, j)`; `join1_keeps` thereby exempts static
  ports, the planned repair (`Cells_2026-11-09.md:1890-1893`), a
  strengthening. `cursor_keeps`: `hjs` becomes
  `RG.off.links(Con{s, Nil{}}, d, j)`, an existing name. `cursor_pos`:
  `R.posw(x)`. `cursor_head`: unchanged.
- Through `port.ok`'s guard, every law over `ring.ok`, `node.ok`,
  `enter.ok` or `pend.ok` changes meaning (15: `join_keeps`,
  `join1_keeps`, `insert_ok`, `cursor_ok`, `cursor_head`, `cursor_pos`
  (their `hx` is `RG.enter.ok`, LAWS 250, 268), `cursor_pend`,
  `join1_pend`, `cross_pend`, `crossings_pend`, `crossings_keeps`,
  `join_exact`, `join1_exact`, `leave_exact`, `leave_keeps`), as the
  2026-11-17
  strengthening of `faces` did (`Cells_2026-11-09.md:1701-1717`). What
  is lost for a static face was the accident; what `layout` gives (the
  head off every member) stays.
- `spike/LAWS.bend`: `link_keeps`'s `hy`, `hz` become `KMd.off.port`
  (stronger); `node_keeps`, `node_next`, `node_index` name
  `P.node_at(fh)`; `free_keeps`'s four premises become
  `KMd.off.node(d, P.base(r), j)`.

Cost:

- Approval: law texts change, so one `--no-ff` merge with every `Law:`
  trailer and the maintainer's holistic yes, as the project does
  (`AGENTS.md`, Laws). No law is weakened; four are strengthened.
- Proofs: wrappers for the most part. `lx_keeps.s` is already
  `off.port` unfolded, so `link_keeps`, `join_keeps`, `leave_keeps` take
  it as `join1_keeps` does. The `faces` family (`fm_sub`, `fm_add`,
  `port_sub`, `faces_write`, `lx_faces`, `links_out0-2`, `ones_*`,
  `ports_at`) gains a static case each, the easy one: `link.to` writes
  nothing. The `faces` strengthening of 2026-11-17 was the same kind of
  edit across the same lemmas and is the measure of the work: a day or
  two. `node_at` and `posw`/`nxw` are rewrites by `{==}`.
- Witnesses: the 64 glam and 34 spike witness terms stand as written; B
  changes no value. Whether each mutation stays caught is another
  matter: the frame laws get stronger (a static face's slot no longer
  excused), but a conclusion over `ring.ok` gets weaker for static
  faces, and a mutation that leaves a static-looking value (bits 11) in
  a face, which today must land its `+ 1` off the members' slots, would
  now pass `faces`. That is for `scripts/one_law.py --mutants` to show,
  which a read-only review cannot run. Mutants that mutate
  `(p + 3 : U32)` (`glam/MUTANTS.txt:9-13`) mutate `R.nxw`'s callers or
  body instead.
- Gate: the proofs' recheck, 30 to 50 s; the mutants' runs.

What B does not do: it does not take the encoding out of the proofs.
`lx_keeps` still reaches `y + 1`, through `P.lw(y)` and one unfolding
equation. It moves the knowledge to two code defs, two model defs and
their unfolding lemmas, and makes the statics' case a `Bool` the laws
name rather than a value they trust. That is the shape the maintainer
asked for: representation in few definitions and proof lemmas.

## 6. Order and recommendation (C)

**F10. B first, and B is wanted whether or not A happens.** F7 is a
latent error in meaning today: the laws' `faces` holds of the eraser by
its value, which the maintainer ruled out for the code. F8 is the repair
the plan already names. Both are a model change plus wrapper proofs, one
approval.

**F11. After B, A is cheaper and safer; before B it is paid twice.** The
34 lemmas of §3 would, after B, name `P.lw(y)` and `KMd.off.port`, and
the law texts carry no `+ 1`: A then changes `P.lw`, `P.is_static`,
`P.pri`, `P.port`, `P.era`, `P.nil`, `KMd.lw`'s unfolding equation and
the witnesses' heaps, but no law's statement, so no second round of
approval on the laws' wording and no re-reading of 15 laws' meaning.
Done the other way, every `+ 1` premise is rewritten for A and again for
B.

Recommendation: do not switch now; do B; take A only under conditions.

1. B first, as §5 lays it out, on a side branch, merged with its `Law:`
   trailers; `cells-freeze.nested.host.repr` closes with a decision
   record on the model names and the static ports' exemption.
2. A waits for `netdata-refs` (`NetData_2026-11-02.md:90-130`), the one
   place where P pays: if the immediates' layout wants 00 tags so that
   small integers compute under the tag (§2), P earns its migration;
   otherwise the bit work is neutral (§2, §4) and the pun's loss (F4,
   F5) is a risk with no return. The same record settles era, nil and
   the zero word (F2, F3): era ≠ 0 recommended.
3. If A is taken: P-a (templates, tables and `R.port_pol` stay 0-based;
   `P.node` keeps answering the base; a named `P.pr(b) = b + 1` gives the
   principal's reference, so that bucket B's sites read as intent, not
   arithmetic); the generator (`new_end`), the tests and the witnesses
   in the same change; the eraser's new value in `P.era` alone.
4. Acceptance: the audit, the differential test against the old store on
   its old encoding, the library, `--verdict`, every mutant; then
   `count_builds.sh` four ways and `gcbench.py compare`, no case beyond
   the forced-inline build's noise (F6). A worse count in any build is a
   stop, not a note.

If the aim is the readability of the bit work alone: B removes the
`+ 1`s from the laws and names the two bit tests the model makes; the
code's own tricks (`pri`, `lw.mw`, `lw.lev`, `lw.pair`) are five lines,
each commented, and P changes their shape without shortening them.

## 7. Open questions for the maintainer

1. Under P, which value is the eraser, and does it still share nil's
   (F2)? With nil = 0 a zero word is "none", as the free list's 0 is; the
   eraser then is a constant of its own, and the four `is_static`-only
   readers (F3) either test `P.era()` or are shown never to meet another
   static.
2. Should the integer class take tag 0000, so that tagged integers add
   under the tag, at the price that a zero word is the integer 0? This is
   the only argument found that makes A pay; it belongs to
   `netdata-refs`.
3. P-a or P-b: abstract 0-based ports with `port(r) = (r .&. 3) - 1`, or
   ports 1 to 3 with 0 for "none" in `kind_dir`, `walk_oth` and `ev_by`
   (today "3 for none", `krules.bend:104-106, 150-153`), which fits the
   tables better but touches about 30 more sites.
4. Where the shared heap model lives: a `spike/kmodel.bend` imported by
   both LAWS files (glam imports spike, not the reverse), or `RG`
   duplicated in spike. And does the maintainer count `port.ok`'s guard
   as a change of all 15 laws over `ring.ok` and `enter.ok` (by the rule
   it is), to be approved at one merge?
5. Is naming `P.lw`, `P.node_at`, `R.facew`, `R.posw`, `R.nxw` in the
   code acceptable as hot-path leaves, measured by `spot.sh` once, with
   `P.base` as the precedent?
6. Does the old store stay on its own encoding as the differential
   test's oracle (recommended), or follow A?
7. `cursor_head` names `P.hd2(18, …)`: is the header's layout, as a
   named constructor the program calls, abstract enough, or does the
   maintainer want a `R.cur_hd(neg)` the code and law both call?
