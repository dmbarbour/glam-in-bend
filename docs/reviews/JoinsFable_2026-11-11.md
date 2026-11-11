# Joining a copy's cursors: a second review

Written by a Fable sub-agent on 2026-11-11 at the agent's request, reviewing the design for joining cursors; kept as written.

Repository claims carry their path; inferences are marked. "Copied" below means copied into one copy `C`; "finished" is the source's fixpoint (`glam/freeze.bend`, header); a "subtree" is the principal tree hanging from a position.

## 1. Uniqueness and completeness, checked

**The copy's side holds.** The maintainer's argument can be made rigorous with three facts, the first two my inference from the kernel's rules, the third from the design:

- *(M) Monotone.* A rewrite relinks only the external peers of its pair (`spike/knet.bend`, `link_pairs`); a finished node is in no pair; so a finished node's principal peer, and every wire between two finished nodes, never changes, and finished nodes stay finished. Fusion was the exception; `copied-controls-unfused` closes it.
- *(D) Disjoint.* By (M) a copied node's principal chain is fixed forever and leads, through copied nodes, to the interface. So a copied node is never in the subtree of an outstanding position, and the subtrees of two outstanding positions share no node. Hence a materialization, which walks only principal-facing peers, never walks into a copied node: each source node is copied at most once per copy.
- *(F) Frontier.* When a node is copied, each aux port whose peer is not copied with it gets a cursor keyed by that port (the design's completeness clause). By (M) the only way a later materialization reaches a copied node is through such a wire, so the join site is always a cursor position of this copy. This covers a source reduced further between two materializations into one copy: whatever became finished meanwhile is uncopied, and touches the copied region only at cursors.

Uniqueness then follows: one cursor per copied port, each port copied once. The cases the brief lists:

- **A finished node of another tree.** `\x -> g (h x)`, `g = \z -> z + 1`, `h = \w -> w * 2`, both handles. Serving the negative cursor at `(Fn, result)` ends with the `+1` and `*2` operators finished, but both hang under `(Fn, arg)`, the positive cursor: the subtree under the served position is empty. The materializer must climb from the node the position faces to its tree root (`*2`, whose principal faces `(Fn, arg)`), copy that subtree, and join at both cursors. The root's parent port is always a cursor position of this copy, by (F), and that is the only stop test the climb has: the first finished node is the one the position faces, and the transient map knows nothing of earlier materializations, so each step up looks the parent port up in the ring and stops when the lookup hits, O(depth · r).
- **Cursors at both ends of one wire.** They do occur: `\x -> (\y -> y) x` has cursors at `(Fn, result)` and `(Fn, arg)`; the beta links the two positions directly (`link_pairs` resolves the identity's loop). The serve then materializes *nothing* and joins cursor to cursor. The design's step 3 speaks only of "each wire leaving the new nodes"; the zero-node serve must be stated, and it is the maintainer's original identity case. A wire joins a positive port to a negative one, so its two cursors are one negative and one positive, and the negative one's serve finds the join; a wire with two negative cursors cannot exist.
- **A copy copied by fans.** Correct as designed, and the two rules are exactly what keeps one ring per materialized copy: `rule.copy KFn` (`spike/rules.bend`) leaves a Merge whose out faces the positive cursor and a Copy whose input faces the body's negative cursor; the join later links the source's consumer to the Merge, and the ordinary rules distribute it. Both logical copies share one ring, as GAL shares one body.
- **Erasure.** Erasing the copy's Fn sends a static `EraN` to the negative cursor and a static `EraP` to the positive one (`KN.static_erase`). Joining a consumer later to the `EraP` is right: it is the void an erased function's variable has. A ring of dead cursors is reachable from nothing and is collected.
- **Joins at negative cursors, levels, the served cursor.** Fine: the join links the raised new node to whatever faces the cursor, the wire a whole copy would have had, controls the host pushed onto it included. The served cursor is one more join site, looked up like any other.

**Where the argument fails: the source's side.** "Each port is a separate source position" and "a position stays valid while the source lives" (the Cells plan) assume a finished node keeps its slot, kind and port numbering. Three things in the kernel break that, none of them fusion:

1. **Events renumber ports.** An eraser reaching a finished fan's side from the pending region runs the table's event: `ev.copy`/`ev.merge` (`spike/rules.bend`) make `CopyR`/`MergeR` with the kept side moved from port 2 to port 1; `lin.mv` in `spike/kstrat.bend` does the same in the sweep. Example: `\x -> k x (h x)`, `k a b = b`. The Copy under `x` is copied with positive cursors at `(Copy, 1)` and `(Copy, 2)`; `k`'s beta puts a static on `(Copy, 1)`, the event makes `CopyR`, and the right output is now port 1. When `h x` is served its wire reads `(Copy, 1)` and the search finds the *left* cursor: the right value by luck for a Copy, with a dead side never told; the wrong context's value for a `MergeR`.
2. **The sweep frees finished nodes.** A collection under positioned demand (`collect_cycle`, `spike/kstrat.bend`) marks from the interface along inputs only and frees the rest. `\x -> k (p x) 5` with `p` an operator: after `k`'s beta the operator's result holds a static, the event makes it a `DOp`, still finished (its principal faces `Fn.arg`), yet no input leads to it, so the sweep frees its slot while the copy holds a cursor at `(p, 1)`. A fan with both sides erased becomes an eraser and is freed the same way (`events_erase_last`).
3. **Freed slots are reused.** A cursor at a freed position then matches a wire of whatever node takes the slot: a wrong join, and a stale bit in the finished bitmap.

So uniqueness is conditional on a *position-stability* invariant the kernel does not keep: in a source, a finished node is never freed, re-kinded or renumbered. The cheap form, by analogy with the mark on controls: events and the sweep's dead-kind edits refuse finished nodes (a bitmap read per event; the bitmap OR-ed into the sweep's marks), and the static stays in the link word, which `erasure-at-write` already allows ("strategies that run no events leave a static on a fan's side"); the copy that takes the node runs the event, as the materializer must whenever it writes a static.

**Dead cursors.** The design frees a dead cursor "at the next search", safe only if its position is never reached again. My inference: under `net-scoped-arguments` the subtree under a dead position is reached from no live position, so it is safe in scoped nets; but a search that finds nothing cannot tell "copied and dropped" from "finished in another subtree" (the bitmap says finished, not copied), so an error there silently makes a second cursor on one wire. Keep dead cursors findable until joined.

## 2. The per-copy structure

**In the host's heap, not the core.** The core sees no erasure and no collection, so a record it keeps per copy can be freed only with the host net; copies are made per application, so that is a leak. The structure must live where the collector can find and drop it: among the host's nodes. That settles the maintainer's "side table or shared structures" in favour of the heap, with one exception below.

**Three layouts, all 4-word nodes** (`spike/kprim.bend`, header: kind 6 bits, form 2, field 24; words 1 to 3 links or payload).

- *A, the design.* Cursor: port in word 1, position (a 30-bit reference) in word 2, next in word 3, offset in the field. Head: source handle, next, offset. Singly linked; the head found by walking; a dead cursor is a kind change, unlinked lazily.
- *B, head pointer.* Pack the position into form plus field, 26 bits: a node index below 2^24 and a port. Word 2 then holds the head's reference, word 3 the next cursor: the source and offset in one read, the offset stored once. The price is a cap of 2^24 nodes (256 MB) on a source, reported as an error, not a crash, when a position does not fit.
- *C, a real ring.* Cursor of arity 3: port 0 the real port, port 1 `prev` (negative), port 2 `next` (positive); the position packed as in B. Head of arity 2: `prev`, `next`, the handle in word 3, the offset in the field. The ring is then ordinary wires: the wiring audit passes, `walk_follows_inputs` passes (port 1 is an input, so the directed walk follows the ring backward round the cycle), and erasing a cursor is an ordinary rule, `RWire{[], [lk(ex(2n), ex(3n))]}` for a negative cursor (B's aux peers; `ex(0n)`, `ex(1n)` for a positive one, which is A): the eraser meets the cursor, and its two ring neighbours are wired to each other. No dead kind, no lazy unlink, O(1) removal. Two laws need the maintainer: `two_outputs` (a negative cursor has outputs at ports 0 and 2, which the law exists to flag for review) and `static_erasure` (the kernel's shortcut would put erasers on the neighbours' ring ports; cursor kinds must take the rule instead).

In every layout the head needs no real port: arity 0 for A and B (the audit skips it, demand never meets it), arity 2 in C. And in every layout a **dead cursor can simply be a cursor whose port holds a static** (`is_static` on word 1): no kind, no event, the join writes the static into the new port with `put_st`.

**Costs** (r cursors in the ring, m wires leaving a materialization, n nodes copied):
- per serve: O(r) to the head in A and C, O(1) in B; positioned demand; the materialization O(n);
- per join or new cursor: O(r) scan; O(r·m) per materialization. A cheap upgrade without ids: keep the ring sorted by position and sort the m far ends, one merge pass, O(r + m log m);
- per copy: 16 bytes a cursor and a head, no table in the source, no core state;
- one cost already paid by `freeze_finished` and to be removed before measuring: the transient map is an array sized to the *source's capacity* (`fz.cap`: `depth_for(31n, cap)`), O(cap) for every materialization. A per-source scratch array kept in the book entry and stamped per materialization, or a hash, is needed.

**Dense ids.** Assigned without touching the net: the source's book entry keeps a hash from position to id, given the first time any copy makes a cursor at that position; nodes never move (`net-nodes-double`), so positions are stable keys exactly as far as section 1's stability holds. A cursor carries the id in the field and the copy's table is an array indexed by id. The catch is the array: the host heap's free list hands out single nodes, not contiguous runs, so an in-heap table is a chain of 4-word blocks walked by id/3, not O(1); an O(1) array lives only in the core, which cannot free it. Dense ids buy O(1) joins only with a block allocator or a leak; they inherit the stability problem; fragments are superseded as the source reduces. Not now.

**The collector** (`spike/kstrat.bend`, the directed walk; `KN.reach`/`KN.sweep` are used by `spike/kernel.bend`'s runners, not by glam's core, and follow ports only). In A and B the ring word is not a port: the walk must be told to follow it (a pseudo-input in `KR.kind_dir`, a reference with port bits 2) and the sweep's boundary pass (`bd.era`) must never write an eraser through it. Two properties make this safe: a ring is marked all or nothing (any reachable cursor marks the whole cycle, head included), so no freed cursor's ring word faces a marked node; and a positive cursor is entered only through the ring, its port a true input followed to the argument. Heads live exactly while some cursor of the ring is reachable, as the design says. In C none of this is special.

**Events.** Cursor kinds make none (`events_fit_header` holds) and hold no table payload (`payload_past_links`). The need is the reverse: the materializer is a new *writer* of statics (a copied port whose source peer is static, a join onto a dead cursor), and `erasure-at-write` makes writers run the table's events; the loader and the splice are the models.

**A host frozen in turn.** The design's answer is right, and the finished test shows why it is needed: a cursor's principal faces a finished node's aux port, so it would read as finished and be copied, the deep cursor the maintainer wants chained instead. Treat cursor kinds as unfinished when `H` is frozen: `H`'s copy gets a cursor *into H* at the consumer's port, and serving it runs positioned demand in `H`, which meets `H`'s own cursor and serves `S` into `H`, shared by every copy of `H`. Positive cursors of `H` are unfinished for free, the value facing one being in a pair with it. Heads are never copied (no real port reaches them). A value leaving its net with a cursor at the root is a need at the interface, served first; one leaving with cursors inside is this freezing.

## 3. Other concerns, laws, tests

**Demand's test for a need** (`may_need` in `spike/kdemand.blend`) is "an application or strict call meeting table data". A negative cursor is a need whatever faces it, so the test widens to "B's kind is 18", and the core dispatches on the kind rather than on a table value (`KS.need` reads word 2 through `val_lazy`; a cursor's word 2 is not a table index). Two places read a positive principal as a value and would misread a cursor: `wk.root` (kinds 11 and 7 aside, "anything else is the value": a cursor at the root would end in state 1 with no data) and `fw.scan`, whose state 7 is the frontier under positioned demand, as the Demand review says.

**Not every negative principal meeting a negative cursor is a need.** `DOp` (a dead operator erases whatever it meets, `ev.op`) and a static `EraN` must *erase* the cursor; demanding it would do work nothing needs, against `net-demand-whnf`. Ap, Op, Copy, CopyL/R, Lift and the interface wait. The design lists the eraser; the dead operator is missing.

**Positive cursors and the rule table.** A positive cursor's pairs (with Fn, Data, Merge, LiftC, EraP, FnD, and a negative cursor of another copy when `f (g x)` feeds one source's argument from another's result) are waits. Demand never sees them: the walk enters nodes by outputs and a positive cursor has none, so `RStuck` costs nothing there; but the eager strategies and `KN.static_erase` count a stuck pair as an error, and the laws over the table will each meet the new kinds. A wait is a third outcome beside "rule" and "stuck"; naming it in the table is cleaner than letting stuck mean two things.

**Controls at cursors.** The design is right that a control's shift cannot be folded into the offset (a control shifts levels above its index only, `P.lift`). A Lift facing a negative cursor is a need; a LiftC facing a positive cursor waits and the joined consumer crosses it by the rules. Fusion is never tried at a cursor, since `fuse` looks only at links a rewrite made between two controls.

**The finished bitmap** (`cells-freeze.demand`) must be extended after every materialization and goes stale the moment a finished slot is freed: one more reason for section 1's stability invariant, since the frontier test reads it.

**Marks on controls** belong to the node, as the design says; but with several copies the mark must be set by the *first* copy to take the control and never cleared. Fine. What the mark does not cover is the aux-side events of section 1.

**Resume.** With one stack, two serves of one copy never interleave (the Positions reviews), so a cursor is never found already joined on resume; under parallel tasks it can be, and resume must then re-read the net rather than assume a cursor faces `top`.

**Laws worth stating** (the wiring model first, `spike/wiring.bend`; the kernel's table later):
1. *Position stability.* In a source, a finished node is never freed, re-kinded or renumbered: `copied-controls-unfused` generalized to events and the sweep.
2. *Monotone finishedness,* from (M): a finished node stays finished and a finished-to-finished wire is never rewired.
3. *Join sites.* Every wire between a copied node and an uncopied one ends at a live or dead cursor position of that copy, and no position has two live cursors in one copy: the invariant of a model of copies, provable by induction on serves given 1 and 2.
4. *Rings all or nothing* under the collector's reach, in A and B.
5. *Cursor kinds* make no events, hold no payload, every pair with a positive cursor is a wait, and a negative cursor meets only needs and erasures.
6. *The oracle,* as a differential check rather than a proof: serve-then-reduce gives the value reduce-then-copy-whole gives, and the linked build with fans gives (CursorsFable's idea 5).

**Testing narrowly, before any kernel change.** A model in Bend over `spike/net.bend` with a source, k copies as nets of their own, placeholders and a serve function, compared on normal forms against copying the fully reduced source whole. Families with what each must show:
- the identity and `\f -> \x -> f x x`: whole copies, no cursor (built already, `glam/test_freeze.bend`);
- `\x -> (\y -> y) x` and a chain of k identity redexes: a zero-node serve, one cursor-to-cursor join;
- `\x -> g (h x)`: the climb to another tree's root, two joins in one serve;
- `\x -> x v v`, `v = h x`, `h` a handle for the identity: the beta wires `v`'s copy fan to `x`'s, and serving the first argument's cursor materializes that fan and joins the second argument's cursor too, a negative cursor still outstanding;
- `\x -> k x (h x)` and `\x -> k (h x) x`, `k a b = b`: the `CopyR`/`CopyL` events on a finished fan, which today fail and must pass once stability holds;
- a copy duplicated by a host fan, each half applied to a different argument: the Merge facing a positive cursor;
- one half erased, then the whole copy erased: dead cursors, the ring collected;
- `f (g x)` across two sources: a positive cursor facing a negative one.

Counts to record on `glam/sharing.txt`'s families and the library, at n, 2n, 4n: cursors per copy, ring length at each serve, far ends looked up and scan lengths, joins (negative, positive, cursor-to-cursor, onto a dead cursor), nodes materialized per serve, and the transient map's size against the nodes copied.

## 4. Recommendation and questions

**Recommendation.** The join design is sound on the copy's side and should be built; what it rests on is not yet true on the source's side. In order:

1. **Position stability first,** as a law and a kernel rule before any cursor kind exists: in a source, events and the sweep leave finished nodes alone, as fusion does. The design's correctness argument, the finished bitmap and the positioned walk's frontier all read positions, and events and the sweep break them today (section 1). Without it the identity-redex tests pass and `\x -> k x (h x)` fails silently.
2. **The ring in the host's heap,** never a core table (section 2). Build layout C if the maintainer accepts a 2^24-node cap per source: erasure becomes an ordinary rule, the audit and the walk laws hold, and no dead kind or lazy unlink is needed. Otherwise layout A as designed, with a dead cursor being a cursor whose port holds a static, and the ring word declared to the collector. In both, the head has no real port.
3. **The materializer's three cases:** a subtree under the served position; a climb to another tree's root; an empty tree joining cursor to cursor. Every wire, the served cursor's included, goes through one lookup: the transient map, then the ring, then a static or a new cursor.
4. **Counts before structure.** Ring lengths and scan lengths on the sharing families and the library decide whether a sorted ring, and only then dense ids, are worth anything; the O(cap) transient map is the cost to remove first.
5. **The model-level tests of section 3** before the kernel changes, with the oracle (reduce first and copy whole, and the linked build) as a differential law.

**Questions for the maintainer.**
1. May finished nodes of a source be exempt from events and from the sweep's dead-kind edits and frees, as `copied-controls-unfused` exempts controls from fusion? A static then stays in the link word, as strategies without events already leave it, and the copy that takes the node runs the event. This is the one ruling the design cannot do without.
2. Is a cap of 2^24 nodes on a source, reported as an error past it, acceptable for packing a position into the header's form and field (layouts B and C)? It is the difference between a ring of real wires and a ring the collector must be taught.
3. A head node with no real port (arity 0, or ports `prev`/`next` only): acceptable in the rule table and the audit?
4. A third outcome in the rule table, "wait", for every pair with a positive cursor, instead of stuck meaning both error and wait?
5. A dead operator meeting a negative cursor erases it, like an eraser; every other negative principal is a need. Agreed?
6. A dead cursor kept findable until its position is joined (a static at its port), rather than unlinked at the next search?
7. Stale cursors at ports the source has since killed (a `FnD`'s variable, a fan's dead side) retain the copy's argument or a duplicate while the ring lives. Tolerate, or reconcile opportunistically during a serve's ring scan, reading the source node's kind?
8. The zero-node serve, cursor to cursor, as the explicit base case of the materializer?
