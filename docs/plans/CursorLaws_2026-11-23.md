# The cursors' laws after the index's merge

`cursor-laws` steps: what the holistic review of the index's merge found,
ordered as the maintainer's answers direct
(`docs/reviews/IndexHolistic_2026-11-23.md`, its second reviewer's
`IndexHolisticFable_2026-11-23.md`). Drafted at the maintainer's request,
a rough plan (2026-11-23: "Ordering is up to you. Prepare a rough plan.
Partition, merge, reorder tasks where it makes sense."). Work proceeds in
this order unless the maintainer reorders it.

The rulings it follows:
- `generated-outputs-checked-in`: proofs a program writes are committed
  with the program, marked generated, checked reproduced.
- `laws-over-tests`: what matters, or is easy to state, is a law.
- `implementation-errors-stop`: glam's own errors stop the run.

And the maintainer's answer on duplicates: "Let's investigate making it a
law first. We can back off if it's impractical."

## Order, and why

1. `cursor-laws.sources` first. Every later step changes laws through
   the proofs' generators, which live in one container today; once they
   are in git, each later change is reproducible and checked.
2. `cursor-laws.stop` next: small, a ruling to carry out, and
   independent of the laws. The merged code's measurement is folded in,
   since it measures what it changes.
3. `cursor-laws.dup`: the decision's own law, of the index alone.
4. `cursor-laws.materializer`: the materializer under laws, with the
   root's laws composed of laws (`crossings_look`, carried here from the
   premises review) and the template freeze builds when nothing has
   finished.
5. `cursor-laws.noself`, at `.materializer`'s end: the kernel's law
   that no port of a net faces itself, so that the frontier's check
   becomes a law (the maintainer, 2026-11-24: "Introducing a kernel law
   that no port faces itself is a good idea IMO. We can add it as
   planned at an appropriate step boundary.").
6. `cursor-laws.loop`: the invariant established, reshaped once, and
   the wires stated. It restates every law, so it comes after the steps
   that add laws, which it then simplifies. It is split in three so that
   the base case comes first.
7. `cursor-laws.index`: the index's laws by disposition, last, as
   nothing waits on it.
8. `cursor-laws.watch`, throughout.

Merged: `crossings_look` into `.materializer`; F3 into `.materializer`;
the measurement (H4) into `.stop`. The premises review's P5 to P11
(`cells-freeze.sharing.cursors.index.ring.premises.later`) are spread
over `.dup` (P8, P9) and `.loop` (P5, P6, P7, P10, P11).

## Steps

- `cursor-laws` — planned — the steps below.
  - `cursor-laws.sources` — built 2026-11-23 — the proofs' generators
    in git (F1, H1), `glam/proofgen/` (its README).
    - `cursor-laws.sources.commit` — built 2026-11-23 — 26 Python
      stages moved from `results/index_bits/` with `regen.sh`, now
      `glam/proofgen/regen.sh`, its paths made the repository's own by
      one uniform substitution (every `exec` marker still found in its
      target). Also moved: the hand-kept inputs `PROOF.bend.in` and
      `SERVE_PROOF.bend.in` (named so that the gate's Bend sweep skips
      them), `align/ALIGN.bend` (checked as itself) with `bisect.py`,
      `sv/ctxp.txt`, `wsel.txt`. The reachability cut was extracted
      from `retire.py`, whose other parts delete laws. Not kept, being
      no stage of the run: `gen_serve.py` (which first wrote the serve
      file's hand-kept part), `gen_ldo.py`, `gen_sfree.py`,
      `split_heap.py`, the retirement's aids, backups.
    - `cursor-laws.sources.reproduce` — built 2026-11-23 — every stage
      runs in a scratch copy of `glam/` under `results/proofgen_run/`,
      the generated files alone copied back, and a stage that would
      change a hand-kept file fails the run. The run reproduces
      `glam/PROOF.bend` byte for byte. `glam/SERVE_PROOF.bend` comes
      out but for one blank line, an artifact of a splice by hand, now
      the generator's. `glam/JOIN_PROOF.bend` turned out generated too
      (`gen_link.py`, `gen_link2.py`, then `gen_lvlink.py`'s section
      appended) and is reproduced. Each generated file's header says
      how it is made. Kept by hand: `glam/INDEX_PROOF.bend`, whose
      header now says aids once wrote half of it;
      `glam/SPLICE_PROOF.bend`, whose `splice_free` section an aid
      wrote once (`gen_sfree.py`); `spike/HEAP_PROOF.bend`, moved there
      by a one-off script (`split_heap.py`).
    - `cursor-laws.sources.check` — built 2026-11-23 —
      `scripts/check_generated.sh` runs `glam/proofgen/regen.sh
      --check`, a generator kind `check`; the run takes about 2 s, so
      no kept pass is needed.
  - `cursor-laws.stop` — built 2026-11-23 — implementation errors stop
    the run (`implementation-errors-stop`; H7).
    - A serve's completed ends read both nets' error counts
      (`frame.ok`, `frame.ok1` in `glam/core.bend`, as `cell.done`
      reads the host's), and a count above 0 stops the run with "the
      kernel reported errors serving a copy" before the core reads
      either net again. The continuation is built only in the clean
      arm. `glam/test_serve_end.bend`, in the ladder's tests, checks
      the host's count and the source's on the serve's path; the one
      net's path has no test, wanting a frame's context.
    - `cursor`'s writes left in their order: once the run stops at the
      serve's end, nothing reads the placeholder a refused insert
      leaves, and moving the header after the insert would move
      `insert_tree`'s premise to every caller.
    - Measured: 52 instructions a serve, +0.05% on `seq` and `deep` at
      every size from 100 to 1,600 (store run 341 against run 340, the
      merged code's, now cited in `cursors-indexed`).
  - `cursor-laws.dup` — built 2026-11-23 — one cursor a position as a
    law (F2, H3; P9, P8), investigated first, backed off if impractical.
    `insert_dup` merged (9f00bcd, approved); `cxs_start` on the side
    branch `cursor-laws-cxs`, for approval at its merge.
    - `insert_dup`, built 2026-11-23: an insert meeting its own key
      equals the heap with one error counted
      (`X.ix.insert(H, s, x) == P.err_if(True{}, H)`), on the find's
      premises, x's word 2 the key and the key found. The proof is
      `insert_tree`'s reads down to the descent (`dsn`), then `near_eq`,
      the dual of `near_ne`: the leaf reached holds the key. Three
      mutants refute it on a two-leaf witness (`WB.ix_pair_pl(7)`):
      `dup_uncounted`, `dup_key_unread` and the existing
      `descent_wrong_side`. Most single-site mutants of the path are
      equivalent, the scan's refusal (`ix.put.c`) following only equal
      keys, as the law's comment says. With `.stop`, the run then
      stops. `glam/INDEX_PROOF.bend` now imports `glam/witness.bend`,
      as the other proof files do, for its witnesses. Not stated yet: the
      serve-level corollary, `R.cursor` at a position the index holds,
      one application where `cursor_pend`'s proof has `hr` and `hk`.
    - `cxs_start`, built 2026-11-23: the crossings' positions distinct
      (`RG.srcs`), none a key of the index (`RG.lacks.all`, read off the
      tree: no leaf holds it), and a node of the free list for each
      (`RG.enough`) give `RG.cxs.ok` at every step. It joins P8's two,
      `cxs_ab` and `cxs_room`, into one law over the model. Absence
      read off the tree needs no invariant: an absent key looks up to
      nothing, and stays absent through a removal and through an
      insert at another key. Two mutants of the model refute it on one
      witness: an insert taking the whole free list, and the new leaf
      at the wrong key.
    - Whether freeze's crossings meet it splits in two. Within one
      template, the positions distinct is freeze's own fact: its
      premise `SV.copy.ok` keeps the holes in distinct slots, and their
      positions are distinct ports. That is a law of freeze, carried to
      `.materializer` with the template it builds. Absent from the
      index at a serve's start depends on every serve before. It is the
      invariant across serves, carried to `.loop`: the index's keys the
      positions of copied trees' boundaries not yet joined, so that no
      serve meets its own.
  - `cursor-laws.materializer` — active — the materializer's
    composition under laws (`laws-over-tests`; F6, H2, F3). M to L.
    - `cursor-laws.materializer.compose` — built 2026-11-24 — on the
      side branch `cursor-laws-serve`. The copy, its crossings and the
      root's leave moved unchanged into `glam/serve.bend` (`SC.serve`),
      both callers repointed (the ladder's bytes unchanged, the cursor
      families within 12 instructions of run 341). `serve_pend`,
      `serve_keeps`, `serve_ring_exact` and `serve_root_keeps` are
      stated over `SC.serve`; the first two gain binders for the root
      and the served cursor, unread away from the root. Their proofs
      rewrite it once to the form they had, by two unfold lemmas
      generic in the splice's result (`serve_false`, `serve_true`,
      in `SERVE_PROOF.bend.in`). Mutants of the composition, each tried
      on a witness first:
      - `root_never_left` refutes `serve_ring_exact`;
      - `root_always_left` refutes `serve_pend`, on a witness whose
        index holds the served cursor.

      The root port one past refutes no law. The invariant does not
      say which port a leave links, and the wrong port's link word lies
      in a copy node the frames allow: evidence for
      `cursor-laws.loop.wires`. Leaving before the crossings only fails
      to typecheck (the map is read once) and is not kept.
    - `cursor-laws.materializer.look` — built 2026-11-24 — on the side
      branch `cursor-laws-look`. `crossings_look`: the served cursor,
      found at its key before a copy's crossings with no crossing's far
      end there, is found there after, in the index the crossings'
      model leaves. On `crossings_pend`'s premises; proved by `cxl.m`,
      until now an internal of the root's proofs. A mutant of the
      model's insert refutes it: the insert drops the leaf it goes
      beside. The root's laws now call `crossings_look` and
      `crossings_pend` as laws, in place of their internals (`cxl.m`,
      `crf.go`). Still internal to them: the copy's own steps
      (`cpi.core`) and the root port's link words off the tracked nodes
      (`rpom`, `rpop`). A law of the copy giving the latter, beside
      `copy_pend`, would leave the root's laws `serve_pend`,
      `crossings_look` and `leave_pend` alone.
    - `cursor-laws.materializer.rootport` — built 2026-11-24 — on the
      side branch `cursor-laws-frontier`: `copy_root_off`, the copy's
      root port read as `rt.e` reads it, its link word off the tracked
      nodes' words and the head, a law of the copy beside `copy_pend`,
      refuted by `serve_map_unwritten`. `serve_ring_exact`'s proof now
      composes laws alone: `copy_pend`, `copy_root_off`,
      `crossings_pend`, `crossings_look` and `leave_pend`, with three
      generic lemmas between them (the crossings return the map they
      are given, `cr_map`; a heap's words read two ways, `rw_kw`; the
      heap's eta). `serve_root_keeps` takes its port from the new law
      too; its frame's region facts stay internal to it. As written:
      a law of the copy
      beside `copy_pend`: the copy's root port, read through the map the
      copy leaves, has its link word off every tracked node's words and
      off the free list's head (`RG.po.all` over `M` and the holes),
      where `SV.root.ok` holds. With it, the root's laws are proved from
      `serve_pend`, `crossings_look` and `leave_pend` alone, the copy's
      steps (`cpi.core`) and the port's lemmas (`rpom`, `rpop`) no
      longer internal to them. To try; S to M.
    - `cursor-laws.materializer.template` — planned — freeze's
      obligations to the serve's laws, as laws of freeze: a
      materialization's template meets `SM.tpl.ok`, `SV.copy.ok` and
      `SV.root.ok`, its crossings at distinct positions (from `.dup`).
      F3 was read out 2026-11-24, and needs no widening. The template
      freeze builds when nothing has finished is never served by the
      copy: the materializer freezes a tree only at a node positioned
      demand found finished (`PdValue`) or a climb reached
      (`glam/materialize.bend`, `materialize`'s two calls), so that a
      materialization's template holds its root at least. Only
      `freeze_finished` builds the empty one, and only tests call it.
      The laws' "Not claimed: that freeze builds such templates" stays
      true; these laws would claim it.
      Partitioned 2026-11-24, after reading freeze's two phases: a walk
      (`fz.reach`, its map an open-addressed table, `hm.*`) collects
      the nodes reached; a write phase (`fz.emits`, `fz.tpl`) gives the
      finished nodes indices below `n`, each placeholder and eraser the
      next index from `n` up, each crossing a link from its
      placeholder's port 0 to the finished node's port, and the root a
      finished node's port. So most obligations hold by construction,
      on two facts from outside the write phase: the walk's nodes
      distinct, and the map's depth leaving the indices in distinct
      slots.
      - `cursor-laws.materializer.template.depth` — built 2026-11-24 —
        on the side branch `cursor-laws-depth`. `map_depth`
        (`glam/SPLICE_LAWS.bend`): the depth below 32, the size at most
        `2^depth` for a size up to `2^31`, and the map
        `[0 : U32^depth]` full at it (lawful-arrays' `new_full`: the
        literal is `Array.new`). No closed big constant is ever
        compared. The size premise is a `U32` literal compare, the
        search's last power doubled on words (`dbl`, computed). The
        fit's invariant is an upper bound, `to_nat(pw) <= 2^d`, so that
        doubling needs no overflow argument (a remainder is at most
        its argument). `2^32` appears only as the same subterm on
        both sides. Not claimed: that the depth is the least, so a
        mutant losing only minimality survives. One mutant refutes it:
        the search starting a power too high. Shared with `.fresh`, for
        which it gives the map's fullness and depth. The size at most
        `2^31` becomes freeze's obligation, under `.compose`.
      - `cursor-laws.materializer.template.emit` — planned — laws of the
        write phase, on a list of distinct node bases: the holes at
        distinct indices from `n`, each named by its one link at its
        port 0 from a finished node; the root a finished node's port
        below 3; the crossings' positions distinct (distinct node and
        port pairs). Stated over indices, then over slots at the depth
        `.depth` gives. M.
      - `cursor-laws.materializer.template.walk` — planned — re-scoped
        2026-11-24 on reading `fz.mark`: the finished part's walk
        (`all` false) never consults the table. It marks each node it
        meets, met once from the port its principal faces
        (`glam/freeze.bend`, `fz.mark.set`), and its table is filled
        after (`hm.fill`). So the list's distinctness is a property of
        the source's net, a finished part reached as a tree through
        two-way links, and joins `cursor-laws.noself`'s family. The
        walk's own law follows it. The table law the write phase needs
        is a lookup after `hm.fill`: each listed base found at its
        index plus one, every other at 0. M, with the net's law L.
      - `cursor-laws.materializer.template.compose` — planned —
        `SM.tpl.ok`, `SV.copy.ok`, `SV.root.ok` and distinct positions
        for `freeze_tree`'s output, the three composed; the serve's
        laws' "Not claimed" then narrowed. Its premises include the
        template's size at most `2^31` (`map_depth`'s), from the source's
        capacity. M.
    - `cursor-laws.materializer.frontier` — dropped 2026-11-24 — read
      out: the frontier's `q` is the source port facing the served
      position (`pd.peer`, the source's word `pos + 1`). The index finds
      the served cursor at `q` only where `q == pos`, the source's port
      at the position facing itself. So the check guards a property of
      the source's net, not of the index or the materializer, and a law
      replacing it is a law of the kernel's nets: no port faces itself,
      kept by every rewrite. The kernel's rules have their half
      (`rules_no_self_links`, `spike/LAWS.bend`: no rule links two ports
      of one of its new nodes); the net's, over a heap through every
      rewrite, is not stated. Until it is, the check stays: one compare a serve
      (`corruption-reported-when-cheap`; its report now stops the run,
      `implementation-errors-stop`). The kernel's law is tentative,
      beyond this plan when read out, planned since
      (`cursor-laws.noself`). The frontier's `join` and the eraser's `leave` are call
      sites of laws already (`join_pend`, `leave_era_pend`), their
      premises the materializer's to meet.
    - `cursor-laws.materializer.fresh` — tentative — the fresh map
      (`mz.fz.t` makes `[0 : U32^T.depth_for(31n, size, 0n)]` and passes
      `k` as the offset) under the laws, which wants a law of
      `T.depth_for`: the map full at a depth below 32.
  - `cursor-laws.noself` — planned — a kernel law: no port of a net
    faces itself, kept by every rewrite (the maintainer, 2026-11-24).
    The rules' half is stated (`rules_no_self_links`, `spike/LAWS.bend`:
    no rule links two ports of one of its new nodes); the net's half is
    over a heap, through the kernel's rewrites and the materializer's
    writes. With it and the index's distinct keys, a law that the
    frontier's join never meets the served cursor replaces `sv.front.c`'s
    check (`.materializer.frontier`'s reading;
    `cells-freeze.nested.host.join.self`). Taken at `.materializer`'s
    end, before `.loop` reshapes the invariant. Size unknown until the
    kernel's rewrites are surveyed for it. Scoped with its family: the
    net's links two-way and none itself, so that a finished part is
    reached as a tree, each node once (`.template.walk`).
  - `cursor-laws.loop` — planned — the invariant established and kept
    across serves (F7, H5).
    - `cursor-laws.loop.base` — planned — the first use made through
      `R.cursor` on an empty index (H8). `situate_pend` (P6): a fresh
      situating node is an empty index, and `cursor_pend` the base case.
      S to M, measured on the sharing families.
    - `cursor-laws.loop.shape` — planned — one change of the
      invariant, every law restated once. L. With it, the index's keys
      across serves: those of copied trees' boundaries not yet joined,
      so that a serve's crossings start absent (`cxs_start`'s premise,
      from `.dup`).
      - The live nodes distinct (P5).
      - Layout, bases and past folded in (P10): four premises off
        every law.
      - `px_sub` and `px_grow` (P11): one serve's conclusion the next
        one's premise, across the heap's growth.
    - `cursor-laws.loop.wires` — planned — `join_links`,
      `leave_links` (P7): the wire a join or a leave makes. M.
  - `cursor-laws.index` — planned — the index's 41 laws by
    disposition, as `.retire`'s were (H6, H9, H12). M.
    - Each law gets the downstream proof that uses it, or the reason it
      stands alone.
    - Left from H4: the six- and eight-head families measured again (their
      workload's source is to be found), and a check that `ds.run`'s second
      caller costs no segment in glam's build (`spike/tools/sharing.py`
      emits the kernel alone, so it would need extending).
    - `at_first` and `RG.first` retired with approval.
    - A mutant, or a stated reason, for each law no mutant names.
    - The redundant error arm of the insert commented.
    - Branches, which no port reaches, stated in `cursors-indexed`'s
      consequences for future sweeps.
  - `cursor-laws.watch` — planned — throughout: the gate's sections and
    the proofs' check times recorded at each step's commit. A step that
    slows iteration much is followed by one that speeds it (the
    maintainer, 2026-11-23: "watch the growth and occasionally take
    action to improve iteration speed").

## Open

- Where the generators live in the tree, and whether `regen.sh`'s
  snapshot stays one file or becomes the hand-kept part of
  `glam/PROOF.bend` (`.sources.commit`).
- How much `.loop.shape` shrinks the proofs, and whether
  `.materializer`'s module should wait for it.
