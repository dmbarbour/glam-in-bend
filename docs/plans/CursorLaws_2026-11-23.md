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
6. `cursor-laws.proofs`, after `.noself`: the proofs reviewed and
   refactored, shared lemmas first (the maintainer, 2026-11-24: "Add a
   step to review and refactor proofs, e.g. shared lemmas"). By then
   the materializer's proofs have added their share of duplicates, and
   `.loop`, which restates every law, starts from the shared lemmas.
7. `cursor-laws.loop`: the invariant established, reshaped once, and
   the wires stated. It restates every law, so it comes after the steps
   that add laws, which it then simplifies. It is split in three so that
   the base case comes first.
8. `cursor-laws.index`: the index's laws by disposition, last, as
   nothing waits on it.
9. `cursor-laws.watch`, throughout.

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
        - `cursor-laws.materializer.template.depth.upper` — built
          2026-11-24 — on the side branch `cursor-laws-upper`,
          `depth_upper` (`glam/SPLICE_LAWS.bend`). The search's power is
          carried as `U32.shln(1, d)`, a word's doubling being its shift
          (`mul2_shl`, 2^32 abstracted, the motive in the law's syntax).
          With `map_depth`, the depth is the least that fits. A mutant
          going one depth past the first fit is refuted. As planned: the
          depth at most `k` for a size at most `2^k` (`k` below 32):
          the search stops at its first fit. `map_depth` disclaims
          minimality, and `emits_far` and `put_keeps` want the hash
          map's depth, `1 + depth_for(n << 1)`, below 32, which this
          gives for `n` at most `2^29`. `.compose` uses it. S.
      - `cursor-laws.materializer.template.emit` — built 2026-11-24 — laws of
        the write phase. Re-sliced 2026-11-24 after a test of the form
        its proofs take. A record holding the heap and the map is named
        once in a proof's terms, so lemmas chained as implications over
        it fail. Each step is instead an equation over mirrors: the
        heap's words, its value table and the map as `Data` trees, the
        code's result rewritten into a pure model of the six data fields
        (`fz.peer`'s closed, two ports chained). The laws are stated
        over any heap, mirrored inside their defs (`find_tree.m`'s
        house style). The bridge stays lemmas.
        - `cursor-laws.materializer.template.emit.shape` — built
          2026-11-24 — the node's read and `P.peek` matched `U32`
          literals, stuck in a proof's default arm (`docs/Proving.md`,
          "Test values; do not match literals"). The node is read by its
          kind, `N.kof` computed once for the read and the ports, and
          `peek` tests its form. Old and new agree by computation on
          every code and form. No regression:
          - Serves cost 0.16% fewer instructions in the default build
            (`scripts/cursors.py`, 100 to 400, run 343).
          - The kernel's workloads are unchanged in the four builds, a
            constant +250 to +290 instructions against main measured
            from the same path lengths (run 345 against 344).
          - The segments are unchanged.
        - `cursor-laws.materializer.template.emit.counts` — built
          2026-11-24 — on the side branch `cursor-laws-emit`.
          `emits_counts` (`glam/FREEZE_LAWS.bend`): writing the nodes
          reached keeps the template's next index just past the nodes
          for statics and cursors, and each crossing at one of the
          cursors' placeholders, in their order
          (`glam/freeze_model.bend`'s `inv`). Any heap, the map full at
          its depth. The bridge runs end to end: the probe, `fz.peer`,
          the node's read, an error's write carried by lawful-arrays'
          `set_tree_eq`, the emit, the emits. The mirrors are made at
          the law's def. Three mutants are refuted by witness:
          - the crossing made at the next index;
          - a placeholder written as an eraser;
          - a static uncounted.

          The start's premise (`n == n` on words) is the consumer's,
          `.compose`'s. Not given yet, each assigned:
          - the placeholders' indices distinct, which wants their count
            past `n` below `2^32` (`.compose`, with `map_depth`'s size
            premise);
          - the template `fz.tpl` makes of the record (`nodes` and the
            reversed `eras`, with `nodes` `n` long), which the serve reads
            (`.compose`);
          - the map `hm.fill(seen, hm.new(n), n)` full (`.walk`, with
            the table's lookup law).
        - `cursor-laws.materializer.template.emit.links` — built
          2026-11-24 — the links, split so that what needs nothing of
          the map's values comes first.
          - `cursor-laws.materializer.template.emit.links.ends` — built
            2026-11-24 — on the side branch `cursor-laws-links`,
            `emits_links` (`glam/FREEZE_LAWS.bend`), four mutants
            refuted by a witness of two nodes whose map `hm.fill` makes.
            Every link's near end a node read back (below `n`), its
            ports below 3, and every eraser's and placeholder's index
            linked at its port 0 from a node read back (a member of the
            eras' indices: membership, so no wrap premise). A far port
            `q & 3` is below 3 off a static, by lawful-words'
            `to_nat_and_mask`. The node's index counts down on words,
            the last node split off. The counts carried as a premise.
          - `cursor-laws.materializer.template.emit.links.far` — built
            2026-11-24 — on the side branch `cursor-laws-links`,
            `emits_far` (`glam/FREEZE_LAWS.bend`): every link's far end
            a node read back (below `n`), or port 0 of an index of eras.
            Its premise on the map is `FM.vals.le` over its view, the
            map full at a depth `1 + e` below 32. The parity came
            cheaply. `(i << 1) + 1` exposes its low bit after one match
            on the word, so it is odd whatever its tail, and a slot keeps
            parity (`nat_mod_mod_pow`). No code reshape was needed. Both
            consumers were prototyped: the read (`mv_le`) and the put
            side, kept as `put_keeps` (`.walk.vals`). The depth below 32
            wants the template's read part at most `2^29` (the hash map
            is `1 + depth_for(n << 1)` deep),
            `.compose`'s premise, discharged through
            `.depth.upper`. Four mutants refuted:
            - the far end at the map's value, not one less;
            - an unmapped peer taken for a node read back;
            - a static linked at the next index;
            - the lookup reading the key as the value.
        - `cursor-laws.materializer.template.emit.ladder` — built
          2026-11-24 — the step ladder written once, a template (`em_T`,
          `glam/FREEZE_PROOF.bend`) over the invariant, a per-node
          context and five leaves (era, root, hole, link, node). The
          counts, links and far ends are its instances, their own
          ladders deleted, the laws and their mutants unchanged. The
          verdict takes 35.0 s against 35.4 s before; the file is 48
          lines longer, as the leaves take what the copies took. A new
          invariant now costs five leaves and its list.
        - `cursor-laws.materializer.template.emit.kinds` — built
          2026-11-24 — the template's nodes' kinds and the root, split
          as the links were.
          - `cursor-laws.materializer.template.emit.kinds.root` — built
            2026-11-24 — on the side branch `cursor-laws-kinds`,
            `emits_root` (`glam/FREEZE_LAWS.bend`), the template's
            instance in five leaves and its list. Three mutants refuted:
            the root at the next index, and a static's eraser or a
            placeholder written as a function node. No heap premise. The root's index is below `n` at a port
            below 3, and each element of eras is an eraser exactly when
            it is no placeholder (what `SM.made` counts). The counts' and
            links' countdown is reused, and the start's root is a
            premise. Not claimed: that `nodes` is `n` long in index
            order, and that the root is no placeholder's index (both
            `.compose`'s); that the root faces the interface.
          - `cursor-laws.materializer.template.emit.kinds.nodes` —
            built 2026-11-24 — on the side branch `cursor-laws-kinds`,
            `emits_nodes` (`glam/FREEZE_LAWS.bend`), well inside its time
            box. The read node is an eraser exactly when its kind is
            (`nd_era`, over the 19 kinds). Three mutants refuted:
            - a function node read as an eraser;
            - the header read from a port's word;
            - the kernel's error count written at a header, not word 1
              (the frame's own mutant, its witness a free table entry).

            Its frame is kept on the current tree: the list's invariant
            is the words full at `d` and each base left a non-eraser kind
            in the current view, which an error's write keeps. It needs
            each base aligned with `2 <= d`, not nonzero (nonzero only
            for a law on port words). Relating the walk's test of the
            code (`fz.is_era`) to the kind goes through `N.kof`'s
            literals. Probed on one path (code 7, the tail any): the low
            six bits matched and the tail zeroed by a lemma, `N.kof`
            reduces and so does `fz.is_era`. So the 64 paths of `rk`'s
            six bits are a case tree for an authoring aid (`.walk`'s).
            The walk's marks (`fz.copied`) set bit 6 on controls only,
            outside `rk`'s bits, and the write phase reads a control's
            field and offset, not its form.
        - `cursor-laws.materializer.template.emit.length` — built
          2026-11-24 — on the side branch `cursor-laws-length`,
          `emits_len` (`glam/FREEZE_LAWS.bend`): the length after is the
          list's plus the length before, the template given a type
          parameter for its invariant's argument (`~X`, `Nat` here, `U32`
          for the others) and entered at `emt_T`. Two mutants refuted: a
          node read but not kept, a base never written. Which node each
          index holds is not claimed: each is no eraser (`emits_nodes`),
          which is all the kinds want. The step as planned: `nodes` is
          `n` long, in index order: the length after the
          write phase is the list's plus the length before. Only the
          ladder shows it, and every kind conclusion at an index below
          `n` rests on it. The count changes at the node's step, so it
          enters the template at `emt_T`, the count as the invariant's
          second argument. Taken before `.positions`.
        - `cursor-laws.materializer.template.emit.positions` — built
          2026-11-24 — on the side branch `cursor-laws-length`,
          `emits_pos` (`glam/FREEZE_LAWS.bend`): the crossings' positions
          stay distinct (`RG.srcs`), what `cxs_start` asks. Its premise
          is the listed nodes' port positions distinct as one list
          (`FM.ports`: `b + 0`, `b + 1`, `b + 2` per base), so its proof
          has no word arithmetic, and `b + p` stays out of its text. That
          is the encoding's nearest point: the references review puts a
          port's reference at `b + p + 1` under statics at `00`.
          - The template's argument moves from port to port (`~nx`). No
            invariant at one fixed argument can tell two ports' pushes
            apart.
          - A port below 3 is split by an eliminator over `port3`
            (`p3e`).

          Two mutants refuted: a crossing at its node's base, and
          positions from the nodes' indices colliding across two nodes.
          Owners of the rest:
          - from distinct aligned bases to distinct port positions, a
            lemma on words: `.walk`;
          - distinctness after `fz.tpl`'s reversal: `.compose`;
          - `RG.lacks.all`, `RG.enough` (`cxs_start`'s) and `RG.far.off`
            (`crossings_look`'s, the served cursor's key): the serve's.

          The step as planned: the
          crossings' positions distinct, over distinct aligned bases.
          Stated from its consumer: which crossings or serve law reads
          `FzC`'s `src` and `far`, and what it needs. `src` is `b + p` on
          words, so distinctness wants room against wrapping as well as
          distinct aligned bases.
        The slices need of the walk's list: its length `n` (the index
        counted down on words from `n - 1`), each base's kind (as
        `N.kof` gives it; relating the walk's tests of the code,
        `fz.is_era`, to kinds is a literal match again, `.walk`'s to
        do), the map's values, and distinct bases, each a multiple of 4
        (nonzero only for a law on port words). Decided 2026-11-24: the walk's premises are about
        the heap before the write phase, while reads after an error's
        count (a free table entry, word 1 written) come from the updated
        tree. A frame lemma at word 1 carries them: the write phase reads
        `b`, `b+1+p`, `b+2`, `b+3` and `base(q)`. A header read at `b`
        is never word 1 when `b` is a multiple of 4 (`emits_nodes`); a
        port word at `b+1+p` is word 1 only at base 0, the heap's header,
        never a net node (`cursor-laws.noself`'s family), which a law on
        port words would need. Not claimed: that the root is the port facing the
        interface (it starts as `T.TE{0, 0}`, which the root's check
        accepts once `n >= 1`). Stated over indices, then over slots at
        the depth `.depth` gives. M to L.
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
        index plus one, every other at 0, and the map full at its depth
        (`emits_counts`' premise) with its values at most `n`
        (`emits_far`'s `FM.vals.le`). It also owes the write phase's
        premises on the list (`.emit`'s): its length, each base's kind,
        each base a multiple of 4 (nonzero only for a law on port
        words). The `all` path (`freeze`, a
        whole finished net) is outside `.compose`'s scope, as the
        materializer serves through `freeze_tree` with `all` false; its
        map, the walk's own, would owe the same. M, with the net's law
        L.
        - `cursor-laws.materializer.template.walk.vals` — built
          2026-11-24 — on the side branch `cursor-laws-links`,
          `put_keeps` (`glam/FREEZE_LAWS.bend`): each `hm.put` keeps the
          map full at its depth and its values at most `n`, the key at
          the probe's slot's even word, the value at its odd one. With
          `hm.new`'s map computing so, `hm.fill`'s map satisfies
          `emits_far`'s premise by an induction over the list. A mutant
          swapping the two words is refuted.
      - `cursor-laws.materializer.template.compose` — planned —
        `SM.tpl.ok`, `SV.copy.ok`, `SV.root.ok` and distinct positions
        for `freeze_tree`'s output, the three composed; the serve's
        laws' "Not claimed" then narrowed. Its premises include the
        template's size at most `2^31` (`map_depth`'s), from the source's
        capacity. It owes what `emits_counts` leaves: the placeholders'
        indices distinct (no wrap past `n`), and the template `fz.tpl`
        makes of the record, `nodes` `n` long. `emits_far`'s map depth
        below 32 wants the read part at most `2^29`. Both size premises
        come from the heap's capacity: node words up to `2^30`, so at
        most `2^28` nodes (`net-capacity`, `spike/kprim.bend`'s
        `w_maxd`), under `2^29` and `map_depth`'s `2^31` (the
        maintainer, 2026-11-24). M.
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
    Surveyed 2026-11-24. Link words are written at about 58 sites in
    the generated rewrites (`spike/krules.bend`), 7 in `knet.bend`, 5 in
    `kprim.bend`'s `link` family, and 9 in glam's ring, index and splice.
    A rewrite that wires two peers through (`link_xx`) is free of a
    self-link only if the peers' links are two-way, so the family is one
    invariant. Sliced:
    - `cursor-laws.noself.model` — built 2026-11-24 — on the side
      branch `cursor-laws-noself`, `wired_port`
      (`spike/WIRED_LAWS.bend`): a net the audit passes has each live
      node's port below its kind's arity pass the audit's check of one
      port (`WR.port.ok`, `spike/wired_model.bend`): a static eraser, or
      a live port, not itself, that links it back. The audit only reads,
      so it bridges to a model over the words' tree as freeze's write
      phase did, its verdict accumulated left to right as the code does.
      The walk to node `j` and port `p` counts on words (`(a + 1 : U32)`
      is `U32.inc`, 2^32 abstracted). Three mutants of the audit, each
      dropping one check (not itself, links back, below the arity), are
      caught by the proof failing on them: no witness can pass the
      original audit and fail a port. As planned: the wiring as a premise
      (`wiring-premise-before-refinement`): `KN.wired_ok`'s verdict on the
      source heap, the audit the library runs, no second definition.
      With it, lemmas that extract per port: a live node's port below its
      arity links a live port, not itself, which links it back.
    - `cursor-laws.noself.link` — dropped 2026-11-24 — to
      `kernel-refine.rewrite` (`wiring-premise-before-refinement`).
    - `cursor-laws.noself.rules` — dropped 2026-11-24 — to
      `kernel-refine.rewrite`.
    - `cursor-laws.noself.copy` — dropped 2026-11-24 — to
      `kernel-refine.copy`.
    - `cursor-laws.noself.frontier` — planned — the frontier's law under
      the premise: the served position's port faces no port that is
      itself, so the cursor found there is never the served one. The
      check stays until `kernel-refine.discharge`. Its parts:
      - `PdFront`'s `q` is the served position's link word in its own
        heap, the reads handing the heap back;
      - `wired_port` on that heap, the position being a live node's
        port below its arity;
      - the index's cursor found at `q` keyed `q`, so that `nc`, keyed
        at the position, is found there only if `q` is the position (the
        index's laws);
      - the position as node `j`'s port `p` (`(j << 2) + p`, a lemma on
        words), and the served position a live node's port below its
        arity (the ring's premises on a cursor's position, `RG.px.ok`).

      The premise was measured on the materializer's heaps before it was
      built on: zero failed audits (store run 347). Sliced 2026-11-24:
      - `cursor-laws.noself.frontier.faces` — built 2026-11-24 — on the
        side branch `cursor-laws-noself-front`, `front_faces`
        (`glam/POSITION_LAWS.bend`). The loop's step walks `pd.q`'s
        branches to each end and settles it there, the induction a
        function of the next heap. `pd.ended.k` was reshaped to test the
        walk's state, equal on every state tried, the serve family
        unchanged (store run 348). Two mutants are refuted by
        `two_lifts`, whose climb reaches the interface: the climb's
        frontier read one word past, and one recorded at its node's
        base. A mutant moving `pd.peer` itself survives, and rightly:
        it moves every read of the position, so the witness never
        reaches a frontier. As planned: positioned
        demand's frontier faces the position: a `PdFront`'s port is the
        position's link word in the frontier's own heap. It needs no
        premise, as both of `PdFront`'s makers read it there (a climb
        that hits, a walk ending in state 7). `pd.ended.k` matches the
        walk's state on `U32` literals, stuck in a proof's default arm,
        so it is reshaped to test the state, measured.
      - `cursor-laws.noself.frontier.apart` — built 2026-11-24 — on
        the side branch `cursor-laws-noself-apart`, `front_apart`
        (`glam/POSITION_LAWS.bend`): `front_faces`' fact and
        `wired_port`'s check of the position's port. The port links
        either a static eraser, which a port that is no static cannot
        be, or no port of its own reference. Its mutant, the audit's
        self-check dropped, is caught by the proof failing through
        `wired_port`'s. As planned: with
        `wired_port`, the frontier's port is not the position itself.
        Its premises are on the frontier's heap: wired, and the position
        a live node's port below its arity. The second is a premise of
        its own: a finished node is untouched by the walks
        (`copied-nodes-untouched`), which the kernel's refinement owes
        too.
      - `cursor-laws.noself.frontier.cursor` — planned — the index's
        cursor found at the frontier's port is keyed there, so the
        served cursor is found there only if that port is its
        position. Then `sv.front.c`'s check never fires, under the
        premises.

    L or more. `.loop`'s reshaping waits on it only where it restates
    the invariant.

    Found 2026-11-24, reading the consumers and what exists:
    - **What the frontier needs.** `PdFront`'s `q` is the port the
      served position faces (`position.bend`'s `pd.peer`). So the check
      fires exactly when the served position's port faces itself: no
      port facing itself in the source, kept through the walks there.
    - **What the walk needs.** The finished walk enters a node only
      through the one port facing its principal. With two-way links
      only one port can face it, so its list is distinct.
    - **The model's half exists.** `spike/wiring.bend`'s `W.wired`
      (each live port referenced exactly once, so no self-link) is kept
      by every rewrite of the rule table (`rewrite_wired`,
      `rules_keep_wired_in`).
    - **The heap's half is audited, not proved.** `KN.wired_ok` checks
      two-way links and no self-link at run time, and the library runs
      it at the end of every case.
    - **The bridge is the HeapModel plan's draft refinement**
      (`kernel_rewrite_refines`, `kernel_audits_exact`, through an
      abstraction `KA`), which `heap-laws-align.statics` (tentative)
      finds cannot hold as drafted. The model places an eraser as a node
      where the kernel makes it static, and the reserve breaks `FL.ok`'s
      one list.

    So `noself`'s kernel half is that refinement, a question of scope
    for the maintainer. `interaction_net`'s construction refusing a port
    wired twice or never (the maintainer, 2026-11-24) is the base case
    at loading.
  - `cursor-laws.proofs` — planned — the proofs reviewed and
    refactored, the laws unchanged (the maintainer, 2026-11-24). Taken
    after `.noself`, before `.loop`.
    - Duplicates found by statement, not by name: a development aid
      listing the defs whose types match across the proof files. Seen so
      far:
      - `not_true` in four files;
      - `u32_refl` in three;
      - `or_l` in two;
      - a heap read handing its heap back in two (`rd_eq`, `rd_back`).

      `u32_eq`, `inv`-style `and` splits and the doubling's word lemmas
      are likely to join them.
    - Shared lemmas in files of their own, beside the code they are
      about: words and Bools, the heap's mirror (`hp`, the reads'
      hand-backs, an error's write kept a tree), the probe. Each is
      imported where it is used, so a change rechecks only its importers.
      Lemmas general enough for the hub go to
      `blend/docs/HubCandidates.md`.
    - The proofs' generators (`glam/proofgen/`) call the shared lemmas
      instead of writing their own, and are regenerated.
    - The bridge from code to model (`glam/FREEZE_PROOF.bend`) reviewed
      for reuse: the materializer's other proofs may want the same form.
      Its own duplicates so far:
      - the mirror plumbing at each law's def, five copies (`ec.m`,
        `ek.m`, `ej.m`, `er.m`, `en.m`), a template's candidate;
      - copies of `wl_ne` and `wd` (as `wdv`) from `INDEX_PROOF.bend`;
      - copies of `slot_mod4` and `ne_mod4` from
        `proofgen/align/ALIGN.bend`.
    - What it buys measured: each proof file's check time before and
      after, and the gate's (`.watch`). A refactor that slows the gate
      is reverted or justified.
    - M.
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
  - `cursor-laws.records` — planned — a cleanup review of the decision
    records (the maintainer, 2026-11-24): a record holds the why of a
    decision, not the when, ordering being the role of plans and git
    history. `wiring-premise-before-refinement` is mostly an ordering
    decision. Its why (the source's wiring as the audit's verdict, one
    owner) stays, and its route and timing move to the plans.
  - `cursor-laws.watch` — planned — throughout: the gate's sections and
    the proofs' check times recorded at each step's commit. A step that
    slows iteration much is followed by one that speeds it (the
    maintainer, 2026-11-23: "watch the growth and occasionally take
    action to improve iteration speed"). At `.emit.links` (2026-11-24):
    `glam/FREEZE_PROOF.bend` checks in 35 s cold, the gate in 81 s with
    the rest kept (run 346).

## Open

- Where the generators live in the tree, and whether `regen.sh`'s
  snapshot stays one file or becomes the hand-kept part of
  `glam/PROOF.bend` (`.sources.commit`).
- How much `.loop.shape` shrinks the proofs, and whether
  `.materializer`'s module should wait for it.
