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
  - `cursor-laws.noself` — built 2026-11-24 — its model and the
    frontier's laws, its kernel half moved to `kernel-refine`. As
    planned: a kernel law: no port of a net
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
      (`net-obvious-errors`): `KN.wired_ok`'s verdict on the
      source heap, the audit the library runs, no second definition.
      With it, lemmas that extract per port: a live node's port below its
      arity links a live port, not itself, which links it back.
    - `cursor-laws.noself.link` — dropped 2026-11-24 — to
      `kernel-refine.rewrite` (`net-obvious-errors`).
    - `cursor-laws.noself.rules` — dropped 2026-11-24 — to
      `kernel-refine.rewrite`.
    - `cursor-laws.noself.copy` — dropped 2026-11-24 — to
      `kernel-refine.copy`.
    - `cursor-laws.noself.frontier` — built 2026-11-24 — in three
      slices, below. As planned: the frontier's law under
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
      - `cursor-laws.noself.frontier.cursor` — built 2026-11-24 — on
        the side branch `cursor-laws-noself-apart`, with `.apart`:
        `found_apart` (`glam/INDEX_LAWS.bend`: the cursor a realized
        index finds at a key is no cursor whose word 2 holds another),
        and `front_joins`, `front_joins1` (`glam/MATERIALIZE_LAWS.bend`,
        new): a serve whose positioned demand ends at the frontier, the
        index finding a cursor at its port, joins it to the served one,
        on the two-heap path and the one-net path. Stated over `sv.pd`
        given the frontier's end and that it faces the position, so a
        serve going on from a walk (`serve.from`) is covered too:
        `front_faces_from` (`glam/POSITION_LAWS.bend`) supplies it there,
        as `front_faces` does on a fresh serve. `front_apart`,
        `found_apart` and `find_tree` composed as laws.
        The serve's verdict first took 190 s: `materialize.bend`'s
        closure 85 s, and the hub's `string.bend` 75 s more, imported by
        the index's proofs for one lemma, `u32_eq_of_is_eq`. That lemma
        is vendored (`vendor/bend-mathlib/`) and the index's proofs use it,
        so their verdict fell from 55 s to 21 s and the serve's to 94 s.
        The premises:
        - on the frontier's heap, the kernel's (`kernel-refine`): wired,
          and the position a live node's port below its arity, no
          static. The interface is node 7's port 0, so a serve at the
          root is covered: on `two_lifts` its header is kind 8, of
          arity 1, under a capacity of 128, and the audit passes, so the
          premises hold together there
          (`results/index_bits/apart/ROOT.bend`);
        - on the host: the index realized on its invariant, and the
          served cursor's word 2 the position, as the serve reads it.
        Owed: on the one-net path, the walks keeping the index and the
        served cursor's word 2 (the host is the source there), for
        `.loop`. Not claimed: the frontier's port holding no cursor (the
        climb). The check stays, its comment pointing at the law, until
        `kernel-refine.discharge`. Mutants: the find keyed at the
        position, and the check comparing the found cursor with itself,
        on each path; a leaf's key unread, for `found_apart`. All are
        caught by the proofs failing; no witness, as a realized index in
        a heap is costly to build. As planned: the index's
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
  - `cursor-laws.proofs` — built 2026-11-25, `.shared.model` and
    `.bridge` tentative — the proofs reviewed and
    refactored, the laws unchanged (the maintainer, 2026-11-24). Taken
    after `.noself`, before `.loop`. In slices, each measured by its
    files' verdicts alone, before and after, and by the gate's:
    - `cursor-laws.proofs.string` — built 2026-11-25 — each file's
      verdict, four at a time, about 20 s less (store run 349):
      `PROOF` 59 to 38 s, `SERVE_PROOF` 68 to 44, `JOIN_PROOF` 47 to 28,
      `SPLICE_PROOF` 43 to 25. The alias `MS` is kept, now naming the
      vendored file. As planned: the proof files off the
      hub's `string.bend`: each file's import of it pointed at the
      vendored `u32_eq_of_is_eq`, which keeps the name, so that the
      generated bodies stand unchanged. The hand-kept inputs
      (`glam/proofgen/PROOF.bend.in`, `SERVE_PROOF.bend.in`, the join's
      header in its stage), `SPLICE_PROOF.bend` and
      `proofgen/align/ALIGN.bend`, then regenerated.
    - `cursor-laws.proofs.dups` — built 2026-11-25 —
      `scripts/proof_dups.py`, run by hand: each proof file's lemmas
      read as their statements, the parameters renamed by position, the
      erasure marks dropped and each module alias replaced by its file,
      grouped where they match. The hub's laws and typed defs, and the
      repo's laws, join the groups. It finds 136 groups over 12 files,
      132 across files:
      - 32 already proved by the hub (`and_l` as bend-mathlib's
        `eq_true_of_and_left`, `sub0` as `sub_zero`, `le0` as
        lawful-arrays' `le0`), which the repo's copies can call;
      - 28 matching one of the repo's laws;
      - 76 among the repo's proofs alone: Bool's `and`, `or` and `not`
        splits (`not_true` in six files, `or_false_l` in three),
        `u32_refl` in five, the alignment lemmas `gen_align.py` copies
        from `ALIGN.bend` into `PROOF.bend` (34, by design), and the
        model's small facts (`po_at`, `lay_at`) copied between the
        serve's and the cursors' proofs.

      Classified (`--detail`: each def's body length, erasure marks,
      and whether it is one call): 46 groups save nothing, their
      members wrappers of one lemma, and 28 are a lemma proving its own
      file's law, no duplicate. What sharing would save is about 843
      lines of proof, not lemmas by count: `ALIGN.bend`'s copies in
      `PROOF.bend` the most (`pig` 85 lines), the hub's laws re-proved
      next (36 groups, their marks fitting every caller's: `le_succ`,
      `or_assoc`, `le_trans`), then the model's facts copied between
      the serve's proofs and the cursors' (`lfull`, `po_at`, `lay_at`).
      As planned: the development aid listing the defs whose types
      match across the proof files, and what it finds.
    - `cursor-laws.proofs.shared` — built 2026-11-25 — `.hub`,
      `.align` and `.basics`; `.model` tentative. Over what sharing would
      save, about 496 lines remain after them (the finder rerun), in 66
      groups of a few lines each: none buys check time, the verdicts'
      cost lying in their imports, and in the generated files each is a
      generator's edit. As planned: the duplicates moved to
      shared lemma files beside the code they are about, the
      generators calling them. Each slice one family, its files'
      verdicts against a baseline of every proof file's alone
      (`results/proofs_shared/baseline.sh`); hand-kept files before
      generated ones.
      - `cursor-laws.proofs.shared.hub` — built 2026-11-25 — nine
        lemmas: `FREEZE_PROOF`'s `nt_of`, `sub0` and `le0`,
        `WIRED_PROOF`'s `sub0` and `le_trans_b`, `INDEX_PROOF`'s
        `bool_and_false` and `or_assoc`, and `POSITION_PROOF`'s
        `ah.nt_of` replaced at their calls by bend-mathlib's and
        lawful-arrays' and lawful-words' laws; `INDEX_PROOF`'s `not_true`,
        42 callers, a wrapper of bend-mathlib's. 92 lines less. Verdicts
        alike within the noise (runs 350 and 351, one file at a time,
        the host's kernel upgraded between: the files touched 1 to 5 s
        slower, the untouched −1 to +4 s). As planned: the hand-kept
        files' re-proofs of hub laws whose file they import, the marks
        fitting: a lemma with many callers kept as a one-line wrapper
        of the hub's law, so that no call site moves, one with few
        replaced by it.
      - `cursor-laws.proofs.shared.align` — built 2026-11-25 —
        `gen_align.py` writes the import (`AL`) where it wrote 30
        copies, and the leave's three stages call `AL.port_of_po` and
        `AL.po_static`: `glam/PROOF.bend` 345 lines shorter, its
        lawful-words imports coming with `ALIGN.bend`'s. Its verdict
        alike, 30.8 s before and 31.0 and 31.4 after, its peak about
        60 MB more, `serve_model` coming too. `SERVE_PROOF` drops its
        copy of `dyn_of_bases` and calls it and `faces_fresh` as `AL`'s
        where it called `PROOF.bend`'s copies (`gen_cpi.py`), its verdict
        alike (39 s in the gate, 2.7 GB). `bases_at`, `none_nil` and
        `po_at`, which `PROOF.bend` proves itself under the same names,
        are `.model`'s. As planned: `PROOF.bend` importing `ALIGN.bend`'s
        lemmas, which `gen_align.py` copied.
      - `cursor-laws.proofs.shared.model` — tentative — taken when the
        proofs holding them are next edited (`po_at`, `none_has` in
        `PROOF.bend` and `SERVE_PROOF.bend`, `lfull` in `SERVE_PROOF`
        and `SPLICE_PROOF`, `links_at` and `pos_at` in `PROOF.bend` and
        `JOIN_PROOF`: about 70 lines). As planned: the model's facts
        the serve's proofs and the cursors' both prove, in a file
        beside the model.
      - `cursor-laws.proofs.shared.basics` — built 2026-11-25 — as a
        rule and a table rather than a file: `docs/Proving.md` lists the
        31 hub laws the proofs had restated, with their statements, and
        asks that a new lemma be checked by the finder first. The
        copies already written stay until their files are next edited. As
        planned: the Bool, Nat and
        U32 facts no hub file holds, in small files by topic; the
        generated files' through their generators. An import a file
        lacks is timed alone first.
    - `cursor-laws.proofs.imports` — built 2026-11-25, `.rules`
      tentative — what the proofs import
      from the spike cut to what they use, for the verdicts' time and
      memory (the maintainer, 2026-11-25: the spike laws' refactoring on
      the docket, read here as the proofs' imports of the kernel). A
      verdict translates every definition its imports hold to BendTT,
      used or not: the kernel's import alone took 82 s and 3.2 GB, its
      BendTT 51 MB, of which the kernel's command line (`main.run`, the
      strategies' every mode) 29.6 MB and the generated rule table
      (`krules`) 15.5 MB; Bend's own check of it 3.8 s.
      `POSITION_PROOF` and `MATERIALIZE_PROOF`, the gate's longest
      verdicts and largest peaks, import it.
      - `cursor-laws.proofs.imports.main` — built 2026-11-25 — the
        kernel's import 82 to 71 s and 3.2 to 2.4 GB at its peak,
        positioned demand's 81 to 74 s and 3.4 to 2.4 GB (store run
        354). The four builds' counts alike: interactions equal,
        instructions 794 to 845 more on every workload, small or large,
        a start-up constant (runs 352, 355). The BendTT more than halved
        (51 to 23 MB) while its writing went from 72 s to 68: the time
        is not the output's size. The library's runner
        (`spike/tools/library.py`) calls `run_dev`, `EDRes` and
        `profile_ev`, which stay in the kernel; a scan of the Bend
        sources alone had missed them, and the gate's library section
        caught it. As planned: the command line
        moved out of `spike/kernel.bend` into `spike/kernel_main.bend`,
        which the build tools build (`count_builds.sh`, `kmem_run.sh`);
        no importer used it. The kernel's compiled code checked
        unchanged by the four builds' counts.
      - `cursor-laws.proofs.imports.rules` — tentative — what remains
        is spread over the modules the walk needs, not one definition:
        a verdict of `krules`' import alone 18 s, `knet`'s 32,
        `kdemand`'s 59, `kstrat`'s 73, each with what it imports, while
        their BendTT is 1 to 1.5 MB a module. Where the writing spends
        its time is Bend's to show (`docs/BendIssues.md`, BendTT emission
        time); until it does, no cut here has a known payoff.
    - `cursor-laws.proofs.bridge` — tentative — taken with the next
      law over the heap, which would reuse it (`.loop`). As planned: the
      bridge from code to
      model reviewed for reuse, its mirror plumbing a template's
      candidate.

    What was found before the slicing:
    - Duplicates found by statement, not by name: a development aid
      listing the defs whose types match across the proof files. Seen so
      far:
      - `not_true` in four files;
      - `u32_refl` in three;
      - `or_l` in two;
      - a heap read handing its heap back in two (`rd_eq`, `rd_back`).

      `u32_eq`, `inv`-style `and` splits and the doubling's word lemmas
      are likely to join them.
    - The rest of the proof files off the hub's `string.bend`, whose
      import costs about 75 s of verdict for the one lemma they take
      from it (`u32_eq_of_is_eq`, vendored in `vendor/bend-mathlib/`
      for the index's proofs at `.frontier.cursor`): `glam/PROOF.bend`,
      `SERVE_PROOF`, `JOIN_PROOF`, `SPLICE_PROOF` and the generated
      `ALIGN.bend` through its generator. A home for the lemma in the
      hub's `u32.bend` is a candidate to offer upstream once glam is
      relatively stable (the maintainer, 2026-11-25).
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
  - `cursor-laws.loop` — active — the invariant established and kept
    across serves (F7, H5).
    - `cursor-laws.loop.base` — built 2026-11-25 — `.code` and
      `.situate`. As planned: the first use made through
      `R.cursor` on an empty index (H8). `situate_pend` (P6): a fresh
      situating node is an empty index, and `cursor_pend` the base case.
      S to M, measured on the sharing families.
      - `cursor-laws.loop.base.code` — built 2026-11-25 — the core's
        first use (`use.situ`, `glam/core.bend`) writes the situating
        node an empty index, its word 3 itself, and puts the leaf in it
        by `R.cursor`, as a serve's crossings are; the hand layout
        (`use.cursor`) gone. The words written are the same (the
        insert's empty case writes the root and the home), at two reads
        and a write more a use; every hello, sharing and growth sample's
        counts alike, 68 of them (`results/loop_base/`), and the ladder
        passing as before.
      - `cursor-laws.loop.base.situate` — built 2026-11-25 — on the
        side branch `cursor-laws-loop-base`, `situate_pend` in
        `glam/LOOP_LAWS.bend` (new, the loop's laws), stated over
        `R.situate`, which the core now calls for the situating node's
        allocation and writes (`glam/ring.bend`; the 68 samples' counts
        alike). Proved over the view's list form (`px_sv`), its reads at
        the written words carried back; the payload word split by the
        header's test. `lay_pair`, two tracked nodes four words apart,
        is new and general. The verdict 35 s at 2.7 GB. Two mutants,
        the index not empty and word 1 left the free list's link, caught
        by the proof failing. As designed: `situate_pend`: the
        situating node's writes, on a node fresh from the free list,
        give `RG.px.ok` over the empty index with the leaf pending, so
        that `cursor_pend` applies to the first use. Its premises on the
        leaf: live, its link two-way and none facing itself (the wiring,
        `net-obvious-errors`), off the other tracked nodes' words.
        Designed 2026-11-25, over `use.top` and `use.situ`'s writes: the
        node taken by `P.node` from a free list whose chain is
        `Con{s, F}` (`node_keeps`, `node_next`, `node_index`), its word 1
        the static eraser (`P.put_st`), word 2 the source's entry, word 3
        itself. Concluded: `RG.px.ok` over the words after, at `s`, the
        index empty, the leaf pending, the live nodes `[s, leaf]`, the
        free list `F`, the tracked `N`; and the words full. Premises: the
        words full at depth 2 or more, below 32; `Con{s, F}` the free
        list's chain and distinct; `[s, leaf]` and `F` in `N`, laid out
        apart, each its own base; the leaf none of `Con{s, F}`; its link
        word `q` (word 1) with `port.ok([s, leaf], d, q)`,
        `po.all(q, [s, leaf], d, N)` and facing neither itself nor `s`.
        The leaf's premises are on the value `q` alone, which the
        writes leave, so that a caller discharges them from the host's
        wiring. The static's conjuncts by `ALIGN.bend`'s `po_static` and
        the alignment lemmas; the realization of the empty index by
        `s`'s word 3. Not claimed: the reserve's and the doubling's
        paths, where the free list is empty (`px_grow`, `.loop.shape`).
    - `cursor-laws.loop.shape` — active — one change of the
      invariant, every law restated once. L. With it, the index's keys
      across serves: those of copied trees' boundaries not yet joined,
      so that a serve's crossings start absent (`cxs_start`'s premise,
      from `.dup`).
      - The live nodes distinct (P5).
      - Layout, bases and past folded in (P10): four premises off
        every law.
      - `px_sub` and `px_grow` (P11): one serve's conclusion the next
        one's premise, across the heap's growth.

      Designed 2026-11-25: the laws already merged stay as they are,
      and a wider invariant is laid over them, `RG.px.ok` with the facts
      no step returns (the live nodes distinct; the tracked nodes laid
      out, each its own base, past the header). Each step gets one law
      of the wider invariant, its own law composed with a "kept" lemma
      per fact added, rather than every proof restated: the facts added
      are about lists and the tracked nodes, which a step's writes do
      not touch. Slices:
      - `cursor-laws.loop.shape.distinct` — built 2026-11-25 — the live nodes
        distinct (P5): the crossings only take nodes out of the live
        list (`cx.L`, `without`), so it stays distinct
        (`cxs_distinct`, a model law); the copy appends its holes,
        fresh nodes none of which is live.
        - `cxs_distinct` built 2026-11-25 on the side branch, with
          `without_distinct` and `has_without`; its mutant, a made
          cursor listed again, caught.
        - The copy's half: its holes are among the nodes the copy takes
          from the free list (`SP.holes_sub`), and no free node is live
          (the invariant's `none.in(F, L)`), so the holes are none of
          the live list and the append stays distinct (`dist_app`,
          `ni_sym`, in `glam/LOOP_PROOF.bend`), composed in the serve's
          law (`.serve`). A detour, that every live node but `s` is a
          cursor between serves, was dropped: carrying it through the
          crossings needs the index laid out at each step, which only
          the heap-level laws keep.
      - `cursor-laws.loop.shape.track` — active — the tracked nodes
        after a serve, the copy's nodes taken from the free list added
        (`M ++ ns`): laid out, bases and past kept, from the free
        list's nodes being laid out apart (`IM.fl.ok`).
        Redesigned 2026-11-25: one tracked list for a whole run, every
        node a serve may touch among it, laid out, bases and past once;
        each serve's laws take the sub-list they name, the old nodes and
        the copy's. Built on the side branch: `px_sub` (P11's, the
        invariant over a sub-list holding the live, free and index's
        nodes; its mutant, a faced port's link word off one tracked node
        enough, caught), and the lemmas `lay_sub` (a distinct sub-list
        of a list laid out is laid out, by `lay_pair`), `bases_sub`,
        `past_sub`. Left for `.serve`: the sub-list's shape `M ++ ns`,
        the copy's nodes last.
        Found 2026-11-25, reading `serve_pend`'s conclusion: after a
        serve the tracked nodes are `M ++ pls`, the copy's holes kept and
        its other nodes, now the host's, dropped; so a run's tracked list
        shrinks with each serve and grows only where the next copy takes
        nodes past the tracked prefix of the free list. Those nodes join
        the tracked list on two conditions: laid out apart from it, and
        no faced port linking into them. The first is arithmetic,
        distinct bases past the header and in range being apart; the
        second is the host's wiring, live ports linking only live ports
        (`net-obvious-errors`' premise). Proposed: both premises of the
        serve's law for now, the kernel's to discharge
        (`kernel-refine`), as the wiring is; the arithmetic law
        (`bases_apart`) a step of its own, which would fold the layout
        into the invariant by computation (P10).
      - `cursor-laws.loop.shape.grow` — planned — `px_grow`: the wider
        invariant across the heap's doubling, the words copied.
      - `cursor-laws.loop.shape.serve` — planned — `serve_loop`: one
        serve keeps the wider invariant, its crossings starting absent
        (`cxs_start`), so that serves compose.
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
  - `cursor-laws.records` — built 2026-11-25, `.stale` planned — the
    review, retired: all
    74 records read; 35 cleaned of their when by six rules the
    maintainer approved, one (`wiring-premise-before-refinement`)
    folded into `net-obvious-errors` at the maintainer's word; the rule
    kept in `docs/Decisions.md`. As planned: a cleanup review of the
    decision
    records (the maintainer, 2026-11-24): a record holds the why of a
    decision, not the when, ordering being the role of plans and git
    history. `wiring-premise-before-refinement` is mostly an ordering
    decision. Its why (the source's wiring as the audit's verdict, one
    owner) stays, and its route and timing move to the plans.
    - `cursor-laws.records.stale` — planned — the records read again for
      content that no longer holds, apart from the when (the maintainer,
      2026-11-25). Seen in the cleanup: rings where the index replaced
      them (`self-copies-are-cursors`' "a ring of cursors",
      `corruption-reported-when-cheap`), `splice-frame-premises`' Context
      on templates that "link every eraser", and `drops-stop-at-index`'
      Context on peeling and fusion, which `drop-runs-fuse` changed. A
      record whose decision still holds is revised in place, its rev
      moved; one that no longer holds is deleted once nothing cites it.
  - `cursor-laws.watch` — planned — throughout: the gate's sections and
    the proofs' check times recorded at each step's commit. A step that
    slows iteration much is followed by one that speeds it (the
    maintainer, 2026-11-23: "watch the growth and occasionally take
    action to improve iteration speed"). At `.emit.links` (2026-11-24):
    `glam/FREEZE_PROOF.bend` checks in 35 s cold, the gate in 81 s with
    the rest kept (run 346). 2026-11-25: the gate started every changed
    file's verdict at once, and five, 11.5 GB at their peaks, overran
    the container's 10 GiB, killing it with the session. Measured alone,
    the verdicts peak at 0.4 to 3.7 GB, the kernel's importers the
    largest (`MATERIALIZE_PROOF` 3.7, `POSITION_PROOF` 3.5,
    `SERVE_PROOF` 2.6); with company, a few percent more. The gate now
    starts them as the memory free at the start holds them
    (`scripts/verdicts.py`, by `scripts/mem_avail.py`, the container's
    limit counted), longest first by their last real durations, each
    capped on its own and its peak recorded for the next; the mutant
    runner sizes its jobs by the same free memory.

## Open

- Where the generators live in the tree, and whether `regen.sh`'s
  snapshot stays one file or becomes the hand-kept part of
  `glam/PROOF.bend` (`.sources.commit`).
- How much `.loop.shape` shrinks the proofs, and whether
  `.materializer`'s module should wait for it.
- Option C of the cursors' design, fewer cursors made (opportunistic
  crossing, for one), waits until it can be exercised usefully (the
  maintainer, 2026-11-22; moved here from `cursors-indexed` by the
  records' cleanup, `cursor-laws.records`).
