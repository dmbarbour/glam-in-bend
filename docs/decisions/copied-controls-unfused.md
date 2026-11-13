# A control a copy has taken is marked, and fusion refuses it

`copied-controls-unfused` · maintainer · rev bfd30ec

**Context.** A live template's finished nodes are copied while its
pending pairs still reduce in the source (`copy-reduced-function-nets`).
The kernel fuses controls after each rewrite (`fuse-control-runs`;
`P.fuse` in `spike/krules.bend`). A rewrite in the source can therefore
fold a new control into a finished one that a copy has already taken,
changing its offset, and the copy then misses the shift that a later
join needs.

Turning runtime fusion off everywhere was measured on 2026-11-11
(analysis store runs 313 to 315; the Cells plan, `cells-freeze.fusion`).
It costs 23.5% more interactions under demand on the library lowered as
glam lowers, 8.4% under full reduction, and 11% to 12% on the ladder's
sharing families.

**Decision.** The maintainer (2026-11-11): "we'll go for marking copied
controls to block further aux-side fusions." When a materialization
first copies a control out of a source, it marks that control in the
source, and fusion refuses any marked control. Runtime fusion stays
everywhere else.

**Consequences.**
- The mark is form 1 of the control's header (`P.mark`, `P.marked` in
  `spike/kprim.bend`), a control's form bits otherwise clear. No reader of
  a control's header reads them, as checked when it was built
  (2026-11-13): dispatch reads the kind (`P.rk`); fusion, peeling and
  freezing read the field and the offset word. A rewrite copies a form
  only from a node it consumes, and a marked control, finished, is in no
  pair; fusion's result and a copy's nodes are written with form 0, so a
  copy in its host fuses freely.
- Fusion tests the mark in `P.fuse_test` before composing, where both
  headers are read already (law `marked_unfused`): instructions moved at
  most 0.02% on the spot workloads (analysis store run 321). Freezing a
  source's finished part sets it, one write for each control taken
  (`fz.copied` in `glam/freeze.bend`); reading a net back whole does
  not. `glam/test_mark.bend` checks both on the kernel's code.
- With the mark, finished nodes stay finished under reduction, which
  the cursor laws can then state without an exception for fusion.
- Instruction-level comparisons come later, with a build that neither
  fuses nor pays to look for fusions (the maintainer, 2026-11-11).
