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
- The mark is a bit of the control's header. A control's two form bits
  are clear today: `hd(k, n)` in `spike/kprim.bend` writes only the kind
  and the field. Every reader of a control's header must ignore the bit,
  which is to check when it is built.
- `fuse` already reads both controls' headers before composing them, so
  testing the mark costs almost nothing. Setting it is one write to the
  source for each control a copy first takes: metadata, not structure.
- With the mark, finished nodes stay finished under reduction, which
  the cursor laws can then state without an exception for fusion.
- Instruction-level comparisons come later, with a build that neither
  fuses nor pays to look for fusions (the maintainer, 2026-11-11).
