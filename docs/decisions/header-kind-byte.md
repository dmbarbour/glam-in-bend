# A node's header: a kind byte, two bits of form, a 22-bit field

`header-kind-byte` · maintainer · rev 25710ad

**Context.** A node's header word held a 4-bit rule kind, a 4-bit value
form and a 24-bit field (`spike/kprim.bend`). All 16 kinds are in use,
the linear fans among them, while dead calls and builtin operators want
more: about two kinds a hot operator, some 40 for 20 primops
(`spike-operators`), besides fused variants. Of the form's values only
four are used, and with operators' states in their kinds, data needs
only whether its value is immediate, and functions, applications and
fans whether their net was built without levels. Options were 6/2/24,
7/1/24 and 8/2/22 (`heap-strategies.kinds.layout` in
`docs/plans/HeapModel_2026-10-27.md`).

**Decision.** 8 bits of kind, 2 of form, 22 of field (the maintainer,
2026-10-30): 256 kinds, room for fused ops to spare.

**Consequences.**
- Levels, sites and a control's index fit in 22 bits, to 4M rather than
  16M; the field's laws (`fld_bits` and those built on it) and the level
  cap change with it.
- Dispatch can no longer be a match on the pair of kinds: it goes in
  tiers, kind to class by a lookup table, the class pair to a rule
  (`heap-strategies.kinds.dispatch`).
- The model's kinds widen with the header.

**Rule lives in:** `docs/plans/HeapModel_2026-10-27.md`,
`heap-strategies.kinds.layout`, until the header changes in
`spike/kprim.bend`.
