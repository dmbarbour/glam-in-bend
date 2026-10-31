# A node's header: a kind byte, two bits of form, a 22-bit field

`header-kind-byte` · maintainer · rev 1b31125

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
  tiers, kind to class, the class pair to a rule
  (`heap-strategies.kinds.dispatch`). The class is the code's minimum
  with the count of base kinds: each base kind its own class, every code
  from the first operator's up one class, the operators', whose rule
  picks the operation by the code inside its step (the maintainer,
  2026-10-31, over a lookup table, which cost 2.3% where the minimum
  costs next to nothing; `heap-strategies.kinds.class`).
- The model's kinds widen with the header. The net's header still
  counts events a word a kind for codes below 16 alone: the first kind
  past them to make an event, a dead operator perhaps, widens it first
  (law `events_fit_header`).

**Rule lives in:** `spike/kprim.bend` ("Headers, levels, values");
the class tier in `spike/tools/gen_krules.bend` ("Dispatch"); the
field's laws in `spike/LAWS.bend` (`fld_bits`, `lift_fits`).
