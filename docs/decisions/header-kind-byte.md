# A node's header: a 6-bit kind, two bits of form, a 24-bit field

`header-kind-byte` · maintainer · rev ea752b2

**Context.** A node's header word held a 4-bit rule kind, a 4-bit value
form and a 24-bit field (`spike/kprim.bend`). With all 16 kinds in use,
the linear fans among them, dead calls and builtin operators wanted more:
about two kinds a hot operator, some 40 for 20 primops, besides fused
variants. 8/2/22 was chosen for that (the maintainer, 2026-10-30), over
6/2/24 and 7/1/24. Then operators came to hold their opcode and remaining
arity in the field, one kind for all of them (`operator-nodes`, revised
2026-11-01), so they need no kinds of their own; 4/4 had been too tight,
but a byte is more than is needed. The slug names the 2026-10-30 choice.

**Decision.** 6 bits of kind, 2 of form, 24 of field (the maintainer,
2026-11-01): 64 kinds, levels, sites and a control's index to 16M.

**Consequences.**
- Of the form's values, data uses all four (a table entry, a number, and
  a builtin's two immediate forms), functions, applications and fans
  whether their net was built without levels.
- A kind that carries no level may use the field for itself: data and
  operators hold a builtin's op and arity there. Lifts and level checks
  must touch only leveled kinds (`spike-operators.levels`).
- Dispatch goes in tiers, kind to class, the class pair to a rule
  (`heap-strategies.kinds.dispatch`). The class is the code's minimum
  with the count of base kinds (the maintainer, 2026-10-31, over a lookup
  table, which cost 2.3% where the minimum costs next to nothing;
  `heap-strategies.kinds.class`).
- The field's laws (`fld_bits` and those built on it) and the level cap
  follow the field's width. The net's header still counts events a word
  a kind for codes below 16 alone: the first kind past them to make an
  event, a dead operator perhaps, widens it first (law
  `events_fit_header`).

**Rule lives in:** `spike/kprim.bend` ("Headers, levels, values");
the class tier in `spike/tools/gen_krules.bend` ("Dispatch"); the
field's laws in `spike/LAWS.bend` (`fld_bits`, `lift_fits`).
