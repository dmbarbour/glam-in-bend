# An application meeting a builtin becomes an operator holding it

`operator-nodes` · maintainer · rev d24c09c

**Context.** A builtin function is an optimized `net_arity K` value
(`functions-are-nets-with-arity`): it stands for a small net of binds
feeding an operator, which takes data in and writes data out, without
that net being built. The spike called a builtin when an application met
data holding one (a `Call`), its encoding grown piecemeal: the op in the
field, the arity in the word or implied, other partial applications in
the data table's flat forms. A general form was built and proven on
2026-10-31: an operator with its payload behind a port, a separate
operator's data pairing an opcode with an accumulator, and a step the
operator rotates into (`spike-operators.model`, `.call`). Holding the
opcode in the header and the accumulator in the operator's own word,
the opcode in the kind all the time, makes the separate data and the
rotation unneeded (the maintainer, 2026-11-01).

**Decision.**
- One operator kind. An application meeting data that holds a builtin
  becomes, in place, an operator holding it: in its field the op (7 or 8
  bits) and the arity remaining (3 bits), in its word the accumulator, by
  form none, an immediate number or a reference into the data table; its
  principal on the argument, its other port the result.
- The argument's data arriving, the operator writes the result: computed
  when no arity remains, else the partial application, data holding the
  builtin with the argument accumulated, which the next application
  meets as data. Data and operators encode a builtin alike, so that
  materializing is a change of kind.
- An operator ensures only that its argument is data, which may be a
  thunk or a promise; forcing it further is the opcode's affair.
  `Bind >< Data(Net)` loads the net and awaits no data argument.
- An operator carries no level: its field is never read or lifted as a
  level, and a control facing it goes on to its result, which laws are to
  hold (`spike-operators.levels`).
- A payload behind a port, a computation rather than a value, waits for
  an operator that needs one. Cell references held directly in nodes were
  set aside: the collector would scan the node heap rather than a compact
  value table.

**Consequences.**
- The header is 6/2/24 (`header-kind-byte`).
- The call becomes the operator, and the dead call an eraser of the
  operator's input (`fusions-as-components`; once the dead operator); the
  general form of 2026-10-31 retires with its law (`spike-operators.one`).
- From the user's view there are still three kinds, copy, data and bind;
  operators are the implementation's.

**Rule lives in:** `spike/rules.bend` (the operator's rules);
`spike/kprim.bend` (the encoding); `spike-operators` in
`docs/plans/EvalSpike_2026-10-26.md`.
