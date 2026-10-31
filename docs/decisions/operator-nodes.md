# Builtins run as operators: an application meeting OpData becomes an Op

`operator-nodes` · maintainer · rev 4163126

**Context.** A builtin function is an optimized `net_arity K` value
(`functions-are-nets-with-arity`): it stands for a small net of binds
feeding an operator, which takes data in and writes data out, without
that net being built. The spike called a builtin when an application met
data holding one (a `Call`, the function inside the node), which left no
general form for the fused ones to be proven against. `spike-operators`
in `docs/plans/EvalSpike_2026-10-26.md` sketched one; the maintainer
settled it on 2026-10-31.

**Decision.**
- An application meeting an operator's data, `OpData(OpCode,
  Accumulator)`, becomes the operator in place: `Ap(Arg, Result) ><
  OpData` rewrites to `Arg >< Op(Payload, Result)` with `Payload` that
  `OpData`, the principal turned to the argument, so that demand now
  reaches it.
- The argument's data arriving, the operator turns to its payload: a
  step holding the argument (`OpStep`) meets the `OpData`, the two data
  meet and one is written to the result. Where arity remains, that
  result is data, a partial application, which the next application
  meets as data.
- Data holding a builtin materializes, one way, into `OpData` when an
  application meets it; that materialization fused with the rotation is
  the call. An operator ensures only that its argument is data, which may
  be a thunk or a promise; forcing it further is the opcode's affair.
  `Bind >< Data(Net)` loads the net and awaits no data argument.
- `OpData` is not data but net structure. Its accumulator is held as a
  value, a reference into the data table first, a computed accumulator a
  lazy value; an accumulator behind a port, and the levels it brings,
  wait for an operator that needs one.
- Fused forms, each proven to behave as the general one
  (`fusions-as-components`): an operator holding a full 32-bit opcode in
  place of its payload port, its payload `OpData(OpCode, EraP)`, a unary
  one finishing on its argument; opcodes in kinds with the payload
  immediate, few, spent where profiles say.
- Cell references held directly in nodes were set aside: the collector
  would scan the node heap rather than a compact value table.

**Consequences.**
- The kinds `Op`, `OpStep` and `OpData` (codes 17 to 19) join the base
  kinds; a step's meeting applies B's function to A's data, a source of
  its own (`SApplyB`).
- An operator's payload looped to its result is a loop the law
  `aux_loops` allows, stuck: the payload waits on its own result.
- From the user's view there are still three kinds, copy, data and bind;
  operators and their data are the implementation's.

**Rule lives in:** `spike/rules.bend` ("Operators"); `spike-operators` in
`docs/plans/EvalSpike_2026-10-26.md`.
