# A function's net is copied as a live template: frozen where finished, cursors where not

`copy-reduced-function-nets` · maintainer · rev 78181fe

**Context.** A function is a net and its remaining arity, and its copies
share the reductions of its source (`functions-are-nets-with-arity`). In
2026-10-28 the maintainer wrote: "I intend to freeze a net only after
we're done reducing instead of many snapshots at arbitrary points".

The Rust bootstrap copied a function's net through cursors, "an
approach to copying live nets while keeping the original separated"
(the maintainer, 2026-11-10). HeapModel summarizes it: "A whole copy
only when the source has nothing left to reduce and at most 64 nodes
reachable from its interface; otherwise cursors, whose pending pairs
reduce in the source, in place, once for every copy."

A net copied whole must first be reduced as far as it goes. The
maintainer called that "maximal partial evaluation at every application
step" (2026-11-09).

**Decision.** The maintainer (2026-11-10), on freezing the parts of a net
that won't change while providing cursors to the unprocessed items:
"This was the intended direction, which I had described as batch
materialization (iirc). We could call that a live template, or a
template with live parts". And, on freezing: "a net simply would not
freeze if or insofar as there's any residue".

- A function's net is copied by batch materialization. Its finished
  parts are frozen and copied whole.
- Each unprocessed item stays in the source, where every copy reaches
  it by a cursor, and it reduces there once for every copy.
- A net freezes only insofar as nothing is left to reduce.
- Reducing the net before it is copied is an optimization
  (`early-evaluation-optimization`): "we don't necessarily need to
  eagerly evaluate functions if we don't need to fully freeze them".

**Consequences.**
- Every copy shares the work in the source, whether it is done before a
  copy is taken or after. An active pair in the source reduces there
  even when its wires reach the function's parameter, which is a free
  wire in the source. Only what waits on an argument's data is done per
  copy, from structure the copy takes as finished.
- The source stays live while any copy can reach it by a cursor.
- Copying a net whole is the case where nothing is left to reduce.
  There, small nets (128 nodes to start, `net-nodes-double`) and compact
  forms of finished nets (`spike-materialize`) matter. Cursors are
  EvalSpike's `spike-cursors`.
- This record first held a quick start the agent favoured as if it were
  decided: reduce a function's net, then copy it whole, with cursors
  later. The maintainer dropped it (2026-11-10): "If it isn't working
  out, drop it. It should have been recorded as an experimental
  direction, not an ADR." Live templates are built now, in the Cells
  plan's `cells-freeze`.
