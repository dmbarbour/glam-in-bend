# Parallelism comes from sparks; a net's pairs reduce in sequence

`parallel-sparks` · maintainer · rev 25e6e26

**Context.** An interaction net allows every active pair to be reduced
at once, and Bend parallelizes balanced fork-join calls. A strategy
reducing a net's pairs in parallel would have to stage each round,
computing every pair's outcome without writing outside its own nodes,
then joining the outcomes' links. Coarse tasks parallelize more cheaply
(`rounds-of-coarse-work`). The evaluation strategies built so far are
sequential (HeapModel's `heap-strategies`).

**Decision.** The primary source of evaluation parallelism is sparks, as
in Haskell: tasks that reduce lazy values ahead of demand. A strategy
reduces its net's active pairs one at a time.

**Consequences.**
- A strategy's rewrites may write anywhere in its net, and its pairs
  need no staging; one worker reduces a net at a time
  (`net-nodes-double`).
- Parallel speed depends on the program exposing sparks: through
  annotations, analysis, or lowering that emits them.
- Parallel reduction of one net's pairs returns only if measurements
  show sparks leave workers idle on work a single net holds.
