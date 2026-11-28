# A serve leaves the free list's last node

`serve-spares-last-free` · agent · rev c16da74

**Context.** The guard before a serve (`mz.room`) asks room for the
nodes the serve may take: its template's, and a branch for each
crossing (`mz.need`). The guard's laws need the free list's tracked
prefix to be the whole list (`LM.ends`), so that must survive a serve.
Where the serve takes every node the list had, the list's end after it
is whatever the last node taken and the nodes freed leave: shown only by
following the list through each crossing's pops and pushes, a second
copy of the crossings' chain proofs. Where it leaves one node, the
last, it writes none of that node's words, so the node's link word,
which ended the list, ends it still (`serve_ends`, from the serve's
frame).

**Decision.** The agent (2026-11-28), as a tactic: the guard asks room
for one node more than the serve can take, so that the free list's last
node outlives every serve.
- The cost is at most one growth earlier, where the list held exactly
  what the serve could take. No net's result changes.
- The spare node is no particular node: nothing marks it, and the
  kernel's steps between serves may take it, the next guard asking
  again.

**Consequences.**
- `serve_ends` asks room for the crossings without the list's last node
  (`RG.cxs.ok` over the list before it), which the spare node gives.
- Without the spare, coverage across a serve needs the step-by-step
  proof through the crossings instead.

**Rule lives in:** `glam/materialize.bend`, `mz.need`.
