# A static eraser at an auxiliary port acts where it is written

`erasure-at-write` · maintainer · rev 8ff2722

**Context.** A static eraser at an auxiliary port marks that port dead
(`static-links-count-as-nodes`). HeapModel's
`heap-strategies.erasure.load.cycle.walk.directed.dead-kinds.links.dead-ports`
read those statics when a pair is rewritten. It took a fan or function
by the kind its dead ports made it, from link words the rewrite reads
anyway. Bend compiles every function into a call with its results passed
through memory, and a shared function with a second caller becomes a
segment of its own. Every form of that read tried cost each rewrite
40 to 100 instructions, 5% to 10% on plain demand, with identical
interactions (gcbench runs 222, 223; spot run 224). That paid for 0.02%
fewer interactions on demand. A generated table indexed by the statics'
pattern was cheapest, but it pushed the library's build past 6 GB.

**Decision.** The maintainer (2026-11-03): erasure at an auxiliary port
is handled where the static is written, never tested on the rewrite's
path. A node whose last auxiliary is erased is erased at its principal,
a linear chain (`.links.propagate`). That step tries it first without the
kinds a dead side makes (the linear fans), whose port layouts cost a swap
and a fault. If kind-based specialization of fans and merges proves
simpler and more efficient, it returns.

**Consequences.**
- The rewrite's dispatch reads kinds alone, as before
  `.links.dead-ports`.
- Writers of statics (native rules, static erasure, the sweep, the
  loader) are where erasure continues; plain strategies may then make
  events, as the erasure modes do now.
- A fan with one dead side goes through the full fan's rules, its dead
  side meeting the static, unless kinds return.
