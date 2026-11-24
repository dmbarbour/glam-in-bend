# The source's wiring is a named premise until the kernel refines its model

`wiring-premise-before-refinement` · maintainer · rev b459ab7

**Context.** The materializer's remaining laws rest on the source net
being wired: no port facing itself, links two-way. The frontier's check
(`sv.front.c`) fires exactly when the served position's port faces
itself, and the finished walk lists each node once only if each
principal is faced by one port. The model proves every rewrite keeps a
net wired (`W.wired`, `rewrite_wired`), and `KN.wired_ok` audits the
heap at run time, the library running it after every case. The bridge
between heap and model, the HeapModel plan's draft refinement
(`kernel_rewrite_refines`, `kernel_audits_exact`), cannot hold as
drafted (`heap-laws-align.statics`). The maintainer was offered three
routes:
- conditional laws now, the wiring a named premise;
- the refinement inside `cursor-laws.noself`;
- the runtime checks kept and `noself` left for later.

**Decision.** The maintainer (2026-11-24): "Take your recommended route,"
the first.

**Consequences.**
- The materializer's laws that need the wiring take it as a premise:
  `KN.wired_ok`'s own verdict on the source heap, so that the premise is
  the audit the library runs, with no second definition of wired.
- `sv.front.c`'s check stays until the premise is discharged.
- The refinement is a plan of its own
  ([`../plans/KernelRefine_2026-11-24.md`](../plans/KernelRefine_2026-11-24.md)),
  starting from `heap-laws-align.statics`; discharging the premise is
  its last step.
- The base case at loading: `interaction_net`'s construction refuses a
  port wired twice or never (the maintainer, 2026-11-24).

**Rule lives in:** `spike/knet.bend` (`KN.wired_ok`, the premise's
owner); the cursor-laws plan's `cursor-laws.noself`.
