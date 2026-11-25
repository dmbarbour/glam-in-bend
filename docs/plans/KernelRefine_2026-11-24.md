# Kernel refinement — 2026-11-24

Drafted for the maintainer's review before building.

The kernel's heap shown to do what the wiring model does, so that the
premises the materializer's laws take on the source's wiring
(`net-obvious-errors`) are discharged. The model's half
exists: every rewrite of the rule table keeps a net wired (`W.wired`,
`rewrite_wired`, `rules_keep_wired_in`, `spike/wiring.bend`). The heap's
half is audited at run time (`KN.wired_ok`). This plan builds the bridge
the HeapModel plan drafted (`kernel_rewrite_refines`,
`kernel_audits_exact`, through an abstraction `KA`), which
`heap-laws-align.statics` found cannot hold as drafted: the model places
an eraser as a node where the kernel makes it static, and the reserve
cut from the free list breaks `FL.ok`'s one list.

The bridge from code to model that the freeze's laws use
(`glam/FREEZE_PROOF.bend`: equations over mirrored arrays, a model
rewritten into, a step template) is the technique to try first on the
kernel's own state, which no law has yet been stated over
(`docs/BendIssues.md`).

## Steps

- `kernel-refine` — planned — the steps below.
  - `kernel-refine.align` — planned — `heap-laws-align.statics`'s
    alignment: statics as leaf ends in `W.wired`, or a phantom node per
    static link where a kernel net is read back
    (`static-links-count-as-nodes`); the reserve in the free list's
    model, or read back as free list then reserve. Laws over the model
    restated where they change, with the maintainer's approval.
  - `kernel-refine.audit` — planned — `kernel_audits_exact`:
    `KN.wired_ok` holds exactly when `W.wired` holds of the heap's
    abstraction. It is read-only, so it is the first bridge to try.
    Its bridge to a model over the words' tree exists already
    (`spike/WIRED_PROOF.bend`'s `b.go` and `wired_back`, built for
    `wired_port`); what remains is the abstraction `KA` and `W.wired`'s
    side.
  - `kernel-refine.probe` — planned — one generated rewrite, the
    smallest rule's, bridged to the model's step before the rest are
    costed. If the kernel's hot path must be reshaped for proofs, that
    goes to the maintainer with the four builds measured.
  - `kernel-refine.rewrite` — planned — `kernel_rewrite_refines` over
    the generated rewrites (about 58 link sites in `spike/krules.bend`),
    per rule or argued once over the generator's output
    (`spike/tools/gen_krules.bend`).
  - `kernel-refine.copy` — planned — the materializer's own writes kept
    wired: the splice from a template in which each port is wired once,
    the ring's joins and leaves.
  - `kernel-refine.discharge` — planned — the wiring premise discharged
    for the materializer's laws; `sv.front.c`'s check replaced by its
    law (`cursor-laws.noself.frontier`). `front_apart` and the serve's
    laws (`front_joins`, `front_joins1`) owe two premises on the
    frontier's heap: wired, and the served position a live node's port
    below its kind's arity, which holds of a finished node as long as
    the walks leave it untouched (`copied-nodes-untouched`).

## Open

- Whether the kernel's state is refined against the model whole, or only
  the wiring is (`KA.ends`), the free list and kinds left to their
  audits.
