# Net construction refuses obvious errors, and only those

`net-obvious-errors` · maintainer · rev e21c554

**Context.** A net built by `interaction_net` can be wrong in ways that
are cheap to see: a port wired twice or not at all; a subnet not
connected to the exposed port, which the Rust bootstrap's construction
already refuses; or a vicious circle, nodes each with its principal port
wired to an auxiliary port of the next, round to the first, which can
never interact (Lafont, Interaction Combinators, 1997, §1.6). Each node
has one principal port, so following principal ports from every node
finds every circle in time linear in the net. Circles also form while a
net reduces. No rule-local condition was found that would keep them from
forming (`pairing-nets.switching`), and whether a net comes to deadlock
is in general as hard as whether a program halts.

**Decision.** glam's net construction refuses the errors it can
recognize and report efficiently: besides a port not wired exactly once,
a subnet disconnected from the exposed port, and a vicious circle. What
glam recognizes as an obvious error grows gradually, through analyses
and lightweight type checking; but glam does not restrict a program where
it cannot efficiently recognize or prove an error. A circle that forms
while a net reduces is not prevented: demand reports it on reaching it.

**Consequences.**
- A vicious circle formed by reduction stays in the net, stuck, where
  diagnosis can see it.
- The spike's tools check lowered nets for vicious circles beside
  polarity (`spike/tools/polarity.py`), and the library keeps a
  hand-built net with one only to show demand finding it.
- A net's wiring, each port wired exactly once and so none facing
  itself, has one definition in the laws: the audit's verdict,
  `KN.wired_ok`, the same check the library runs after every case. A law
  that needs the wiring takes that verdict as a premise; its reading
  port by port (`WR.port.ok`) is tied to the audit by a law
  (`wired_port`), so that no second definition of wired can drift from
  the first. The model proves every rewrite keeps a net wired
  (`W.wired`, `rewrite_wired`); construction's refusal of a port not
  wired exactly once is the premise's base case at loading, and the
  kernel's refinement against the model its discharge through reduction
  ([`../plans/KernelRefine_2026-11-24.md`](../plans/KernelRefine_2026-11-24.md)).
  The maintainer (2026-11-24): "each port must appear exactly once in
  the initial wiring (for `interaction_net`), which prevents initial
  self links."

**Rule lives in:** `docs/Design.md`, Interaction Nets; `spike/knet.bend`
(`KN.wired_ok`, the wiring premise's owner) and `spike/WIRED_LAWS.bend`
(`wired_port`).
