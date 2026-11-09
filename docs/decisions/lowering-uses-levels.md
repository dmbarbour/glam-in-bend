# glam's lowering pairs its fans by GAL levels from the start

`lowering-uses-levels` · maintainer · rev c7a90cd

**Context.** Fans pair by static labels or by levels after GAL
(NetPairing, `pairing-gal`). The spike found static labels right on most
lambda terms and wrong under self-application, where two copies of one
duplication meet under one label; levels right on every term tried, at
the cost of control nodes (brackets and croissants) and their
interactions. The hello ladder's first fans, locals copying data
(`ladder-locals`), paired by labels. Lowering functions (`ladder-lambda`)
needed the choice: labels first, levels where a test shows a need, or
levels throughout.

**Decision.** The maintainer (2026-11-09): GAL levels from the start.
glam's lowering gives every function, application and copy fan its
level, the depth of boxes around it, an application's argument a box one
level deeper, and puts controls where a variable's uses cross box
boundaries, as `spike/tools/terms.py` lowers terms with levels; a local
binding's value is a box, as the argument of the application it stands
for (`let x = v in b` is `(\x -> b) v`).

**Consequences.**
- Nets from `.g` pair as the spike's leveled terms do, self-application
  included; the controls' interactions are part of every count.
- Whether a function known to need no levels could drop them is a later
  optimization (NetPairing's `pairing-overhead`), measured against this.
- `pairing-verdict` keeps the question open for nets users build with
  `interaction_net` (`pairing-nets`).

**Rule lives in:** `glam/lower.bend`, its header.
