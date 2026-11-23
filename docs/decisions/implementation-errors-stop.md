# glam stops at its own implementation's first reported error

`implementation-errors-stop` · maintainer · rev 4713121

**Context.** The kernel counts its errors in the heap's header, among
them corruption detected for free (`corruption-reported-when-cheap`) and
an index insert meeting its own key. The count was read only when a
cell's value was forced or the run ended. So a serve that met corruption
went on: the crossings continued, the serve returned as if whole, and
the core could read a half-made cursor's words before anything
reported it (`docs/reviews/IndexHolistic_2026-11-23.md`; the second
reviewer's H7).

**Decision.** The maintainer (2026-11-23), asked whether a serve should
stop at the first error it reports: "Yes. We won't push through glam
implementation errors. This is different from user errors such as syntax
issues."

**Consequences.**
- An error of glam's own implementation stops the run where it is first
  read cheaply, and is reported: a kernel error, corruption, a broken
  invariant. A net known to be corrupt is driven no further.
- User errors are diagnostics as before, collected and reported as the
  language reports them (`diagnostic-wording-ours`), and may continue.
- The serve reads the error count where it ends (`cursor-laws.stop`).

**Rule lives in:** `glam/core.bend`, where a serve's end is received.
