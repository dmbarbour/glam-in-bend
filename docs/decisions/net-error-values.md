# Errors are data: a value that carries its diagnostic

`net-error-values` · maintainer · rev 8de15f2

**Context.** The kernel had no value for a failure. A void (`EraP`)
propagates through application, copies and operators, but means nothing
supplied and carries no reason (`net-void-demanded`); a stuck pair stops
demand with no message; the kernel's error count is for its own faults.
A builtin given arguments it had no case for, a dict read of a missing
key among them, answered unit, glam's real `()`, so that a failure
could not be told from a value, nor its cause read.

**Decision.** The maintainer (2026-11-09): a `Data` variant represents
an error. The rest is the agent's:
- `VErr{e}`, its diagnostic `e` a glam value, a text for now; Syntax.md's
  diagnostic objects, with their context frames, come with `anno 'error`.
- A builtin given an error answers it; applying an error answers it, the
  kernel's application test counting an error among the values it
  applies (`is_fn`), so that its operator waits for the argument as a
  builtin's does.
- A builtin given arguments it has no case for answers an error naming
  the builtin, every path to that answer giving one message (law
  `builtin_last_agrees`); a dict read of a missing key names the key.
- An error is data otherwise: copied, erased, passed by controls, and
  demanded only where needed, so that an error nothing demands fails
  nothing.

**Consequences.**
- The core reports an error that reaches `asm.result` with its
  diagnostic.
- An error applied to an argument that is no data (a function) leaves
  the operator stuck, as a builtin's would: the argument is not erased
  yet.
- HeapModel's permanent failure (`Failed{e}`) has its value.

**Rule lives in:** `spike/val.bend`, Builtins.
