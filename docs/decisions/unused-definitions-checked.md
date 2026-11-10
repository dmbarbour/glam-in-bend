# Errors in definitions nothing uses may fail the assembly; module loading stays lazy

`unused-definitions-checked` · maintainer · rev 3a628b4

**Context.** Root cells (`cells-data.root`) lower a module's templates and
recipes when the module starts, so a form not lowered yet, or any error
lowering finds, fails the assembly even in a definition nothing demands.
The static linker before them dropped such a definition unread, a
difference the differential run against it cannot see. The desugarer
already reports every definition's errors, used or not.

**Decision.** The maintainer (2026-11-10): "I don't mind that errors in
unused definitions fail the assembly, so long as hierarchical module
loading is lazy."

**Consequences.**
- A module's own definitions are all checked when it loads, by the
  desugarer and the lowering alike.
- A module is loaded only when demanded: modules as objects
  (`cells-modules`) keep loading lazy, so an error in a module nothing
  needs fails nothing.
