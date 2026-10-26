# Shadowing a name a file defines or selects is an error

`shadowing-is-an-error` · maintainer · rev 42da1ff

**Context.** DistilledDesign said namespace shadowing "may warn", while
Syntax.md and the cheat sheet made it an error for a local to reuse a global
name its file defines or selects.

**Decision.** It is an error, as Syntax.md states. A local may not shadow
another local, a global name its file defines in a visible namespace, or a
global root the file selects. A name that merely exists in an imported or
extended namespace stays usable as a local until the file introduces,
overrides or references it.

**Consequences.** Within one file, one name has one meaning.

**Rule lives in:** Syntax.md, "Forbidden Shadows".
