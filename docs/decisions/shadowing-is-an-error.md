# A bare name is a local or a global, never both, within a file or object

`shadowing-is-an-error` · maintainer · rev 9433be0

**Context.** DistilledDesign said namespace shadowing "may warn", while
Syntax.md made it an error. Toplevel imports bring in names a reader may not
see, so a bare name that means a local in one place and a global in another
invites confusion.

**Decision.** Within a file or object, every bare name mentioned has exactly
one disposition: a local or a global, never both. A use that would give a
name a second disposition is an error, not a warning. Local-to-local
shadowing stays an error too.

**Consequences.**
- A name that merely exists in an imported or extended namespace may serve
  as a local, as long as the file or object never also uses it as a global.
- The rule may strengthen: the module work toward multiple inheritance may
  bring eager toplevel imports.

**Rule lives in:** Syntax.md, "Forbidden Shadows".
