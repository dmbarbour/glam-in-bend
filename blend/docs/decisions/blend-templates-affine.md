# A template is affine by default, as any definition

`blend-templates-affine` · maintainer · rev e8e6dfb

**Context.** Templates are Bend's, passed through (`README.md`).
Blend's affine default counts a template's call sites as any
definition's, so a template used twice is an error until marked
`shared` or `copied`, though Bend compiles each distinct set of `~`
arguments to a copy of its own. A default of its own for templates was
weighed (`blend-template-sharing`): `shared`, matching Bend, but letting
the same arguments at two sites, and an affine definition the template's
body calls, gain callers Blend does not count; `copied`, keeping the
affine guarantee at the cost of code; counting uses per distinct set of
arguments, mirroring Bend's own notion of distinct.

**Decision.** The maintainer (2026-11-05): affine stays the default for
templates, for consistency and as the "first, do no harm" option. The
guide explains the choice: `shared`, one definition and Bend's copies,
against `copied`, a copy for each use with the template's affine
callees copied with it, transitively.

**Consequences.**
- A template used more than once is marked, its sharing stated as any
  definition's is; the sample `templates` marks one `shared`.
- No rule keyed on `~`; the README's Templates and the planned
  `blend guide` carry the trade-offs.

**Rule lives in:** `README.md`, The model.
