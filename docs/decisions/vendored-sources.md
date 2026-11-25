# Third-party code is vendored by source, with its license and origin

`vendored-sources` · maintainer · rev 284f490

**Context.** The spike's proofs needed laws relating `U32` division to
`Nat` that no Bend hub package carries; another project's file has them
(the one upstream issue #1850 points to), under the MIT license. A hub
package is imported by its content hash, which pins it as well as a copy
would, so copying is needed only for code the hub does not hold. The
maintainer does not mind vendoring (2026-10-29).

A hub file can cost far more than the code taken from it, though: the
proofs took one lemma from bend-mathlib's `string.bend`, whose import
cost each proof file's verdict about 75 s (2026-11-24). The maintainer
(2026-11-25): "I'm not too concerned about copying if licenses are okay
for it, but we do need to document things properly."

**Decision.** Third-party code may be copied into the repository, under
`vendor/`, one subdirectory per source. Each subdirectory holds the
source's license and attribution files and a `SOURCE.md` giving where the
code came from, at which revision, what changed here and what uses it;
`vendor/README.md` indexes the sources. Code on the hub is imported by
hash instead, unless importing it costs far more than the code taken
from it; then that code is vendored the same way.

**Consequences.**
- A copy's license must let it join glam's GPL-3.0, and its subdirectory
  meets the license's terms: the license's text, the source's notices,
  and the changes marked in the copy and listed in `SOURCE.md`.
- Changes to vendored code are kept to what is needed, each listed in
  its `SOURCE.md`; a copy is replaced by a package once one carries it.
- The gate typechecks vendored Bend files with the rest and checks the
  links of `vendor/`'s Markdown.

**Rule lives in:** `vendor/README.md`.
