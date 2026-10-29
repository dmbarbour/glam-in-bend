# Third-party code is vendored by source, with its license and origin

`vendored-sources` · maintainer · rev 4f5db02

**Context.** The spike's proofs needed laws relating `U32` division to
`Nat` that no Bend hub package carries; another project's file has them
(the one upstream issue #1850 points to), under the MIT license. A hub
package is imported by its content hash, which pins it as well as a copy
would, so copying is needed only for code the hub does not hold. The
maintainer does not mind vendoring (2026-10-29).

**Decision.** Third-party code may be copied into the repository, under
`vendor/`, one subdirectory per source. Each subdirectory holds the
source's license and attribution files and a `SOURCE.md` giving where the
code came from, at which revision, what changed here and what uses it;
`vendor/README.md` indexes the sources. Code on the hub is imported by
hash instead.

**Consequences.**
- Changes to vendored code are kept to what is needed, each listed in
  its `SOURCE.md`; a copy is replaced by a package once one carries it.
- The gate typechecks vendored Bend files with the rest and checks the
  links of `vendor/`'s Markdown.

**Rule lives in:** `vendor/README.md`.
