# Vendored sources

Third-party code copied into this repository (`vendored-sources`): one
subdirectory per source, holding the source's license and a `SOURCE.md`
saying where it came from, at which revision, what changed here, and what
uses it. A package on the Bend hub is imported by its hash instead, which
pins it as well as a copy would.

| Directory | Source | License | Used by |
|---|---|---|---|
| (none) | | | |

The last source, ajbarryiii/wilderness-labs-stt's `u32.bend` (MIT, laws
relating `U32` division to `Nat`), went once bend-mathlib 0.8.1.0
carried its laws (2026-10-31); git history keeps the copy.
