# Vendored sources

Third-party code copied into this repository (`vendored-sources`): one
subdirectory per source, holding the source's license and a `SOURCE.md`
saying where it came from, at which revision, what changed here, and what
uses it. A package on the Bend hub is imported by its hash instead, which
pins it as well as a copy would.

| Directory | Source | License | Used by |
|---|---|---|---|
| [`wilderness-labs-stt/`](wilderness-labs-stt/SOURCE.md) | ajbarryiii/wilderness-labs-stt, `u32.bend` at f3603a0e14b8: laws relating `U32` to `Nat` | MIT | `spike/PROOF.bend` |
