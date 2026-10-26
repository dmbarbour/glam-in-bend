# Texts and binaries are lists, stored packed

`packed-texts-and-binaries` · maintainer · rev a5d3082

**Context.** Texts and binaries are lists of small numbers in glam's
semantics. Stored as one Bend value per element, a megabyte costs tens of
megabytes; even one byte per `U32` array cell quadruples memory traffic.

**Decision.** Store texts and binaries packed: four bytes per `U32`, byte
`i` in word `i >> 2` at bits `8 * (i & 3)`, low byte first, in rope leaves
and in byte arrays alike. Code points pack likewise for texts.
Semantically they stay lists. Only a parser may keep one byte per cell, and
only where that is especially convenient; evaluation never does.

**Consequences.**
- Every byte index carries two bits of complexity, which costs about
  0.4 ns per byte on random access. Sequential consumers (lexer, hashing,
  output) read whole words and come out ahead: scanning 64 MB took 20 ms a
  word at a time against 29 ms at one byte per cell.
- List operations handle packed leaves, unpacking only what a non-byte
  element forces.
