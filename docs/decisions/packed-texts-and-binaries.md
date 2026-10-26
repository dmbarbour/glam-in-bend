# Texts and binaries are lists, stored packed

`packed-texts-and-binaries` · maintainer · rev e7899c5

**Context.** Texts and binaries are lists of small numbers in glam's
semantics. Stored as one Bend value per element, a megabyte costs tens of
megabytes.

**Decision.** Store texts and binaries packed, in rope leaves: four bytes per
`U32` for binaries, code points alike for texts. Semantically they stay
lists.

**Consequences.** List operations handle packed leaves, and unpack only what
a non-byte element forces.
