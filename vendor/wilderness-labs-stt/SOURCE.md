# wilderness-labs-stt: U32 laws

- **From:** https://github.com/ajbarryiii/wilderness-labs-stt,
  `finetune/bend-planner/u32.bend` at commit
  `f3603a0e14b8328d62488e0d0a3f5f907d96ef58`, retrieved 2026-10-29: the
  file that upstream Bend issue #1850 points to.
- **Author:** ajbarryiii.
- **License:** MIT, in [`LICENSE`](LICENSE), copied from the repository's
  root at the same commit.
- **Here:** `u32.bend`, laws relating `U32` to `Nat`: comparison,
  subtraction, increment, conversions, and division (`U32.to_nat_div`,
  `U32.divmod_spec`).
- **Changed:** one line, the `nat.bend` import, from
  `0xcd4682caa53da19986acd472c2181473` (an earlier bend-mathlib release)
  to `0x78e347bf8d0582a322c01b02c727566f` (bend-mathlib 0.8.0.0, which
  the spike's proofs import), so that one release of the `Nat` laws is
  loaded. The upstream file's SHA-256 is
  `88184af1d2a0731ab178ff1e77c939fe301f4cca44f73061363fa88e5a10c64f`.
- **Used by:** `spike/PROOF.bend` (laws `fld_bits`, `off_by_bits`).
- **Replace with:** a hub package or Base, once either carries these laws.
