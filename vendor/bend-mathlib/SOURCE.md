# bend-mathlib's `u32_eq_of_is_eq`

- **Source:** bend-mathlib 0.8.1.0 on the Bend hub, package
  `0x8ae61ec3a6615abd35f196c07232ad28`, file `string.bend`: the
  definitions `internal_false_ne_true`, `internal_fin_head`,
  `internal_fin_tail`, `internal_word_eq` and `u32_eq_of_is_eq`.
- **License:** Apache-2.0, its text in [LICENSE](LICENSE) as the package
  ships it; the package has no NOTICE file. glam is GPL-3.0, which
  Apache-2.0 code may join.
- **Why copied, though on the hub:** importing `string.bend` costs a
  proof file's verdict about 75 s (2026-11-24, Bend 2.0.39), and glam's
  proofs take this one lemma from it. The serve's verdict fell from
  190 s to 94 s with the index's proofs taking the copy instead
  (`cursor-laws.noself.frontier.cursor`).
- **Changes:** the definitions copied into a file of their own,
  [u32_eq.bend](u32_eq.bend), with a header saying so;
  `u32_eq_of_is_eq`'s law and def written as one def with its types.
  The bodies are unchanged.
- **Used by:** `glam/INDEX_PROOF.bend`. The other proof files importing
  `string.bend` for it move to the copy at `cursor-laws.proofs`.
- **Replaced** by an import once the hub carries the lemma in a file
  cheap to import. Offering that upstream waits until glam is
  relatively stable (the maintainer, 2026-11-25: "to avoid hassle and
  churn").
