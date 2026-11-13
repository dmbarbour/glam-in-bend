# Array laws — 2026-11-13

Drafted for the maintainer, at their request (2026-11-13): "Do
investigate what other users have proven about arrays. We might be able
to reuse a bit. Or we might not, but we should know that and have a list
of deficiencies ready to present for the appropriate packages." The
need is the proof ladder of `cells-freeze.nested.host` in
[`../plans/Cells_2026-11-09.md`](../plans/Cells_2026-11-09.md), whose
first rungs read the heap after a write: the heap's words are a Bend
`Array<U32>` (`spike/kmem_grow.bend`), indexed by shifts and masks. This
review proposes; the maintainer decides, among other things whether
glam's laws may depend on third-party packages.

## How it was searched

The hub's search (`hub.bend-lang.com/search.json?q=`) for array, word,
bit, bits, shift, u32, lemma, lemmas, proof, mathlib, vector, lawful,
osdev, gralha and ndarray: 146 package versions. Read, from the hub's
raw files (`hub.bend-lang.com/<hash>/<file>`): `lawful-arrays`,
`lawful-words`, `lawful-bytes`, `lawful-halves`, `lawful-fields`,
`bend-osdev-array`, `bend-osdev-word64`, `bend-kit-lemmas`,
`gralha-byte-words` and `bend-ndarray`, beside `bend-mathlib`, which
glam's proofs use now. Checked under the Bend glam pins (2.0.39):
`lawful-arrays@0.1.0.1`, `lawful-words@0.1.0.1` and
`bend-osdev-array@0.1.0.1`, each its whole `PROOF.bend` with `--check-only`
and `--verdict` (BendTT's kernel, as the gate runs it), all passing, in
seconds.

## Findings

**F1. `lawful-arrays` proves the first rung.** By luiscleto, MIT,
version 0.1.0.1 (hash `0x2c172a8ac85e328d5e6af8aa51cec1f8`). Its laws
are stated on the list of an array's leaves (`D.view`), for perfect
trees (`D.full(T, a, d)`, depth `d`, as `Array.new` makes them and every
write keeps them), an index reaching leaf `i mod 2^d` (`D.slot`), depth
below 32 where an index is read. What the ladder needs, by name:
- `get_set_same`: a read after a write at one index gives the value
  written, for every tree;
- `get_set_other`: a write at slot `i` leaves the read at another slot
  `j` as it was;
- `new_full`, `set_full`, `swap_full`: `Array.new` makes a perfect tree,
  and writes keep it;
- `slot_small`: an index below `2^d` reaches itself, so that a heap's
  word index, below its capacity, needs no modular reasoning;
- `size_count`, `get_kept`, `get_pair`, `get_new`, `set_view`,
  `view_inj` and more.

The array literal glam's heaps are made with, `[0 : U32^d]`, is
`Array.new(U32, d, 0)` by definition (checked by `{==}`), so `new_full`
covers it. Its README says its laws "have been reviewed by AI models but
not yet by a human expert": the proofs are the checker's, and the agent
read the statements above and finds them to say what their comments say.
Verdict: reuse.

**F2. `bend-osdev-array` proves the same by another route.** Version
0.1.0.1 (hash `0xf8d2948fe25df08ae8d37c3c80a363ba`), MIT, on
`bend-osdev-u32`. Its `get_set_other` takes the masked indexes' words
unequal (`U32.and(i, 2^d - 1)`), where `lawful-arrays` takes the slots'
values unequal; and it adds `reflect`: every perfect array is one built
from a `Data` list (`Arrays.of_list`), so a proof can follow a run of
reads and writes on data alone. Verdict: an alternative; `lawful-arrays`
first, for its companion `lawful-words`.

**F3. `lawful-words` proves the word arithmetic.** Version 0.1.0.1 (hash
`0x96ab58f86121cb4f3fb48b3c8a045989`), MIT, same author. The values of
`U32.shr`, `U32.shl`, `U32.shrn`, `U32.shln` (`to_nat_shr` and the
rest), a mask of the low `k` bits as the remainder modulo `2^k`
(`to_nat_and_mask`), `not`, `or` and `xor` of disjoint parts, bit by bit
(`bit_and`, `bit_or`, `bit_xor`, `bit_not`, `bit_ext`), and a word split
into its high part and low bits (`to_nat_split`), with byte indexes as
`word * 4 + byte`: the arithmetic of a node's base and port in the
kernel's heap (`P.base`, `b + 1 + p`). Verdict: reuse.

**F4. `bend-mathlib` lacks what the heap needs.** The hub package glam's
and Blend's proofs import (`0x8ae61ec3a6615abd35f196c07232ad28`,
0.8.1.0) proves comparison, addition, subtraction, increment, `min`,
`max` and division of `U32`s through their values, and nothing of
shifts, masks, bitwise operations or arrays. Verdict: keep it beside the
two above; all state their facts through `U32.to_nat`, so they compose.

**F5. What no package proves, which the ladder needs anyway.**
- *The heap growing.* `KM.m_ensure` copies the words into a deeper array
  (`kmem_grow.bend`'s `copy`): a law that the copy keeps every word
  below the old capacity, and the new array perfect, is glam's to write,
  from `get_set_same`, `get_set_other` and `set_full`.
- *A node's base.* `P.base` clears a reference's low two bits
  (`r .&. 4294967292`); its value, `r - r mod 4`, follows from
  `to_nat_split` and the bit laws, but no package states it.
- *The free list, joins and serves.* The kernel's free-list laws are
  over a model (`FL`), not over `P.alloc` and `P.free`; these and the
  rungs above them are glam's own.

## Deficiencies to present

By package, for when the maintainer chooses to raise them (upstream is
commented on only at the maintainer's request):
- **`bend-mathlib`:** `U32` shifts (`shr`, `shl`, `shrn`, `shln`), masks
  and bitwise `and`, `or`, `xor`, `not` through their values; a law of
  `U32.mod` (already among Blend's candidates,
  `blend/docs/HubCandidates.md`); and laws of Base's `Array`, or a
  pointer to `lawful-arrays` and `bend-osdev-array`. Four packages now
  prove overlapping `U32` facts (`bend-mathlib`, `lawful-words`,
  `bend-kit-lemmas`, `bend-osdev-u32`), each stated a little
  differently: one shared set would serve every user.
- **`lawful-words`:** clearing the low bits as a value, `U32.and(a,
  U32.not(m))` for `m` standing for `2^k - 1` is `a - a mod 2^k`, the
  mask the kernel's references use.
- **`lawful-arrays`:** an array grown into a deeper one keeps its
  leaves as the new view's prefix (no Base function grows an array; a
  helper with that law would serve every heap that doubles); and laws
  for arrays of non-`Data` elements beyond `swap_full`, such as an array
  of pages (`kmem_paged.bend`).
- **Base:** none new. `Array.size` wraps to 0 at depth 32, as both
  array packages note, which `docs/BendIssues.md` already tracks as an
  array past depth 31.

## Recommendation

Adopt `lawful-arrays@0.1.0.1` and `lawful-words@0.1.0.1`, pinned by
version, in the laws of `cells-freeze.nested.host`: `.host.array` is
then their laws, and `.host.words` thin lemmas over `P.rd`, `P.wr` and
`KM.m_get`, `KM.m_set`, which pass straight to `Array.get` and
`Array.set`. The heap's growth, a node's base and the rungs above are
glam's. Whether glam's laws may rest on third-party packages is the
maintainer's to rule: they are machine-checked, `--verdict` included,
pinned by hash, and MIT; the cost is a dependency whose statements were
read by the agent, not by their author's human reviewer.
