# A serve's write set: the splice's writes listed, the joins' by region

`serve-write-sets-hybrid` · maintainer · rev 075b251

**Context.** The law of `cells-freeze.nested.host.serve` must say which
words of the host a serve may write, so that `.host.path` can show a
walk's kept path untouched. The join laws say it by regions: no member's
word 3, the joined cursors' own words, the head, the faced ports' link
words. At the maintainer's request the agent sketched the other form,
the exact list of words a step writes, and proved it for a join
(`docs/reviews/JoinLaws_2026-11-14.md`, question 3): a frame law over
an exact list needs no premise on the ring and composes by appending
lists, but the list is computed by the code's own walks, so it shares
their faults, and it moves the ring's reasoning to every law that uses
it. It was false of a join unlinking a cursor twice, which the region
law allows, and true of a walk following the wrong word, which the
region law refutes.

**Decision.** The maintainer (2026-11-14): "We'll go with your hybrid
recommendation on D3." A serve's writes are stated in two forms by what
decides them: the splice's writes, fixed by the template and the fresh
nodes it is given, as an exact list of words; the joins' and the
cursors', which a walk round the ring decides, by regions. The serve's
own law is stated in regions, which `.host.path` reads.

**Consequences.**
- The splice gets a frame law over an exact list (its fresh nodes'
  words and the link words its crossings write), composed by appending
  and with no premise on the ring.
- The join laws keep their regions; the claims that a walk stopped where
  it should belong to the ring's laws (`cells-freeze.nested.host.ring.exact`).
- A list computed by the code's own reads claims nothing of those reads
  (`docs/Proving.md`, "A specification sharing the decisions"): where a
  list is used, what decides it is listed among the law's missing pieces.

**Rule lives in:** `docs/plans/Cells_2026-11-09.md`, `cells-freeze.nested.host.serve`.
