# Decisions

Why glam-in-bend is the way it is. Each decision is a small record in
[`decisions/`](decisions/); this index groups the records under the larger
decisions they belong to. Standing docs keep the rules themselves (the
design docs, `LAWS.bend`): a record says why, and names where its rule
lives.

## Records

A record is `decisions/<slug>.md`. Its slug is its stable name: cite it as
`` `slug` `` in docs, plans, reviews, code comments and commits.

    # <Descriptive title>

    `<slug>` · maintainer|agent · rev <short hash>

    **Context.** …
    **Decision.** …
    **Consequences.** …
    **Rule lives in:** <doc and section>   (omit if none)

- **rev** names the commit a record's last substantive revision was made
  on top of (`HEAD` while editing, since a commit cannot name itself).
  `git log <hash>.. -- docs/decisions/<slug>.md` finds the revision. Typo
  fixes leave it alone.
- **Revise in place.** A record states the current decision only; git keeps
  the old versions.
- **Delete what no longer holds**, with its index line, once nothing cites
  its slug. A successor may name what it replaced in a sentence.
- **maintainer** marks a decision the maintainer made or ratified; **agent**
  one an agent made in a plan or review, open to revision.
- Plans and reviews extract their durable decisions here, at the latest
  before they retire ([`plans/README.md`](plans/README.md)).

`scripts/check.sh` checks every record's header and rev, and that this
index lists it.

## Host: Bend 2

glam is reimplemented in Bend 2, a pure, affine, termination-checked
language with laws, instead of continuing the Rust bootstrap. The assembler
is a deterministic interpreter whose only contact with the world is a thin
IO shell.

- [`host-bend2`](decisions/host-bend2.md): Bend 2 as the host; the Rust
  bootstrap is reference, not specification.
- [`pure-core-io-shell`](decisions/pure-core-io-shell.md): a pure core
  answering results or requests, behind a thin IO shell.

## Language

Surface and semantic rules settled for this implementation.

- [`shadowing-is-an-error`](decisions/shadowing-is-an-error.md): reusing a
  name a file defines or selects is an error, not a warning.
- [`keywords-reserved-freely`](decisions/keywords-reserved-freely.md):
  until glam has users, reserve any keyword a form needs.
- [`prior-update-disabled`](decisions/prior-update-disabled.md): `::=` is
  disabled until it is redesigned.
- [`handlers-assumed-lawful`](decisions/handlers-assumed-lawful.md):
  effects are described under handlers assumed, not required, to obey the
  monad laws.

## Reflection

- [`reflection-api-per-runtime`](decisions/reflection-api-per-runtime.md):
  beyond the standard effects, reflection APIs may differ per runtime.
