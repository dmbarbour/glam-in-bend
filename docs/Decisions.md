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

- **rev** leads back in history: it names the commit a record's last
  substantive revision was made on top of (`HEAD` while editing).
  `git show <rev>:docs/decisions/<slug>.md` shows the version before, and
  `git log <rev>` the context it was decided in. Typo fixes leave it alone.
- **Revise in place.** A record states the current decision only; git keeps
  the old versions.
- **Delete what no longer holds**, with its index line, once nothing cites
  its slug. A successor may name what it replaced in a sentence.
- **maintainer** marks a decision the maintainer made or ratified; **agent**
  one an agent made in a plan or review, open to revision.
- Plans and reviews extract their durable decisions here, at the latest
  before they retire ([`plans/README.md`](plans/README.md)).

This index stays an index: a short paragraph per larger decision, then one
linked line per record. `scripts/check.sh` checks every record's header and
rev, that this index lists it, and that no record's body moves in here.

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

- [`shadowing-is-an-error`](decisions/shadowing-is-an-error.md): within a
  file or object, a bare name is a local or a global, never both.
- [`keywords-reserved-freely`](decisions/keywords-reserved-freely.md):
  until glam has users, reserve any keyword a form needs.
- [`prior-update-disabled`](decisions/prior-update-disabled.md): `::=` is
  disabled until it is redesigned.
- [`handlers-assumed-lawful`](decisions/handlers-assumed-lawful.md):
  effects are described under handlers assumed, not required, to obey the
  monad laws.

## Language, from the Rust bootstrap

Language decisions made during the Rust bootstrap, carried over where our
docs cite them. The rest remain in the Rust decision log
(github.com/dmbarbour/glam, `docs/Decisions.md` at 21912fc9) until needed.

- [`dict-empty-is-a-value`](decisions/dict-empty-is-a-value.md): `{}` is a
  value; reading what is undefined is an error; definedness is asked.
- [`only-comparables-compare`](decisions/only-comparables-compare.md):
  comparing anything but numbers, lists and dicts of them is an error.
- [`dict-literals-introduce-in-order`](decisions/dict-literals-introduce-in-order.md):
  a dict literal introduces members in written order; union is shallow.
- [`tail-forms-end-at-separators`](decisions/tail-forms-end-at-separators.md):
  a tail form runs to the end of its region, which separator keywords end.
- [`nested-arrows-share-an-arms-line`](decisions/nested-arrows-share-an-arms-line.md):
  a nested match's arrows may share its arm's line.
- [`aliases-and-locals-are-body-declarations`](decisions/aliases-and-locals-are-body-declarations.md):
  `alias` and `let` are declarations inside bodies, not header clauses.
- [`lone-do-statements-run-as-effects`](decisions/lone-do-statements-run-as-effects.md):
  a lone `do` statement lowers as `.r () >>= \_ -> X`.

## Values and representation

How glam values sit on Bend 2's immutable, reference-counted data, and
where the shared lazy state that Bend cannot hold goes.

- [`split-heap`](decisions/split-heap.md): ground data is Bend data;
  everything holding lazy state lives in our store, split for parallelism.
- [`store-pages`](decisions/store-pages.md): the store is equal pages of
  cells that never move; a handle is one `U32`, page and slot.
- [`rounds-of-coarse-work`](decisions/rounds-of-coarse-work.md): a
  coordinator runs coarse work on workers in rounds; fairness comes across
  rounds.
- [`store-collection`](decisions/store-collection.md): the store's own
  collector, stop-the-world first, then concurrent with an SATB barrier.
- [`net-nodes-double`](decisions/net-nodes-double.md): a net holds its
  nodes in one flat array of its own, doubled when full; the heap holds nets
  as values, each reduced by one worker at a time.
- [`net-demand-whnf`](decisions/net-demand-whnf.md): a forced net reduces
  to weak head normal form at its root, erasing eagerly; other strategies
  only where they terminate.
- [`copy-reduced-function-nets`](decisions/copy-reduced-function-nets.md):
  a function's net reduces locally, then each application copies it
  whole; cursors wait for measurements.
- [`diagnostic-order-follows-schedule`](decisions/diagnostic-order-follows-schedule.md):
  deterministic scheduling decides the order diagnostics are observed in.
- [`functions-are-nets-with-arity`](decisions/functions-are-nets-with-arity.md):
  a function is a net and its remaining arity; copies share its reductions.
- [`packed-texts-and-binaries`](decisions/packed-texts-and-binaries.md):
  texts and binaries are lists, stored packed in rope leaves.
- [`intern-hot-values`](decisions/intern-hot-values.md): widely shared
  values are interned, keeping Bend's reference counts in bounds.

## Reflection

- [`reflection-api-per-runtime`](decisions/reflection-api-per-runtime.md):
  beyond the standard effects, reflection APIs may differ per runtime.
- [`reflection-key-order-free`](decisions/reflection-key-order-free.md):
  reflection may list dict keys in any order.
