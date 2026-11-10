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
- [`generated-sources`](decisions/generated-sources.md): code needed in
  several variants is a template where Bend's templates serve, else
  generated into files of its own, by Bend programs, and checked current;
  no external macro processor (one of our own, in Bend, may come), no
  script editing sources.
- [`vendored-sources`](decisions/vendored-sources.md): third-party code
  not on the hub is copied under `vendor/`, a subdirectory per source with
  its license and origin, indexed.

Blend, the preprocessor of static objects for Bend that `generated-sources`
allows, is a repository of its own, a submodule here, and keeps its
records with it: [`blend/docs/Decisions.md`](../blend/docs/Decisions.md)
(`blend-own-repository`).

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
- [`net-obvious-errors`](decisions/net-obvious-errors.md): net
  construction refuses errors it recognizes cheaply (disconnected
  subnets, vicious circles), and restricts nothing it cannot.
- [`net-scoped-arguments`](decisions/net-scoped-arguments.md): a
  function's argument is used only within its body, checked as a net is
  built; demand reports a variable demanded outside it.
- [`net-void-demanded`](decisions/net-void-demanded.md): demand finding
  a void, nothing supplied as a value, reports that as an outcome of its
  own.
- [`builtin-imports-compiler-local`](decisions/builtin-imports-compiler-local.md):
  built-in imports such as `import 'std` are the compiler's, presented as
  module imports, and may come before modules are objects.

## Language, from the Rust bootstrap

Language decisions made during the Rust bootstrap, carried over where our
docs cite them. The rest remain in the Rust decision log
(github.com/dmbarbour/glam, `docs/Decisions.md` at 21912fc9) until needed.

- [`net-error-values`](decisions/net-error-values.md): an error is a data
  value carrying its diagnostic; builtins and application pass it on,
  and builtins answer one for arguments they have no case for.
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

- [`lambdas-lower-to-nets`](decisions/lambdas-lower-to-nets.md): the
  lambda calculus is evaluated by lowering to the kernel's nets; a lazy
  machine over thunks is not the toplevel's evaluator.
- [`lowering-uses-levels`](decisions/lowering-uses-levels.md): glam's
  lowering pairs its fans by GAL levels from the start, a local's value
  a box as an application's argument is.
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
- [`net-capacity`](decisions/net-capacity.md): a net holds at most 2^28
  nodes, so a reference stays below 2^30.
- [`static-links-count-as-nodes`](decisions/static-links-count-as-nodes.md):
  a static link counts as the node it stands for, in every count and
  profile; its value means only what the layout gives it.
- [`erasure-at-write`](decisions/erasure-at-write.md): a static eraser at
  an auxiliary port acts where it is written, never tested on a rewrite's
  path, which costs every rewrite in Bend.
- [`net-demand-whnf`](decisions/net-demand-whnf.md): a forced net reduces
  to weak head normal form at its root, only the pairs on the way; other
  strategies only where they terminate.
- [`machine-limits-not-errors`](decisions/machine-limits-not-errors.md):
  running out of memory is an error of the runtime, no state of the net,
  never stuck, and never cached as a value.
- [`copy-reduced-function-nets`](decisions/copy-reduced-function-nets.md):
  a function's net is copied as a live template, by batch
  materialization. Its finished parts are frozen and copied whole; its
  unfinished ones stay in the source, behind cursors, and reduce once
  for every copy. Reducing first is an optimization.
- [`fuse-control-runs`](decisions/fuse-control-runs.md): controls fuse
  only into runs of raises, peeled where a facing control meets them at
  their index; other fusion waits on a safety criterion.
- [`header-kind-byte`](decisions/header-kind-byte.md): a node's header is
  a 6-bit kind, two bits of form and a 24-bit field.
- [`fusions-as-components`](decisions/fusions-as-components.md): a fused
  op behaves as its components, stuck where they are, observing no data
  value, and a law proves it; at lowering too.
- [`operator-nodes`](decisions/operator-nodes.md): an application
  meeting a builtin becomes an operator holding its opcode and arity in
  the header, its accumulator in its word, which on its argument writes
  the result.
- [`diagnostic-order-follows-schedule`](decisions/diagnostic-order-follows-schedule.md):
  deterministic scheduling decides the order diagnostics are observed in.
- [`functions-are-nets-with-arity`](decisions/functions-are-nets-with-arity.md):
  a function is a net and its remaining arity; copies share its reductions.
- [`templates-spliced-at-level`](decisions/templates-spliced-at-level.md):
  a top-level function is a closed template, a copy spliced where demand
  applies it, raised to the application's level; an experiment.
- [`object-members-as-templates`](decisions/object-members-as-templates.md):
  a member is a template of `self` and the whole prior dict, applied per
  instance to two constant dicts; the instance a dict of member handles.
- [`unused-definitions-checked`](decisions/unused-definitions-checked.md):
  errors in definitions nothing uses may fail the assembly, while module
  loading stays lazy.
- [`bounded-duplication`](decisions/bounded-duplication.md): a small,
  local lazy computation may be evaluated twice; an emission to
  reflection happens at most once, and expensive work stays shared.
- [`early-evaluation-optimization`](decisions/early-evaluation-optimization.md):
  evaluation ahead of demand is an optimization only; fuel stops it
  before it can diverge, and a reflection task blocks it; what it
  leaves stays lazy.
- [`packed-texts-and-binaries`](decisions/packed-texts-and-binaries.md):
  texts and binaries are lists, stored packed in rope leaves.
- [`intern-hot-values`](decisions/intern-hot-values.md): widely shared
  values are interned, keeping Bend's reference counts in bounds.

## Diagnostics

- [`diagnostic-wording-ours`](decisions/diagnostic-wording-ours.md):
  messages are worded for use and improved at will, the samples'
  `.expect` substrings changing with them.

## Reflection

- [`reflection-api-per-runtime`](decisions/reflection-api-per-runtime.md):
  beyond the standard effects, reflection APIs may differ per runtime.
- [`reflection-key-order-free`](decisions/reflection-key-order-free.md):
  reflection may list dict keys in any order.
