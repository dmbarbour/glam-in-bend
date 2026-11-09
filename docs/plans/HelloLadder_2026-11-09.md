# The hello ladder: `.g` samples run end to end — 2026-11-09

**Drafted for the maintainer's review before building.** From the
direction review (`docs/reviews/Direction_2026-11-09.md`, F1 and
Recommendation 1) and the maintainer's answer to it: a part of `.g` is
hard to make usable, and the Rust bootstrap's hello samples built the
syntax up incrementally. So this plan climbs that ladder:
`samples/hello/` in the order of the syntax each sample introduces, each
rung a sample producing `Hello, World!` from its bytes through the real
layers, the parser, the lowering, the cells and the shell growing a rung
at a time. The kernel is the evaluator (`lambdas-lower-to-nets`, the
maintainer's leaning on `spike-verdict`): the core has no lambda, and
the `.g` front end lowers lambdas, applications and bindings to the net
construction `interaction_net` gives every user. This plan builds the
front end and what sits around the kernel, and yields the first
representative workloads. Its data types are the kernel's: the
maintainer (2026-11-09) wants kernel data types that the final evaluator
adopts directly, a matured model of lists, dicts and numbers not
throwaway, though maturing it may throw a lot away. So no rung takes a
placeholder value beside the kernel; each takes the kernel's first form
of the type it needs, from NetData's steps as they are decided
(`netdata-table`, `netdata-structures`, `netdata-numbers`), expecting to
redo it.

## What each rung forces into being

The samples' own text decides the order. Each rung names the forms it
adds and the layer work it carries; the earlier plans' steps it absorbs
are named, and marked there when a rung is built.

1. `ladder-text` — `hello_text.g`: `language g0`, `#` comments, a text
   literal, `asm.result`. Carries the whole skeleton at its smallest: a
   fuel-driven lexer over packed bytes and a parser for declarations
   (the Architecture sketch's Front end), a namespace of lazy cells, one
   forced to a value (`heap-cells`, minimal: a cell made, forced, read),
   the core answering `Done{bytes}`, and the shell: read the file named
   on the command line, write `asm.result` to stdout as binary
   (`arch-shell-spike`, minimal, `pure-core-io-shell`). A text is the
   kernel's list of code points in its first form, as `netdata-table`
   and `netdata-structures` decide it (nodes, or a value in the net's
   table), packed later (`packed-texts-and-binaries`).
2. `ladder-lists` — `hello_list.g`, `hello_mixed.g`: list literals,
   number literals in decimal, `++`. The kernel's list type, `++` as an
   operator over it; the first lowering of an expression to a net and
   its demand to a value (`spike-lowering`, begun).
3. `ladder-names` — `hello_names.g`, `hello_where.g`, `hello_let.g`:
   definitions used before they are written, `where`, `let` groups.
   Laziness across cells, local bindings lowered as sharing, a name used
   twice a copy fan: the first nets with fans from glam's own lowering,
   which is what NetPairing waited on (`spike-lowering`, and the question
   of `EvalSpike_2026-10-26.md:124-127`).
4. `ladder-lambda` — `hello_lambda.g`, `hello_lambda_sugar.g`: lambdas,
   application, a dict literal in leading-comma layout, field access.
   The front end lowers a lambda to `.bind`, `.copy` and `.wire` as a
   user's `interaction_net` would, never to a core term
   (`lambdas-lower-to-nets`); functions as nets with arity, applied by
   copying (`functions-are-nets-with-arity`,
   `copy-reduced-function-nets`, `heap-apply` minimal); the kernel's
   dict type in its first form.
5. `ladder-dicts` — `hello_dict.g`, `hello_tagged.g`, `hello_tuple.g`:
   `(tag:)` sections, `path:V` members, `.["key"]` indexing, tuples.
   Dict construction and reading as operators or as lowering.
6. `ladder-objects` — `hello_override.g`, `hello_object.g`,
   `hello_object_prior.g`, then the `hello_object_*.g` family:
   `:=` and `_name`, `object ... with`, `extends`, `self`. Objects as
   open fixpoints: the first `self` knot and the first recursive binding
   group through cells, `spike-fixpoints` made real on glam's own
   programs, costs measured as that step asked (deep mixin chains,
   repeated `extend`).
7. `ladder-imports` — `hello_import_as.g`, `hello_import_at.g`,
   `hello_import_as_extend.g`, `hello_import_binary.g` with `libs/`: the
   core's first requests, `Need{Read{path}}`, answered by the shell in
   logged order; a module as a mixin; a binary import as bytes.
8. `ladder-effects` — `hello_do.g`, `hello_applicative.g`, `hello_std.g`:
   `import 'std`, `.r`, `<-`, `->`, `!>`, `do` blocks; the freer monad
   lowered, `list.head` and `list.pure` as builtins. The first effect
   steps measured, against the Rust bootstrap's "376 K instructions a
   `.r ()` step".
9. `ladder-numbers` — `hello_arith.g`, `hello_floor.g`: `0x48`, `1_00`,
   `1.08e2`, `216 / 2`, `_0b1`, `std.math.floor 13.9`. Exact rationals
   enter here (`netdata-numbers`), last, since every earlier rung stands
   on `U32`.
10. `ladder-invalid` — `samples/invalid/` with their `.expect` lines:
    diagnostics by severity, line and substrings, from the parser first.
    Not a rung of its own in time: each rung above takes the invalid
    samples its forms make reachable.
11. `ladder-syntax` — `samples/syntax/`: the forms the hello samples do
    not reach (patterns, `match`, conditionals, layouts, recursive `do`),
    parsed, and lowered where a hello sample needs none.
12. `ladder-executable` — `samples/executable/hello_x86_64_linux/hello.g`
    (45 lines): direct-style assembly as effects to an ELF. The capstone,
    and the first assembly workload.
13. `ladder-measure` — at each rung built, the sample's instructions
    and interactions into the store with the rung's name, so that the
    kernel's workloads become glam programs, and a performance review of
    what the rungs found, as the maintainer prefers: features first, the
    review after, anything past 10% looked at as it appears.

## Acceptance

A rung is built when its samples write their expected bytes, every
earlier rung still does, and the gate passes; `scripts/check.sh` gains a
section running the rungs built so far. No rung is built by special
casing a sample: the parser accepts the forms, the lowering lowers them.

## Deferred, on purpose

Collection across cells (`spike-lazy-data`), rounds and parallelism
(`spike-page-rounds`, `spike-deep-parallelism`), frozen nets and cursors
(`heap-freeze`, `spike-cursors`), ropes and balanced dicts
(`arch-structures-spike`), interning, the manifest and remotes, the IDE.
Each comes after the ladder reaches the forms that need it, with a
workload from the rungs to measure it on.

## Open questions

- How a rung's expected output is recorded: the Rust bootstrap's
  convention, or a `.out` beside each sample.
- Whether `ladder-text` and `ladder-lists` wait for `netdata-review`, or
  take the kernel's first list form now and are redone when NetData
  decides (this plan's reading of "maturing may throw a lot away").

Answered by the maintainer, 2026-11-09:
- The lowering is the front end's, to net construction through
  `interaction_net`; the core has no lambda term type
  (`lambdas-lower-to-nets`).
- No placeholder values: the kernel's data types, built to be adopted by
  the final evaluator and iterated to maturity.
