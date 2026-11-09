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

The samples' own text decides the order, with one rule from the
maintainer (2026-11-09): plain data first, no thunks, since thunks and
promises are likely the hardest to integrate or prove. So the rungs
whose samples are one expression over data come first, and references
between top-level definitions, which want cells, come after them as a
rung of their own (`ladder-thunks`). Each rung names the forms it adds
and the layer work it carries; the earlier plans' steps it absorbs are
named, and marked there when a rung is built.

1. `ladder-text` — built 2026-11-09 — `hello_text.g`: `language g0`,
   `#` comments, a text literal, `asm.result`. Carries the whole skeleton
   at its smallest: a lexer over the file's bytes, one byte a step,
   structural on the list so that it needs no fuel, tokens with their
   line and column (the `.expect` files name lines; the layout reads
   columns), and a parser for the header and `path = "text"`
   declarations grouped by column 0 (the Architecture sketch's Front
   end); the definitions a plain list, no cell, `asm.result` found and
   lowered to a one-node net the kernel reduces on demand (`K.run_d`),
   its value read back as bytes; the core answering bytes or
   diagnostics, never printing; and the shell: `-f FILE [--count]`,
   `asm.result` written to `/dev/stdout` as bytes, diagnostics to stderr
   as `error at line N: message` with exit status 1
   (`arch-shell-spike`, minimal, `pure-core-io-shell`). A text is the
   kernel's list of code points in its first form, `V.VList`, a list of
   values in the net's table that copies share and erasure drops, as
   `netdata-table` and `netdata-structures` later decide (nodes, or a
   value in the table), bytes unpacked until `packed-texts-and-binaries`.
   Built as `glam/` (`lex`, `parse`, `lower`, `core`, `main`), importing
   the kernel as `../spike/kernel.bend`, which Bend allows; the layout
   stays an open question. Found: `V.VList` touched no kernel code (its
   matches end in `_`) and 20 exhaustive `Val` splits in the proofs, an
   arm each, added by a script; Bend's rules shaped every function
   (callees first, binders matched in order, a shrinking first argument,
   `+` on a value used twice, an affine `List<String>` from `IO.args`
   walked once), each refusal a minute; a native build takes 32 s. The
   five invalid samples about the header pass with their `.expect`
   lines (`missing_language`, `unknown_language_version`,
   `unknown_language_extension`, `bad_language_decl`,
   `non_ascii_without_utf8`); `bad_asm_result` waits on operators
   (`ladder-lists`). `scripts/ladder.py` runs `glam/ladder.txt` in the
   gate, the build kept by its inputs' hash; the gate's `bend files`
   section grew from 25 s to 43 s, `val.bend`'s change rechecking the
   kernel's closure, and the ladder's build costs 32 s whenever an
   input of `glam/main.bend` moves. AGENTS' rule that fenced `g` blocks
   in the docs must parse once a parser exists reaches, for now, only
   the forms the ladder has climbed; the docs check does not run it
   yet. Measured (store run 296, i7-6700): `hello_text.g` 0
   interactions, the root facing data at once, and 451,844 instructions
   for the process, a diagnostic run 393,650, so the assembly itself
   about 58,000. The kernel's own counts are untouched by `V.VList`:
   the spot check against main's run 288 is alike in every row within a
   few hundred instructions (run 297).
2. `ladder-lists` — `hello_list.g`, `hello_mixed.g`: list literals,
   number literals in decimal, `++`. The kernel's list type, `++` as an
   operator over it; the first lowering of an expression to a net and
   its demand to a value (`spike-lowering`, begun).
3. `ladder-locals` — `hello_where.g`, `hello_let.g`: `where` and `let`
   groups within one definition. Local bindings lowered as sharing in
   one net, a name used twice a copy fan: the first nets with fans from
   glam's own lowering, which is what NetPairing waited on
   (`spike-lowering`, and the question of
   `EvalSpike_2026-10-26.md:124-127`). No thunk: one expression, one
   net.
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
6. `ladder-thunks` — `hello_names.g`: definitions used before they are
   written, `asm.result` first and `hello` below it. The first cells:
   a namespace of lazy entries, one forced by another's demand
   (`heap-cells`, minimal), the point where the maintainer expects the
   hard part to begin, reached only once the data rungs stand.
7. `ladder-objects` — `hello_override.g`, `hello_object.g`,
   `hello_object_prior.g`, then the `hello_object_*.g` family:
   `:=` and `_name`, `object ... with`, `extends`, `self`. Objects as
   open fixpoints: the first `self` knot and the first recursive binding
   group through cells, `spike-fixpoints` made real on glam's own
   programs, costs measured as that step asked (deep mixin chains,
   repeated `extend`).
8. `ladder-imports` — `hello_import_as.g`, `hello_import_at.g`,
   `hello_import_as_extend.g`, `hello_import_binary.g` with `libs/`: the
   core's first requests, `Need{Read{path}}`, answered by the shell in
   logged order; a module as a mixin; a binary import as bytes.
9. `ladder-effects` — `hello_do.g`, `hello_applicative.g`, `hello_std.g`:
   `import 'std`, `.r`, `<-`, `->`, `!>`, `do` blocks; the freer monad
   lowered, `list.head` and `list.pure` as builtins. The first effect
   steps measured, against the Rust bootstrap's "376 K instructions a
   `.r ()` step".
10. `ladder-numbers` — `hello_arith.g`, `hello_floor.g`: `0x48`, `1_00`,
   `1.08e2`, `216 / 2`, `_0b1`, `std.math.floor 13.9`. Exact rationals
   enter here (`netdata-numbers`), last, since every earlier rung stands
   on `U32`.
11. `ladder-invalid` — `samples/invalid/` with their `.expect` lines:
    diagnostics by severity, line and substrings, from the parser first.
    Not a rung of its own in time: each rung above takes the invalid
    samples its forms make reachable.
12. `ladder-syntax` — `samples/syntax/`: the forms the hello samples do
    not reach (patterns, `match`, conditionals, layouts, recursive `do`),
    parsed, and lowered where a hello sample needs none.
13. `ladder-executable` — `samples/executable/hello_x86_64_linux/hello.g`
    (45 lines): direct-style assembly as effects to an ELF. The capstone,
    and the first assembly workload.
14. `ladder-measure` — at each rung built, the sample's instructions
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

- Where the front end's modules live: beside the kernel in `spike/`, or
  a directory of their own importing it (`../spike/kernel.bend`, which
  Bend allows).

Settled by this plan: every `hello/` sample produces `Hello, World!`
(`samples/README.md`), so the check asserts that literal for each built
rung's samples, with no `.out` files; the invalid samples' `.expect`
lines are the diagnostics' test. The maintainer, 2026-11-09: do not wait
for `netdata-review`; implement something to get started, plain data
first, so `ladder-text` takes the kernel's first list form and is redone
when NetData decides.

Answered by the maintainer, 2026-11-09:
- The lowering is the front end's, to net construction through
  `interaction_net`; the core has no lambda term type
  (`lambdas-lower-to-nets`).
- No placeholder values: the kernel's data types, built to be adopted by
  the final evaluator and iterated to maturity.
