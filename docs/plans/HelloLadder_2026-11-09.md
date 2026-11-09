# The hello ladder: `.g` samples run end to end — 2026-11-09

**Drafted for the maintainer's review before building.** From the
direction review (`docs/reviews/Direction_2026-11-09.md`, F1 and
Recommendation 1) and the maintainer's answer to it: a part of `.g` is
hard to make usable, and the Rust bootstrap's hello samples built the
syntax up incrementally. So this plan climbs that ladder:
`samples/hello/` in the order of the syntax each sample introduces, each
rung a sample producing `Hello, World!` from its bytes through the real
layers, the parser, the lowering, the cells and the shell growing a rung
at a time. The kernel stays as it is (`lambdas-lower-to-nets`, the
maintainer's leaning on `spike-verdict`); this plan builds what sits
around it, and yields the first representative workloads.

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
   (`arch-shell-spike`, minimal, `pure-core-io-shell`). Texts are lists
   of `U32` code points for now (`packed-texts-and-binaries` later).
2. `ladder-lists` — `hello_list.g`, `hello_mixed.g`: list literals,
   number literals in decimal, `++`. Lists as a placeholder value, `++`
   as an operator; the first lowering of an expression to a net and its
   demand to a value (`spike-lowering`, begun).
3. `ladder-names` — `hello_names.g`, `hello_where.g`, `hello_let.g`:
   definitions used before they are written, `where`, `let` groups.
   Laziness across cells, local bindings lowered as sharing, a name used
   twice a copy fan: the first nets with fans from glam's own lowering,
   which is what NetPairing waited on (`spike-lowering`, and the question
   of `EvalSpike_2026-10-26.md:124-127`).
4. `ladder-lambda` — `hello_lambda.g`, `hello_lambda_sugar.g`: lambdas,
   application, a dict literal in leading-comma layout, field access.
   Functions as nets with arity, applied by copying
   (`functions-are-nets-with-arity`, `copy-reduced-function-nets`,
   `heap-apply` minimal); dicts as a placeholder value keyed by text.
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

- Where the lowering lives: a module of its own over a core term type,
  or straight from the parser's syntax to nets.
- Whether the first rungs' placeholder values (texts and lists as `U32`
  lists, dicts keyed by text) are a throwaway or the start of
  `arch-structures-spike`.
- How a rung's expected output is recorded: the Rust bootstrap's
  convention, or a `.out` beside each sample.
