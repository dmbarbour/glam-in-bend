# Inside data — 2026-11-10

The design round of the Cells plan's `cells-lazy-data`
([`../plans/Cells_2026-11-09.md`](../plans/Cells_2026-11-09.md), its item
8), held at the maintainer's word: "Design round now." (2026-11-10).
Effects wait on it (`bridge-effects.functions`), objects made at run time
too (`cells-objects.runtime`), and lazy members with them. This review
proposes; the maintainer decides; nothing here is recorded as decided.

## What fails today

Two programs, each stuck (`error: evaluating asm.result: stuck`):

```g
d = {f: \y -> y}
asm.result = d.f "Hello, World!"
```

```g
id y = y
d = {f: id}
asm.result = d.f "Hello, World!"
```

The dict is built at run time by the `tag` operator. In the first, its
payload is a bind node, no data, and the operator waits for data. In the
second, its payload is `id`'s leaf: demand stops wherever an application
(kind 2) or an operator (kind 9) faces a data node whose entry is a
handle (`may_need` in `spike/kdemand.blend`), and the core serves the
need by splicing `id`'s template where the operator wants data, so the
operator faces a bind. Objects escape this only because the core builds
their dicts as constants at load; a dict built at run time cannot hold
a function, not even a top-level one.

## Who needs it

- **Effects** (DistilledDesign, Effects): a request is a tagged dict
  holding a closure, `eff:(\api -> api.op)`; applying one to an argument
  builds another, `(eff:f) x = eff:(\api -> f api x)`; a handler's api
  is a dict of methods; a method object `{apply:f} x` is `f x`. A `do`
  block makes a continuation, a closure, at every bind.
- **Objects made at run time** (`cells-objects.runtime`): member
  templates applied to dicts that evaluation builds, a computed parent
  or `object_from_dict`'s; `self`, the instance, filled after its dict
  exists.
- **Lazy members**: a dict member computed only when read, and once:
  under `bounded-duplication` a small one may be computed twice, an
  expensive one may not.

## The question

Where a function's environment lives when the function enters data.
Three answers, each one of the maintainer's ideas or a record's:

**A. In the data: closures of templates and values.** A lambda in value
position, anywhere but the head of an application, is lambda lifted: its
body a closed template, its free variables passed first; the closure is
the template with those arguments collected, a partial application, data
like any other value. Applying a closure splices its template at the
applying level with its arguments, as `templates-spliced-at-level` does
for top-level functions. This is `functions-are-nets-with-arity` read
literally, a net and its remaining arity; the Rust bootstrap's
`FunctionCaptures`; the heap review's second reviewer's A3. It keeps
`lambdas-lower-to-nets`: the body is a net, lowered as now. A captured
variable must be data, and one bound to an unevaluated subnet is either
forced or held lazily by B's mechanism: the fork inside A.

**B. A reference into the live net.** Data holds a counted reference to
a subnet of its own net, a box: moved where it is used when the
reference is the last, copied by a fan at the box's level otherwise, and
evaluated in place when what it holds is wanted as data, its value then
kept for every reference. This is the maintainer's "reference-counted
'data' nodes as allocations within a net", and the live counterpart of
their `Data(Net)` capture. Used for functions too, a live subnet with
free wires travels inside level-free data, its levels adjusted where it
is used.

**C. Structures in the net.** Dicts, tags and lists as nodes, their
members live subnets; reading a member an interaction; laziness and
sharing by fans. The maintainer's nets as heaps, and NetData's
`netdata-structures`. A value leaving its net is frozen.

And a mixed answer, **A+B**: functions enter data as A's closures, while
a closure's lazy captures and lazy members are B's boxes. Every function
in data being a closure, a box only ever yields data, which no level
concerns: B's question of levels never arises.

## Weighed

| | A, captures forced | A+B | B | C |
|---|---|---|---|---|
| Captures lazy | no: an unused capture that fails or diverges changes the outcome | yes | yes | yes |
| Sharing | values shared as data | a box evaluated once for its net | functions shared by fans too | fans, optimal |
| An effect step | a continuation a small record; applying it splices a small template, a round trip to the core | as A | applying moves a live lambda, no copy when linear | an interaction or two |
| Levels | closed templates spliced at a level: item 2's experiment, which the ladder checks | boxes yield data: as A | a live subnet with free wires reached through data, adjusted at its use: untested | constructors with lazy fields are boxes to fans: not covered by NetPairing |
| Leaving a net | closures and values cross as data | a box stays with its net (below) | as A+B | frozen, sharing lost across |
| Kernel | handles as data | plus a box node and its rules: force, keep, count, erase, under laws | plus levels adjusted at use | node kinds for dicts, tags, lists, their rules, the builtins over them |
| Reuse | templates, splice, cells, Bend data as they are | as A | as A | today's data kept for final data only |

## Two consequences

- **Data that refers into a live net keeps that net alive.** Under A+B,
  B and C alike, a cell whose value holds a box cannot discard its net
  when its demand ends: the store holding only `Data` (the Cells plan's
  item 4) ends there. HeapModel's net kept in its cell returns, as the
  tree of heaps the maintainer sketched, a box named relative to the
  heap that holds it, with no identity global to the run. A value may
  instead be forced at the boundary, which is strictness, or a box moved
  when its reference is the last.
- **The cheapest step serves every answer.** A function's handle treated
  as data by operators and still needed by applications: `may_need`
  decides by the kinds that face each other, so telling an application
  from an operator for a function's handle is a small, local change, in
  Blend-generated demand code, under the kernel's laws. It makes
  `{f: id}` work, and object methods and a handler's api of top-level
  functions with it; not closures.

## Recommended, staged

1. **Handles as data** (`cells-lazy-data.handles`): common to every
   answer, and reversible.
2. **Closures of templates and values** (`cells-lazy-data.closures`):
   lambdas in value position lifted, their captures collected as data,
   applied by splice; a dict applied, `(eff:f) x` and `{apply:f} x`, by
   templates of the compiler's own. This commits the lowering: a lambda
   stays a bind in its net only at the head of an application.
3. **Lazy captures and lazy members** (`cells-lazy-data.boxes`), the
   fork: forced, or boxed. Recommended: boxes holding subnets that yield
   data, so that laziness is kept and levels never travel; this commits
   the kernel to a box node, and cells to keeping the nets their values
   refer into.
4. Then effects (`bridge-effects`) and objects made at run time
   (`cells-objects.runtime`) on these, the effect step measured first.

C stays open for streams, lists as nodes that a producer and a consumer
pipeline through, where it is strongest; B's levels can be tried once A+B
stands, if copying closures costs too much.

## Questions for the maintainer

1. May a lambda in value position become a closure of a template and its
   captures? Sharing reductions across its applications is given up
   already by `copy-reduced-function-nets`.
2. May a captured unevaluated local be forced, or must it stay lazy?
3. Does a cell whose value refers into its own net keep that net alive,
   as a tree of heaps, or must such a value be forced or moved at the
   boundary?
4. What alternatives do you have in mind?
