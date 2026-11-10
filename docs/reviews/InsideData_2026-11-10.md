# Inside data — 2026-11-10

The design round of the Cells plan's `cells-lazy-data`
([`../plans/Cells_2026-11-09.md`](../plans/Cells_2026-11-09.md), its item
8), held at the maintainer's word: "Design round now." (2026-11-10).
Effects wait on it (`bridge-effects.functions`), as do objects made at
run time (`cells-objects.runtime`) and lazy members with them.

The first draft (1bf6dc1) recommended closures of templates and
captured values, and asked four questions. The maintainer's answers
showed that those closures lose the work of partial applications (F1).
A revision (93243b7) followed, with four more questions. A second round
of answers set the direction: a function in data is a live template,
the maintainer's batch materialization. A third round dropped whole
copies first and favoured linear moves within a net. The direction is
recorded in `copy-reduced-function-nets`, and the answer on early
evaluation in `early-evaluation-optimization`. The steps are in the
Cells plan. The rest proposes, and the maintainer decides. The review
stays open until the spike of `cells-lazy-data.cursors` settles
cursors against ports.

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

The dict is built at run time by the `tag` operator. In the first
program, its payload is a bind node, not data, and the operator waits
for data. In the second, its payload is `id`'s leaf. Demand stops
wherever an application (kind 2) or an operator (kind 9) faces a data
node whose entry is a handle (`may_need`, in `spike/kdemand.blend`).
The core serves the need by splicing `id`'s template where the operator
wants data, so the operator now faces a bind. Objects escape this only
because the core builds their dicts as constants at load. A dict built
at run time cannot hold a function, not even a top-level one.

## Who needs it

- **Effects** (DistilledDesign, Effects). A request is a tagged dict
  holding a closure, `eff:(\api -> api.op)`. Applying one to an argument
  builds another, `(eff:f) x = eff:(\api -> f api x)`. A handler's api
  is a dict of methods, and a method object `{apply:f} x` is `f x`. A
  `do` block makes a continuation, a closure, at every bind.
- **Objects made at run time** (`cells-objects.runtime`). Member
  templates are applied to dicts that evaluation builds, from a
  computed parent or from `object_from_dict`. `self`, the instance, is
  filled after its dict exists.
- **Lazy members.** A dict member is computed only when read, and only
  once. Under `bounded-duplication` a small member may be computed
  twice; an expensive one may not.

## The maintainer's answers

### First round (2026-11-10)

- **Q1.** The draft asked whether a lambda in value position may become
  a closure of a template and its captures, claiming that sharing was
  "given up already by `copy-reduced-function-nets`". The answer: "Hold
  up. I'm not willing to give up on sharing work for partial
  applications. How are you envisioning "copy a function's net"?
  Because I'm seeing it as either copying a frozen net (a template) as
  data, in which case there is no work to share (precondition of
  freeze), or copying a live net using a fan, in which case we cannot
  copy active pairs within the function because they don't have
  principal ports facing our fan. Or am I misunderstanding you?"
- **Q2.** The draft asked whether a captured local not yet evaluated
  may be forced. The answer: "We can evaluate early as an optimization.
  Divergence or reflection tasks would be blockers." It is recorded as
  `early-evaluation-optimization`.
- **Q3.** The draft asked whether a cell whose value refers into its
  own net keeps that net alive. The answer: "Not sure I understand the
  question. In context of GC, a cell cannot keep itself alive. If
  you're speaking of frozen vs live nets, we'd need to handle this
  properly as part of any template representation."
- **Q4** asked for the maintainer's alternatives. It was answered in
  the second round: batch materialization.

### Second round (2026-11-10)

The revision wrote that "a frozen net can hold leftover work that fuel
or a reflection task stopped", and it asked four questions. The
maintainer answered:

"By my understanding, a net simply would not freeze if or insofar as
there's any residue.

The cursors-based approach in the Rust implementation was essentially
an approach to copying live nets while keeping the original separated.
IIUC, your Q1 is suggesting we freeze parts of the net that won't
change while providing cursors to the unprocessed items. This was the
intended direction, which I had described as batch materialization
(iirc).

We could call that a live template, or a template with live parts, if
approaching it from a certain perspective.

Not sure I grasp the `cells-need` question. But we don't necessarily
need to eagerly evaluate functions if we don't need to fully freeze
them."

The revision's questions were answered as follows:
- Its first, on the residue, was answered by batch materialization.
- Its third, on templates holding live parts, was answered by the live
  template.
- Its fourth, on needs, was answered by the last sentence, as F4 below
  explains.
- Its second, on what to do within a net, is restated below.

### Third round (2026-11-10)

The second revision asked whether whole copies come first, and whether
data within a net holds cursors or ports. The maintainer answered:

"We can certainly relax the "put whole copies first". That was a
position you favored as a quick getting started thing. If it isn't
working out, drop it. It should have been recorded as an experimental
direction, not an ADR.

Q2. I like the idea of linear moves. Reference counting is awkward
with recursive structures. But when we know a function or cell is
never shared, we could feasibly move it. This would reduce a count to a
lightweight boolean flag."

- **Whole copies first** are dropped. `copy-reduced-function-nets`
  says so, and `cells-freeze` builds live templates.
- **Within a net,** the agent reads the answer as cursors, with a
  use through a cursor known unshared moving what it names. A flag, not
  a count, records the sharing; ports remain the alternative should the
  spike fail. The maintainer was asked to confirm this reading.

## Findings

**F1. Option A, as first drafted, redoes the work of a partial
application.** The draft said: "A lambda in value position ... is lambda
lifted: its body a closed template, its free variables passed first;
the closure is the template with those arguments collected ...
Applying a closure splices its template at the applying level with its
arguments."

- **What A did.** That template is frozen when the program is
  compiled, before any argument exists. Applying the closure copies it
  and applies the captures afresh, so every application redoes the
  work that needs only the captures or the earlier arguments.
- **The maintainer's readings keep that work.** A net is frozen only
  after it is reduced, so the source has no work left for its copies
  to share. A fan copying a live net waits at each active pair: the
  pair stays in the source, and the fan copies only what it yields. A
  is neither reading.
- **A is the model a record rejected.** `functions-are-nets-with-arity`
  rejects "a closed template plus captured values, instantiated afresh
  at each application. That loses work". The draft cited that record
  in favour of A, which misread it.
- **The draft misread `copy-reduced-function-nets` the same way.** It
  read "work that needs the argument is done again in each copy" (the
  record's wording then) as giving up sharing. That sentence is about
  each application's own work, which no copy can share; the partial
  application's work was kept.
- **Full laziness alone falls short too.** The second reviewer's A3
  first floated maximal free expressions out of lambdas (full laziness)
  and made every capture a heap object. A dropped the float. Even with
  it, some work is redone: in `(eff:f) x = eff:(\api -> f api x)`, work
  in `f` that needs `x` but not `api` appears only once `f` is applied.
  The float cannot see it, while a live template's source reduces it
  once.

Verdict: A is withdrawn as the way a function is held in data. A
template with its captures survives in two roles. It is a recipe, the
thing a function's net is built from. It is also a fast path where
nothing in the net can reduce before the last argument: the
maintainer's "analysis to determine how many values are required before
partial evaluation begins" (2026-11-09).

**F2. The build already redoes such work, in two places.** Two families
were counted with `--count` at 1, 2, 4 and 8 uses, under templates and
linked (`--link`). They are run 312 of the analysis store, beside three
families that stay flat. The first family is closed work in a template:

```g
c2 h x = h (h x)
id x = x
f s = s ++ c2 c2 c2 id "!"
asm.result = f (f "Hello, World")
```

The second is a partial application in a root cell. Its uses are
`use (use ...)`:

```g
c2 h x = h (h x)
id x = x
k x y = x
f a = k (c2 c2 c2 id a)
g = f id
use x = g id x
asm.result = use (use "Hello, World")
```

| Interactions at uses | 1 | 2 | 4 | 8 |
|---|---|---|---|---|
| closed work, templates | 147 | 294 | 588 | 1176 |
| closed work, linked | 246 | 255 | 293 | 369 |
| partial application in a cell, templates | 151 | 300 | 598 | 1194 |
| partial application in a cell, linked | 305 | 310 | 332 | 376 |

A splice is not an interaction, so the template rows understate the
cost. They also make 8 and 12 splices a use, each a copy.

- **Closed work in a template.** `f`'s body holds `c2 c2 c2 id "!"`,
  which needs no argument. Each splice copies the template whole, as
  lowered, and does that work again: exactly 147 interactions and 8
  splices a use. `copy-reduced-function-nets` would either reduce the
  template first or leave that work in its source behind cursors, and
  neither is built. Linked, `f` is one subnet shared by fans, so the
  work is done once.
- **A partial application in a root cell.** `g`'s outcome is a
  function, so `cells-data.root`'s stopgap splices its recipe at each
  use: about 149 interactions and 12 splices a use.
- **What stays flat.** The same partial application made inside one
  net stays flat under templates (151, 156 and 174 at 1, 2 and 4
  uses), because fans share it. So does `g` named only by
  `asm.result`, which links it, and a data-valued cell, which is forced
  once and kept.

The ladder's differential run compares bytes, so it could see neither
loss.

Verdict: both losses break rulings made before the bridge, and every
path below needs them fixed. They become steps under `cells-freeze` in
the Cells plan, with a check in the ladder that counts. The record
`templates-spliced-at-level` claimed its copies were made "as
`copy-reduced-function-nets` copies a function's net". That claim is
corrected in place.

**F3. Unfinished work stays live, in the source.** The revision said
that a frozen net may hold leftover work that fuel or a reflection
task stopped. The maintainer corrected this: "a net simply would not
freeze if or insofar as there's any residue".

Such work cannot be copied either. Copies would redo expensive work, or
emit a reflection task more than once, which `bounded-duplication`
forbids. The sharp case:

    f a = let t = anno refl:(log a) in \y -> ... t ...
    g = f "x"          -- g applied many times

Verdict: answered by the second round. The parts of a net that won't
change are frozen and copied in a batch. Each unprocessed item stays in
the source, where every copy reaches it by a cursor, and it reduces
there once for every copy. That is the maintainer's batch
materialization, a live template (`copy-reduced-function-nets`, revised
in place).

So `t` is reduced once in `g`'s source and emitted at most once. A
pending pair in the source reduces there even when its wires reach the
parameter, which is a free wire in the source. Only what waits on the
parameter's data is done per copy, and the copy takes it as finished
structure. Reducing before copying is an optimization, which the
maintainer's "we don't necessarily need to eagerly evaluate functions
if we don't need to fully freeze them" makes optional.

**F4. `cells-freeze`'s "needs left alone".** A need is the kernel's stop
where an application or an operator faces a leaf: a data node holding
the handle of a template or a root cell. The core serves it by splicing
the template or forcing the cell. F2's closed work lies behind needs:
`c2` is a leaf, so `c2 c2` is a need. The question was whether
`cells-freeze` serves needs before freezing.

- **Under whole copies,** a need left alone is copied with the net, and
  every copy serves it again: F2's loss.
- **Under live templates,** a need left alone is an unprocessed item
  behind a cursor. It is served once, in the source.

Closed work in a template also has a cheaper fix while templates are
copied whole: lift each closed subexpression of a template into a root
cell at lowering (the second reviewer's CAF point, HeapFable 3b).

Verdict: answered by the second round's last sentence. With live
templates the step's "needs left alone" stands. Serving needs first
matters only if whole copies come first, which is the first question
below.

## Where the question stands

A function is "a value referencing a net (frozen or not) and remaining
arity" (the maintainer, 2026-10-28; `functions-are-nets-with-arity`).
After the second round, a function held in data is a live template.
Its finished parts are frozen, and its unprocessed items are reached by
cursors in its source, where they reduce once for every copy. What
remains open is where the source lies and how data refers to it.

- **At a boundary.** When a cell's task ends, the cell's net becomes the
  source, live while a cursor reaches it. Its value is a live template.
  This is `cells-freeze`, the fix for F2. The boundary step
  `cells-lazy-data.boundary` has converged with it: it is the same step
  applied to data with unfinished parts.
- **Within a net: ports or cursors.**
  - **Ports.** The revision proposed ports: a data node's value with
    holes, each a port wired to a live subnet, shared by fans as
    everything else in the net is, so that a linear application is a
    beta with no copy.
  - **Cursors into the same net.** A cursor into the same net does what
    a port does. Data holds a reference instead of a wire, and the net
    is its own source. This uses the one mechanism the boundary uses,
    and needs no data node with a varying number of ports.
  - **The cost to watch.** Under cursors, a linear application copies
    the finished parts, unless the last cursor moves them instead. That
    needs counts, which would be one more form of the data table's
    discipline. Today that discipline is linear: "an entry has one
    owner, is handed on when its owner's value moves, duplicated when it
    is copied, freed when it is dropped" (`spike/kprim.bend`).
- **Freeze at entry is gone.** The revision's alternative froze a
  function wherever it entered data, after reducing it. Under live
  templates, nothing need be reduced on entry, and a cursor into the
  same net is what remains of that option.

## Weighed, within a net

| | Ports | Cursors into the same net |
|---|---|---|
| Sharing | fans: what reduced is copied, the rest stays shared | the source reduces each item once for every copy |
| Laziness | kept: a hole is reduced only when needed | kept: an item is reduced only when a copy needs it |
| An effect step | a request built in a few interactions; a continuation applied by a beta, no copy when linear | the continuation's finished parts copied, unless the last cursor moves them (counts) |
| Captures | stay wires | stay in the source, reached by cursors |
| Kernel | a data node with ports, and its rules with fans, lifts, erasers and operators, under laws | anchors in a live net, demand from an anchor, materialization: the mechanism the boundary needs anyway |
| Levels | a port holding a function, adjusted at its use: untested | a copy materialized at the applying level, as templates are spliced |
| Builtins | those reading a hole need it; the rest pass it on | those reading a cursor need it; the rest pass it on |
| Identity | none: a wire | an anchor named relative to its net, never global |

## Recommended, staged

The Cells plan holds the steps, in this order:

1. `cells-freeze.sharing`: the ladder counts as well as compares, a
   regression before the fix. F2's families are known losses, marked
   strictly.
2. `cells-freeze.cursors`: the mechanism, a design for the
   maintainer's review before any kernel change.
3. `cells-freeze.cells`, then `cells-freeze.templates`: F2's two
   families made flat.
4. `cells-lazy-data.handles`, then `cells-lazy-data.cursors` after a
   spike, then `cells-lazy-data.boundary`.
5. Then effects (`bridge-effects`) and objects made at run time
   (`cells-objects.runtime`).

Full structures in the net (dicts, tags and lists as nodes) stay open
for streams.

## Questions for the maintainer

1. **Within a net.** Is "cursors, a use through one known unshared
   moving what it names, a one-way flag for sharing" the right reading
   of the third round?
2. **The design of `cells-freeze.cursors`.** Do its proposals hold, in
   the Cells plan? They cover what a cursor names, what counts as
   finished, where demand starts, and how a level offset is carried.
