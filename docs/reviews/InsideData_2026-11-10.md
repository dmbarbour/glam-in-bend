# Inside data — 2026-11-10

The design round of the Cells plan's `cells-lazy-data`
([`../plans/Cells_2026-11-09.md`](../plans/Cells_2026-11-09.md), its item
8), held at the maintainer's word: "Design round now." (2026-11-10).
Effects wait on it (`bridge-effects.functions`), as do objects made at
run time (`cells-objects.runtime`) and lazy members with them.

The first draft (1bf6dc1) recommended closures of templates and
captured values. It asked four questions. The maintainer's answers
showed that those closures lose the work of partial applications (F1),
and this revision follows from them. Their answer to Q2 is recorded as
`early-evaluation-optimization`. The rest proposes, and the maintainer
decides.

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

## The maintainer's answers (2026-11-10)

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
  properly as part of any template representation." The question is
  restated below.
- **Q4**, which asked for the maintainer's alternatives, is still open.

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
- **The draft misread `copy-reduced-function-nets` the same way.** Its
  "work that needs the argument is done again in each copy" is each
  application's own work, which no copy can share. The partial
  application's work is kept: "Work in the source is shared as far as
  local reduction reaches".
- **Full laziness alone falls short too.** The second reviewer's A3
  first floated maximal free expressions out of lambdas (full laziness)
  and made every capture a heap object. A dropped the float. Even with
  it, some work is redone: in `(eff:f) x = eff:(\api -> f api x)`, work
  in `f` that needs `x` but not `api` appears only once `f` is applied.
  The float cannot see it, while reducing before a freeze does it once.

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
  which needs no argument. Each splice copies the template as lowered
  and does that work again: exactly 147 interactions and 8 splices a
  use. `copy-reduced-function-nets` asks for the net to be reduced
  before it is copied, and that reduction is not built. Linked, `f` is
  one subnet shared by fans, so the work is done once.
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

**F3. Early evaluation leaves a residue.** After Q2, freezing means:
reduce until the net is done, the fuel runs out, or a reflection task
blocks; then freeze what is left. What is left is the residue.

- **Residue that does not need a parameter cannot be copied** with the
  frozen net. Copies would redo expensive work or emit a reflection
  task more than once, which `bounded-duplication` forbids. The sharp
  case:

      f a = let t = anno refl:(log a) in \y -> ... t ...
      g = f "x"          -- g applied many times

  `t` needs `a` but not `y`. Early evaluation may not run it, so
  freezing `g` leaves it in the net, and each copy of the frozen `g`
  would emit it on its first demand. The Rust bootstrap's cursors
  shared it.
- **Residue that needs a parameter** is each application's own work,
  and copying it loses nothing.

Verdict: a question for the maintainer (below).

**F4. `cells-freeze` as planned would keep F2's loss.** The step reads
"its net reduced eagerly under fuel, needs left alone". The work F2
measured lies behind needs: `c2` is a leaf, so `c2 c2` is a need. Either
needs are served as early evaluation, under fuel and stopped by a
reflection task, or the region behind an unserved need is shared as a
cell.

Closed work in a template has a cheaper fix: lift each closed
subexpression of a template into a root cell at lowering (the second
reviewer's CAF point, HeapFable 3b). That needs no reduction at run
time and leaves no residue. A lifted subexpression whose value is a
function would still meet the stopgap until `cells-freeze`.

Verdict: noted beside the step, and a question below.

## The question, restated

A function is "a value referencing a net (frozen or not) and remaining
arity" (the maintainer, 2026-10-28; `functions-are-nets-with-arity`),
and its copies share what its net reduced before them. The draft asked
where a function's environment lives when the function enters data.
With A withdrawn, the question becomes how data holds a function's net,
frozen or live, and what a frozen net holds where early evaluation
stopped.

Within one net, the kernel already keeps the sharing. Fans copy what
has reduced and wait at what has not (F2's flat families). Freezing is
needed only where a value leaves its net, as a cell's value does when
its task ends. That splits the question:

- **Within a net: ports.** Functions and lazy parts in data stay live.
  A data node's value has holes, each a port wired to a live subnet: a
  function, a lazy member, a lazy capture.
  - Fans copy the frozen part as data and share the ports, as they
    share everything else in the net.
  - A linear application is a beta, with no copy.
  - An operator that needs a hole's value needs it as it needs a
    handle today.

  This is C limited to the live parts: the maintainer's "partial data
  in net and final data as Bend data" (2026-11-09). No capture is
  closed or extracted. A closure frozen inside a running net would need
  that, since its captures are wires into a net that other parts still
  use: "a subnet with free wires is not closed, and closing it
  allocates" (HeapFable 3b; the Cells plan's item 8).

  The cost is a data node with ports, with rules for fans, lifts,
  erasers and operators, proved under laws, and levels for a port that
  holds a function (NetPairing does not cover constructors with lazy
  fields). It is unproven, and wants a spike first.
- **At a boundary: freeze.** When a cell's task ends, its value owns
  everything left in its net, so nothing needs untangling. The frozen
  part becomes data. The residue (F3) moves into cells made at run
  time, each named by a leaf in the frozen net and kept alive by
  reachability: a cell cannot keep itself alive (the maintainer's Q3).
  This is `cells-freeze`, the fix for F2. Cursors copy lazily across
  nets, leaving a reference at each active pair (the Rust bootstrap;
  `spike-cursors`). They replace the copy if boundary copies cost too
  much.
- **Within a net, the alternative: freeze at entry.** A function
  entering data becomes a cell made at run time, its net built from
  its recipe, reduced under fuel, and frozen. The records allow it, but
  it pays the cost the maintainer named (2026-11-09): "If we insist on
  a frozen net, we'll be forced to perform maximal partial evaluation
  at every application step". For effects, that is every bind. The
  mitigations they named are ApplyK and arity analysis. This path must
  also extract residue captures.

## Weighed

| | Ports, within a net | Freeze at entry |
|---|---|---|
| Sharing | fans: what reduced is copied, the rest stays shared | as far as early evaluation reaches; the residue shared as cells |
| Laziness | kept: a hole is reduced only when needed | kept: early evaluation stops at fuel and reflection |
| An effect step | a request built in a few interactions; a continuation applied by a beta, no copy when linear | a reduction under fuel, a freeze and a copy at each bind |
| Captures | stay wires | forced, or extracted into cells where the residue needs them |
| Kernel | a data node with ports and its rules, under laws | cells made at run time and freezing, which boundaries need anyway |
| Levels | a port holding a function, adjusted at its use: untested | frozen nets spliced at a level, as templates are |
| Builtins | those reading a hole need it; the rest pass it on | unchanged: data stays data |

The boundary is the same under both: `cells-freeze`, the residue in
cells made at run time.

## Recommended, staged

1. **Fix F2 first** (`cells-freeze.templates`, `cells-freeze.cells`,
   `cells-freeze.sharing`). These follow rulings already made, and
   every path needs them.
   - Closed subexpressions of templates are lifted into root cells at
     lowering.
   - A function-valued cell is frozen at the end of its task, once the
     first question is answered.
   - The ladder gains a check that fails when a family's interactions
     grow with its uses under templates but not linked.
2. **Handles as data** (`cells-lazy-data.handles`). Unchanged, and
   common to every path.
3. **Ports, after a spike** (`cells-lazy-data.ports`). The spike starts
   with one port, a tag with a live payload: its rules with fans,
   erasers and lifts, and a field read. It counts the effect step
   against a freeze at entry. Recommended because, within one net, it
   keeps the sharing the kernel already has, applies a linear
   continuation without a copy, and extracts nothing. It is unproven
   until the spike.
4. **Boundaries** (`cells-lazy-data.boundary`). A value with ports that
   leaves its net is frozen as step 1 freezes a function: the frozen
   part as data, the residue in cells made at run time.
5. Then effects (`bridge-effects`) and objects made at run time
   (`cells-objects.runtime`).

Full structures in the net (dicts, tags and lists as nodes) stay open
for streams. Cursors wait until boundary copies have been measured.

## Questions for the maintainer

1. **The residue (F3).** Should it be shared by every copy, as cells
   made at run time named by leaves in the frozen net and kept alive by
   reachability, with only the residue that needs a parameter copied?
   Or is another representation wanted?
2. **Within a net.** Ports, after a spike, or a freeze at entry with
   ApplyK or arity analysis?
3. **Q3, restated.** The draft meant this: in the draft's option B, a
   cell's value is data holding a reference into the net that computed
   it. When that task ends, the store cannot hold only `Data`, as the
   Cells plan's item 4 has it. Either the net is kept, or the value is
   closed first. I read your answer as "a template may hold live parts,
   shared by its copies and kept alive by reachability". Is that the
   reading?
4. **`cells-freeze` (F4).** Are needs served under fuel as early
   evaluation, or left alone with the regions behind them shared as
   cells?
