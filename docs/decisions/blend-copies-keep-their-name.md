# A copied definition is always emitted by its own name too

`blend-copies-keep-their-name` · maintainer · rev 9fbf666

**Context.** A `copied` definition is emitted once for each use, numbered
(`Obj.f.c1`, `Obj.f.c2`), so that each copy folds into its own caller.
Blend's first emitter wrote the definition by its own name, `Obj.f`, only
when nothing used it, so that a plain `.bend` file could still call it.
Whether `Obj.f` existed then depended on its uses elsewhere.

**Decision.** The maintainer (2026-11-04): a copied definition is either
never emitted by its own name or always, never conditionally; always is
the less surprising. Blend emits `Obj.f` always, and a numbered copy more
for each use. An affine definition that only a copied definition reaches
is copied with it (as `blend/README.md` had it), the copy by its own name
included: `Obj.h` with `Obj.f`, `Obj.h.c1` with `Obj.f.c1`.

**Consequences.**
- The module's definitions, Bend's (`blend-module-is-bend`), call a
  copied definition by its own name, and need no copy of their own.
- The sample `sharing` emits `Arith.inc` beside `Arith.inc.c1` and
  `Arith.inc.c2`.

**Rule lives in:** `blend/README.md`, The model.
