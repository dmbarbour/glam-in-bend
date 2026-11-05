# Blend's namespaces are Bend's: a file's own, its imports' by alias

`blend-namespaces-as-bends` · maintainer · rev ab4154f

**Context.** Bend's top-level namespace, tried 2026-11-04:
- A file's definitions, datatypes and constructors go by their names.
  Another file's go only through an alias the file imports (`A.foo`,
  `TA.T`, `TA.K{...}`); same names in two files do not clash.
- An alias is local to the file that imports it, and passes through no
  import: a file cannot name what its imports import.
- A file is one module however it is reached, by the file it resolves to:
  a type reached by two routes, or through a symlink, is one type, and a
  function so reached is compiled once (`FID_a_foo`, named by its
  file's path), one function with as many callers as call it.
- Datatypes are nominal, by file and name: one shape declared in two
  files makes two types, a byte-identical copy at another path too. A
  type a definition computes is transparent: two definitions computing
  `List<&2, U32>` interchange.
- Import paths are plain: `./x.bend`, or `../x.bend` leading.

Blend's first imports carried, into the root's emitted file, the aliases
of the modules whose bodies it copied (`Ut`, `D`, `D2`). Whether the
root's own code could name `Ut.sq` then depended on what it inherited.
And a copied body naming its module's datatype by its bare name broke,
constructors being no more global than definitions.

**Decision.** The maintainer (2026-11-04): if Bend's top-level namespace
does not depend on the path of imports, neither does Blend's; no
surprises. Blend's top-level namespace follows Bend's as far as it can,
foibles and all (the maintainer, 2026-11-04). A module made an object, copied for each importer, would
also make its datatypes as many distinct types, values of one copy's
refused by another's: the module stays one, as a Bend file is.
- A module's names are its own definitions and objects, and through the
  aliases it imports, theirs.
- An object is one however reached.
- `extend` stays out of the top level, as it would change an object
  that other modules depend on, which Bend's top-level namespace has no
  room for; inside an object it is a mixin on the named nested object
  (`blend-nested`).

**Consequences.**
- A body copied from another module keeps its meaning in the root's
  emission. That module's aliases, and its datatypes' and constructors'
  bare names, are named through the root's own alias for the file
  where it has one, else through one Blend reserves (`Blend_1` and on).
- A name the user writes may not begin `Blend_`. The root's namespace is
  no larger for what it inherits: a name it did not import fails in
  Bend, however its inheritance runs.
- The sample `imports` copies a datatype (`S.Dim`) and a plain Bend
  import (`Blend_1`); `reserved-prefix` fails.
- Known short of it: Blend identifies a module by its path made plain,
  where Bend goes by the file a path resolves to, so a symlinked
  `.blend` file is two modules to Blend and its emission one to Bend
  (`blend-symlinks`).

**Rule lives in:** `README.md`, The model.
