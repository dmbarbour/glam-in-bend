# Blend

Static objects for Bend, after glam's object model: a preprocessor of our
own that reads `.blend` files and writes `.bend` files, the objects
vanishing in the translation. It is meant to specialize code without
sharing it by accident: Bend folds a chain of functions into one compiled
segment only while each function has one caller, so a family of
strategies wants a copy of its chain each, and a hook a family supplies
wants to be a definition it overrides rather than a template argument
threaded through every signature (`docs/plans/Codegen_2026-11-04.md`,
`codegen-vehicle.blend`).

Status: the tool emits. `blend/run.sh emit FILE.blend` prints the
`.bend` a `.blend` file makes, every concrete object's definitions, or
its errors (on stderr, the status 1). The
stages before it print what they find: `read` the structure, `objects`
each object's linearization and definitions, `resolve` each copy and
what its names reach. `blend/run.sh` runs the tool built once for each
version of its sources (`blend/build.sh`); `bend blend.bend COMMAND ...`
runs the same, checked and compiled each time. `blend/check.sh`, in the
gate, holds every sample to its `.bend` or its `.err`.

The maintainer's direction (2026-11-04): `def` and `upd` for
introduction and override, definitions affine unless marked; the samples
may change to fit the implementation, keeping their intention. The tool
and the kernel's move onto it: `docs/plans/Blend_2026-11-04.md`.

## The model

A `.blend` file is a module of Bend's kind, holding its imports, its own
definitions and its objects. The module is no object
(`blend-module-is-bend`): its own definitions are plain Bend, emitted as
written, with no prefix, no `upd`, no `declare` and no sharing marks.
Bend's imports pass through.

    import Base
    import ./kprim.bend as P

    object Name extends Parent1, Parent2 with   # `with` before members
      def f(+x: U32) -> U32:        # introduces f: an error if Name has f
        g(x)
      upd g(+x: U32) -> U32:        # updates g: an error if Name has none
        (_g(x) + 1 : U32)
      shared def h(...) -> ...:     # sharing other than affine, stated
        ...
      object Inner with             # objects nest
        ...

    abstract object Family with     # emitted only through its children
      declare after                 # a name a concrete child must define

    object Both extends Name, Family    # no members: no `with`

- **Definitions** are Bend definitions, `def` introducing a name and
  `upd` replacing one the object has, glam's `=` and `:=`. A body is Bend.
- **References** in a body, as in glam: a bare name called binds to the
  final object's definition, so that an update reaches every definition
  that calls it; a reference takes the longest name defined, dots
  included (`note.go`). `_name` is the prior definition, the one this
  `upd` replaces. `^name` steps out of the innermost object to its
  host's scope, `^^name` two steps: a top-level object's host is the
  module, the outermost scope, with no host of its own. `Obj.name` or
  `Outer.Inner.name` is that object's final definition. A bare name that
  no object in reach defines may be one of the module's definitions,
  Bend's, its text kept; any other name is Bend's. A bare name is a local
  or an object's definition, never both (`shadowing-is-an-error`).
- **Inheritance** is multiple, linearized by C3 as glam's is: a parent
  named twice is one parent. An object's definitions apply after its
  parents', so that an `upd`'s prior is the definition the next object
  in the linearization gives (`prior`: Bold's update of Loud's of
  Plain's).
- **Sharing** is stated for each definition, within the emitted program:
  - affine, the default: one use at most (a definition's calls to itself
    aside), so that Bend folds it into its caller;
  - `shared`: one copy, however many use it;
  - `copied`: emitted by its own name, and a copy more for each use, each
    folding into its own caller (`blend-copies-keep-their-name`); an
    affine definition a copy alone reaches is copied with it.
  The module's definitions are Bend's, and shared; their uses count.
- **Types** are members too: `type S = T` is sugar for a shared
  definition returning the type, `shared def S() -> Type: T`, and
  `type S: Data = T` for one of kind Data; `type Pair(A: Data) = A & A`
  takes parameters; `upd type` and `declare type` as for any definition
  (the maintainer, 2026-11-04). A name of one is a call, `S()`, bound as
  a definition's is, in signatures as in bodies, so that no family
  threads type parameters. Bend erases them.
- **Nothing at run time.** Datatypes stay in plain Bend, the module's,
  passed through as written (`type Box<A> is Data:`): Bend's constructor
  names are global; a type member can be one's argument (`Box<S()>`).
- **Imports** of other `.blend` files, `import ./lib/shapes.blend as
  S`, name their objects `S.Square`, to extend and to call. Imports form
  a DAG, each file read once, a cycle an error, and an object means the
  same however an import reaches it, the module being no object
  (`blend-module-is-bend`). Each module emits its own `.bend`; the
  root's import of one names it. An object extending another module's
  copies what it inherits, and the bodies copied name that module's
  definitions through its alias; the imports they need, that module and
  its own, are carried into the root's emission, where the root has none
  of that alias, an alias two imports give two files an error.
- **No Bend logic of its own.** Blend translates objects; what a
  definition says in Bend means what Bend makes of it, so two
  definitions calling each other are an error, as in Bend
  (`blend-adds-no-bend-logic`). Anything more is a construct of Blend's
  own, named where it is used.

## What it emits

For each concrete object, every definition its linearization gives it,
its own copy, bound to its own finals: no sharing between objects.

- The final definition of `f` in `Obj` is `Obj.f`; a definition it
  replaced, where reached through `_f`, is `Obj.f.Origin`, after the
  object that defined it; a copied `f` is `Obj.f`, and its copies for its
  uses `Obj.f.c1`, `Obj.f.c2`, one for each use; the
  module's definitions call `Obj.f`. A nested object's prefix is its
  path, `Outer.Inner.f`.
- Definitions come callees first, as Bend requires. Two definitions
  calling each other have no such order: an error, as Bend has no mutual
  recursion. Any other order, and which copy of a copied definition takes
  which number, is the tool's, not Blend's: they change nothing Bend
  observes (the maintainer, 2026-11-04), and a plain `.bend` file calls a
  copied definition by its own name. The samples hold the tool to its
  present order.
- An abstract object emits nothing of its own.
- Before each definition, a marker names where it is written,
  `# blend: FILE:LINE`; its lines follow as they are there, so the line
  k lines below a marker is the source's k lines below LINE.
  `blend/where.sh FILE.bend LINE` finds it, for Bend's errors on emitted
  code.

## The samples

`blend/samples/`: each `.blend` beside the `.bend` it emits, a generated
file checked current by `scripts/check_generated.sh`, and the `.out` its
program prints.

- `override`: introduction, update, late binding.
- `prior`: `_name`, and C3 over a diamond of updates.
- `family`: an abstract object's declared hook, introduced by each
  family, in place of a template argument; a definition calling itself.
- `sharing`: affine by default, `shared` and `copied`.
- `nested`: nested objects, `^name`, the module's definitions as Bend's.
- `types`: type members declared, given by each family and named in
  signatures, a datatype of the module's taking one as its argument.
- `imports`, with `lib/shapes.blend`: an object extending an imported
  one, the library's definitions named through its alias.
- `choice`: a family's choice as a constant definition, the branch
  on it left to the C compiler to fold.

`blend/samples/invalid/`: each `.blend` beside the error it must raise
(`.err`): an update of nothing, an introduction of a name inherited, an
affine definition used twice, mutual recursion, a declared name left
undefined, a parameter shadowing a definition, parents with no C3
linearization, `^` in a definition of the module, members after a header
that leaves out `with`, a declared type left undefined, a datatype in an
object, an import reaching the module importing it, an import of no
file.

## Open questions

- Partial evaluation: a constant definition and the C compiler cover
  static choices (the sample `choice`); next, `static` definitions
  substituted where used and a `static match` pruning arms; at most,
  definitions computed by running Bend when generating, as
  `spike/tools/gen_krules.bend` does.
- A plain `.bend` file names an object's definitions by their emitted
  names, `Eager.go` (the maintainer, 2026-11-04). A module emits every
  definition, not only those some roots reach, so that a module several
  import is emitted once (the maintainer, 2026-11-04).
- Several files on one command line, and how their outputs are written;
  the maintainer leans to one root module doing a dozen jobs by its
  imports (2026-11-04).
- Nested objects inherited and extended, `extend Inner with ...`
  (`blend-nested`).
- Laws and proofs as members, each family its own instance
  (`blend-object-laws`); Blend's own laws (`blend-laws`).
- Macros, explicit in the source, marked apart from Bend's templates
  (`~~name`): the maintainer allows that Blend may support them
  (2026-11-04, `blend-macros`).
- Blend's own home: written in Bend (`generated-sources`), here first,
  perhaps shared beyond this project.
