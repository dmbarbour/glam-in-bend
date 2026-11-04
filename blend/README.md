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

Status: a design, its samples, and the tool's first steps: `bend
blend.bend read FILE.blend` reads a `.blend` file and prints its
structure (`blend-read`); `bend blend.bend objects FILE.blend` checks
its objects and prints their linearizations and definitions
(`blend-objects`). Each valid sample's emitted form is written by
hand and checked to run under Bend; `blend/check.sh` checks them and
reads every sample, and the gate runs it. The maintainer's
direction (2026-11-04): `def` and `upd` for introduction and override,
definitions affine unless marked; the samples may change to fit the
implementation, keeping their intention. The tool and the kernel's move
onto it: `docs/plans/Blend_2026-11-04.md`.

## The model

A `.blend` file is a module, and the module is an object: its own
definitions are emitted with no prefix. Bend's imports pass through.

    import Base
    import ./kprim.bend as P

    object Name extends Parent1, Parent2 with
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

- **Definitions** are Bend definitions, `def` introducing a name and
  `upd` replacing one the object has, glam's `=` and `:=`. A body is Bend.
- **References** in a body, as in glam: a bare name called binds to the
  final object's definition, so that an update reaches every definition
  that calls it; a reference takes the longest name defined, dots
  included (`note.go`). `_name` is the prior definition, the one this
  `upd` replaces. `^name` steps out of the innermost object to its host,
  `^^name` two steps; the module has no host. `Obj.name` or
  `Outer.Inner.name` is that object's final definition. Any other name is
  Bend's. A bare name is a local or a definition, never both
  (`shadowing-is-an-error`).
- **Inheritance** is multiple, linearized by C3 as glam's is: a parent
  named twice is one parent. An object's definitions apply after its
  parents', so that an `upd`'s prior is the definition the next object
  in the linearization gives (`prior`: Bold's update of Loud's of
  Plain's).
- **Sharing** is stated for each definition, within the emitted program:
  - affine, the default: one use at most (a definition's calls to itself
    aside), so that Bend folds it into its caller;
  - `shared`: one copy, however many use it;
  - `copied`: a copy for each use, each folding into its own caller; an
    affine definition a copy alone reaches is copied with it.
- **Nothing at run time.** Types stay in plain Bend: they make no code to
  specialize, and Bend's constructor names are global.
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
  object that defined it; the copies of a copied `f` are `Obj.f.c1`,
  `Obj.f.c2`, in the order their uses appear. A nested object's prefix is
  its path, `Outer.Inner.f`.
- Definitions come callees first, as Bend requires, source order between
  the unrelated. Two definitions calling each other have no such order:
  an error, as Bend has no mutual recursion.
- An abstract object emits nothing of its own.

## The samples

`blend/samples/`: each `.blend` beside the `.bend` it emits and the
`.out` its program prints.

- `override`: introduction, update, late binding.
- `prior`: `_name`, and C3 over a diamond of updates.
- `family`: an abstract object's declared hook, introduced by each
  family, in place of a template argument; a definition calling itself.
- `sharing`: affine by default, `shared` and `copied`.
- `nested`: the module as an object, nested objects, `^name`.
- `static`: a family's static choice as a constant definition, the branch
  on it left to the C compiler to fold.

`blend/samples/invalid/`: each `.blend` beside the error it must raise
(`.err`): an update of nothing, an introduction of a name inherited, an
affine definition used twice, mutual recursion, a declared name left
undefined, a parameter shadowing a definition, parents with no C3
linearization, `^` out of the module.

## Open questions

- Partial evaluation: a constant definition and the C compiler cover
  static choices (`static`); next, `static` definitions substituted where
  used and a `static match` pruning arms; at most, definitions computed
  by running Bend when generating, as `spike/tools/gen_krules.bend` does.
- Type parameters, a family's state type: an alias definition
  substituted where used, or the family's types left to Bend's `~`.
- Imports between `.blend` files. A plain `.bend` file names an object's
  definitions by their emitted names, `Eager.go` (the maintainer,
  2026-11-04), and which definitions are emitted, every concrete
  object's or those reachable from roots, is the command line's to say.
  Several files given as roots could confuse where they extend one
  imported object; the maintainer leans to an import system that lets
  one root module do a dozen jobs (2026-11-04).
- Macros, explicit in the source: the maintainer allows that Blend may
  support them (2026-11-04).
- Types, laws and proofs overridden or specialized per family: Bend's
  for now, to revisit once Blend matures (the maintainer, 2026-11-04).
- Errors from Bend on emitted code: line markers back to the `.blend`.
- Blend's own home: written in Bend (`generated-sources`), here first,
  perhaps shared beyond this project.
