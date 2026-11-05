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

Status: the tool emits. `blend/run.sh emit [--alone] FILE.blend...
[DIR]` writes, for each module named, the `.bend` it makes, every
concrete object's definitions, and where it has laws its laws and its
proofs, each a file of its own beside the code, beside the module or
into DIR, printing each path; or, writing nothing at all, the errors of
any (on stderr, the status 1). A module's emission depends on nothing
that imports it (every definition emitted, no top-level object
extended), so modules emit independently. Only the modules named are
written (`blend-emit-verifies-imports`): an import none names is
verified instead, emitted again in memory and compared with its files
beside it, each byte, a file stale, missing or no longer emitted an
error that writes nothing; `--alone` leaves the imports unverified
(`bend blend.bend -- emit --alone ...` under Bend, which takes a dashed
argument as its own). DIR takes every file flat, for checking: two
modules writing one name there are an error. The
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
      upd def g(+x: U32) -> U32:    # updates g: an error if Name has none
        (_g(x) + 1 : U32)
      upd h(+x: U32) -> U32:        # `upd` alone: sugar for `upd def`
        (_h(x) * 2 : U32)
      shared def k(...) -> ...:     # sharing other than affine, stated
        ...
      object Inner with             # objects nest
        ...

    abstract object Family with     # emitted only through its children
      declare after                 # a name a concrete child must define
      declare step(+n: U32) -> U32  # and what it must be, Bend checking

    object Both extends Name, Family    # no members: no `with`

    abstract object Monoid with
      declare type T
      declare zero, op
      law right_id:                 # a claim, each family its own
        for +x: T()
        {op(x, zero()) == x : T()}

    object NatAdd extends Monoid with
      ...
      proof right_id(x):            # its proof, Bend's def of the law
        ...

- **Definitions** are Bend definitions, `def` introducing a name and
  `upd def` replacing one the object has, glam's `=` and `:=`; `upd`
  alone is sugar for `upd def`, as `upd type` updates a type (the
  maintainer, 2026-11-04). A body is Bend.
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
- **Nested objects** are members too, folded down their host's
  linearization as a definition is: `object Inner` introduces one,
  `extend Inner with` updates it (glam's `extend`, a mixin on the named
  object), `extend abstract Inner` keeps it abstract, a plain `extend`
  instantiating it. An object has its parents' nested objects, each its
  own (`Outer2.Inner`), linearized from the contributors nearest it to
  the one introducing it, then that one's parents. `extend` stays out of
  the top level (`blend-namespaces-as-bends`).
- **`^` is frozen** (`blend-frozen-host`), glam's semantics: a bare name
  binds to the final object's definition; a nested object made for host
  X binds a copy of each mixin it is made of to X, `^` in their bodies X
  and `^^` X's host, a bare name in the introducing mixin's `extends`
  found from X as well; inheritance never binds again. So `Outer2.Inner`
  sees Outer2, being made again for each host, and an object inheriting
  `Outer2.Inner` sees Outer2 in every body, as a call of `Outer2.foo`
  would. Each made object's copies are its own: inheriting
  `Outer2.Inner` and `Outer.Inner` together introduces their shared
  names twice, an error as any two introductions are.
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
  threads type parameters. Bend erases them. A type member is
  transparent, the type it computes: `Sum.S()` is `U32` wherever it
  meets one, no type of its own as a datatype is (Bend's datatypes are
  nominal, by file and name).
- **Laws and proofs** are members too (`blend-proofs-beside-code`):
  `law name:` with its `for` lines and its claim, Bend's, stated over
  the object's definitions and types, each concrete object getting its
  own instance, `NatAdd.right_id`, bound to its own finals; `proof
  name(params):` proves the law `name`, where the law is stated or in
  any object below it, and `upd proof` proves it again where a family
  needs its own, `_name` its prior proof. A typed proof, `proof
  add_succ(a: Nat, -b: Nat) -> {...}:`, is a lemma, stating what it
  proves. In a proof, its own law named is the proof itself, its
  induction; another law named is that law's final proof. A law is a
  claim stated once: never updated (the maintainer, 2026-11-04: a
  robust foundation), and code names no law, proof or lemma. A member's
  kind holds down the linearization: `upd` updates a definition,
  `upd proof` a proof or a lemma. An inherited proof, a prior's too, is
  checked against the family's finals, as any inherited body is: a
  family that changes what a proof relies on proves it again. An
  unproved law is an open claim, which the gate's proof step reports.
  The module's own laws and proofs, at its top level, are Bend's, as
  its definitions are, written beside the code as an object's are.
- **Declarations** say what a family must give (`blend-declares-witnessed`):
  `declare after` a name, untyped; `declare def push(st: S(), +x: U32)
  -> S()`, or `declare push(...) -> S()` for short, what the definition
  must be; `declare type S: Data`, the kind a type must have. A typed
  declaration is bound in each concrete object to its own finals, so
  that a family's types flow into it, and is fixed where first made, the
  families varying by their types. Blend has no type checker: for each
  concrete object it writes a witness into the proofs' file,
  `def Listed.push.as_declared(st: Blend_0.Listed.S(), +x: U32) ->
  Blend_0.Listed.S(): Blend_0.Listed.push(st, x)`, and Bend checks it;
  never into the program, where a witness would be a second caller,
  splitting the definition into a segment of its own.
- **Templates** are Bend's, passed through: a `~` parameter binds as any
  parameter, and a `~` argument is a reference as any, bound to the
  final object's definition (`~inc` emitted `~Twice.inc`), or a closed
  lambda. Bend compiles each distinct set of `~` arguments to a copy of
  its own, so a template used more than once is marked `shared`, Bend
  making its copies; the affine default counts its call sites as any
  definition's. A typed declaration's witness passes a template's
  parameter on as `~f` and an erased one as `A`.
- **Nothing at run time.** Datatypes stay in plain Bend, the module's,
  passed through as written (`type Box<A> is Data:`); a type member can
  be one's argument (`Box<S()>`).
- **Imports** of other `.blend` files, `import ./lib/shapes.blend as
  S`, name their objects `S.Square`, to extend and to call. Imports form
  a DAG, each file read once, a cycle an error, and an object means the
  same however an import reaches it, the module being no object
  (`blend-module-is-bend`). An import's path is as Bend's: `./` and
  `../` leading only, then plain names (letters, digits, `_`, `-`), no
  absolute path; Blend refuses the paths Bend would. Each module emits its own `.bend`; the
  root's import of one names it. An object extending another module's
  copies what it inherits, and the bodies copied name that module's
  definitions through its alias.
- **Namespaces are Bend's** (`blend-namespaces-as-bends`): a file's
  definitions, datatypes and constructors by their names, another's
  through an alias it imports, local to it and passed through no
  import. A body copied from another module keeps its meaning: its
  module's aliases and datatypes are named in the copy through the
  root's own alias for the file, else one Blend reserves (`Blend_1`),
  which no name the user writes may begin. `extend` stays out of the top
  level.
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
- Laws and proofs go into files of their own beside the code, as Bend's
  convention keeps them, so that the programs built carry no proofs and
  no open law stops them, written by the same emission as the code:
  `X_LAWS.bend`, every law, importing the code `X.bend` as `Blend_0`;
  `X_PROOF.bend`, every proof, as
  `def Blend_Laws.NatAdd.right_id(...)`, and every lemma, as
  `def NatAdd.add_succ(...) -> ...`, and every typed declaration's
  witness, `def Listed.push.as_declared(...)`, importing the code, and
  the laws where there are any, as `Blend_Laws`, each after those it
  uses. A module with witnesses and no laws writes no laws' file. Bend imports only plain names,
  so `_`, not a dot. The gate checks every `*PROOF.bend` with
  `--verdict`, and that each `X_LAWS.bend` has its `X_PROOF.bend`.
- A prior proof is written only where a proof reaches it by `_name`:
  replaced and not named, it is gone, and nothing checks it. Reached, it
  is a def of its own, `Blend_Laws.AnyOf.double_op.Monoid`, proving its
  law for the family's finals; Bend gives an untyped def the type of the
  law of its name, so the laws' file states that law again by the
  prior's name. It is no new claim, the same law named twice, and the
  prior must hold for the family as the proof relying on it does.
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
- `family-nested`: nested objects inherited and extended down their
  hosts' linearizations, `^` seeing the final host.
- `nested-reach`: frozen hosts, an object inheriting `Outer2.Inner` by
  its path, a nested object's `extends` found from its host, a diamond
  of hosts.
- `types`: type members declared, given by each family and named in
  signatures, a datatype of the module's taking one as its argument.
- `imports`, with `lib/shapes.blend`: an object extending an imported
  one, the library's definitions named through its alias.
- `choice`: a family's choice as a constant definition, the branch
  on it left to the C compiler to fold.
- `laws`, with `laws_LAWS.bend` and `laws_PROOF.bend`: laws an abstract
  family states, proved by each family by induction or cases, or once
  for all by the family stating them, `upd proof` where a family's
  update of a definition needs its own; a lemma; the module's own law
  and proof at its top level.
- `declares`: typed declarations of a definition, of its short form and
  of a type's kind, each family's checked by its witnesses; an untyped
  declaration beside them.
- `templates`: a template in a family, shared, called with a definition
  and with a lambda; typed declarations taking a template's parameter
  and an erased one.
- `laws-imported`, with `lib/adds.blend`: laws a library states and
  proves for every family, a family's own law proved with an inherited
  one, and a prior proof reached across modules.

`blend/samples/invalid/`: each `.blend` beside the error it must raise
(`.err`): an update of nothing, an introduction of a name inherited, an
affine definition used twice, mutual recursion, a declared name left
undefined, a parameter shadowing a definition, parents with no C3
linearization, `^` in a definition of the module, members after a header
that leaves out `with`, a declared type left undefined, a datatype in an
object, an import reaching the module importing it, an import of no
file, an import's path Bend would refuse, a name beginning `Blend_`, an extension of nothing inherited, a
nested object introduced where one is inherited, `extend` at the top
level, two nested objects made of one mixin inherited together, a proof
of no law, code naming a law, `upd law`, a proof introduced where one
is inherited, `upd proof` with no proof to update, `upd` of an
inherited law, a definition meeting an inherited law, code naming a
lemma, `upd proof` of a definition, a declaration made again below, a
typed declaration with no return type.

`blend/samples/refused/`: each `.blend` Blend emits and Bend refuses,
its proofs' file failing as its `.err` says: a family's definition that
does not fit its declaration, a type of another kind than declared.

## Known issues

- Symlinks: Blend identifies a module by its path made plain (`.` and
  `..` resolved), where Bend goes by the file a path resolves to, a
  symlink included; a `.blend` file reached by a symlink is two modules
  to Blend (`docs/plans/Blend_2026-11-04.md`, `blend-symlinks`).

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
- A `blend` command of its own, so that no script stands between the
  user and the tool (`blend-cli`).
- Verifying an import costs its emission again. A stamp in each
  emitted file's header, a hash of the sources it comes from and of
  Blend, would let verification read a line instead (`blend-cli`).
- Blend's own laws (`blend-laws`); what a declared definition must be,
  checked by a witness in the proof file (`blend-typed-declares`).
- Theories, `theory` declarations as objects, should something more
  extensible and mutable than laws be wanted (the maintainer,
  2026-11-04, `blend-theories`).
- Macros, explicit in the source, marked apart from Bend's templates
  (`~~name`): the maintainer allows that Blend may support them
  (2026-11-04, `blend-macros`).
- Blend's own home: written in Bend (`generated-sources`), here first,
  perhaps shared beyond this project.
