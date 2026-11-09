# Built-in imports are the compiler's, presented as module imports

`builtin-imports-compiler-local` · maintainer · rev bb7a163

**Context.** Modules are to become objects with parents, a `.link` file
standing for a remote module (the maintainer, 2026-11-09, `cells-modules`),
and the hello ladder defers module imports until then (`ladder-imports`).
Thirteen hello samples import the built-in `'std`, every sample of
`ladder-effects` among them, so deferring every import would hold
effects back too.

**Decision.** The maintainer (2026-11-09): built-in imports are a purely
compiler-local feature, presented as module imports but not truly part
of the module system. `import 'std` may be supported before modules
become objects, as a rung needs it.

**Consequences.**
- `ladder-effects` need not wait for modules as objects: the front end
  answers `import 'std` itself, with nothing read from a file.
- The module redesign need not give built-in modules a place among a
  module's parents or its `.link` files; they only look like imports.
