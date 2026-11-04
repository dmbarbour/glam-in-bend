# A Blend module is no object: its own definitions are Bend's

`blend-module-is-bend` · maintainer · rev 9fbf666

**Context.** Blend's first design made the module an object
(`blend/README.md`): its definitions were the outermost scope, reached
from an object's body by a bare name or by enough `^`, and checked as an
object's are, with `upd`, `declare` and sharing marks allowed. Bend's
own modules are static: a file of definitions, imported by path under a
name (`import ./kprim.bend as P`, then `P.fuse`), with no inheritance.

**Decision.** The maintainer (2026-11-04): the module is not an object,
to align with Bend's static top-level modules. Its own definitions are
plain Bend, emitted as written, with no prefix, no `upd`, no `declare`
and no sharing marks. An object's body names them as Bend's top-level
names, after every object's definition. `^` stops at a top-level object,
which has no host.

**Consequences.**
- At the top level, `upd`, `declare`, `shared def` and `copied def` are
  errors; `^name` in a definition of the module is an error; `_name`
  there is Bend's name.
- Blend still binds the names in the module's definitions, without
  rewriting them, to put callees first and to find the objects'
  definitions they use. Their uses of an affine definition count, since
  Bend makes no difference between their calls and an object's.
- The module's definitions are shared, as Bend's are: neither affine,
  nor copied, nor held to the rule against shadowing.
- The sample `nested` reaches the module's `unit` by its name;
  `host-at-module` fails for `^` in a definition of the module.

**Rule lives in:** `blend/README.md`, The model.
