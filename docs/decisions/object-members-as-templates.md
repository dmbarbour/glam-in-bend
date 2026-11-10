# An object's member is a template of `self` and the whole prior dict

`object-members-as-templates` · agent · rev efc1803

**Context.** An object is a chain of mixins (Syntax.md, Objects: `defs`
is `\prior instance -> prior with ...`). The bridge's object milestone
instantiates the objects whose bodies and parents are known at load;
objects made at run time are to follow. The maintainer (2026-11-10):
"Regarding the recipe for members, you may need the entire prior
dictionary in general." Resolving member names straight to cell handles
at load would be faster, and is the shortcut runtime objects would have
to undo.

**Decision.** A member is lowered as Syntax.md desugars a body: a
template of two parameters, `self`, the instance, and `_self`, the whole
prior dict. Under the default alias a bare member name is a field of
`self` and a prior `_k` one of `_self`; under `alias h`, bare names are
the host's, `h` is `self` and `_h` `_self`, an alias spelt `_h` being
`h`. Each instance has a cell for each member definition, its recipe the
member's template applied to two constants: the instance's dict of
member handles, and the prior dict where the definition's body stands.
The instance is that dict of handles, a constant. Each body, an object's
own or an `extend`'s, is a mixin step of its own. `spec` is left out
until something reads it.

**Consequences.**
- One template for each member definition, shared by every instance;
  late binding comes free, each instance having cells of its own.
- A member reads its own object's members through one field read on
  `self`, a cost for each reference that handles resolved at load would
  not have.
- Objects made at run time apply the same templates to dicts that
  evaluation builds; what remains for them is making cells at run time.
- The module resolves its own overrides statically, by versions, until
  modules become objects (`cells-modules`).

**Rule lives in:** `glam/objects.bend`, its header.
