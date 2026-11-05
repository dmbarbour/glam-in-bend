# A bare name is a local or a definition, never both

`blend-no-shadowing` · agent · rev e443d92

**Context.** Blend follows glam's object model, and glam forbids
shadowing (`shadowing-is-an-error`, glam-in-bend's): a bare name that
means a local in one place and a definition in another invites
confusion. Blend applied that rule from its first resolver, citing
glam's record; as Blend becomes a repository of its own
(`blend-own-repository`), the rule wants a record of Blend's.

**Decision.** Within a `.blend` file or object, a bare name is a local
(a parameter or a binder of a body) or a definition, never both: a local
named as a definition in reach is an error. A name beginning `^` (a
host's) or `~` (a template's argument) is neither.

**Consequences.**
- A local is emitted as it is written, bound to no definition (Blend's
  laws `locals.not_name`, `locals.kept`, `locals.template`).
- The error is the invalid sample `shadow` (`samples/invalid/`).

**Rule lives in:** `README.md`, The model.
