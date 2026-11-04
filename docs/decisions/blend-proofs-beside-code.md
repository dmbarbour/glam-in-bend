# A Blend module's laws and proofs are written beside its code

`blend-proofs-beside-code` · agent · rev 5699309

**Context.** Laws and proofs became object members (`blend-object-laws`,
`blend-adds-no-bend-logic`): a law stated in an abstract family holds for
each concrete family, bound to its own finals, and is proved by each, or
once by a proof the family gives, replaced where one needs its own. Bend
pairs a law with a def of its name, in the same file or another, and
erases proofs from what it compiles. But a law left open in a program's
own file stops Bend running or building it ("1 TODO found", tried
2026-11-04), and the gate checks proofs by running every `*PROOF.bend`
with `--verdict`. The plan proposed a file of their own; the maintainer
said proceed (2026-11-04) and settled that a law's statement and its
proof may sit apart, in an abstract root family and a child, across
modules; then that the laws and the proofs be files of their own, as
Bend's `LAWS.bend` and `PROOF.bend` are.

**Decision.**
1. Three files, as Bend's convention keeps laws and proofs apart from
   the code and from each other (the maintainer, 2026-11-04), written
   by one emission, never one without the others (the maintainer,
   2026-11-04): `blend/run.sh emit X.blend [DIR]` writes the code
   `X.bend` and, where the module has laws or proofs, `X_LAWS.bend`,
   every law of the module, its concrete objects' instances and its
   own, importing the code as `Blend_0`, and `X_PROOF.bend`, every
   proof, `def Blend_Laws.Obj.name`, importing the code and the laws,
   as `Blend_Laws`, each proof after those it uses; where any has an
   error, none. Both name the code through `Blend_0`, the module's
   datatypes too, and other modules as the code does. `_`, not a dot:
   Bend imports only plain names (letters, digits, `_` and `-`), and
   `X.LAWS.bend` is refused.
2. `law name:` with its `for` lines and its claim is a member, named as
   a definition is (`Obj.name`). `proof name(params):` is the proof of
   the law `name`, a member of its own beside the law, emitted as the
   def Bend pairs with it; `upd proof` replaces one inherited, by the
   rules for any definition.
3. A law is a claim, not a definition: code that names one is an error.
   A proof naming its own law names itself, its induction, a prior
   proof's included (any proof of a law serves; binding it late would
   make a prior and the final call each other); naming another law, it
   calls that law's final proof. A proof of no law is an error. A law
   is stated once, never updated: a family wanting a stronger claim
   states a new law. The maintainer (2026-11-04): reasonable to forbid
   in most cases, a robust foundation; something more extensible and
   mutable may come as theories, `theory` declarations as objects
   (`blend-theories`).
4. An unproved law is an open claim, as in Bend: the gate's proof step
   reports it.
5. A typed proof, `proof name(params) -> T:`, is a lemma: it states what
   it proves, goes into the proofs' file by its own name, and is named
   by proofs, never by code. `_name` in a proof, of a law (which has no
   prior), is its proof's prior: the prior is written in the proofs'
   file, its law stated again in the laws' file by the prior's name, so
   that Bend pairs them. A member keeps its kind down the
   linearization: `upd` updates a definition, `upd proof` a proof or a
   lemma, and neither a law.

**Consequences.**
- The programs built carry no proofs, and no open law blocks them. The
  gate checks every `*PROOF.bend` and pairs each `X_LAWS.bend` with its
  `X_PROOF.bend`, as `LAWS.bend` with `PROOF.bend`.
- A proof's name inside Blend is its law's with `#` after it, which no
  name in a body can spell; messages name it `proof name`.
- `scripts/check_laws.py` reads `law` members in `.blend` files as it
  reads `LAWS.bend`, each named by the objects it sits in
  (`Monoid.right_id`): changing one on main needs its `Law:` trailer.
  An invalid sample's laws are none, the sample held only to its error
  (the maintainer, 2026-11-04).
- scripts/check_generated.sh checks a module's files together, from one
  emission into results/, and a laws or proofs file the emission no
  longer writes is stale. Bend's IO cannot rename, so the files are
  written one after another: a write failing midway leaves the set
  mixed, which the checks catch.
- The self-binding of a proof's own law is the agent's choice, made
  when a prior proof by induction and the final delegating to it formed
  a cycle (`laws-imported`).
- The samples `laws` and `laws-imported`, and the invalid
  `proof-no-law`, `law-named`, `upd-law`, `proof-twice`,
  `upd-proof-undefined`, `law-updated`, `law-shadowed`, `lemma-named`,
  `upd-proof-def`.

**Rule lives in:** `blend/README.md`, The model and What it emits.
