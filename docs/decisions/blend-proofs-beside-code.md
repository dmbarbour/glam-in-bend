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
   the code and from each other (the maintainer, 2026-11-04):
   `blend/run.sh emit X.blend` writes the code `X.bend`; `laws`,
   `X_LAWS.bend`, every law of the module, its concrete objects'
   instances and its own, importing the code as `Blend_0`; `proof`,
   `X_PROOF.bend`, every proof, `def Blend_Laws.Obj.name`, importing
   the code and the laws, as `Blend_Laws`, each proof after those it
   uses. Both name the code through `Blend_0`, the module's datatypes
   too, and other modules as the code does. `_`, not a dot: Bend
   imports only plain names (letters, digits, `_` and `-`), and
   `X.LAWS.bend` is refused.
2. `law name:` with its `for` lines and its claim is a member, named as
   a definition is (`Obj.name`). `proof name(params):` is the proof of
   the law `name`, a member of its own beside the law, emitted as the
   def Bend pairs with it; `upd proof` replaces one inherited, by the
   rules for any definition.
3. A law is a claim, not a definition: code that names one is an error,
   and a proof naming one, its own law in an induction or another as a
   lemma, calls that law's proof. A proof of no law is an error. A law
   is stated once, never updated: a family wanting a stronger claim
   states a new law.
4. An unproved law is an open claim, as in Bend: the gate's proof step
   reports it.

**Consequences.**
- The programs built carry no proofs, and no open law blocks them. The
  gate checks every `*PROOF.bend` and pairs each `X_LAWS.bend` with its
  `X_PROOF.bend`, as `LAWS.bend` with `PROOF.bend`.
- A proof's name inside Blend is its law's with `#` after it, which no
  name in a body can spell; messages name it `proof name`.
- `scripts/check_laws.py` reads `law` members in `.blend` files as it
  reads `LAWS.bend`, each named by the objects it sits in
  (`Monoid.right_id`): changing one on main needs its `Law:` trailer.
- Not yet: a lemma's own statement as a member (a definition typed as
  an equality goes with the code, a typed `proof` is to come), the
  prior of a proof (`_name` in an `upd proof`), which Bend sees as an
  untyped def.
- The samples `laws`, and the invalid `proof-no-law`, `law-named`,
  `upd-law`, `proof-twice`, `upd-proof-undefined`.

**Rule lives in:** `blend/README.md`, The model and What it emits.
