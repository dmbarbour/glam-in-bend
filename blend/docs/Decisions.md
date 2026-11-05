# Decisions

Why Blend is the way it is. Each decision is a small record in
[`decisions/`](decisions/), grouped here under the larger decisions they
belong to. The rules themselves live in Blend's standing docs (the
README's model above all, `LAWS.bend`): a record says why, and names
where its rule lives. Blend grew in glam-in-bend, whose records some of
these cite by slug (`generated-sources`, `shadowing-is-an-error`).

## Records

A record is `decisions/<slug>.md`, its slug its stable name, cited as
`` `slug` `` in docs, plans, code comments and commits.

    # <Descriptive title>

    `<slug>` · maintainer|agent · rev <short hash>

    **Context.** …
    **Decision.** …
    **Consequences.** …
    **Rule lives in:** <doc and section>   (omit if none)

- **rev** names the commit a record's last substantive revision was made
  on top of (`HEAD` while editing); `git log <rev>` gives the context it
  was decided in. Typo fixes leave it alone.
- **Revise in place**: a record states the current decision only; git
  keeps the old versions. **Delete what no longer holds**, with its index
  line, once nothing cites its slug.
- **maintainer** marks a decision the maintainer made or ratified;
  **agent** one an agent made, open to revision.
- Plans extract their durable decisions here, at the latest before they
  retire ([`plans/README.md`](plans/README.md)).

This index stays an index: a short paragraph per larger decision, then
one linked line per record. The docs check (`check.sh`) holds every
record's header and rev, that this index lists it, and that no record's
body moves in here.

## The repository

- [`blend-own-repository`](decisions/blend-own-repository.md): Blend is
  arranged within its directory as its own repository would hold it, the
  tools it shares with glam-in-bend found there until a split copies
  them.

## The model

Blend translates static objects into Bend and adds no logic of its own;
its modules, namespaces and emitted names are Bend's.

- [`blend-adds-no-bend-logic`](decisions/blend-adds-no-bend-logic.md):
  Blend translates objects and adds no Bend logic of its own; mutual
  recursion is an error as in Bend; types, laws and proofs are members,
  emitted as Bend.
- [`blend-module-is-bend`](decisions/blend-module-is-bend.md): a Blend
  module is no object; its own definitions are plain Bend, as Bend's
  static modules are.
- [`blend-namespaces-as-bends`](decisions/blend-namespaces-as-bends.md):
  Blend's namespaces are Bend's, a file's own names and its imports' by
  local aliases, the same however imports reach them; `extend` stays out
  of the top level.
- [`blend-frozen-host`](decisions/blend-frozen-host.md): `^` sees the host a
  nested object is made for, and inheritance never binds it again.
- [`blend-copies-keep-their-name`](decisions/blend-copies-keep-their-name.md):
  a copied definition is always emitted by its own name, and once more
  for each use.
- [`blend-declares-witnessed`](decisions/blend-declares-witnessed.md): a
  typed declaration is bound in each concrete object to its own types
  and checked by a witness Bend checks, in the proofs' file.
- [`blend-templates-affine`](decisions/blend-templates-affine.md): a
  template is affine by default, as any definition; the guide explains
  `shared` against `copied` for templates.
- [`blend-emit-verifies-imports`](decisions/blend-emit-verifies-imports.md):
  emission writes only the modules a command names, and verifies each
  import none names against its emission, unless `--alone`.
- [`blend-proofs-beside-code`](decisions/blend-proofs-beside-code.md): a
  Blend module's laws and proofs are written into files of their own
  beside its code, `X_LAWS.bend` and `X_PROOF.bend`, by the emission
  that writes the code; a law is a claim stated once, its proof a member
  `upd proof` may replace, a typed proof a lemma.
- [`blend-no-shadowing`](decisions/blend-no-shadowing.md): within a
  `.blend` file or object, a bare name is a local or a definition, never
  both, as glam's `shadowing-is-an-error` has it.
