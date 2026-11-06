# Laws in Bend: where Blend writes laws and proofs

A review of how Blend and glam-in-bend place laws and proofs, against
how Bend checks them (the maintainer, 2026-11-06: "we had some deep
misunderstanding here. We should revisit our blend and glam code in
this light"). Blend's paths are its repository's, a submodule at
`blend/`.

## How Bend checks laws

Read in 2.0.40's compiler (`bend.ts`, `main.ts`, the bundle inside the
release binary) and tried, 2026-11-06:

- A law is a type and its proof a def of the same name, in any file.
  A run checks every definition it loads (`book_valid`, every def after
  Base's: the entry and all its imports, a hub package's too), each
  time; nothing is trusted for being on the hub, whose content hash
  fixes the files, not their truth. `--verdict` rechecks the same with
  the kernel proved in Lean.
- A law left open in any file loaded fails the run: a program importing
  a file with one prints "SOME PROOFS FAIL ... 1 TODO found" and does
  not run.
- `LAWS.bend` and `PROOF.bend` are a project's convention: the claims
  the human writes apart from the proofs the AI writes, and the program
  loading neither. The one rule Bend enforces is that a `PROOF.bend`
  imports the `./LAWS.bend` beside it.
- bend-mathlib keeps each law with its proof in the file that states it
  (`bool.bend`: `law not_not` and `def not_not`), so whoever imports a
  lemma checks it: Blend's `PROOF.bend` imports five of its files, and
  each gate run checks their proofs.
- `--publish` ships what its entry reaches by imports: from a
  package's code, none of its laws or proofs kept in such a pair.
- Defs no `main` reaches are not compiled. A file holding a law, its
  proof and an unreachable def calling the code compiles to the same C
  as the file without them, byte for byte (a small program, 2026-11-06).
- Checking proofs costs seconds: `blend.bend` 0.8 s alone, 3.6 s with
  its 14,444 lines of proofs (`PROOF.bend`); `spike/kernel.bend` 3.7 s,
  its `PROOF.bend` 5.8 s (`--check-only`, i7-6700).

## Findings

- **F1** — Blend writes each module's laws and proofs into files of
  their own. `blend/docs/decisions/blend-proofs-beside-code.md`:
  "Three files, as Bend's convention keeps laws and proofs apart from
  the code and from each other (the maintainer, 2026-11-04)", with
  `X_LAWS.bend` and `X_PROOF.bend` beside `X.bend`. Its context knew
  that Bend "erases proofs from what it compiles" and that "a law left
  open in a program's own file stops Bend running or building it". What
  it missed: a module's proofs so kept are checked by no one who
  imports the module, a package's least of all.
  *Verdict:* to revisit. The maintainer's proposal (2026-11-06): laws
  and proofs in the module's own `.bend`, as `Object.LAW.Name`, a law
  and its proof under one name, and `LAW.Name` for one outside any
  object; the separation the files gave comes from inheritance and
  from laws that cannot be overridden; a project keeps its own
  `LAWS.bend` and `PROOF.bend` where it wants them.
- **F2** — `blend/docs/decisions/blend-declares-witnessed.md`: a witness
  goes "never in the program: a witness is a second caller, which would
  make Bend split the definition into a segment of its own"; likewise
  `blend/README.md`, Declarations. A def no `main` reaches is not
  compiled, and one calling the code left the C unchanged (above).
  *Verdict:* the reason does not hold for a small program; to confirm on
  a module the size of the kernel's before relying on it.
- **F3** — The emission's three modes follow F1: `proof.parts`
  (`blend.bend`), the code imported as `Blend_0` and the laws as
  `Blend_Laws`, `ref.put.m`'s paths for the proofs' file, `tok.in.proof`
  naming the root's types through `Blend_0`, and the laws stated over
  the code's file alone (`sharing.counts`, `sharing.plain`,
  `markers.witness` and the joined `*.emitted` laws, which compose
  `emitted` with its laws' and proofs' parts). *Verdict:* one file
  would remove the modes; the laws that state them change with it,
  each a law change on main for the maintainer to approve.
- **F4** — A law left open stops a run of every program that loads its
  file. With laws in the module's file, a module with an unproven law
  cannot be run, nor imported. *Verdict:* a decision for the
  maintainer: Blend refusing to emit a law no concrete object proves,
  as an error of its own; or a law not yet proven kept apart until it
  is; or accepted, a law stated first stopping the program until its
  proof comes.
- **F5** — Every run and build that loads a module would check its
  proofs: some 3 s at Blend's scale, on top of a build of 13 s (Blend)
  or about 20 s (the kernel). `--verdict` stays the gate's.
  *Verdict:* acceptable, measured; recheck once a module's proofs grow.
- **F6** — Packages: laws and proofs in the module's file travel with
  it, are checked by whoever imports it, and serve them as lemmas, as
  bend-mathlib's do; publishing needs no file beyond the code's.
  `#2077` stays for a package's `.blend` sources.
- **F7** — glam-in-bend's own laws keep the project convention
  (`LAWS.bend`, `PROOF.bend` at the root; `spike/LAWS.bend`,
  `spike/PROOF.bend`): sound as it is. Its tools carry pairs only
  because Blend writes them: `scripts/check.sh` ("one beside every
  LAWS.bend: X_LAWS.bend beside X_PROOF.bend, as Blend writes a
  module's"), `scripts/one_law.py` (`X_MUTANTS.txt` beside
  `X_PROOF.bend`), `docs/Proving.md`. *Verdict:* follow F1; no change
  until Blend's.
- **F8** — Blend's own laws of `blend.bend` keep the project convention
  (`blend/LAWS.bend`, `blend/PROOF.bend`): untouched by F1.

## Next

The maintainer's decisions on F1 and F4; F2 measured on the kernel; then
a step in Blend's plan for the change, its laws restated with the
maintainer's approval.
