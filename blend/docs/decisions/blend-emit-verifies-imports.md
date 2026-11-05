# Emission writes the modules named and verifies their imports

`blend-emit-verifies-imports` · maintainer · rev e08eff7

**Context.** A module's emission depends on nothing that imports it:
every definition is emitted and no top-level object can be extended, so
`emit` takes several modules at once (`README.md`). Emitting a
root's imports with it, one root doing a dozen jobs, was weighed. But
writing files a command did not name cannot last once packages come: a
package's emitted files are its own (`blend-packages`). Left alone, an
import emitted by no command goes stale unseen.

**Decision.** The maintainer (2026-11-05): `emit` writes only the
modules it names. An import none of them names is verified, lightweight
where that is robust and efficient: Blend emits it again in memory and
compares each file beside it, byte for byte, with what it would write;
a file stale, missing, or no longer emitted (a laws file of a module
that has no laws now) is reported, and the command writes nothing.
`emit --alone` emits the modules named individually, leaving their
imports unverified.

**Consequences.**
- Verification costs each unnamed import's emission again; a stamp of
  the sources' hash in each emitted header may make it cheaper
  (`blend-cli`).
- `bend blend.bend -- emit --alone ...` under Bend, whose CLI takes a
  dashed argument as its own; the built tool takes it directly.
- scripts/check_generated.sh, emitting each directory's modules,
  verifies the imports the other directories emit; check.sh holds
  a stale import to its error and `--alone` to its bypass.

**Rule lives in:** `README.md`, Status.
