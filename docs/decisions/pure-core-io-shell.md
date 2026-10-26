# A pure core behind a thin IO shell

`pure-core-io-shell` · maintainer · rev 42da1ff

**Context.** glam promises reproducible assembly: the same sources give the
same binary. Host concurrency was a main source of bugs in the Rust runtime.

**Decision.** The assembler is a pure core that answers either a result or a
request together with the state to resume from: read a file, fetch a remote
revision, wait for an event. A thin Bend IO shell fulfills each request and
resumes the core. Everything nondeterministic, interaction included, enters
through the shell as ordered input.

**Consequences.**
- An assembly result is a function of the inputs the core requested, which a
  law can state.
- glam's own concurrency (tasks, ports, promises, cuts) is a deterministic
  scheduler inside the core, not host threads.
- Reflection and interactive mode are deterministic relative to the shell's
  event log: a run can be replayed, though two live runs may differ.
  Modeling interaction (what counts as an event, and where events enter)
  waits for interactive mode.
- Bend's parallel calls speed up the core; they never decide results.
