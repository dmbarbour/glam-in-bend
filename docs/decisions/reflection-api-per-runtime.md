# Reflection APIs may differ per runtime

`reflection-api-per-runtime` · maintainer · rev 42da1ff

**Context.** The Rust runtime grew a large reflection API: machines, ports,
promises, volumes and obligations. Reflection is already version-specific
and outside reproducibility.

**Decision.** Beyond the standard effects, and enough `.env` access to tell
which assembler implementation runs, reflection APIs may differ between
runtimes. This implementation keeps what fits from the Rust API.

**Consequences.** Reflection code meant to be portable discriminates on the
implementation through `.env`.
