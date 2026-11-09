# Diagnostics are worded for use, the samples' expectations with them

`diagnostic-wording-ours` · maintainer · rev c7a90cd

**Context.** The invalid samples came from the Rust bootstrap with
`.expect` files naming each error's line and substrings of its message
(`samples/README.md`). The hello ladder's assembler matched those
wordings as it reached them. The maintainer gave the Rust bootstrap
little direction on error messages.

**Decision.** The maintainer (2026-11-09): error messages are to be
useful to whoever reads them, the agents working on glam included, and
may be improved at will. A sample's `.expect` substrings change with the
message they test; the line an error is reported at, and that it is an
error at all, stay as the sample states unless the sample was wrong.

**Consequences.**
- A wording inherited from the Rust bootstrap is a starting point, not a
  specification.
- A better message changes its `.expect` line in the same commit.

**Rule lives in:** `samples/README.md`, Expectations.
