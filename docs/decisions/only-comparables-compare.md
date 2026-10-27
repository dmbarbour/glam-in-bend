# Only comparables compare

`only-comparables-compare` · maintainer · rev 79fd435

**Context.** The Rust bootstrap once compared more than the language
specifies: opaque values by identity, volume handles by the volume they
named. Definedness was spelled `x == {}`. Carried over from the Rust
decision log (2026-10-24).

**Decision.** Only comparables compare: numbers, and lists or dicts of
comparables, texts and binaries being lists and atoms dicts. Equality takes
any two comparables; two of different kinds are unequal, and dicts compare
structurally. Ordering is for numbers, lists and tuples. Comparing anything
else, directly or within a list or dict, is an error naming it
incomparable, never `false` and never `.fail`.

**Reasons.** An answer about an incomparable would observe what evaluation
must not: a resolver's or opaque value's identity, a function's code. An
error rather than `false` keeps a mistaken comparison from passing as a
verdict.

**Consequences.** A dict's members compare only where its keys match, so
`{a:f} == {b:g}` is `false` without forcing them. Definedness is asked with
`dict.defines` (`dict-empty-is-a-value`).

**Rule lives in:** Syntax.md, "Operators" (comparison).
