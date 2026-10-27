# The empty dict is a value; reading what is undefined is an error

`dict-empty-is-a-value` · maintainer · rev 79fd435

**Context.** In the Rust bootstrap, `{}` once meant both the empty dict and
"undefined": `{foo:{}}` was `{}`, a missing key read `{}`, and writing `{}`
erased. Whether a key was defined depended on its value, so equality,
union and every definedness check forced values. Carried over from the
Rust decision log (2026-10-24).

**Decision.**
- `{}` is the empty dict, a value like any other: `{foo:{}}` defines `foo`.
- Reading what is undefined is an error at the read, naming the path;
  nothing after the read runs. `.try_get` gives the value where defined and
  fails where not.
- Definedness is asked, never read: `dict.defines` answers `.r ()` or
  `.fail`, forcing only the dicts on the way; `dict.default` reads with a
  fallback.
- Removing is its own operation (`dict.remove`, `.del`), pruning the dicts
  it empties; union is shallow, and a key both operands define is an error.

**Reasons.** A key's presence known from keys alone forces no value, so
equality, union, patterns and definedness stay lazy. One meaning per
value: an empty dict that was also "absent" hid mistakes. An error where
the read happens reports a missing state before an effect acts on it.

**Consequences.** `::=` lost its meaning for undefined names
(`prior-update-disabled`).

**Rule lives in:** Syntax.md, "Dicts" and "Introductions and Overrides".
