# Demanding a void is an outcome of its own

`net-void-demanded` · maintainer · rev 479113d

**Context.** A void is nothing supplied where a value is wanted. Erasing
a function leaves one as its variable, and a user supplies one by wiring
a `.copy 0` port to a consumer; applying, copying or operating on a void
gives voids. Demand that found a void at the interface ended done with no
value, as it does facing a function. Reporting it instead as a variable
used outside its function's body (`net-scoped-arguments`) assumed every
void came from erasing a function, which a user's does not.

**Decision.** Demand that finds a void at the interface reports a void
demanded, an outcome of its own beside a value, a cycle and a variable
used outside its body: it says what demand found, and nothing of where
the void came from. Supplying a void stays allowed.

**Consequences.**
- A user's void surfaces where demand reaches it, not only at the bridge
  that takes a net's result (`net_arity`), which refuses a non-data
  normal form.
- On a net refused when built, plain and collecting demand may still end
  differently, both in error: demand reports the variable, or a
  collection that erased its function leaves a void demanded.
- One test where demand reaches the interface; the walk pays nothing.

**Rule lives in:** `docs/Design.md`, Interaction Nets.
