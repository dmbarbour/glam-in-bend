# Handlers are assumed, not required, to obey the monad laws

`handlers-assumed-lawful` · maintainer · rev 42da1ff

**Context.** `or` desugars to `.alt`, and DistilledDesign says parentheses
only group it, yet under some reflection handlers `(x or y) or z` and
`x or (y or z)` behave differently.

**Decision.** This is no contradiction. Desugarings and the docs that
describe them assume a handler obeys the monad laws, but a user-defined
free-monad handler is not guaranteed to. Under a handler that breaks them,
grouping can be observable.

**Consequences.** Docs describe effects under lawful handlers and need not
caveat each grouping.
