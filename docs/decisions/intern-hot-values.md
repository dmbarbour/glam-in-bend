# Hot shared values are interned

`intern-hot-values` · maintainer · rev e7899c5

**Context.** Bend counts the owners of a shared node in 24 bits, and an
overflow is a fail-stop. Values packed into one word (unit, small numbers)
are never counted, but a value referenced from millions of places, as `env`
may be, could overflow.

**Decision.** Intern values expected to be shared very widely, and pass
handles to them instead. The 2^24 limit is adequate in practice, though a
collector for shared data would be preferable.

**Consequences.** Interning needs a table that outlives its users; which
values qualify is decided by measurement.
