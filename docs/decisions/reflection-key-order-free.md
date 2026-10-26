# Reflection may list dict keys in any order

`reflection-key-order-free` · maintainer · rev e7899c5

**Context.** glam exposes no dict key order; only reflection lists keys. A
dict representation wants whatever key order suits it.

**Decision.** Reflection may list keys in any order the implementation
chooses.

**Consequences.** Dicts may use any canonical internal order, or none. Within
the pure core the order is still deterministic.
