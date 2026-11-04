# `^` sees the host a nested object is made for, frozen

`blend-frozen-host` · maintainer · rev dcf89d2

**Context.** A nested object is folded down its host's linearization
(`blend-nested`): `Outer2.Inner` is made of Outer's Inner and Outer2's
extension of it, mixins written in two hosts. The first implementation
walked the writer's host chain beside the final object's, taking the
final object's where the writer's was in its linearization. That gave
`Outer2.Inner` Outer2, and `object X extends Outer.In` Outer. But an
object reaching `Outer2.Inner` by its path saw Outer in the bodies Outer
wrote and Outer2 in Outer2's: one inherited object, two hosts. Two
consistent semantics were open: grafting, where `^` is always the host
of the object a body is emitted into, or a frozen host.

**Decision.** The maintainer (2026-11-04): frozen host. If the
inheritance names `Outer2.Inner`, that is what it gets, as a call of
`Outer2.foo(bar)` is independent of the caller's own inheritance; no
surprises. Three rules, glam's `.g` semantics:
1. A bare name binds to the final object's definition (`self`).
2. A nested object made for host X binds its mixins to X: `^` in their
   bodies is X, `^^` X's host, outward. A name in the introducing
   mixin's `extends` binds from X as well: `object Sub extends In`, made
   for Outer2, extends `Outer2.In`.
3. Inheritance never binds again: an object inheriting another, by its
   family or by a path, gets its bodies bound as they are; its own
   bodies see its own hosts.

**Consequences.**
- In family inheritance, `Outer2.Inner` sees Outer2, as before: the
  nested object is made again for each host, so that its host is the
  final one. `object Y extends Outer2.Inner` sees Outer2 in every body.
- A mixin's bodies are emitted once in an object. A mixin one object's
  linearization brings through two made objects of different hosts
  (`object Z extends Outer2.Inner, Outer3.Inner`, both made of Outer's
  Inner) would see two hosts at once: an error, as glam refuses one
  specification's name for two specifications. A diamond of hosts
  (`object Both extends Outer2, Outer3`) is one made object, one host.
- The samples `nested-reach` and `nested-diamond`.

**Rule lives in:** `blend/README.md`, The model.
