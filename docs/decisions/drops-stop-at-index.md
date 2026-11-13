# A drop lowers levels above its index, to the index at the lowest

`drops-stop-at-index` · maintainer · rev 8810386

**Context.** A control (n, up, by) moves levels above n by `by`, up or
down. A drop computed `j - by` for a level j above n, so a drop by more
than one more than its index took a level below zero, and the kernel's
U32 subtraction wrapped silently. No net met one: lowering emits only
drops by one, peeling splits raises only, fusion joins raises only, and
rules copy a control's amount unchanged. But the loader and the splice
accept any amount, and the shift law for drops had to assume a bound
(`raise_lift_down`). The second reviewer of the Levels review found the
unguarded subtraction (`docs/reviews/LevelsFable_2026-11-12.md`, L8).
Two remedies were offered: define a drop so that it cannot underflow, or
guard that every drop is a unit and prove that nothing makes another.

**Decision.** The maintainer (2026-11-13): "Option 1": a drop at n by b
moves a level j above n to max(n, j - b), never below n. This is the
maintainer's framing from NetPairing (`pairing-gal`): "a control (n, k)
leaves levels up to n alone and moves those above to max(n, j + k)". For
a drop by one it is the drop as before.

**Consequences.**
- No amount makes a level wrap. The model (`V.drop_by` in
  `spike/val.bend`) and the kernel (`P.drop_by` in `spike/kprim.bend`)
  clamp the amount passed to the drop's arm to j - n.
- The kernel's drop is proved to be max(n, j - b), with no hypothesis
  (law `lift_drop`), and the shift law holds for drops of any amount
  (`raise_lift_drop`). It replaced `raise_lift_down`, whose premise
  bounded a drop's amount, deleted with the maintainer's approval
  (2026-11-13).
- A drop by more than one now means something: b unit drops at one
  index, which drop fusion would make (`pairing-fusion.drops` in
  `docs/plans/NetPairing_2026-10-26.md`). Drops still do not fuse
  (`fuse-control-runs`).
- Instructions moved -1.1% to +0.6% on the spot workloads (analysis
  store run 319 against 318).

**Rule lives in:** `spike/LAWS.bend`, laws `lift_drop` and
`raise_lift_drop`.
