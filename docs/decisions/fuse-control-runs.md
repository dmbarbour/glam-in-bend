# Controls fuse only into runs of raises, peeled where a partner meets them

`fuse-control-runs` · agent · rev 8786a68

**Context.** Control fusion (NetPairing) merged any two controls in
series whose composite moves every level as the two do: raises, a raise
and a drop, a raise and a drop that cancel. Reduced in another order, as
demand does, it read wrong values on 8 of 600 random leveled terms that
unfused levels get right. A one-wire model of controls, every reduction
order enumerated, showed why. Facing controls cancel only when equal, so
a composite has lost what a partner needs: a run raising by 2 meeting the
partner of its first unit swaps past it instead of cancelling, two
composites equal as maps but split differently cancel when their parts
would not, and a raise fused with a drop into nothing hides the unit a
facing control was to cancel. Asperti and Chroboczek's safe operators
merge only controls no partner can reach; Fable's review (2026-10-28)
gave the same account.

**Decision.** Two controls fuse only when both raise and the second's
index is where the first's raise ends, n2 = n1 + k1: the composite
(n1, k1 + k2) then stands for exactly one run of unit brackets n1, n1 +
1, and so on. Where a Lift and a LiftC meet at one index as different
controls, the run that raises further is peeled before the rule applies:
it keeps as many units facing as the other raises, which then cancel, or
one unit facing a drop, which crosses it, and a new control takes the
rest from the index where the kept units end. Nothing else fuses until a
safety criterion licenses it.

**Consequences.**
- Fused and unfused reductions agree in the model on every start
  (exhaustive to four controls, sampled to ten). On the 3,600 random
  terms of the differential test (analysis store run 27), spike,
  interpreter and generated rewrites agree on every value and count, and
  demand gets every leveled term right in no more interactions than the
  full reduction.
- Peeling never fires on nets lowering makes without runtime fusion:
  there, facing controls of one index are always equal.
- Peeling runs in the generated rewrite for a Lift meeting a LiftC, and
  in the interpreter's branch for the pair, so no other pair pays for it:
  the full reduction's instructions move -0.9% to +0.4% in the default
  and profile-guided builds, +1.2% to +2.4% forced inline. Tested in
  `go`, on every pair, it cost 2% to 12% whichever way it was written.
- Random leveled terms make 2.6 times the interactions the unsound
  fusion made, 22% fewer than none; `m 2 succ 0` is unchanged. The loss
  sits where controls accumulate: one term in 600 is 41% of the cost,
  25.8 times its old count. Recovering it is the safe operators' work: a
  safety bit set where a control's box is closed for good.
- The laws `units_are_run`, `run_splits` and `peel_pairs_units` hold the
  arithmetic of runs to their units; that the unit system is confluent,
  and that runs simulate it wherever they meet other nodes, rests on the
  model's enumeration and the differential tests.

**Rule lives in:** `spike/val.bend` (`V.compose`), `spike/kprim.bend`
("Fusing controls", "Peeling"), `spike/tools/gen_krules.bend` (the
pair's peeled rewrite), `spike/net.bend` ("Peeling"); `pairing-fusion` in
`docs/plans/NetPairing_2026-10-26.md`.
