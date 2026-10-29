# The evaluator spike's laws (docs/plans/EvalSpike_2026-10-26.md).
# PROOF.bend proves them.

import Base
import ./store.bend as S
import ./rules.bend as R
import ./val.bend as V
import ./ctl.bend as CT
import ./kprim.bend as P
import ./freelist.bend as FL
import ./wiring.bend as W
import 0x78e347bf8d0582a322c01b02c727566f/nat.bend as MNat

# LAW: allocating conserves a page's slots: live, recycled and fresh slots
# still sum to the page's capacity.
# Record: store-pages
law alloc_conserves:
  for +m: S.Meta
  {S.meta_count(S.got_meta(S.meta_alloc(m))) == S.meta_count(m) : Nat}

# LAW: freeing conserves them too, a double free included.
# Record: store-pages
law free_conserves:
  for +m: S.Meta
  for +s: U32
  {S.meta_count(S.meta_free(m, s)) == S.meta_count(m) : Nat}

# LAW: every interaction rule links a positive port to a negative one, so
# reduction keeps a polarized net polarized.
law rules_polarized:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +s: Bool
  {R.polarized(a, b, R.rule(a, b, s)) == True{} : Bool}

# LAW: every interaction rule links each external peer and each new port
# exactly once, so reduction keeps every live port wired exactly once
# (rules_keep_wired, below, proves that of a model of the net).
law rules_linear:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +s: Bool
  {R.linear(a, b, R.rule(a, b, s)) == True{} : Bool}

# LAW: a builtin applied to its last argument by V.builtin_last, which
# matches the collected arguments where they lie, computes what V.builtin
# computes on them with that argument appended: the kernel's shortcut
# adds no semantics of its own.
law builtin_last_agrees:
  for +op: U32
  for +args: List<&2, V.Val>
  for +x: V.Val
  {V.builtin_last(op, args, x) == V.builtin(op, List.append(&2, V.Val, args, [x])) : V.Val}

# LAW: applying the kernel's flat form of a builtin given one number,
# V.VP1, computes what applying the VFun it stands for computes, seen
# through V.norm.
law vp1_agrees:
  for +op: U32
  for +need: U32
  for +a: U32
  for +x: V.Val
  {V.norm(V.apply_fn(V.VP1{op, need, a}, x)) == V.norm(V.apply_fn(V.VFun{op, need, [V.VNum{a}]}, x)) : V.Val}

# LAW: likewise for two numbers, V.VP2.
law vp2_agrees:
  for +op: U32
  for +need: U32
  for +a: U32
  for +b: U32
  for +x: V.Val
  {V.norm(V.apply_fn(V.VP2{op, need, a, b}, x)) == V.norm(V.apply_fn(V.VFun{op, need, [V.VNum{a}, V.VNum{b}]}, x)) : V.Val}

# LAW: V.norm leaves no placeholder (VP1, VP2) at the top of a value, only
# a free slot, which the kernel reports as an error wherever it reads one
# as a value.
law norm_not_placeholder:
  for +v: V.Val
  {V.is_ph(V.norm(v)) == V.is_free(v) : Bool}

# LAW: applying a value whose collected arguments hold no placeholder, to
# anything but a free slot, yields one whose collected arguments hold
# none: each argument is collected normalized.
law apply_keeps_clean:
  for +f: V.Val
  for +x: V.Val
  {Bool.or(Bool.or(Bool.not(V.clean(f)), V.is_free(x)), V.clean(V.apply_fn(f, x))) == True{} : Bool}

# LAW: normalizing keeps a value's collected arguments free of
# placeholders.
law norm_keeps_clean:
  for +v: V.Val
  {Bool.or(Bool.not(V.clean(v)), V.clean(V.norm(v))) == True{} : Bool}

# LAW: where the payload test decides whether A meeting B is stuck, the
# rule that rewrites them makes at most one node, so the kernel's demand
# walk tells a rewrite from a stuck pair by B's slot alone.
# Record: net-demand-whnf
law rules_tested_small:
  for +a: R.NodeKind
  for +b: R.NodeKind
  {R.tested_small(a, b) == True{} : Bool}

# LAW: unit brackets at n, n + 1, ..., n + b - 1, crossed in turn, move a
# level as one control raising levels above n by b: a run, as fusion makes
# it, does to every level what its units do.
# Record: fuse-control-runs
law units_are_run:
  for +b: Nat
  for +n: Nat
  for +j: Nat
  {CT.units(b, n, j) == CT.raise(n, b, j) : Nat}

# LAW: a run of k + r units at n is k at n then r at n + k: fusing two
# runs where the second begins at the first's end, or peeling one apart
# there, changes nothing a level crossing them sees.
# Record: fuse-control-runs
law run_splits:
  for +k: Nat
  for +r: Nat
  for +n: Nat
  for +j: Nat
  {CT.raise(Nat.add(k, n), r, CT.raise(n, k, j)) == CT.raise(n, Nat.add(k, r), j) : Nat}

# LAW: facing runs at one index, peeled, leave what their units would,
# the inner pairs cancelling one by one.
# Record: fuse-control-runs
law peel_pairs_units:
  for +c: Nat
  for +l: Nat
  for +n: Nat
  {CT.pair_off(c, l, n) == CT.peel(n, c, l) : CT.Left}

# LAW: the kernel's raise is the model's: a level j through a control
# raising levels above n by b (kprim.bend's lift.go, U32), read as a Nat,
# is CT.raise of their Nat values, whenever j + b fits a U32. The kernel's
# own U32 arithmetic proved against the model, through bend-mathlib's laws
# relating U32 to Nat (docs/BendIssues.md, "Reasoning about U32 in
# proofs"); lift_decoded below discharges the fit for decoded fields.
# Record: fuse-control-runs
law lift_raise:
  for +n: U32
  for +b: U32
  for +j: U32
  for h: MNat.lt(Nat.add(U32.to_nat(j), U32.to_nat(b)), Nat.pow(2n, 32n))
  {U32.to_nat(P.lift.go(U32.is_gt(j, n), True{}, b, j)) == CT.raise(U32.to_nat(n), U32.to_nat(b), U32.to_nat(j)) : Nat}

# LAW: a level decoded from a header has 24 bits: kprim.bend's fld, a U32
# division by 2^8, read as a Nat, lies below 2^24.
# Record: net-nodes-double
law fld_bits:
  for +h: U32
  MNat.lt(U32.to_nat(P.fld(h)), Nat.pow(2n, 24n))

# LAW: an offset's amount has 31 bits: kprim.bend's off_by, a U32
# remainder by 2^31, read as a Nat, lies below 2^31.
# Record: net-nodes-double
law off_by_bits:
  for +o: U32
  MNat.lt(U32.to_nat(P.off_by(o)), Nat.pow(2n, 31n))

# LAW: the kernel raises a decoded level as the model does: lift_raise
# without its hypothesis, a 24-bit level and a 31-bit amount summing
# within a U32.
# Record: fuse-control-runs
law lift_decoded:
  for +n: U32
  for +o: U32
  for +h: U32
  for up: {P.off_up(o) == True{} : Bool}
  {U32.to_nat(P.lift(n, o, P.fld(h))) == CT.raise(U32.to_nat(n), U32.to_nat(P.off_by(o)), U32.to_nat(P.fld(h))) : Nat}

# LAW: the kernel's level check suffices: a raise of a decoded level that
# lift_wraps passes has 24 bits, so it fits the field it is written to.
# Record: fuse-control-runs
law lift_fits:
  for +n: U32
  for +o: U32
  for +h: U32
  for up: {P.off_up(o) == True{} : Bool}
  for ok: {P.lift_wraps(n, o, P.fld(h)) == False{} : Bool}
  MNat.lt(U32.to_nat(P.lift(n, o, P.fld(h))), Nat.pow(2n, 24n))

# LAW: taking a slot keeps the net's free list exact. In the free-list
# model (freelist.bend, the kernel's nodes and links in Nat), FL.ok says
# the links from the head spell a list holding every free slot and no
# slot twice: each free node is on the free list exactly once, and no
# node in use is. alloc keeps it.
# Record: net-nodes-double
law free_list_alloc:
  for f: FL.FL
  for ok: {FL.ok(f) == True{} : Bool}
  {FL.ok(FL.alloc(f)) == True{} : Bool}

# LAW: freeing a slot in use keeps the free list exact.
# Record: net-nodes-double
law free_list_free:
  for +s: List<&2, FL.Slot>
  for +fh: Nat
  for +l: List<&2, Nat>
  for +i: Nat
  for live: {FL.in_use(s, i) == True{} : Bool}
  for ok: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}
  {FL.ok(FL.free(FL.FL{s, fh, l}, i)) == True{} : Bool}

# LAW: the slot alloc takes, the head's, is free: allocation never takes a
# node in use.
# Record: net-nodes-double
law free_list_takes_free:
  for +s: List<&2, FL.Slot>
  for +i: Nat
  for l: List<&2, Nat>
  for ok: {FL.ok(FL.FL{s, 1n+i, l}) == True{} : Bool}
  {FL.is_free(FL.get(s, i)) == True{} : Bool}

# LAW: every interaction rule links exactly the ends it must, none twice:
# its links' ends, listed, repeat none, and are the ends rules_linear
# expects (R.exact), the form the net's wiring law takes.
# Record: net-nodes-double
law rules_exact:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +s: Bool
  {R.exact(a, b, R.rule(a, b, s)) == True{} : Bool}

# LAW: a rewrite keeps the net's wiring exact. In the wiring model
# (wiring.bend, the net's node kinds and links in Nat), W.wired says the
# links' ends name each live port once and nothing else: every live node is
# referenced once at each port, and no dead one is. Replacing an active
# pair a >< b by a rule's new nodes and links, the rule exact by R.exact,
# keeps it.
# Record: net-nodes-double
law rewrite_wired:
  for +ks: List<&2, R.NodeKind>
  for +a: Nat
  for +b: Nat
  for +es: W.Peers
  for +c: List<&2, W.Ln>
  for +xs: List<&2, R.Spec>
  for +ls: List<&2, R.Link>
  for hw: {W.wired(ks, W.fends(W.Foc{ks, a, b, es, c})) == True{} : Bool}
  for hr: {R.exact(W.kind_at(ks, a), W.kind_at(ks, b), R.RWire{xs, ls}) == True{} : Bool}
  {W.wired(W.rw_kinds(ks, a, b, xs), W.ends(W.rw_links(ks, es, c, ls))) == True{} : Bool}

# LAW: so every step of the rule table keeps a wired net wired: the
# rewrite of an active pair by the rule its kinds select, or a stuck pair
# left as it was.
# Record: net-nodes-double
law rules_keep_wired:
  for +ks: List<&2, R.NodeKind>
  for +a: Nat
  for +b: Nat
  for +es: W.Peers
  for +c: List<&2, W.Ln>
  for +s: Bool
  for hw: {W.wired(ks, W.fends(W.Foc{ks, a, b, es, c})) == True{} : Bool}
  {W.wired(W.step_kinds(ks, a, b, R.rule(W.kind_at(ks, a), W.kind_at(ks, b), s)), W.step_ends(ks, a, b, es, c, R.rule(W.kind_at(ks, a), W.kind_at(ks, b), s))) == True{} : Bool}

# LAW: a peer of the pair may be a port of the pair itself (a's auxiliary
# port linked to b's, or to a's other). Under every pattern of such peers
# the pair's arities allow (R.pat_ok), the links the kernel makes of a
# rule's (R.contract, as knet.bend's link_plain and link_pairs) link
# exactly the ends left, the outside peers and the new ports, none twice;
# or the kernel reports an error, which rules_pairs_total rules out.
# Record: net-nodes-double
law rules_pairs_exact:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +s: Bool
  {R.exact_pairs(a, b, R.rule(a, b, s)) == True{} : Bool}

# LAW: with peers inside the pair as pattern p says, the focused net
# listing only the outside ones (W.fends_in), the rewrite by the links the
# kernel makes keeps a wired net wired.
# Record: net-nodes-double
law rewrite_pairs_wired:
  for +ks: List<&2, R.NodeKind>
  for +a: Nat
  for +b: Nat
  for +es: W.Peers
  for +c: List<&2, W.Ln>
  for +xs: List<&2, R.Spec>
  for +ls: List<&2, R.Link>
  for +p: R.Pat
  for +ls2: List<&2, R.Link>
  for hw: {W.wired(ks, W.fends_in(W.Foc{ks, a, b, es, c}, p)) == True{} : Bool}
  for hc: {R.contract(p, ls) == Some{ls2} : Maybe<&2, List<&2, R.Link>>}
  for hr: {R.exact_in(W.kind_at(ks, a), W.kind_at(ks, b), p, R.RWire{xs, ls}) == True{} : Bool}
  {W.wired(W.rw_kinds(ks, a, b, xs), W.ends(W.rw_links(ks, es, c, ls2))) == True{} : Bool}

# LAW: so every step of the rule table, its pair's peers inside it or
# not, keeps a wired net wired, unless the kernel reports an error, which
# rules_pairs_total rules out.
# Record: net-nodes-double
law rules_keep_wired_in:
  for +ks: List<&2, R.NodeKind>
  for +a: Nat
  for +b: Nat
  for +es: W.Peers
  for +c: List<&2, W.Ln>
  for +s: Bool
  for +p: R.Pat
  for hv: {R.pat_ok(W.kind_at(ks, a), W.kind_at(ks, b), p) == True{} : Bool}
  for hw: {W.wired(ks, W.fends_in(W.Foc{ks, a, b, es, c}, p)) == True{} : Bool}
  {W.keeps_wired(ks, a, b, es, c, R.rule(W.kind_at(ks, a), W.kind_at(ks, b), s), p) == True{} : Bool}

# LAW: the kernel joins any rule's links under any pattern of peers inside
# the pair its arities allow without an error: a closed loop the rule's
# links and the pair's own make vanishes, and no chain through the pair
# reaches outside at both ends.
# Record: net-nodes-double
law rules_pairs_total:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +s: Bool
  {R.total_pairs(a, b, R.rule(a, b, s)) == True{} : Bool}

# LAW: wherever the new nodes go, the rewrite keeps a wired net wired, as
# long as their slots are distinct and each is the pair's own or free: the
# kernel's placement, the pair's two slots then the free list's
# (kprim.bend's renode and alloc), among them, rewrite_pairs_wired's
# appended nodes another (W.range).
# Record: net-nodes-double
law rewrite_placed_wired:
  for +ks: List<&2, R.NodeKind>
  for +a: Nat
  for +b: Nat
  for +es: W.Peers
  for +c: List<&2, W.Ln>
  for +xs: List<&2, R.Spec>
  for +ls: List<&2, R.Link>
  for +p: R.Pat
  for +ls2: List<&2, R.Link>
  for +ss: List<&2, Nat>
  for hw: {W.wired(ks, W.fends_in(W.Foc{ks, a, b, es, c}, p)) == True{} : Bool}
  for hc: {R.contract(p, ls) == Some{ls2} : Maybe<&2, List<&2, R.Link>>}
  for hr: {R.exact_in(W.kind_at(ks, a), W.kind_at(ks, b), p, R.RWire{xs, ls}) == True{} : Bool}
  for hss: {W.nodup_nat(ss) == True{} : Bool}
  for hok: {W.slots_ok(ks, a, b, ss) == True{} : Bool}
  for hlen: {List.length(&2, Nat, ss) == List.length(&2, R.Spec, xs) : Nat}
  {W.wired(W.rp_kinds(ks, a, b, ss, xs), W.ends(W.rp_links(es, c, ss, ls2))) == True{} : Bool}

