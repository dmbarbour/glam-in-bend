# The evaluator spike's laws (docs/plans/EvalSpike_2026-10-26.md).
# PROOF.bend proves them.

import Base
import ./store.bend as S
import ./rules.bend as R
import ./net.bend as N
import ./val.bend as V
import ./ctl.bend as CT
import ./kprim.bend as P
import ./freelist.bend as FL
import ./wiring.bend as W
import ./kplace.bend as KP
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

# LAW: the kernel's placement (kplace.bend: the pair's two slots, then the
# free list's heads) meets rewrite_placed_wired's conditions, its slots
# distinct, each the pair's own or free, one for each new node, when the
# free list is exact, agrees with the kinds on which slots are free
# (KP.in_step) and holds enough, and the pair's nodes are distinct and
# live.
# Record: net-nodes-double
law kernel_slots_ok:
  for +s: List<&2, FL.Slot>
  for +fh: Nat
  for +l: List<&2, Nat>
  for +ks: List<&2, R.NodeKind>
  for +a: Nat
  for +b: Nat
  for +k: Nat
  for hf: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}
  for hs: {KP.in_step(s, ks) == True{} : Bool}
  for hab: {R.nat_eq(a, b) == False{} : Bool}
  for hla: {W.is_free_kind(W.kind_at(ks, a)) == False{} : Bool}
  for hlb: {W.is_free_kind(W.kind_at(ks, b)) == False{} : Bool}
  for hen: {KP.has(Nat.sub(k, 2n), l) == True{} : Bool}
  {KP.kslots_ok(ks, a, b, k, FL.FL{s, fh, l}) == True{} : Bool}

# LAW: and leaves the free list exact: the slots it takes off the list,
# or the pair's slots it frees.
# Record: net-nodes-double
law kernel_free_ok:
  for +s: List<&2, FL.Slot>
  for +fh: Nat
  for +l: List<&2, Nat>
  for +ks: List<&2, R.NodeKind>
  for +a: Nat
  for +b: Nat
  for +k: Nat
  for hf: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}
  for hs: {KP.in_step(s, ks) == True{} : Bool}
  for hab: {R.nat_eq(a, b) == False{} : Bool}
  for hla: {W.is_free_kind(W.kind_at(ks, a)) == False{} : Bool}
  for hlb: {W.is_free_kind(W.kind_at(ks, b)) == False{} : Bool}
  {FL.ok(KP.kfree(a, b, k, FL.FL{s, fh, l})) == True{} : Bool}

# LAW: so a rewrite with the kernel's placement keeps a wired net wired.
# Record: net-nodes-double
law kernel_rewrite_wired:
  for +ks: List<&2, R.NodeKind>
  for +a: Nat
  for +b: Nat
  for +es: W.Peers
  for +c: List<&2, W.Ln>
  for +xs: List<&2, R.Spec>
  for +ls: List<&2, R.Link>
  for +p: R.Pat
  for +ls2: List<&2, R.Link>
  for +s: List<&2, FL.Slot>
  for +fh: Nat
  for +l: List<&2, Nat>
  for hw: {W.wired(ks, W.fends_in(W.Foc{ks, a, b, es, c}, p)) == True{} : Bool}
  for hc: {R.contract(p, ls) == Some{ls2} : Maybe<&2, List<&2, R.Link>>}
  for hr: {R.exact_in(W.kind_at(ks, a), W.kind_at(ks, b), p, R.RWire{xs, ls}) == True{} : Bool}
  for hf: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}
  for hs: {KP.in_step(s, ks) == True{} : Bool}
  for hab: {R.nat_eq(a, b) == False{} : Bool}
  for hla: {W.is_free_kind(W.kind_at(ks, a)) == False{} : Bool}
  for hlb: {W.is_free_kind(W.kind_at(ks, b)) == False{} : Bool}
  for hen: {KP.has(Nat.sub(List.length(&2, R.Spec, xs), 2n), l) == True{} : Bool}
  {W.wired(W.rp_kinds(ks, a, b, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l}), xs), W.ends(W.rp_links(es, c, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l}), ls2))) == True{} : Bool}

# LAW: and after it the free list and the kinds still agree, every new
# node's kind live: an exact free list, kinds in step with it and a wired
# net carry from one rewrite to the next.
# Record: net-nodes-double
law kernel_in_step:
  for +s: List<&2, FL.Slot>
  for +fh: Nat
  for +l: List<&2, Nat>
  for +ks: List<&2, R.NodeKind>
  for +a: Nat
  for +b: Nat
  for +xs: List<&2, R.Spec>
  for hf: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}
  for hs: {KP.in_step(s, ks) == True{} : Bool}
  for hab: {R.nat_eq(a, b) == False{} : Bool}
  for hla: {W.is_free_kind(W.kind_at(ks, a)) == False{} : Bool}
  for hlb: {W.is_free_kind(W.kind_at(ks, b)) == False{} : Bool}
  for hen: {KP.has(Nat.sub(List.length(&2, R.Spec, xs), 2n), l) == True{} : Bool}
  for hkl: {KP.kinds_live(W.kinds(xs)) == True{} : Bool}
  {KP.in_step(KP.slots_of(KP.kfree(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l})), W.rp_kinds(ks, a, b, KP.kslots(a, b, List.length(&2, R.Spec, xs), FL.FL{s, fh, l}), xs)) == True{} : Bool}


# LAW: every rule's new nodes have live kinds: a rewrite never makes a
# free node, which kernel_in_step takes as a hypothesis.
# Record: net-nodes-double
law rules_kinds_live:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +s: Bool
  {KP.rule_live(R.rule(a, b, s)) == True{} : Bool}

# LAW: so every step of the rule table at the kernel's placement leaves
# the free list and the kinds agreeing, given only the state's own
# conditions: an exact free list holding enough, kinds in step with it,
# the pair's nodes distinct and live.
# Record: net-nodes-double
law kernel_rules_in_step:
  for +s: List<&2, FL.Slot>
  for +fh: Nat
  for +l: List<&2, Nat>
  for +ks: List<&2, R.NodeKind>
  for +a: Nat
  for +b: Nat
  for +t: Bool
  for hf: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}
  for hs: {KP.in_step(s, ks) == True{} : Bool}
  for hab: {R.nat_eq(a, b) == False{} : Bool}
  for hla: {W.is_free_kind(W.kind_at(ks, a)) == False{} : Bool}
  for hlb: {W.is_free_kind(W.kind_at(ks, b)) == False{} : Bool}
  for hen: {KP.step_has(R.rule(W.kind_at(ks, a), W.kind_at(ks, b), t), l) == True{} : Bool}
  {KP.in_step(KP.slots_of(KP.step_free(a, b, R.rule(W.kind_at(ks, a), W.kind_at(ks, b), t), FL.FL{s, fh, l})), KP.step_kinds(ks, a, b, R.rule(W.kind_at(ks, a), W.kind_at(ks, b), t), FL.FL{s, fh, l})) == True{} : Bool}

# LAW: growing the storage keeps the free list exact: n free slots
# appended, each linking the next, the last the old head, the first now
# the head (kplace.bend's grow, as kprim.bend's grow.done and thread do
# with the old head none).
# Record: net-nodes-double
law free_list_grow:
  for +s: List<&2, FL.Slot>
  for +fh: Nat
  for +l: List<&2, Nat>
  for +n: Nat
  for hf: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}
  {FL.ok(KP.grow(FL.FL{s, fh, l}, n)) == True{} : Bool}

# LAW: and keeps the free list and the kinds agreeing, the kinds grown by
# as many free nodes.
# Record: net-nodes-double
law grow_in_step:
  for +s: List<&2, FL.Slot>
  for +fh: Nat
  for +l: List<&2, Nat>
  for +ks: List<&2, R.NodeKind>
  for +n: Nat
  for hs: {KP.in_step(s, ks) == True{} : Bool}
  {KP.in_step(KP.slots_of(KP.grow(FL.FL{s, fh, l}, n)), KP.grow_kinds(ks, n)) == True{} : Bool}

# LAW: growing changes no node's kind: past the end every node is free
# already.
# Record: net-nodes-double
law grow_kind_at:
  for +ks: List<&2, R.NodeKind>
  for +n: Nat
  for +i: Nat
  {W.kind_at(KP.grow_kinds(ks, n), i) == W.kind_at(ks, i) : R.NodeKind}

# LAW: so a wired net stays wired.
# Record: net-nodes-double
law grow_wired:
  for +ks: List<&2, R.NodeKind>
  for +n: Nat
  for +xs: List<&2, W.Pt>
  for hw: {W.wired(ks, xs) == True{} : Bool}
  {W.wired(KP.grow_kinds(ks, n), xs) == True{} : Bool}

# LAW: and the free list then holds at least the n slots grown, what the
# kernel's placement needs (KP.has).
# Record: net-nodes-double
law grow_has:
  for +s: List<&2, FL.Slot>
  for +fh: Nat
  for +l: List<&2, Nat>
  for +n: Nat
  {KP.has(n, KP.ghost(KP.grow(FL.FL{s, fh, l}, n))) == True{} : Bool}

# LAW: a linear fan, a copy or merge one of whose sides an eraser met,
# rewrites exactly where its full fan does: its rules are the full fan's
# with an eraser where the dead side was, run among the new nodes
# (rules.bend's Linear fans; heap-strategies.erasure.rules).
# Record: net-nodes-double
law rules_linear_rewrites:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +s: Bool
  {R.lin_rewrites(a, b, s) == True{} : Bool}

# LAW: and where the full fan's rule makes nodes, the linear fan's makes
# fewer: nothing is copied for the side erased.
# Record: net-nodes-double
law rules_linear_fewer:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +s: Bool
  {R.lin_fewer(a, b, s) == True{} : Bool}

# LAW: an eraser facing an auxiliary port runs an event (rules.bend's
# Events; heap-strategies.erasure.events), a rewrite of the node and the
# eraser that links exactly the ends left, under every pattern of peers
# inside the pair the arities allow, or none runs.
# Record: net-nodes-double
law events_exact:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +p: Nat
  {R.exact_pairs(a, b, R.event(a, b, p)) == True{} : Bool}

# LAW: an event's eraser faces a port of the other polarity, and every
# link the event makes joins a positive port to a negative one.
# Record: net-nodes-double
law events_polarized:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +p: Nat
  {R.ev_polarized(a, b, p) == True{} : Bool}

# LAW: an event leaves fewer ports than the node and the eraser had, so
# events end.
# Record: net-nodes-double
law events_shrink:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +p: Nat
  {R.ev_shrinks(a, b, p) == True{} : Bool}

# LAW: an event's new nodes have live kinds.
# Record: net-nodes-double
law events_kinds_live:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +p: Nat
  {KP.rule_live(R.event(a, b, p)) == True{} : Bool}

# LAW: a copy or merge an event makes linear is the kind whose derived
# rules have erased the side the event erased, so that it annihilates its
# duals position for position.
# Record: net-nodes-double
law events_side:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +p: Nat
  {R.ev_side(a, b, p) == True{} : Bool}

# LAW: an event that makes its node an eraser erased the node's last
# auxiliary port. Demand's walk reached each node on its path through an
# auxiliary port facing the principal of the node below, never an
# eraser's, so no event frees a node on the path, and the walk needs no
# exception (knet.bend's Events).
# Record: net-demand-whnf
law events_erase_last:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +p: Nat
  {R.ev_last(a, b, p) == True{} : Bool}

# LAW: no eraser's rule depends on the payload test, so the derivation's
# normalizer, which knows no payload, applies every erasure.
# Record: net-nodes-double
law erasers_untested:
  for +k: R.NodeKind
  {R.erasers_untested(k) == True{} : Bool}

# LAW: no rule links two ports of one of its new nodes: rewriting never
# makes a node face itself of its own.
# Record: net-nodes-double
law rules_no_self_links:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +t: Bool
  {R.no_self_links(a, b, t) == True{} : Bool}

# LAW: every event makes one node, linked only to external peers: the
# normalizer applies events in place, as the kernel places them, and an
# event of more nodes, should one be wanted, fails here first.
# Record: net-nodes-double
law events_one_node:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +p: Nat
  {R.ev_one_node(a, b, p) == True{} : Bool}

# LAW: every rule's new nodes take their payloads from the two nodes it
# rewrites, as the kernel's do: none takes a source composed of others,
# as the laws' graphs follow a payload through several rewrites, derived
# rules included.
# Record: fusions-as-components
law rules_base_sources:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +t: Bool
  {R.base_sources(a, b, t) == True{} : Bool}

# LAW: and every event's new node.
# Record: fusions-as-components
law events_base_sources:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +p: Nat
  {R.ev_base_sources(a, b, p) == True{} : Bool}

# LAW: a test comparing two payloads (R.test_eq: two fans' identities, an
# application's level and a function's, two controls' indexes) passes
# for a payload met by itself, as the reference interpreter tests it:
# the law checks' normalizer runs such a pair where both payloads have
# one source. A co-control's payload is a control's, as every rewrite
# keeps it (rules_keep_fits, events_keep_fits).
# Record: fusions-as-components
law tests_reflexive:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +p: V.Pay
  {N.test_refl(a, b, p) == True{} : Bool}

# LAW: rewriting keeps payloads fitting their kinds, as tests_reflexive
# takes them to: every control or co-control a rule makes carries a
# control's index and offset when the pair's own did, a control being
# made only from a control's payload.
# Record: fusions-as-components
law rules_keep_fits:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +t: Bool
  for +pa: V.Pay
  for +pb: V.Pay
  {N.keeps_fits(a, b, t, pa, pb) == True{} : Bool}

# LAW: and so does every event, none making a control.
# Record: fusions-as-components
law events_keep_fits:
  for +a: R.NodeKind
  for +b: R.NodeKind
  for +p: Nat
  for +pa: V.Pay
  {N.ev_keeps_fits(a, b, p, pa) == True{} : Bool}

# LAW: a loop from a node's auxiliary port to its other one joins ports of
# opposite polarity, which only a function has (body to variable, the
# identity) and an application (argument to result); a fan's two outputs,
# or two inputs, share a polarity, and a node of two ports has one
# auxiliary port. A loop from a principal port to an auxiliary one is a
# vicious circle on any node.
# Record: net-obvious-errors
law aux_loops:
  for +k: R.NodeKind
  {R.loops_aux(k) == True{} : Bool}

# LAW: a linear fan has its full fan's polarities at the ports it keeps,
# so its loops are its components'.
# Record: net-nodes-double
law fused_polarity:
  for +k: R.NodeKind
  {R.fused_pol(k) == True{} : Bool}

# LAW: beta where the redex's own ports are joined, as the kernel's
# interpreter rewrites it: a function whose body is its variable is the
# identity; an application whose result is its argument knots the
# function, its body feeding its variable, observed only where that
# variable is; both, nothing left.
# Record: net-nodes-double
law beta_loops:
  {R.beta_loops() == True{} : Bool}

# LAW: the identity function copied is two identities: the copy and the
# merge its rule makes meet, of one fan's identity, and annihilate, as
# the law checks' normalizer now knows (R.copy_identity).
# Record: fusions-as-components
law copy_identity:
  {R.copy_identity() == True{} : Bool}

# LAW: a fused node behaves as its components: a linear fan, whatever its
# principal meets, is stuck where its full fan with the dead side erased
# is, and otherwise leaves the same graph, both normalized by the
# derivation's normalizer and compared in a canonical order
# (R.fz_linear). A fused rule wrong, or a stuck pair that a fused one
# would reduce, fails it.
# Record: net-nodes-double
law linear_as_components:
  for +f: R.NodeKind
  for +v: R.NodeKind
  for +t: Bool
  {R.fz_linear(f, v, t) == True{} : Bool}

# LAW: and so does an event's pattern: the node and the eraser at the port
# it erases behave, against whatever the node's principal meets, as the
# node the event makes (R.fz_event). It fails for an application whose
# result is erased, a variable used outside its function's body seeing
# the difference, and for a call whose output is, its rule stuck against
# a function where an eraser's is not: neither makes an event. It implies
# events_side: a linear fan keeping the wrong side fails it.
# Record: net-nodes-double
law events_as_components:
  for +a: R.NodeKind
  for +p: Nat
  for +v: R.NodeKind
  for +t: Bool
  {R.fz_event(a, p, v, t) == True{} : Bool}

# LAW: and so does a run of controls: a control standing for a run of
# unit brackets, against whatever its principal meets but a control
# facing it, is stuck where its units in series are, and otherwise leaves
# what they leave, both normalized with controls fused where segments of
# one run meet in order (R.fz_runs). A run of two units stands for any
# split, the normalizer reading the bounds only to join them;
# run_splits holds their arithmetic. A control facing it is peeling's
# case.
# Record: fuse-control-runs
law runs_as_units:
  for +k: R.NodeKind
  for +v: R.NodeKind
  for +t: Bool
  {R.fz_runs(k, v, t) == True{} : Bool}

# LAW: so an event keeps a wired net wired, the node's peers inside the
# pair or not.
# Record: net-nodes-double
law events_keep_wired_in:
  for +ks: List<&2, R.NodeKind>
  for +a: Nat
  for +b: Nat
  for +es: W.Peers
  for +c: List<&2, W.Ln>
  for +q: Nat
  for +p: R.Pat
  for hv: {R.pat_ok(W.kind_at(ks, a), W.kind_at(ks, b), p) == True{} : Bool}
  for hw: {W.wired(ks, W.fends_in(W.Foc{ks, a, b, es, c}, p)) == True{} : Bool}
  {W.keeps_wired(ks, a, b, es, c, R.event(W.kind_at(ks, a), W.kind_at(ks, b), q), p) == True{} : Bool}

# LAW: and at the kernel's placement, the node's own slot first, an event
# leaves the free list and the kinds agreeing, given an exact free list,
# kinds in step with it, and the node and the eraser distinct and live.
# Record: net-nodes-double
law kernel_events_in_step:
  for +s: List<&2, FL.Slot>
  for +fh: Nat
  for +l: List<&2, Nat>
  for +ks: List<&2, R.NodeKind>
  for +a: Nat
  for +b: Nat
  for +q: Nat
  for hf: {FL.ok(FL.FL{s, fh, l}) == True{} : Bool}
  for hs: {KP.in_step(s, ks) == True{} : Bool}
  for hab: {R.nat_eq(a, b) == False{} : Bool}
  for hla: {W.is_free_kind(W.kind_at(ks, a)) == False{} : Bool}
  for hlb: {W.is_free_kind(W.kind_at(ks, b)) == False{} : Bool}
  for hen: {KP.step_has(R.event(W.kind_at(ks, a), W.kind_at(ks, b), q), l) == True{} : Bool}
  {KP.in_step(KP.slots_of(KP.step_free(a, b, R.event(W.kind_at(ks, a), W.kind_at(ks, b), q), FL.FL{s, fh, l})), KP.step_kinds(ks, a, b, R.event(W.kind_at(ks, a), W.kind_at(ks, b), q), FL.FL{s, fh, l})) == True{} : Bool}

# To do
# =====
#
# Laws wanted, not yet stated as laws: drafts, as comments, each with the
# step it waits for. A draft is no law; stating one is a law change like
# any other. The drafts name functions that do not exist yet.
#
# Growth in the kernel's order (heap-strategies.net.wiring.grow). The
# kernel grows inside alloc, when the list runs out partway through a
# rewrite's allocations, by its old size (kprim.bend's alloc.k); the
# laws above grow apart from a rewrite. KP.galloc(g, f), alloc growing f
# by g first if its list is empty, and KP.gkslots, KP.gkfree and
# KP.gkinds, the placement through it:
#
#   law kernel_galloc_ok:   FL.ok(f) and g at least 1 give
#                           FL.ok(KP.galloc(g, f)) and the slot taken free
#   law kernel_grow_in_step: kernel_in_step through KP.galloc, with no
#                           KP.has hypothesis
#   law kernel_grow_wired:  kernel_rewrite_wired likewise
#
# The kernel refining the models (spike-refinement). KA, an abstraction
# reading a kernel net H back as the models: KA.fl(h), its free list
# (headers, word 1, the head; the ghost list the walk from the head);
# KA.kinds(h), each node's kind from its header; KA.ends(h), the links'
# ends from words 1 to 3. Then each kernel operation does on the
# abstraction what the model's does:
#
#   law kernel_new_ok:      KA.fl(P.h_new()) is FL.ok, its kinds in step
#                           (KP.in_step) and wired (W.wired)
#   law kernel_alloc_refines: KA.fl of P.alloc(h)'s net is
#                           KP.galloc(wcap, KA.fl(h)), its node the slot
#                           taken, where KA.fl(h) is FL.ok
#   law kernel_free_refines: KA.fl(P.free(h, n)) is FL.free(KA.fl(h), n)
#                           for n in use
#   law kernel_rewrite_refines: the kernel's rewrite of a pair (knet.bend)
#                           reads back as W.rp_kinds and W.rp_links at
#                           KP.kslots, its links R.contract's
#   law kernel_audits_exact: KN.free_ok(h) and KN.wired_ok(h) hold exactly
#                           when FL.ok(KA.fl(h)), KP.in_step and W.wired
#                           hold of the abstraction
#
# Polarity of the kernel's own links (pairing-nets.check): fusion and
# peeling link a positive port to a negative one, by construction so far.
#
#   law fusion_polarized:   each link fusion or peeling makes joins ports
#                           of opposite polarity (R.port_pol)
