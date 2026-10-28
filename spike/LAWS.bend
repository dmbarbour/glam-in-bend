# The evaluator spike's laws (docs/plans/EvalSpike_2026-10-26.md).
# PROOF.bend proves them.

import Base
import ./store.bend as S
import ./rules.bend as R
import ./val.bend as V

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
# exactly once, so reduction keeps every live port wired exactly once.
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
