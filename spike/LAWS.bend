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
