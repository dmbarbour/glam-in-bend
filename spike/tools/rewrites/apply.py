"""Patch a copy of spike/net.bend: insert a variant's apply_k before
interact.pays and route interact.pays through it."""
import sys
net, variant = sys.argv[1], sys.argv[2]
s = open(net).read()
code = open(variant).read()
anchor = "def interact.pays("
old = """  apply(R.rule(n3_kind(na), n3_kind(nb), rule_test(n3_kind(na), n3_kind(nb), pa, pb)),
    err_if(violation(n3_kind(na), n3_kind(nb), pa, pb), q), a, b, n3_kind(na), ext_of(na, nb), pa, pb)"""
new = """  apply_k(n3_kind(na), n3_kind(nb), rule_test(n3_kind(na), n3_kind(nb), pa, pb),
    err_if(violation(n3_kind(na), n3_kind(nb), pa, pb), q), a, b, ext_of(na, nb), pa, pb)"""
assert s.count(anchor) == 1 and s.count(old) == 1
s = s.replace(old, new).replace(anchor, code + anchor)
open(net, "w").write(s)
