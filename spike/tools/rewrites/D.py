"""Variant D: C without the level assertions and fusion checks."""
import sys
p = sys.argv[1]
s = open(p).read()
pairs = [
("""    err_if(violation(n3_kind(na), n3_kind(nb), pa, pb), q), a, b, ext_of(na, nb), pa, pb)""",
 """    q, a, b, ext_of(na, nb), pa, pb)"""),
("""  fuse_all(ext_node(e0, a, b, ext_node(e1, a, b, ext_node(e2, a, b, ext_node(e3, a, b, Nil{})))),
    link(link(fresh(q, a, b), e0, e1), e2, e3))""",
 """  link(link(fresh(q, a, b), e0, e1), e2, e3)"""),
]
for old, new in pairs:
    assert s.count(old) == 1, old
    s = s.replace(old, new)
open(p, "w").write(s)
