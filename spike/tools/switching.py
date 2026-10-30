#!/usr/bin/env python3
"""Could a switching criterion keep vicious circles from forming? For each
way of calling the three-port kinds (Fn, Ap, Copy, Merge) tensor or par,
asks whether every rewriting rule keeps Danos and Regnier's condition:
under every switching (each par node keeping one of its auxiliary ports,
a tensor node both), the net is acyclic. A rule keeps it when, for every
switching of its new nodes and every way the rest of the net could join
the pair's outer ends, a cycle on the right means one on the left under
some switching of the pair. If some assignment were kept by all rules, a
net built acyclic would stay so, and could have no vicious circle.

None is (pairing-library.switching in docs/plans/NetPairing_2026-10-26.md):
the fan commutations, which duplicate, break each one, as linear logic's
need for boxes predicts. Arity-1 and arity-2 kinds have one switching.

    bend spike/tools/rules_dump.bend > rules.txt
    switching.py rules.txt
"""
import itertools
import sys

AR = {"KFree": 0, "KFn": 3, "KAp": 3, "KCopy": 3, "KMerge": 3, "KData": 1, "KEraN": 1,
      "KEraP": 1, "KRoot": 1, "KCall": 2, "KLift": 2, "KLiftC": 2,
      "KCopyL": 2, "KCopyR": 2, "KMergeL": 2, "KMergeR": 2}
FANS = ["KFn", "KAp", "KCopy", "KMerge"]


def parse(line):
    """a dumped rule: the pair's kinds and test, new kinds, links"""
    head, specs, links = [p.strip() for p in line.split("|")]
    a, b, s = head.split()
    return a, b, s, specs.split(), [tuple(lk.split("-")) for lk in links.split()]


def choices(kind, cls):
    """the auxiliary ports a switching keeps, for each switching"""
    n = AR[kind] - 1
    if n <= 1 or cls.get(kind, "T") == "T":
        return [tuple(range(1, n + 1))]
    return [(p,) for p in range(1, n + 1)]


def partitions(xs):
    if not xs:
        yield []
        return
    for p in partitions(xs[1:]):
        for i in range(len(p)):
            yield p[:i] + [[xs[0]] + p[i]] + p[i + 1:]
        yield [[xs[0]]] + p


def cyclic(edges, part):
    """whether the edges close a cycle, the outer ends in each class of
    part joined outside"""
    up = {}

    def find(x):
        up.setdefault(x, x)
        while up[x] != x:
            up[x] = up[up[x]]
            x = up[x]
        return x
    for cl in part:
        for e in cl[1:]:
            up[find(("E", e))] = find(("E", cl[0]))
    for u, v in edges:
        ru, rv = find(u), find(v)
        if ru == rv:
            return True
        up[ru] = rv
    return False


def lhs_graphs(a, b, cls):
    """the pair under each switching: outer ends 0 and 1 face a's
    auxiliary ports, 2 and 3 b's (R.ext_ends)"""
    for ka in choices(a, cls):
        for kb in choices(b, cls):
            yield ([("A", "B")] + [("A", ("E", p - 1)) for p in ka]
                   + [("B", ("E", p + 1)) for p in kb])


def end(e, keep):
    if e[0] == "x":
        return ("E", int(e[1:]))
    j, p = [int(t) for t in e[1:].split(".")]
    return ("N", j) if p == 0 or p in keep[j] else ("D", j, p)


def broken(rule, cls):
    """a partition of the outer ends under which the rule makes a cycle
    the pair had not, or None"""
    a, b, _, xs, ls = rule
    outer = list(range(AR[a] - 1)) + list(range(2, AR[b] + 1))
    lhs = list(lhs_graphs(a, b, cls))
    for part in partitions(outer):
        if any(cyclic(g, part) for g in lhs):
            continue
        for keep in itertools.product(*[choices(k, cls) for k in xs]):
            if cyclic([(end(x, keep), end(y, keep)) for x, y in ls], part):
                return part
    return None


def main():
    rules = [parse(ln) for ln in open(sys.argv[1]).read().splitlines() if "|" in ln]
    kept = 0
    for combo in itertools.product("TP", repeat=len(FANS)):
        cls = dict(zip(FANS, combo))
        bad = [(r[0], r[1], r[2], p) for r in rules for p in [broken(r, cls)] if p is not None]
        kept += not bad
        name = " ".join(f"{k[1:]}={c}" for k, c in cls.items())
        print(name + ": " + ("kept by every rule" if not bad else
                             f"{len(bad)} rules break it, e.g. {bad[:3]}"))
    print(f"{len(rules)} rules, {kept} of {2 ** len(FANS)} assignments kept")


if __name__ == "__main__":
    main()
