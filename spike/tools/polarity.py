#!/usr/bin/env python3
"""Are the nets terms.py lowers polarized, free of vicious circles, and
scoped? Every link must join a positive port to a negative one, every port
be linked exactly once, and the exposed port be positive (the loader links
it to the interface's negative principal); no principal path may close
(vicious), an obvious error glam's construction refuses
(net-obvious-errors); and no function's argument may be used outside its
body (unscoped, net-scoped-arguments). Port polarities are rules.bend's
(R.port_pol):

    Fn [+ fn, - result, + arg]    Ap [- ap, - arg, + result]
    Copy [- in, + left, + right]  Lift [- in, + out]
    data [+]                      EraN [-]   void, EraP [+]
    LiftC [+ out, - in] (no lowering makes one; spike/library.txt may)

    polarity.py [COUNT]   the differential test's terms (spike/tools/
                          differential.sh): three seeds of COUNT, each
                          ending, lowered with levels, without, and unfused
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import terms  # noqa: E402

POL = {"fn": "+-+", "ap": "--+", "cp": "-++", "br": "-+", "cr": "-+", "ctl": "-+", "ctlc": "+-",
       "num": "+", "succ": "+", "plus": "+", "fma": "+", "era": "-", "void": "+"}


def check(net, root):
    """the problems with one lowered net, as strings"""
    bad = []
    seen = {}
    for a, b in net.links:
        for end in (a, b):
            seen[end] = seen.get(end, 0) + 1
        pa = POL[net.nodes[a[0]][0]][a[1]]
        pb = POL[net.nodes[b[0]][0]][b[1]]
        if pa == pb:
            bad.append(f"link {a}-{b} joins {pa} to {pb}")
    for i, (kind, _) in enumerate(net.nodes):
        for p in range(len(POL[kind])):
            want = 0 if (i, p) == tuple(root) else 1
            if seen.get((i, p), 0) != want:
                bad.append(f"port {(i, p)} of {kind} linked {seen.get((i, p), 0)} times, not {want}")
    if POL[net.nodes[root[0]][0]][root[1]] != "+":
        bad.append(f"exposed port {root} is negative")
    return bad


def vicious(net, root):
    """the vicious circles of length one or more in a net (Lafont,
    Interaction Combinators, 1997, section 1.6): closed principal paths,
    each cell's principal port linked to an auxiliary port of the next.
    None can ever be eliminated, since no cell on one can interact first.
    A cyclic wire, a vicious circle of length zero, has no ports, so no net
    is built with one; rewriting makes them (heap-strategies.net.wiring.
    circles). Returns each circle's cells, from its least."""
    peer = {}
    for a, b in net.links:
        peer[tuple(a)] = tuple(b)
        peer[tuple(b)] = tuple(a)
    # each cell's successor on a principal path, if any
    nxt = {}
    for i in range(len(net.nodes)):
        q = peer.get((i, 0))
        if q is not None and q[1] != 0:
            nxt[i] = q[0]
    circles, state = [], {}
    for start in range(len(net.nodes)):
        path, i = [], start
        while i is not None and i not in state:
            state[i] = start
            path.append(i)
            i = nxt.get(i)
        if i is not None and state[i] == start:
            cyc = path[path.index(i):]
            k = cyc.index(min(cyc))
            circles.append(cyc[k:] + cyc[:k])
    return circles


def unscoped(net, root):
    """the functions whose argument the exposed port can need other than
    through their body (net-scoped-arguments): on the graph of ports, an
    output needing its node's inputs and an input the output linked to it,
    a function's result port must dominate its argument port from the
    exposed port, as a definition dominates its uses in SSA. Dominators by
    Cooper, Harvey and Kennedy's iteration ("A Simple, Fast Dominance
    Algorithm", 2001), near linear on such graphs. Returns the functions'
    cells; an argument the exposed port never needs is scoped."""
    peer = {}
    for a, b in net.links:
        peer[tuple(a)] = tuple(b)
        peer[tuple(b)] = tuple(a)

    def needs(v):
        i, p = v
        pol = POL[net.nodes[i][0]]
        if pol[p] == "+":
            return [(i, q) for q in range(len(pol)) if pol[q] == "-"]
        w = peer.get(v)
        return [w] if w is not None else []

    start = tuple(root)
    # the ports the exposed port needs, in reverse postorder
    seen, post, stack = {start}, [], [(start, iter(needs(start)))]
    while stack:
        v, it = stack[-1]
        for w in it:
            if w not in seen:
                seen.add(w)
                stack.append((w, iter(needs(w))))
                break
        else:
            stack.pop()
            post.append(v)
    order = post[::-1]
    index = {v: k for k, v in enumerate(order)}
    preds = {v: [] for v in order}
    for v in order:
        for w in needs(v):
            preds[w].append(v)
    idom = {start: start}
    changed = True
    while changed:
        changed = False
        for v in order[1:]:
            ps = [p for p in preds[v] if p in idom]
            new = ps[0]
            for p in ps[1:]:
                a, b = new, p
                while a != b:
                    while index[a] > index[b]:
                        a = idom[a]
                    while index[b] > index[a]:
                        b = idom[b]
                new = a
            if idom.get(v) != new:
                idom[v] = new
                changed = True
    bad = []
    for i, (kind, _) in enumerate(net.nodes):
        if kind != "fn" or (i, 2) not in idom:
            continue
        v = (i, 2)
        while v != start and v != (i, 1):
            v = idom[v]
        if v != (i, 1):
            bad.append(i)
    return bad


def main(argv):
    count = int(argv[0]) if argv else 200
    total = failing = 0
    for tail, label in (("succ 0", "succ"), ("(plus 1) 0", "plus"), ("(fma 1 1) 0", "fma")):
        for seed in (7, 11, 23):
            for text in terms.gen(count, seed, tail=tail):
                for levels, fused, mode in ((True, True, "levels"), (False, True, "labels"), (True, False, "unfused")):
                    net, root = terms.to_tpl(terms.parse(text), levels, fused)
                    total += 1
                    bad = (check(net, root) + [f"vicious circle through cells {c}" for c in vicious(net, root)]
                           + [f"function {i}'s argument used outside its body" for i in unscoped(net, root)])
                    if bad:
                        failing += 1
                        if failing <= 5:
                            print(label, seed, mode, text, bad[:3])
    print(f"{total} nets, {failing} not polarized, with a vicious circle, or unscoped")
    return 1 if failing else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
