#!/usr/bin/env python3
"""Are the nets terms.py lowers polarized? Every link must join a positive
port to a negative one, every port be linked exactly once, and the exposed
port be positive (the loader links it to the interface's negative
principal). Port polarities are rules.bend's (R.port_pol):

    Fn [+ fn, - result, + arg]    Ap [- ap, - arg, + result]
    Copy [- in, + left, + right]  Lift [- in, + out]
    data [+]                      EraN [-]

    polarity.py [COUNT]   the differential test's terms (spike/tools/
                          differential.sh): three seeds of COUNT, each
                          ending, lowered with levels, without, and unfused
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import terms  # noqa: E402

POL = {"fn": "+-+", "ap": "--+", "cp": "-++", "br": "-+", "cr": "-+", "ctl": "-+",
       "num": "+", "succ": "+", "plus": "+", "fma": "+", "era": "-"}


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


def main(argv):
    count = int(argv[0]) if argv else 200
    total = failing = 0
    for tail, label in (("succ 0", "succ"), ("(plus 1) 0", "plus"), ("(fma 1 1) 0", "fma")):
        for seed in (7, 11, 23):
            for text in terms.gen(count, seed, tail=tail):
                for levels, fused, mode in ((True, True, "levels"), (False, True, "labels"), (True, False, "unfused")):
                    net, root = terms.to_tpl(terms.parse(text), levels, fused)
                    total += 1
                    bad = check(net, root)
                    if bad:
                        failing += 1
                        if failing <= 5:
                            print(label, seed, mode, text, bad[:3])
    print(f"{total} nets, {failing} not polarized")
    return 1 if failing else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
