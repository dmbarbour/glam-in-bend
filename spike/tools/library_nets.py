#!/usr/bin/env python3
"""The library's entries as nets in load.bend's format, for
spike/runmode.bend: every mode an entry names, a row a mode.

    library_nets.py OUT NAME...

writes OUT/nets.txt.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import library  # noqa: E402
import terms  # noqa: E402


def main(argv):
    sys.setrecursionlimit(100000)
    if len(argv) < 2:
        print(__doc__.strip())
        return 2
    out = os.path.abspath(argv[0])
    os.makedirs(out, exist_ok=True)
    cs = library.cases(library.entries(open(library.LIBRARY).read().split("\n")), set(argv[1:]))
    rows = [(f"{c.entry} {c.mode}", c.value if isinstance(c.value, int) else None, c.net, c.root) for c in cs]
    terms.write_nets(out, rows)
    print(len(rows), "nets in", os.path.join(out, "nets.txt"))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
