"""Workloads in which cursors are the cost (the Cells plan's
cells-freeze.sharing.cursors): a function-valued cell holding a lazy list
of n elements, each cons cell and each head a computation its source
reduces where a copy first needs it, walked by one use, about two serves
an element. Two folds: `seq` reads each head as it goes, one cursor open
at a time (h ++ acc); `deep` descends to the list's end first, the
copy's ring holding every head's cursor at once (acc ++ h). The heads
are empty strings, so that the appends stay small and what grows is the
serving. Each size is written under results/cursors/ and run with
--count and under perf (scripts/count.sh); the growth from one size to
the next shows whether a serve's cost rises with the list, as AGENTS.md
asks (sizes n, 2n, 4n).

Run from the repository root, after the ladder's build:
  python3 -I scripts/cursors.py [--exe PATH] [N ...]   default 100 200 400 800
"""

import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "results", "cursors")
COUNT = os.path.join(ROOT, "scripts", "count.sh")
FOLDS = {"seq": "h ++ acc", "deep": "acc ++ h"}


def sample(fold, n):
    xs = "nil"
    for _ in range(n):
        xs = f'cons (lit "") ({xs})'
    return f'''language g0

cons h t c n = c h (t c n)
nil c n = n
lit s = s ++ ""
cat h acc = {FOLDS[fold]}
mk u = \\f -> f ({xs})
g = mk ""
use x = g (\\l -> l cat x)
asm.result = use ""
'''


def run(exe, path):
    c = subprocess.run([exe, "-f", path, "--count"], capture_output=True)
    m = re.search(rb"(\d+) interactions, \d+ splices, \d+ values forced, (\d+) serves", c.stderr)
    k = subprocess.run([COUNT, exe, "-f", path], capture_output=True)
    i = re.search(rb"count\.sh: (\d+) instructions", k.stderr)
    if c.returncode != 0 or not m or not i:
        return None
    return int(m.group(1)), int(m.group(2)), int(i.group(1))


def main(args):
    exe = os.path.join(ROOT, "results", "build", "glam")
    if args[:1] == ["--exe"]:
        exe, args = os.path.abspath(args[1]), args[2:]
    sizes = [int(a) for a in args] or [100, 200, 400, 800]
    os.makedirs(OUT, exist_ok=True)
    status = 0
    for fold in FOLDS:
        last = None
        for n in sizes:
            path = os.path.join(OUT, f"{fold}_{n}.g")
            with open(path, "w") as f:
                f.write(sample(fold, n))
            r = run(exe, path)
            if r is None:
                print(f"{fold} n={n}: the run failed")
                status = 1
                continue
            itrs, serves, ins = r
            grow = f", x{ins / last[1]:.2f} for x{n / last[0]:g}" if last else ""
            print(f"{fold} n={n}: {serves} serves, {itrs} interactions, {ins} instructions, "
                  f"{ins // n} an element{grow}")
            last = (n, ins)
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
