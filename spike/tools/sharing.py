#!/usr/bin/env python3
"""Sharing in the compiled kernel (heap-strategies.generate.sharing): which
Bend functions the compiler made segments of their own, compared between
two commits, with the call sites of each that changed.

Bend folds a chain of functions into one segment of the C it emits (a
work-loop function, `#define FID_<module>_<function>_<instance>`, with
`_k<n>` continuation pieces) only while each has one caller. A function
given a second caller, or a branch whose arms both call the continuation,
becomes a segment of its own, and every call into it pays for its
arguments and results through memory: a helper on a shared path costs
every rewrite (`.links.dead-ports`, 5% to 10% on demand). The segments a
change adds or moves are where to look.

    sharing.py compare BASE OUT [PROGRAM]   segments at commit BASE against
                                            the working tree's
    sharing.py segs PROGRAM OUT             one tree's segments, to OUT.segs
    sharing.py diff A.segs B.segs           compare two lists
    sharing.py callers MODULE FUNCTION      a function's call sites

PROGRAM is a Bend file under spike/, runmode.bend by default (the kernel
and its strategies, no test nets: about 15 s and 1.8 GB to C). OUT is a
scratch directory; `compare` checks BASE out there in a detached git
worktree, removed after. Each emission runs alone under
scripts/capped.sh. A function is named as Bend names it (`go.ext.r`), its
segments counted per instance, the family a template was compiled for.
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SPIKE = os.path.dirname(HERE)
ROOT = os.path.dirname(SPIKE)
CAPPED = os.path.join(ROOT, "scripts", "capped.sh")
CAP = os.environ.get("SHARING_CAP", "3000 120").split()

FID = re.compile(r"^#define FID_(\w+) \d+$", re.M)
DEF = re.compile(r"^def ([A-Za-z_][\w.]*)\(", re.M)
IMPORT = re.compile(r"^import \./(\w+)\.bend as (\w+)$", re.M)


def emit(spike, program, out_c):
    """Bend's C for program, in tree spike."""
    subprocess.run([CAPPED] + CAP + ["bend", program, "-o", out_c], cwd=spike, check=True,
                   stdout=subprocess.DEVNULL)


def segments(c_path):
    """{(module, name, instance): segments}, names as the C spells them:
    continuation pieces counted with their function, closure numbers
    dropped."""
    counts = {}
    for f in FID.findall(open(c_path).read()):
        f = re.sub(r"(_[kc]\d+)+$", "", f)
        m = re.match(r"(.*?)_(\d+)$", f)
        base, inst = (m.group(1), m.group(2)) if m else (f, "")
        mod, _, name = base.partition("_")
        key = (mod, name, inst)
        counts[key] = counts.get(key, 0) + 1
    return counts


def write_segs(counts, path):
    with open(path, "w") as f:
        for (mod, name, inst), n in sorted(counts.items()):
            f.write(f"{mod} {name} {inst or '-'} {n}\n")


def read_segs(path):
    counts = {}
    for line in open(path):
        mod, name, inst, n = line.split()
        counts[(mod, name, "" if inst == "-" else inst)] = int(n)
    return counts


def defs(spike, mod):
    """The functions module mod defines, by the C's spelling of each name."""
    path = os.path.join(spike, mod + ".bend")
    if not os.path.exists(path):
        return {}
    return {d.replace(".", "_"): d for d in DEF.findall(open(path).read())}


def callers(spike, mod, fn):
    """Each call of mod's fn in the spike's sources: (file, line, caller)."""
    sites = []
    for f in sorted(os.listdir(spike)):
        if not f.endswith(".bend") or f in ("PROOF.bend", "LAWS.bend"):
            continue
        src = open(os.path.join(spike, f)).read()
        if f == mod + ".bend":
            pat = r"(?<![\w.])" + re.escape(fn) + r"\("
        else:
            aliases = [a for m, a in IMPORT.findall(src) if m == mod]
            if not aliases:
                continue
            pat = r"(?<![\w.])(?:" + "|".join(map(re.escape, aliases)) + r")\." + re.escape(fn) + r"\("
        cur = None
        for i, line in enumerate(src.splitlines(), 1):
            d = DEF.match(line)
            if d:
                cur = d.group(1)
                continue
            if cur and re.search(pat, line):
                sites.append((f, i, cur))
    return sites


def bend_name(spike, mod, name):
    return defs(spike, mod).get(name, name.replace("_", "."))


def show_sites(label, sites):
    print(f"    {label}: {len(sites)} call site(s)")
    for f, line, cur in sites[:8]:
        print(f"      {f}:{line} in {cur}")
    if len(sites) > 8:
        print(f"      ... {len(sites) - 8} more")


def report(a, b, spike, base_spike=None):
    """Each function whose segments differ, A's against B's, with its call
    sites in B's sources (spike), and in A's (base_spike) where those
    differ."""
    names = sorted(set(a) | set(b))
    changed = [k for k in names if a.get(k, 0) != b.get(k, 0)]
    fns = sorted({(m, n) for m, n, _ in changed})
    print(f"segments: {sum(a.values())} -> {sum(b.values())}; {len(fns)} functions changed")
    for mod, name in fns:
        insts = sorted({i for m, n, i in names if (m, n) == (mod, name)})
        counts = ", ".join(f"{i or '-'}: {a.get((mod, name, i), 0)} -> {b.get((mod, name, i), 0)}" for i in insts)
        bn = bend_name(spike, mod, name)
        print(f"  {mod}.{bn}  [{counts}]")
        sites = callers(spike, mod, bn)
        show_sites("now", sites)
        if base_spike:
            old = callers(base_spike, mod, bend_name(base_spike, mod, name))
            if [(f, c) for f, _, c in old] != [(f, c) for f, _, c in sites]:
                show_sites("base", old)
    return 0


def cmd_segs(program, out):
    os.makedirs(out, exist_ok=True)
    c = os.path.join(os.path.abspath(out), "prog.c")
    emit(SPIKE, program, c)
    counts = segments(c)
    write_segs(counts, os.path.join(out, "prog.segs"))
    print(f"{sum(counts.values())} segments in {len(counts)} function instances: {os.path.join(out, 'prog.segs')}")
    return 0


def cmd_compare(base, out, program="runmode.bend"):
    out = os.path.abspath(out)
    os.makedirs(out, exist_ok=True)
    wt = os.path.join(out, "base")
    emit(SPIKE, program, os.path.join(out, "head.c"))
    subprocess.run(["git", "worktree", "add", "-q", "--detach", wt, base], cwd=ROOT, check=True)
    try:
        emit(os.path.join(wt, "spike"), program, os.path.join(out, "base.c"))
        a, b = segments(os.path.join(out, "base.c")), segments(os.path.join(out, "head.c"))
        write_segs(a, os.path.join(out, "base.segs"))
        write_segs(b, os.path.join(out, "head.segs"))
        print(f"{program} at {base} against the working tree")
        return report(a, b, SPIKE, os.path.join(wt, "spike"))
    finally:
        subprocess.run(["git", "worktree", "remove", "--force", wt], cwd=ROOT, check=True)


def main(argv):
    if len(argv) >= 3 and argv[0] == "compare":
        return cmd_compare(*argv[1:4])
    if len(argv) == 3 and argv[0] == "segs":
        return cmd_segs(argv[1], argv[2])
    if len(argv) == 3 and argv[0] == "diff":
        return report(read_segs(argv[1]), read_segs(argv[2]), SPIKE)
    if len(argv) == 3 and argv[0] == "callers":
        for f, line, cur in callers(SPIKE, argv[1], argv[2]):
            print(f"{f}:{line} in {cur}")
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
