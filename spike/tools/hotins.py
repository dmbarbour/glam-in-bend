#!/usr/bin/env python3
"""Where a native Bend program spends its instructions.

    hotins.py OUTDIR [TOP] -- PROGRAM ARGS...

Samples user-mode instructions under `perf record` (one sample every
10,000), then joins the sampled addresses with `objdump`'s disassembly:
the share of each instruction kind (stack moves, arithmetic, compares,
...), of each function, and the TOP hottest instructions (20 by default).
`perf annotate` printed nothing for these binaries; this does its job.
OUTDIR keeps perf.data, the samples and the disassembly.
"""
import collections
import os
import re
import subprocess
import sys


def main(argv):
    if "--" not in argv or argv.index("--") < 2:
        print(__doc__)
        return 2
    cut = argv.index("--")
    out, top = argv[1], int(argv[2]) if cut > 2 else 20
    cmd = argv[cut + 1:]
    os.makedirs(out, exist_ok=True)
    data = os.path.join(out, "perf.data")
    subprocess.run(["perf", "record", "-q", "-e", "instructions:u", "-c", "10000", "-o", data] + cmd,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
    ips = subprocess.run(["perf", "script", "-i", data, "-F", "ip,sym"], capture_output=True, text=True).stdout
    dis = subprocess.run(["objdump", "-d", "--no-show-raw-insn", cmd[0]], capture_output=True, text=True).stdout
    open(os.path.join(out, "ips.txt"), "w").write(ips)
    open(os.path.join(out, "dis.txt"), "w").write(dis)
    cnt = collections.Counter(line.split()[0] for line in ips.splitlines() if len(line.split()) >= 2)
    total = sum(cnt.values())
    code, sym_of, cur = {}, {}, None
    for line in dis.splitlines():
        m = re.match(r"^([0-9a-f]+) <(.+)>:", line)
        if m:
            cur = m.group(2)
            continue
        m = re.match(r"^\s+([0-9a-f]+):\s+(.*)$", line)
        if m:
            off = int(m.group(1), 16)
            code[off], sym_of[off] = m.group(2).strip(), cur
    # the load base: the page offset that maps the most samples into the code
    pages = collections.Counter()
    for ip, c in cnt.items():
        pages[int(ip, 16) >> 12] += c
    page = pages.most_common(1)[0][0]
    base, hits = max((((page - d) << 12, sum(c for ip, c in cnt.items() if int(ip, 16) - ((page - d) << 12) in code))
                      for d in range(0x400)), key=lambda t: t[1])
    print(f"{total} samples, {hits} matched")
    kinds, funcs, hot = collections.Counter(), collections.Counter(), collections.Counter()
    for ip, c in cnt.items():
        off = int(ip, 16) - base
        ins = code.get(off)
        if ins is None:
            continue
        op = ins.split()[0]
        if op.startswith("mov") and "(%rsp)" in ins: kind = "stack move"
        elif op.startswith("mov") and "(%r" in ins: kind = "memory move"
        elif op.startswith("mov"): kind = "register move"
        elif op.startswith(("j", "cmov", "set")): kind = "branch or select"
        elif op in ("cmp", "test"): kind = "compare"
        elif op in ("call", "ret", "push", "pop"): kind = "call, return, push, pop"
        elif op in ("lea", "add", "sub", "and", "or", "shl", "shr", "inc", "dec", "xor", "not", "neg", "imul"): kind = "arithmetic"
        else: kind = "other"
        kinds[kind] += c
        funcs[sym_of.get(off)] += c
        hot[(sym_of.get(off), off, ins)] += c
    for k, v in kinds.most_common():
        print(f"  {v / total * 100:5.1f}%  {k}")
    print()
    for f, v in funcs.most_common(12):
        print(f"  {v / total * 100:5.1f}%  {f}")
    print()
    for (f, off, ins), v in hot.most_common(top):
        print(f"  {v / total * 100:5.2f}%  {f:24s} {off:7x}  {ins}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
