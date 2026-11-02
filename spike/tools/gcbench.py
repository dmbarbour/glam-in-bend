#!/usr/bin/env python3
"""The collecting demand's benchmark (heap-strategies.erasure.load.cycle.bench):
every case of the library of nets, one a file (library_nets.py's rows),
run by a build of spike/runmode.bend on plain demand (lazy) and on demand
collecting where its net would grow (dclazy), each run's instructions
counted by scripts/count.sh, recorded in the analysis store (table
gcbench) with each case's state, interactions and capacity both ways, and
the collections' count, interactions and nodes scanned.

Two runs compare case by case, a case's cost the instructions collecting
takes over plain demand in its own run (so that builds whose plain demand
differs compare fairly): how many cases the second run improves, worsens
or leaves alike, among those that collect in either run, a change
counting where it passes the larger of 2,000 instructions and 0.1% of
plain demand; the totals; capacities grown and shrunk; and the
exceptions, each with what changed with it. A case whose collecting state
or value differs from its plain demand's, in either run, is listed first:
collecting must keep demand's outcome.

    gcbench.py nets OUT                     write OUT/rows/NNN.txt and OUT/index.txt
    gcbench.py run OUT RUNMODE NOTE [JOBS]  count every row; prints the run id
    gcbench.py compare RUN_A RUN_B [N]      compare, the N largest changes each way (8)
"""
import concurrent.futures
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import results  # noqa: E402

COUNT = os.path.join(ROOT, "scripts", "count.sh")
CAPPED = os.path.join(ROOT, "scripts", "capped.sh")

SCHEMA = """
create table if not exists gcbench (
  run_id integer not null references runs(id), row integer not null, name text not null,
  lazy_state text, lazy_value text, lazy_itrs integer, lazy_cap integer, lazy_ins integer,
  dc_state text, dc_value text, dc_itrs integer, dc_cap integer, dc_ins integer,
  dc_cyc integer, dc_citrs integer, dc_scan integer,
  primary key (run_id, row));
"""

# one row of runmode's output: name, state, then the result from the right
LINE = re.compile(r"^(?P<name>[^:]+): (?P<state>[^:]+): (?P<value>.*), (?P<itrs>\d+) interactions, \d+ errors, "
                  r"\d+ nodes live of (?P<cap>\d+), \d+ reached"
                  r"(?:; (?P<cyc>\d+) collections, (?P<citrs>\d+) interactions, (?P<scan>\d+) nodes scanned)?$")


def db():
    c = results.db()
    c.executescript(SCHEMA)
    return c


def cmd_nets(out):
    os.makedirs(os.path.join(out, "rows"), exist_ok=True)
    names = [ln.split()[1] for ln in open(os.path.join(ROOT, "spike", "library.txt")) if ln.startswith("name:")]
    subprocess.run([sys.executable, os.path.join(HERE, "library_nets.py"), out, *names], check=True,
                   stdout=subprocess.DEVNULL)
    lines = open(os.path.join(out, "nets.txt")).read().split("\n")
    rows = [ln for ln in lines[1:] if ln.strip()]
    for i, r in enumerate(rows):
        with open(os.path.join(out, "rows", f"{i:03d}.txt"), "w") as f:
            f.write("1\n" + r + "\n")
    print(len(rows), "rows in", os.path.join(out, "rows"))


def count(binary, path, mode):
    p = subprocess.run([CAPPED, "2000", "300", COUNT, binary, path, mode], capture_output=True, text=True)
    ins = None
    for ln in p.stderr.splitlines():
        if ln.startswith("count.sh:"):
            ins = int(ln.split()[1])
    m = LINE.match(p.stdout.strip())
    if not m or ins is None:
        raise SystemExit(f"gcbench: no result for {path} {mode}: {p.stdout.strip()!r} {p.stderr.strip()[-200:]!r}")
    return m, ins


def one(binary, out, i):
    path = os.path.join(out, "rows", f"{i:03d}.txt")
    lz, li = count(binary, path, "lazy")
    dc, di = count(binary, path, "dclazy")
    return (i, lz["name"], lz["state"], lz["value"], int(lz["itrs"]), int(lz["cap"]), li,
            dc["state"], dc["value"], int(dc["itrs"]), int(dc["cap"]), di,
            int(dc["cyc"]), int(dc["citrs"]), int(dc["scan"]))


def cmd_run(out, binary, note, jobs="4"):
    n = len(os.listdir(os.path.join(out, "rows")))
    params = json.dumps({"rows": n, "runmode": os.path.abspath(binary), "tool": "spike/tools/gcbench.py"})
    with db() as c:
        cur = c.execute(
            "insert into runs (at, tool, params, git_commit, git_changed, bend, cpu, note) values (?,?,?,?,?,?,?,?)",
            (results.datetime.datetime.now(results.datetime.timezone.utc).isoformat(timespec="seconds"), "gcbench",
             params, results.sh("git", "rev-parse", "--short", "HEAD"),
             len((results.sh("git", "status", "--porcelain") or "").splitlines()),
             results.sh(os.environ.get("BEND", "bend"), "version"), results.cpu(), note))
        run = cur.lastrowid
    with concurrent.futures.ThreadPoolExecutor(int(jobs)) as ex:
        rows = list(ex.map(lambda i: one(binary, out, i), range(n)))
    with db() as c:
        c.executemany("insert into gcbench values (" + ",".join("?" * 16) + ")", [(run, *r) for r in rows])
    print(run)


def load(c, run):
    cols = ["row", "name", "lazy_state", "lazy_value", "lazy_itrs", "lazy_cap", "lazy_ins", "dc_state", "dc_value",
            "dc_itrs", "dc_cap", "dc_ins", "dc_cyc", "dc_citrs", "dc_scan"]
    return {r[0]: dict(zip(cols, r)) for r in c.execute(f"select {', '.join(cols)} from gcbench where run_id=?",
                                                        (int(run),))}


def over(r):
    return r["dc_ins"] - r["lazy_ins"]


def describe(a, b):
    d = over(b) - over(a)
    return (f"  {b['name']:30s} {d:+12,d} ({100 * d / a['lazy_ins']:+.2f}% of plain) cap {a['dc_cap']}->{b['dc_cap']}"
            f" collections {a['dc_cyc']}->{b['dc_cyc']} their interactions {a['dc_citrs']}->{b['dc_citrs']}"
            f" scanned {a['dc_scan']}->{b['dc_scan']}")


def cmd_compare(ra, rb, n="8"):
    with db() as c:
        a, b = load(c, ra), load(c, rb)
    keys = sorted(set(a) & set(b))
    if len(keys) != len(a) or len(keys) != len(b):
        print(f"runs differ in rows: {len(a)} and {len(b)}, {len(keys)} shared")
    bad = [k for k in keys for r in (a[k], b[k])
           if (r["dc_state"], r["dc_value"]) != (r["lazy_state"], r["lazy_value"])]
    for k in sorted(set(bad)):
        for tag, r in (("A", a[k]), ("B", b[k])):
            print(f"OUTCOME {tag} {r['name']}: plain {r['lazy_state']} {r['lazy_value']}, collecting {r['dc_state']}"
                  f" {r['dc_value']}")
    coll = [k for k in keys if a[k]["dc_cyc"] or b[k]["dc_cyc"]]
    thr = {k: max(2000, a[k]["lazy_ins"] // 1000) for k in keys}
    better = [k for k in coll if over(b[k]) - over(a[k]) < -thr[k]]
    worse = [k for k in coll if over(b[k]) - over(a[k]) > thr[k]]
    calm = [k for k in keys if k not in coll and abs(over(b[k]) - over(a[k])) > thr[k]]
    tot = lambda rs, f: sum(f(rs[k]) for k in keys)
    for tag, rs, run in (("A", a, ra), ("B", b, rb)):
        print(f"run {tag} ({run}): collecting {tot(rs, over) / tot(rs, lambda r: r['lazy_ins']) * 100:.2f}% over plain"
              f" demand in all, {tot(rs, lambda r: r['dc_cap']):,} nodes of capacity, {tot(rs, lambda r: r['dc_cyc'])}"
              f" collections, {tot(rs, lambda r: r['dc_citrs']):,} interactions in them")
    print(f"{len(keys)} cases, {len(coll)} collecting in either: B improves {len(better)}, worsens {len(worse)},"
          f" leaves {len(coll) - len(better) - len(worse)} alike; {len(calm)} not collecting changed")
    up = [k for k in keys if b[k]["dc_cap"] > a[k]["dc_cap"]]
    down = [k for k in keys if b[k]["dc_cap"] < a[k]["dc_cap"]]
    print(f"capacity: {len(up)} grown, {len(down)} shrunk")
    for title, ks in (("worse", sorted(worse, key=lambda k: over(a[k]) - over(b[k]))),
                      ("better", sorted(better, key=lambda k: over(b[k]) - over(a[k]))),
                      ("capacity grown", up), ("capacity shrunk", down), ("not collecting, changed", calm)):
        if ks:
            print(f"{title}:")
            for k in ks[:int(n)]:
                print(describe(a[k], b[k]))


def main(argv):
    cmds = {"nets": cmd_nets, "run": cmd_run, "compare": cmd_compare}
    if not argv or argv[0] not in cmds:
        print(__doc__.strip())
        return 2
    cmds[argv[0]](*argv[1:])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
