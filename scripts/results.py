#!/usr/bin/env python3
"""The analysis store: bulk results and the parameters that produced them.

One SQLite file, results/analysis.sqlite (or $GLAM_RESULTS), kept out of
git. A run is one invocation of a tool: its parameters as JSON, the commit
it ran on and how many paths were changed, Bend's version, the CPU, a
note. Results hang off runs:
  terms    the differential test (spike/tools/differential.sh), one row
           per term, ending, pairing mode and seed
  profiles the profiling strategy (spike/tools/profile.sh), one row per
           term: value, interactions, errors, logical interactions, peels
  pair_counts  its interactions by pair of kinds, A's principal negative
  library  the library of nets (spike/tools/library.py --store), one row
           per entry and mode: whether its checks passed, its value, and
           the interactions of the spike, the full reduction, demand and two stacks
  library_ev  the same in the erasure modes: interactions and events
           eager, on demand (and its nodes live after, and demand's
           without events) and with two stacks; eager profiled, its
           logical interactions and its events by kind (` k:n`)
  counts   instructions and interactions per build and workload
  metrics  any named number

    results.py run TOOL PARAMS_JSON [NOTE]       start a run, print its id
    results.py terms RUN ENDING MODE SEED FILE   import a differential output
    results.py profiles RUN ENDING MODE SEED FILE  import a profile output
    results.py library RUN FILE                  import library.py's rows
    results.py library_ev RUN FILE               and its erasure modes' rows
    results.py count RUN BUILD WORKLOAD K LAZY ITRS INSTRUCTIONS [CYCLES]
    results.py metric RUN NAME VALUE
    results.py sql QUERY                         print rows, tab-separated
    results.py summary RUN                       the differential's verdicts
    results.py fusion ON OFF                     two profile runs, fusion on
                                                 and off, compared per mode

Run from anywhere in the repository; read the store with any SQLite client
(`results.py sql "select ..."`), e.g. to compare runs with one parameter
changed.
"""
import datetime
import json
import os
import re
import sqlite3
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DB = os.environ.get("GLAM_RESULTS", os.path.join(ROOT, "results", "analysis.sqlite"))

SCHEMA = """
create table if not exists runs (
  id integer primary key, at text not null, tool text not null, params text not null,
  git_commit text, git_changed integer, bend text, cpu text, note text);
create table if not exists terms (
  run_id integer not null references runs(id), ending text not null, mode text not null,
  seed integer not null, term integer not null, name text, want text,
  spike_v text, spike_i integer, spike_e integer,
  ref_v text, ref_i integer, ref_e integer,
  fast_v text, fast_i integer, fast_e integer,
  lazy_v text, lazy_i integer, lazy_e integer, lazy_state text, lazy_live integer,
  verdict text, lazy_more integer,
  primary key (run_id, ending, mode, seed, term));
create table if not exists counts (
  run_id integer not null references runs(id), build text not null, workload text not null,
  k integer not null, lazy integer not null, interactions integer, instructions integer, cycles integer);
create table if not exists metrics (
  run_id integer not null references runs(id), name text not null, value real);
create table if not exists profiles (
  run_id integer not null references runs(id), ending text not null, mode text not null,
  seed integer not null, term integer not null, name text, want text, value text,
  interactions integer, errors integer, logical integer, peels integer, wide integer,
  primary key (run_id, ending, mode, seed, term));
create table if not exists pair_counts (
  run_id integer not null references runs(id), ending text not null, mode text not null,
  seed integer not null, term integer not null, a text not null, b text not null, n integer not null,
  primary key (run_id, ending, mode, seed, term, a, b));
create table if not exists library (
  run_id integer not null references runs(id), name text not null, mode text not null, ok integer,
  value text, spike_i integer, fast_i integer, lazy_i integer, logical integer, peels integer,
  two_i integer, primary key (run_id, name, mode));
create table if not exists library_ev (
  run_id integer not null references runs(id), name text not null, mode text not null,
  ev_i integer, ev_n integer, evlazy_i integer, evlazy_n integer, evlazy_live integer,
  evtwo_i integer, evtwo_n integer, lazy_live integer, evprof_logical integer, ev_kinds text,
  primary key (run_id, name, mode));
"""

# columns added to a table after a store was made: (table, column, type)
LATER = [("library_ev", "evprof_logical", "integer"), ("library_ev", "ev_kinds", "text")]

# one line of terms.py --kernel's output
TERM = re.compile(
    r"#(\d+) want (\S+): spike (\S+) \((\d+), (\d+)\) \| ref (\S+) \((\d+), (\d+)\) \| fast (\S+) \((\d+), (\d+)\)"
    r"(?: \| lazy (\S+) \((\d+), (\d+)\) (.+?), (\d+) live)?  "
    r"(TABLE MISMATCH|DIFFER ref/fast|DIFFER value|same, counts equal|same, counts differ)(  LAZY MORE)?  (.*)$")

# one line of terms.py --profile's output
PROFILE = re.compile(
    r"#(\d+) want (\S+): (.+?) \((\d+), (\d+)\); logical (\d+|past 2\^48), (\d+) peels, (\d+) wide; "
    r"pairs((?: \d+\.\d+:\d+)*)  (.*)$")

# rule kinds by code (kprim.bend's header, low four bits)
KINDS = {1: "Fn", 2: "Ap", 3: "Copy", 4: "Merge", 5: "Data", 6: "EraN", 7: "EraP", 8: "Root", 9: "Call",
         10: "Lift", 11: "LiftC", 12: "CopyL", 13: "CopyR", 14: "MergeL", 15: "MergeR"}


def db():
    os.makedirs(os.path.dirname(DB), exist_ok=True)
    c = sqlite3.connect(DB)
    c.executescript(SCHEMA)
    for table, col, ty in LATER:
        if col not in [r[1] for r in c.execute(f"pragma table_info({table})")]:
            c.execute(f"alter table {table} add column {col} {ty}")
    return c


def sh(*args):
    try:
        return subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=30).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return None


def cpu():
    try:
        for line in open("/proc/cpuinfo"):
            if line.startswith("model name"):
                return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return None


def cmd_run(tool, params, note=None):
    json.loads(params)
    status = sh("git", "status", "--porcelain")
    bend = sh(os.environ.get("BEND", "bend"), "version")
    with db() as c:
        cur = c.execute(
            "insert into runs (at, tool, params, git_commit, git_changed, bend, cpu, note) values (?,?,?,?,?,?,?,?)",
            (datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"), tool, params,
             sh("git", "rev-parse", "--short", "HEAD"), len(status.splitlines()) if status is not None else None,
             bend, cpu(), note))
        print(cur.lastrowid)


def num(s):
    return None if s is None else int(s)


def cmd_terms(run, ending, mode, seed, path):
    rows = []
    for line in open(path):
        m = TERM.match(line.rstrip("\n"))
        if not m:
            continue
        g = m.groups()
        rows.append((int(run), ending, mode, int(seed), int(g[0]), g[18], g[1],
                     g[2], num(g[3]), num(g[4]), g[5], num(g[6]), num(g[7]), g[8], num(g[9]), num(g[10]),
                     g[11], num(g[12]), num(g[13]), g[14], num(g[15]), g[16], 1 if g[17] else 0))
    with db() as c:
        c.executemany("insert or replace into terms values (" + ",".join("?" * 23) + ")", rows)
    print(len(rows), "terms from", path)


def cmd_profiles(run, ending, mode, seed, path):
    rows, pairs = [], []
    for line in open(path):
        m = PROFILE.match(line.rstrip("\n"))
        if not m:
            continue
        g = m.groups()
        key = (int(run), ending, mode, int(seed), int(g[0]))
        rows.append(key + (g[9], g[1], g[2], num(g[3]), num(g[4]), None if g[5].startswith("past") else int(g[5]),
                           num(g[6]), num(g[7])))
        for p in g[8].split():
            ab, n = p.split(":")
            a, b = (int(x) for x in ab.split("."))
            pairs.append(key + (KINDS.get(a, str(a)), KINDS.get(b, str(b)), int(n)))
    with db() as c:
        c.executemany("insert or replace into profiles values (" + ",".join("?" * 13) + ")", rows)
        c.executemany("insert or replace into pair_counts values (" + ",".join("?" * 8) + ")", pairs)
    print(len(rows), "terms,", len(pairs), "pair counts from", path)


def cmd_library(run, path):
    rows = []
    for line in open(path):
        f = line.rstrip("\n").split("\t")
        rows.append((int(run), f[0], f[1], int(f[2]), f[3]) + tuple(None if x == "" else int(x) for x in f[4:10]))
    with db() as c:
        c.executemany("insert or replace into library (run_id, name, mode, ok, value, spike_i, fast_i, lazy_i, logical,"
                      " peels, two_i) values (" + ",".join("?" * 11) + ")", rows)
    print(len(rows), "library cases from", path)


def cmd_library_ev(run, path):
    rows = []
    for line in open(path):
        f = line.rstrip("\n").split("\t")
        rows.append((int(run), f[0], f[1]) + tuple(int(x) for x in f[2:10]) + (None if f[10] == "" else int(f[10]), f[11]))
    with db() as c:
        c.executemany("insert or replace into library_ev values (" + ",".join("?" * 13) + ")", rows)
    print(len(rows), "library cases in the erasure modes from", path)


def cmd_count(run, build, workload, k, lazy, itrs, ins, cycles=None):
    with db() as c:
        c.execute("insert into counts values (?,?,?,?,?,?,?,?)",
                  (int(run), build, workload, int(k), int(lazy), num(itrs), num(ins), num(cycles)))


def cmd_metric(run, name, value):
    with db() as c:
        c.execute("insert into metrics values (?,?,?)", (int(run), name, float(value)))


def cmd_sql(query):
    with db() as c:
        cur = c.execute(query)
        if cur.description:
            print("\t".join(d[0] for d in cur.description))
        for row in cur:
            print("\t".join("" if x is None else str(x) for x in row))


SUMMARY = """
select ending, mode, seed, count(*) as terms,
  sum(verdict = 'same, counts equal') as equal, sum(verdict = 'same, counts differ') as other_counts,
  sum(verdict = 'DIFFER ref/fast') as ref_fast, sum(verdict = 'DIFFER value') as value,
  sum(verdict = 'TABLE MISMATCH') as tab, sum(lazy_more) as lazy_more,
  sum(fast_v != want) as full_wrong, sum(lazy_v is not null and lazy_v != want) as lazy_wrong
from terms where run_id = {run} group by ending, mode, seed
order by case ending when 'succ' then 0 when 'plus' then 1 else 2 end, mode desc, seed
"""

# per mode, the terms both runs reduced to the wanted value: whether the
# logical interactions agree, and with unit brackets (unfused), whether
# the logical interactions with fusion are the interactions without it
FUSION = """
with a as (select * from profiles where run_id = {on}), b as (select * from profiles where run_id = {off})
select a.mode, count(*) as terms, sum(a.value = a.want and b.value = b.want) as complete,
  sum(a.value = a.want and b.value = b.want and a.logical = b.logical) as logical_equal,
  sum(a.value = a.want and b.value = b.want and a.logical = b.interactions) as logical_is_unfused,
  sum(case when a.value = a.want and b.value = b.want then a.interactions end) as interactions_on,
  sum(case when a.value = a.want and b.value = b.want then b.interactions end) as interactions_off,
  sum(case when a.value = a.want and b.value = b.want then a.logical end) as logical
from a join b using (ending, mode, seed, term)
group by a.mode order by a.mode
"""


def main(argv):
    cmds = {"run": cmd_run, "terms": cmd_terms, "profiles": cmd_profiles, "library": cmd_library, "library_ev": cmd_library_ev, "count": cmd_count, "metric": cmd_metric, "sql": cmd_sql,
            "summary": lambda run: cmd_sql(SUMMARY.format(run=int(run))),
            "fusion": lambda on, off: cmd_sql(FUSION.format(on=int(on), off=int(off)))}
    if not argv or argv[0] not in cmds:
        print(__doc__.strip())
        return 2
    cmds[argv[0]](*argv[1:])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
