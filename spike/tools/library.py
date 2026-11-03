#!/usr/bin/env python3
"""The library of nets (pairing-library in docs/plans/NetPairing_2026-10-26.md):
small nets kept for what they exercise, each run through the spike, the
kernel's interpreted table and its generated rewrites, on demand, with
two stacks, by the profiling strategy, and in the erasure modes, which
run events (heap-strategies.erasure.kernel): eager by the generated
rewrites and by the interpreted table, on demand, with two stacks, and
profiled, its logical interactions those of the interactions made, its
events by kind apart. What must hold is checked; interactions and events
are measurements, recorded in the analysis store when asked.

    library.py OUT [--update] [--store NOTE] [NAME...]

OUT holds the program written and its output; NAME runs those entries
alone. --update writes each mode's logical interactions and peels into
the library from the run, never its value. --store records every case in
the store (scripts/results.py library). Exits 1 if any check fails.

spike/library.txt holds the entries, separated by blank lines, each a few
`key: value` lines, a line starting with a blank continuing the last:
  name     a unique slug
  why      why the entry is kept
  term     a lambda term in terms.py's syntax, lowered once per mode:
  levels, labels, unfused    what must hold, lowered that way; or
  nodes, links, root         a net written out: nodes as terms.py makes
           them (fn(n) fnd(n) ap(n) cp(site,n) br(n) cr(n) ctl(n,+by) ctl(n,-1)
           ctlc(n,+by) num(v) succ plus fma era void), links `a.p-b.p`, the
           exposed port `a.p`, and
  net      what must hold
  fuel     the full reductions' fuel, 1280000 if not given (demand has
           twice as many steps, the spike as many interactions)
What must hold is one of
  VALUE logical L peels P    the value every strategy reaches, demand in
           no more interactions, and the logical interactions and peels
           the profile counts (kstrat.bend's Profiling); the two-stack
           strategy's interactions are measured, not checked, since
           fusion's savings depend on order
  demand VALUE   the value demand reaches; the full reductions need not
           finish in the fuel, as where the value needs only part of the
           net
  cycle    demand finds a cycle of principal ports facing auxiliary ones,
           and the full reductions no value
  void     demand, collecting or not, finds a void at the interface,
           nothing supplied where a value is wanted, an outcome of its own
           (`net-void-demanded`), and the full reductions no value
  unscoped VALUE   a function's argument used outside its body, which
           glam's construction refuses (`net-scoped-arguments`): demand,
           collecting or not, reports it, and the full reductions, which
           refuse nothing, reach VALUE
  wrong    a mode known to miss the value (labels on some
           self-applications), which must still miss it.
The erasure modes must reach the same value where every strategy must,
and demand's where demand must; events change the interactions, which are
measured, the generated rewrites and the interpreted table making the
same interactions and events, and the profile with events as many as the
generated rewrites.
The kernel's events tables are checked against the model's events for
every kind code a header holds (knet.bend's ev_tables), and a builtin's
field read back for every op and need it holds (builtin_fields).
Demand collecting where its net would grow (events, the pairs that do
not grow the net, the sweep; heap-strategies.erasure.load.cycle) must
keep demand's value and state, the audits passing after; its
interactions are the total, demand's and the collections'. So must its
stress test, which collects a net of 1024 nodes or fewer every 16 steps
(heap-strategies.erasure.load.cycle.stress).
Checked besides, for every case: no errors, the data table, the free
list (KN.free_ok) and the wiring (KN.wired_ok) in step, every net
polarized, and a net built with a vicious circle (a closed principal
path), which glam's construction refuses (`net-obvious-errors`), kept
only to show demand finding it, so expecting `cycle` (polarity.py); a
net built with a function's argument used outside its body likewise
expecting `unscoped`, and no other (polarity.py's `unscoped`); a
cycle may also form by rewriting,
the interpreted table and the generated rewrites making the same
interactions and the profile too; a term's value its evaluator's
(terms.py).

The build and the run go under scripts/capped.sh, each capped near its
cost so that a run going astray fails in minutes: the build peaks at
3.5 GB in 76 s, the run at a few dozen MB in under a minute (2026-11-03).
LIBRARY_BUILD_CAP and LIBRARY_RUN_CAP override them, "MEGABYTES SECONDS".
Run one library at a time: two builds at once need 7 GB.
"""
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import polarity  # noqa: E402
import terms  # noqa: E402

SPIKE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.dirname(SPIKE)
LIBRARY = os.path.join(SPIKE, "library.txt")
MODES = ("levels", "labels", "unfused")
FUEL = 1280000
BUILD_CAP = "5000 240"
RUN_CAP = "1000 120"


def cap(var, default):
    """A cap for scripts/capped.sh, MEGABYTES SECONDS, from the environment."""
    return os.environ.get(var, default).split()

NODE = re.compile(r"([a-z]+)(?:\(([^)]*)\))?$")
END = re.compile(r"(\d+)\.(\d+)$")
WANT = re.compile(r"(\S+) logical (\d+) peels (\d+)$")
DEMAND = re.compile(r"demand (\S+)$")
UNSCOPED = re.compile(r"unscoped (\S+)$")


class Case:
    def __init__(self, entry, mode, want, line, fuel):
        self.entry, self.mode, self.want, self.line, self.fuel = entry, mode, want, line, fuel
        self.net = self.root = self.value = None


def entries(lines):
    """the library's entries: dicts of key to (value, line index)"""
    out, cur, last = [], {}, None
    for i, raw in enumerate(lines + [""]):
        line = raw.rstrip("\n")
        if line.startswith("#"):
            continue
        if not line.strip():
            if cur:
                out.append(cur)
            cur, last = {}, None
        elif line[0] in " \t" and last:
            v, j = cur[last]
            cur[last] = (v + " " + line.strip(), j)
        else:
            k, _, v = line.partition(":")
            last = k.strip()
            cur[last] = (v.strip(), i)
    return out


def end(text):
    m = END.match(text)
    if not m:
        raise ValueError(f"not a port: {text}")
    return int(m.group(1)), int(m.group(2))


def written_net(e):
    net = terms.Net(True)
    for tok in e["nodes"][0].split():
        m = NODE.match(tok)
        if not m:
            raise ValueError(f"not a node: {tok}")
        args = tuple(int(a) for a in m.group(2).split(",")) if m.group(2) else ()
        net.node(m.group(1), *args)
    for tok in e["links"][0].split():
        a, _, b = tok.partition("-")
        net.link(end(a), end(b))
    return net, end(e["root"][0])


def cases(es, only):
    names, out = set(), []
    for e in es:
        name = e["name"][0]
        if name in names:
            raise ValueError(f"entry {name} twice")
        names.add(name)
        if only and name not in only:
            continue
        fuel = int(e["fuel"][0]) if "fuel" in e else FUEL
        if "term" in e:
            t = terms.parse(e["term"][0])
            for mode in MODES:
                if mode in e:
                    c = Case(name, mode, *e[mode], fuel)
                    c.net, c.root = terms.to_tpl(t, mode != "labels", mode != "unfused")
                    c.value = terms.evaluate(t)
                    out.append(c)
        else:
            c = Case(name, "net", *e["net"], fuel)
            c.net, c.root = written_net(e)
            out.append(c)
    return out


MAIN = r'''
def show_m(m: Maybe<&2, V.Val>) -> String:
  match m:
    case Some{v}:
      match v:
        case V.VNum{+n}:
          U32.show(n)
        case _:
          "fn"
    case None{}:
      "none"

def tab(+ok: Bool) -> String:
  match ok:
    case True{}:
      ""
    case False{}:
      "!"

def res_str(r: K.KRes) -> String:
  match r:
    case K.KRes{v, +itrs, +errs, +ok}:
      show_m(v) ++ " (" ++ U32.show(itrs) ++ ", " ++ U32.show(errs) ++ ")" ++ tab(ok)

def spike_str(r: N.Q & Maybe<&2, V.Val>) -> String:
  (q, v) = r
  match q:
    case N.Q{st, rq, +itrs, +errs, +ser}:
      show_m(v) ++ " (" ++ U32.show(itrs) ++ ", " ++ U32.show(errs) ++ ")"

def lazy_str(r: K.DRes) -> String:
  match r:
    case K.DRes{k, +st, +lz, +live, +cap, +reach}:
      res_str(k) ++ " " ++ K.st_name(st) ++ ", " ++ U32.show(live) ++ " live of " ++ U32.show(cap) ++ ", " ++ U32.show(reach) ++ " reached"

def ev_str(r: K.ERes) -> String:
  match r:
    case K.ERes{k, +evs}:
      res_str(k) ++ " ev " ++ U32.show(evs)

def evlazy_str(r: K.EDRes) -> String:
  match r:
    case K.EDRes{k, +evs}:
      lazy_str(k) ++ " ev " ++ U32.show(evs)

def dc_str(r: K.CRes) -> String:
  match r:
    case K.CRes{k, +cyc, +citrs, +cevs, +scan}:
      lazy_str(k) ++ " cyc " ++ U32.show(cyc) ++ " itrs " ++ U32.show(citrs) ++ " ev " ++ U32.show(cevs) ++ " scan " ++ U32.show(scan)

# a case through every strategy
def one(+k: U32) -> String:
  "#" ++ U32.show(k) ++ ": spike " ++ spike_str(T.result(T.run(tpl_of(k), fuel_of(k, 1n)))) ++
    " | ref " ++ res_str(K.run_t(tpl_of(k), fuel_of(k, 0n), False{})) ++
    " | fast " ++ res_str(K.run_t(tpl_of(k), fuel_of(k, 0n), True{})) ++
    " | lazy " ++ lazy_str(K.run_d(tpl_of(k), fuel_of(k, 2n), [])) ++
    " | two " ++ res_str(K.run_two(tpl_of(k), fuel_of(k, 0n), True{})) ++
    " | ev " ++ ev_str(K.run_ev(tpl_of(k), fuel_of(k, 0n), True{})) ++
    " | evref " ++ ev_str(K.run_ev(tpl_of(k), fuel_of(k, 0n), False{})) ++
    " | evlazy " ++ evlazy_str(K.run_dev(tpl_of(k), fuel_of(k, 2n), [])) ++
    " | evtwo " ++ ev_str(K.run_two_ev(tpl_of(k), fuel_of(k, 0n), True{})) ++
    " | evprof " ++ K.profile_ev(tpl_of(k), fuel_of(k, 0n), True{}) ++
    " | prof " ++ K.profile_t(tpl_of(k), fuel_of(k, 0n), True{}) ++
    " | dc " ++ dc_str(K.run_dc(tpl_of(k), fuel_of(k, 2n), [])) ++
    " | dcs " ++ dc_str(K.run_ds.s(tpl_of(k), fuel_of(k, 2n), []))

def all(n: Nat, +k: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      one(k) ++ "\n" ++ all(p, (k + 1 : U32))

def main() -> IO(Unit):
  IO.print(all(COUNT, 0) ++ "events tables: " ++ KN.ev_tables() ++ "\nbuiltin fields: " ++ KN.builtin_fields())
'''


def program(cs, out):
    rel = os.path.relpath(SPIKE, out)
    lines = ["import Base"]
    for mod, alias in [("val", "V"), ("net", "N"), ("tpl", "T"), ("nets", "X"), ("kernel", "K"), ("knet", "KN")]:
        lines.append(f"import {rel}/{mod}.bend as {alias}")
    lines += ["", "# Written by spike/tools/library.py from spike/library.txt; do not edit.", ""]
    for i, c in enumerate(cs):
        lines.append(f"# {c.entry}, {c.mode}\ndef t{i}() -> T.Tpl:\n  {terms.bend_tpl(c.net, c.root)}\n")
    lines.append("def tpl_of(+k: U32) -> T.Tpl:\n  match k:")
    for i in range(len(cs)):
        lines.append(f"    case {i}:\n      t{i}()")
    lines.append(f"    case _:\n      t{len(cs) - 1}()\n")
    # case k's fuel for the full reductions (0), the spike (1), whose fuel
    # counts rounds of 64 interactions (tpl.bend's run), and demand (2)
    lines.append("def fuel.go(+f: Nat, +who: Nat) -> Nat:\n  match who:\n    case 0n:\n      f\n"
                 "    case 1n:\n      Nat.div(f, 64n)\n    case _:\n      Nat.mul(f, 2n)\n")
    lines.append("def fuel_of(+k: U32, +who: Nat) -> Nat:\n  match k:")
    for i, c in enumerate(cs):
        lines.append(f"    case {i}:\n      fuel.go({c.fuel}n, who)")
    lines.append(f"    case _:\n      fuel.go({FUEL}n, who)\n")
    lines.append(MAIN.replace("COUNT", f"{len(cs)}n"))
    path = os.path.join(out, "library.bend")
    with open(path, "w") as f:
        f.write("\n".join(lines))
    return path


RES = r"(\S+) \((\d+), (\d+)\)(!?)"
LAZY = r"(.+?), (\d+) live of (\d+), (\d+) reached"
LINE = re.compile(rf"#(\d+): spike (\S+) \((\d+), (\d+)\) \| ref {RES} \| fast {RES} \| lazy {RES} {LAZY} \| two {RES}"
                  rf" \| ev {RES} ev (\d+) \| evref {RES} ev (\d+) \| evlazy {RES} {LAZY} ev (\d+) \| evtwo {RES} ev (\d+)"
                  r" \| evprof (.+?) \((\d+), (\d+)\); logical (\d+|past 2\^48), (\d+) peels, (\d+) wide; pairs[^|;]*;"
                  r" events (\d+) by kind([^|]*)"
                  r" \| prof (.+?) \((\d+), (\d+)\); logical (\d+|past 2\^48), (\d+) peels, (\d+) wide; pairs([^|]*)"
                  rf" \| dc {RES} {LAZY} cyc (\d+) itrs (\d+) ev (\d+) scan (\d+)"
                  rf" \| dcs {RES} {LAZY} cyc (\d+) itrs (\d+) ev (\d+) scan (\d+)$")


class Run:
    def __init__(self, g):
        self.spike = (g[1], int(g[2]), int(g[3]))
        self.ref = (g[4], int(g[5]), int(g[6]), g[7])
        self.fast = (g[8], int(g[9]), int(g[10]), g[11])
        self.lazy = (g[12], int(g[13]), int(g[14]), g[15])
        self.state, self.live, self.cap, self.reach = g[16], int(g[17]), int(g[18]), int(g[19])
        self.two = (g[20], int(g[21]), int(g[22]), g[23])
        # the erasure modes: value, interactions, errors, table, events
        self.ev = (g[24], int(g[25]), int(g[26]), g[27], int(g[28]))
        self.evref = (g[29], int(g[30]), int(g[31]), g[32], int(g[33]))
        self.evlazy = (g[34], int(g[35]), int(g[36]), g[37], int(g[42]))
        self.evstate, self.evlive = g[38], int(g[39])
        self.evtwo = (g[43], int(g[44]), int(g[45]), g[46], int(g[47]))
        # profiled with events: value, interactions, errors; its events,
        # logical interactions and events by kind
        self.evprof = (g[48], int(g[49]), int(g[50]))
        self.evprof_n = int(g[54])
        self.evlogical = None if g[51].startswith("past") else int(g[51])
        self.evkinds = g[55].strip()
        self.prof = (g[56], int(g[57]), int(g[58]))
        self.logical = None if g[59].startswith("past") else int(g[59])
        self.peels, self.wide = int(g[60]), int(g[61])
        # demand collecting where its net would grow (heap-strategies.
        # erasure.load.cycle): its result, its interactions the total; the
        # collections, their interactions and events, the capacity scanned
        self.dc = (g[-24], int(g[-23]), int(g[-22]), g[-21])
        self.dcstate, self.dclive, self.dccap = g[-20], int(g[-19]), int(g[-18])
        self.dccyc, self.dcitrs, self.dcev, self.dcscan = int(g[-16]), int(g[-15]), int(g[-14]), int(g[-13])
        # its stress test: its result and its collections
        self.dcs = (g[-12], int(g[-11]), int(g[-10]), g[-9])
        self.dcsstate, self.dcscyc = g[-8], int(g[-4])


def check(c, r):
    """the failures of case c in run r"""
    bad = []
    m, d, u = WANT.match(c.want), DEMAND.match(c.want), UNSCOPED.match(c.want)
    if c.want == "wrong":
        if r.fast[0] == str(c.value):
            bad.append(f"marked wrong, but gives {c.value}: update the library")
    elif c.want == "cycle":
        if r.state != "a cycle":
            bad.append(f"demand ends {r.state}, not a cycle")
        if r.fast[0] != "none":
            bad.append(f"the full reduction gives {r.fast[0]}")
        if r.evstate != "a cycle":
            bad.append(f"demand with events ends {r.evstate}, not a cycle")

        if r.ev[0] != "none":
            bad.append(f"the full reduction with events gives {r.ev[0]}")
    elif c.want == "void":
        for label, st in (("demand", r.state), ("demand with events", r.evstate)):
            if st != "a void":
                bad.append(f"{label} ends {st}, not a void")
        for label, res in (("fast", r.fast), ("ev", r.ev)):
            if res[0] != "none":
                bad.append(f"the full reduction ({label}) gives {res[0]}")
    elif u:
        if r.state != "unscoped":
            bad.append(f"demand ends {r.state}, not unscoped")
        if r.evstate != "unscoped":
            bad.append(f"demand with events ends {r.evstate}, not unscoped")
        for label, res in (("spike", r.spike), ("ref", r.ref), ("fast", r.fast), ("two", r.two), ("profile", r.prof),
                           ("ev", r.ev), ("evref", r.evref), ("evtwo", r.evtwo), ("evprofile", r.evprof)):
            if res[0] != u.group(1):
                bad.append(f"{label} gives {res[0]}, not {u.group(1)}")
    elif d:
        if c.value is not None and d.group(1) != str(c.value):
            bad.append(f"the library says {d.group(1)}, the evaluator {c.value}")
        if r.lazy[0] != d.group(1) or r.state != "done":
            bad.append(f"demand gives {r.lazy[0]}, {r.state}, not {d.group(1)}")
        if r.evlazy[0] != d.group(1) or r.evstate != "done":
            bad.append(f"demand with events gives {r.evlazy[0]}, {r.evstate}, not {d.group(1)}")

    elif not m:
        bad.append(f"wants `{c.want}`, not `VALUE logical L peels P` (--update fills them)")
    if m:
        want = m.group(1)
        if c.value is not None and want != str(c.value):
            bad.append(f"the library says {want}, the evaluator {c.value}")
        for label, res in (("spike", r.spike), ("ref", r.ref), ("fast", r.fast), ("lazy", r.lazy), ("two", r.two),
                           ("profile", r.prof), ("ev", r.ev), ("evref", r.evref), ("evlazy", r.evlazy),
                           ("evtwo", r.evtwo), ("evprofile", r.evprof)):
            if res[0] != want and not (label in ("profile", "evprofile") and res[0] == "no value" and want == "none"):
                bad.append(f"{label} gives {res[0]}, not {want}")
        if r.logical != int(m.group(2)):
            bad.append(f"{r.logical} logical interactions, not {m.group(2)}")
        if r.peels != int(m.group(3)):
            bad.append(f"{r.peels} peels, not {m.group(3)}")
        if r.state != "done":
            bad.append(f"demand ends {r.state}")
        if r.evstate != "done":
            bad.append(f"demand with events ends {r.evstate}")

        if r.lazy[1] > r.fast[1]:
            bad.append(f"demand makes {r.lazy[1]} interactions, the full reduction {r.fast[1]}")
    for label, res in (("spike", r.spike), ("ref", r.ref), ("fast", r.fast), ("lazy", r.lazy), ("two", r.two),
                       ("profile", r.prof), ("ev", r.ev), ("evref", r.evref), ("evlazy", r.evlazy),
                       ("evtwo", r.evtwo), ("evprofile", r.evprof), ("collecting", r.dc),
                       ("collecting under stress", r.dcs)):
        if res[2]:
            bad.append(f"{label} counts {res[2]} errors")
        if len(res) > 3 and res[3]:
            bad.append(f"{label}'s data table or free list out of step")
    # demand collecting keeps demand's value and its state
    # (heap-strategies.erasure.load.cycle)
    if r.dc[0] != r.lazy[0] or r.dcstate != r.state:
        bad.append(f"demand collecting: {r.dc[0]}, {r.dcstate}, where demand gave {r.lazy[0]}, {r.state}")
    if r.dcs[0] != r.lazy[0] or r.dcsstate != r.state:
        bad.append(f"demand collecting under stress: {r.dcs[0]}, {r.dcsstate}, where demand gave {r.lazy[0]}, {r.state}")
    if r.ref[1] != r.fast[1] or r.prof[1] != r.fast[1]:
        bad.append(f"interactions differ: ref {r.ref[1]}, fast {r.fast[1]}, profile {r.prof[1]}")
    if r.evref[1] != r.ev[1] or r.evref[4] != r.ev[4] or r.evprof[1] != r.ev[1] or r.evprof_n != r.ev[4]:
        bad.append(f"with events, interactions or events differ: evref {r.evref[1]}, {r.evref[4]},"
                   f" ev {r.ev[1]}, {r.ev[4]}, evprofile {r.evprof[1]}, {r.evprof_n}")
    if r.wide:
        bad.append(f"{r.wide} interactions too wide to count as logical ones")
    return bad


def store(note, out, runs):
    R = [sys.executable, "-I", os.path.join(ROOT, "scripts", "results.py")]
    run = subprocess.run(R + ["run", "library", f'{{"fuel": {FUEL}, "cases": {len(runs)}}}', note],
                         capture_output=True, text=True, check=True).stdout.strip()
    rows = os.path.join(out, "rows.tsv")
    with open(rows, "w") as f:
        for c, r in runs:
            f.write("\t".join(str(x) for x in (
                c.entry, c.mode, int(not check(c, r)), r.fast[0], r.spike[1], r.fast[1], r.lazy[1],
                "" if r.logical is None else r.logical, r.peels, r.two[1])) + "\n")
    subprocess.run(R + ["library", run, rows], check=True)
    evrows = os.path.join(out, "evrows.tsv")
    with open(evrows, "w") as f:
        for c, r in runs:
            f.write("\t".join(str(x) for x in (
                c.entry, c.mode, r.ev[1], r.ev[4], r.evlazy[1], r.evlazy[4], r.evlive, r.evtwo[1], r.evtwo[4],
                r.live, "" if r.evlogical is None else r.evlogical, r.evkinds, r.cap, r.dc[1], r.dccap, r.dclive,
                r.dccyc, r.dcitrs, r.dcev, r.dcscan)) + "\n")
    subprocess.run(R + ["library_ev", run, evrows], check=True)
    return run


def main(argv):
    sys.setrecursionlimit(100000)
    update = "--update" in argv
    note = None
    if "--store" in argv:
        i = argv.index("--store")
        note = argv[i + 1]
        argv = argv[:i] + argv[i + 2:]
    argv = [a for a in argv if a != "--update"]
    if not argv:
        print(__doc__.strip())
        return 2
    out = os.path.abspath(argv[0])
    os.makedirs(out, exist_ok=True)
    lines = open(LIBRARY).read().split("\n")
    cs = cases(entries(lines), set(argv[1:]))
    failing = 0
    for c in cs:
        bad = polarity.check(c.net, c.root)
        if bad:
            failing += 1
            print(f"FAIL {c.entry} {c.mode}: not polarized: {bad[:3]}")
        # a net built with a vicious circle is kept to show demand finding it
        circles = polarity.vicious(c.net, c.root)
        if circles and c.want != "cycle":
            failing += 1
            print(f"FAIL {c.entry} {c.mode}: vicious circles {circles[:3]}, but no cycle expected")
        # and one with a function's argument used outside its body to show
        # demand reporting it (net-scoped-arguments)
        loose = polarity.unscoped(c.net, c.root)
        if bool(loose) != bool(UNSCOPED.match(c.want)):
            failing += 1
            print(f"FAIL {c.entry} {c.mode}: " + (f"functions {loose[:3]} with an argument used outside the body,"
                                                  " but not expected unscoped" if loose else
                                                  "expected unscoped, but every argument is used within its body"))
    if failing:
        return 1
    path = program(cs, out)
    exe = os.path.join(out, "library")
    bend = os.environ.get("BEND", "bend")
    capped = os.path.join(ROOT, "scripts", "capped.sh")
    subprocess.run([capped] + cap("LIBRARY_BUILD_CAP", BUILD_CAP) + [bend, os.path.basename(path), "-o", "library"],
                   cwd=out, check=True, stdout=subprocess.DEVNULL)
    res = subprocess.run([capped] + cap("LIBRARY_RUN_CAP", RUN_CAP) + [exe], capture_output=True, text=True)
    if res.returncode == 137:
        failing += 1
        print("FAIL the run: " + (res.stderr.strip().splitlines() or ["killed"])[-1])
    with open(os.path.join(out, "out.txt"), "w") as f:
        f.write(res.stdout)
    got = {}
    for line in res.stdout.splitlines():
        m = LINE.match(line)
        if m:
            got[int(m.group(1))] = Run(m.groups())
    # the kernel's events tables against the model, every kind code a
    # header holds (knet.bend's ev_tables)
    tables = [l for l in res.stdout.splitlines() if l.startswith("events tables: ")]
    if tables != ["events tables: ok"]:
        failing += 1
        print("FAIL the events tables: " + (tables[0][len("events tables: "):] if tables else "no result"))
    fields = [l for l in res.stdout.splitlines() if l.startswith("builtin fields: ")]
    if fields != ["builtin fields: ok"]:
        failing += 1
        print("FAIL the builtin fields: " + (fields[0][len("builtin fields: "):] if fields else "no result"))
    runs = []
    for i, c in enumerate(cs):
        r = got.get(i)
        if r is None:
            failing += 1
            print(f"FAIL {c.entry} {c.mode}: no result (the run's status {res.returncode})")
            continue
        runs.append((c, r))
        if update and c.want not in ("wrong", "cycle", "void") and not DEMAND.match(c.want) and not UNSCOPED.match(c.want):
            w = WANT.match(c.want)
            lines[c.line] = f"{c.mode}: {w.group(1) if w else c.want.split()[0]} logical {r.logical} peels {r.peels}"
            c.want = lines[c.line].partition(": ")[2]
        bad = check(c, r)
        saved = "" if not r.logical else f" ({100 * (r.logical - r.fast[1]) // r.logical}% fused away)"
        if bad:
            failing += 1
            print(f"FAIL {c.entry} {c.mode}: " + "; ".join(bad))
        else:
            print(f"ok   {c.entry} {c.mode}: {r.fast[0]} in {r.fast[1]} interactions, demand {r.lazy[1]}"
                  f" ({r.live} live of {r.cap}, {r.reach} reached),"
                  f" two stacks {r.two[1]}, logical {r.logical}{saved}, {r.peels} peels;"
                  f" events: eager {r.ev[1]}+{r.ev[4]} (logical {r.evlogical}), demand {r.evlazy[1]}+{r.evlazy[4]}"
                  f" ({r.evlive} live), two {r.evtwo[1]}+{r.evtwo[4]};"
                  f" collecting: {r.dc[1]} interactions in all, {r.dccyc} collections ({r.dcitrs} interactions,"
                  f" {r.dcev} events, {r.dcscan} nodes scanned), {r.dclive} live of {r.dccap};"
                  f" under stress {r.dcscyc} collections")
    if update:
        with open(LIBRARY, "w") as f:
            f.write("\n".join(lines))
    if note is not None and runs:
        print("store run", store(note, out, runs))
    print(f"{len(cs)} cases, {failing} failing")
    return 1 if failing else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
