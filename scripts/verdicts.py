#!/usr/bin/env python3
"""The gate's verdicts (scripts/check.sh, section proofs), run at once as
far as memory holds them.

    python3 -I scripts/verdicts.py VDIR PAR FILE...

For each proof file FILE, `scripts/kept.py verdict FILE` runs, its output
written to VDIR/NAME.log, its status to NAME.status and its seconds to
NAME.time, NAME the file's path with `/` as `_`, as check.sh prints them.
With PAR 0 they run one after another (BendTT not yet built, its build
run once). Else they start longest first, by the last verdict's time
(NAME.runtime, a kept pass's not counted), while
the peaks they reached when last run, each from NAME.peak (4000 MB where
none is known), fit within the memory free at the start
(scripts/mem_avail.py, the container's limit counted) less a reserve.
One runs alone when nothing else does, whatever its peak. Each runs under
scripts/capped.sh at that free memory, so that one outgrowing it is
killed, not the container; where capped.sh caps by cgroup it reports
the run's peak, kept for the next gate.

The verdicts once all started together: five, 11.5 GB at their peaks,
past the container's 10 GiB, killed it with the session (2026-11-25;
glam/MATERIALIZE_PROOF.bend's 3.7 GB and POSITION_PROOF's 3.5 GB the
largest).
"""
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
UNKNOWN_MB = 4000
RESERVE_MB = 500
PEAK = re.compile(r"^capped\.sh: peak (\d+) MB, [0-9.]+ s\n?", re.M)


def load(path, default):
    try:
        with open(path) as f:
            return type(default)(float(f.read().strip()))
    except (OSError, ValueError):
        return default


def avail_mb():
    out = subprocess.run([sys.executable, "-I", os.path.join(HERE, "mem_avail.py")],
                         capture_output=True, text=True)
    try:
        return int(out.stdout.strip())
    except ValueError:
        return UNKNOWN_MB


def main(args):
    if len(args) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    vdir, par, files = args[0], args[1] == "1", args[2:]
    os.makedirs(vdir, exist_ok=True)
    name = {f: f.replace("/", "_") for f in files}
    peak = {f: load(f"{vdir}/{name[f]}.peak", UNKNOWN_MB) for f in files}
    last = {f: load(f"{vdir}/{name[f]}.runtime", 1e9) for f in files}
    budget = max(1, avail_mb() - RESERVE_MB)
    queue = sorted(files, key=lambda f: -last[f])
    running = {}  # file -> (process, start)

    def start(f):
        cmd = [os.path.join(HERE, "capped.sh"), str(budget), "3000",
               sys.executable, "-I", os.path.join(HERE, "kept.py"), "verdict", f]
        env = dict(os.environ, CAPPED_REPORT="1")
        log = open(f"{vdir}/{name[f]}.raw", "w")
        running[f] = (subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT, env=env), time.time(), log)

    def finish(f):
        proc, t0, log = running.pop(f)
        log.close()
        with open(f"{vdir}/{name[f]}.raw") as r:
            text = r.read()
        os.remove(f"{vdir}/{name[f]}.raw")
        m = PEAK.search(text)
        text = PEAK.sub("", text)
        with open(f"{vdir}/{name[f]}.log", "w") as w:
            w.write(text)
        with open(f"{vdir}/{name[f]}.status", "w") as w:
            w.write(f"{proc.returncode}\n")
        with open(f"{vdir}/{name[f]}.time", "w") as w:
            w.write(f"{time.time() - t0:.1f}\n")
        # a kept pass ran nothing: the peak and time a run would take stay
        # as known
        if "(kept:" not in text:
            with open(f"{vdir}/{name[f]}.runtime", "w") as w:
                w.write(f"{time.time() - t0:.1f}\n")
            if m:
                with open(f"{vdir}/{name[f]}.peak", "w") as w:
                    w.write(f"{m.group(1)}\n")

    while queue or running:
        # start what fits: the first in the queue whose peak fits beside
        # the running ones', or the first at all when none runs
        held = sum(peak[f] for f in running)
        fits = [f for f in queue if not running or (par and held + peak[f] <= budget)]
        if fits:
            f = fits[0]
            queue.remove(f)
            start(f)
            continue
        time.sleep(0.2)
        for f in [f for f, (p, _, _) in running.items() if p.poll() is not None]:
            finish(f)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
