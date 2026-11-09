#!/usr/bin/env python3
"""The hello ladder's check (HelloLadder): the assembler built from
glam/main.bend, then each sample of glam/ladder.txt run through it. A
sample under samples/hello/ must write `Hello, World!` to stdout and exit
0 (samples/README.md: every hello sample produces it); one under
samples/invalid/ must exit 1 and report, on stderr, every line of its
.expect file, `severity|line|substring...`: a diagnostic of that severity
at that line whose message holds every substring (the shell writes them
as `error at line N: message`).

The build is kept while its inputs are unchanged, keyed as scripts/kept.py
keys a check (the file and every file it imports, and Bend as it stands),
at results/build/glam with its key beside it; a build is about 30 s.

    python3 -I scripts/ladder.py            check every listed sample
    python3 -I scripts/ladder.py --fresh    build again whatever the key
"""
import os
import subprocess
import sys

os.environ["BEND_NO_TELEMETRY"] = "1"

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import kept  # noqa: E402

MAIN = os.path.join(ROOT, "glam", "main.bend")
LIST = os.path.join(ROOT, "glam", "ladder.txt")
EXE = os.path.join(ROOT, "results", "build", "glam")
HELLO = b"Hello, World!"


def build(fresh):
    bend = kept.bend_exe()
    key = kept.key(MAIN, kept.tool_key(bend), "build")
    keyfile = EXE + ".key"
    if not fresh and os.path.exists(EXE) and os.path.exists(keyfile):
        with open(keyfile) as f:
            if f.read().strip() == key:
                return True
    os.makedirs(os.path.dirname(EXE), exist_ok=True)
    r = subprocess.run([os.path.join(HERE, "capped.sh"), "4000", "600", bend, MAIN, "-o", EXE],
                       capture_output=True, text=True)
    if r.returncode != 0 or not os.path.exists(EXE):
        print("ladder: the build failed")
        print(r.stdout + r.stderr)
        return False
    with open(keyfile, "w") as f:
        f.write(key + "\n")
    return True


def samples():
    out = []
    with open(LIST) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            rung, path = line.split()
            out.append((rung, path))
    return out


def diagnostics(stderr):
    """(severity, line, message) for each diagnostic the shell wrote."""
    out = []
    for line in stderr.splitlines():
        if line.startswith("error at line "):
            rest = line[len("error at line "):]
            n, _, msg = rest.partition(": ")
            out.append(("error", int(n), msg))
        elif line.startswith("error: "):
            out.append(("error", 0, line[len("error: "):]))
    return out


def expect_ok(expect_path, diags):
    """every .expect line met by some diagnostic; the lines not met"""
    missed = []
    with open(expect_path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split("|")
            if len(parts) < 3 or not parts[1].isdigit():
                missed.append(f"{line} (not severity|line|substring...)")
                continue
            sev, n, subs = parts[0], int(parts[1]), parts[2:]
            if not any(d[0] == sev and d[1] == n and all(s in d[2] for s in subs) for d in diags):
                missed.append(line)
    return missed


def run_one(rung, path):
    r = subprocess.run([EXE, "-f", os.path.join(ROOT, path)], capture_output=True)
    err = r.stderr.decode("utf-8", "replace")
    if path.startswith("samples/hello/"):
        if r.returncode != 0 or r.stdout != HELLO:
            return f"FAIL {rung} {path}: exit {r.returncode}, stdout {r.stdout!r}\n{err}"
        return None
    expect = os.path.join(ROOT, path[:-2] + ".expect")
    if r.returncode != 1:
        return f"FAIL {rung} {path}: exit {r.returncode}, expected 1\n{err}"
    missed = expect_ok(expect, diagnostics(err))
    if missed:
        return f"FAIL {rung} {path}: not reported: {'; '.join(missed)}\n{err}"
    return None


def main(args):
    fresh = "--fresh" in args
    if not build(fresh):
        return 1
    failures = 0
    ss = samples()
    for rung, path in ss:
        bad = run_one(rung, path)
        if bad:
            failures += 1
            print(bad)
        else:
            print(f"ok {rung} {path}")
    print(f"{len(ss)} samples, {failures} failing")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
