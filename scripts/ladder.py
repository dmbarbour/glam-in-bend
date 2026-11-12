#!/usr/bin/env python3
"""The hello ladder's check (HelloLadder): the assembler built from
glam/main.bend, then each sample of glam/ladder.txt run through it. A
sample under samples/hello/ must write `Hello, World!` to stdout and exit
0 (samples/README.md: every hello sample produces it); one under
samples/invalid/ must exit 1 and report, on stderr, every line of its
.expect file, `severity|line|substring...`: a diagnostic of that severity
at that line whose message holds every substring (the shell writes them
as `error at line N: message`).

Each hello sample runs twice: as the assembler runs it, top-level functions
as templates spliced where they are applied, and with `--link`, every
definition linked statically as before templates. Where the linked run
succeeds, both must write the same bytes (the Cells plan, re-scoped by the
bridge: a differential run against the linker); a sample the linker
refuses, such as a recursive one, is compared with nothing.

Then the sharing families of glam/sharing.txt (the Cells plan's
cells-freeze.sharing): each sample applies a prefix to a string literal,
nested 1, 2, 4 and 8 times into a copy under results/sharing/, run with
`--count` both ways. Every size must write the same bytes both ways, and
from 4 uses to 8 a use may cost at most SLACK_ITRS interactions more than
it does linked and at most SLACK_SPLICES splices: work that needs no
argument is done once, however many times it is used. A family marked
`loss` is known not to share until its step is built, and fails once it
shares, until the mark is removed. What the check cannot see: a splice
is no interaction, so the size of the copies is invisible to it, and
only their number is bounded.

Every hello sample and every size of a sharing family runs a third way,
with `--refreeze`: each template loaded and frozen back before the run
(glam/freeze.bend, the Cells plan's cells-freeze.cursors). It must write
the same bytes and report the same counts as the plain run. Then each
unit test of TESTS runs, `bend` printing `"ok"` alone, its pass kept as
the build is while its inputs are unchanged.

The build is kept while its inputs are unchanged, keyed as scripts/kept.py
keys a check (the file and every file it imports, and Bend as it stands),
at results/build/glam with its key beside it; a build is about 30 s.

    python3 -I scripts/ladder.py            check every listed sample
    python3 -I scripts/ladder.py --fresh    build again whatever the key
"""
import os
import re
import subprocess
import sys

os.environ["BEND_NO_TELEMETRY"] = "1"

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import kept  # noqa: E402

MAIN = os.path.join(ROOT, "glam", "main.bend")
LIST = os.path.join(ROOT, "glam", "ladder.txt")
SHARING = os.path.join(ROOT, "glam", "sharing.txt")
NESTED = os.path.join(ROOT, "results", "sharing")
USES = (1, 2, 4, 8)
SLACK_ITRS = 8
SLACK_SPLICES = 2
EXE = os.path.join(ROOT, "results", "build", "glam")
HELLO = b"Hello, World!"
TESTS = [os.path.join(ROOT, "glam", "test_freeze.bend"), os.path.join(ROOT, "glam", "test_cursor.bend")]


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


def linked_differs(path, stdout):
    """the bytes the linked run writes, where it succeeds and they differ"""
    r = subprocess.run([EXE, "-f", os.path.join(ROOT, path), "--link"], capture_output=True)
    if r.returncode == 0 and r.stdout != stdout:
        return r.stdout
    return None


def refreeze_differs(path):
    """the counted run and the refrozen one, where they differ"""
    a = subprocess.run([EXE, "-f", path, "--count"], capture_output=True)
    b = subprocess.run([EXE, "-f", path, "--count", "--refreeze"], capture_output=True)
    if (a.returncode, a.stdout, a.stderr) != (b.returncode, b.stdout, b.stderr):
        return (a.stdout + a.stderr, b.stdout + b.stderr)
    return None


def run_one(rung, path):
    r = subprocess.run([EXE, "-f", os.path.join(ROOT, path)], capture_output=True)
    err = r.stderr.decode("utf-8", "replace")
    if path.startswith("samples/hello/"):
        if r.returncode != 0 or r.stdout != HELLO:
            return f"FAIL {rung} {path}: exit {r.returncode}, stdout {r.stdout!r}\n{err}"
        other = linked_differs(path, r.stdout)
        if other is not None:
            return f"FAIL {rung} {path}: with --link it writes {other!r}"
        rf = refreeze_differs(os.path.join(ROOT, path))
        if rf is not None:
            return f"FAIL {rung} {path}: with --refreeze {rf[1]!r}, plainly {rf[0]!r}"
        return None
    expect = os.path.join(ROOT, path[:-2] + ".expect")
    if r.returncode != 1:
        return f"FAIL {rung} {path}: exit {r.returncode}, expected 1\n{err}"
    missed = expect_ok(expect, diagnostics(err))
    if missed:
        return f"FAIL {rung} {path}: not reported: {'; '.join(missed)}\n{err}"
    return None


def families():
    """(step, path, known loss, prefix) for each line of glam/sharing.txt"""
    out = []
    with open(SHARING) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            step, path, mark, prefix = line.split(None, 3)
            out.append((step, path, mark == "loss", prefix))
    return out


def nested(path, prefix, n):
    """the sample with `prefix "..."` applied n times, written under
    results/sharing/; None where the prefix is not met exactly once"""
    with open(os.path.join(ROOT, path)) as f:
        src = f.read()
    at = re.compile(r"(?<![\w'.])" + re.escape(prefix) + r' ("[^"]*")')
    if len(at.findall(src)) != 1:
        return None
    def wrap(m):
        inner = m.group(1)
        for _ in range(n):
            inner = f"{prefix} ({inner})"
        return inner
    os.makedirs(NESTED, exist_ok=True)
    out = os.path.join(NESTED, f"{os.path.basename(path)[:-2]}_{n}.g")
    with open(out, "w") as f:
        f.write(at.sub(wrap, src))
    return out


def counted(path, linked):
    """(stdout, interactions, splices) of a run with --count; None on failure"""
    args = [EXE, "-f", path, "--count"] + (["--link"] if linked else [])
    r = subprocess.run(args, capture_output=True)
    m = re.search(rb"(\d+) interactions, (\d+) splices", r.stderr)
    if r.returncode != 0 or not m:
        return None
    return r.stdout, int(m.group(1)), int(m.group(2))


def family(step, path, loss, prefix):
    """None if the family behaves as its mark says, else what went wrong"""
    runs = {}
    for n in USES:
        src = nested(path, prefix, n)
        if src is None:
            return f"FAIL {step} {path}: `{prefix} \"...\"` must occur exactly once"
        t, l = counted(src, False), counted(src, True)
        if t is None or l is None:
            return f"FAIL {step} {path}: the run at {n} uses failed"
        if t[0] != l[0]:
            return f"FAIL {step} {path}: at {n} uses it writes {t[0]!r}, linked {l[0]!r}"
        rf = refreeze_differs(src)
        if rf is not None:
            return f"FAIL {step} {path}: at {n} uses, with --refreeze {rf[1]!r}, plainly {rf[0]!r}"
        runs[n] = (t[1], t[2], l[1])
    a, b = runs[USES[-2]], runs[USES[-1]]
    per = USES[-1] - USES[-2]
    itrs, splices, linked = (b[0] - a[0]) / per, (b[1] - a[1]) / per, (b[2] - a[2]) / per
    shares = itrs <= linked + SLACK_ITRS and splices <= SLACK_SPLICES
    said = f"a use costs {itrs:g} interactions and {splices:g} splices, {linked:g} linked"
    if shares and loss:
        return f"FAIL {step} {path}: marked a loss, but it shares ({said}): remove its mark"
    if not shares and not loss:
        return f"FAIL {step} {path}: does not share ({said})"
    return ("known loss" if loss else "ok") + f" {step} {path}: {said}"


def unit_test(path):
    """None if the test prints "ok" alone, its pass kept; else the failure"""
    bend = kept.bend_exe()
    key = kept.key(path, kept.tool_key(bend), "test")
    keyfile = os.path.join(ROOT, "results", "build", os.path.basename(path) + ".key")
    if os.path.exists(keyfile):
        with open(keyfile) as f:
            if f.read().strip() == key:
                return None
    r = subprocess.run([os.path.join(HERE, "capped.sh"), "2000", "300", bend, path],
                       capture_output=True, text=True)
    if r.returncode != 0 or r.stdout.strip() != '"ok"':
        return f"FAIL {os.path.relpath(path, ROOT)}: {(r.stdout + r.stderr).strip()[-600:]}"
    with open(keyfile, "w") as f:
        f.write(key + "\n")
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
    fs = families()
    bad_fs, losses = 0, 0
    for step, path, loss, prefix in fs:
        said = family(step, path, loss, prefix)
        print(said)
        if said.startswith("FAIL"):
            bad_fs += 1
        elif loss:
            losses += 1
    bad_ts = 0
    for t in TESTS:
        said = unit_test(t)
        if said:
            bad_ts += 1
            print(said)
        else:
            print(f"ok test {os.path.relpath(t, ROOT)}")
    print(f"{len(ss)} samples, {failures} failing; {len(fs)} sharing families, "
          f"{bad_fs} failing, {losses} known losses; {len(TESTS)} tests, {bad_ts} failing")
    return 1 if failures or bad_fs or bad_ts else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
