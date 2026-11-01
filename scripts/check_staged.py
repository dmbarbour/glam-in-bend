#!/usr/bin/env python3
"""The pre-commit hook's Bend checks, a few seconds where the gate takes
minutes: every staged Bend file typechecks (bend --check-only), and where a
staged file is a PROOF.bend or among what one imports, that proof checks
by bend (the gate rechecks it by the proven kernel, --verdict).

    check_staged.py
"""
import concurrent.futures
import os
import re
import subprocess
import sys

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                      check=True).stdout.strip()
BEND = os.environ.get("BEND") or "bend"
IMPORT = re.compile(r"^import\s+\./(\S+\.bend)\b", re.M)


def staged():
    out = subprocess.run(["git", "diff", "--cached", "--name-only", "--diff-filter=ACMR", "--", "*.bend"],
                         cwd=ROOT, capture_output=True, text=True, check=True).stdout
    return [p for p in out.split() if os.path.exists(os.path.join(ROOT, p))]


def closure(path):
    """the Bend files path imports, itself among them, by relative path"""
    seen, todo = set(), [os.path.normpath(path)]
    while todo:
        p = todo.pop()
        if p in seen or not os.path.exists(os.path.join(ROOT, p)):
            continue
        seen.add(p)
        text = open(os.path.join(ROOT, p)).read()
        todo += [os.path.normpath(os.path.join(os.path.dirname(p), m)) for m in IMPORT.findall(text)]
    return seen


def check(job):
    args, label = job
    r = subprocess.run([BEND] + args, cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        return f"{label}:\n" + "\n".join((r.stdout + r.stderr).strip().splitlines()[-20:])
    return None


def main():
    files = staged()
    jobs = [([f, "--check-only"], f) for f in files if not f.endswith(("LAWS.bend", "PROOF.bend"))]
    proofs = subprocess.run(["git", "ls-files", "--", "*PROOF.bend", ":!bench/"], cwd=ROOT, capture_output=True,
                            text=True, check=True).stdout.split()
    jobs += [([proof], proof) for proof in proofs if set(files) & closure(proof)]
    # side by side, so that a commit staging several files stays near a dozen
    # seconds
    with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count() or 4) as pool:
        failures = [f for f in pool.map(check, jobs) if f]
    for f in failures:
        print(f)
    print(f"staged Bend files: {'failed' if failures else 'ok'} ({len(files)} staged)")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
