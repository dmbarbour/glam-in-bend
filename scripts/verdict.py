"""Bend's verdict on proof files, cached: `bend FILE --verdict` rechecks a
proof file's proofs by BendTT's kernel, proved in Lean, and costs far more
than Bend's own check. A verdict depends only on its inputs, so a pass is
kept, keyed on them, and a file whose inputs are unchanged is not rechecked:
the file and every file it imports, transitively, by their contents; Bend
(its version, its executable's size, time and inode, Base and its effects
beside it, as blend/build.sh keys its build); and Lean's version. A failure
is never kept. The passes live in results/verdicts/ (out of git).

An import is read as Bend reads it, `import PATH [as ALIAS]` at a line's
start: a path to a local file is followed; one to none (a hub package's,
named by its hash or its name) is keyed by the path as written, the hub's
own content being fixed by it.

Run from the repository root:
  python3 -I scripts/verdict.py FILE...           each file's verdict, a
                                                  kept pass where its inputs
                                                  are unchanged
  python3 -I scripts/verdict.py --fresh FILE...   each rechecked, the cache
                                                  ignored (passes still kept)
"""

import hashlib
import os
import re
import shutil
import subprocess
import sys

IMPORT = re.compile(r"^import\s+(\S+)", re.M)
CACHE = os.path.join("results", "verdicts")


def bend_exe():
    return os.environ.get("BEND") or shutil.which("bend") or os.path.expanduser("~/.bend/bin/bend")


def tool_key(bend):
    """Bend and Lean, as they stand: what a verdict depends on besides the
    files."""
    h = hashlib.sha256()
    h.update(subprocess.run([bend, "version"], capture_output=True).stdout)
    real = os.path.realpath(shutil.which(bend) or bend)
    st = os.stat(real)
    h.update(f"{st.st_size} {st.st_mtime_ns} {st.st_ino}".encode())
    lib = os.path.join(os.path.dirname(real), "..", "bend2")
    for path in [os.path.join(lib, "base.bend")] + sorted(
            os.path.join(lib, "effs", n) for n in os.listdir(os.path.join(lib, "effs"))):
        with open(path, "rb") as f:
            h.update(path.encode() + b"\0" + f.read())
    lean = shutil.which("lean") or os.path.expanduser("~/.lean/bin/lean")
    if os.path.exists(lean):
        h.update(subprocess.run([lean, "--version"], capture_output=True).stdout)
    return h.digest()


def closure(path):
    """The file and every local file it imports, transitively; the paths of
    imports of no local file, as written."""
    files, others, todo = {}, set(), [os.path.normpath(path)]
    while todo:
        p = todo.pop()
        if p in files:
            continue
        with open(p, "rb") as f:
            files[p] = f.read()
        for imp in IMPORT.findall(files[p].decode("utf-8", "replace")):
            if not imp.endswith(".bend"):
                others.add(imp)
                continue
            q = os.path.normpath(os.path.join(os.path.dirname(p), imp))
            if os.path.isfile(q):
                todo.append(q)
            else:
                others.add(imp)
    return files, others


def key(path, tools):
    files, others = closure(path)
    h = hashlib.sha256(tools)
    h.update(os.path.normpath(path).encode() + b"\0")
    for p in sorted(files):
        h.update(p.encode() + b"\0" + hashlib.sha256(files[p]).digest())
    for o in sorted(others):
        h.update(b"import\0" + o.encode())
    return h.hexdigest()


def main(args):
    fresh = bool(args) and args[0] == "--fresh"
    paths = args[1:] if fresh else args
    if not paths:
        print("usage: python3 -I scripts/verdict.py [--fresh] FILE...", file=sys.stderr)
        return 2
    bend = bend_exe()
    tools = tool_key(bend)
    os.makedirs(CACHE, exist_ok=True)
    status = 0
    for path in paths:
        mark = os.path.join(CACHE, key(path, tools))
        if not fresh and os.path.exists(mark):
            print(f"ALL PROOFS CHECK (kept: {path} and its imports unchanged)")
            continue
        run = subprocess.run([bend, path, "--verdict"])
        if run.returncode == 0:
            with open(mark, "w") as f:
                f.write(path + "\n")
        else:
            status = 1
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
