"""Bend's checks of files, a pass kept for unchanged inputs: `verdict`,
`bend FILE --verdict`, a proof file's proofs rechecked by BendTT's kernel,
proved in Lean, far costlier than Bend's own check; `check`, `bend FILE
--check-only`, a file typechecked; `mutants`, a mutants file's mutations
tried against the laws they name (scripts/one_law.py), its inputs those
of the proof file beside it, the file itself and the scripts that try
it. Each depends only on its inputs, so a
pass is kept, keyed on them, and a file whose inputs are unchanged is not
checked again: the file and every file it imports, transitively, by their
contents; Bend (its version, its executable's size, time and inode, Base and
its effects beside it, as blend/build.sh keys its build); Lean's version;
and the check. A failure is never kept. The passes live in results/kept/
(out of git).

An import is read as Bend reads it, `import PATH [as ALIAS]` at a line's
start: a path to a local file is followed; one to none (a hub package's,
named by its hash or its name) is keyed by the path as written, the hub's
own content being fixed by it.

Run from the root of the project the files are in (the repository, or
Blend's directory), its passes kept under that project's results/kept/:
  python3 -I scripts/kept.py verdict FILE...   each file's verdict, a kept
                                               pass where its inputs are
                                               unchanged, Bend's output shown
  python3 -I scripts/kept.py check FILE...     each file typechecked, a
                                               failure's output shown, then
                                               a count
  python3 -I scripts/kept.py mutants FILE...   each mutants file tried, its
                                               output shown
  --fresh after the mode checks every file again, the kept passes ignored
  (passes still kept)
"""

import hashlib
import os
import re
import shutil
import subprocess
import sys

IMPORT = re.compile(r"^import\s+(\S+)", re.M)
CACHE = os.path.join("results", "kept")
FLAGS = {"verdict": "--verdict", "check": "--check-only"}
MODES = list(FLAGS) + ["mutants"]
# the scripts that try a mutants file, beside this one
HERE = os.path.dirname(os.path.abspath(__file__))
TRIES = [os.path.join(HERE, "one_law.py"), os.path.join(HERE, "capped.sh")]


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


def beside(path):
    """The proof file beside a mutants file, as scripts/one_law.py finds it."""
    d, b = os.path.split(os.path.normpath(path))
    return os.path.join(d, b.removesuffix("MUTANTS.txt") + "PROOF.bend")


def key(path, tools, mode):
    if mode == "mutants":
        files, others = closure(beside(path))
        for p in [path] + TRIES:
            with open(p, "rb") as f:
                files[os.path.normpath(p)] = f.read()
    else:
        files, others = closure(path)
    h = hashlib.sha256(tools + mode.encode() + b"\0")
    h.update(os.path.normpath(path).encode() + b"\0")
    for p in sorted(files):
        h.update(p.encode() + b"\0" + hashlib.sha256(files[p]).digest())
    for o in sorted(others):
        h.update(b"import\0" + o.encode())
    return h.hexdigest()


def main(args):
    mode = args[0] if args else ""
    fresh = len(args) > 1 and args[1] == "--fresh"
    paths = args[2:] if fresh else args[1:]
    if mode not in MODES or not paths:
        print("usage: python3 -I scripts/kept.py verdict|check|mutants [--fresh] FILE...", file=sys.stderr)
        return 2
    bend = bend_exe()
    tools = tool_key(bend)
    os.makedirs(CACHE, exist_ok=True)
    status, kept, ran = 0, 0, 0
    for path in paths:
        if mode == "mutants" and not os.path.isfile(beside(path)):
            print(f"{path} has no {beside(path)} beside it")
            status = 1
            continue
        mark = os.path.join(CACHE, key(path, tools, mode))
        if not fresh and os.path.exists(mark):
            kept += 1
            if mode == "verdict":
                print(f"ALL PROOFS CHECK (kept: {path} and its imports unchanged)")
            elif mode == "mutants":
                print(f"{path}: every mutation fails (kept: its inputs unchanged)")
            continue
        ran += 1
        if mode == "mutants":
            run = subprocess.run([sys.executable, "-I", TRIES[0], "--mutants", path],
                                 env=dict(os.environ, BEND=bend))
        elif mode == "verdict":
            run = subprocess.run([bend, path, FLAGS[mode]])
        else:
            run = subprocess.run([bend, path, FLAGS[mode]], capture_output=True, text=True)
            if run.returncode != 0:
                print(f"{path}:\n{run.stdout}{run.stderr}", end="")
        if run.returncode == 0:
            with open(mark, "w") as f:
                f.write(f"{mode} {path}\n")
        else:
            status = 1
    if mode == "check":
        print(f"bend files: {'ok' if status == 0 else 'failures'} ({ran} checked, {kept} kept)")
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
