"""One law checked alone, and mutations of the code tried against it.

Bend reports only the first proof that fails, often of an earlier law a
mutation breaks too; and a whole proof file is slow to recheck while one
law is being written. This copies a proof file and every local file it
imports, transitively, into results/one_law/ (out of git), cuts the laws
file it imports to the one law (and those whose proofs its proof calls),
and the proof file to that law's proof and the defs it reaches, then
runs `bend` on the copy. A proof file that
imports no laws file is cut to the def LAW names.

With --mutants FILE, each mutation of FILE naming the law is tried on a
copy of its own, after the copy unmutated (the control): a law that
survives a mutation of what it is about claims less than meant
(docs/Proving.md). FILE holds mutations as

    === NAME LAW...
    a line or two on what it breaks
    --- PATH
    the code, verbatim, to replace
    +++
    its replacement, verbatim

PATH relative to the proof file's directory, the code found there exactly
once; lines before the first `===` are comments. A mutants file sits
beside its proof file, as a laws file does: MUTANTS.txt beside PROOF.bend,
X_MUTANTS.txt beside X_PROOF.bend. Given only the mutants file, every law
it names is tried, as the gate does (scripts/check.sh, through
scripts/kept.py). Exits 0 where each control passes and every mutation
fails, 1 otherwise, 2 on bad usage.

Run from the root of the project the proof file is in (the repository, or
Blend's directory), its copies written under that project's results/:
  python3 -I scripts/one_law.py PROOF LAW              the law checked alone
  python3 -I scripts/one_law.py PROOF LAW --mutants FILE
                                                       and each of FILE's
                                                       mutations naming it
  python3 -I scripts/one_law.py --mutants FILE         every law FILE
                                                       names, against the
                                                       proof file beside it
  --cap MB SECONDS   each run's cap (scripts/capped.sh), 3000 MB 300 s by
                     default
"""

import os
import re
import shutil
import subprocess
import sys

IMPORT = re.compile(r"^import\s+(\S+)(?:\s+as\s+(\S+))?", re.M)
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_.]*")
OUT = os.path.join("results", "one_law")


def closure(path):
    """The file and every local file it imports, transitively, by path."""
    files, todo = {}, [os.path.normpath(path)]
    while todo:
        p = todo.pop()
        if p in files:
            continue
        with open(p) as f:
            files[p] = f.read()
        for imp, _ in IMPORT.findall(files[p]):
            q = os.path.normpath(os.path.join(os.path.dirname(p), imp))
            if imp.endswith(".bend") and os.path.isfile(q):
                todo.append(q)
    return files


def items(text):
    """The file's top-level items, each with the comments just above it:
    its head (all before the first def), then (name, text) for each item, a
    def named, anything else not."""
    lines = text.split("\n")
    starts = [i for i, l in enumerate(lines) if l[:1] not in ("", " ", "\t", "#")]
    starts = [i for i in starts if not lines[i].startswith("import ")]
    if not starts:
        return text, []
    bounds = []
    for i in starts:
        j = i
        while j > 0 and lines[j - 1].startswith("#"):
            j -= 1
        bounds.append((j, i))
    out = []
    for k, (j, i) in enumerate(bounds):
        end = bounds[k + 1][0] if k + 1 < len(bounds) else len(lines)
        line = lines[i]
        name = NAME.match(line[4:]).group(0) if line.startswith("def ") else None
        out.append((name, "\n".join(lines[j:end])))
    return "\n".join(lines[:bounds[0][0]]), out


def cut_proof(text, root):
    """The proof file cut to the def root and every def it reaches; items
    other than defs kept."""
    head, its = items(text)
    body = {n: t for n, t in its if n}
    if root not in body:
        sys.exit(f"one_law: no def {root} in the proof file")
    keep, todo = set(), [root]
    while todo:
        n = todo.pop()
        if n in keep:
            continue
        keep.add(n)
        todo += [t for t in NAME.findall(body[n]) if t in body and t not in keep]
    kept = [t for n, t in its if n is None or n in keep]
    return "\n".join([head] + kept), keep, len(body)


def cut_laws(text, law, also):
    """The laws file cut to the one law, and those whose proofs its proof
    uses (also); anything not a law kept."""
    head, its = items(text)
    laws = [t for _, t in its if re.search(r"(?m)^law ", t)]
    if not any(re.search(r"(?m)^law " + re.escape(law) + r":", t) for t in laws):
        sys.exit(f"one_law: no law {law} in the laws file")
    wanted = {law} | also
    mine = [t for t in laws if re.search(r"(?m)^law (\S+):", t).group(1) in wanted]
    rest = [t for _, t in its if not re.search(r"(?m)^law ", t)]
    return "\n".join([head] + rest + mine)


def mutants(path):
    """The mutations of the file at path: (name, laws, what, file, old, new)."""
    with open(path) as f:
        text = f.read()
    out = []
    for block in re.split(r"(?m)^=== ", text)[1:]:
        head, _, rest = block.partition("\n")
        words = head.split()
        what, _, rest = ("\n" + rest).partition("\n--- ")
        file, _, rest = rest.partition("\n")
        old, sep, new = rest.partition("\n+++\n")
        if len(words) < 2 or not file or not sep:
            sys.exit(f"one_law: {path}: a mutation malformed: === {head}")
        out.append((words[0], words[1:], what.strip(), file.strip(), old + "\n",
                    new.rstrip("\n") + "\n"))
    return out


def copy(files, proof, law, dest, mutation=None):
    """The files copied under dest, as laid out under their common
    directory, cut to the law, mutated; the copied proof file's path."""
    root = os.path.commonpath([os.path.dirname(p) or "." for p in files])
    text = files[proof]
    laws = [(imp, alias) for imp, alias in IMPORT.findall(text) if imp.endswith("LAWS.bend")]
    if laws:
        lpath = os.path.normpath(os.path.join(os.path.dirname(proof), laws[0][0]))
        rootdef = (laws[0][1] or "") + "." + law
    else:
        lpath, rootdef = None, law
    out = {}
    cut, keep, total = cut_proof(files[proof], rootdef)
    print(f"   ({len(keep)} of {total} defs kept)")
    prefix = rootdef[:len(rootdef) - len(law)]
    also = {n[len(prefix):] for n in keep if laws and n.startswith(prefix)}
    for p, t in files.items():
        if p == proof:
            t = cut
        elif p == lpath:
            t = cut_laws(t, law, also)
        out[p] = t
    if mutation:
        name, _, _, file, old, new = mutation
        p = os.path.normpath(os.path.join(os.path.dirname(proof), file))
        if p not in out:
            sys.exit(f"one_law: {name}: {file} is not among the proof's files")
        if out[p].count(old) != 1:
            sys.exit(f"one_law: {name}: its code is found in {file} {out[p].count(old)} times, not once")
        out[p] = out[p].replace(old, new)
    for p, t in out.items():
        q = os.path.join(dest, os.path.relpath(p, root))
        os.makedirs(os.path.dirname(q), exist_ok=True)
        with open(q, "w") as f:
            f.write(t)
    return os.path.join(dest, os.path.relpath(proof, root))


def check(path, cap):
    """Bend's check of the copied proof file: whether it passes, and the
    first failure's location or else the start of Bend's output."""
    capped = os.path.join(os.path.dirname(os.path.abspath(__file__)), "capped.sh")
    run = subprocess.run([capped, cap[0], cap[1], os.environ.get("BEND", "bend"),
                          os.path.basename(path)],
                         cwd=os.path.dirname(path), capture_output=True, text=True)
    lines = (run.stdout + run.stderr).splitlines()
    ok = run.returncode == 0 and any(l.startswith("ALL PROOFS CHECK") for l in lines)
    loc = [l.split()[-1] for l in lines if l.startswith("Location:")]
    return ok, loc[0] if loc else " / ".join(lines[:3])


def beside(muts):
    """The proof file beside a mutants file."""
    d, b = os.path.split(os.path.normpath(muts))
    return os.path.join(d, b.removesuffix("MUTANTS.txt") + "PROOF.bend")


def try_law(files, proof, law, muts, cap):
    """The law checked alone, then each mutation naming it: 0 where the
    control passes and every mutation fails."""
    tag = proof.replace(os.sep, "_").removesuffix(".bend")
    status = 0
    print(f"-- {law} alone")
    ok, where = check(copy(files, proof, law, os.path.join(OUT, tag, law, "control")), cap)
    print(f"{law}: {'passes' if ok else 'FAILS at ' + where}")
    status |= 0 if ok else 1
    for m in mutants(muts) if muts else []:
        name, laws, what = m[0], m[1], m[2]
        if law not in laws:
            continue
        print(f"-- {name}: {what}")
        ok, where = check(copy(files, proof, law, os.path.join(OUT, tag, law, name), m), cap)
        print(f"{name}: {'SURVIVES' if ok else 'fails ' + law + ' at ' + where}")
        status |= 1 if ok else 0
    return status


def main(args):
    cap = ("3000", "300")
    muts = None
    if "--cap" in args:
        i = args.index("--cap")
        cap, args = tuple(args[i + 1:i + 3]), args[:i] + args[i + 3:]
    if "--mutants" in args:
        i = args.index("--mutants")
        muts, args = args[i + 1], args[:i] + args[i + 2:]
    if len(cap) != 2 or not (len(args) == 2 or (not args and muts)):
        print(__doc__.split("Run from")[1], file=sys.stderr)
        return 2
    if args:
        proof, laws = os.path.normpath(args[0]), [args[1]]
    else:
        proof = beside(muts)
        laws = list(dict.fromkeys(law for m in mutants(muts) for law in m[1]))
        if not os.path.isfile(proof):
            print(f"one_law: {muts} has no {proof} beside it", file=sys.stderr)
            return 2
    files = closure(proof)
    status = 0
    for law in laws:
        status |= try_law(files, proof, law, muts, cap)
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
