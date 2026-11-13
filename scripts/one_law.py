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
    >>> witness LAW
    a def: LAW's statement at one instance, proved by {==}

PATH relative to the proof file's directory, the code found there exactly
once; lines before the first `===` are comments. A mutation is caught
where Bend refutes the law's proof on the mutated copy (SOME PROOFS
FAIL). A run that ends with no verdict, Bend's checker overflowing its
stack (as it does building the report of a mismatch over symbolic
words) or the run's cap reached, is a crash, and catches nothing: unless
the mutation carries a witness for the law, a closed instance of its
statement, which must check on a copy unmutated, so that the instance
meets the law's premises, and be refuted on the mutated one. The witness
runs in a copy of its own, the proof file's imports and the witness
alone (its laws files left out), as WITNESS.bend beside the proof file:
Bend asks a file named PROOF.bend to import its laws. A mutants file sits
beside its proof file, as a laws file does: MUTANTS.txt beside PROOF.bend,
X_MUTANTS.txt beside X_PROOF.bend. Given only the mutants file, every law
it names is tried, as the gate does (scripts/check.sh, through
scripts/kept.py). Exits 0 where each control passes and every mutation
fails (refuted, or crashing with its witness refuted), 1 otherwise, 2 on
bad usage.

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

# no update check: Bend's notice of a newer release would print beside
# what this reads, as scripts/check.sh has it
os.environ["BEND_NO_TELEMETRY"] = "1"

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
    """The mutations of the file at path: (name, laws, what, file, old, new,
    witnesses by law)."""
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
        new, *wits = re.split(r"(?m)^>>> witness ", new)
        witness = {}
        for w in wits:
            law, _, body = w.partition("\n")
            if law.strip() not in words[1:]:
                sys.exit(f"one_law: {path}: {words[0]}'s witness names {law.strip()}, which it does not")
            witness[law.strip()] = body.rstrip("\n") + "\n"
        out.append((words[0], words[1:], what.strip(), file.strip(), old + "\n",
                    new.rstrip("\n") + "\n", witness))
    return out


def witness_text(text, body):
    """A proof file of the witness alone: the proof file's imports but its
    laws files, and the witness."""
    imps = [l for l in text.splitlines()
            if l.startswith("import ") and not l.split()[1].endswith("LAWS.bend")]
    return "\n".join(imps) + "\n\n" + body


def copy(files, proof, law, dest, mutation=None, witness=None):
    """The files copied under dest, as laid out under their common
    directory, cut to the law (or, given a witness, the proof file the
    witness alone), mutated; the copied proof file's path."""
    root = os.path.commonpath([os.path.dirname(p) or "." for p in files])
    text = files[proof]
    if witness is not None:
        out = dict(files)
        wpath = os.path.join(os.path.dirname(proof), "WITNESS.bend")
        out[wpath] = witness_text(text, witness)
        write(files, proof, root, out, dest, mutation)
        return os.path.join(dest, os.path.relpath(wpath, root))
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
    return write(files, proof, root, out, dest, mutation)


def write(files, proof, root, out, dest, mutation):
    """The copy written under dest, mutated; the copied proof file's path."""
    if mutation:
        name, _, _, file, old, new = mutation[:6]
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
    """Bend's check of the copied proof file: pass; refuted, with the first
    failure's location; or crash, with why: a run that ends with no verdict
    (docstring above)."""
    capped = os.path.join(os.path.dirname(os.path.abspath(__file__)), "capped.sh")
    run = subprocess.run([capped, cap[0], cap[1], os.environ.get("BEND", "bend"),
                          os.path.basename(path)],
                         cwd=os.path.dirname(path), capture_output=True, text=True)
    lines = (run.stdout + run.stderr).splitlines()
    if run.returncode == 0 and any(l.startswith("ALL PROOFS CHECK") for l in lines):
        return "pass", ""
    if any(l.startswith("SOME PROOFS FAIL") for l in lines):
        loc = [l.split()[-1] for l in lines if l.startswith("Location:")]
        return "refuted", loc[0] if loc else " / ".join(lines[:3])
    why = [l.strip() for l in lines if "RangeError" in l or l.startswith("capped.sh:")]
    return "crash", why[0] if why else " / ".join(lines[:3])


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
    kind, where = check(copy(files, proof, law, os.path.join(OUT, tag, law, "control")), cap)
    print(f"{law}: " + {"pass": "passes", "refuted": "FAILS at " + where,
                        "crash": "CRASHES the checker: " + where}[kind])
    status |= 0 if kind == "pass" else 1
    for m in mutants(muts) if muts else []:
        name, laws, what, witness = m[0], m[1], m[2], m[6]
        if law not in laws:
            continue
        print(f"-- {name}: {what}")
        dest = os.path.join(OUT, tag, law, name)
        kind, where = check(copy(files, proof, law, dest, m), cap)
        if kind == "pass":
            print(f"{name}: SURVIVES")
            status |= 1
        elif kind == "refuted":
            print(f"{name}: fails {law} at {where}")
        elif law not in witness:
            print(f"{name}: CRASHES the checker ({where}), and has no witness for {law}: not caught")
            status |= 1
        else:
            kc, wc = check(copy(files, proof, law, dest + "_witness_control", witness=witness[law]), cap)
            km, wm = check(copy(files, proof, law, dest + "_witness", m, witness=witness[law]), cap)
            if kc == "pass" and km == "refuted":
                print(f"{name}: crashes the checker; its witness refutes {law} at {wm}")
            else:
                print(f"{name}: CRASHES the checker, and its witness for {law} "
                      + ("does not check unmutated: " + wc if kc != "pass" else "is not refuted: " + km))
                status |= 1
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
