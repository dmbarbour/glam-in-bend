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
copy of its own, after the copy unmutated (the control; left out with
--gate, the gate's verdict having checked the whole file): a law that
survives a mutation of what it is about claims less than meant
(docs/Proving.md). FILE holds mutations as

    === NAME LAW...
    a line or two on what it breaks
    --- PATH
    the code, verbatim, to replace
    +++
    its replacement, verbatim
    >>> witness LAW
    NAME = TERM
    ...

PATH relative to the proof file's directory, the code found there exactly
once; lines before the first `===` are comments. A mutation without a
witness for the law is caught where Bend refutes the law's proof on the
mutated copy (SOME PROOFS FAIL). A run that ends with no verdict, Bend's checker overflowing its
stack (as it does building the report of a mismatch over symbolic
words) or the run's cap reached, is a crash, and catches nothing.

A witness is the law at one instance: a term for each of the law's `for`
binders it names (a line indented further continues the term above), a
binder left out proved by {==}, as a premise equation at a closed
instance is. From the law's own text in the laws file, the instance
substituted, the witness is written as a def per binder (its term at
the binder's type: the values typed, the premises proved) and last the
conclusion, `witness`, proved by {==}; so that its premises are the
law's by construction. It runs in a copy of its own, the proof file's
imports and the witness alone (its laws and proof files left out), as
WITNESS.bend beside the proof file: Bend asks a file named PROOF.bend
to import its laws. Every witness of the file checks unmutated in one
run, the names told apart (_w<law>_<case>); a failure there is laid to
the witness it names, the rest unknown, Bend reporting the first alone.
A mutation that carries a witness for the law is caught by it alone,
its proof mutated not run: the witness must check unmutated, and on
the mutated one be refuted at its conclusion, Bend reporting the first
def that fails in the file's order, so that the premises still hold
there, the mutated code the law's counterexample; a refuted proof whose
witness holds is a mutation the law may survive (docs/Proving.md, What
to claim). A mutants file sits beside its proof file, as a laws file
does: MUTANTS.txt beside PROOF.bend, X_MUTANTS.txt beside X_PROOF.bend.
Given only the mutants file, every law it names is tried, as the gate
does (scripts/check.sh, through scripts/kept.py). The runs are made in
parallel, as many at once as fit the machine's available memory at the
cap, at most half its processors, and reported in order. A run whose
outcome is the one its role wants (a control passing, a mutated proof
refuted, a mutated witness refuted at its conclusion) is kept while the
files it checks are unchanged, with Bend, this tool and the cap
(results/one_law_kept/): a witness's run checks the code's modules and
not the proof file, so that an edit to the proofs reruns none of them;
nothing else is kept. Exits 0 where each control passes and every
mutation is caught, 1 otherwise, 2 on bad usage.

Run from the root of the project the proof file is in (the repository, or
Blend's directory), its copies written under that project's results/:
  python3 -I scripts/one_law.py PROOF LAW              the law checked alone
  python3 -I scripts/one_law.py PROOF LAW --mutants FILE
                                                       and each of FILE's
                                                       mutations naming it
  python3 -I scripts/one_law.py --mutants FILE         every law FILE
                                                       names, against the
                                                       proof file beside it
  --cap MB SECONDS   each run's cap (scripts/capped.sh), 1500 MB 300 s by
                     default, the largest run 380 MB (2026-11-16), or the
                     mutants file's own: a line `cap: MB SECONDS` among
                     its comments (glam/MATERIALIZE_MUTANTS.txt's laws
                     importing the loop's proofs, about 2 GB, 2026-11-27)
  --jobs N           at most N runs at once
  --gate             no law checked alone, as the gate runs it
"""

import hashlib
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

# no update check: Bend's notice of a newer release would print beside
# what this reads, as scripts/check.sh has it
os.environ["BEND_NO_TELEMETRY"] = "1"

IMPORT = re.compile(r"^import\s+(\S+)(?:\s+as\s+(\S+))?", re.M)
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_.]*")
OUT = os.path.join("results", "one_law")
KEPT = os.path.join("results", "one_law_kept")
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import kept  # noqa: E402
TOOLS = b""


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
            witness[law.strip()] = bindings(path, words[0], body)
        out.append((words[0], words[1:], what.strip(), file.strip(), old + "\n",
                    new.rstrip("\n") + "\n", witness))
    return out


def bindings(path, name, body):
    """A witness's terms by binder: `NAME = TERM` lines, a line indented
    further continuing the term above; comments and blank lines left."""
    out, last = {}, None
    for line in body.rstrip("\n").split("\n"):
        if line.startswith("#"):
            continue
        m = re.match(r"(\w+) = (.*)$", line)
        if m:
            last = m.group(1)
            out[last] = m.group(2).strip()
        elif line.strip() and line[:1] in (" ", "\t") and last:
            out[last] += " " + line.strip()
        elif line.strip():
            sys.exit(f"one_law: {path}: {name}'s witness: not `NAME = TERM`: {line.strip()}")
    return out


def law_parts(text, law):
    """A law's binders, (name, type) in order, and its conclusion."""
    m = re.search(r"(?m)^law " + re.escape(law) + r":\n((?:[ \t]+.*\n?)*)", text)
    if not m:
        sys.exit(f"one_law: no law {law} in the laws file")
    binders, rest = [], []
    for line in m.group(1).split("\n"):
        b = re.match(r"\s+for [+-]?(\w+): (.*)$", line)
        if b:
            binders.append((b.group(1), b.group(2).strip()))
        elif line.strip():
            rest.append(line.strip())
    return binders, " ".join(rest)


def subst(text, terms):
    """The text, each binder named in terms replaced by its term: names
    alone, not a qualified name's part nor another name's."""
    if not terms:
        return text
    pat = re.compile(r"(?<![\w.])(" + "|".join(map(re.escape, terms)) + r")(?![\w.])")
    return pat.sub(lambda m: terms[m.group(1)], text)


def witness_body(laws, law, terms, tag=""):
    """The witness's defs: one per binder, its term (or {==}) at its type,
    and the conclusion last; each name ending in tag, so that the
    witnesses of one law check unmutated in one file."""
    binders, concl = law_parts(laws, law)
    names = {n for n, _ in binders}
    if set(terms) - names:
        sys.exit(f"one_law: the witness for {law} names no binder of it: {', '.join(sorted(set(terms) - names))}")
    used = " ".join([concl] + [t for _, t in binders])
    for n, _ in binders:
        if n not in terms and re.search(r"(?<![\w.])" + re.escape(n) + r"(?![\w.])", used):
            sys.exit(f"one_law: the witness for {law} binds no term for {n}, which its statement uses")
    defs = [f"def wit_{n}{tag}() -> {subst(t, terms)}:\n  {terms.get(n, '{==}')}\n" for n, t in binders]
    return "\n".join(defs + [f"def witness{tag}() -> {subst(concl, terms)}:\n  {{==}}\n"])


def witness_text(text, body):
    """A proof file of the witness alone: the proof file's imports but its
    laws and proof files, and the witness. A witness evaluates the law at
    its instance, which needs the code and the models, never a proof: an
    imported proof file a mutation breaks (glam/SERVE_PROOF.bend importing
    the splice's, whose code is the one mutated) would refute the witness
    before its instance."""
    imps = [l for l in text.splitlines()
            if l.startswith("import ") and not l.split()[1].endswith(("LAWS.bend", "PROOF.bend"))]
    return "\n".join(imps) + "\n\n" + body


def laws_file(files, proof):
    """The laws file the proof file imports, its text, or None."""
    for imp, _ in IMPORT.findall(files[proof]):
        if imp.endswith("LAWS.bend"):
            return files.get(os.path.normpath(os.path.join(os.path.dirname(proof), imp)))
    return None


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
    copy.kept = f"   ({len(keep)} of {total} defs kept)"
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


def run_key(path, dest, cap):
    """A run's key: the file it checks and every local file that imports,
    as the copy has them (laid out under dest, so that two runs of one
    content share it), the imports of no local file by name, Bend's and
    this tool's versions, and the cap."""
    files, others = kept.closure(path)
    h = hashlib.sha256(TOOLS)
    h.update(f"{cap[0]} {cap[1]}\0{os.path.relpath(path, dest)}\0".encode())
    for f in sorted(files):
        h.update(os.path.relpath(f, dest).encode() + b"\0" + hashlib.sha256(files[f]).digest())
    for o in sorted(others):
        h.update(o.encode() + b"\0")
    return h.hexdigest()


def check(path, cap, dest=None, want=None):
    """Bend's check of the copied proof file: pass; refuted, with the first
    failure's location; or crash, with why: a run that ends with no verdict
    (docstring above). A run whose outcome is the one its role wants (want:
    "pass", "refuted", or "witness", refuted at its conclusion) keeps it
    while the files it checks are unchanged (results/one_law_kept/); no
    other outcome is kept."""
    mark = os.path.join(KEPT, run_key(path, dest, cap)) if want else None
    if mark and os.path.exists(mark):
        with open(mark) as f:
            kind, _, where = f.read().partition(" ")
        check.kept += 1
        return kind, where
    capped = os.path.join(os.path.dirname(os.path.abspath(__file__)), "capped.sh")
    run = subprocess.run([capped, cap[0], cap[1], os.environ.get("BEND", "bend"),
                          os.path.basename(path)],
                         cwd=os.path.dirname(path), capture_output=True, text=True)
    lines = (run.stdout + run.stderr).splitlines()
    if run.returncode == 0 and any(l.startswith("ALL PROOFS CHECK") for l in lines):
        res = "pass", ""
    elif any(l.startswith("SOME PROOFS FAIL") for l in lines):
        loc = [l.split()[-1] for l in lines if l.startswith("Location:")]
        res = "refuted", loc[0] if loc else " / ".join(lines[:3])
    else:
        why = [l.strip() for l in lines if "RangeError" in l or l.startswith("capped.sh:")]
        res = "crash", why[0] if why else " / ".join(lines[:3])
    good = {"pass": res[0] == "pass", "refuted": res[0] == "refuted",
            "witness": res == ("refuted", "witness")}.get(want, False)
    if good:
        os.makedirs(KEPT, exist_ok=True)
        with open(mark, "w") as f:
            f.write(f"{res[0]} {res[1]}")
    return res
check.kept = 0


def beside(muts):
    """The proof file beside a mutants file."""
    d, b = os.path.split(os.path.normpath(muts))
    return os.path.join(d, b.removesuffix("MUTANTS.txt") + "PROOF.bend")


def plan_law(files, proof, law, muts, li, alone=True):
    """The runs a law asks, as (path, dest, want): the law checked alone
    (unless the gate's verdict has checked the whole file), then each
    mutation naming it: its witness mutated where it has one, which decides
    alone, else its proof mutated. Its witnesses' defs unmutated, named
    apart (_w<law>_<case>), go to the file's one joint run. Then reports the
    results, given the joint run's, (lines, status)."""
    tag = proof.replace(os.sep, "_").removesuffix(".bend")
    laws = laws_file(files, proof)
    runs, heads = [], [f"-- {law}" + (" alone" if alone else "")]
    if alone:
        d = os.path.join(OUT, tag, law, "control")
        runs.append((copy(files, proof, law, d), d, "pass"))
        heads.append(copy.kept)
    cases, controls = [], []
    for m in mutants(muts) if muts else []:
        name, ls, what, witness = m[0], m[1], m[2], m[6]
        if law not in ls:
            continue
        dest = os.path.join(OUT, tag, law, name)
        if law in witness:
            if laws is None:
                sys.exit(f"one_law: {name}'s witness for {law}: the proof file imports no laws file")
            controls.append(witness_body(laws, law, witness[law], f"_w{li}_{len(cases)}"))
            d = dest + "_witness"
            runs.append((copy(files, proof, law, d, m, witness=witness_body(laws, law, witness[law])), d, "witness"))
            cases.append((name, what, "", len(runs) - 1, True))
        else:
            runs.append((copy(files, proof, law, dest, m), dest, "refuted"))
            cases.append((name, what, copy.kept, len(runs) - 1, False))

    def report(res, joint):
        lines, status = list(heads), 0
        if alone:
            kind, where = res[0]
            lines.append(f"{law}: " + {"pass": "passes", "refuted": "FAILS at " + where,
                                       "crash": "CRASHES the checker: " + where}[kind])
            status = 0 if kind == "pass" else 1
        for k, (name, what, kept, at, wit) in enumerate(cases):
            got = [res[at]]
            if wit:
                # the witnesses' joint check unmutated: this one's failure,
                # or another's, Bend reporting the first alone
                kc, wc = joint
                mt = re.search(r"_w(\d+)_(\d+)$", wc) if kc == "refuted" else None
                mine = kc == "pass" or (mt is not None and (int(mt.group(1)), int(mt.group(2))) != (li, k))
                got = [("pass", "") if mine else (kc, wc), res[at]]
            line, bad = verdict(name, law, got)
            lines += [f"-- {name}: {what}", kept, line]
            status |= bad
        return lines, status
    return runs, controls, report


def verdict(name, law, res):
    """A mutation's line and whether it is not caught, from its runs: its
    proof mutated, or its witness unmutated (in the joint run) and
    mutated."""
    if len(res) == 1:
        kind, where = res[0]
        if kind == "pass":
            return f"{name}: SURVIVES", 1
        if kind == "refuted":
            return f"{name}: fails {law} at {where}", 0
        return f"{name}: CRASHES the checker ({where}), and has no witness for {law}: not caught", 1
    (kc, wc), (km, wm) = res
    if kc != "pass":
        return f"{name}: its witness for {law} does not check unmutated ({kc} at {wc}): NOT CAUGHT", 1
    if km == "refuted" and wm == "witness":
        return f"{name}: its witness refutes {law}", 0
    if km == "refuted":
        return f"{name}: its witness's premise {wm.removeprefix('wit_')} fails on the mutated code, not the law's instance there: NOT CAUGHT", 1
    if km == "pass":
        return f"{name}: its witness holds on the mutated code: NOT CAUGHT", 1
    return f"{name}: its witness crashes the checker on the mutated code ({wm}): NOT CAUGHT", 1


def jobs_for(cap, asked):
    """Runs at once: as asked, else as many as the available memory holds
    at the cap, at most half the processors, at least one. The memory
    free is the container's (scripts/mem_avail.py): /proc/meminfo alone
    is the host's."""
    if asked:
        return max(1, asked)
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "mem_avail", os.path.join(os.path.dirname(os.path.abspath(__file__)), "mem_avail.py"))
    mem = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mem)
    return max(1, min((os.cpu_count() or 2) // 2, mem.avail_mb() // int(cap[0])))


def file_cap(path):
    """A mutants file's own cap: a line `cap: MB SECONDS` among the
    comments before its first mutation, for a file whose laws' proofs
    import more than the default holds."""
    with open(path) as f:
        head = re.split(r"(?m)^=== ", f.read())[0]
    m = re.search(r"(?m)^cap: (\d+) (\d+)\s*$", head)
    return (m.group(1), m.group(2)) if m else None


def main(args):
    cap = ("1500", "300")
    muts, jobs = None, 0
    alone = "--gate" not in args
    args = [a for a in args if a != "--gate"]
    given = "--cap" in args
    if given:
        i = args.index("--cap")
        cap, args = tuple(args[i + 1:i + 3]), args[:i] + args[i + 3:]
    if "--jobs" in args:
        i = args.index("--jobs")
        jobs, args = int(args[i + 1]), args[:i] + args[i + 2:]
    if "--mutants" in args:
        i = args.index("--mutants")
        muts, args = args[i + 1], args[:i] + args[i + 2:]
        if not given and os.path.isfile(muts):
            cap = file_cap(muts) or cap
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
    global TOOLS
    TOOLS = kept.tool_key(kept.bend_exe())
    for t in (os.path.abspath(__file__), os.path.join(HERE, "capped.sh"), os.path.join(HERE, "kept.py")):
        with open(t, "rb") as f:
            TOOLS += hashlib.sha256(f.read()).digest()
    files = closure(proof)
    plans = [plan_law(files, proof, law, muts, li, alone) for li, law in enumerate(laws)]
    runs = [r for rs, _, _ in plans for r in rs]
    controls = [c for _, cs, _ in plans for c in cs]
    if controls:
        tag = proof.replace(os.sep, "_").removesuffix(".bend")
        d = os.path.join(OUT, tag, "witness_control")
        runs.append((copy(files, proof, None, d, witness="\n".join(controls)), d, "pass"))
    with ThreadPoolExecutor(jobs_for(cap, jobs)) as pool:
        results = list(pool.map(lambda r: check(r[0], cap, r[1], r[2]), runs))
    joint = results[-1] if controls else ("pass", "")
    status, at = 0, 0
    for rs, _, report in plans:
        lines, bad = report(results[at:at + len(rs)], joint)
        at += len(rs)
        print("\n".join(l for l in lines if l), flush=True)
        status |= bad
    print(f"one_law: {len(runs)} runs, {check.kept} kept", flush=True)
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
