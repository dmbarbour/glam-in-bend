#!/usr/bin/env python3
"""List the proof files' definitions whose types match (cursor-laws.proofs.dups).

A development aid, run by hand: a lemma written twice under two names is
found by its statement, not its name. Each top-level `def` of the files
named (default: every *PROOF.bend outside bench/ and blend/, and
glam/proofgen/align/ALIGN.bend) is read as its parameters' types and its
result's, with its parameters renamed by position, `+` and `-` dropped,
and each module alias replaced by the file it imports, so that `MB.x` in
one file and `MBool.x` in another compare equal. Only lemmas are read,
their results an equation or Empty; definitions without a result type
(a law's proof, `def Laws.x(a, b)`) are left out, their statements
their laws'.

    python3 -I scripts/proof_dups.py [--detail] [FILE...]

prints each group of two or more definitions whose types match, across
files or within one, the largest groups first, then a count. The laws of
the hub packages installed (~/.bend/lib) and of the repo's laws files
join the groups, and the hub's typed defs (marked `*`), so that a lemma a
law or the hub already proves shows beside it; a group of laws and hub
defs alone is left out. --detail gives each def's body length, its
parameters' erasure marks in order (+, - or . for a linear one) and
whether its body is one call, a wrapper of another lemma.
"""
import os
import re
import subprocess
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEF = re.compile(r"^def ([A-Za-z_][\w.]*)\(")
IMPORT = re.compile(r"^import (\S+) as (\w+)\s*$")
IDENT = re.compile(r"(?<![\w.])([A-Za-z_]\w*)(?![\w])")


def default_files():
    out = subprocess.run(["git", "ls-files", "*PROOF.bend"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout.split()
    files = [f for f in out if not f.startswith(("bench/", "blend/"))]
    align = "glam/proofgen/align/ALIGN.bend"
    if os.path.exists(os.path.join(ROOT, align)):
        files.append(align)
    return files


def aliases(path, text):
    """alias -> the imported file, resolved from the importing file's directory."""
    base = os.path.dirname(path)
    out = {}
    for line in text.splitlines():
        m = IMPORT.match(line)
        if not m:
            continue
        target, alias = m.groups()
        if target.startswith("0x"):
            out[alias] = target
        else:
            out[alias] = os.path.normpath(os.path.join(base, target))
    return out


def header(lines, i):
    """the def's header from line i: up to the first line that ends in a
    colon with every bracket closed, that colon left out."""
    text = ""
    depth = 0
    for line in lines[i:i + 40]:
        for ch in line:
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
        text += line + "\n"
        if depth == 0 and line.rstrip().endswith(":"):
            return text.rstrip()[:-1]
    return None


def split_params(s):
    """a parameter list's entries, at depth zero."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{<":
            depth += 1
        elif ch in ")]}>" and not (ch == ">" and cur.endswith("-")):
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return out


def signature(head, amap):
    """the normalized statement of a def's header, or None without a result type."""
    m = re.match(r"def [\w.]+\((.*)\)\s*->\s*(.*)$", head.replace("\n", " "), re.S)
    if not m:
        return None
    params, result = m.groups()
    if not result.strip().startswith(("{", "Empty")):
        return None  # a function, not a lemma: its type says little
    names, types = [], []
    for p in split_params(params):
        p = p.strip()
        pm = re.match(r"^[+\-]?\s*(~?\w+)\s*:\s*(.*)$", p, re.S)
        if not pm:
            return None
        names.append(pm.group(1).lstrip("~"))
        types.append(pm.group(2))
    return normalized(names, types, result, amap)


def normalized(names, types, result, amap):
    """types and a result with the names renamed by position and the
    module aliases replaced by their files."""
    rename = {n: f"_{k}" for k, n in enumerate(names)}

    def norm(t):
        t = re.sub(r"\s+", " ", t).strip()
        t = re.sub(r"(?<![\w.])(\w+)\.(?=[A-Za-z_])",
                   lambda mm: (amap[mm.group(1)] + "::") if mm.group(1) in amap else mm.group(0), t)
        t = IDENT.sub(lambda mm: rename.get(mm.group(1), mm.group(1)), t)
        t = re.sub(r"@\s*\+?\s*(\w+)", r"@\1", t)
        return t

    return " , ".join(norm(t) for t in types) + " -> " + norm(result)


DETAIL = {}
LAW_MARKS = {}


def detail(lines, i, head):
    """a def's body length in lines, its parameters' erasure marks, and
    whether its body is one call (a wrapper of another lemma)."""
    hl = head.count("\n") + 1
    body = []
    for line in lines[i + hl:]:
        if line.strip() and not line.startswith((" ", "\t")):
            break
        if line.strip():
            body.append(line.strip())
    m = re.match(r"def [\w.]+\((.*)\)\s*->", head.replace("\n", " "), re.S)
    marks = []
    if m:
        for p in split_params(m.group(1)):
            p = p.strip()
            marks.append(p[0] if p[:1] in "+-" else ".")
    wrapper = len(body) == 1 and re.match(r"^[\w.]+\(", body[0]) is not None
    return len(body), "".join(marks), wrapper


LAW = re.compile(r"^law ([A-Za-z_][\w.]*):\s*$")
FOR = re.compile(r"^\s+for\s+([+\-]?)\s*(~?\w+)\s*:\s*(.*)$")


def laws(lines, amap):
    """each law block's name, line and normalized statement: its `for`s
    the parameters, the conclusion after them the result."""
    for i, line in enumerate(lines):
        m = LAW.match(line)
        if not m:
            continue
        names, types, concl, marks = [], [], [], ""
        for line2 in lines[i + 1:i + 80]:
            fm = FOR.match(line2)
            if fm and not concl:
                marks += fm.group(1) or "."
                names.append(fm.group(2).lstrip("~"))
                types.append(fm.group(3))
            elif line2.strip() and line2.startswith((" ", "\t")):
                concl.append(line2.strip())
            else:
                break
        if concl:
            LAW_MARKS[(m.group(1), i + 1)] = marks
            yield m.group(1), i + 1, normalized(names, types, " ".join(concl), amap)


def hub_files():
    """the hub packages the proofs import, as (key, path): the key the
    package's hash and file, as glam's imports name them."""
    lib = os.path.expanduser("~/.bend/lib")
    out = []
    if not os.path.isdir(lib):
        return out
    for pkg in sorted(os.listdir(lib)):
        d = os.path.join(lib, pkg)
        if not pkg.startswith("0x") or not os.path.isdir(d):
            continue
        for name in sorted(os.listdir(d)):
            if name.endswith(".bend"):
                out.append((f"{pkg}/{name}", os.path.join(d, name)))
    return out


def scan(files, extra=()):
    """files: the repo's proof files, their defs read; extra: (key, path)
    pairs whose laws and typed defs are read too, marked as such."""
    groups = defaultdict(list)
    sources = [(f, os.path.join(ROOT, f), "") for f in files] + [(k, p, "*") for k, p in extra]
    for key, path, mark in sources:
        text = open(path).read()
        amap = aliases(key, text)
        lines = text.splitlines()
        for i, line in enumerate(lines):
            m = DEF.match(line)
            if not m or m.group(1).startswith("Laws."):
                continue
            head = header(lines, i)
            if head is None:
                continue
            sig = signature(head, amap)
            if sig is None:
                continue
            groups[sig].append((key, i + 1, mark + m.group(1)))
            DETAIL[(key, i + 1)] = detail(lines, i, head)
        if mark:
            for name, line, sig in laws(lines, amap):
                groups[sig].append((key, line, "law " + name))
    return groups


def repo_laws():
    out = subprocess.run(["git", "ls-files", "*LAWS.bend"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout.split()
    return [(f, os.path.join(ROOT, f)) for f in out if not f.startswith(("bench/", "blend/"))]


def main(argv):
    files = [a for a in argv[1:] if not a.startswith("--")] or default_files()
    groups = scan(files, hub_files() + repo_laws())
    # a group is a duplicate when it holds two entries, one a repo proof's def
    dups = [(sig, ds) for sig, ds in groups.items()
            if len(ds) > 1 and any(not n.startswith(("*", "law ")) for _, _, n in ds)]
    dups.sort(key=lambda g: (-len({f for f, _, _ in g[1]}), -len(g[1]), g[1][0]))
    detailed = "--detail" in argv
    for sig, ds in dups:
        nfiles = len({f for f, _, _ in ds})
        print(f"{len(ds)} defs in {nfiles} file(s): {sig[:200]}")
        for f, line, name in ds:
            extra = ""
            if detailed and (f, line) in DETAIL:
                n, marks, wrap = DETAIL[(f, line)]
                extra = f"  [{n} lines, marks {marks}{', a wrapper' if wrap else ''}]"
            elif detailed and name.startswith("law ") and (name[4:], line) in LAW_MARKS:
                extra = f"  [marks {LAW_MARKS[(name[4:], line)]}]"
            print(f"    {f}:{line} {name}{extra}")
    across = sum(1 for _, ds in dups if len({f for f, _, _ in ds}) > 1)
    print(f"proof_dups: {len(dups)} groups, {across} across files, over {len(files)} files")


if __name__ == "__main__":
    main(sys.argv)
