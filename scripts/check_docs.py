"""Docs checks for scripts/check.sh: links, decision records, plan lists.

Run from the repository root: python3 -I scripts/check_docs.py
"""

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(".")
LINK = re.compile(r"\[[^\]]*\]\(([^)\s]+)\)")
FENCE = re.compile(r"^```.*?^```", re.S | re.M)
HEADER = re.compile(r"^`([a-z0-9-]+)` · (maintainer|agent) · rev ([0-9a-f]{7,40})$")

errors = []


def fail(where, message):
    errors.append(f"{where}: {message}")


def git_ok(*args):
    return subprocess.run(["git", *args], capture_output=True).returncode == 0


def markdown_files():
    files = set(ROOT.glob("*.md")) | set(ROOT.glob("docs/**/*.md")) | set(ROOT.glob("samples/**/*.md"))
    return sorted(files)


def links(path):
    text = FENCE.sub("", path.read_text())
    for match in LINK.finditer(text):
        target = match.group(1)
        if re.match(r"[a-z]+:", target) or target.startswith("#"):
            continue
        yield target.split("#")[0]


def check_links():
    for path in markdown_files():
        for target in links(path):
            if not (path.parent / target).exists():
                fail(path, f"dead link {target}")


def check_decisions():
    index = ROOT / "docs/Decisions.md"
    listed = {(index.parent / t).resolve() for t in links(index)}
    for record in sorted(ROOT.glob("docs/decisions/*.md")):
        lines = [line for line in record.read_text().splitlines() if line.strip()]
        if len(lines) < 2 or not lines[0].startswith("# "):
            fail(record, "must start with '# <title>', then its header line")
            continue
        header = HEADER.match(lines[1])
        if not header:
            fail(record, "header must read `<slug>` · maintainer|agent · rev <short hash>")
            continue
        slug, _, rev = header.groups()
        if slug != record.stem:
            fail(record, f"slug `{slug}` differs from its file name")
        if not git_ok("cat-file", "-e", f"{rev}^{{commit}}"):
            fail(record, f"rev {rev} is not a commit")
        elif not git_ok("merge-base", "--is-ancestor", rev, "HEAD"):
            fail(record, f"rev {rev} is not an ancestor of HEAD")
        if record.resolve() not in listed:
            fail(record, "not listed in docs/Decisions.md")


def check_listed(directory):
    readme = ROOT / directory / "README.md"
    listed = {(readme.parent / t).resolve() for t in links(readme)}
    for doc in sorted((ROOT / directory).glob("*.md")):
        if doc.name != "README.md" and doc.resolve() not in listed:
            fail(doc, f"not listed in {readme}")


check_links()
check_decisions()
check_listed("docs/plans")
check_listed("docs/reviews")

for error in errors:
    print(error)
print(f"docs: {len(errors)} problem(s)" if errors else "docs: ok")
sys.exit(1 if errors else 0)
