"""Docs checks for scripts/check.sh: links, decision records, plan lists.

Run from the repository root:
  python3 -I scripts/check_docs.py                    check the docs
  python3 -I scripts/check_docs.py --commit-msg FILE  check FILE's Plan-Step
                                                      trailers (commit-msg hook)
"""

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(".")
LINK = re.compile(r"\[[^\]]*\]\(([^)\s]+)\)")
FENCE = re.compile(r"^```.*?^```", re.S | re.M)
HEADER = re.compile(r"^`([a-z0-9-]+)` · (maintainer|agent) · rev ([0-9a-f]{7,40})$")
INDEX_LINE = re.compile(r"^- \[`([a-z0-9-]+)`\]\(decisions/\1\.md\)")
RECORD_BODY = re.compile(r"^\*\*(Context|Decision|Consequences)\.\*\*")
STEP = re.compile(r"^\s*(?:\d+\.|[-*])\s+`([a-z][a-z0-9-]*(?:\.[a-z][a-z0-9-]*)*)`\s+—(.*)$", re.M)
# a sub-step's disposition, the first words after its name (docs/plans/README.md)
DISPOSITION = re.compile(r"^\s*(tentative|active|contingent on `[^`]+`(?:(?:,| and) `[^`]+`)*"
                         r"|built \d{4}-\d\d-\d\d|dropped \d{4}-\d\d-\d\d)(?![\w-])")
PLAN_STEP = re.compile(r"^Plan-Step:\s*(\S+)\s*$", re.M)

errors = []


def fail(where, message):
    errors.append(f"{where}: {message}")


def git(*args):
    return subprocess.run(["git", *args], capture_output=True, text=True)


def git_ok(*args):
    return git(*args).returncode == 0


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


def check_index_stays_an_index():
    """Outside "Records", the index holds paragraphs and one line per record."""
    index = ROOT / "docs/Decisions.md"
    section = None
    for number, line in enumerate(index.read_text().splitlines(), 1):
        if line.startswith("## "):
            section = line[3:].strip()
        if section in (None, "Records"):
            continue
        if RECORD_BODY.match(line):
            fail(f"{index}:{number}", "a record's body belongs in docs/decisions/")
        elif line.startswith("- ") and not INDEX_LINE.match(line):
            fail(f"{index}:{number}", "index lines read - [`slug`](decisions/slug.md): summary")


def check_listed(directory):
    readme = ROOT / directory / "README.md"
    listed = {(readme.parent / t).resolve() for t in links(readme)}
    for doc in sorted((ROOT / directory).glob("*.md")):
        if doc.name != "README.md" and doc.resolve() not in listed:
            fail(doc, f"not listed in {readme}")


def history_docs(tree):
    """(path, text) of each plan and review, in the working tree or at HEAD."""
    if tree == "work":
        for directory in ("docs/plans", "docs/reviews"):
            for doc in sorted((ROOT / directory).glob("*.md")):
                if doc.name != "README.md":
                    yield str(doc), doc.read_text()
        return
    listing = git("ls-tree", "-r", "--name-only", tree, "--", "docs/plans", "docs/reviews")
    for path in listing.stdout.split():
        if path.endswith(".md") and not path.endswith("README.md"):
            yield path, git("show", f"{tree}:{path}").stdout


def steps(tree):
    found = {}
    for path, text in history_docs(tree):
        for name, _ in STEP.findall(text):
            found.setdefault(name, []).append(path)
    return found


def check_step_names():
    known = steps("work")
    for name, paths in sorted(known.items()):
        if len(paths) > 1:
            fail(", ".join(paths), f"step `{name}` is named more than once")
    # a sub-step sits in its parent's plan, with a disposition naming real steps
    for path, text in history_docs("work"):
        mine = {name for name, _ in STEP.findall(text)}
        for name, rest in STEP.findall(text):
            if "." not in name:
                continue
            parent = name.rsplit(".", 1)[0]
            if parent not in mine:
                fail(path, f"sub-step `{name}` has no parent `{parent}` in its plan")
            d = DISPOSITION.match(rest)
            if not d:
                fail(path, f"sub-step `{name}` gives no disposition (tentative, contingent on `step`, active, built <date>, dropped <date>)")
            elif d.group(1).startswith("contingent on"):
                for dep in re.findall(r"`([^`]+)`", d.group(1)):
                    if dep not in known:
                        fail(path, f"sub-step `{name}` is contingent on `{dep}`, which names no step")


def check_commit_msg(message_file):
    """Every Plan-Step trailer names a step of a plan or review, now or at HEAD."""
    message = pathlib.Path(message_file).read_text()
    message = "\n".join(line for line in message.splitlines() if not line.startswith("#"))
    known = set(steps("work"))
    if git_ok("rev-parse", "--verify", "-q", "HEAD"):
        known |= set(steps("HEAD"))
    for name in PLAN_STEP.findall(message):
        if name not in known:
            fail(message_file, f"Plan-Step `{name}` names no step in docs/plans or docs/reviews")


if len(sys.argv) == 3 and sys.argv[1] == "--commit-msg":
    check_commit_msg(sys.argv[2])
    label = "plan steps"
else:
    check_links()
    check_decisions()
    check_index_stays_an_index()
    check_listed("docs/plans")
    check_listed("docs/reviews")
    check_step_names()
    label = "docs"

for error in errors:
    print(error)
print(f"{label}: {len(errors)} problem(s)" if errors else f"{label}: ok")
sys.exit(1 if errors else 0)
