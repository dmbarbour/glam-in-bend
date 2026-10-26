"""Law checks: every law changed on main is named in its commit.

A law is a `law <name>:` block in a file named LAWS.bend: the `law` line at
column 0 and the indented lines after it. Comments and spacing aside, adding,
changing or removing one is a law change. Each commit on main's first-parent
history that changes laws must name every one of them in `Law: <name>`
trailers. Side branches are free: land law work on main with a merge
(`--no-ff`) or squash commit that names the laws.

Comments in LAWS.bend may cite decision records as `# Record: <slug>`; each
cited record must exist.

Run from the repository root:
  python3 -I scripts/check_laws.py                    check main's history and
                                                      the record citations
  python3 -I scripts/check_laws.py --commit-msg FILE  on main, check the staged
                                                      laws against FILE's
                                                      trailers (commit-msg hook)
"""

import pathlib
import re
import subprocess
import sys

LAW = re.compile(r"^law\s+([A-Za-z0-9_.-]+)\s*:")
TRAILER = re.compile(r"^Law:\s*(\S+)\s*$", re.M)
CITATION = re.compile(r"#\s*Record:\s*(.+)$")

errors = []


def fail(where, message):
    errors.append(f"{where}: {message}")


def git(*args):
    return subprocess.run(["git", *args], capture_output=True, text=True)


def strip_comment(line):
    """The line without its `#` comment; a `#` inside a string stays."""
    quoted = False
    for i, char in enumerate(line):
        if char == '"':
            quoted = not quoted
        elif char == "#" and not quoted:
            return line[:i]
    return line


def laws(text):
    """{name: normalized text} of the law blocks in one LAWS.bend."""
    found, name, body = {}, None, []
    for line in text.splitlines() + ["<end>"]:
        start = LAW.match(line)
        inside = name is not None and (not line.strip() or line[0] in " \t")
        if inside:
            body.append(line)
            continue
        if name is not None:
            found[name] = " ".join(" ".join(strip_comment(l) for l in body).split())
            name = None
        if start:
            name, body = start.group(1), [line]
    return found


def tree_laws(tree):
    """{(path, name): text} for every LAWS.bend at a tree-ish, or the index (":")."""
    if tree == ":":
        paths = git("ls-files").stdout.split()
    elif tree is None:
        return {}
    else:
        paths = git("ls-tree", "-r", "--name-only", tree).stdout.split()
    found = {}
    for path in paths:
        if path == "LAWS.bend" or path.endswith("/LAWS.bend"):
            text = git("show", f"{tree}{path}" if tree == ":" else f"{tree}:{path}").stdout
            for name, body in laws(text).items():
                found[(path, name)] = body
    return found


def changed(before, after):
    keys = set(before) | set(after)
    return sorted({name for (path, name) in keys if before.get((path, name)) != after.get((path, name))})


def check_named(where, names, message):
    trailers = set(TRAILER.findall(message))
    for name in names:
        if name not in trailers:
            fail(where, f"law `{name}` changed without a `Law: {name}` trailer")


def check_history():
    if git("rev-parse", "--verify", "-q", "main").returncode != 0:
        return
    log = git("log", "--first-parent", "--format=%H", "main", "--", ":(glob)**/LAWS.bend")
    for commit in log.stdout.split():
        parent = commit + "^1"
        has_parent = git("rev-parse", "--verify", "-q", parent).returncode == 0
        names = changed(tree_laws(parent if has_parent else None), tree_laws(commit))
        message = git("log", "-1", "--format=%B", commit).stdout
        check_named(commit[:7], names, message)


def check_citations():
    for path in pathlib.Path(".").glob("**/LAWS.bend"):
        for number, line in enumerate(path.read_text().splitlines(), 1):
            citation = CITATION.search(line)
            if not citation:
                continue
            for slug in re.split(r"[,\s]+", citation.group(1).strip()):
                if slug and not pathlib.Path(f"docs/decisions/{slug}.md").exists():
                    fail(f"{path}:{number}", f"cites missing record `{slug}`")


def check_commit_msg(message_file):
    branch = git("symbolic-ref", "--short", "-q", "HEAD").stdout.strip()
    if branch != "main":
        return
    message = pathlib.Path(message_file).read_text()
    message = "\n".join(line for line in message.splitlines() if not line.startswith("#"))
    has_head = git("rev-parse", "--verify", "-q", "HEAD").returncode == 0
    names = changed(tree_laws("HEAD" if has_head else None), tree_laws(":"))
    check_named(message_file, names, message)


if len(sys.argv) == 3 and sys.argv[1] == "--commit-msg":
    check_commit_msg(sys.argv[2])
else:
    check_history()
    check_citations()

for error in errors:
    print(error)
print(f"laws: {len(errors)} problem(s)" if errors else "laws: ok")
sys.exit(1 if errors else 0)
