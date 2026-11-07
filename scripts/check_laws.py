"""Law checks: every law changed on main is named in its commit.

A law is a `law <name>:` block in a file named LAWS.bend: the `law` line at
column 0 and the indented lines after it. A Blend module's law members are
laws too (blend/README.md): in a `.blend` file, a `law <name>:` line at any
indentation and the lines indented deeper after it, named by the objects
it sits in, `Monoid.right_id`. Comments and spacing aside, adding,
changing or removing one is a law change. A sample's laws are none: a
file under a directory named `samples` is a fixture, held to what it
prints or the error it must raise, and only the product's laws, Blend's
and glam's, ask the maintainer's approval (2026-11-07); one under a
directory named `invalid` neither (2026-11-04). Each commit on main's first-parent
history that changes laws must name every one of them in `Law: <name>`
trailers. Side branches are free: land law work on main with a merge
(`--no-ff`) or squash commit that names the laws.

Comments in LAWS.bend and in `.blend` files may cite decision records as
`# Record: <slug>`; each cited record must exist, in `docs/decisions/` or
in a project's directly within it (scripts/check_docs.py, Blend's).

Run from the repository root, or from a project's within it to check
that project's alone:
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
MEMBER = re.compile(r"^(\s*)law\s+([A-Za-z0-9_.-]+)\s*:")
OBJECT = re.compile(r"^(\s*)(?:abstract\s+)?(?:object|extend)\s+(?:abstract\s+)?([A-Za-z0-9_.]+)")
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


def normalized(body):
    return " ".join(" ".join(strip_comment(l) for l in body).split())


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
            found[name] = normalized(body)
            name = None
        if start:
            name, body = start.group(1), [line]
    return found


def blend_laws(text):
    """{name: normalized text} of the law members in one .blend file, each
    named by the objects it sits in."""
    found, objects, name, depth, body = {}, [], None, 0, []
    for line in text.splitlines() + ["<end>"]:
        at = len(line) - len(line.lstrip())
        if name is not None and (not line.strip() or at > depth):
            body.append(line)
            continue
        if name is not None:
            found[name] = normalized(body)
            name = None
        if not strip_comment(line).strip():
            continue
        while objects and objects[-1][0] >= at:
            objects.pop()
        start, header = MEMBER.match(line), OBJECT.match(line)
        if start:
            name = ".".join([o for _, o in objects] + [start.group(2)])
            depth, body = at, [line]
        elif header:
            objects.append((at, header.group(2)))
    return found


def invalid(path):
    """Whether a path is an invalid sample's, under a directory `invalid`."""
    return "invalid" in pathlib.PurePosixPath(path).parts[:-1]


def sample(path):
    """Whether a path is a sample's, under a directory `samples` or
    `invalid`: its laws are no law history."""
    return invalid(path) or "samples" in pathlib.PurePosixPath(path).parts[:-1]


def tree_laws(tree):
    """{(path, name): text} for every LAWS.bend and .blend file at a
    tree-ish, or the index (":")."""
    if tree == ":":
        paths = git("ls-files").stdout.split()
    elif tree is None:
        return {}
    else:
        paths = git("ls-tree", "-r", "--name-only", tree).stdout.split()
    found = {}
    for path in paths:
        read = (None if sample(path) else laws if path == "LAWS.bend" or path.endswith("/LAWS.bend")
                else blend_laws if path.endswith(".blend") else None)
        if read:
            # the path relative to here, as git lists it
            text = git("show", f":./{path}" if tree == ":" else f"{tree}:./{path}").stdout
            for name, body in read(text).items():
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
    log = git("log", "--first-parent", "--format=%H", "main", "--", ":(glob)**/LAWS.bend", ":(glob)**/*.blend")
    for commit in log.stdout.split():
        parent = commit + "^1"
        has_parent = git("rev-parse", "--verify", "-q", parent).returncode == 0
        names = changed(tree_laws(parent if has_parent else None), tree_laws(commit))
        message = git("log", "-1", "--format=%B", commit).stdout
        check_named(commit[:7], names, message)


# where records are: here, and in each project directly within, but a
# submodule (its `.git` its own), a repository checked by its own gate
RECORDS = [pathlib.Path("docs/decisions"),
           *sorted(d for d in pathlib.Path(".").glob("*/docs/decisions") if not (d.parents[1] / ".git").exists())]


def check_citations():
    # this repository's files, tracked or not but not ignored, as git lists
    # them: a submodule's are its own repository's
    listed = git("ls-files", "--cached", "--others", "--exclude-standard", "--",
                 ":(glob)**/LAWS.bend", ":(glob)**/*.blend").stdout.split()
    for path in [pathlib.Path(p) for p in listed if pathlib.Path(p).exists()]:
        if invalid(path.as_posix()):
            continue
        for number, line in enumerate(path.read_text().splitlines(), 1):
            citation = CITATION.search(line)
            if not citation:
                continue
            for slug in re.split(r"[,\s]+", citation.group(1).strip()):
                if slug and not any((d / f"{slug}.md").exists() for d in RECORDS):
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
