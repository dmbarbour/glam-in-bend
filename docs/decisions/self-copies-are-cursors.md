# A source's copy of itself is a cursor into itself

`self-copies-are-cursors` · maintainer · rev e84733f

**Context.** Since `cells-freeze.nested`, a live source whose walk needs
another live function holds a copy of it: a ring of cursors into that
function's source, served by a frame whose host is the walk. A source
needing itself still spliced its own recipe, since a serve copies from
one net into another and a frame held two. Each unfolding redid the
recipe's work, and a cycle at one place unfolded without end where a
cycle through two sources is reported.

**Decision.** The maintainer (2026-11-13): "Self copies should literally
be self copies, i.e. a cursor into self instead of rebuilding from
recipe." It is the special case that ties the knot, as the Rust bootstrap
did.

**Consequences.**
- A source's need on itself puts a ring in the source, served from the
  same source. The walk that needs it is reentered, so it is released
  first, and the serve runs positioned demand and the copy in one net:
  the finished tree frozen to a template, spliced back where the cursor
  stands.
- The recipe splice inside sources retires; an `ESrc` keeps its recipe
  for `--refreeze` alone.
- A cycle at one place in a source meets the busy check, as one through
  two sources does. Divergence elsewhere is the program's: a program may
  run forever, as it may wait on a reflection task.

**Rule lives in:** `docs/plans/Cells_2026-11-09.md`,
`cells-freeze.nested.self`, until built.
