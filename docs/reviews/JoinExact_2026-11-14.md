# The exact join's premises — 2026-11-14

Drafted for the maintainer, at their request (2026-11-14): "Review
`join_exact` with advice from Fable to see if we can tighten or refactor
it; fourteen premises is a lot; it isn't necessarily an error, but it's
a smell", and, of the walk's fuel in the laws, "A fuel limit in law is
terribly awkward. We could have an abstract static-variable fuel limit,
if necessary, but setting a number like a million steps as a law doesn't
feel right to me." The subject: `join_exact` and its siblings
`pred_exact`, `unlink_exact`, `insert_exact` (`glam/LAWS.bend`, branch
`host-ring-exact`, commit `cbd26cc`), for
`cells-freeze.nested.host.ring.exact` of
[`../plans/Cells_2026-11-09.md`](../plans/Cells_2026-11-09.md). The
second reviewer's review, a Fable sub-agent's written without reading
this one, is [`JoinExactFable_2026-11-14.md`](JoinExactFable_2026-11-14.md).

## The premises, sorted

`join_exact` takes seven values beyond the heap (`d`, the situating
node `s`, the lists `pa`, `pb`, `pc`, `pd`, the cursors `x`, `y`) and
fourteen premises. Sorted by what they say:

| kind | premises | count |
| --- | --- | --- |
| the heap's shape, as every heap law has | `hf`, `hd32` | 2 |
| the ring | `hr` | 1 |
| where x and y stand in it | `hsp` (and the six list binders) | 1 |
| the walk's fuel | `hn` | 1 |
| node arithmetic | `hbx`, `hby` (bases), `hx0`, `hx1`, `hy0`, `hy1`, `hh` (the frees' words off the ring's links) | 7 |
| the ports the cursors face | `hu`, `hw` | 2 |

Two are the shape every heap law has, and one is the ring itself. The
other eleven fall in three groups, each with one cause: where the
cursors stand, said by splitting lists; the fuel; and facts of nodes
(where a node's words lie, what a cursor's port may face), said word by
word because the model knows nothing of nodes but their word 3.

## F1. Where the cursors stand: membership, not splits

The law names the ring as `pa ++ x :: pb`, then `pa ++ pb` as
`pc ++ y :: pd` (`hsp`), so that the walk's lemma can follow the list
from x round to x, and so that either order of x and y is covered. The
splits are the proof's device, not the claim. The claim is: x and y
members, the ring after the join is the ring without them. With a
function taking a member out of a list (`drop(t, x)`) and its split
(`before(t, x)`, `after(t, x)`, with the lemma that a member's list is
`before ++ x :: after`, proved once by induction), the law reads:

    for hr: ring(view(w), d, s, t)
    for hx: has(t, x)
    for hy: has(drop(t, x), y)
    ring(view(words(join(h, x, y))), d, s, drop(drop(t, x), y))

Six binders and `hsp` go; `pred_exact` says `last(before(t, x), s)`,
`unlink_exact` `drop(t, x)`. That y is not x follows from `hy`, as it
follows from `hsp` now.

Verdict: adjust. Cheap, lists only.

## F2. The fuel: from the heap, not a constant

The walks round a ring (`rg.pred`, `rg.find`, `rg.situ`,
`glam/ring.bend`) take a million steps of fuel, because Bend asks every
loop to end. The laws that follow a walk to its end then need the ring
shorter than the fuel, so the million enters the law (`hn`). The
options:

1. **A named constant** (`R.rg.fuel()`): the maintainer's abstract
   static variable. The literal leaves the laws, the premise stays: the
   ring has fewer cursors than the walk's fuel. Cheap; but the claim
   still depends on a number chosen for the code's convenience, and a
   ring longer than it would make the walk stop early and unlink the
   wrong node, silently.
2. **Fuel from the heap the ring lives in.** A walk round a ring of a
   heap of `2^d` words takes as fuel the heap's word count: the array's
   size, or the capacity word the heap's header keeps
   (`P.at_wcap()`, word 3). An exact ring's members' word 3 lie in
   distinct slots of those `2^d` words (`apart.all`), so it has at most
   `2^d` members, and the walk never runs out: the premise is then a
   theorem, pigeonhole over the slots, and no law names a fuel. The
   code reads the size once per walk. Until the pigeonhole lemma is
   proved, the laws can take the bound in the heap's own terms,
   fewer cursors than words, with no constant in sight.
3. **The walk's end as a result**: the laws claim only walks that found
   their cursor, and the code reports a walk out of fuel as an error,
   not a wrong node. Honest about the code as it stands (today a walk
   out of fuel returns a wrong predecessor), but every law about a serve
   would carry "no walk ran out", which is option 1's premise moved.

Verdict: replace, by option 2: the fuel taken from the heap; the
premise, fewer cursors than words, carried until pigeonhole is proved,
then dropped. Option 3's lesson stands whichever is chosen: a walk out
of fuel today silently returns a wrong node. The repository's rules ask
that a limit reached from user input be reported as a failure, not a
crash (`AGENTS.md`, Working Rules); a wrong answer is worse than either,
and option 2 makes it impossible rather than reported.

## F3. Node arithmetic: one lemma, and the ring's own invariants

Seven premises say where a node's words lie relative to another's:
x and y their own bases (for the free, which clears `P.base(r)`), and
the words the two frees write, x's and y's words 0 and 1 and the head,
none a remaining member's word 3. The model knows a member only by its
word 3 (`apart`), so each fact about a node's other words is a premise.

Every one follows from what nodes are: blocks of four words at bases
that are multiples of four, inside the heap, above the header's nodes
(node 0 holds the head, `P.at_fh()`, and the capacity, `P.at_wcap()`).
Two pieces:

- a model predicate on the ring, `nodes(Con{s, t}, d)`: each member its
  own base, below the heap's end, above the header; inserted cursors
  bring it (from `node_index`, a node is made at `(fh - 1) << 2`);
- one lemma of word arithmetic: two nodes at distinct aligned bases
  inside the heap have no word slot in common, and a node's four words
  lie in four slots. This is `lawful-words`' territory, the same fact
  the ArrayLaws review listed as missing (F5, a node's base), and it
  pays twice: the allocator's fresh node apart from every member, which
  `insert_exact`'s premise `apart` and the serve law will need, is the
  same lemma.

With them, `hbx`, `hby`, `hx0`, `hx1`, `hy0`, `hy1` and `hh` are
consequences of the ring and of x and y being members.

An alternative avoids arithmetic: strengthen `apart.all` to all four
words of distinct members in distinct slots, and every member off the
head. It defers the arithmetic to the insert's premise (the fresh node
apart from every member's four words), where the serve law will need it
anyway. The agent prefers the lemma, proved once.

Verdict: adjust, by the predicate and the lemma.

## F4. The ports: an invariant of the ring that the ring's steps keep

`hu`, `hw`: the link words of the ports x and y face are no member's
word 3, so that the join's link leaves the ring's links alone. With the
maintainer's facts (a cursor's only port is word 1, the situating node
has none, word 3 a pointer), a port's link word is a member's word 3
only were it that member's port 2, which none has.

As a premise of the whole ring: every member's word 1 holds a static or
a port whose link word is no member's word 3 (`faces`). It discharges
`hu` and `hw` for any two members. It must be kept by every step, and
it is, by its form:

- an unlink writes a word 3, a free its node's words 0 and 1 and the
  head: no remaining member's word 1 changes;
- a join's link writes `u + 1` with `w` and `w + 1` with `u`. Where x
  faced another member z (two cursors facing each other), `u + 1` is
  z's word 1, which now holds `w`, the port y faced, whose link word is
  off the ring's links by y's own `faces`: kept;
- an insert adds a member whose word 1 the splice linked: its port
  must satisfy `faces`, and every member's port must stay off the new
  member's word 3, a premise of the insert, which the serve discharges.

A stronger form, every member facing a port of a node outside the ring,
would not be kept where two cursors face each other: after the join the
member z faces whatever y faced, possibly another member. The weaker
form is the one that holds.

Verdict: adjust, by the invariant.

## F5. The law refactored

With F1 to F4, `ring` gains two conjuncts (`nodes`, `faces`), or a
bundle `ring.ok` beside it, and `join_exact` reads:

    for w, a, d, s, t, x, y
    for hf: full(w, d)
    for hd32: d < 32
    for hr: ring.ok(view(w), d, s, t)
    for hx: has(t, x)
    for hy: has(drop(t, x), y)
    ring.ok(view(words(join(h, x, y))), d, s, drop(drop(t, x), y))

Three premises beyond the heap's shape, from fourteen; and the
conclusion is the premise's own form, so that joins compose: a serve's
joins in turn keep `ring.ok`. `insert_exact` gains premises for the
cursor inserted (its node, its port), which the serve discharges from
the allocator and the splice. `join_keeps` and `join1_keeps` can take
the same `ring.ok` in place of `closed` and their own five premises on
x, y and their ports.

## F6. Cost and order

1. Membership (F1): `drop`, `before`, `after`, the split lemma, the
   laws restated. Small.
2. The fuel from the heap (F2): the three walks' fuel read from the
   heap, the laws' premise in its terms. A change to the code, so a
   count of its cost (`--count` is unaffected; instructions per walk,
   a read more).
3. `nodes` and the arithmetic lemma (F3). Moderate, on `lawful-words`.
4. `faces` (F4) and its keeping through each step. Moderate.
5. Pigeonhole over slots (F2), to drop the last premise on length. A
   lemma no hub package has: a list of distinct numbers below `n` is no
   longer than `n`. Moderate; a candidate for the hub
   (`blend/docs/HubCandidates.md`). The free list's model already says
   distinct as `nodup` over `Nat` (`spike/freelist.bend`), and the free
   list's exactness will want the same count.

Each is a narrow slice with its own mutations; the merge of
`host-ring-exact` can come first, with these as its next rungs, or
after the first two.

## Beside the second reviewer

The second reviewer read the same code without this review
(`JoinExactFable_2026-11-14.md`). The agent checked the lines it cites
before relaying it: the header's capacity word counts nodes, so the
words are four times it (`P.grow.done`, `spike/kprim.bend`); the
kernel allows 2^28 nodes; the freeze links a placeholder to any port of
a copied node, port 2 included (`glam/freeze.bend`).

Where the two agree:

- **The cause** (here the sorting, there F1): the premises are facts
  of the heap's layout that a model knowing only word 3 cannot state;
  enrich the model rather than trim premises one by one.
- **Membership, not splits** (here F1, there F7). The second reviewer
  is better on one point: state `x` and `y` both members of the ring
  and `x` not `y` as a premise of its own, rather than `y` a member of
  the ring without `x`. Then a join of a cursor with itself is outside
  the law by a premise that says so, which is where the proof the
  maintainer asked for (`.host.join.self`) lands.
- **The ports** (here F4, there F3): the same predicate, `faces`, every
  member's faced link word off the members' word 3, kept by every step
  with cursors facing each other included; the plan's `faces_out` is
  false there and is struck.
- **The fuel** (here F2, there F5, F6): a walk out of fuel today writes
  a wrong word silently, which the code should not do whatever the laws
  say; and the heap bounds a ring, so a walk given the heap's size as
  fuel never runs out on an exact ring, by pigeonhole over word-3
  slots, a lemma no package has.

What the second reviewer found and the agent did not:

- **More walks than three**: the materializer's climb takes the same
  million (`glam/materialize.bend`, `cl.go`), and `rg.find` out of fuel
  answers that no cursor holds the position, so that `mz.found` would
  insert a second cursor where one stands.
- **Rings interfere**: a join in one ring may write the word 1 of
  another ring's cursor (the port `y` faced may be that cursor), so
  `faces` of one ring is not kept by another ring's join. A law over
  every ring of a heap is `.host.path`'s territory; until then each
  ring's `faces` is a premise of its serve.
- **`join1_exact` and `leave_exact`**: the serve calls `join1` for every
  crossing found, and the root's join and the static's (`mz.root.w`,
  `sv.static.w`) are an unlink and a free with no law; a `leave(h, x)`
  in `glam/ring.bend` would carry them.
- **`hbx`, `hby` cost nothing to drop**: they only rewrite the frees'
  premises to `P.base(x)`; stated on `P.base(x)` directly, as
  `free_keeps` states its own, they go before any model changes.

Where they differ:

- **Node facts** (here F3, there F4). The agent proposed one arithmetic
  lemma, nodes at distinct aligned bases share no word slot, on the
  ground that the serve's fresh node needs it too. The second reviewer
  proposes widening the model's distinctness from word 3 to whole
  nodes (`disjoint`), with the head a conjunct of the ring, so that the
  join's premises follow by computation, no word arithmetic. Its
  argument holds: the fresh node's freshness enters as the insert's
  premise in either form, so the arithmetic is needed once at the
  serve whichever way, and the model route is the cheaper now. The
  agent concedes: `disjoint` first; `bases` once the mask lemma exists.
- **The fuel's first step** (here F2, there F6). The second reviewer
  would name the constant now (`R.fuel()`), the maintainer's fallback,
  then fuel from the heap with the pigeonhole. The agent would go to
  the heap at once, the laws carrying "fewer cursors than the heap's
  words", no constant at any point, then the pigeonhole. The heap's size
  can come from the words' array (lawful-arrays gives its size for a
  perfect tree, no new premise) or from the header's capacity word
  (one read, and a premise that it matches the array, which the kernel's
  growth keeps). The maintainer's to choose.

## Recommendation, both reviews together

On the branch, before the merge, so that four laws change once:

1. The fuel from the heap (or the named constant first), the walks out
   of fuel reported, not silent.
2. The laws stated by membership, `x` not `y` explicit; `hbx`, `hby`
   dropped by stating the frees' premises on `P.base`.
3. The model: `disjoint`, `faces`, the head off the ring's links, each
   a conjunct with the lemmas that keep it, each retiring its premises.
4. `join1_exact`, and `leave` with `leave_exact`.
5. The pigeonhole, retiring the last premise on length.

`join_exact` then takes the heap's shape, the ring, `x` and `y` members
and distinct: six premises, from fourteen.

## Questions for the maintainer

1. The fuel: straight to the heap's size, or the named constant first?
2. The heap's size: from the words' array, or the header's capacity
   word?
3. A walk out of fuel on a corrupt ring: an error reported
   (`P.err_if`), as the splice reports its own? It changes the walks'
   code and the frame laws, which then allow the error word.
4. The merge: after the refactoring, as recommended, or now with the
   refactoring as the next branch?
