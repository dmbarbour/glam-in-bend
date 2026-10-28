#!/usr/bin/env python3
"""One wire of controls, every reduction order: is fusion sound?

The model behind `fuse-control-runs` (docs/decisions/) and NetPairing's
`pairing-fusion`. A control is (kind, n, up, by): kind 'L' faces the source
(values cross it going down), 'C' faces consumers (consumers cross it going
up); it moves levels above n up or down by `by` (kprim.bend's lift). A word
lists a wire's controls from source to consumer; every word is polarized,
each control's negative port toward the source. A value at level v sits
above the word, a consumer at level u below it. Moves, as the kernel's
rules:
  - the value crosses a leading L: v = lift(L, v), the L gone with it;
  - the consumer crosses a trailing C: u = lift(C, u);
  - C a then L b, facing: equal, both gone; else they swap, each index
    above the other's moved through the other (rule.lift, t false);
  - with fusion, L p then L l (values cross p first) become compose(p, l),
    C a then C b (consumers cross b first) compose(b, a), when the pair's
    shape is allowed (below);
  - with --peel, a facing pair at one index that differs is first taken
    apart as runs of unit brackets: two raises cancel the shorter's units
    and leave the rest from where they end; a raise of more than one
    meeting a drop gives up one unit, which crosses it.
When the word is empty, value and consumer meet: the outcome is the pair of
levels. Unfused reduction reaches one outcome from every start; a start
whose fused outcomes differ from it is a failure. Failures are shrunk (drop
a control, lower an index, an offset or a level, while it still fails) and
the distinct minimal ones printed with a reduction to each wrong outcome.

Shapes of a fusion of (n1, up b1) then (n2, o2), by number:
  0 up then up, n2 = n1 + b1   1 up then up, n2 = n1   2 up then up, between
  3 up then down by b1 (nothing)   4 up then down by less   5 up then down by more

    ctlwire.py [--peel] [--shapes 0,1,..] [--weights] exhaustive MAXLEN [MAXN [MAXLVL]]
    ctlwire.py [--peel] [--shapes 0,1,..] [--weights] sample LENGTH COUNT SEED [MAXN [MAXLVL]]

With --weights, a start fails instead when its fused reductions, each
move weighted by the unit interactions it stands for (Model.weighted),
do not all total the interactions of its unit brackets reduced unfused
(units), or when those depend on order: the weights that
heap-strategies.profile counts on whole nets.

The kernel's rule: --peel --shapes 0. Its old fusion: --shapes 0,1,2,3,4,5.
Drops are by 1 only, as lowering emits. Memory grows with MAXLEN; run under
scripts/capped.sh (length 4 exhaustive: about 0.7 GB, two minutes).
"""
import itertools
import random
import sys


def lift(c, j):
    _, n, up, by = c
    if j > n:
        return j + by if up else j - by
    return j


def shape(first, second):
    _, n1, _, b1 = first
    _, n2, u2, b2 = second
    if u2:
        return 0 if n2 == n1 + b1 else 1 if n2 == n1 else 2
    return 3 if b1 == b2 else 4 if b1 > b2 else 5


def compose(first, second):
    """kprim.compose before fuse-control-runs: the control acting as first
    then second, 'id' for none, None if they do not fuse"""
    _, n1, u1, b1 = first
    _, n2, u2, b2 = second
    if not (u1 and n1 <= n2 <= n1 + b1):
        return None
    if u2:
        return (n1, True, b1 + b2)
    if b1 > b2:
        return (n1, True, b1 - b2)
    if b1 == b2:
        return "id"
    return (n1, False, b2 - b1)


class Model:
    def __init__(self, shapes, peel):
        self.shapes, self.peel = shapes, peel

    def facing(self, a, b):
        """C a then L b facing: what replaces them, and the unit
        interactions that stands for (--weights)"""
        if a[1:] == b[1:]:
            return (), a[3]
        if self.peel and a[1] == b[1]:
            n = a[1]
            if a[2] and b[2]:
                m = min(a[3], b[3])
                if b[3] > a[3]:
                    return (("L", n + m, True, b[3] - m),), m
                return (("C", n + m, True, a[3] - m),), m
            if b[2] and b[3] > 1:
                return (("L", n, True, 1), ("L", n, True, b[3] - 1), a), b[3]
            if a[2] and a[3] > 1:
                return (b, ("C", n, True, a[3] - 1), ("C", n, True, 1)), a[3]
        return (("L", lift(a, b[1]), b[2], b[3]), ("C", lift(b, a[1]), a[2], a[3])), a[3] * b[3]

    def weighted(self, state, fuse):
        """each move from state, and the unit interactions it stands for: a
        run of b crossing a value, a consumer or a control's b units, two
        runs crossing each unit of one each of the other, equal runs
        cancelling unit by unit, a peel what it cancels or crosses, a
        fusion none"""
        v, w, u = state
        out = []
        if w and w[0][0] == "L":
            out.append(((lift(w[0], v), w[1:], u), w[0][3]))
        if w and w[-1][0] == "C":
            out.append(((v, w[:-1], lift(w[-1], u)), w[-1][3]))
        for i in range(len(w) - 1):
            a, b = w[i], w[i + 1]
            if a[0] == "C" and b[0] == "L":
                rep, k = self.facing(a, b)
                out.append(((v, w[:i] + rep + w[i + 2:], u), k))
            if fuse and a[0] == b[0]:
                first, second = (a, b) if a[0] == "L" else (b, a)
                r = compose(first, second)
                if r is not None and shape(first, second) in self.shapes:
                    rep = () if r == "id" else ((a[0],) + r,)
                    out.append(((v, w[:i] + rep + w[i + 2:], u), 0))
        return out

    def moves(self, state, fuse):
        return [m for m, _ in self.weighted(state, fuse)]

    def totals(self, state, fuse, memo):
        """the unit interactions of every complete reduction from state"""
        if state in memo:
            return memo[state]
        ws = self.weighted(state, fuse)
        res = frozenset([0]) if not ws else frozenset(
            k + t for m, k in ws for t in self.totals(m, fuse, memo))
        memo[state] = res
        return res

    def outcomes(self, state, fuse, memo):
        if state in memo:
            return memo[state]
        ms = self.moves(state, fuse)
        if not ms:
            v, w, u = state
            res = frozenset([(v, u)]) if not w else frozenset([("stuck", v, w, u)])
        else:
            res = frozenset().union(*(self.outcomes(m, fuse, memo) for m in ms))
        memo[state] = res
        return res

    def path_to(self, state, target):
        seen = {state: None}
        frontier = [state]
        while frontier:
            nxt = []
            for s in frontier:
                ms = self.moves(s, True)
                if not ms and not s[1] and (s[0], s[2]) == target:
                    out = []
                    while s is not None:
                        out.append(s)
                        s = seen[s]
                    return out[::-1]
                for m in ms:
                    if m not in seen:
                        seen[m] = s
                        nxt.append(m)
            frontier = nxt
        return None


def show(state):
    v, w, u = state
    ws = " ".join(f"{k}({n},{'+' if up else '-'}{by})" for k, n, up, by in w)
    return f"v{v} [{ws}] u{u}"


def units(state):
    """the start with every run of raises as its unit brackets, in the
    order they are crossed: an L's from the source, a C's from the
    consumer (law units_are_run)"""
    v, w, u = state
    out = []
    for k, n, up, by in w:
        idx = range(n, n + by) if up else [n]
        us = [(k, j, up, 1 if up else by) for j in idx]
        out.extend(us if k == "L" else us[::-1])
    return (v, tuple(out), u)


def smaller(state):
    v, w, u = state
    for i in range(len(w)):
        yield (v, w[:i] + w[i + 1:], u)
    for i, (k, n, up, by) in enumerate(w):
        if n > 0:
            yield (v, w[:i] + ((k, n - 1, up, by),) + w[i + 1:], u)
        if by > 1:
            yield (v, w[:i] + ((k, n, up, by - 1),) + w[i + 1:], u)
    if v > 0:
        yield (v - 1, w, u)
    if u > 0:
        yield (v, w, u - 1)


def main(argv):
    peel = "--peel" in argv
    weights = "--weights" in argv
    argv = [a for a in argv if a not in ("--peel", "--weights")]
    shapes = {0, 1, 2, 3, 4, 5}
    if "--shapes" in argv:
        i = argv.index("--shapes")
        shapes = {int(c) for c in argv[i + 1].split(",") if c}
        argv = argv[:i] + argv[i + 2:]
    mode = argv[0]
    if mode == "exhaustive":
        maxlen, rest = int(argv[1]), argv[2:]
    else:
        length, count, seed, rest = int(argv[1]), int(argv[2]), int(argv[3]), argv[4:]
    maxn = int(rest[0]) if rest else 2
    maxlvl = int(rest[1]) if len(rest) > 1 else 5
    model = Model(shapes, peel)
    cs = [(k, n, up, by) for k in "LC" for n in range(maxn + 1) for up in (True, False)
          for by in (1, 2) if up or by == 1]
    fm, um = {}, {}
    found, failures, total, multi = set(), 0, 0, 0

    def fails(s):
        if weights:
            ut = model.totals(units(s), False, um)
            return len(ut) != 1 or model.totals(s, True, fm) != ut
        return model.outcomes(s, True, fm) != model.outcomes(s, False, um)

    def check(state):
        nonlocal failures, total, multi
        total += 1
        if weights:
            if len(model.totals(units(state), False, um)) > 1:
                multi += 1
        elif len(model.outcomes(state, False, um)) > 1:
            multi += 1
        if fails(state):
            failures += 1
            while True:
                for s in smaller(state):
                    if s[1] and fails(s):
                        state = s
                        break
                else:
                    break
            found.add(state)
        if len(fm) + len(um) > 1_500_000:
            fm.clear()
            um.clear()

    if mode == "exhaustive":
        for n in range(1, maxlen + 1):
            for w in itertools.product(cs, repeat=n):
                for v in range(maxlvl + 1):
                    for u in range(maxlvl + 1):
                        check((v, w, u))
    else:
        rng = random.Random(seed)
        for _ in range(count):
            check((rng.randrange(maxlvl + 1), tuple(rng.choice(cs) for _ in range(length)), rng.randrange(maxlvl + 1)))
    if weights:
        print(f"shapes {sorted(shapes)}, peel {peel}, weights: {failures} of {total} starts fail; "
              f"{multi} where the unit brackets' interactions depend on order; "
              f"{len(found)} distinct minimal failures")
        for st in sorted(found, key=lambda s: (len(s[1]), s)):
            print(show(st), "units", sorted(model.totals(units(st), False, {})),
                  "| fused", sorted(model.totals(st, True, {})))
        return 1 if failures else 0
    print(f"shapes {sorted(shapes)}, peel {peel}: {failures} of {total} starts fail; "
          f"{multi} where unfused reaches more than one outcome; {len(found)} distinct minimal failures")
    for st in sorted(found, key=lambda s: (len(s[1]), s)):
        good = model.outcomes(st, False, {})
        bad = model.outcomes(st, True, {}) - good
        print("\n" + show(st), "unfused ->", sorted(good, key=str), "| fused also ->", sorted(bad, key=str))
        for o in sorted(bad, key=str):
            p = model.path_to(st, o)
            if p:
                print("   ", " => ".join(show(x) for x in p))


if __name__ == "__main__":
    main(sys.argv[1:])
