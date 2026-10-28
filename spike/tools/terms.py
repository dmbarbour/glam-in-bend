#!/usr/bin/env python3
"""Lambda terms as spike nets, with their values as a reference.

Lowers each term the way optimal reduction does: a live Fn per lambda, an Ap
per application, Copy fans for a variable used more than once (a site per
fan), an eraser for an unused one, and levels with brackets and croissants
at box boundaries. Evaluates each term directly,
call by need, for the value its net must reduce to. Writes a Bend program
that tests every term, or traces one through tracelib.bend.

    terms.py [--labels] emit OUT TERM...       the given terms
    terms.py [--labels] gen OUT COUNT [SEED]   COUNT random numeral expressions

--labels lowers without levels or control nodes, fans told apart by
their site alone; --unfused emits a bracket per box boundary and a
croissant per use, rather than one fused control per edge. --kernel
writes a differential test instead: each term through the spike, the
kernel's interpreted rule table and its generated rewrites (knet.bend),
flagging any difference between the last two, or in value with the
spike, and on demand (kstrat.bend's Demand), flagging a table mismatch
or more interactions than the full reduction. --profile writes each term
through the kernel's profiling strategy instead (kstrat.bend's
Profiling): value, counts, the weighted count, peels and interactions by
pair of kinds (spike/tools/profile.sh). --plus ends random terms in `(plus 1) 0` rather than `succ 0`,
so the partial application is data the copies share; --fma ends them in
`(fma 1 1) 0`, whose partial application, holding two numbers, is a data
table entry.

Then, in OUT:  bend terms.bend -o terms;  ./terms  (test all)  or
./terms trace K STEPS [FROM]. Run both under scripts/capped.sh.

Syntax: \\x y. body, application by juxtaposition, parentheses; #n is the
Church numeral n; succ, plus (curried addition), fma (curried a * b + c)
and decimal numbers are
builtin data; free names
from PRELUDE expand in place, fresh at each use. A term should reduce to a
number, so tests usually end in `succ 0`.
"""
import os
import random
import re
import sys

PRELUDE = {
    "I": r"\x. x",
    "K": r"\x y. x",
    "self": r"\t. t t",
    "add": r"\m n f x. m f (n f x)",
    "mul": r"\m n f. m (n f)",
    "pow": r"\m n. n m",
    "twice": r"\f x. f (f x)",
    "compose": r"\f g x. f (g x)",
    "flip": r"\f x y. f y x",
    "pair": r"\a b k. k a b",
    "fst": r"\p. p (\x y. x)",
    "snd": r"\p. p (\x y. y)",
}

TOKEN = re.compile(r"\s*(?:(\\)|(\.)|(\()|(\))|#(\d+)|(\d+)|([A-Za-z_][A-Za-z0-9_']*))")


def tokenize(s):
    out, i = [], 0
    s = s.rstrip()
    while i < len(s):
        m = TOKEN.match(s, i)
        if not m or m.end() == i:
            raise SyntaxError(f"bad input at {i}: {s[i:i + 10]!r}")
        i = m.end()
        lam, dot, lp, rp, church, num, name = m.groups()
        if lam: out.append(("\\",))
        elif dot: out.append((".",))
        elif lp: out.append(("(",))
        elif rp: out.append((")",))
        elif church is not None: out.append(("church", int(church)))
        elif num is not None: out.append(("int", int(num)))
        else: out.append(("name", name))
    return out


class Parser:
    def __init__(self, text):
        self.t, self.i = tokenize(text), 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else ("eof",)

    def take(self, kind):
        tok = self.peek()
        if tok[0] != kind:
            raise SyntaxError(f"expected {kind}, got {tok}")
        self.i += 1
        return tok

    def term(self):
        if self.peek()[0] == "\\":
            self.take("\\")
            names = []
            while self.peek()[0] == "name":
                names.append(self.take("name")[1])
            if not names:
                raise SyntaxError("lambda without a variable")
            self.take(".")
            body = self.term()
            for x in reversed(names):
                body = ("lam", x, body)
            return body
        f = self.atom()
        while self.peek()[0] in ("name", "church", "int", "(", "\\"):
            if self.peek()[0] == "\\":
                return ("app", f, self.term())
            f = ("app", f, self.atom())
        return f

    def atom(self):
        tok = self.peek()
        if tok[0] == "(":
            self.take("(")
            t = self.term()
            self.take(")")
            return t
        self.i += 1
        if tok[0] == "name":
            return ("var", tok[1])
        if tok[0] == "church":
            return church(tok[1])
        if tok[0] == "int":
            return ("int", tok[1])
        raise SyntaxError(f"unexpected {tok}")

    def whole(self):
        t = self.term()
        if self.peek()[0] != "eof":
            raise SyntaxError(f"trailing input at token {self.i}")
        return t


def church(n):
    body = ("var", "x")
    for _ in range(n):
        body = ("app", ("var", "f"), body)
    return ("lam", "f", ("lam", "x", body))


def parse(text):
    return expand(Parser(text).whole(), set())


def expand(t, bound):
    """Replace free prelude names and succ, leaving bound names alone."""
    k = t[0]
    if k == "var":
        x = t[1]
        if x in bound:
            return t
        if x == "succ":
            return ("succ",)
        if x == "plus":
            return ("plus",)
        if x == "fma":
            return ("fma",)
        if x in PRELUDE:
            return expand(Parser(PRELUDE[x]).whole(), set())
        raise NameError(f"free variable {x}")
    if k == "lam":
        return ("lam", t[1], expand(t[2], bound | {t[1]}))
    if k == "app":
        return ("app", expand(t[1], bound), expand(t[2], bound))
    return t


def show(t):
    k = t[0]
    if k == "var": return t[1]
    if k == "int": return str(t[1])
    if k == "succ": return "succ"
    if k == "plus": return "plus"
    if k == "fma": return "fma"
    if k == "lam": return f"(\\{t[1]}. {show(t[2])})"
    return f"({show(t[1])} {show(t[2])})"


# Reference evaluation, call by need
# ==================================

class OutOfFuel(Exception):
    pass


class Thunk:
    def __init__(self, f):
        self.f, self.done, self.v = f, False, None

    def force(self):
        if not self.done:
            self.v, self.done, self.f = self.f(), True, None
        return self.v


SUCC = "succ"
PLUS = "plus"
FMA = "fma"


def evaluate(t, fuel=200000, limit=10**6):
    budget = [fuel]

    def tick():
        budget[0] -= 1
        if budget[0] < 0:
            raise OutOfFuel()

    def ev(t, env):
        tick()
        k = t[0]
        if k == "var": return env[t[1]].force()
        if k == "int": return t[1]
        if k == "succ": return SUCC
        if k == "plus": return PLUS
        if k == "fma": return FMA
        if k == "lam": return ("fn", t[1], t[2], env)
        f = ev(t[1], env)
        a = Thunk(lambda: ev(t[2], env))
        return apply(f, a)

    def apply(f, a):
        tick()
        if f == SUCC:
            v = a.force()
            if not isinstance(v, int) or v >= limit:
                raise OutOfFuel()
            return v + 1
        if f == PLUS:
            v = a.force()
            if not isinstance(v, int):
                raise TypeError("plus of a non-number")
            return ("plus1", v)
        if isinstance(f, tuple) and f[0] == "plus1":
            v = a.force()
            if not isinstance(v, int) or f[1] + v >= limit:
                raise OutOfFuel()
            return f[1] + v
        if f == FMA or (isinstance(f, tuple) and f[0] in ("fma1", "fma2")):
            v = a.force()
            if not isinstance(v, int):
                raise TypeError("fma of a non-number")
            if f == FMA:
                return ("fma1", v)
            if f[0] == "fma1":
                return ("fma2", f[1], v)
            if f[1] * f[2] + v >= limit:
                raise OutOfFuel()
            return f[1] * f[2] + v
        if isinstance(f, tuple) and f[0] == "fn":
            _, x, body, env = f
            return ev(body, {**env, x: a})
        raise TypeError("applied a non-function")

    v = ev(t, {})
    return v if isinstance(v, int) else None


# Lowering to a spike template
# ============================
#
# With levels (docs/plans/NetPairing_2026-10-26.md, "Derivation"): a term
# at level n lowers a lambda to an Fn at n, an application to an Ap at n
# with its argument a box at n + 1. A variable's uses form a trie over the
# boxes entered from its binder: entering a box at depth k crosses a
# bracket Br k, a use at depth d sits behind a croissant Cr d, and where
# paths split at depth k a copy fan at level k joins them. Without levels
# (--labels), every use hangs off one chain of fans at the binder.

class Net:
    def __init__(self, levels, fused=True):
        self.nodes, self.links, self.site, self.boxes = [], [], 0, 0
        self.levels, self.fused = levels, fused

    def node(self, kind, *args):
        self.nodes.append((kind, args))
        return len(self.nodes) - 1

    def link(self, a, b):
        self.links.append((a, b))


class Var:
    """A bound variable: its binder's depth and boxes, and its uses."""
    def __init__(self, depth, path):
        self.depth, self.path, self.uses = depth, path, []


class Use:
    def __init__(self, var, depth, path):
        self.var, self.depth, self.path = var, depth, path


def plug(net, value, consumer):
    """Wire a value (a port, or a variable's use) to a consumer port."""
    if isinstance(value, Use):
        value.var.uses.append((consumer, value.depth, value.path))
    else:
        net.link(value, consumer)


def lower(net, t, env, depth, path):
    """Lower t; return the port providing its value, or a Use."""
    k = t[0]
    if k == "var":
        return Use(env[t[1]], depth, path)
    if k == "int":
        return (net.node("num", t[1]), 0)
    if k == "succ":
        return (net.node("succ"), 0)
    if k == "plus":
        return (net.node("plus"), 0)
    if k == "fma":
        return (net.node("fma"), 0)
    if k == "app":
        a = net.node("ap", depth if net.levels else 0)
        plug(net, lower(net, t[1], env, depth, path), (a, 0))
        net.boxes += 1
        plug(net, lower(net, t[2], env, depth + 1, path + (net.boxes,)), (a, 1))
        return (a, 2)
    # a lambda: Fn [+ fn, - result, + arg]
    f = net.node("fn", depth if net.levels else 0)
    v = Var(depth, path)
    plug(net, lower(net, t[2], {**env, t[1]: v}, depth, path), (f, 1))
    if net.levels:
        fan_trie(net, (f, 2), v)
    else:
        fan_chain(net, (f, 2), [u for u, d, p in v.uses])
    return (f, 0)


def fan_chain(net, src, uses):
    if not uses:
        net.link(src, (net.node("era"), 0))
        return
    for u in uses[:-1]:
        net.site += 1
        c = net.node("cp", net.site, 0)
        net.link(src, (c, 0))
        net.link((c, 1), u)
        src = (c, 2)
    net.link(src, uses[-1])


def fan_trie(net, src, var):
    if not var.uses:
        net.link(src, (net.node("era"), 0))
        return
    trie = {"uses": [], "boxes": {}}
    for consumer, depth, path in var.uses:
        node = trie
        for box in path[len(var.path):]:
            node = node["boxes"].setdefault(box, {"uses": [], "boxes": {}})
        node["uses"].append(consumer)
    if net.fused:
        emit_edge(net, src, var.depth, compress(trie, var.depth))
    else:
        emit_trie(net, src, trie, var.depth)


# Fused: each edge from a fan (or the binder) at depth k to the next fan,
# at depth k', crosses Br k, ..., Br (k' - 1), one control raising levels
# above k by k' - k; to a use at depth d it crosses Br k, ..., Br (d - 1)
# and Cr d, one control moving them by d - k - 1, none when that is 0.

def compress(trie, k):
    """Skip boxes holding one item: the next fan or use, and its depth."""
    items = len(trie["uses"]) + len(trie["boxes"])
    if items == 1 and trie["uses"]:
        return ("use", trie["uses"][0], k)
    if items == 1:
        return compress(next(iter(trie["boxes"].values())), k + 1)
    return ("fan", trie, k)


def emit_edge(net, src, k, target):
    kind, item, depth = target
    off = depth - k - 1 if kind == "use" else depth - k
    if off != 0:
        c = net.node("ctl", k, off)
        net.link(src, (c, 0))
        src = (c, 1)
    if kind == "use":
        net.link(src, item)
    else:
        emit_fan(net, src, item, depth)


def emit_fan(net, src, trie, k):
    items = [("use", u, k) for u in trie["uses"]] + [compress(b, k + 1) for b in trie["boxes"].values()]
    for n, target in enumerate(items):
        if n < len(items) - 1:
            net.site += 1
            c = net.node("cp", net.site, k)
            net.link(src, (c, 0))
            here, src = (c, 1), (c, 2)
        else:
            here = src
        emit_edge(net, here, k, target)


def emit_trie(net, src, trie, k):
    items = [("use", u) for u in trie["uses"]] + [("box", b) for b in trie["boxes"].values()]
    for n, (kind, item) in enumerate(items):
        if n < len(items) - 1:
            net.site += 1
            c = net.node("cp", net.site, k)
            net.link(src, (c, 0))
            here, src = (c, 1), (c, 2)
        else:
            here = src
        if kind == "use":
            cr = net.node("cr", k)
            net.link(here, (cr, 0))
            net.link((cr, 1), item)
        else:
            br = net.node("br", k)
            net.link(here, (br, 0))
            emit_trie(net, (br, 1), item, k + 1)


def to_tpl(t, levels=True, fused=True):
    net = Net(levels, fused)
    root = lower(net, t, {}, 0, ())
    if isinstance(root, Use):
        raise ValueError("a bare variable")
    return net, root


def bend_node(kind, args, levels=True):
    if kind == "fn": return f"X.fnl({args[0]})" if levels else "X.fn()"
    if kind == "ap": return f"X.apl({args[0]})" if levels else "X.ap()"
    if kind == "cp": return f"X.cpl({args[0]}, {args[1]})" if levels else f"X.cp({args[0]})"
    if kind == "br": return f"X.br({args[0]})"
    if kind == "cr": return f"X.cr({args[0]})"
    if kind == "ctl":
        n, off = args
        return f"X.ctl({n}, {'True{}' if off > 0 else 'False{}'}, {abs(off)})"
    if kind == "num": return f"X.num({args[0]})"
    return {"era": "X.era()", "succ": "X.succ()", "plus": "X.plus()", "fma": "X.fma()"}[kind]


def bend_tpl(net, root):
    nodes = ", ".join(bend_node(k, a, net.levels) for k, a in net.nodes)
    links = ", ".join(f"X.l({a}, {pa}, {b}, {pb})" for (a, pa), (b, pb) in net.links)
    return (f"T.Tpl{{[{nodes}],\n    [{links}],\n    T.TE{{{root[0]}, {root[1]}}}, {len(net.nodes)}}}")


def bend_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def emit(out, terms, spike, levels=True, fused=True, kernel=False, profile=False):
    os.makedirs(out, exist_ok=True)
    rel = os.path.relpath(spike, out)
    rows = []
    for text in terms:
        t = parse(text)
        want = evaluate(t)
        net, root = to_tpl(t, levels, fused)
        rows.append((text, want, net, root))
    lines = ["import Base"]
    for mod, alias in [("val", "V"), ("net", "N"), ("tpl", "T"), ("nets", "X"), ("tracelib", "L"), ("kernel", "K")]:
        lines.append(f"import {rel}/{mod}.bend as {alias}")
    lines.append("")
    lines.append("# Generated by spike/tools/terms.py; do not edit.")
    lines.append("")
    for i, (text, want, net, root) in enumerate(rows):
        lines.append(f"def t{i}() -> T.Tpl:\n  {bend_tpl(net, root)}\n")

    def dispatch(name, rtype, f):
        out = [f"def {name}(+k: U32) -> {rtype}:", "  match k:"]
        for i, row in enumerate(rows):
            out += [f"    case {i}:", f"      {f(i, row)}"]
        out += ["    case _:", f"      {f(len(rows) - 1, rows[-1])}", ""]
        return "\n".join(out)

    lines.append(dispatch("tpl_of", "T.Tpl", lambda i, r: f"t{i}()"))
    lines.append(dispatch("name_of", "String", lambda i, r: bend_str(r[0])))
    lines.append(dispatch("want_of", "U32", lambda i, r: str(r[1] if r[1] is not None else 4294967295)))
    main = PROFILE_MAIN if profile else KERNEL_MAIN if kernel else TEST_MAIN
    lines.append(main.replace("COUNT", f"{len(rows)}n"))
    path = os.path.join(out, "terms.bend")
    with open(path, "w") as f:
        f.write("\n".join(lines))
    print(f"wrote {path}: {len(rows)} terms, {sum(len(r[2].nodes) for r in rows)} nodes")


TEST_MAIN = r'''
def verdict(+ok: Bool) -> String:
  match ok:
    case True{}:
      "PASS"
    case False{}:
      "FAIL"

def got.show(m: Maybe<&2, V.Val>, +want: U32) -> String:
  match m:
    case Some{v}:
      match v:
        case V.VNum{+n}:
          verdict(U32.is_eq(n, want)) ++ " got " ++ U32.show(n)
        case _:
          "FAIL got a non-number"
    case None{}:
      "FAIL no value"

def got(r: N.Q & Maybe<&2, V.Val>, +want: U32) -> String:
  (q, v) = r
  match q:
    case N.Q{st, rq, +itrs, +errs, +ser}:
      got.show(v, want) ++ " in " ++ U32.show(itrs) ++ " interactions, " ++ U32.show(errs) ++ " errors"

def test_one(+k: U32, +fuel: Nat) -> String:
  "#" ++ U32.show(k) ++ " want " ++ U32.show(want_of(k)) ++ ": " ++ got(T.result(T.run(tpl_of(k), fuel)), want_of(k)) ++ "  " ++ name_of(k)

def test_all(n: Nat, +k: U32, +fuel: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      test_one(k, fuel) ++ "\n" ++ test_all(p, (k + 1 : U32), fuel)

def trace_k(+k: U32, +steps: Nat, +from: U32) -> String:
  L.trace(tpl_of(k), name_of(k), steps, from)

def go.args(xs: List<String>) -> String:
  match xs:
    case Con{p, r}:
      match r:
        case Con{cmd, r2}:
          match r2:
            case Con{k, r3}:
              match r3:
                case Con{s, r4}:
                  match r4:
                    case Con{f, r5}:
                      trace_k(L.u32_of(k), L.nat_of(s), L.u32_of(f))
                    case Nil{}:
                      trace_k(L.u32_of(k), L.nat_of(s), 0)
                case Nil{}:
                  test_all(COUNT, 0, L.nat_of(k))
            case Nil{}:
              test_all(COUNT, 0, 5000n)
        case Nil{}:
          test_all(COUNT, 0, 5000n)
    case Nil{}:
      test_all(COUNT, 0, 5000n)

# no arguments: test every term (fuel 64 rounds of 5000); `fuel F`: of F;
# `trace K STEPS [FROM]`: trace term K
def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    IO.print(go.args(xs))
'''


KERNEL_MAIN = r'''
def show_m(m: Maybe<&2, V.Val>) -> String:
  match m:
    case Some{v}:
      match v:
        case V.VNum{+n}:
          U32.show(n)
        case _:
          "fn"
    case None{}:
      "none"

def spike_res(r: N.Q & Maybe<&2, V.Val>) -> K.KRes:
  (q, v) = r
  match q:
    case N.Q{st, rq, +itrs, +errs, +ser}:
      K.KRes{v, itrs, errs, True{}}

def res_str(r: K.KRes) -> String:
  match r:
    case K.KRes{v, +itrs, +errs, +ok}:
      show_m(v) ++ " (" ++ U32.show(itrs) ++ ", " ++ U32.show(errs) ++ ")"

def res_val(r: K.KRes) -> String:
  match r:
    case K.KRes{v, +itrs, +errs, +ok}:
      show_m(v)

def res_tab(r: K.KRes) -> Bool:
  match r:
    case K.KRes{v, +itrs, +errs, +ok}:
      ok

def verdict(+tab: Bool, +same: Bool, +agree: Bool, +counts: Bool) -> String:
  match tab same agree counts:
    case False{} _ _ _:
      "TABLE MISMATCH"
    case True{} False{} _ _:
      "DIFFER ref/fast"
    case True{} True{} False{} _:
      "DIFFER value"
    case True{} True{} True{} True{}:
      "same, counts equal"
    case True{} True{} True{} False{}:
      "same, counts differ"

def lazy_res(r: K.DRes) -> K.KRes:
  match r:
    case K.DRes{k, +st, +lz, +live}:
      k

# on demand: the state it ended in, the nodes it left
def lazy_st(r: K.DRes) -> String:
  match r:
    case K.DRes{k, +st, +lz, +live}:
      K.st_name(st) ++ ", " ++ U32.show(live) ++ " live"

def lazy_more.s(more: Bool) -> String:
  match more:
    case True{}:
      "  LAZY MORE"
    case False{}:
      ""

def lazy_more(+lz: K.KRes, +fs: K.KRes) -> String:
  match lz fs:
    case K.KRes{v, +i, +e, +ok} K.KRes{v2, +i2, +e2, +ok2}:
      lazy_more.s(U32.is_gt(i, i2))

def cmp.go(+k: U32, +sp: K.KRes, +rf: K.KRes, +fs: K.KRes, +lz: K.DRes) -> String:
  "#" ++ U32.show(k) ++ " want " ++ U32.show(want_of(k)) ++ ": spike " ++ res_str(sp) ++ " | ref " ++ res_str(rf) ++
    " | fast " ++ res_str(fs) ++ " | lazy " ++ res_str(lazy_res(lz)) ++ " " ++ lazy_st(lz) ++ "  " ++
    verdict(res_tab(rf) && res_tab(fs) && res_tab(lazy_res(lz)), String.eq(res_str(rf), res_str(fs)), String.eq(res_val(rf), res_val(sp)), String.eq(res_str(rf), res_str(sp))) ++
    lazy_more(lazy_res(lz), fs) ++ "  " ++ name_of(k)

# demand's fuel counts the walk's steps too
def cmp_one(+k: U32) -> String:
  cmp.go(k, spike_res(T.result(T.run(tpl_of(k), 5000n))), K.run_t(tpl_of(k), 320000n, False{}), K.run_t(tpl_of(k), 320000n, True{}),
    K.run_d(tpl_of(k), 1280000n, []))

def cmp_all(n: Nat, +k: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      cmp_one(k) ++ "\n" ++ cmp_all(p, (k + 1 : U32))

# every term through the spike, the kernel's table, its generated rewrites
def main() -> IO(Unit):
  IO.print(cmp_all(COUNT, 0))
'''


PROFILE_MAIN = r'''
# a term reduced fully by the kernel's profiling strategy
def prof_one(+k: U32) -> String:
  "#" ++ U32.show(k) ++ " want " ++ U32.show(want_of(k)) ++ ": " ++ K.profile_t(tpl_of(k), 1280000n, True{}) ++ "  " ++ name_of(k)

def prof_all(n: Nat, +k: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      prof_one(k) ++ "\n" ++ prof_all(p, (k + 1 : U32))

# every term profiled
def main() -> IO(Unit):
  IO.print(prof_all(COUNT, 0))
'''


# Random numeral expressions
# ==========================

NUMFUNS = [r"(\n. mul n #2)", r"(\n. pow n #2)", r"(add #1)", r"(\n. n n)",
           r"(\n. add n n)", r"(mul #2)", r"(\n. n (add #1) #0)"]


def gen_expr(rng, depth):
    if depth <= 0 or rng.random() < 0.25:
        return f"#{rng.randint(0, 3)}"
    a = lambda: gen_expr(rng, depth - 1)
    choice = rng.randrange(8)
    if choice == 0: return f"(add {a()} {a()})"
    if choice == 1: return f"(mul {a()} {a()})"
    if choice == 2: return f"(pow {a()} {a()})"
    if choice == 3: return f"(self {a()})"
    if choice == 4:
        op = rng.choice(["add", "mul", "pow"])
        return f"((\\x. {op} x x) {a()})"
    if choice == 5:
        op = rng.choice(["add", "mul"])
        return f"((\\f. {op} (f {a()}) (f {a()})) {rng.choice(NUMFUNS)})"
    if choice == 6:
        return f"(twice {rng.choice(NUMFUNS)} {a()})"
    return f"({rng.choice(NUMFUNS)} {a()})"


def gen(count, seed, depth=3, maxval=64, tail="succ 0"):
    rng, seen, out = random.Random(seed), set(), []
    tries = 0
    while len(out) < count and tries < count * 200:
        tries += 1
        text = f"{gen_expr(rng, depth)} {tail}"
        if text in seen:
            continue
        seen.add(text)
        try:
            v = evaluate(parse(text), fuel=100000, limit=maxval + 1)
        except (OutOfFuel, RecursionError):
            continue
        if v is not None and v <= maxval:
            out.append(text)
    return out


def main(argv):
    sys.setrecursionlimit(100000)
    spike = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    levels, fused, kernel = "--labels" not in argv, "--unfused" not in argv, "--kernel" in argv
    profile = "--profile" in argv
    tail = "(plus 1) 0" if "--plus" in argv else "(fma 1 1) 0" if "--fma" in argv else "succ 0"
    argv = [a for a in argv if a not in ("--labels", "--unfused", "--kernel", "--profile", "--plus", "--fma")]
    if len(argv) >= 3 and argv[1] == "emit":
        emit(argv[2], argv[3:], spike, levels, fused, kernel, profile)
    elif len(argv) >= 4 and argv[1] == "gen":
        seed = int(argv[4]) if len(argv) > 4 else 1
        emit(argv[2], gen(int(argv[3]), seed, tail=tail), spike, levels, fused, kernel, profile)
    else:
        print(__doc__)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
