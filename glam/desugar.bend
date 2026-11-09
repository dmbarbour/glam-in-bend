import Base
import ./parse.bend as G

# Desugaring (HelloLadder, ladder-lambda.levels): a parsed expression to
# the few forms the lowering knows, its scope checked on the way.
# - `a ++ b` is the builtin append applied to a, then to b.
# - `x.a.b` is x's field a read, then that one's b: the builtin get,
#   its key collected, applied to x.
# - A binding group, `let`'s or `where`'s, is the lambdas and
#   applications it stands for, `let x = v in b` being `(\x -> b) v`: its
#   live bindings nested in the order of their needs, each binding's
#   lambda scoping the bindings after it and the body. A binding nothing
#   needs is dropped: a subnet disconnected from the result is an obvious
#   error (`net-obvious-errors`), and dead code is none. Live bindings
#   that need each other in a cycle wait for fixpoints (`ladder-objects`).
# - A name bound twice in one group, a local bound again inside its scope
#   ("local `x` shadows existing local `x`"), and a local named as a
#   top-level definition are errors (`shadowing-is-an-error`).
#
# The lowering then pairs every fan by GAL levels (`lowering-uses-levels`),
# a binding's value an application's argument, a box one level deeper.

type Ds is Data:
  DOk{e: G.Expr}
  DErr{d: G.Diag}

def has(+n: List<&2, U32>, ns: List<&2, List<&2, U32>>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{m, rest}:
      G.bytes_eq(n, m) || has(n, rest)

def without.k(+drop: Bool, n: List<&2, U32>, rest: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match drop:
    case True{}:
      rest
    case False{}:
      Con{n, rest}

# ns without the name x
def without(ns: List<&2, List<&2, U32>>, +x: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+n, rest}:
      without.k(G.bytes_eq(n, x), n, without(rest, x))

# ns without any of xs (xs first, the list that shrinks)
def without_all(xs: List<&2, List<&2, U32>>, ns: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      ns
    case Con{x, rest}:
      without_all(rest, without(ns, x))

def only.k(+keep: Bool, n: List<&2, U32>, rest: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match keep:
    case True{}:
      Con{n, rest}
    case False{}:
      rest

# the names of ns that are among group's
def only(ns: List<&2, List<&2, U32>>, +group: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+n, rest}:
      only.k(has(n, group), n, only(rest, group))

def union.k(+seen: Bool, n: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match seen:
    case True{}:
      acc
    case False{}:
      Con{n, acc}

# a's names, then b's not among them (b first, the list that shrinks)
def union(b: List<&2, List<&2, U32>>, +a: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match b:
    case Nil{}:
      a
    case Con{+n, rest}:
      union(rest, union.k(has(n, a), n, a))

# A group's chain
# ===============

# the names a chain binds, in order
def gnames(g: G.Expr) -> List<&2, List<&2, U32>>:
  match g:
    case G.EBind{+l, n, v, rest}:
      Con{n, gnames(rest)}
    case _:
      Nil{}

def gbinds(g: G.Expr) -> List<&2, G.Bd>:
  match g:
    case G.EBind{+l, n, v, rest}:
      Con{G.Bd{l, n, v}, gbinds(rest)}
    case _:
      Nil{}

def gbody(g: G.Expr) -> G.Expr:
  match g:
    case G.EBind{+l, n, v, rest}:
      gbody(rest)
    case G.EIn{b}:
      b
    case _:
      g

# the names an expression needs from outside it, each as often as used;
# a list's members are literals for now, needing none
def fv(e: G.Expr) -> List<&2, List<&2, U32>>:
  match e:
    case G.EName{+l, path}:
      match path:
        case Con{n, rest}:
          [n]
        case Nil{}:
          Nil{}
    case G.EOp2{+l, op, a, b}:
      List.append(&2, List<&2, U32>, fv(a), fv(b))
    case G.EApp{+l, f, x}:
      List.append(&2, List<&2, U32>, fv(f), fv(x))
    case G.ELam{+l, +x, body}:
      without(fv(body), x)
    case G.ELet{+l, +g}:
      without_all(gnames(g), fv(g))
    case G.EBind{+l, n, v, rest}:
      List.append(&2, List<&2, U32>, fv(v), fv(rest))
    case G.EIn{b}:
      fv(b)
    case _:
      Nil{}

def deps.if(more: Unit -> List<&2, List<&2, U32>>, +hit: Bool, v: G.Expr) -> List<&2, List<&2, U32>>:
  match hit:
    case True{}:
      fv(v)
    case False{}:
      more(Unit{})

# the names the binding named n needs
def deps_of(+n: List<&2, U32>, bs: List<&2, G.Bd>) -> List<&2, List<&2, U32>>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, rest}:
      match b:
        case G.Bd{+l, m, v}:
          deps.if(u => deps_of(n, rest), G.bytes_eq(n, m), v)

def deps_all(ns: List<&2, List<&2, U32>>, +bs: List<&2, G.Bd>) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, rest}:
      List.append(&2, List<&2, U32>, deps_of(n, bs), deps_all(rest, bs))

# ns and the group's names they need, through each other, k times
def grow(k: Nat, +ns: List<&2, List<&2, U32>>, +bs: List<&2, G.Bd>, +group: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match k:
    case 0n:
      ns
    case 1n+p:
      grow(p, union(only(deps_all(ns, bs), group), ns), bs, group)

def line_of.if(more: Unit -> U32, +hit: Bool, +l: U32) -> U32:
  match hit:
    case True{}:
      l
    case False{}:
      more(Unit{})

def line_of(+n: List<&2, U32>, bs: List<&2, G.Bd>) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{b, rest}:
      match b:
        case G.Bd{+l, m, v}:
          line_of.if(u => line_of(n, rest), G.bytes_eq(n, m), l)

def cycle.if(more: Unit -> Maybe<&2, G.Diag>, +hit: Bool, +n: List<&2, U32>, +l: U32) -> Maybe<&2, G.Diag>:
  match hit:
    case True{}:
      Some{G.Diag{l, "local `" ++ G.str(n) ++ "` needs itself through its group: recursive bindings are not supported yet"}}
    case False{}:
      more(Unit{})

# the first live binding that needs itself, through the group
def cycles(live: List<&2, List<&2, U32>>, +k: Nat, +bs: List<&2, G.Bd>, +group: List<&2, List<&2, U32>>) -> Maybe<&2, G.Diag>:
  match live:
    case Nil{}:
      None{}
    case Con{+n, rest}:
      cycle.if(u => cycles(rest, k, bs, group), has(n, grow(k, only(deps_of(n, bs), group), bs, group)), n, line_of(n, bs))

def all_in(ns: List<&2, List<&2, U32>>, +of: List<&2, List<&2, U32>>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+n, rest}:
      has(n, of) && all_in(rest, of)

def ready.if(more: Unit -> Maybe<&2, List<&2, U32>>, +ok: Bool, n: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{n}
    case False{}:
      more(Unit{})

# the first live binding not placed yet whose needs in the group all are
def ready(live: List<&2, List<&2, U32>>, +placed: List<&2, List<&2, U32>>, +bs: List<&2, G.Bd>, +group: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match live:
    case Nil{}:
      None{}
    case Con{+n, rest}:
      ready.if(u => ready(rest, placed, bs, group), Bool.not(has(n, placed)) && all_in(only(deps_of(n, bs), group), placed), n)

def place(m: Maybe<&2, List<&2, U32>>, +placed: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match m:
    case Some{n}:
      List.append(&2, List<&2, U32>, placed, [n])
    case None{}:
      placed

# the live bindings in the order of their needs, one placed a step
def order(k: Nat, +live: List<&2, List<&2, U32>>, +placed: List<&2, List<&2, U32>>, +bs: List<&2, G.Bd>, +group: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match k:
    case 0n:
      placed
    case 1n+p:
      order(p, live, place(ready(live, placed, bs, group), placed), bs, group)

def bind_of.if(more: Unit -> Maybe<&2, G.Bd>, +hit: Bool, b: G.Bd) -> Maybe<&2, G.Bd>:
  match hit:
    case True{}:
      Some{b}
    case False{}:
      more(Unit{})

def bind_of(+n: List<&2, U32>, bs: List<&2, G.Bd>) -> Maybe<&2, G.Bd>:
  match bs:
    case Nil{}:
      None{}
    case Con{b, rest}:
      match b:
        case G.Bd{+l, +m, v}:
          bind_of.if(u => bind_of(n, rest), G.bytes_eq(n, m), G.Bd{l, m, v})

def nest.one(m: Maybe<&2, G.Bd>, acc: G.Expr) -> G.Expr:
  match m:
    case Some{b}:
      match b:
        case G.Bd{+l, n, v}:
          G.EApp{l, G.ELam{l, n, acc}, v}
    case None{}:
      acc

# the body inside the bindings' lambdas, the last placed innermost
def nest(rev: List<&2, List<&2, U32>>, +bs: List<&2, G.Bd>, acc: G.Expr) -> G.Expr:
  match rev:
    case Nil{}:
      acc
    case Con{n, rest}:
      nest(rest, bs, nest.one(bind_of(n, bs), acc))

def checked(d: Maybe<&2, G.Diag>, more: Unit -> Ds) -> Ds:
  match d:
    case Some{x}:
      DErr{x}
    case None{}:
      more(Unit{})

def group.l(+live: List<&2, List<&2, U32>>, +bs: List<&2, G.Bd>, body: G.Expr, +group: List<&2, List<&2, U32>>, +k: Nat) -> Ds:
  checked(cycles(live, k, bs, group), u =>
    DOk{nest(List.reverse(&2, List<&2, U32>, order(k, live, Nil{}, bs, group)), bs, body)})

# a desugared chain to the lambdas and applications it stands for
def group.k(+bs: List<&2, G.Bd>, +body: G.Expr, +group: List<&2, List<&2, U32>>, +k: Nat) -> Ds:
  group.l(grow(k, only(fv(body), group), bs, group), bs, body, group, k)

def group(r: Ds) -> Ds:
  match r:
    case DOk{+g}:
      group.k(gbinds(g), gbody(g), gnames(g), U32.to_nat((U32.from_nat(List.length(&2, List<&2, U32>, gnames(g))) + 1 : U32)))
    case DErr{d}:
      DErr{d}

# Scope
# =====

def shadow.if(more: Unit -> Maybe<&2, G.Diag>, +local: Bool, +global: Bool, +n: List<&2, U32>, +l: U32) -> Maybe<&2, G.Diag>:
  match local global:
    case True{} _:
      Some{G.Diag{l, "local `" ++ G.str(n) ++ "` shadows existing local `" ++ G.str(n) ++ "`"}}
    case False{} True{}:
      Some{G.Diag{l, "local `" ++ G.str(n) ++ "` shadows the top-level definition `" ++ G.str(n) ++ "`"}}
    case False{} False{}:
      more(Unit{})

def bound.if(more: Unit -> Maybe<&2, G.Diag>, +twice: Bool, +local: Bool, +global: Bool, +n: List<&2, U32>, +l: U32) -> Maybe<&2, G.Diag>:
  match twice:
    case True{}:
      Some{G.Diag{l, "local `" ++ G.str(n) ++ "` is defined twice in its group"}}
    case False{}:
      shadow.if(more, local, global, n, l)

# a group's names checked: none bound twice in it, none bound outside it
def bound(bs: List<&2, G.Bd>, +seen: List<&2, List<&2, U32>>, +scope: List<&2, List<&2, U32>>, +globals: List<&2, List<&2, U32>>) -> Maybe<&2, G.Diag>:
  match bs:
    case Nil{}:
      None{}
    case Con{b, rest}:
      match b:
        case G.Bd{+l, +n, v}:
          bound.if(u => bound(rest, Con{n, seen}, scope, globals), has(n, seen), has(n, scope), has(n, globals), n, l)

# both halves desugared: an application, or `++`'s two
def two.k(+app: Bool, +line: U32, x: G.Expr, y: G.Expr) -> Ds:
  match app:
    case True{}:
      DOk{G.EApp{line, x, y}}
    case False{}:
      DOk{G.EApp{line, G.EApp{line, G.EBuiltin{4, 2}, x}, y}}

def two(a: Ds, b: Ds, +line: U32, +app: Bool) -> Ds:
  match a b:
    case DOk{x} DOk{y}:
      two.k(app, line, x, y)
    case DErr{d} _:
      DErr{d}
    case DOk{x} DErr{d}:
      DErr{d}

def bind_two(a: Ds, b: Ds, +line: U32, n: List<&2, U32>) -> Ds:
  match a b:
    case DOk{v} DOk{rest}:
      DOk{G.EBind{line, n, v, rest}}
    case DErr{d} _:
      DErr{d}
    case DOk{v} DErr{d}:
      DErr{d}

def in_one(a: Ds) -> Ds:
  match a:
    case DOk{b}:
      DOk{G.EIn{b}}
    case DErr{d}:
      DErr{d}

# a name's path past its first name: each a field read of the last
def fields(fs: List<&2, List<&2, U32>>, +line: U32, acc: G.Expr) -> G.Expr:
  match fs:
    case Nil{}:
      acc
    case Con{f, rest}:
      fields(rest, line, G.EApp{line, G.EField{line, f}, acc})

def lam_one(a: Ds, +line: U32, n: List<&2, U32>) -> Ds:
  match a:
    case DOk{b}:
      DOk{G.ELam{line, n, b}}
    case DErr{d}:
      DErr{d}

# an expression desugared within the locals of scope; globals are the
# module's top-level names
def expr(e: G.Expr, +scope: List<&2, List<&2, U32>>, +globals: List<&2, List<&2, U32>>) -> Ds:
  match e:
    case G.EOp2{+l, op, a, b}:
      two(expr(a, scope, globals), expr(b, scope, globals), l, False{})
    case G.EApp{+l, f, x}:
      two(expr(f, scope, globals), expr(x, scope, globals), l, True{})
    case G.ELam{+l, +n, body}:
      checked(shadow.if(u => None{}, has(n, scope), has(n, globals), n, l), u =>
        lam_one(expr(body, Con{n, scope}, globals), l, n))
    case G.ELet{+l, +g}:
      checked(bound(gbinds(g), Nil{}, scope, globals), u =>
        group(expr(g, List.append(&2, List<&2, U32>, scope, gnames(g)), globals)))
    case G.EBind{+l, n, v, rest}:
      bind_two(expr(v, scope, globals), expr(rest, scope, globals), l, n)
    case G.EIn{b}:
      in_one(expr(b, scope, globals))
    case G.EName{+l, path}:
      match path:
        case Con{n, rest}:
          DOk{fields(rest, l, G.EName{l, [n]})}
        case Nil{}:
          DOk{G.EName{l, Nil{}}}
    case _:
      DOk{e}
