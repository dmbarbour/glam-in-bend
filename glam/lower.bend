import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/nets.bend as X
import ./parse.bend as G

# Lowering (HelloLadder): a parsed expression to the net the kernel
# reduces, through the construction `interaction_net` gives every user,
# data nodes, binds, copies and wires, never a term of the core's
# (`lambdas-lower-to-nets`). As far as the ladder reaches:
# - a text, a number, or a list literal of them: one data node holding
#   the value, a text and a list being the kernel's list (V.VList);
# - `a ++ b`: the builtin append (V's op 4) as data, applied to a's net,
#   then to b's: two application binds;
# - a `let` or `where` group (ladder-locals): each binding lowered once,
#   its value's port wired to its one use, or to a chain of binary copy
#   fans where it has several (`.copy N` as trees of binary fans,
#   Design.md), each fan's site its own node's index, unleveled: the
#   locals pair by static labels, which copying data needs no more of;
#   `ladder-lambda`, which copies functions, decides levels. A binding
#   nothing uses is not lowered at all: a subnet disconnected from the
#   result is an obvious error (`net-obvious-errors`), and dead code is
#   none. A group whose live bindings refer to each other in a cycle
#   waits for fixpoints (`ladder-objects`).
#
# Bend admits no mutual recursion, so one function, `expr`, walks the
# expression, a group's bindings encoded in the expression itself
# (parse.bend's EBind chain), and each result is a piece of net (Sub)
# numbered from 0: its nodes and links, its result port, the uses of
# names it leaves pending (a variable is no node, but a port waiting to be
# wired where its name is bound), and the names its groups bind, for the
# shadowing check (`shadowing-is-an-error`).

type Root is Data:
  REnd{e: T.TEnd}
  # the result is a name's value, not yet bound
  RVar{+line: U32, name: List<&2, U32>}

# a port waiting for the value of a name
type Use is Data:
  Use{name: List<&2, U32>, +line: U32, at: T.TEnd}

type Binder is Data:
  Binder{name: List<&2, U32>, +line: U32}

type Sub is Data:
  Sub{nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +size: U32, root: Root, uses: List<&2, Use>, binders: List<&2, Binder>}

# a binding lowered: its name, its line, its value's piece of net
type Bnd is Data:
  Bnd{name: List<&2, U32>, +line: U32, s: Sub}

type Lw is Data:
  LOk{s: Sub}
  # a group's bindings and body, lowered apart, before the group closes
  LGroup{bs: List<&2, Bnd>, body: Sub}
  LErr{d: G.Diag}

def codes(bs: List<&2, U32>) -> List<&2, V.Val>:
  match bs:
    case Con{+b, rest}:
      Con{V.VNum{b}, codes(rest)}
    case Nil{}:
      Nil{}

def data(v: V.Val) -> Sub:
  Sub{[T.TN{R.KData{}, V.PVal{v}}], Nil{}, 1, REnd{T.TE{0, 0}}, Nil{}, Nil{}}

def var(+line: U32, name: List<&2, U32>) -> Sub:
  Sub{Nil{}, Nil{}, 0, RVar{line, name}, Nil{}, Nil{}}

# Names
# =====

def has(+n: List<&2, U32>, ns: List<&2, List<&2, U32>>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{m, rest}:
      G.bytes_eq(n, m) || has(n, rest)

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

def use_names(us: List<&2, Use>) -> List<&2, List<&2, U32>>:
  match us:
    case Nil{}:
      Nil{}
    case Con{u, rest}:
      match u:
        case Use{n, +l, at}:
          Con{n, use_names(rest)}

def root_names(r: Root) -> List<&2, List<&2, U32>>:
  match r:
    case REnd{e}:
      Nil{}
    case RVar{+l, n}:
      [n]

# the names a piece of net needs: its pending uses and its result
def sub_names(s: Sub) -> List<&2, List<&2, U32>>:
  match s:
    case Sub{nodes, links, +size, root, uses, binders}:
      List.append(&2, List<&2, U32>, use_names(uses), root_names(root))

def bnames(bs: List<&2, Bnd>) -> List<&2, List<&2, U32>>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, rest}:
      match b:
        case Bnd{n, +l, s}:
          Con{n, bnames(rest)}

def sub_binders(s: Sub) -> List<&2, Binder>:
  match s:
    case Sub{nodes, links, +size, root, uses, binders}:
      binders

# the binders of every binding's value
def bs_binders(bs: List<&2, Bnd>) -> List<&2, Binder>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, rest}:
      match b:
        case Bnd{n, +l, s}:
          List.append(&2, Binder, sub_binders(s), bs_binders(rest))

def own_binders(bs: List<&2, Bnd>) -> List<&2, Binder>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, rest}:
      match b:
        case Bnd{n, +l, s}:
          Con{Binder{n, l}, own_binders(rest)}

# Shifting a piece of net past n nodes
# ====================================

def sh_root(r: Root, +by: U32) -> Root:
  match r:
    case REnd{e}:
      REnd{X.sh_end(e, by)}
    case RVar{+l, n}:
      RVar{l, n}

def sh_uses(us: List<&2, Use>, +by: U32) -> List<&2, Use>:
  match us:
    case Nil{}:
      Nil{}
    case Con{u, rest}:
      match u:
        case Use{n, +l, at}:
          Con{Use{n, l, X.sh_end(at, by)}, sh_uses(rest, by)}

# a port wired to a result: a link, or a use where the result is a name
type At is Data:
  At{ls: List<&2, T.TLink>, us: List<&2, Use>}

def attach(port: T.TEnd, r: Root) -> At:
  match r:
    case REnd{e}:
      At{[T.TL{port, e}], Nil{}}
    case RVar{+l, n}:
      At{Nil{}, [Use{n, l, port}]}

def at_ls(a: At) -> List<&2, T.TLink>:
  match a:
    case At{ls, us}:
      ls

def at_us(a: At) -> List<&2, Use>:
  match a:
    case At{ls, us}:
      us

def op2.at(a1: At, a2: At, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +k: U32, uses: List<&2, Use>, binders: List<&2, Binder>) -> Sub:
  match a1 a2:
    case At{l1, u1} At{l2, u2}:
      Sub{nodes, List.append(&2, T.TLink, links, List.append(&2, T.TLink, l1, l2)), (k + 3 : U32), REnd{T.TE{(k + 2 : U32), 2}},
        List.append(&2, Use, uses, List.append(&2, Use, u1, u2)), binders}

def op2.k(an: List<&2, T.TNode>, al: List<&2, T.TLink>, +sa: U32, ar: Root, au: List<&2, Use>, ab: List<&2, Binder>, bn: List<&2, T.TNode>, bl: List<&2, T.TLink>, +sb: U32, br: Root, bu: List<&2, Use>, bb: List<&2, Binder>, +k: U32) -> Sub:
  op2.at(attach(T.TE{(k + 1 : U32), 1}, ar), attach(T.TE{(k + 2 : U32), 1}, sh_root(br, sa)),
    List.append(&2, T.TNode, an, List.append(&2, T.TNode, bn, [T.TN{R.KData{}, V.PVal{V.VFun{4, 2, Nil{}}}}, X.ap(), X.ap()])),
    List.append(&2, T.TLink, al, List.append(&2, T.TLink, X.sh_links(bl, sa), [T.TL{T.TE{(k + 1 : U32), 0}, T.TE{k, 0}}, T.TL{T.TE{(k + 2 : U32), 0}, T.TE{(k + 1 : U32), 2}}])),
    k, List.append(&2, Use, au, sh_uses(bu, sa)), List.append(&2, Binder, ab, bb))

# glam's `++`: the builtin append, needing two lists, applied to a then
# to b: the data, then two applications, each's principal on the
# function, its first auxiliary the argument, its second the result
def op2.ab(a: Sub, b: Sub) -> Sub:
  match a b:
    case Sub{an, al, +sa, ar, au, ab} Sub{bn, bl, +sb, br, bu, bb}:
      op2.k(an, al, sa, ar, au, ab, bn, bl, sb, br, bu, bb, ((sa + sb : U32)))

def op2(+line: U32, a: Lw, b: Lw) -> Lw:
  match a b:
    case LOk{x} LOk{y}:
      LOk{op2.ab(x, y)}
    case LErr{d} _:
      LErr{d}
    case LOk{x} LErr{d}:
      LErr{d}
    case _ _:
      LErr{G.Diag{line, "a binding group where an operand was wanted"}}

# Lists of literals
# =================

def cons_v(v: V.Val, r: Maybe<&2, List<&2, V.Val>>) -> Maybe<&2, List<&2, V.Val>>:
  match r:
    case Some{vs}:
      Some{Con{v, vs}}
    case None{}:
      None{}

def cons_l(a: Maybe<&2, List<&2, V.Val>>, r: Maybe<&2, List<&2, V.Val>>) -> Maybe<&2, List<&2, V.Val>>:
  match a r:
    case Some{xs} Some{vs}:
      Some{Con{V.VList{xs}, vs}}
    case _ _:
      None{}

# a list literal's members as values, while every one is a literal
def consts(es: List<&2, G.Expr>) -> Maybe<&2, List<&2, V.Val>>:
  match es:
    case Nil{}:
      Some{Nil{}}
    case Con{e, rest}:
      match e:
        case G.EText{s}:
          cons_v(V.VList{codes(s)}, consts(rest))
        case G.ENum{+n}:
          cons_v(V.VNum{n}, consts(rest))
        case G.EList{xs}:
          cons_l(consts(xs), consts(rest))
        case _:
          None{}

def list(r: Maybe<&2, List<&2, V.Val>>, +line: U32) -> Lw:
  match r:
    case Some{vs}:
      LOk{data(V.VList{vs})}
    case None{}:
      LErr{G.Diag{line, "a list's members must be literals for now"}}

# A group closing
# ===============
#
# Its bindings and body were lowered apart. The checks first: a name bound
# twice in the group, a group's name bound again inside it (shadowing),
# the bindings the body needs (live, through each other), a cycle among
# those. Then the body and the live bindings put side by side, each
# binding's uses wired to its value: a binding whose value is another
# name's (an alias) passes its uses on to that name; the body's result,
# where it is a group's name, is wired as a use at a port that stands for
# the group's result (`self_end`).

def dups.if(more: Unit -> Maybe<&2, G.Diag>, +hit: Bool, n: List<&2, U32>, +l: U32) -> Maybe<&2, G.Diag>:
  match hit:
    case True{}:
      Some{G.Diag{l, "local `" ++ G.str(n) ++ "` is defined twice in its group"}}
    case False{}:
      more(Unit{})

def dups(bs: List<&2, Bnd>, +seen: List<&2, List<&2, U32>>) -> Maybe<&2, G.Diag>:
  match bs:
    case Nil{}:
      None{}
    case Con{b, rest}:
      match b:
        case Bnd{+n, +l, s}:
          dups.if(u => dups(rest, Con{n, seen}), has(n, seen), n, l)

def shadow.if(more: Unit -> Maybe<&2, G.Diag>, +hit: Bool, +n: List<&2, U32>, +l: U32) -> Maybe<&2, G.Diag>:
  match hit:
    case True{}:
      Some{G.Diag{l, "local `" ++ G.str(n) ++ "` shadows existing local `" ++ G.str(n) ++ "`"}}
    case False{}:
      more(Unit{})

# the first binder inside the group that binds one of its names again
def shadow(+own: List<&2, List<&2, U32>>, bds: List<&2, Binder>) -> Maybe<&2, G.Diag>:
  match bds:
    case Nil{}:
      None{}
    case Con{b, rest}:
      match b:
        case Binder{+n, +l}:
          shadow.if(u => shadow(own, rest), has(n, own), n, l)

def deps.if(more: Unit -> List<&2, List<&2, U32>>, +hit: Bool, s: Sub) -> List<&2, List<&2, U32>>:
  match hit:
    case True{}:
      sub_names(s)
    case False{}:
      more(Unit{})

# the names the binding named n needs
def deps_of(+n: List<&2, U32>, bs: List<&2, Bnd>) -> List<&2, List<&2, U32>>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, rest}:
      match b:
        case Bnd{m, +l, s}:
          deps.if(u => deps_of(n, rest), G.bytes_eq(n, m), s)

def deps_all(ns: List<&2, List<&2, U32>>, +bs: List<&2, Bnd>) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, rest}:
      List.append(&2, List<&2, U32>, deps_of(n, bs), deps_all(rest, bs))

# ns and the group's names they need, through each other, fuel times
def grow(k: Nat, +ns: List<&2, List<&2, U32>>, +bs: List<&2, Bnd>, +group: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
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

def line_of(+n: List<&2, U32>, bs: List<&2, Bnd>) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{b, rest}:
      match b:
        case Bnd{m, +l, s}:
          line_of.if(u => line_of(n, rest), G.bytes_eq(n, m), l)

def cycle.if(more: Unit -> Maybe<&2, G.Diag>, +hit: Bool, n: List<&2, U32>, +l: U32) -> Maybe<&2, G.Diag>:
  match hit:
    case True{}:
      Some{G.Diag{l, "local `" ++ G.str(n) ++ "` refers to itself through its group: recursive bindings are not supported yet"}}
    case False{}:
      more(Unit{})

# the first live binding that needs itself, through the group
def cycles(live: List<&2, List<&2, U32>>, +k: Nat, +bs: List<&2, Bnd>, +group: List<&2, List<&2, U32>>) -> Maybe<&2, G.Diag>:
  match live:
    case Nil{}:
      None{}
    case Con{+n, rest}:
      cycle.if(u => cycles(rest, k, bs, group), has(n, grow(k, only(deps_of(n, bs), group), bs, group)), n, line_of(n, bs))

# the body and the live bindings side by side: the nodes, links and uses
# so far, the next node's index, the binders, and each live binding's
# result shifted to its place
type Rb is Data:
  Rb{name: List<&2, U32>, +line: U32, root: Root}

type Mg is Data:
  Mg{nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +size: U32, uses: List<&2, Use>, roots: List<&2, Rb>}

def merge.put(+keep: Bool, n: List<&2, U32>, +l: U32, s: Sub, m: Mg) -> Mg:
  match keep:
    case False{}:
      m
    case True{}:
      match s m:
        case Sub{sn, sl, +ss, sr, su, sb} Mg{mn, ml, +ms, mu, mr}:
          Mg{List.append(&2, T.TNode, mn, sn), List.append(&2, T.TLink, ml, X.sh_links(sl, ms)), (ms + ss : U32),
            List.append(&2, Use, mu, sh_uses(su, ms)), Con{Rb{n, l, sh_root(sr, ms)}, mr}}

def merge(bs: List<&2, Bnd>, +live: List<&2, List<&2, U32>>, m: Mg) -> Mg:
  match bs:
    case Nil{}:
      m
    case Con{b, rest}:
      match b:
        case Bnd{+n, +l, s}:
          merge(rest, live, merge.put(has(n, live), n, l, s, m))

# Aliases: a binding whose value is another name's passes its uses on
# to that name, as many times as there are bindings, so that a chain of
# aliases resolves; the cycle check has refused a cycle of them.

def target.if(more: Unit -> Maybe<&2, List<&2, U32>>, +hit: Bool, r: Root) -> Maybe<&2, List<&2, U32>>:
  match hit:
    case True{}:
      match r:
        case RVar{+l, t}:
          Some{t}
        case REnd{e}:
          None{}
    case False{}:
      more(Unit{})

# the name the binding named n stands for, where it is an alias
def target(+n: List<&2, U32>, rs: List<&2, Rb>) -> Maybe<&2, List<&2, U32>>:
  match rs:
    case Nil{}:
      None{}
    case Con{r, rest}:
      match r:
        case Rb{m, +l, root}:
          target.if(u => target(n, rest), G.bytes_eq(n, m), root)

def renamed(t: Maybe<&2, List<&2, U32>>, n: List<&2, U32>, +l: U32, at: T.TEnd) -> Use:
  match t:
    case Some{m}:
      Use{m, l, at}
    case None{}:
      Use{n, l, at}

def rename(us: List<&2, Use>, +rs: List<&2, Rb>) -> List<&2, Use>:
  match us:
    case Nil{}:
      Nil{}
    case Con{u, rest}:
      match u:
        case Use{+n, +l, at}:
          Con{renamed(target(n, rs), n, l, at), rename(rest, rs)}

def renames(k: Nat, us: List<&2, Use>, +rs: List<&2, Rb>) -> List<&2, Use>:
  match k:
    case 0n:
      us
    case 1n+p:
      renames(p, rename(us, rs), rs)

# Wiring: each live binding's value to its uses, through a chain of
# binary copy fans where there are several. The port standing for the
# group's result is none of the net's (node 2^32 - 1): wired to it, a
# value becomes the result.

def self_end() -> T.TEnd:
  T.TE{4294967295, 0}

def is_self(e: T.TEnd) -> Bool:
  match e:
    case T.TE{+n, +p}:
      U32.is_eq(n, 4294967295)

# the extra nodes and links, the next node's index, and the result where
# a value was wired to the group's result
type Cn is Data:
  Cn{nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +size: U32, res: Maybe<&2, T.TEnd>}

def link_to.k(+to_self: Bool, src: T.TEnd, dst: T.TEnd, c: Cn) -> Cn:
  match to_self c:
    case True{} Cn{ns, ls, +k, res}:
      Cn{ns, ls, k, Some{src}}
    case False{} Cn{ns, ls, +k, res}:
      Cn{ns, Con{T.TL{dst, src}, ls}, k, res}

def link_to(src: T.TEnd, +dst: T.TEnd, c: Cn) -> Cn:
  link_to.k(is_self(dst), src, dst, c)

# a copy fan at the next index: its principal takes src, its first
# auxiliary goes to the use p
def add_cp(c: Cn, src: T.TEnd, +p: T.TEnd) -> Cn:
  match c:
    case Cn{ns, ls, +k, res}:
      link_to(T.TE{k, 1}, p, Cn{Con{X.cp(k), ns}, Con{T.TL{T.TE{k, 0}, src}, ls}, (k + 1 : U32), res})

def fan.if(more: Unit -> Cn, +last: Bool, src: T.TEnd, +p: T.TEnd, c: Cn) -> Cn:
  match last:
    case True{}:
      link_to(src, p, c)
    case False{}:
      more(Unit{})

def cn_size(c: Cn) -> U32:
  match c:
    case Cn{ns, ls, +k, res}:
      k

# src wired to the ends: directly to the last, through a fan to each
# other, the fans chained by their second auxiliaries
def fan(ends: List<&2, T.TEnd>, +src: T.TEnd, +c: Cn) -> Cn:
  match ends:
    case Nil{}:
      c
    case Con{+p, +rest}:
      fan.if(u => fan(rest, T.TE{cn_size(c), 2}, add_cp(c, src, p)), List.is_empty(&2, T.TEnd, rest), src, p, c)

def ends_of.k(+hit: Bool, at: T.TEnd, rest: List<&2, T.TEnd>) -> List<&2, T.TEnd>:
  match hit:
    case True{}:
      Con{at, rest}
    case False{}:
      rest

# the ports waiting for the name n
def ends_of(+n: List<&2, U32>, us: List<&2, Use>) -> List<&2, T.TEnd>:
  match us:
    case Nil{}:
      Nil{}
    case Con{u, rest}:
      match u:
        case Use{m, +l, at}:
          ends_of.k(G.bytes_eq(n, m), at, ends_of(n, rest))

def wire.root(r: Root, n: List<&2, U32>, +us: List<&2, Use>, c: Cn) -> Cn:
  match r:
    case REnd{e}:
      fan(ends_of(n, us), e, c)
    case RVar{+l, t}:
      c

def wire(rs: List<&2, Rb>, +us: List<&2, Use>, c: Cn) -> Cn:
  match rs:
    case Nil{}:
      c
    case Con{r, rest}:
      match r:
        case Rb{n, +l, root}:
          wire(rest, us, wire.root(root, n, us, c))

def outside.k(+inside: Bool, u: Use, rest: List<&2, Use>) -> List<&2, Use>:
  match inside:
    case True{}:
      rest
    case False{}:
      Con{u, rest}

# the uses left for an enclosing group: of no name of this one
def outside(us: List<&2, Use>, +group: List<&2, List<&2, U32>>) -> List<&2, Use>:
  match us:
    case Nil{}:
      Nil{}
    case Con{u, rest}:
      match u:
        case Use{+n, +l, at}:
          outside.k(has(n, group), Use{n, l, at}, outside(rest, group))

# a use left at the group's result: its name is an enclosing group's, so
# the result is that name's
def self_use.if(more: Unit -> Maybe<&2, Use>, +hit: Bool, u: Use) -> Maybe<&2, Use>:
  match hit:
    case True{}:
      Some{u}
    case False{}:
      more(Unit{})

def self_use(us: List<&2, Use>) -> Maybe<&2, Use>:
  match us:
    case Nil{}:
      None{}
    case Con{u, rest}:
      match u:
        case Use{n, +l, +at}:
          self_use.if(u2 => self_use(rest), is_self(at), Use{n, l, at})

def not_self.k(+self: Bool, u: Use, rest: List<&2, Use>) -> List<&2, Use>:
  match self:
    case True{}:
      rest
    case False{}:
      Con{u, rest}

def not_self(us: List<&2, Use>) -> List<&2, Use>:
  match us:
    case Nil{}:
      Nil{}
    case Con{u, rest}:
      match u:
        case Use{n, +l, +at}:
          not_self.k(is_self(at), Use{n, l, at}, not_self(rest))

# the group's result: the body's own port, a value wired to the group's
# result, or an enclosing group's name
def result(body: Root, res: Maybe<&2, T.TEnd>, left: Maybe<&2, Use>) -> Root:
  match res left:
    case Some{e} _:
      REnd{e}
    case None{} Some{u}:
      match u:
        case Use{n, +l, at}:
          RVar{l, n}
    case None{} None{}:
      body

def closed.c(c: Cn, m: Mg, body: Root, +us: List<&2, Use>, binders: List<&2, Binder>) -> Lw:
  match c m:
    case Cn{cn, cl, +k, res} Mg{mn, ml, +ms, mu, mr}:
      LOk{Sub{List.append(&2, T.TNode, mn, List.reverse(&2, T.TNode, cn)), List.append(&2, T.TLink, ml, cl), k,
        result(body, res, self_use(us)), not_self(us), binders}}

def body_use.k(+inside: Bool, +l: U32, n: List<&2, U32>) -> List<&2, Use>:
  match inside:
    case True{}:
      [Use{n, l, self_end()}]
    case False{}:
      Nil{}

# the body's result, where it is one of the group's names, as a use at
# the group's result port
def body_use(r: Root, +group: List<&2, List<&2, U32>>) -> List<&2, Use>:
  match r:
    case REnd{e}:
      Nil{}
    case RVar{+l, +n}:
      body_use.k(has(n, group), l, n)

def body_root.k(+inside: Bool, +l: U32, n: List<&2, U32>) -> Root:
  match inside:
    case True{}:
      REnd{self_end()}
    case False{}:
      RVar{l, n}

def body_root(r: Root, +group: List<&2, List<&2, U32>>) -> Root:
  match r:
    case REnd{e}:
      REnd{e}
    case RVar{+l, +n}:
      body_root.k(has(n, group), l, n)

def closed.u(+us: List<&2, Use>, m: Mg, +body: Root, +group: List<&2, List<&2, U32>>, binders: List<&2, Binder>) -> Lw:
  match m:
    case Mg{mn, ml, +ms, mu, +mr}:
      closed.c(wire(mr, us, Cn{Nil{}, Nil{}, ms, None{}}), Mg{mn, ml, ms, mu, mr}, body_root(body, group), outside(us, group), binders)

def closed.m(m: Mg, +body: Root, +k: Nat, +group: List<&2, List<&2, U32>>, binders: List<&2, Binder>) -> Lw:
  match m:
    case Mg{mn, ml, +ms, mu, +mr}:
      closed.u(renames(k, List.append(&2, Use, mu, body_use(body, group)), mr), Mg{mn, ml, ms, Nil{}, mr}, body, group, binders)

def checked(d: Maybe<&2, G.Diag>, more: Unit -> Lw) -> Lw:
  match d:
    case Some{x}:
      LErr{x}
    case None{}:
      more(Unit{})

def body_sub(s: Sub) -> Mg:
  match s:
    case Sub{sn, sl, +ss, sr, su, sb}:
      Mg{sn, sl, ss, su, Nil{}}

def sub_root(s: Sub) -> Root:
  match s:
    case Sub{sn, sl, +ss, sr, su, sb}:
      sr

def sub_names_body(+s: Sub) -> List<&2, List<&2, U32>>:
  sub_names(s)

def group_close.l(+live: List<&2, List<&2, U32>>, +group: List<&2, List<&2, U32>>, +bs: List<&2, Bnd>, +body: Sub, +k: Nat) -> Lw:
  checked(cycles(live, k, bs, group), u =>
    closed.m(merge(bs, live, body_sub(body)), sub_root(body), k, group,
      List.append(&2, Binder, own_binders(bs), List.append(&2, Binder, sub_binders(body), bs_binders(bs)))))

def group_close.g(+group: List<&2, List<&2, U32>>, +bs: List<&2, Bnd>, +body: Sub, +k: Nat) -> Lw:
  checked(dups(bs, Nil{}), u1 =>
    checked(shadow(group, List.append(&2, Binder, sub_binders(body), bs_binders(bs))), u2 =>
      group_close.l(grow(k, only(sub_names(body), group), bs, group), group, bs, body, k)))

def group_close(+bs: List<&2, Bnd>, +body: Sub) -> Lw:
  group_close.g(bnames(bs), bs, body, U32.to_nat((U32.from_nat(List.length(&2, Bnd, bs)) + 1 : U32)))

def close(g: Lw, +line: U32) -> Lw:
  match g:
    case LGroup{bs, body}:
      group_close(bs, body)
    case LErr{d}:
      LErr{d}
    case LOk{s}:
      LErr{G.Diag{line, "a binding group without its bindings"}}

def bind(n: List<&2, U32>, +line: U32, v: Lw, r: Lw) -> Lw:
  match v r:
    case LOk{s} LGroup{bs, body}:
      LGroup{Con{Bnd{n, line, s}, bs}, body}
    case LErr{d} _:
      LErr{d}
    case _ LErr{d}:
      LErr{d}
    case _ _:
      LErr{G.Diag{line, "a binding where its group was wanted"}}

def in(b: Lw) -> Lw:
  match b:
    case LOk{s}:
      LGroup{Nil{}, s}
    case LErr{d}:
      LErr{d}
    case LGroup{bs, body}:
      LErr{G.Diag{0, "a binding group where its body was wanted"}}

def name(+line: U32, path: List<&2, List<&2, U32>>) -> Lw:
  match path:
    case Con{n, rest}:
      match rest:
        case Nil{}:
          LOk{var(line, n)}
        case _:
          LErr{G.Diag{line, "a field of a name is not supported yet (ladder-dicts): " ++ G.path_str(Con{n, rest})}}
    case Nil{}:
      LErr{G.Diag{line, "an empty name"}}

# an expression lowered, the line its diagnostics name where it has none
def expr(e: G.Expr, +line: U32) -> Lw:
  match e:
    case G.EText{s}:
      LOk{data(V.VList{codes(s)})}
    case G.ENum{+n}:
      LOk{data(V.VNum{n})}
    case G.EList{xs}:
      list(consts(xs), line)
    case G.EName{+l, path}:
      name(l, path)
    case G.EOp2{+l, op, a, b}:
      op2(l, expr(a, l), expr(b, l))
    case G.ELet{+l, g}:
      close(expr(g, l), l)
    case G.EBind{+l, n, v, rest}:
      bind(n, l, expr(v, l), expr(rest, l))
    case G.EIn{body}:
      in(expr(body, line))

# The whole expression
# ====================
#
# The net of `asm.result`: its result a port, no name left pending (a
# reference to a top-level definition waits for ladder-thunks), and no
# local named as a top-level definition is (`shadowing-is-an-error`).

def global_shadow.if(more: Unit -> Maybe<&2, G.Diag>, +hit: Bool, +n: List<&2, U32>, +l: U32) -> Maybe<&2, G.Diag>:
  match hit:
    case True{}:
      Some{G.Diag{l, "local `" ++ G.str(n) ++ "` shadows existing global `" ++ G.str(n) ++ "`"}}
    case False{}:
      more(Unit{})

def global_shadow(bds: List<&2, Binder>, +globals: List<&2, List<&2, U32>>) -> Maybe<&2, G.Diag>:
  match bds:
    case Nil{}:
      None{}
    case Con{b, rest}:
      match b:
        case Binder{+n, +l}:
          global_shadow.if(u => global_shadow(rest, globals), has(n, globals), n, l)

type Top is Data:
  TOk{t: T.Tpl}
  TErr{d: G.Diag}

def pending(n: List<&2, U32>, +l: U32) -> Top:
  TErr{G.Diag{l, "a reference to " ++ G.str(n) ++ " is not evaluated yet (ladder-thunks)"}}

def top.e(us: List<&2, Use>, t: T.Tpl) -> Top:
  match us:
    case Con{u, rest}:
      match u:
        case Use{n, +l, at}:
          pending(n, l)
    case Nil{}:
      TOk{t}

def top.s(s: Sub) -> Top:
  match s:
    case Sub{nodes, links, +size, root, uses, binders}:
      match root:
        case REnd{e}:
          top.e(uses, T.Tpl{nodes, links, e, size})
        case RVar{+l, n}:
          pending(n, l)

def top.g(d: Maybe<&2, G.Diag>, s: Sub) -> Top:
  match d:
    case Some{x}:
      TErr{x}
    case None{}:
      top.s(s)

def top.w(w: Lw, +globals: List<&2, List<&2, U32>>) -> Top:
  match w:
    case LOk{+s}:
      top.g(global_shadow(sub_binders(s), globals), s)
    case LErr{d}:
      TErr{d}
    case LGroup{bs, body}:
      TErr{G.Diag{0, "a binding group left open"}}

# asm.result's expression to its net, the module's top-level names given
def top(e: G.Expr, +line: U32, +globals: List<&2, List<&2, U32>>) -> Top:
  top.w(expr(e, line), globals)
