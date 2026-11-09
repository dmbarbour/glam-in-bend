import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/nets.bend as X
import ./parse.bend as G

# Lowering (HelloLadder): a desugared expression (glam/desugar.bend) to
# the net the kernel reduces, through the construction `interaction_net`
# gives every user, data nodes, binds, copies and wires, never a term of
# the core's (`lambdas-lower-to-nets`). Every fan pairs by GAL levels
# (`lowering-uses-levels`), as spike/tools/terms.py lowers terms with
# levels (NetPairing, "Derivation"): an expression at depth n lowers a
# lambda to a function bind at n and an application to an application
# bind at n, its argument a box at n + 1; a variable's uses form a trie
# over the boxes entered from its binder, a copy fan at the depth where
# their paths split, and each edge from the binder or a fan to the next
# fan or use crosses one fused control, raising the levels above the
# edge's depth by the boxes entered, or lowering them by one where a use
# sits at its binder's depth (`fuse-control-runs`). A function whose
# variable is unused has no port for it (KFnD), and no eraser. Data, a
# text, a number, a list or a dict of literals, a builtin, a field's read
# with its key, is one data node, which no level concerns.
#
# Bend admits no mutual recursion, so one function, `expr`, walks the
# expression, and each result is a piece of net (Sub) numbered from 0:
# its nodes and links, its result port, and the uses of names it leaves
# pending, each a port waiting where the name is bound, with the depth
# and the boxes it sits in. A box is named by the position of the
# expression that opens it, unique in the tree.

type Root is Data:
  REnd{e: T.TEnd}
  # the result is a name's value, used at a depth within boxes
  RVar{+line: U32, name: List<&2, U32>, +depth: U32, boxes: List<&2, List<&2, U32>>}

# a port waiting for the value of a name
type Use is Data:
  Use{name: List<&2, U32>, +line: U32, at: T.TEnd, +depth: U32, boxes: List<&2, List<&2, U32>>}

type Sub is Data:
  Sub{nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +size: U32, root: Root, uses: List<&2, Use>}

type Lw is Data:
  LOk{s: Sub}
  LErr{d: G.Diag}

def codes(bs: List<&2, U32>) -> List<&2, V.Val>:
  match bs:
    case Con{+b, rest}:
      Con{V.VNum{b}, codes(rest)}
    case Nil{}:
      Nil{}

# a name as a dict key: its atom, `'name`, the dict of the text "name"
# to unit (Syntax.md, Atoms)
def atom(name: List<&2, U32>) -> V.Val:
  V.VDict{[V.Ent{V.VList{codes(name)}, V.VUnit{}}]}

def data(v: V.Val) -> Sub:
  Sub{[T.TN{R.KData{}, V.PVal{v}}], Nil{}, 1, REnd{T.TE{0, 0}}, Nil{}}

# Shifting a piece of net past n nodes
# ====================================

def sh_root(r: Root, +by: U32) -> Root:
  match r:
    case REnd{e}:
      REnd{X.sh_end(e, by)}
    case RVar{+l, n, +d, bx}:
      RVar{l, n, d, bx}

def sh_uses(us: List<&2, Use>, +by: U32) -> List<&2, Use>:
  match us:
    case Nil{}:
      Nil{}
    case Con{u, rest}:
      match u:
        case Use{n, +l, at, +d, bx}:
          Con{Use{n, l, X.sh_end(at, by), d, bx}, sh_uses(rest, by)}

# a port wired to a result: a link, or a use where the result is a name
type At is Data:
  At{ls: List<&2, T.TLink>, us: List<&2, Use>}

def attach(port: T.TEnd, r: Root) -> At:
  match r:
    case REnd{e}:
      At{[T.TL{port, e}], Nil{}}
    case RVar{+l, n, +d, bx}:
      At{Nil{}, [Use{n, l, port, d, bx}]}

# Applications
# ============

def app.at(a1: At, a2: At, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +k: U32, uses: List<&2, Use>) -> Sub:
  match a1 a2:
    case At{l1, u1} At{l2, u2}:
      Sub{nodes, List.append(&2, T.TLink, links, List.append(&2, T.TLink, l1, l2)), (k + 1 : U32), REnd{T.TE{k, 2}},
        List.append(&2, Use, uses, List.append(&2, Use, u1, u2))}

# f applied to x: the application bind at the depth, its principal on the
# function, its first auxiliary the argument, its second the result
def app.ab(+depth: U32, f: Sub, x: Sub) -> Sub:
  match f x:
    case Sub{fn, fl, +sf, fr, fu} Sub{xn, xl, +sx, xr, xu}:
      app.at(attach(T.TE{(sf + sx : U32), 0}, fr), attach(T.TE{(sf + sx : U32), 1}, sh_root(xr, sf)),
        List.append(&2, T.TNode, fn, List.append(&2, T.TNode, xn, [X.apl(depth)])),
        List.append(&2, T.TLink, fl, X.sh_links(xl, sf)), (sf + sx : U32), List.append(&2, Use, fu, sh_uses(xu, sf)))

def app(+depth: U32, f: Lw, x: Lw) -> Lw:
  match f x:
    case LOk{a} LOk{b}:
      LOk{app.ab(depth, a, b)}
    case LErr{d} _:
      LErr{d}
    case LOk{a} LErr{d}:
      LErr{d}

# A variable's uses: the trie and its fans
# ========================================

# the uses at a point of the trie, and the boxes entered from it
type Trie is Data:
  Trie{us: List<&2, T.TEnd>, ks: List<&2, Kid>}

type Kid is Data:
  Kid{box: List<&2, U32>, t: Trie}

def kids_put.if(more: (Trie -> Trie) -> List<&2, Kid>, +hit: Bool, kb: List<&2, U32>, kt: Trie, rest: List<&2, Kid>, f: Trie -> Trie) -> List<&2, Kid>:
  match hit:
    case True{}:
      Con{Kid{kb, f(kt)}, rest}
    case False{}:
      Con{Kid{kb, kt}, more(f)}

# f applied to the kid of box b, made empty where there is none
def kids_put(ks: List<&2, Kid>, +b: List<&2, U32>, f: Trie -> Trie) -> List<&2, Kid>:
  match ks:
    case Nil{}:
      [Kid{b, f(Trie{Nil{}, Nil{}})}]
    case Con{k, +rest}:
      match k:
        case Kid{+kb, kt}:
          kids_put.if(g => kids_put(rest, b, g), G.bytes_eq(kb, b), kb, kt, rest, f)

# a use at the end of the boxes rel, entered from the trie's point
def insert(rel: List<&2, List<&2, U32>>, t: Trie, +at: T.TEnd) -> Trie:
  match rel:
    case Nil{}:
      match t:
        case Trie{us, ks}:
          Trie{List.append(&2, T.TEnd, us, [at]), ks}
    case Con{b, rest}:
      match t:
        case Trie{us, ks}:
          Trie{us, kids_put(ks, b, s => insert(rest, s, at))}

# the uses' trie, their boxes past the binder's nb
def trie_of(us: List<&2, Use>, +nb: Nat, t: Trie) -> Trie:
  match us:
    case Nil{}:
      t
    case Con{u, rest}:
      match u:
        case Use{n, +l, at, +d, bx}:
          trie_of(rest, nb, insert(List.drop(&2, List<&2, U32>, bx, nb), t, at))

# where an edge goes: a use at a depth, or a fan of a trie's point
type Tgt is Data:
  TgUse{at: T.TEnd, +depth: U32}
  TgFan{t: Trie, +depth: U32}

# the next fan or use from a point at depth k, boxes holding one item
# skipped
def compress(t: Trie, +k: U32) -> Tgt:
  match t:
    case Trie{us, ks}:
      match us ks:
        case Con{u, Nil{}} Nil{}:
          TgUse{u, k}
        case Nil{} Con{Kid{b, kt}, Nil{}}:
          compress(kt, (k + 1 : U32))
        case _ _:
          TgFan{Trie{us, ks}, k}

def uses_t(us: List<&2, T.TEnd>, +d: U32) -> List<&2, Tgt>:
  match us:
    case Nil{}:
      Nil{}
    case Con{u, rest}:
      Con{TgUse{u, d}, uses_t(rest, d)}

def kids_t(ks: List<&2, Kid>, +d: U32) -> List<&2, Tgt>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{kid, rest}:
      match kid:
        case Kid{b, kt}:
          Con{compress(kt, d), kids_t(rest, d)}

# the nodes made so far, reversed, the links, the next node's index
type Em is Data:
  Em{nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +size: U32}

def em_size(em: Em) -> U32:
  match em:
    case Em{ns, ls, +k}:
      k

def em_link(em: Em, a: T.TEnd, b: T.TEnd) -> Em:
  match em:
    case Em{ns, ls, +k}:
      Em{ns, Con{T.TL{a, b}, ls}, k}

# an edge from src, one control on it where it moves levels: its principal
# on src, the edge going on from its auxiliary
type Eo is Data:
  Eo{em: Em, out: T.TEnd}

def edge.k(+none: Bool, em: Em, src: T.TEnd, +n: U32, +up: Bool, +by: U32) -> Eo:
  match none em:
    case True{} _:
      Eo{em, src}
    case False{} Em{ns, ls, +k}:
      Eo{Em{Con{X.ctl(n, up, by), ns}, Con{T.TL{src, T.TE{k, 0}}, ls}, (k + 1 : U32)}, T.TE{k, 1}}

def edge(em: Em, src: T.TEnd, +n: U32, +up: Bool, +by: U32) -> Eo:
  edge.k(U32.is_eq(by, 0), em, src, n, up, by)

def eo_link(r: Eo, at: T.TEnd) -> Em:
  match r:
    case Eo{em, out}:
      em_link(em, out, at)

# an edge from depth k to a use at depth d: the boxes entered, less the
# use's own croissant, d - k - 1 up, or one down where d = k
def use_edge.k(+same: Bool, em: Em, src: T.TEnd, +k: U32, +d: U32, at: T.TEnd) -> Em:
  match same:
    case True{}:
      eo_link(edge(em, src, k, False{}, 1), at)
    case False{}:
      eo_link(edge(em, src, k, True{}, ((d - k : U32) - 1 : U32)), at)

type Job is Data:
  Job{src: T.TEnd, +k: U32, tgt: Tgt}

# what is made, and the jobs left
type Fj is Data:
  Fj{em: Em, jobs: List<&2, Job>}

def cp_at(em: Em, +d: U32, src: T.TEnd) -> Em:
  match em:
    case Em{ns, ls, +k}:
      Em{Con{X.cpl(k, d), ns}, Con{T.TL{src, T.TE{k, 0}}, ls}, (k + 1 : U32)}

def fan_jobs.if(more: Unit -> Fj, +last: Bool, src: T.TEnd, +d: U32, it: Tgt, em: Em, jobs: List<&2, Job>) -> Fj:
  match last:
    case True{}:
      Fj{em, Con{Job{src, d, it}, jobs}}
    case False{}:
      more(Unit{})

# a fan's items at depth d from src: a copy fan at d for each but the
# last, its first auxiliary the item's edge, its second the chain's next
def fan_jobs(its: List<&2, Tgt>, +src: T.TEnd, +d: U32, +em: Em, +jobs: List<&2, Job>) -> Fj:
  match its:
    case Nil{}:
      Fj{em, jobs}
    case Con{+it, +rest}:
      fan_jobs.if(u => fan_jobs(rest, T.TE{em_size(em), 2}, d, cp_at(em, d, src), Con{Job{T.TE{em_size(em), 1}, d, it}, jobs}),
        List.is_empty(&2, Tgt, rest), src, d, it, em, jobs)

def eo_fan(r: Eo, t: Trie, +d: U32, jobs: List<&2, Job>) -> Fj:
  match r t:
    case Eo{em, out} Trie{us, ks}:
      fan_jobs(List.append(&2, Tgt, uses_t(us, d), kids_t(ks, (d + 1 : U32))), out, d, em, jobs)

def job(j: Job, rest: List<&2, Job>, em: Em) -> Fj:
  match j:
    case Job{src, +k, tgt}:
      match tgt:
        case TgUse{at, +d}:
          Fj{use_edge.k(U32.is_eq(d, k), em, src, k, d, at), rest}
        case TgFan{t, +d}:
          eo_fan(edge(em, src, k, True{}, (d - k : U32)), t, d, rest)

# every job done, one a step, under fuel enough for every item of every
# fan
def emit(n: Nat, st: Fj) -> Fj:
  match n:
    case 0n:
      st
    case 1n+p:
      match st:
        case Fj{em, jobs}:
          match jobs:
            case Nil{}:
              Fj{em, Nil{}}
            case Con{j, rest}:
              emit(p, job(j, rest, em))

# fuel for a variable's fans: each use and each box on its way, twice
def fuel(us: List<&2, Use>, acc: Nat) -> Nat:
  match us:
    case Nil{}:
      Nat.add(acc, 2n)
    case Con{u, rest}:
      match u:
        case Use{n, +l, at, +d, bx}:
          fuel(rest, Nat.add(acc, Nat.mul(2n, Nat.add(List.length(&2, List<&2, U32>, bx), 1n))))

# Lambdas
# =======

# the uses of x, and the others
type Sp is Data:
  Sp{xs: List<&2, Use>, others: List<&2, Use>}

def split.k(+hit: Bool, u: Use, r: Sp) -> Sp:
  match hit r:
    case True{} Sp{xs, others}:
      Sp{Con{u, xs}, others}
    case False{} Sp{xs, others}:
      Sp{xs, Con{u, others}}

def split(us: List<&2, Use>, +x: List<&2, U32>) -> Sp:
  match us:
    case Nil{}:
      Sp{Nil{}, Nil{}}
    case Con{u, rest}:
      match u:
        case Use{+n, +l, at, +d, bx}:
          split.k(G.bytes_eq(n, x), Use{n, l, at, d, bx}, split(rest, x))

def em_out(r: Fj) -> Em:
  match r:
    case Fj{em, jobs}:
      em

def lam.fans(em: Em, +depth: U32, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +k: U32, others: List<&2, Use>) -> Sub:
  match em:
    case Em{ns, ls, +size}:
      Sub{List.append(&2, T.TNode, nodes, Con{X.fnl(depth), List.reverse(&2, T.TNode, ns)}), List.append(&2, T.TLink, links, ls), size,
        REnd{T.TE{k, 0}}, others}

# the function: its variable's uses, if any, wired from its third port
def lam.sp(sp: Sp, +depth: U32, +nb: Nat, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, +k: U32) -> Sub:
  match sp:
    case Sp{xs, others}:
      match xs:
        case Nil{}:
          Sub{List.append(&2, T.TNode, nodes, [X.fndl(depth)]), links, (k + 1 : U32), REnd{T.TE{k, 0}}, others}
        case Con{+u, +more}:
          lam.fans(em_out(emit(fuel(Con{u, more}, 0n), Fj{Em{Nil{}, Nil{}, (k + 1 : U32)},
              [Job{T.TE{k, 2}, depth, compress(trie_of(Con{u, more}, nb, Trie{Nil{}, Nil{}}), depth)}]})),
            depth, nodes, links, k, others)

def lam.at(a: At, +depth: U32, +nb: Nat, x: List<&2, U32>, bn: List<&2, T.TNode>, bl: List<&2, T.TLink>, +bs: U32, bu: List<&2, Use>) -> Sub:
  match a:
    case At{al, au}:
      lam.sp(split(List.append(&2, Use, bu, au), x), depth, nb, bn, List.append(&2, T.TLink, bl, al), bs)

def lam.b(+depth: U32, +nb: Nat, x: List<&2, U32>, b: Sub) -> Sub:
  match b:
    case Sub{bn, bl, +bs, br, bu}:
      lam.at(attach(T.TE{bs, 1}, br), depth, nb, x, bn, bl, bs, bu)

def lam(+depth: U32, +nb: Nat, x: List<&2, U32>, b: Lw) -> Lw:
  match b:
    case LOk{s}:
      LOk{lam.b(depth, nb, x, s)}
    case LErr{d}:
      LErr{d}

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
        case G.EAtom{n}:
          cons_v(atom(n), consts(rest))
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

# Dicts of literals
# =================

def has_key(+k: List<&2, U32>, ks: List<&2, List<&2, U32>>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{m, rest}:
      G.bytes_eq(k, m) || has_key(k, rest)

# the entries of a constant dict literal, or the first trouble: a key
# introduced twice. Its members are tags of literals (glam/desugar.bend),
# keys values: a name's its atom.
type Dc is Data:
  DcOk{es: List<&2, V.Ent>}
  DcErr{d: G.Diag}

# a literal's value
def cval(r: Maybe<&2, List<&2, V.Val>>) -> V.Val:
  match r:
    case Some{vs}:
      match vs:
        case Con{v, rest}:
          v
        case Nil{}:
          V.VUnit{}
    case None{}:
      V.VUnit{}

# a text's values as bytes, for a message
def bytes_of(xs: List<&2, V.Val>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      match x:
        case V.VNum{+n}:
          Con{n, bytes_of(rest)}
        case _:
          Con{63, bytes_of(rest)}

def has_val(+k: V.Val, ks: List<&2, V.Val>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{m, rest}:
      V.veq(k, m) || has_val(k, rest)

def dent.add(+twice: Bool, +l: U32, k: V.Val, v: V.Val, more: Dc) -> Dc:
  match twice more:
    case True{} _:
      DcErr{G.Diag{l, "the key " ++ G.str(bytes_of(V.key_show(k))) ++ " is introduced twice in one dict"}}
    case False{} DcOk{es}:
      DcOk{Con{V.Ent{k, v}, es}}
    case False{} DcErr{d}:
      DcErr{d}

def dents(ms: G.Expr, +seen: List<&2, V.Val>) -> Dc:
  match ms:
    case G.EMem{m, rest}:
      match m:
        case G.ETag{+l, k, v}:
          +kv = cval(consts([k]))
          dent.add(has_val(kv, seen), l, kv, cval(consts([v])), dents(rest, Con{kv, seen}))
        case _:
          DcErr{G.Diag{0, "a dict member that is no tag of literals"}}
    case _:
      DcOk{Nil{}}

def dict(r: Dc) -> Lw:
  match r:
    case DcOk{es}:
      LOk{data(V.VDict{es})}
    case DcErr{d}:
      LErr{d}

def name(+line: U32, path: List<&2, List<&2, U32>>, +depth: U32, boxes: List<&2, List<&2, U32>>) -> Lw:
  match path:
    case Con{n, rest}:
      match rest:
        case Nil{}:
          LOk{Sub{Nil{}, Nil{}, 0, RVar{line, n, depth, boxes}, Nil{}}}
        case _:
          LErr{G.Diag{line, "a field of a name is not supported yet (ladder-lambda.dicts): " ++ G.path_str(Con{n, rest})}}
    case Nil{}:
      LErr{G.Diag{line, "an empty name"}}

# an expression lowered at a depth within boxes, at a position; the line
# its diagnostics name where it has none
def expr(e: G.Expr, +line: U32, +depth: U32, +pos: List<&2, U32>, +boxes: List<&2, List<&2, U32>>) -> Lw:
  match e:
    case G.EText{s}:
      LOk{data(V.VList{codes(s)})}
    case G.ENum{+n}:
      LOk{data(V.VNum{n})}
    case G.EList{xs}:
      list(consts(xs), line)
    case G.EBuiltin{+op, +need}:
      LOk{data(V.VFun{op, need, Nil{}})}
    case G.EDict{+l, ms}:
      dict(dents(ms, Nil{}))
    case G.ETag{+l, k, v}:
      dict(dents(G.EMem{G.ETag{l, k, v}, G.EMemEnd{}}, Nil{}))
    case G.EAtom{n}:
      LOk{data(atom(n))}
    case G.EField{+l, k}:
      LOk{data(V.VFun{5, 1, [atom(k)]})}
    case G.EName{+l, path}:
      name(l, path, depth, boxes)
    case G.EApp{+l, f, x}:
      app(depth, expr(f, l, depth, Con{1, pos}, boxes),
        expr(x, l, (depth + 1 : U32), Con{2, pos}, List.append(&2, List<&2, U32>, boxes, [Con{2, pos}])))
    case G.ELam{+l, n, body}:
      lam(depth, List.length(&2, List<&2, U32>, boxes), n, expr(body, l, depth, Con{1, pos}, boxes))
    case _:
      LErr{G.Diag{line, "this form is not lowered yet"}}

# The whole expression
# ====================
#
# The net of `asm.result`: its result a port, no name left pending, the
# module's definitions bound around it already (glam/core.bend), so that
# a name left is one nothing defines.

type Top is Data:
  TOk{t: T.Tpl}
  TErr{d: G.Diag}

def pending(n: List<&2, U32>, +l: U32) -> Top:
  TErr{G.Diag{l, "`" ++ G.str(n) ++ "` is not defined"}}

def top.e(us: List<&2, Use>, t: T.Tpl) -> Top:
  match us:
    case Con{u, rest}:
      match u:
        case Use{n, +l, at, +d, bx}:
          pending(n, l)
    case Nil{}:
      TOk{t}

def top.s(s: Sub) -> Top:
  match s:
    case Sub{nodes, links, +size, root, uses}:
      match root:
        case REnd{e}:
          top.e(uses, T.Tpl{nodes, links, e, size})
        case RVar{+l, n, +d, bx}:
          pending(n, l)

def top.w(w: Lw) -> Top:
  match w:
    case LOk{s}:
      top.s(s)
    case LErr{d}:
      TErr{d}

# a desugared expression to its net
def top(e: G.Expr, +line: U32) -> Top:
  top.w(expr(e, line, 0, Nil{}, Nil{}))

# Templates and their leaves
# ==========================
#
# A top-level function is a template (Cells, re-scoped by the bridge,
# `bridge-recursion`): its net lowered alone, closed. A name of a
# top-level function, there and in asm.result's net, is a leaf: a data
# node holding the function's handle, one for each use, which no level
# concerns. Demand meeting a leaf at an application splices a copy of the
# template there (glam/splice.bend); a function may so name itself.

type Ref is Data:
  Ref{name: List<&2, U32>, +id: U32}

def ref_of.if(more: Unit -> Maybe<&2, U32>, +hit: Bool, +id: U32) -> Maybe<&2, U32>:
  match hit:
    case True{}:
      Some{id}
    case False{}:
      more(Unit{})

# the handle of the function a name names, if one does
def ref_of(rs: List<&2, Ref>, +n: List<&2, U32>) -> Maybe<&2, U32>:
  match rs:
    case Nil{}:
      None{}
    case Con{r, rest}:
      match r:
        case Ref{m, +id}:
          ref_of.if(u => ref_of(rest, n), G.bytes_eq(m, n), id)

# a name no template answers: a value definition used inside a function
# needs a cell, not built yet; any other name is undefined
def unres(+val: Bool, n: List<&2, U32>, +l: U32) -> G.Diag:
  match val:
    case True{}:
      G.Diag{l, "`" ++ G.str(n) ++ "` is a value used inside a top-level function, which needs cells: not supported yet"}
    case False{}:
      G.Diag{l, "`" ++ G.str(n) ++ "` is not defined"}

def leaf(+id: U32) -> T.TNode:
  T.TN{R.KData{}, V.PVal{V.VLazy{id}}}

# the leaves made so far, reversed, their links, and the net's size
type Rs is Data:
  ROk{leaves: List<&2, T.TNode>, links: List<&2, T.TLink>, +size: U32}
  RErr{d: G.Diag}

def res.k(m: Maybe<&2, U32>, at: T.TEnd, n: List<&2, U32>, +l: U32, +val: Bool, r: Rs) -> Rs:
  match m r:
    case Some{+id} ROk{leaves, links, +size}:
      ROk{Con{leaf(id), leaves}, Con{T.TL{T.TE{size, 0}, at}, links}, (size + 1 : U32)}
    case None{} ROk{leaves, links, +size}:
      RErr{unres(val, n, l)}
    case _ RErr{d}:
      RErr{d}

# each use left pending, a leaf for the function it names
def res(us: List<&2, Use>, +rs: List<&2, Ref>, +vals: List<&2, List<&2, U32>>, r: Rs) -> Rs:
  match us:
    case Nil{}:
      r
    case Con{u, rest}:
      match u:
        case Use{+n, +l, at, +d, bx}:
          res(rest, rs, vals, res.k(ref_of(rs, n), at, n, l, has_key(n, vals), r))

def tg.done(r: Rs, nodes: List<&2, T.TNode>, links: List<&2, T.TLink>, e: T.TEnd) -> Top:
  match r:
    case ROk{leaves, ls, +size}:
      TOk{T.Tpl{List.append(&2, T.TNode, nodes, List.reverse(&2, T.TNode, leaves)), List.append(&2, T.TLink, links, ls), e, size}}
    case RErr{d}:
      TErr{d}

# a net that is a name alone: a leaf, if a function's
def tg.var(m: Maybe<&2, U32>, n: List<&2, U32>, +l: U32, +val: Bool) -> Top:
  match m:
    case Some{+id}:
      TOk{T.Tpl{[leaf(id)], Nil{}, T.TE{0, 0}, 1}}
    case None{}:
      TErr{unres(val, n, l)}

def tg.s(s: Sub, +rs: List<&2, Ref>, +vals: List<&2, List<&2, U32>>) -> Top:
  match s:
    case Sub{nodes, links, +size, root, uses}:
      match root:
        case REnd{e}:
          tg.done(res(uses, rs, vals, ROk{Nil{}, Nil{}, size}), nodes, links, e)
        case RVar{+l, +n, +d, bx}:
          tg.var(ref_of(rs, n), n, l, has_key(n, vals))

def tg.w(w: Lw, +rs: List<&2, Ref>, +vals: List<&2, List<&2, U32>>) -> Top:
  match w:
    case LOk{s}:
      tg.s(s, rs, vals)
    case LErr{d}:
      TErr{d}

# a desugared expression to its net, each name in rs answered by a leaf
# holding its handle; a name in vals, a value definition, reported as
# needing cells
def top_g(e: G.Expr, +line: U32, rs: List<&2, Ref>, vals: List<&2, List<&2, U32>>) -> Top:
  tg.w(expr(e, line, 0, Nil{}, Nil{}), rs, vals)
