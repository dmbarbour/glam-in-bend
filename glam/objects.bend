import Base
import ../spike/val.bend as V
import ./parse.bend as G
import ./lower.bend as W

# Objects (Syntax.md, Objects; the Cells plan, `cells-objects`),
# instantiated at load where their bodies and parents are known. A
# member is lowered as Syntax.md desugars it: a template of two
# parameters, `self` the instance and `_self` the prior dict, the whole
# of it (the maintainer, 2026-11-10: a member's recipe may need it), a
# bare member name read from `self` and a prior `_k` from `_self`. Under
# `alias h` bare names are the host's, `h` is `self` and `_h` `_self`;
# an alias spelt `_h` is `h`, one name in two spellings. Each instance
# has a cell of its own for each member definition: its recipe applies
# the member's template to two constants, the instance's dict of member
# handles and the prior dict where the member's object stands, so that
# the template is shared and late binding comes free. The instance is
# itself a constant, its dict of member handles; `spec` is left out,
# nothing on the ladder reading it.

def self_name() -> List<&2, U32>:
  [115, 101, 108, 102]

def prior_name() -> List<&2, U32>:
  [95, 115, 101, 108, 102]

def field_of(+l: U32, k: List<&2, U32>, obj: List<&2, U32>) -> G.Expr:
  G.EApp{l, G.EField{l, k}, G.EName{l, [obj]}}

def uscore.k(+u: Bool, rest: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match u:
    case True{}:
      match rest:
        case Nil{}:
          None{}
        case Con{h, t}:
          Some{Con{h, t}}
    case False{}:
      None{}

# k, of a name `_k`
def uscore(x: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match x:
    case Con{+c, rest}:
      uscore.k(U32.is_eq(c, 95), rest)
    case Nil{}:
      None{}

# an alias in its plain spelling: `_h` is `h`
def plain.m(m: Maybe<&2, List<&2, U32>>, x: List<&2, U32>) -> List<&2, U32>:
  match m:
    case Some{k}:
      k
    case None{}:
      x

def plain(+x: List<&2, U32>) -> List<&2, U32>:
  plain.m(uscore(x), x)

# Rewriting a member's body
# =========================

def mrw.under(m: Maybe<&2, List<&2, U32>>, +l: U32, x: List<&2, U32>) -> G.Expr:
  match m:
    case Some{k}:
      field_of(l, k, prior_name())
    case None{}:
      field_of(l, x, self_name())

# a free name under the default alias: `self` and `_self` as they are, a
# prior `_k` _self's field, any other self's
def mrw.kw(+kw: Bool, +l: U32, +x: List<&2, U32>) -> G.Expr:
  match kw:
    case True{}:
      G.EName{l, [x]}
    case False{}:
      mrw.under(uscore(x), l, x)

def mrw.al.k(+me: Bool, +prior: Bool, +l: U32, x: List<&2, U32>) -> G.Expr:
  match me prior:
    case True{} _:
      G.EName{l, [self_name()]}
    case False{} True{}:
      G.EName{l, [prior_name()]}
    case False{} False{}:
      G.EName{l, [x]}

# a free name under `alias h`: h self, _h _self, any other the host's
def mrw.alias(+l: U32, +x: List<&2, U32>, +al: List<&2, U32>) -> G.Expr:
  mrw.al.k(G.bytes_eq(x, al), G.bytes_eq(x, Con{95, al}), l, x)

def mrw.mode(+al: List<&2, U32>, +l: U32, +x: List<&2, U32>) -> G.Expr:
  match al:
    case Nil{}:
      mrw.kw(G.bytes_eq(x, self_name()) || G.bytes_eq(x, prior_name()), l, x)
    case Con{a, rest}:
      mrw.alias(l, x, Con{a, rest})

def mrw.free(+b: Bool, +al: List<&2, U32>, +l: U32, +x: List<&2, U32>) -> G.Expr:
  match b:
    case True{}:
      G.EName{l, [x]}
    case False{}:
      mrw.mode(al, l, x)

def mrw.name(+bound: List<&2, List<&2, U32>>, +al: List<&2, U32>, +l: U32, path: List<&2, List<&2, U32>>) -> G.Expr:
  match path:
    case Con{+x, rest}:
      match rest:
        case Nil{}:
          mrw.free(W.has_key(x, bound), al, l, x)
        case Con{y, more}:
          G.EName{l, Con{x, Con{y, more}}}
    case Nil{}:
      G.EName{l, Nil{}}

# a member's desugared body, its free names as the alias has them
def mrw(+e: G.Expr, +bound: List<&2, List<&2, U32>>, +al: List<&2, U32>) -> G.Expr:
  match e:
    case G.EName{+l, path}:
      mrw.name(bound, al, l, path)
    case G.EOp2{+l, op, a, b}:
      G.EOp2{l, op, mrw(a, bound, al), mrw(b, bound, al)}
    case G.ELet{+l, g}:
      G.ELet{l, mrw(g, bound, al)}
    case G.EBind{+l, n, v, rest}:
      G.EBind{l, n, mrw(v, bound, al), mrw(rest, bound, al)}
    case G.EIn{b}:
      G.EIn{mrw(b, bound, al)}
    case G.ELam{+l, +x, body}:
      G.ELam{l, x, mrw(body, Con{x, bound}, al)}
    case G.EApp{+l, f, x}:
      G.EApp{l, mrw(f, bound, al), mrw(x, bound, al)}
    case G.EDict{+l, ms}:
      G.EDict{l, mrw(ms, bound, al)}
    case G.EMem{m, rest}:
      G.EMem{mrw(m, bound, al), mrw(rest, bound, al)}
    case G.ETag{+l, k, v}:
      G.ETag{l, mrw(k, bound, al), mrw(v, bound, al)}
    case G.ESection{+l, k}:
      G.ESection{l, mrw(k, bound, al)}
    case G.EIndex{+l, x, k}:
      G.EIndex{l, mrw(x, bound, al), mrw(k, bound, al)}
    case _:
      e

# a member's template: \self -> \_self -> its body rewritten
def mtpl(+line: U32, body: G.Expr, +al: List<&2, U32>) -> G.Expr:
  G.ELam{line, self_name(), G.ELam{line, prior_name(), mrw(body, Nil{}, plain(al))}}

# a member cell's recipe: its template applied to the instance's dict and
# the prior dict
def recipe(+line: U32, +tid: U32, inst: V.Val, prior: V.Val) -> G.Expr:
  G.EApp{line, G.EApp{line, G.EConst{V.VLazy{tid}}, G.EConst{inst}}, G.EConst{prior}}

# an entry of an instance's dict: a member's key, its cell's handle
def entry(name: List<&2, U32>, +cid: U32) -> V.Ent:
  V.Ent{W.atom(name), V.VLazy{cid}}
