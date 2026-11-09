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
# - a list whose members are not literals, and a name, wait for later
#   rungs (a list constructor; ladder-thunks for names).

type Lw is Data:
  LOk{t: T.Tpl}
  LErr{d: G.Diag}

def codes(bs: List<&2, U32>) -> List<&2, V.Val>:
  match bs:
    case Con{+b, rest}:
      Con{V.VNum{b}, codes(rest)}
    case Nil{}:
      Nil{}

def data(v: V.Val) -> T.Tpl:
  X.t_one(T.TN{R.KData{}, V.PVal{v}})

# glam's `++`: the builtin append, needing two lists
def append() -> T.Tpl:
  data(V.VFun{4, 2, Nil{}})

# a list literal's members as values, while every one is a literal
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

def op2(+line: U32, a: Lw, b: Lw) -> Lw:
  match a b:
    case LOk{x} LOk{y}:
      LOk{X.t_ap(X.t_ap(append(), x), y)}
    case LErr{d} _:
      LErr{d}
    case LOk{x} LErr{d}:
      LErr{d}

# the line an expression's diagnostics name, where it has one
def expr(e: G.Expr, +line: U32) -> Lw:
  match e:
    case G.EText{s}:
      LOk{data(V.VList{codes(s)})}
    case G.ENum{+n}:
      LOk{X.t_one(X.num(n))}
    case G.EList{xs}:
      list(consts(xs), line)
    case G.EName{+l, path}:
      LErr{G.Diag{l, "a reference to " ++ G.path_str(path) ++ " is not evaluated yet (ladder-thunks)"}}
    case G.EOp2{+l, op, a, b}:
      op2(l, expr(a, l), expr(b, l))
