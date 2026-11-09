import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/nets.bend as X
import ./parse.bend as G

# Lowering (HelloLadder, ladder-text): a parsed expression to the net the
# kernel reduces, through the construction `interaction_net` gives every
# user, data nodes, binds, copies and wires, never a term of the core's
# (`lambdas-lower-to-nets`). A text is one data node holding the kernel's
# list of its code points (V.VList), the net's exposed port its
# principal.

def codes(bs: List<&2, U32>) -> List<&2, V.Val>:
  match bs:
    case Con{+b, rest}:
      Con{V.VNum{b}, codes(rest)}
    case Nil{}:
      Nil{}

def expr(e: G.Expr) -> T.Tpl:
  match e:
    case G.EText{s}:
      X.t_one(T.TN{R.KData{}, V.PVal{V.VList{codes(s)}}})
