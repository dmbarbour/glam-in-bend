import Base
import ../rules.bend as R

# Prints the rule table, a line per rewriting rule: the pair's kinds and
# test, the new nodes' kinds, the links (x i an Ext end, n j.p a new
# node's port), for spike/tools/switching.py.
#
#   bend spike/tools/rules_dump.bend

def kname(k: R.NodeKind) -> String:
  match k:
    case R.KFree{}:
      "KFree"
    case R.KFn{}:
      "KFn"
    case R.KAp{}:
      "KAp"
    case R.KCopy{}:
      "KCopy"
    case R.KMerge{}:
      "KMerge"
    case R.KData{}:
      "KData"
    case R.KEraN{}:
      "KEraN"
    case R.KEraP{}:
      "KEraP"
    case R.KRoot{}:
      "KRoot"
    case R.KCall{}:
      "KCall"
    case R.KLift{}:
      "KLift"
    case R.KLiftC{}:
      "KLiftC"

def kinds() -> List<&2, R.NodeKind>:
  [R.KFree{}, R.KFn{}, R.KAp{}, R.KCopy{}, R.KMerge{}, R.KData{}, R.KEraN{}, R.KEraP{}, R.KRoot{}, R.KCall{}, R.KLift{}, R.KLiftC{}]

def nshow(n: Nat) -> String:
  U32.show(U32.from_nat(n))

def eshow(e: R.End) -> String:
  match e:
    case R.Ext{i}:
      "x" ++ nshow(i)
    case R.New{j, p}:
      "n" ++ nshow(j) ++ "." ++ nshow(p)

def specs(xs: List<&2, R.Spec>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{R.Spec{k, s}, t}:
      kname(k) ++ " " ++ specs(t)

def lks(ls: List<&2, R.Link>) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{R.Link{x, y}, t}:
      eshow(x) ++ "-" ++ eshow(y) ++ " " ++ lks(t)

def rshow(+a: R.NodeKind, +b: R.NodeKind, +s: String, r: R.Rule) -> String:
  match r:
    case R.RWire{xs, ls}:
      kname(a) ++ " " ++ kname(b) ++ " " ++ s ++ " | " ++ specs(xs) ++ "| " ++ lks(ls) ++ "\n"
    case R.RStuck{}:
      ""

def over_b(+a: R.NodeKind, bs: List<&2, R.NodeKind>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, t}:
      rshow(a, b, "True", R.rule(a, b, True{})) ++ rshow(a, b, "False", R.rule(a, b, False{})) ++ over_b(a, t)

def over_a(as: List<&2, R.NodeKind>) -> String:
  match as:
    case Nil{}:
      ""
    case Con{+a, t}:
      over_b(a, kinds()) ++ over_a(t)

def main() -> IO(Unit):
  IO.print(over_a(kinds()))
