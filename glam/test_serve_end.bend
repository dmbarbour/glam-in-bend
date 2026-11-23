# A copy's serve ending on a net whose kernel counted an error
# (implementation-errors-stop; the CursorLaws plan's cursor-laws.stop):
# the run stops with a diagnostic, before the core reads either net
# again; the host's count or the source's, on the serve's path and the
# one net's. A refused insert or a descent out of fuel is such an error
# (corruption-reported-when-cheap), which no sample reaches.
import Base
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/knet.bend as KN
import ./core.bend as C

def fn() -> T.TNode:
  T.TN{R.KFn{}, V.PNone{}}

def ln(+a: U32, +p: U32, +b: U32, +q: U32) -> T.TLink:
  T.TL{T.TE{a, p}, T.TE{b, q}}

# a net of one function node, its body its variable
def one() -> P.H:
  KN.load(T.Tpl{[fn()], [ln(0, 1, 0, 2)], T.TE{0, 0}, 1})

def outcome(r: C.Run) -> String:
  match r:
    case C.RDone{o}:
      match o:
        case C.OErrs{ds}:
          "stopped"
        case _:
          "done"
    case C.RMore{m}:
      "went on"

# a host the run would go on with: its words as a walk's path, never read
# when the run stops
def host(h: P.H) -> C.Hb:
  match h:
    case P.H{w, a}:
      C.HbTk{w, 0, 0, 0, 0, 0, 0, C.LoNil{}}

def counts() -> C.Cn:
  C.Cn{0, 0, 0, 0, 0, 0, 0, 0}

def serve_end(h: P.H, s: P.H) -> String:
  outcome(C.frame.ok(P.stats(h), P.stats(s), host(one()), 0, C.SrsNil{}, [], counts()))

def check.k(+same: Bool, got: String, want: String, name: String) -> String:
  match same:
    case True{}:
      ""
    case False{}:
      name ++ ": got " ++ got ++ ", want " ++ want ++ "\n"

def check(+got: String, +want: String, name: String) -> String:
  check.k(String.eq(got, want), got, want, name)

def report.k(+none: Bool, s: String) -> String:
  match none:
    case True{}:
      "ok"
    case False{}:
      s

def report(+s: String) -> String:
  report.k(String.eq(s, ""), s)

def main() -> String:
  report(
    check(serve_end(P.err_if(True{}, one()), one()), "stopped", "the host's error") ++
    check(serve_end(one(), P.err_if(True{}, one())), "stopped", "the source's error"))
