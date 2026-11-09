import Base
import ../spike/val.bend as V
import ../spike/kernel.bend as K
import ../spike/knet.bend as KN
import ../spike/kstrat.bend as KS
import ../spike/kdemand.bend as KD
import ./lex.bend as L
import ./parse.bend as G
import ./desugar.bend as D
import ./lower.bend as W

# The core (pure-core-io-shell): a source's bytes to the assembly's
# result, bytes, or its diagnostics; it never prints. As far as the hello
# ladder has climbed (HelloLadder): the module parsed, its `asm.result`
# lowered to a net, the net reduced on demand by the kernel's plain
# demand, its value read back as bytes.
#
# Evaluation runs in slices, `step(fuel, Core) -> Done | More` as the
# Architecture sketch has it: each slice a fuel of demand's steps, a slice
# that runs out (demand's state 4) set going again (state 0) by the next,
# the walk resuming where it stopped. Bend requires every loop to end, so
# the shell counts down a budget of slices too large for any assembly to
# reach (glam/main.bend); no @unsafe is needed.

type Out is Data:
  OBytes{bs: List<&2, U32>, +itrs: U32}
  OErrs{ds: List<&2, G.Diag>}

# where an assembly stands: done, or a demand to go on with
type Run is Type:
  RDone{o: Out}
  RMore{d: KD.D}

def find.k(+hit: Bool, d: G.Def) -> Maybe<&2, G.Def>:
  match hit:
    case True{}:
      Some{d}
    case False{}:
      None{}

# asm.result among the definitions, walked with what was found so far
def find(ds: List<&2, G.Def>, found: Maybe<&2, G.Def>) -> Maybe<&2, G.Def>:
  match ds:
    case Nil{}:
      found
    case Con{d, rest}:
      match d:
        case G.Def{+line, +path, body}:
          match found:
            case Some{e}:
              Some{e}
            case None{}:
              find(rest, find.k(G.path_eq(path, [[97, 115, 109], [114, 101, 115, 117, 108, 116]]), G.Def{line, path, body}))

# a list's values as bytes: every one a number below 256
type Bs is Data:
  BOk{bs: List<&2, U32>}
  BNo{}

def bytes.k(+ok: Bool, +b: U32, r: Bs) -> Bs:
  match ok r:
    case True{} BOk{bs}:
      BOk{Con{b, bs}}
    case _ _:
      BNo{}

def bytes(xs: List<&2, V.Val>) -> Bs:
  match xs:
    case Nil{}:
      BOk{Nil{}}
    case Con{v, rest}:
      match v:
        case V.VNum{+b}:
          bytes.k(U32.is_lt(b, 256), b, bytes(rest))
        case _:
          BNo{}

def out.bs(r: Bs, +itrs: U32) -> Out:
  match r:
    case BOk{bs}:
      OBytes{bs, itrs}
    case BNo{}:
      OErrs{[G.Diag{0, "asm.result is not a binary: an element is not a byte"}]}

def text.k(r: Bs) -> String:
  match r:
    case BOk{bs}:
      G.str(bs)
    case BNo{}:
      "an error whose diagnostic is no text"

# an error's diagnostic, a text for now (net-error-values)
def diagnostic(e: V.Val) -> String:
  match e:
    case V.VList{xs}:
      text.k(bytes(xs))
    case _:
      "an error whose diagnostic is no text"

def out.val(v: Maybe<&2, V.Val>, +itrs: U32) -> Out:
  match v:
    case Some{x}:
      match x:
        case V.VList{xs}:
          out.bs(bytes(xs), itrs)
        case V.VErr{e}:
          OErrs{[G.Diag{0, diagnostic(e)}]}
        case V.VUnit{}:
          OErrs{[G.Diag{0, "asm.result is unit, which is no binary"}]}
        case _:
          OErrs{[G.Diag{0, "asm.result is not a binary"}]}
    case None{}:
      OErrs{[G.Diag{0, "asm.result has no value"}]}

def out.errs.k(+none: Bool, +errs: U32, v: Maybe<&2, V.Val>, +itrs: U32) -> Out:
  match none:
    case True{}:
      out.val(v, itrs)
    case False{}:
      OErrs{[G.Diag{0, "the kernel reported " ++ U32.show(errs) ++ " errors"}]}

def out.errs(+errs: U32, v: Maybe<&2, V.Val>, +itrs: U32) -> Out:
  out.errs.k(U32.is_eq(errs, 0), errs, v, itrs)

# demand's end: done, or an outcome or a limit named (kernel.bend's states)
def out.st(+st: U32, k: K.KRes) -> Out:
  match st:
    case 1:
      match k:
        case K.KRes{v, +itrs, +errs, +ok}:
          out.errs(errs, v, itrs)
    case _:
      OErrs{[G.Diag{0, "evaluating asm.result: " ++ K.st_name(st)}]}

def out(r: K.DRes) -> Out:
  match r:
    case K.DRes{k, +st, +lz, +live, +cap, +reach}:
      out.st(st, k)

# Slices
# ======

# the fuel of one slice: demand's steps
def slice() -> Nat:
  1048576n

# a slice's end: out of fuel goes on (state 4 set going again, 0); any
# other state ends the assembly
def sliced(d: KD.D) -> Run:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      match st:
        case 4:
          RMore{KD.D{h, path, top, depth, n, 0}}
        case _:
          RDone{out(K.dres(KD.D{h, path, top, depth, n, st}))}

# one slice of the assembly
def step(d: KD.D) -> Run:
  sliced(KD.Demand.demand(slice(), d))

# Starting
# ========

def lowered(w: W.Top) -> Run:
  match w:
    case W.TOk{t}:
      RMore{KS.d.start(KN.load(t))}
    case W.TErr{d}:
      RDone{OErrs{[d]}}

def run(m: Maybe<&2, G.Def>) -> Run:
  match m:
    case Some{d}:
      match d:
        case G.Def{+line, path, body}:
          lowered(W.top(body, line))
    case None{}:
      RDone{OErrs{[G.Diag{0, "asm.result is not defined"}]}}

# the module's top-level names: each definition's path's first name
def globals(ds: List<&2, G.Def>) -> List<&2, List<&2, U32>>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, rest}:
      match d:
        case G.Def{+line, path, body}:
          match path:
            case Con{n, more}:
              Con{n, globals(rest)}
            case Nil{}:
              globals(rest)

# every definition desugared, so that each one's errors are reported
# whether asm.result needs it or not: the desugared, and the errors, each
# reversed
type Dd is Data:
  Dd{ds: List<&2, G.Def>, es: List<&2, G.Diag>}

def dput(r: D.Ds, +line: U32, path: List<&2, List<&2, U32>>, a: Dd) -> Dd:
  match r a:
    case D.DOk{e} Dd{ds, es}:
      Dd{Con{G.Def{line, path, e}, ds}, es}
    case D.DErr{d} Dd{ds, es}:
      Dd{ds, Con{d, es}}

def dall(defs: List<&2, G.Def>, +globals: List<&2, List<&2, U32>>, a: Dd) -> Dd:
  match defs:
    case Nil{}:
      a
    case Con{d, rest}:
      match d:
        case G.Def{+line, path, body}:
          dall(rest, globals, dput(D.expr(body, Nil{}, globals), line, path, a))

def start.d(a: Dd) -> Run:
  match a:
    case Dd{ds, es}:
      match es:
        case Nil{}:
          run(find(List.reverse(&2, G.Def, ds), None{}))
        case Con{e, rest}:
          RDone{OErrs{List.reverse(&2, G.Diag, Con{e, rest})}}

def start.p(p: G.Parsed) -> Run:
  match p:
    case G.PErr{ds}:
      RDone{OErrs{ds}}
    case G.POk{m}:
      match m:
        case G.Mod{+utf8, +defs}:
          start.d(dall(defs, globals(defs), Dd{Nil{}, Nil{}}))

# a ".g" source's bytes to its assembly, begun: parsed and lowered, its
# evaluation not yet stepped
def start(bs: List<&2, U32>) -> Run:
  start.p(G.parse(L.lex(bs)))
