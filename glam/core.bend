import Base
import ../spike/val.bend as V
import ../spike/kernel.bend as K
import ./lex.bend as L
import ./parse.bend as G
import ./lower.bend as W

# The core (pure-core-io-shell): a source's bytes to the assembly's
# result, bytes, or its diagnostics; it never prints. As far as the hello
# ladder has climbed (HelloLadder, ladder-text): the module parsed, its
# `asm.result` lowered to a net and reduced on demand by the kernel
# (K.run_d), the value read back as bytes.

type Out is Data:
  OBytes{bs: List<&2, U32>, +itrs: U32}
  OErrs{ds: List<&2, G.Diag>}

def find.k(+hit: Bool, body: G.Expr) -> Maybe<&2, G.Expr>:
  match hit:
    case True{}:
      Some{body}
    case False{}:
      None{}

# asm.result among the definitions, walked with what was found so far
def find(ds: List<&2, G.Def>, found: Maybe<&2, G.Expr>) -> Maybe<&2, G.Expr>:
  match ds:
    case Nil{}:
      found
    case Con{d, rest}:
      match d:
        case G.Def{+line, path, body}:
          match found:
            case Some{e}:
              Some{e}
            case None{}:
              find(rest, find.k(G.path_eq(path, [[97, 115, 109], [114, 101, 115, 117, 108, 116]]), body))

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

def out.val(v: Maybe<&2, V.Val>, +itrs: U32) -> Out:
  match v:
    case Some{x}:
      match x:
        case V.VList{xs}:
          out.bs(bytes(xs), itrs)
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

def fuel() -> Nat:
  1000000n

def run(e: Maybe<&2, G.Expr>) -> Out:
  match e:
    case Some{x}:
      out(K.run_d(W.expr(x), fuel(), Nil{}))
    case None{}:
      OErrs{[G.Diag{0, "asm.result is not defined"}]}

def assemble.p(p: G.Parsed) -> Out:
  match p:
    case G.PErr{ds}:
      OErrs{ds}
    case G.POk{m}:
      match m:
        case G.Mod{+utf8, defs}:
          run(find(defs, None{}))

# a ".g" source's bytes to its assembly
def assemble(bs: List<&2, U32>) -> Out:
  assemble.p(G.parse(L.lex(bs)))
