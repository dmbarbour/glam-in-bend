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
import ./splice.bend as S
import ../spike/tpl.bend as T

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

# where an assembly stands: done, or a demand to go on with, and the
# templates its leaves name, each top-level function's (W.top_g)
type Run is Type:
  RDone{o: Out}
  RMore{d: KD.D, b: List<&2, T.Tpl>}

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

# the template a leaf's handle names, if any
def book_at(b: List<&2, T.Tpl>, +k: U32) -> Maybe<&2, T.Tpl>:
  match b:
    case Nil{}:
      None{}
    case Con{t, rest}:
      match k:
        case 0:
          Some{t}
        case _:
          book_at(rest, (k - 1 : U32))

def spliced(m: Maybe<&2, T.Tpl>, d: KD.D, b: List<&2, T.Tpl>) -> Run:
  match m:
    case Some{t}:
      RMore{S.splice(d, t), b}
    case None{}:
      RDone{OErrs{[G.Diag{0, "a leaf names no template"}]}}

# demand stopped at a leaf (state 2): the template it names spliced there
def needed(r: KD.D & U32, +b: List<&2, T.Tpl>) -> Run:
  (d, +k) = r
  spliced(book_at(b, k), d, b)

# a slice's end: out of fuel goes on (state 4 set going again, 0); a leaf
# met is spliced (state 2); any other state ends the assembly
def sliced(d: KD.D, +b: List<&2, T.Tpl>) -> Run:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      match st:
        case 4:
          RMore{KD.D{h, path, top, depth, n, 0}, b}
        case 2:
          needed(KS.need(KD.D{h, path, top, depth, n, st}), b)
        case _:
          RDone{out(K.dres(KD.D{h, path, top, depth, n, st}))}

# one slice of the assembly
def step(d: KD.D, b: List<&2, T.Tpl>) -> Run:
  sliced(KD.Demand.demand(slice(), d), b)

# Starting
# ========

def lowered(w: W.Top, b: List<&2, T.Tpl>) -> Run:
  match w:
    case W.TOk{t}:
      RMore{KS.d.start(KN.load(t)), b}
    case W.TErr{d}:
      RDone{OErrs{[d]}}

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

# Linking (HelloLadder, ladder-thunks.globals): the module's top-level
# definitions of one name bound around asm.result as one binding group,
# as `asm.result = e where ...` would bind them: the live ones nested in
# the order of their needs, the rest dropped, a cycle refused
# (glam/desugar.bend). No cell yet: a definition is lowered into the net
# of every assembly that needs it. Definitions on a longer path, other
# than asm.result, wait for dicts built by paths.

def is_asm(p: List<&2, List<&2, U32>>) -> Bool:
  G.path_eq(p, [[97, 115, 109], [114, 101, 115, 117, 108, 116]])

def one_name(p: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match p:
    case Con{n, rest}:
      match rest:
        case Nil{}:
          Some{n}
        case _:
          None{}
    case Nil{}:
      None{}

def bind.k(m: Maybe<&2, List<&2, U32>>, +line: U32, body: G.Expr, acc: G.Expr) -> G.Expr:
  match m:
    case Some{n}:
      G.EBind{line, n, body, acc}
    case None{}:
      acc

# the definitions of one name as a chain of bindings ending in the body
def binds(ds: List<&2, G.Def>, body: G.Expr) -> G.Expr:
  match ds:
    case Nil{}:
      G.EIn{body}
    case Con{d, rest}:
      match d:
        case G.Def{+line, path, v}:
          bind.k(one_name(path), line, v, binds(rest, body))

def linked(r: D.Ds, +line: U32, rs: List<&2, W.Ref>, b: List<&2, T.Tpl>) -> Run:
  match r:
    case D.DOk{e}:
      lowered(W.top_g(e, line, rs, Nil{}), b)
    case D.DErr{d}:
      RDone{OErrs{[d]}}

# asm.result's net: the value definitions bound around it, functions'
# names left to their templates
def link(m: Maybe<&2, G.Def>, +ds: List<&2, G.Def>, rs: List<&2, W.Ref>, b: List<&2, T.Tpl>) -> Run:
  match m:
    case Some{d}:
      match d:
        case G.Def{+line, path, body}:
          linked(D.group(D.DOk{binds(ds, body)}), line, rs, b)
    case None{}:
      RDone{OErrs{[G.Diag{0, "asm.result is not defined"}]}}

# Templates (Cells, re-scoped by the bridge, `bridge-recursion`): a
# definition of one name whose body, desugared, is a lambda is a top-level
# function, lowered alone to a template; the others are values, linked
# around asm.result. With --link, every definition is a value, as before
# templates, for a differential run.

def fn_name.b(m: Maybe<&2, List<&2, U32>>, body: G.Expr) -> Maybe<&2, List<&2, U32>>:
  match body:
    case G.ELam{+l, x, b}:
      m
    case _:
      None{}

def fn_of(+lk: Bool, path: List<&2, List<&2, U32>>, body: G.Expr) -> Maybe<&2, List<&2, U32>>:
  match lk:
    case True{}:
      None{}
    case False{}:
      fn_name.b(one_name(path), body)

# the functions and the values, each reversed
type Pt is Data:
  Pt{fns: List<&2, G.Def>, vals: List<&2, G.Def>}

def part.k(m: Maybe<&2, List<&2, U32>>, d: G.Def, r: Pt) -> Pt:
  match m r:
    case Some{n} Pt{fs, vs}:
      Pt{Con{d, fs}, vs}
    case None{} Pt{fs, vs}:
      Pt{fs, Con{d, vs}}

def part(ds: List<&2, G.Def>, +lk: Bool, r: Pt) -> Pt:
  match ds:
    case Nil{}:
      r
    case Con{d, rest}:
      match d:
        case G.Def{+line, +path, +body}:
          part(rest, lk, part.k(fn_of(lk, path, body), G.Def{line, path, body}, r))

def refs.k(m: Maybe<&2, List<&2, U32>>, +i: U32, acc: List<&2, W.Ref>) -> List<&2, W.Ref>:
  match m:
    case Some{n}:
      Con{W.Ref{n, i}, acc}
    case None{}:
      acc

# each function's name and handle, its place among the functions
def refs(fs: List<&2, G.Def>, +i: U32) -> List<&2, W.Ref>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{d, rest}:
      match d:
        case G.Def{+line, path, body}:
          refs.k(one_name(path), i, refs(rest, (i + 1 : U32)))

# the templates, in the functions' order, or the first one's trouble
type Bk is Data:
  BkOk{ts: List<&2, T.Tpl>}
  BkErr{d: G.Diag}

def book.k(w: W.Top, r: Bk) -> Bk:
  match w r:
    case W.TOk{t} BkOk{ts}:
      BkOk{Con{t, ts}}
    case W.TErr{d} _:
      BkErr{d}
    case W.TOk{t} BkErr{d}:
      BkErr{d}

def book(fs: List<&2, G.Def>, +rs: List<&2, W.Ref>, +vals: List<&2, List<&2, U32>>) -> Bk:
  match fs:
    case Nil{}:
      BkOk{Nil{}}
    case Con{d, rest}:
      match d:
        case G.Def{+line, path, body}:
          book.k(W.top_g(body, line, rs, vals), book(rest, rs, vals))

def start.b(r: Bk, +vs: List<&2, G.Def>, rs: List<&2, W.Ref>) -> Run:
  match r:
    case BkOk{ts}:
      link(find(vs, None{}), vs, rs, ts)
    case BkErr{d}:
      RDone{OErrs{[d]}}

def start.rs(+rs: List<&2, W.Ref>, fs: List<&2, G.Def>, +vs: List<&2, G.Def>) -> Run:
  start.b(book(fs, rs, globals(vs)), vs, rs)

# Which functions are templates, until root cells hold the values a
# template names (the Cells plan, re-scoped): those that reach no value
# definition through the functions they name. A function that reaches one
# is linked around asm.result as before, so that nothing linked today
# stops working; recursion through it is refused as before.

def reaches(names: List<&2, List<&2, U32>>, +bad: List<&2, List<&2, U32>>) -> Bool:
  match names:
    case Nil{}:
      False{}
    case Con{n, rest}:
      W.has_key(n, bad) || reaches(rest, bad)

def bad.add(m: Maybe<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match m:
    case Some{n}:
      Con{n, acc}
    case None{}:
      acc

def bad.if(+hit: Bool, m: Maybe<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match hit:
    case True{}:
      bad.add(m, acc)
    case False{}:
      acc

# the values, and each function naming a value or a function in bad
def bad.once(fs: List<&2, G.Def>, +bad: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match fs:
    case Nil{}:
      acc
    case Con{d, rest}:
      match d:
        case G.Def{+line, path, body}:
          bad.once(rest, bad, bad.if(reaches(D.fv(body), bad), one_name(path), acc))

# the names that reach a value: as many rounds as there are functions
def bad.fix(k: Nat, +fs: List<&2, G.Def>, +vals: List<&2, List<&2, U32>>, bad: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match k:
    case 0n:
      bad
    case 1n+p:
      bad.fix(p, fs, vals, bad.once(fs, bad, vals))

def fname(path: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match path:
    case Con{n, rest}:
      n
    case Nil{}:
      Nil{}

def tsplit.k(+linked: Bool, d: G.Def, r: Pt) -> Pt:
  match linked r:
    case True{} Pt{fs, vs}:
      Pt{fs, Con{d, vs}}
    case False{} Pt{fs, vs}:
      Pt{Con{d, fs}, vs}

# the templates apart from the functions linked, each reversed
def tsplit(fs: List<&2, G.Def>, +bad: List<&2, List<&2, U32>>, r: Pt) -> Pt:
  match fs:
    case Nil{}:
      r
    case Con{d, rest}:
      match d:
        case G.Def{+line, +path, +body}:
          tsplit(rest, bad, tsplit.k(W.has_key(fname(path), bad), G.Def{line, path, body}, r))

def start.split(r: Pt, vs: List<&2, G.Def>) -> Run:
  match r:
    case Pt{+ts, ls}:
      start.rs(refs(List.reverse(&2, G.Def, ts), 0), List.reverse(&2, G.Def, ts), List.append(&2, G.Def, vs, List.reverse(&2, G.Def, ls)))

def start.fv(+fs: List<&2, G.Def>, +vs: List<&2, G.Def>) -> Run:
  start.split(tsplit(fs, bad.fix(List.length(&2, G.Def, fs), fs, globals(vs), globals(vs)), Pt{Nil{}, Nil{}}), vs)

def start.pt(r: Pt) -> Run:
  match r:
    case Pt{fs, vs}:
      start.fv(List.reverse(&2, G.Def, fs), List.reverse(&2, G.Def, vs))

def start.d(a: Dd, +lk: Bool) -> Run:
  match a:
    case Dd{+ds, es}:
      match es:
        case Nil{}:
          start.pt(part(List.reverse(&2, G.Def, ds), lk, Pt{Nil{}, Nil{}}))
        case Con{e, rest}:
          RDone{OErrs{List.reverse(&2, G.Diag, Con{e, rest})}}

def start.p(p: G.Parsed, +lk: Bool) -> Run:
  match p:
    case G.PErr{ds}:
      RDone{OErrs{ds}}
    case G.POk{m}:
      match m:
        case G.Mod{+utf8, +defs}:
          start.d(dall(defs, globals(defs), Dd{Nil{}, Nil{}}), lk)

# a ".g" source's bytes to its assembly, begun: parsed and lowered, its
# evaluation not yet stepped; lk links every definition statically
def start(bs: List<&2, U32>, +lk: Bool) -> Run:
  start.p(G.parse(L.lex(bs)), lk)
