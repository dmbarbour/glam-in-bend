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

# the bytes, with the interactions of every net reduced, the splices, and
# the values forced (for --count); or the diagnostics
type Out is Data:
  OBytes{bs: List<&2, U32>, +itrs: U32, +splices: U32, +forced: U32}
  OErrs{ds: List<&2, G.Diag>}

# An entry of the book (Cells, re-scoped by the bridge), named by a
# leaf's handle: a top-level function's template; or a root cell, a value
# a template names: its recipe not yet forced, forced now (busy, the
# recipe kept), its value, or a function, its recipe spliced at each use
# as a template is (a stopgap until `cells-freeze`: the work of its first
# forcing is not kept)
type Ent is Data:
  ETpl{t: T.Tpl}
  ERecipe{t: T.Tpl, name: List<&2, U32>}
  EBusy{t: T.Tpl, name: List<&2, U32>}
  EValue{v: V.Val}
  EFn{t: T.Tpl}

# A task, the protocol's state: a demand, the entry it computes (none,
# no_cell, for asm.result's net) and the entry it waits on
type Tk is Type:
  Tk{d: KD.D, +cell: U32, +waits: U32}

# the tasks set aside, each waiting on the one above it: one stack,
# forcing depth first, the first container of tasks
type Stk is Type:
  TkNil{}
  TkCon{t: Tk, rest: Stk}

# counted for --count: interactions of the cells' nets, splices, values
# forced
type Cn is Data:
  Cn{+itrs: U32, +splices: U32, +forced: U32}

# where an assembly stands: done, or a task to go on with, the tasks
# waiting, the book and the counts
type Run is Type:
  RDone{o: Out}
  RMore{t: Tk, s: Stk, b: List<&2, Ent>, c: Cn}

def no_cell() -> U32:
  4294967295

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
      OBytes{bs, itrs, 0, 0}
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

def cn.add(c: Cn, +i: U32) -> Cn:
  match c:
    case Cn{+itrs, +sp, +fo}:
      Cn{(itrs + i : U32), sp, fo}

def cn.splice(c: Cn) -> Cn:
  match c:
    case Cn{+itrs, +sp, +fo}:
      Cn{itrs, (sp + 1 : U32), fo}

def cn.force(c: Cn) -> Cn:
  match c:
    case Cn{+itrs, +sp, +fo}:
      Cn{itrs, sp, (fo + 1 : U32)}

# the counts added to the bytes' own
def counted(o: Out, c: Cn) -> Out:
  match o:
    case OBytes{bs, +itrs, +sp, +fo}:
      match c:
        case Cn{+i, +s2, +f2}:
          OBytes{bs, (itrs + i : U32), s2, f2}
    case OErrs{ds}:
      OErrs{ds}

def book_get(b: List<&2, Ent>, +k: U32) -> Maybe<&2, Ent>:
  match b:
    case Nil{}:
      None{}
    case Con{e, rest}:
      match k:
        case 0:
          Some{e}
        case _:
          book_get(rest, (k - 1 : U32))

def book_set(b: List<&2, Ent>, +k: U32, e: Ent) -> List<&2, Ent>:
  match b:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      match k:
        case 0:
          Con{e, rest}
        case _:
          Con{x, book_set(rest, (k - 1 : U32), e)}

# Aliases: a cell whose value is a handle stands for that handle's entry,
# chased at most as many hops as there are entries, past which the
# aliases go round

type Ch is Data:
  ChAt{+k: U32}
  ChLoop{}

def alias_of.v(v: V.Val) -> Maybe<&2, U32>:
  match v:
    case V.VLazy{+h}:
      Some{h}
    case _:
      None{}

def alias_of(m: Maybe<&2, Ent>) -> Maybe<&2, U32>:
  match m:
    case Some{e}:
      match e:
        case EValue{v}:
          alias_of.v(v)
        case _:
          None{}
    case None{}:
      None{}

def chase.k(m: Maybe<&2, U32>, +k: U32, more: U32 -> Ch) -> Ch:
  match m:
    case Some{+h}:
      more(h)
    case None{}:
      ChAt{k}

def chase(hops: Nat, +b: List<&2, Ent>, +k: U32) -> Ch:
  match hops:
    case 0n:
      ChLoop{}
    case 1n+p:
      chase.k(alias_of(book_get(b, k)), k, h => chase(p, b, h))

def go(d: KD.D, +cell: U32, s: Stk, b: List<&2, Ent>, c: Cn) -> Run:
  RMore{Tk{d, cell, no_cell()}, s, b, c}

def err(msg: String) -> Run:
  RDone{OErrs{[G.Diag{0, msg}]}}

# a need served by entry k: a template spliced, a value resumed, a recipe
# forced on a task of its own above this one, a busy cell a cycle
def needed.e(m: Maybe<&2, Ent>, d: KD.D, +k: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn) -> Run:
  match m:
    case Some{e}:
      match e:
        case ETpl{t}:
          go(S.splice(d, t), cell, s, b, cn.splice(c))
        case EFn{t}:
          go(S.splice(d, t), cell, s, b, cn.splice(c))
        case EValue{v}:
          go(KS.resume(d, v), cell, s, b, c)
        case ERecipe{+t, +name}:
          RMore{Tk{KS.d.start(KN.load(t)), k, no_cell()}, TkCon{Tk{d, cell, k}, s}, book_set(b, k, EBusy{t, name}), cn.force(c)}
        case EBusy{t, name}:
          err("`" ++ G.str(name) ++ "` needs its own value: a cycle")
    case None{}:
      err("a leaf names no definition")

def needed.c(ch: Ch, d: KD.D, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn) -> Run:
  match ch:
    case ChAt{+k}:
      needed.e(book_get(b, k), d, k, cell, s, b, c)
    case ChLoop{}:
      err("definitions name each other alone, with no value: a cycle")

# demand stopped at a leaf (state 2)
def needed(r: KD.D & U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn) -> Run:
  (d, +k) = r
  needed.c(chase(List.length(&2, Ent, b), b, k), d, cell, s, b, c)

# A cell's net done (state 1): its outcome kept, the task below it served:
# a value resumed there; no value, a function, its recipe spliced there
# and at each use after

def finished.fn(m: Maybe<&2, Ent>, d0: KD.D, +cell0: U32, rest: Stk, +cell: U32, +b: List<&2, Ent>, c: Cn) -> Run:
  match m:
    case Some{e}:
      match e:
        case EBusy{+t, name}:
          go(S.splice(d0, t), cell0, rest, book_set(b, cell, EFn{t}), cn.splice(c))
        case _:
          err("a value forced was not busy")
    case None{}:
      err("a value forced names no definition")

def finished.v(v: Maybe<&2, V.Val>, d0: KD.D, +cell0: U32, rest: Stk, +cell: U32, +b: List<&2, Ent>, c: Cn) -> Run:
  match v:
    case Some{+x}:
      go(KS.resume(d0, x), cell0, rest, book_set(b, cell, EValue{x}), c)
    case None{}:
      finished.fn(book_get(b, cell), d0, cell0, rest, cell, b, c)

def finished.s(s: Stk, v: Maybe<&2, V.Val>, +cell: U32, +b: List<&2, Ent>, c: Cn) -> Run:
  match s:
    case TkCon{t, rest}:
      match t:
        case Tk{d0, +cell0, +waits0}:
          finished.v(v, d0, cell0, rest, cell, b, c)
    case TkNil{}:
      err("a value forced for no one")

def finished.e(+clean: Bool, v: Maybe<&2, V.Val>, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn) -> Run:
  match clean:
    case True{}:
      finished.s(s, v, cell, b, c)
    case False{}:
      err("the kernel reported errors forcing a value")

def finished(r: K.DRes, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn) -> Run:
  match r:
    case K.DRes{k, +st, +lz, +live, +cap, +reach}:
      match k:
        case K.KRes{v, +itrs, +errs, +ok}:
          finished.e(U32.is_eq(errs, 0), v, cell, s, b, cn.add(c, itrs))

def ended.cell(d: KD.D, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn) -> Run:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      match st:
        case 1:
          finished(K.dres(KD.D{h, path, top, depth, n, st}), cell, s, b, c)
        case _:
          err("forcing a value: " ++ K.st_name(st))

def ended.rm(m: Maybe<&2, U32>, d: KD.D, s: Stk, +b: List<&2, Ent>, c: Cn) -> Run:
  match m:
    case Some{+k}:
      needed.c(chase(List.length(&2, Ent, b), b, k), d, no_cell(), s, b, c)
    case None{}:
      RDone{counted(out(K.dres(d)), c)}

# asm.result's net done: its output, unless its root faces a leaf, as when
# a function returns a value's leaf, which is served as a need is and the
# net then finished again
def ended.root(r: KD.D & Maybe<&2, U32>, s: Stk, +b: List<&2, Ent>, c: Cn) -> Run:
  (d, m) = r
  ended.rm(m, d, s, b, c)

# asm.result's demand ended: done, looked at for a leaf; else its outcome
def ended.r(d: KD.D, s: Stk, +b: List<&2, Ent>, c: Cn) -> Run:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      match st:
        case 1:
          ended.root(S.lazy_at(KD.D{h, path, top, depth, n, st}), s, b, c)
        case _:
          RDone{counted(out(K.dres(KD.D{h, path, top, depth, n, st})), c)}

# demand's end: asm.result's, its output; a cell's, served below
def ended(+root: Bool, d: KD.D, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn) -> Run:
  match root:
    case True{}:
      ended.r(d, s, b, c)
    case False{}:
      ended.cell(d, cell, s, b, c)

# a slice's end: out of fuel goes on (state 4 set going again, 0); a leaf
# met is served (state 2); any other state ends the task
def sliced(d: KD.D, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn) -> Run:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      match st:
        case 4:
          go(KD.D{h, path, top, depth, n, 0}, cell, s, b, c)
        case 2:
          needed(KS.need(KD.D{h, path, top, depth, n, st}), cell, s, b, c)
        case _:
          ended(U32.is_eq(cell, no_cell()), KD.D{h, path, top, depth, n, st}, cell, s, b, c)

# one slice of the assembly: of the task on top
def step(t: Tk, s: Stk, b: List<&2, Ent>, c: Cn) -> Run:
  match t:
    case Tk{d, +cell, +waits}:
      sliced(KD.Demand.demand(slice(), d), cell, s, b, c)

# Starting
# ========

def lowered(w: W.Top, b: List<&2, Ent>) -> Run:
  match w:
    case W.TOk{t}:
      go(KS.d.start(KN.load(t)), no_cell(), TkNil{}, b, Cn{0, 0, 0})
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

def unover(e: G.Expr) -> G.Expr:
  match e:
    case G.EOver{x}:
      x
    case _:
      e

def reover.k(r: D.Ds) -> D.Ds:
  match r:
    case D.DOk{e}:
      D.DOk{G.EOver{e}}
    case D.DErr{d}:
      D.DErr{d}

# an override's body desugared, its mark kept for the versions (vers)
def reover(+ov: Bool, r: D.Ds) -> D.Ds:
  match ov:
    case True{}:
      reover.k(r)
    case False{}:
      r

def dall(defs: List<&2, G.Def>, +globals: List<&2, List<&2, U32>>, a: Dd) -> Dd:
  match defs:
    case Nil{}:
      a
    case Con{d, rest}:
      match d:
        case G.Def{+line, path, +body}:
          dall(rest, globals, dput(reover(G.is_over(body), D.expr(unover(body), Nil{}, globals)), line, path, a))

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

def linked(r: D.Ds, +line: U32, rs: List<&2, W.Ref>, b: List<&2, Ent>) -> Run:
  match r:
    case D.DOk{e}:
      lowered(W.top_g(e, line, rs, Nil{}), b)
    case D.DErr{d}:
      RDone{OErrs{[d]}}

# asm.result's net: the value definitions bound around it, functions'
# names left to their templates
def link(m: Maybe<&2, G.Def>, +ds: List<&2, G.Def>, rs: List<&2, W.Ref>, b: List<&2, Ent>) -> Run:
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

# Root cells (Cells, re-scoped by the bridge): the values a template
# names, and those such values name in turn, each a cell of its own,
# forced at most once and resumed wherever named; every other value is
# linked around asm.result as before

def fname(path: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match path:
    case Con{n, rest}:
      n
    case Nil{}:
      Nil{}

def fvs(ds: List<&2, G.Def>) -> List<&2, List<&2, U32>>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, rest}:
      match d:
        case G.Def{+line, path, body}:
          List.append(&2, List<&2, U32>, D.fv(body), fvs(rest))

def among.k(+hit: Bool, n: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match hit:
    case True{}:
      Con{n, acc}
    case False{}:
      acc

# the names among ns that are in ks
def among(ns: List<&2, List<&2, U32>>, +ks: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+n, rest}:
      among.k(W.has_key(n, ks), n, among(rest, ks))

def pick.k(+hit: Bool, d: G.Def, r: Pt) -> Pt:
  match hit r:
    case True{} Pt{a, b}:
      Pt{Con{d, a}, b}
    case False{} Pt{a, b}:
      Pt{a, Con{d, b}}

# the definitions whose names are in ks, apart from the others, each
# reversed
def pick(ds: List<&2, G.Def>, +ks: List<&2, List<&2, U32>>, r: Pt) -> Pt:
  match ds:
    case Nil{}:
      r
    case Con{d, rest}:
      match d:
        case G.Def{+line, +path, +body}:
          pick(rest, ks, pick.k(W.has_key(fname(path), ks), G.Def{line, path, body}, r))

def picked(r: Pt) -> List<&2, G.Def>:
  match r:
    case Pt{a, b}:
      a

# the values' names reached from the templates: as many rounds as there
# are values
def cells.fix(k: Nat, +vs: List<&2, G.Def>, +vnames: List<&2, List<&2, U32>>, +named0: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match k:
    case 0n:
      acc
    case 1n+p:
      cells.fix(p, vs, vnames, named0, List.append(&2, List<&2, U32>, named0, among(fvs(picked(pick(vs, acc, Pt{Nil{}, Nil{}}))), vnames)))

def cell_names.n(+vs: List<&2, G.Def>, +vnames: List<&2, List<&2, U32>>, +named0: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  cells.fix(List.length(&2, G.Def, vs), vs, vnames, named0, named0)

def cell_names(fs: List<&2, G.Def>, +vs: List<&2, G.Def>) -> List<&2, List<&2, U32>>:
  cell_names.n(vs, globals(vs), among(fvs(fs), globals(vs)))

# The book: the templates, then the cells' recipes, in the order of their
# handles, or the first trouble lowering one

type Bk is Data:
  BkOk{es: List<&2, Ent>}
  BkErr{d: G.Diag}

def book.tk(w: W.Top, r: Bk) -> Bk:
  match w r:
    case W.TOk{t} BkOk{es}:
      BkOk{Con{ETpl{t}, es}}
    case W.TErr{d} _:
      BkErr{d}
    case W.TOk{t} BkErr{d}:
      BkErr{d}

def book.t(fs: List<&2, G.Def>, +rs: List<&2, W.Ref>, +vals: List<&2, List<&2, U32>>) -> Bk:
  match fs:
    case Nil{}:
      BkOk{Nil{}}
    case Con{d, rest}:
      match d:
        case G.Def{+line, path, body}:
          book.tk(W.top_g(body, line, rs, vals), book.t(rest, rs, vals))

def book.ck(w: W.Top, n: List<&2, U32>, r: Bk) -> Bk:
  match w r:
    case W.TOk{t} BkOk{es}:
      BkOk{Con{ERecipe{t, n}, es}}
    case W.TErr{d} _:
      BkErr{d}
    case W.TOk{t} BkErr{d}:
      BkErr{d}

def book.c(cs: List<&2, G.Def>, +rs: List<&2, W.Ref>, +vals: List<&2, List<&2, U32>>) -> Bk:
  match cs:
    case Nil{}:
      BkOk{Nil{}}
    case Con{d, rest}:
      match d:
        case G.Def{+line, path, body}:
          book.ck(W.top_g(body, line, rs, vals), fname(path), book.c(rest, rs, vals))

def bk.cat(a: Bk, b: Bk) -> Bk:
  match a b:
    case BkOk{x} BkOk{y}:
      BkOk{List.append(&2, Ent, x, y)}
    case BkErr{d} _:
      BkErr{d}
    case BkOk{x} BkErr{d}:
      BkErr{d}

def start.b(r: Bk, +ls: List<&2, G.Def>, rs: List<&2, W.Ref>) -> Run:
  match r:
    case BkOk{es}:
      link(find(ls, None{}), ls, rs, es)
    case BkErr{d}:
      RDone{OErrs{[d]}}

def start.rs(+rs: List<&2, W.Ref>, fs: List<&2, G.Def>, cs: List<&2, G.Def>, +ls: List<&2, G.Def>) -> Run:
  start.b(bk.cat(book.t(fs, rs, globals(ls)), book.c(cs, rs, globals(ls))), ls, rs)

# the handles: the templates' from 0, the cells' after them
def start.all(+fs: List<&2, G.Def>, +cs: List<&2, G.Def>, ls: List<&2, G.Def>) -> Run:
  start.rs(List.append(&2, W.Ref, refs(fs, 0), refs(cs, U32.from_nat(List.length(&2, G.Def, fs)))), fs, cs, ls)

def start.cs(r: Pt, fs: List<&2, G.Def>) -> Run:
  match r:
    case Pt{cs, ls}:
      start.all(fs, List.reverse(&2, G.Def, cs), List.reverse(&2, G.Def, ls))

def start.fv(+fs: List<&2, G.Def>, +vs: List<&2, G.Def>) -> Run:
  start.cs(pick(vs, cell_names(fs, vs), Pt{Nil{}, Nil{}}), fs)

def start.pt(r: Pt) -> Run:
  match r:
    case Pt{fs, vs}:
      start.fv(List.reverse(&2, G.Def, fs), List.reverse(&2, G.Def, vs))

# Versions (Syntax.md, Introductions and Overrides): a name defined again
# by `:=` is a chain of definitions in source order, each reading the one
# before it as `_name`. The last keeps the name; each earlier one is named
# `name'k`, k its place in the chain, a name no source can spell. A free
# `_m` in a definition reads m's latest version before it; with none, it
# is left to be reported undefined. The module resolves its priors so,
# statically; objects reach theirs through `_self` (`cells-objects`).

type VC is Data:
  VC{name: List<&2, U32>, +n: U32}

def vc.get.k(+hit: Bool, +n: U32, +more: U32) -> U32:
  match hit:
    case True{}:
      n
    case False{}:
      more

def vc.get(cs: List<&2, VC>, +x: List<&2, U32>) -> U32:
  match cs:
    case Nil{}:
      0
    case Con{c, rest}:
      match c:
        case VC{m, +n}:
          vc.get.k(G.bytes_eq(m, x), n, vc.get(rest, x))

def vc.inc.k(+hit: Bool, m: List<&2, U32>, +n: U32, rest: List<&2, VC>, more: List<&2, VC>) -> List<&2, VC>:
  match hit:
    case True{}:
      Con{VC{m, (n + 1 : U32)}, rest}
    case False{}:
      Con{VC{m, n}, more}

def vc.inc(cs: List<&2, VC>, +x: List<&2, U32>) -> List<&2, VC>:
  match cs:
    case Nil{}:
      [VC{x, 1}]
    case Con{c, +rest}:
      match c:
        case VC{+m, +n}:
          vc.inc.k(G.bytes_eq(m, x), m, n, rest, vc.inc(rest, x))

def vtot.p(m: Maybe<&2, List<&2, U32>>, acc: List<&2, VC>) -> List<&2, VC>:
  match m:
    case Some{n}:
      vc.inc(acc, n)
    case None{}:
      acc

# how many definitions each name has
def vtot(ds: List<&2, G.Def>, acc: List<&2, VC>) -> List<&2, VC>:
  match ds:
    case Nil{}:
      acc
    case Con{d, rest}:
      match d:
        case G.Def{+line, path, body}:
          vtot(rest, vtot.p(one_name(path), acc))

def decimal.if(more: Unit -> List<&2, U32>, +last: Bool, +k: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match last:
    case True{}:
      Con{(48 + k : U32), acc}
    case False{}:
      more(Unit{})

def decimal(f: Nat, +k: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  match f:
    case 0n:
      acc
    case 1n+p:
      decimal.if(u => decimal(p, (k / 10 : U32), Con{(48 + (k % 10 : U32) : U32), acc}), U32.is_lt(k, 10), k, acc)

def vname.k(+last: Bool, n: List<&2, U32>, +k: U32) -> List<&2, U32>:
  match last:
    case True{}:
      n
    case False{}:
      List.append(&2, U32, n, Con{39, decimal(10n, k, Nil{})})

# the name of version k of n, of tot
def vname(+n: List<&2, U32>, +k: U32, +tot: U32) -> List<&2, U32>:
  vname.k(U32.is_eq((k + 1 : U32), tot), n, k)

def under.k(+u: Bool, rest: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match u:
    case True{}:
      match rest:
        case Nil{}:
          None{}
        case Con{h, t}:
          Some{Con{h, t}}
    case False{}:
      None{}

# m, of a name `_m`
def under(x: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match x:
    case Con{+c, rest}:
      under.k(U32.is_eq(c, 95), rest)
    case Nil{}:
      None{}

def prior.k(+c: U32, m: List<&2, U32>, +tot: U32, x: List<&2, U32>) -> List<&2, U32>:
  match c:
    case 0:
      x
    case _:
      vname(m, (c - 1 : U32), tot)

def prior.m(mm: Maybe<&2, List<&2, U32>>, x: List<&2, U32>, +cur: List<&2, VC>, +tot: List<&2, VC>) -> List<&2, U32>:
  match mm:
    case Some{+m}:
      prior.k(vc.get(cur, m), m, vc.get(tot, m), x)
    case None{}:
      x

def rn.x(+b: Bool, +x: List<&2, U32>, +cur: List<&2, VC>, +tot: List<&2, VC>) -> List<&2, U32>:
  match b:
    case True{}:
      x
    case False{}:
      prior.m(under(x), x, cur, tot)

def rn.head(+bound: List<&2, List<&2, U32>>, path: List<&2, List<&2, U32>>, +cur: List<&2, VC>, +tot: List<&2, VC>) -> List<&2, List<&2, U32>>:
  match path:
    case Con{+x, rest}:
      Con{rn.x(W.has_key(x, bound), x, cur, tot), rest}
    case Nil{}:
      Nil{}

# each free `_m` renamed to m's version before this definition
def rn(+e: G.Expr, +bound: List<&2, List<&2, U32>>, +cur: List<&2, VC>, +tot: List<&2, VC>) -> G.Expr:
  match e:
    case G.EName{+l, path}:
      G.EName{l, rn.head(bound, path, cur, tot)}
    case G.EOp2{+l, op, a, b}:
      G.EOp2{l, op, rn(a, bound, cur, tot), rn(b, bound, cur, tot)}
    case G.ELet{+l, g}:
      G.ELet{l, rn(g, bound, cur, tot)}
    case G.EBind{+l, n, v, rest}:
      G.EBind{l, n, rn(v, bound, cur, tot), rn(rest, bound, cur, tot)}
    case G.EIn{b}:
      G.EIn{rn(b, bound, cur, tot)}
    case G.ELam{+l, +x, body}:
      G.ELam{l, x, rn(body, Con{x, bound}, cur, tot)}
    case G.EApp{+l, f, x}:
      G.EApp{l, rn(f, bound, cur, tot), rn(x, bound, cur, tot)}
    case G.EDict{+l, ms}:
      G.EDict{l, rn(ms, bound, cur, tot)}
    case G.EMem{m, rest}:
      G.EMem{rn(m, bound, cur, tot), rn(rest, bound, cur, tot)}
    case G.ETag{+l, k, v}:
      G.ETag{l, rn(k, bound, cur, tot), rn(v, bound, cur, tot)}
    case G.ESection{+l, k}:
      G.ESection{l, rn(k, bound, cur, tot)}
    case G.EIndex{+l, x, k}:
      G.EIndex{l, rn(x, bound, cur, tot), rn(k, bound, cur, tot)}
    case G.EOver{x}:
      G.EOver{rn(x, bound, cur, tot)}
    case _:
      e

type Vw is Data:
  Vw{ds: List<&2, G.Def>, cur: List<&2, VC>}

def vers.p(m: Maybe<&2, List<&2, U32>>, +line: U32, path: List<&2, List<&2, U32>>, body: G.Expr, +tot: List<&2, VC>, w: Vw) -> Vw:
  match m w:
    case Some{+n} Vw{ds, +cur}:
      Vw{Con{G.Def{line, [vname(n, vc.get(cur, n), vc.get(tot, n))], rn(unover(body), Nil{}, cur, tot)}, ds}, vc.inc(cur, n)}
    case None{} Vw{ds, +cur}:
      Vw{Con{G.Def{line, path, rn(unover(body), Nil{}, cur, tot)}, ds}, cur}

def vers.go(ds: List<&2, G.Def>, +tot: List<&2, VC>, w: Vw) -> Vw:
  match ds:
    case Nil{}:
      w
    case Con{d, rest}:
      match d:
        case G.Def{+line, +path, body}:
          vers.go(rest, tot, vers.p(one_name(path), line, path, body, tot, w))

def vers.out(w: Vw) -> List<&2, G.Def>:
  match w:
    case Vw{ds, cur}:
      List.reverse(&2, G.Def, ds)

def vers(+ds: List<&2, G.Def>) -> List<&2, G.Def>:
  vers.out(vers.go(ds, vtot(ds, Nil{}), Vw{Nil{}, Nil{}}))

def start.d(a: Dd, +lk: Bool) -> Run:
  match a:
    case Dd{+ds, es}:
      match es:
        case Nil{}:
          start.pt(part(vers(List.reverse(&2, G.Def, ds)), lk, Pt{Nil{}, Nil{}}))
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
