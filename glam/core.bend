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
import ./objects.bend as O
import ../spike/tpl.bend as T
import ./freeze.bend as F
import ../spike/kprim.bend as P
import ./materialize.bend as M
import ../spike/kmem_grow.bend as KM

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

# the bytes, with the interactions of every net reduced, the splices, the
# values forced, the cursors served, and the walks a frame lost in its
# source with the steps they had descended (for --count); or the
# diagnostics
type Out is Data:
  OBytes{bs: List<&2, U32>, +itrs: U32, +splices: U32, +forced: U32, +serves: U32, +stops: U32, +rewalk: U32}
  OErrs{ds: List<&2, G.Diag>}

# An entry of the book (Cells, re-scoped by the bridge), named by a
# leaf's handle: a top-level function's template; or a root cell, a value
# a template names: its recipe not yet forced, forced now (busy, the
# recipe kept), its value, or a function. A function's net is kept live
# as a source (cells-freeze.cells; copy-reduced-function-nets), its place
# i among the sources, and each use materializes it; its recipe is kept
# for a need from inside another source, spliced there as a template is
# until sources hold copies of sources
type Ent is Data:
  ETpl{t: T.Tpl}
  ERecipe{t: T.Tpl, name: List<&2, U32>}
  EBusy{t: T.Tpl, name: List<&2, U32>}
  EValue{v: V.Val}
  ESrc{+i: U32, t: T.Tpl, name: List<&2, U32>}

# The live sources, a net each, linear as nets are: the book is copied
# freely and holds none. A frame takes its source out for a step and puts
# it back (SrcOut in its place meanwhile), so no heap is ever shared and
# written
type Src is Type:
  SrcIn{h: P.H}
  SrcOut{}

type Srcs is Type:
  SrsNil{}
  SrsCon{x: Src, rest: Srcs}

# A task, the protocol's state: a demand, the entry it computes (none,
# no_cell, for asm.result's net) and the entry it waits on; or a frame
# serving a negative cursor nc, at position pos of source k, in the net of
# the task below it (cells-freeze.cells), holding no net between steps;
# or such a frame going on with its walk in the source, which it holds
# from one step to the next, on top of the stack, so that nothing else
# runs between (cells-freeze.rewalk)
type Tk is Type:
  Tk{d: KD.D, +cell: U32, +waits: U32}
  TkSv{+k: U32, +nc: U32, +pos: U32}
  TkSvD{+k: U32, +nc: U32, +pos: U32, d: KD.D}

# the tasks set aside, each waiting on the one above it: one stack,
# forcing depth first, the first container of tasks
type Stk is Type:
  TkNil{}
  TkCon{t: Tk, rest: Stk}

# counted for --count: interactions of the cells' nets and the sources,
# splices, values forced, cursors served, and the frames' stops in their
# sources with the depth each walk had reached, which the frame's next
# step walks again (cells-freeze.rewalk)
type Cn is Data:
  Cn{+itrs: U32, +splices: U32, +forced: U32, +serves: U32, +stops: U32, +rewalk: U32}

# where an assembly stands: done, or a task to go on with, the tasks
# waiting, the book and the counts
type Run is Type:
  RDone{o: Out}
  RMore{t: Tk, s: Stk, b: List<&2, Ent>, c: Cn, ss: Srcs}

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
      OBytes{bs, itrs, 0, 0, 0, 0, 0}
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
    case Cn{+itrs, +sp, +fo, +sv, +st, +rw}:
      Cn{(itrs + i : U32), sp, fo, sv, st, rw}

def cn.splice(c: Cn) -> Cn:
  match c:
    case Cn{+itrs, +sp, +fo, +sv, +st, +rw}:
      Cn{itrs, (sp + 1 : U32), fo, sv, st, rw}

def cn.force(c: Cn) -> Cn:
  match c:
    case Cn{+itrs, +sp, +fo, +sv, +st, +rw}:
      Cn{itrs, sp, (fo + 1 : U32), sv, st, rw}

def cn.serve(c: Cn) -> Cn:
  match c:
    case Cn{+itrs, +sp, +fo, +sv, +st, +rw}:
      Cn{itrs, sp, fo, (sv + 1 : U32), st, rw}

# a frame's walk stopped in its source at depth d, to be walked again
def cn.stop(c: Cn, +d: U32) -> Cn:
  match c:
    case Cn{+itrs, +sp, +fo, +sv, +st, +rw}:
      Cn{itrs, sp, fo, sv, (st + 1 : U32), (rw + d : U32)}

# the counts added to the bytes' own
def counted(o: Out, c: Cn) -> Out:
  match o:
    case OBytes{bs, +itrs, +sp, +fo, +sv, +st, +rw}:
      match c:
        case Cn{+i, +s2, +f2, +v2, +t2, +r2}:
          OBytes{bs, (itrs + i : U32), s2, f2, v2, t2, r2}
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

def go(d: KD.D, +cell: U32, s: Stk, b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  RMore{Tk{d, cell, no_cell()}, s, b, c, ss}

def err(msg: String) -> Run:
  RDone{OErrs{[G.Diag{0, msg}]}}

# a demand's net
def dh(d: KD.D) -> P.H:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      h

# Sources
# =======

def srcs.push.r(x: Src, r: Srcs & U32) -> Srcs & U32:
  (rest, +i) = r
  (SrsCon{x, rest}, i)

# h put last among the sources, and its place, i the place of the first
def srcs.push(ss: Srcs, h: P.H, +i: U32) -> Srcs & U32:
  match ss:
    case SrsNil{}:
      (SrsCon{SrcIn{h}, SrsNil{}}, i)
    case SrsCon{x, rest}:
      srcs.push.r(x, srcs.push(rest, h, (i + 1 : U32)))

type SrT is Type:
  SrT{ss: Srcs, x: Src}

def srcs.take.r(x: Src, r: SrT) -> SrT:
  match r:
    case SrT{rest, y}:
      SrT{SrsCon{x, rest}, y}

# source i taken out, SrcOut left in its place
def srcs.take(ss: Srcs, +i: U32) -> SrT:
  match ss:
    case SrsNil{}:
      SrT{SrsNil{}, SrcOut{}}
    case SrsCon{x, rest}:
      match i:
        case 0:
          SrT{SrsCon{SrcOut{}, rest}, x}
        case _:
          srcs.take.r(x, srcs.take(rest, (i - 1 : U32)))

# h put back as source i
def srcs.put(ss: Srcs, +i: U32, h: P.H) -> Srcs:
  match ss:
    case SrsNil{}:
      SrsNil{}
    case SrsCon{x, rest}:
      match i:
        case 0:
          SrsCon{SrcIn{h}, rest}
        case _:
          SrsCon{x, srcs.put(rest, (i - 1 : U32), h)}

# Frames and their sources
# ========================
#
# A frame (TkSv) serves a negative cursor of the task below it from the
# cursor's source (cells-freeze.cells; glam/materialize.bend). Busy at a
# position: a frame waiting on a task above keeps no path, a walk walking
# again from its position, and no net, its source back among the
# sources; a serve of the same source at a position a frame waits on is a
# cycle.

type Bu is Type:
  Bu{s: Stk, +yes: Bool}

def busy.hit(t: Tk, +k: U32, +pos: U32) -> Tk & Bool:
  match t:
    case Tk{d, +cell, +w}:
      (Tk{d, cell, w}, False{})
    case TkSv{+k2, +nc2, +pos2}:
      (TkSv{k2, nc2, pos2}, U32.is_eq(k2, k) && U32.is_eq(pos2, pos))
    case TkSvD{+k2, +nc2, +pos2, d}:
      (TkSvD{k2, nc2, pos2, d}, U32.is_eq(k2, k) && U32.is_eq(pos2, pos))

def busy.r2(r: Tk & Bool, s: Stk, +y: Bool) -> Bu:
  (t, +x) = r
  Bu{TkCon{t, s}, x || y}

def busy.r(r: Tk & Bool, b: Bu) -> Bu:
  match b:
    case Bu{s, +y}:
      busy.r2(r, s, y)

# whether a frame on the stack serves source k at pos
def busy(s: Stk, +k: U32, +pos: U32) -> Bu:
  match s:
    case TkNil{}:
      Bu{TkNil{}, False{}}
    case TkCon{t, rest}:
      busy.r(busy.hit(t, k, pos), busy(rest, k, pos))

def src.name(m: Maybe<&2, Ent>) -> String:
  match m:
    case Some{e}:
      match e:
        case ESrc{+i, t, name}:
          G.str(name)
        case _:
          "a value"
    case None{}:
      "a value"

def frame.push.k(+hit: Bool, s: Stk, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +k: U32, +nc: U32, +pos: U32, +cell: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match hit:
    case True{}:
      err("`" ++ src.name(book_get(b, k)) ++ "` needs its own value: a cycle")
    case False{}:
      RMore{TkSv{k, nc, pos}, TkCon{Tk{KD.D{h, path, top, depth, n, 2}, cell, k}, s}, b, c, ss}

def frame.push.r(r: Bu, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +k: U32, +nc: U32, +pos: U32, +cell: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match r:
    case Bu{s, +hit}:
      frame.push.k(hit, s, h, path, top, depth, n, k, nc, pos, cell, b, c, ss)

# a frame pushed to serve cursor nc at position pos of source k, its host
# the demand d stopped needing it, set aside below it
def frame.push(h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +k: U32, +nc: U32, +pos: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  frame.push.r(busy(s, k, pos), h, path, top, depth, n, k, nc, pos, cell, b, c, ss)

# A use of a live source: the leaf a host's demand stopped needing becomes
# a negative cursor at the source's interface, in a ring of its own whose
# situating node holds the source's entry and the applying node's level
# (the splice's, sp.by), laid out as glam/test_materialize.bend's ring;
# the leaf's data entry dropped, as a splice drops it. A frame then serves
# the cursor, the first copy a serve like any other.

def use.cursor(h: P.H, +leaf: U32, +situ: U32) -> P.H:
  P.wr(P.wr(P.wr(h, leaf, P.hd2(18, 0, 0)), (leaf + 2 : U32), P.iface()), (leaf + 3 : U32), situ)

def use.situ(r: P.H & U32, +leaf: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +k: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (h, +situ) = r
  frame.push(use.cursor(P.wr(P.wr(P.put_st(h, situ, P.era()), (situ + 2 : U32), k), (situ + 3 : U32), leaf), leaf, situ),
    path, top, depth, n, k, leaf, P.iface(), cell, s, b, c, ss)

def use.top(r: P.H & U32, +leaf: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +k: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (h, +ht) = r
  use.situ(P.node(h, P.hd2(18, 2, S.sp.by(ht)), 0), leaf, path, top, depth, n, k, cell, s, b, c, ss)

def use.w(r: P.H & U32, +hb: U32, +leaf: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +k: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (h, +w) = r
  use.top(P.rd(P.drop(h, P.form(hb), w), top), leaf, path, top, depth, n, k, cell, s, b, c, ss)

def use.hb(r: P.H & U32, +leaf: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +k: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (h, +hb) = r
  use.w(P.rd(h, (leaf + 2 : U32)), hb, leaf, path, top, depth, n, k, cell, s, b, c, ss)

def use.leaf(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +k: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (h, +leaf) = r
  use.hb(P.rd(h, leaf), leaf, path, top, depth, n, k, cell, s, b, c, ss)

# source k used where d stopped needing it
def use.src(d: KD.D, +k: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      use.leaf(KS.d.at(h, top), path, top, depth, n, k, cell, s, b, c, ss)

# a host stopped at a cursor x: a frame for x's source at x's position
def frame.at.k(r: P.H & U32, +x: U32, +pos: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (h, +k) = r
  frame.push(h, path, top, depth, n, k, x, pos, cell, s, b, c, ss)

def frame.at.s(r: P.H & U32, +x: U32, +pos: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (h, +situ) = r
  frame.at.k(P.rd(h, (situ + 2 : U32)), x, pos, path, top, depth, n, cell, s, b, c, ss)

def frame.at.p(r: P.H & U32, +x: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (h, +pos) = r
  frame.at.s(M.rg.situ(h, x), x, pos, path, top, depth, n, cell, s, b, c, ss)

# A need served by entry k: a template spliced, a value resumed, a recipe
# forced on a task of its own above this one, a busy cell a cycle, a
# function's live source used
def needed.e(m: Maybe<&2, Ent>, d: KD.D, +k: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match m:
    case Some{e}:
      match e:
        case ETpl{t}:
          go(S.splice(d, t), cell, s, b, cn.splice(c), ss)
        case ESrc{+i, t, name}:
          use.src(d, k, cell, s, b, c, ss)
        case EValue{v}:
          go(KS.resume(d, v), cell, s, b, c, ss)
        case ERecipe{+t, +name}:
          RMore{Tk{KS.d.start(KN.load(t)), k, no_cell()}, TkCon{Tk{d, cell, k}, s}, book_set(b, k, EBusy{t, name}), cn.force(c), ss}
        case EBusy{t, name}:
          err("`" ++ G.str(name) ++ "` needs its own value: a cycle")
    case None{}:
      err("a leaf names no definition")

def needed.c(ch: Ch, d: KD.D, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match ch:
    case ChAt{+k}:
      needed.e(book_get(b, k), d, k, cell, s, b, c, ss)
    case ChLoop{}:
      err("definitions name each other alone, with no value: a cycle")

# demand stopped at a leaf (state 2)
def needed(r: KD.D & U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (d, +k) = r
  needed.c(chase(List.length(&2, Ent, b), b, k), d, cell, s, b, c, ss)

# Demand stopped needing (state 2), told apart by the kind of what it
# waits on: a cursor is served, any other a leaf, as a leaf ever was
# (KS.need would read a cursor's position as a handle)
def need.k(+cur: Bool, h: P.H, +x: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match cur:
    case True{}:
      frame.at.p(P.rd(h, (x + 2 : U32)), x, path, top, depth, n, cell, s, b, c, ss)
    case False{}:
      needed(KS.need(KD.D{h, path, top, depth, n, 2}), cell, s, b, c, ss)

def need.hd(r: P.H & U32, +x: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (h, +hd) = r
  need.k(U32.is_eq(P.rk(hd), 18), h, x, path, top, depth, n, cell, s, b, c, ss)

def need.at(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (h, +x) = r
  need.hd(P.rd(h, x), x, path, top, depth, n, cell, s, b, c, ss)

# A frame's step: its source taken out, served once into the net of the
# task below; then the source put back, and the host goes on, or the
# frame stays: out of fuel, or the source's own need met in the source (a
# template spliced, a value resumed, another live source's recipe spliced
# until sources hold copies), or a cell forced on a task above it

# a walk set going again, its interactions so far counted already
def d.again(d: KD.D) -> KD.D:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      KD.D{h, path, top, depth, 0, 0}

# the frame goes on with its walk at the next step, the source kept out
def frame.keep(d: KD.D, s2: Stk, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  RMore{TkSvD{k, nc, pos, d.again(d)}, s2, b, c, ss}

def frame.need.e(m: Maybe<&2, Ent>, d: KD.D, +depth: U32, +h2: U32, s2: Stk, +i: U32, +name: List<&2, U32>, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match m:
    case Some{e}:
      match e:
        case ETpl{t}:
          frame.keep(S.splice(d, t), s2, k, nc, pos, b, cn.splice(c), ss)
        case ESrc{+i2, t, name2}:
          frame.keep(S.splice(d, t), s2, k, nc, pos, b, cn.splice(c), ss)
        case EValue{v}:
          frame.keep(KS.resume(d, v), s2, k, nc, pos, b, c, ss)
        case ERecipe{+t, +name2}:
          RMore{Tk{KS.d.start(KN.load(t)), h2, no_cell()}, TkCon{TkSv{k, nc, pos}, s2}, book_set(b, h2, EBusy{t, name2}), cn.stop(cn.force(c), depth), srcs.put(ss, i, dh(d))}
        case EBusy{t, name2}:
          err("`" ++ G.str(name2) ++ "` needs its own value: a cycle")
    case None{}:
      err("a leaf names no definition")

def frame.need.c(ch: Ch, d: KD.D, +depth: U32, s2: Stk, +i: U32, +name: List<&2, U32>, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match ch:
    case ChAt{+h2}:
      frame.need.e(book_get(b, h2), d, depth, h2, s2, i, name, k, nc, pos, b, c, ss)
    case ChLoop{}:
      err("definitions name each other alone, with no value: a cycle")

def frame.need.l(r: KD.D & U32, +depth: U32, s2: Stk, +i: U32, +name: List<&2, U32>, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (d, +h2) = r
  frame.need.c(chase(List.length(&2, Ent, b), b, h2), d, depth, s2, i, name, k, nc, pos, b, c, ss)

def frame.need.k(+cur: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, s2: Stk, +i: U32, +name: List<&2, U32>, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match cur:
    case True{}:
      err("`" ++ G.str(name) ++ "` uses a copy of a live function inside its own net, not yet served")
    case False{}:
      frame.need.l(KS.need(KD.D{h, path, top, depth, n, 2}), depth, s2, i, name, k, nc, pos, b, c, ss)

def frame.need.hd(r: P.H & U32, +x: U32, path: KM.M, +top: U32, +depth: U32, +n: U32, s2: Stk, +i: U32, +name: List<&2, U32>, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (h, +hd) = r
  frame.need.k(U32.is_eq(P.rk(hd), 18), h, path, top, depth, n, s2, i, name, k, nc, pos, b, c, ss)

def frame.need.at(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, s2: Stk, +i: U32, +name: List<&2, U32>, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (h, +x) = r
  frame.need.hd(P.rd(h, x), x, path, top, depth, n, s2, i, name, k, nc, pos, b, c, ss)

# positioned demand stopped in the source, in state st
def frame.st(+st: U32, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, s2: Stk, +i: U32, +name: List<&2, U32>, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match st:
    case 4:
      RMore{TkSvD{k, nc, pos, KD.D{h, path, top, depth, 0, 0}}, s2, b, c, ss}
    case 2:
      frame.need.at(KS.d.at(h, top), path, top, depth, n, s2, i, name, k, nc, pos, b, c, ss)
    case _:
      err("serving `" ++ G.str(name) ++ "`: " ++ K.st_name(st))

def frame.stop(d: KD.D, s2: Stk, +i: U32, +name: List<&2, U32>, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      frame.st(st, h, path, top, depth, n, s2, i, name, k, nc, pos, b, c, ss)

def frame.sv(v: M.Sv, path0: KM.M, +top0: U32, +depth0: U32, +n0: U32, +st0: U32, +i: U32, +name: List<&2, U32>, +cell0: U32, +w0: U32, rest: Stk, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match v:
    case M.SvOk{hs, h, +n}:
      RMore{Tk{KD.d.go(h, path0, top0, depth0, n0), cell0, w0}, rest, b, cn.serve(cn.add(c, n)), srcs.put(ss, i, hs)}
    case M.SvStop{d, h, +n}:
      frame.stop(d, TkCon{Tk{KD.D{h, path0, top0, depth0, n0, st0}, cell0, w0}, rest}, i, name, k, nc, pos, b, cn.add(c, n), ss)

def frame.d(hs: P.H, d0: KD.D, +i: U32, +name: List<&2, U32>, +cell0: U32, +w0: U32, rest: Stk, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match d0:
    case KD.D{h0, path0, +top0, +depth0, +n0, +st0}:
      frame.sv(M.serve(hs, h0, nc, 8n, slice()), path0, top0, depth0, n0, st0, i, name, cell0, w0, rest, k, nc, pos, b, c, ss)

def frame.t(r: SrT, d0: KD.D, +i: U32, +name: List<&2, U32>, +cell0: U32, +w0: U32, rest: Stk, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn) -> Run:
  match r:
    case SrT{ss, x}:
      match x:
        case SrcIn{hs}:
          frame.d(hs, d0, i, name, cell0, w0, rest, k, nc, pos, b, c, ss)
        case SrcOut{}:
          err("a live source served twice at once")

def frame.e(m: Maybe<&2, Ent>, d0: KD.D, +cell0: U32, +w0: U32, rest: Stk, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match m:
    case Some{e}:
      match e:
        case ESrc{+i, t, +name}:
          frame.t(srcs.take(ss, i), d0, i, name, cell0, w0, rest, k, nc, pos, b, c)
        case _:
          err("a cursor's source is no live source")
    case None{}:
      err("a cursor's source names no definition")

# a frame's step, its host the task below it
def frame(s: Stk, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match s:
    case TkCon{below, rest}:
      match below:
        case Tk{d0, +cell0, +w0}:
          frame.e(book_get(b, k), d0, cell0, w0, rest, k, nc, pos, b, c, ss)
        case TkSv{+k2, +nc2, +pos2}:
          err("a frame serves no host")
        case TkSvD{+k2, +nc2, +pos2, d2}:
          err("a frame serves no host")
    case TkNil{}:
      err("a frame serves no host")

# a frame going on with its walk d in the source, out of the sources
def frame.dc(d: KD.D, d0: KD.D, +i: U32, +name: List<&2, U32>, +cell0: U32, +w0: U32, rest: Stk, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match d0:
    case KD.D{h0, path0, +top0, +depth0, +n0, +st0}:
      frame.sv(M.serve.from(d, h0, nc, 8n, slice()), path0, top0, depth0, n0, st0, i, name, cell0, w0, rest, k, nc, pos, b, c, ss)

def frame.cd(m: Maybe<&2, Ent>, d: KD.D, d0: KD.D, +cell0: U32, +w0: U32, rest: Stk, +k: U32, +nc: U32, +pos: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match m:
    case Some{e}:
      match e:
        case ESrc{+i, t, +name}:
          frame.dc(d, d0, i, name, cell0, w0, rest, k, nc, pos, b, c, ss)
        case _:
          err("a cursor's source is no live source")
    case None{}:
      err("a cursor's source names no definition")

# a step of a frame going on with its walk, its host the task below it
def frame.c(s: Stk, +k: U32, +nc: U32, +pos: U32, d: KD.D, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match s:
    case TkCon{below, rest}:
      match below:
        case Tk{d0, +cell0, +w0}:
          frame.cd(book_get(b, k), d, d0, cell0, w0, rest, k, nc, pos, b, c, ss)
        case TkSv{+k2, +nc2, +pos2}:
          err("a frame serves no host")
        case TkSvD{+k2, +nc2, +pos2, d2}:
          err("a frame serves no host")
    case TkNil{}:
      err("a frame serves no host")

# A cell's net done (state 1): its outcome kept, the task below it served.
# A value is resumed there, or the frame there goes on; a function's net
# is kept as a live source, used where the task below stopped, or the
# frame there goes on and finds it

def finished.v(s: Stk, +v: V.Val, +cell: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match s:
    case TkCon{t, rest}:
      match t:
        case Tk{d0, +cell0, +waits0}:
          go(KS.resume(d0, v), cell0, rest, book_set(b, cell, EValue{v}), c, ss)
        case TkSv{+k, +nc, +pos}:
          RMore{TkSv{k, nc, pos}, rest, book_set(b, cell, EValue{v}), c, ss}
        case TkSvD{+k, +nc, +pos, d}:
          err("a value forced for a frame going on")
    case TkNil{}:
      err("a value forced for no one")

def finished.src(s: Stk, +cell: U32, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match s:
    case TkCon{t, rest}:
      match t:
        case Tk{d0, +cell0, +waits0}:
          use.src(d0, cell, cell0, rest, b, c, ss)
        case TkSv{+k, +nc, +pos}:
          RMore{TkSv{k, nc, pos}, rest, b, c, ss}
        case TkSvD{+k, +nc, +pos, d}:
          err("a value forced for a frame going on")
    case TkNil{}:
      err("a value forced for no one")

def cell.src.e(m: Maybe<&2, Ent>, +i: U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match m:
    case Some{e}:
      match e:
        case EBusy{+t, +name}:
          finished.src(s, cell, book_set(b, cell, ESrc{i, t, name}), c, ss)
        case _:
          err("a value forced was not busy")
    case None{}:
      err("a value forced names no definition")

def cell.src(r: Srcs & U32, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn) -> Run:
  (ss, +i) = r
  cell.src.e(book_get(b, cell), i, cell, s, b, c, ss)

def cell.out(v: Maybe<&2, V.Val>, h: P.H, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match v:
    case Some{x}:
      finished.v(s, x, cell, b, c, ss)
    case None{}:
      cell.src(srcs.push(ss, h, 0), cell, s, b, c)

def cell.res(r: P.H & Maybe<&2, V.Val>, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (h, v) = r
  cell.out(v, h, cell, s, b, c, ss)

def cell.clean(+clean: Bool, h: P.H, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match clean:
    case True{}:
      cell.res(KN.result(h), cell, s, b, c, ss)
    case False{}:
      err("the kernel reported errors forcing a value")

def cell.done(r: P.H & P.HS, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      cell.clean(U32.is_eq(errs, 0), h, cell, s, b, cn.add(c, itrs), ss)

def ended.cell(d: KD.D, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      match st:
        case 1:
          cell.done(P.stats(P.count(h, n)), cell, s, b, c, ss)
        case _:
          err("forcing a value: " ++ K.st_name(st))

def ended.rm(m: Maybe<&2, U32>, d: KD.D, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match m:
    case Some{+k}:
      needed.c(chase(List.length(&2, Ent, b), b, k), d, no_cell(), s, b, c, ss)
    case None{}:
      RDone{counted(out(K.dres(d)), c)}

# asm.result's net done: its output, unless its root faces a leaf, as when
# a function returns a value's leaf, which is served as a need is and the
# net then finished again
def ended.root(r: KD.D & Maybe<&2, U32>, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  (d, m) = r
  ended.rm(m, d, s, b, c, ss)

# asm.result's demand ended: done, looked at for a leaf; else its outcome
def ended.r(d: KD.D, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      match st:
        case 1:
          ended.root(S.lazy_at(KD.D{h, path, top, depth, n, st}), s, b, c, ss)
        case _:
          RDone{counted(out(K.dres(KD.D{h, path, top, depth, n, st})), c)}

# demand's end: asm.result's, its output; a cell's, served below
def ended(+root: Bool, d: KD.D, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match root:
    case True{}:
      ended.r(d, s, b, c, ss)
    case False{}:
      ended.cell(d, cell, s, b, c, ss)

# a slice's end: out of fuel goes on (state 4 set going again, 0); a need
# is served (state 2); any other state ends the task
def sliced(d: KD.D, +cell: U32, s: Stk, +b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      match st:
        case 4:
          go(KD.D{h, path, top, depth, n, 0}, cell, s, b, c, ss)
        case 2:
          need.at(KS.d.at(h, top), path, top, depth, n, cell, s, b, c, ss)
        case _:
          ended(U32.is_eq(cell, no_cell()), KD.D{h, path, top, depth, n, st}, cell, s, b, c, ss)

# one slice of the assembly: of the task on top, a demand or a frame
def step(t: Tk, s: Stk, b: List<&2, Ent>, c: Cn, ss: Srcs) -> Run:
  match t:
    case Tk{d, +cell, +waits}:
      sliced(KD.Demand.demand(slice(), d), cell, s, b, c, ss)
    case TkSv{+k, +nc, +pos}:
      frame(s, k, nc, pos, b, c, ss)
    case TkSvD{+k, +nc, +pos, d}:
      frame.c(s, k, nc, pos, d, b, c, ss)

# Starting
# ========

def lowered(w: W.Top, b: List<&2, Ent>) -> Run:
  match w:
    case W.TOk{t}:
      go(KS.d.start(KN.load(t)), no_cell(), TkNil{}, b, Cn{0, 0, 0, 0, 0, 0}, SrsNil{})
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

# Objects at load (glam/objects.bend)
# ===================================
#
# Each object's members desugared, its body's names among the globals;
# every member a template of `self` and `_self`; each object an instance
# of its own, a cell for each of its members, its recipe the member's
# template applied to the instance's dict and the prior dict, the
# instance itself a constant, its dict of member handles. No object
# extends another yet, so a prior dict is empty and an override is an
# error. In the book: the functions' templates, the members' templates,
# the cells, the members' cells, the instances.

type Om is Data:
  Om{+line: U32, key: List<&2, U32>, body: G.Expr, +ov: Bool}

# a body, an object's own or an `extend`'s: its alias and its members
type Bo is Data:
  Bo{al: List<&2, U32>, ms: List<&2, Om>}

# an object: its line, name, parents' names and bodies in order
type Ob is Data:
  Ob{+line: U32, name: List<&2, U32>, ps: List<&2, List<&2, U32>>, bs: List<&2, Bo>}

# the members and the trouble so far, each reversed
type Oa is Data:
  Oa{ms: List<&2, Om>, es: List<&2, G.Diag>}

def om.put(r: D.Ds, m: Maybe<&2, List<&2, U32>>, +line: U32, +ov: Bool, a: Oa) -> Oa:
  match r m a:
    case D.DOk{e} Some{k} Oa{ms, es}:
      Oa{Con{Om{line, k, e, ov}, ms}, es}
    case D.DOk{e} None{} Oa{ms, es}:
      Oa{ms, Con{G.Diag{line, "a member's name is one name"}, es}}
    case D.DErr{d} _ Oa{ms, es}:
      Oa{ms, Con{d, es}}

def om.all(defs: List<&2, G.Def>, +globals: List<&2, List<&2, U32>>, a: Oa) -> Oa:
  match defs:
    case Nil{}:
      a
    case Con{d, rest}:
      match d:
        case G.Def{+line, path, +body}:
          om.all(rest, globals, om.put(D.expr(unover(body), Nil{}, globals), one_name(path), line, G.is_over(body), a))

# the objects desugared and the trouble so far, each reversed
type Oz is Data:
  Oz{obs: List<&2, Ob>, es: List<&2, G.Diag>}

# Parents: each a declared object's name, for now
type Pn is Data:
  PnOk{ns: List<&2, List<&2, U32>>}
  PnErr{d: G.Diag}

def pn.path(path: List<&2, List<&2, U32>>, +l: U32, ns: List<&2, List<&2, U32>>) -> Pn:
  match path:
    case Con{n, rest}:
      match rest:
        case Nil{}:
          PnOk{Con{n, ns}}
        case _:
          PnErr{G.Diag{l, "a parent other than an object's name is not supported yet"}}
    case Nil{}:
      PnErr{G.Diag{l, "an empty parent"}}

def pn.k(e: G.Expr, +line: U32, r: Pn) -> Pn:
  match e r:
    case G.EName{+l, path} PnOk{ns}:
      pn.path(path, l, ns)
    case _ PnErr{d}:
      PnErr{d}
    case _ PnOk{ns}:
      PnErr{G.Diag{line, "a parent other than an object's name is not supported yet"}}

def pn(ps: List<&2, G.Expr>, +line: U32) -> Pn:
  match ps:
    case Nil{}:
      PnOk{Nil{}}
    case Con{p, rest}:
      pn.k(p, line, pn(rest, line))

def ob.put.k(r: Pn, ms: List<&2, Om>, es1: List<&2, G.Diag>, +line: U32, name: List<&2, U32>, al: List<&2, U32>, z: Oz) -> Oz:
  match r z:
    case PnOk{ns} Oz{obs, es}:
      Oz{Con{Ob{line, name, ns, [Bo{al, List.reverse(&2, Om, ms)}]}, obs}, List.append(&2, G.Diag, es1, es)}
    case PnErr{d} Oz{obs, es}:
      Oz{obs, Con{d, List.append(&2, G.Diag, es1, es)}}

def ob.put(r: Oa, +line: U32, name: List<&2, U32>, al: List<&2, U32>, ps: List<&2, G.Expr>, z: Oz) -> Oz:
  match r:
    case Oa{ms, es1}:
      ob.put.k(pn(ps, line), ms, es1, line, name, al, z)

def ob.all(os: List<&2, G.Obj>, +gl: List<&2, List<&2, U32>>, z: Oz) -> Oz:
  match os:
    case Nil{}:
      z
    case Con{o, rest}:
      match o:
        case G.Obj{+line, name, ps, al, +members}:
          ob.all(rest, gl, ob.put(om.all(members, List.append(&2, List<&2, U32>, gl, globals(members)), Oa{Nil{}, Nil{}}), line, name, al, ps, z))

# Extends: each `extend Name with body` appended to Name's bodies

def ob.add.k(+hit: Bool, o: Ob, +b: Bo) -> Ob:
  match hit:
    case True{}:
      match o:
        case Ob{+line, name, ps, bs}:
          Ob{line, name, ps, List.append(&2, Bo, bs, [b])}
    case False{}:
      o

def ext.into(obs: List<&2, Ob>, +name: List<&2, U32>, +b: Bo) -> List<&2, Ob>:
  match obs:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case Ob{+line, +n2, ps, bs}:
          Con{ob.add.k(G.bytes_eq(n2, name), Ob{line, n2, ps, bs}, b), ext.into(rest, name, b)}

def ob.has(obs: List<&2, Ob>, +name: List<&2, U32>) -> Bool:
  match obs:
    case Nil{}:
      False{}
    case Con{o, rest}:
      match o:
        case Ob{+line, n2, ps, bs}:
          G.bytes_eq(n2, name) || ob.has(rest, name)

def ext.k(+has: Bool, r: Oa, +line: U32, +name: List<&2, U32>, al: List<&2, U32>, z: Oz) -> Oz:
  match has r z:
    case True{} Oa{ms, es1} Oz{obs, es}:
      Oz{ext.into(obs, name, Bo{al, List.reverse(&2, Om, ms)}), List.append(&2, G.Diag, es1, es)}
    case False{} Oa{ms, es1} Oz{obs, es}:
      Oz{obs, Con{G.Diag{line, "`extend " ++ G.str(name) ++ "` names no declared object"}, List.append(&2, G.Diag, es1, es)}}

def ext.one(z: Oz, +line: U32, +name: List<&2, U32>, al: List<&2, U32>, r: Oa) -> Oz:
  match z:
    case Oz{+obs, es}:
      ext.k(ob.has(obs, name), r, line, name, al, Oz{obs, es})

def ext.all(xs: List<&2, G.Obj>, +gl: List<&2, List<&2, U32>>, z: Oz) -> Oz:
  match xs:
    case Nil{}:
      z
    case Con{x, rest}:
      match x:
        case G.Obj{+line, name, ps, al, +members}:
          ext.all(rest, gl, ext.one(z, line, name, al, om.all(members, List.append(&2, List<&2, U32>, gl, globals(members)), Oa{Nil{}, Nil{}})))

def onames(os: List<&2, G.Obj>) -> List<&2, List<&2, U32>>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case G.Obj{+line, name, ps, al, ms}:
          Con{name, onames(rest)}

# every member's template, a definition of its key, reversed onto acc
def mt.ms(ms: List<&2, Om>, +al: List<&2, U32>, acc: List<&2, G.Def>) -> List<&2, G.Def>:
  match ms:
    case Nil{}:
      acc
    case Con{m, rest}:
      match m:
        case Om{+line, key, body, +ov}:
          mt.ms(rest, al, Con{G.Def{line, [key], O.mtpl(line, body, al)}, acc})

def mt.bs(bs: List<&2, Bo>, acc: List<&2, G.Def>) -> List<&2, G.Def>:
  match bs:
    case Nil{}:
      acc
    case Con{b, rest}:
      match b:
        case Bo{+al, ms}:
          mt.bs(rest, mt.ms(ms, al, acc))

def mt.all(obs: List<&2, Ob>, acc: List<&2, G.Def>) -> List<&2, G.Def>:
  match obs:
    case Nil{}:
      List.reverse(&2, G.Def, acc)
    case Con{o, rest}:
      match o:
        case Ob{+line, name, ps, bs}:
          mt.all(rest, mt.bs(bs, acc))

# C3 (Syntax.md, Objects): an object's order is the object first, then
# the merge of its parents' orders and its parents' list: at each step
# the first head no sequence holds in its tail

def tail_has(+x: List<&2, U32>, s: List<&2, List<&2, U32>>) -> Bool:
  match s:
    case Nil{}:
      False{}
    case Con{h, t}:
      W.has_key(x, t)

def tails_have(+x: List<&2, U32>, seqs: List<&2, List<&2, List<&2, U32>>>) -> Bool:
  match seqs:
    case Nil{}:
      False{}
    case Con{s, rest}:
      tail_has(x, s) || tails_have(x, rest)

def all_empty(seqs: List<&2, List<&2, List<&2, U32>>>) -> Bool:
  match seqs:
    case Nil{}:
      True{}
    case Con{s, rest}:
      match s:
        case Nil{}:
          all_empty(rest)
        case Con{h, t}:
          False{}

def drop_head.k(+hit: Bool, h: List<&2, U32>, t: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match hit:
    case True{}:
      t
    case False{}:
      Con{h, t}

def drop_head.s(s: List<&2, List<&2, U32>>, +x: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match s:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      drop_head.k(G.bytes_eq(h, x), h, t)

def drop_head(seqs: List<&2, List<&2, List<&2, U32>>>, +x: List<&2, U32>) -> List<&2, List<&2, List<&2, U32>>>:
  match seqs:
    case Nil{}:
      Nil{}
    case Con{s, rest}:
      Con{drop_head.s(s, x), drop_head(rest, x)}

type St is Data:
  St{seqs: List<&2, List<&2, List<&2, U32>>>, acc: List<&2, List<&2, U32>>}

def c3.pick.if(more: Unit -> Maybe<&2, St>, +ok: Bool, +x: List<&2, U32>, +all: List<&2, List<&2, List<&2, U32>>>, +acc: List<&2, List<&2, U32>>) -> Maybe<&2, St>:
  match ok:
    case True{}:
      Some{St{drop_head(all, x), Con{x, acc}}}
    case False{}:
      more(Unit{})

def c3.pick(seqs: List<&2, List<&2, List<&2, U32>>>, +all: List<&2, List<&2, List<&2, U32>>>, +acc: List<&2, List<&2, U32>>) -> Maybe<&2, St>:
  match seqs:
    case Nil{}:
      None{}
    case Con{s, rest}:
      match s:
        case Nil{}:
          c3.pick(rest, all, acc)
        case Con{+x, t}:
          c3.pick.if(u => c3.pick(rest, all, acc), Bool.not(tails_have(x, all)), x, all, acc)

def merge.k(+done: Bool, m: Maybe<&2, St>, acc: List<&2, List<&2, U32>>, more: St -> Maybe<&2, List<&2, List<&2, U32>>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match done:
    case True{}:
      Some{List.reverse(&2, List<&2, U32>, acc)}
    case False{}:
      match m:
        case Some{s2}:
          more(s2)
        case None{}:
          None{}

def merge(fuel: Nat, st: St) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match fuel:
    case 0n:
      None{}
    case 1n+p:
      match st:
        case St{+seqs, +acc}:
          merge.k(all_empty(seqs), c3.pick(seqs, seqs, acc), acc, s2 => merge(p, s2))

# the orders found: an object's name and its order, itself first
type Li is Data:
  Li{name: List<&2, U32>, order: List<&2, List<&2, U32>>}

def li.get.k(+hit: Bool, o: List<&2, List<&2, U32>>, more: Maybe<&2, List<&2, List<&2, U32>>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match hit:
    case True{}:
      Some{o}
    case False{}:
      more

def li.get(ls: List<&2, Li>, +n: List<&2, U32>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, rest}:
      match l:
        case Li{m, o}:
          li.get.k(G.bytes_eq(m, n), o, li.get(rest, n))

def li.has(ls: List<&2, Li>, +n: List<&2, U32>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{l, rest}:
      match l:
        case Li{m, o}:
          G.bytes_eq(m, n) || li.has(rest, n)

# the parents' orders, if every parent has one
type Po is Data:
  PoOk{os: List<&2, List<&2, List<&2, U32>>>}
  PoNo{}

def po.k(m: Maybe<&2, List<&2, List<&2, U32>>>, r: Po) -> Po:
  match m r:
    case Some{o} PoOk{os}:
      PoOk{Con{o, os}}
    case _ _:
      PoNo{}

def po(ps: List<&2, List<&2, U32>>, +ls: List<&2, Li>) -> Po:
  match ps:
    case Nil{}:
      PoOk{Nil{}}
    case Con{p, rest}:
      po.k(li.get(ls, p), po(rest, ls))

type Lr is Data:
  LrDone{l: Li}
  LrWait{}
  LrBad{name: List<&2, U32>, d: G.Diag}

def lr.m(m: Maybe<&2, List<&2, List<&2, U32>>>, +name: List<&2, U32>, +line: U32) -> Lr:
  match m:
    case Some{o}:
      LrDone{Li{name, Con{name, o}}}
    case None{}:
      LrBad{name, G.Diag{line, "the parents of `" ++ G.str(name) ++ "` cannot be ordered (C3)"}}

def lr.p(r: Po, +ps: List<&2, List<&2, U32>>, +name: List<&2, U32>, +line: U32, +fuel: Nat) -> Lr:
  match r:
    case PoOk{os}:
      lr.m(merge(fuel, St{List.append(&2, List<&2, List<&2, U32>>, os, [ps]), Nil{}}), name, line)
    case PoNo{}:
      LrWait{}

def lr.skip(+done: Bool, r: Lr) -> Lr:
  match done:
    case True{}:
      LrWait{}
    case False{}:
      r

# the orders found so far, and the trouble
type Lp is Data:
  Lp{ls: List<&2, Li>, es: List<&2, G.Diag>}

def lp.k(r: Lr, lp: Lp) -> Lp:
  match r lp:
    case LrDone{l} Lp{ls, es}:
      Lp{Con{l, ls}, es}
    case LrWait{} Lp{ls, es}:
      Lp{ls, es}
    case LrBad{+n, d} Lp{ls, es}:
      Lp{Con{Li{n, [n]}, ls}, Con{d, es}}

def lp.ob(o: Ob, +fuel: Nat, lp: Lp) -> Lp:
  match o lp:
    case Ob{+line, +name, +ps, bs} Lp{+ls, es}:
      lp.k(lr.skip(li.has(ls, name), lr.p(po(ps, ls), ps, name, line, fuel)), Lp{ls, es})

def lp.pass(obs: List<&2, Ob>, +fuel: Nat, lp: Lp) -> Lp:
  match obs:
    case Nil{}:
      lp
    case Con{o, rest}:
      lp.pass(rest, fuel, lp.ob(o, fuel, lp))

def lp.fix(k: Nat, +obs: List<&2, Ob>, +fuel: Nat, lp: Lp) -> Lp:
  match k:
    case 0n:
      lp
    case 1n+p:
      lp.fix(p, obs, fuel, lp.pass(obs, fuel, lp))

# an object still with no order extends itself
def cyc.k(+has: Bool, name: List<&2, U32>, +line: U32, es: List<&2, G.Diag>) -> List<&2, G.Diag>:
  match has:
    case True{}:
      es
    case False{}:
      Con{G.Diag{line, "`" ++ G.str(name) ++ "` extends itself through its parents, or a parent is no declared object"}, es}

def cyc(obs: List<&2, Ob>, +ls: List<&2, Li>, es: List<&2, G.Diag>) -> List<&2, G.Diag>:
  match obs:
    case Nil{}:
      es
    case Con{o, rest}:
      match o:
        case Ob{+line, +name, ps, bs}:
          cyc(rest, ls, cyc.k(li.has(ls, name), name, line, es))

# The instances: each object's mixins, its order from the base, walked
# with the latest cell of each key; each member definition a cell whose
# prior dict is the keys before its mixin; `=` introducing a key that
# mixin has not, `:=` overriding one it has

# how many members the bodies hold
def bo.n(bs: List<&2, Bo>) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{b, rest}:
      match b:
        case Bo{al, ms}:
          (U32.from_nat(List.length(&2, Om, ms)) + bo.n(rest) : U32)

type Mo is Data:
  Mo{name: List<&2, U32>, +mbase: U32, bs: List<&2, Bo>}

def mos(obs: List<&2, Ob>, +mi: U32) -> List<&2, Mo>:
  match obs:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case Ob{+line, name, ps, +bs}:
          Con{Mo{name, mi, bs}, mos(rest, (mi + bo.n(bs) : U32))}

def mo.get.k(+hit: Bool, x: Mo, more: Maybe<&2, Mo>) -> Maybe<&2, Mo>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      more

def mo.get(ms: List<&2, Mo>, +n: List<&2, U32>) -> Maybe<&2, Mo>:
  match ms:
    case Nil{}:
      None{}
    case Con{x, rest}:
      match x:
        case Mo{+m, +b, xs}:
          mo.get.k(G.bytes_eq(m, n), Mo{m, b, xs}, mo.get(rest, n))

type Kc is Data:
  Kc{key: List<&2, U32>, +cid: U32}

def kc.dict(cur: List<&2, Kc>) -> List<&2, V.Ent>:
  match cur:
    case Nil{}:
      Nil{}
    case Con{c, rest}:
      match c:
        case Kc{k, +cid}:
          Con{O.entry(k, cid), kc.dict(rest)}

def kc.has(cur: List<&2, Kc>, +k: List<&2, U32>) -> Bool:
  match cur:
    case Nil{}:
      False{}
    case Con{c, rest}:
      match c:
        case Kc{m, +cid}:
          G.bytes_eq(m, k) || kc.has(rest, k)

def kc.set.k(+hit: Bool, c: Kc, +k: List<&2, U32>, +cid: U32, rest: List<&2, Kc>, more: List<&2, Kc>) -> List<&2, Kc>:
  match hit:
    case True{}:
      Con{Kc{k, cid}, rest}
    case False{}:
      Con{c, more}

# key k's latest cell set to cid, in place or appended
def kc.set(cur: List<&2, Kc>, +k: List<&2, U32>, +cid: U32) -> List<&2, Kc>:
  match cur:
    case Nil{}:
      [Kc{k, cid}]
    case Con{c, +rest}:
      match c:
        case Kc{+m, +c2}:
          kc.set.k(G.bytes_eq(m, k), Kc{m, c2}, k, cid, rest, kc.set(rest, k, cid))

# a member's cell queued: its line, key, template and prior dict
type Cq is Data:
  Cq{+line: U32, key: List<&2, U32>, +tid: U32, prior: V.Val}

# a walk: the latest cells, the next handle, the cells queued reversed,
# the trouble
type Wk is Data:
  Wk{cur: List<&2, Kc>, +next: U32, cq: List<&2, Cq>, es: List<&2, G.Diag>}

def wk.one(+ov: Bool, +had: Bool, +line: U32, +key: List<&2, U32>, +tid: U32, +prior: V.Val, w: Wk) -> Wk:
  match ov had w:
    case True{} False{} Wk{cur, +next, cq, es}:
      Wk{cur, next, cq, Con{G.Diag{line, "`" ++ G.str(key) ++ "` is not defined before; := overrides"}, es}}
    case False{} True{} Wk{cur, +next, cq, es}:
      Wk{cur, next, cq, Con{G.Diag{line, "`" ++ G.str(key) ++ "` is already defined by a parent; := overrides"}, es}}
    case _ _ Wk{cur, +next, cq, es}:
      Wk{kc.set(cur, key, next), (next + 1 : U32), Con{Cq{line, key, tid, prior}, cq}, es}

def wk.m(ms: List<&2, Om>, +tid: U32, +prior: V.Val, +pkeys: List<&2, Kc>, w: Wk) -> Wk:
  match ms:
    case Nil{}:
      w
    case Con{m, rest}:
      match m:
        case Om{+line, +key, body, +ov}:
          wk.m(rest, (tid + 1 : U32), prior, pkeys, wk.one(ov, kc.has(pkeys, key), line, key, tid, prior, w))

# a body, its prior dict the keys before it
def wk.body(ms: List<&2, Om>, +tid: U32, w: Wk) -> Wk:
  match w:
    case Wk{+cur, +next, cq, es}:
      wk.m(ms, tid, V.VDict{kc.dict(cur)}, cur, Wk{cur, next, cq, es})

# an object's bodies in order, each a mixin step of its own
def wk.bodies(bs: List<&2, Bo>, +tid: U32, w: Wk) -> Wk:
  match bs:
    case Nil{}:
      w
    case Con{b, rest}:
      match b:
        case Bo{al, +ms}:
          wk.bodies(rest, (tid + U32.from_nat(List.length(&2, Om, ms)) : U32), wk.body(ms, tid, w))

def wk.mixin(mo: Maybe<&2, Mo>, x: List<&2, U32>, +tbase: U32, w: Wk) -> Wk:
  match mo w:
    case Some{Mo{m, +mbase, bs}} Wk{cur, +next, cq, es}:
      wk.bodies(bs, (tbase + mbase : U32), Wk{cur, next, cq, es})
    case None{} Wk{cur, +next, cq, es}:
      Wk{cur, next, cq, Con{G.Diag{0, "`" ++ G.str(x) ++ "` is no declared object"}, es}}

def wk.all(mixins: List<&2, List<&2, U32>>, +mos: List<&2, Mo>, +tbase: U32, w: Wk) -> Wk:
  match mixins:
    case Nil{}:
      w
    case Con{+x, rest}:
      wk.all(rest, mos, tbase, wk.mixin(mo.get(mos, x), x, tbase, w))

def dotted(o: List<&2, U32>, k: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, o, Con{46, k})

# the queued cells' recipes, in handle order, onto acc reversed
def cq.defs(cq: List<&2, Cq>, +inst: V.Val, +name: List<&2, U32>, acc: List<&2, G.Def>) -> List<&2, G.Def>:
  match cq:
    case Nil{}:
      acc
    case Con{c, rest}:
      match c:
        case Cq{+line, key, +tid, prior}:
          cq.defs(rest, inst, name, Con{G.Def{line, [dotted(name, key)], O.recipe(line, tid, inst, prior)}, acc})

# the layout so far: the next handle, the members' cells reversed, the
# instances reversed, the trouble
type Gl is Data:
  Gl{+next: U32, defs: List<&2, G.Def>, ivs: List<&2, V.Val>, es: List<&2, G.Diag>}

def gl.k(+inst: V.Val, cq: List<&2, Cq>, +name: List<&2, U32>, +next: U32, defs: List<&2, G.Def>, ivs: List<&2, V.Val>, es: List<&2, G.Diag>) -> Gl:
  Gl{next, cq.defs(List.reverse(&2, Cq, cq), inst, name, defs), Con{inst, ivs}, es}

def gl.w(w: Wk, +name: List<&2, U32>, defs: List<&2, G.Def>, ivs: List<&2, V.Val>, es: List<&2, G.Diag>) -> Gl:
  match w:
    case Wk{cur, +next, cq, es2}:
      gl.k(V.VDict{kc.dict(cur)}, cq, name, next, defs, ivs, List.append(&2, G.Diag, es2, es))

def gl.ob(order: Maybe<&2, List<&2, List<&2, U32>>>, +name: List<&2, U32>, +mos: List<&2, Mo>, +tbase: U32, g: Gl) -> Gl:
  match order:
    case None{}:
      g
    case Some{ord}:
      match g:
        case Gl{+next, defs, ivs, es}:
          gl.w(wk.all(List.reverse(&2, List<&2, U32>, ord), mos, tbase, Wk{Nil{}, next, Nil{}, Nil{}}), name, defs, ivs, es)

def gl.all(obs: List<&2, Ob>, +ls: List<&2, Li>, +mos: List<&2, Mo>, +tbase: U32, g: Gl) -> Gl:
  match obs:
    case Nil{}:
      g
    case Con{o, rest}:
      match o:
        case Ob{+line, +name, ps, bs}:
          gl.all(rest, ls, mos, tbase, gl.ob(li.get(ls, name), name, mos, tbase, g))

def orefs(obs: List<&2, Ob>, +i: U32) -> List<&2, W.Ref>:
  match obs:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case Ob{+line, name, ps, bs}:
          Con{W.Ref{name, i}, orefs(rest, (i + 1 : U32))}

def ev.all(vs: List<&2, V.Val>) -> List<&2, Ent>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{v, rest}:
      Con{EValue{v}, ev.all(rest)}

# Starting
# ========

def len(xs: List<&2, G.Def>) -> U32:
  U32.from_nat(List.length(&2, G.Def, xs))

def start.ly(es: List<&2, G.Diag>, +rs: List<&2, W.Ref>, fs: List<&2, G.Def>, mts: List<&2, G.Def>, cs: List<&2, G.Def>, mcs: List<&2, G.Def>, ivs: List<&2, V.Val>, +ls: List<&2, G.Def>) -> Run:
  match es:
    case Nil{}:
      start.b(bk.cat(bk.cat(book.t(fs, rs, globals(ls)), book.t(mts, rs, globals(ls))), bk.cat(bk.cat(book.c(cs, rs, globals(ls)), book.c(mcs, rs, globals(ls))), BkOk{ev.all(ivs)})), ls, rs)
    case Con{e, rest}:
      RDone{OErrs{List.reverse(&2, G.Diag, Con{e, rest})}}

def start.gl(g: Gl, lpes: List<&2, G.Diag>, +f: U32, +m: U32, +c: U32, +fs: List<&2, G.Def>, mts: List<&2, G.Def>, +cs: List<&2, G.Def>, +ls: List<&2, G.Def>, obs: List<&2, Ob>) -> Run:
  match g:
    case Gl{+next, defs, ivs, es}:
      start.ly(List.append(&2, G.Diag, es, lpes),
        List.append(&2, W.Ref, refs(fs, 0), List.append(&2, W.Ref, refs(cs, (f + m : U32)), orefs(obs, next))),
        fs, mts, cs, List.reverse(&2, G.Def, defs), List.reverse(&2, V.Val, ivs), ls)

def start.lp(r: Lp, +f: U32, +m: U32, +c: U32, +fs: List<&2, G.Def>, mts: List<&2, G.Def>, +cs: List<&2, G.Def>, ls: List<&2, G.Def>, +obs: List<&2, Ob>) -> Run:
  match r:
    case Lp{+lis, es}:
      start.gl(gl.all(obs, lis, mos(obs, 0), f, Gl{(f + m + c : U32), Nil{}, Nil{}, Nil{}}), cyc(obs, lis, es), f, m, c, fs, mts, cs, ls, obs)

# the handles: the functions' templates from 0, the members' templates,
# the cells, the members' cells, the instances
def start.ids(+f: U32, +m: U32, +c: U32, +fs: List<&2, G.Def>, mts: List<&2, G.Def>, +cs: List<&2, G.Def>, ls: List<&2, G.Def>, +obs: List<&2, Ob>) -> Run:
  start.lp(lp.fix(List.length(&2, Ob, obs), obs, Nat.add(List.length(&2, Ob, obs), 1n), Lp{Nil{}, Nil{}}), f, m, c, fs, mts, cs, ls, obs)

def start.cs(r: Pt, +fs: List<&2, G.Def>, +mts: List<&2, G.Def>, obs: List<&2, Ob>) -> Run:
  match r:
    case Pt{+cs, ls}:
      start.ids(len(fs), len(mts), len(List.reverse(&2, G.Def, cs)), fs, mts, List.reverse(&2, G.Def, cs), List.reverse(&2, G.Def, ls), obs)

def start.mt(+mts: List<&2, G.Def>, +fs: List<&2, G.Def>, +vs: List<&2, G.Def>, obs: List<&2, Ob>) -> Run:
  start.cs(pick(vs, cell_names(List.append(&2, G.Def, fs, mts), vs), Pt{Nil{}, Nil{}}), fs, mts, obs)

def start.fv(+fs: List<&2, G.Def>, +vs: List<&2, G.Def>, +obs: List<&2, Ob>) -> Run:
  start.mt(mt.all(obs, Nil{}), fs, vs, obs)

def start.pt(r: Pt, obs: List<&2, Ob>) -> Run:
  match r:
    case Pt{fs, vs}:
      start.fv(List.reverse(&2, G.Def, fs), List.reverse(&2, G.Def, vs), obs)

def start.e(es: List<&2, G.Diag>, ds: List<&2, G.Def>, obs: List<&2, Ob>, +lk: Bool) -> Run:
  match es:
    case Nil{}:
      start.pt(part(vers(List.reverse(&2, G.Def, ds)), lk, Pt{Nil{}, Nil{}}), List.reverse(&2, Ob, obs))
    case Con{e, rest}:
      RDone{OErrs{List.reverse(&2, G.Diag, Con{e, rest})}}

def start.d(a: Dd, z: Oz, +lk: Bool) -> Run:
  match a z:
    case Dd{ds, es} Oz{obs, oes}:
      start.e(List.append(&2, G.Diag, oes, es), ds, obs, lk)

def start.g(+gl: List<&2, List<&2, U32>>, defs: List<&2, G.Def>, objs: List<&2, G.Obj>, exts: List<&2, G.Obj>, +lk: Bool) -> Run:
  start.d(dall(defs, gl, Dd{Nil{}, Nil{}}), ext.all(exts, gl, ob.all(objs, gl, Oz{Nil{}, Nil{}})), lk)

def start.p(p: G.Parsed, +lk: Bool) -> Run:
  match p:
    case G.PErr{ds}:
      RDone{OErrs{ds}}
    case G.POk{m}:
      match m:
        case G.Mod{+utf8, +defs, +objs, exts}:
          start.g(List.append(&2, List<&2, U32>, globals(defs), onames(objs)), defs, objs, exts, lk)

# a ".g" source's bytes to its assembly, begun: parsed and lowered, its
# evaluation not yet stepped; lk links every definition statically
# A check of freezing (the Cells plan's `cells-freeze.cursors`): with
# `--refreeze`, every template in the book is loaded and frozen back
# before the run, so that the ladder can compare what it writes and counts
# with the templates as lowered.
def refrozen.r(r: P.H & T.Tpl) -> T.Tpl:
  (h, t) = r
  t

def refrozen.t(t: T.Tpl) -> T.Tpl:
  refrozen.r(F.freeze(KN.load(t)))

def refrozen.e(e: Ent) -> Ent:
  match e:
    case ETpl{t}:
      ETpl{refrozen.t(t)}
    case ERecipe{t, name}:
      ERecipe{refrozen.t(t), name}
    case EBusy{t, name}:
      EBusy{refrozen.t(t), name}
    case EValue{v}:
      EValue{v}
    case ESrc{+i, t, name}:
      ESrc{i, refrozen.t(t), name}

def refrozen.b(b: List<&2, Ent>) -> List<&2, Ent>:
  match b:
    case Nil{}:
      Nil{}
    case Con{e, rest}:
      Con{refrozen.e(e), refrozen.b(rest)}

def refrozen(+on: Bool, r: Run) -> Run:
  match on:
    case False{}:
      r
    case True{}:
      match r:
        case RDone{o}:
          RDone{o}
        case RMore{t, s, b, c, ss}:
          RMore{t, s, refrozen.b(b), c, ss}

def start(bs: List<&2, U32>, +lk: Bool) -> Run:
  start.p(G.parse(L.lex(bs)), lk)
