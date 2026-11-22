import Base
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/kmodel.bend as KMd
import ../spike/val.bend as V
import ./index.bend as X
import ./index_model.bend as M

# The index's model run beside its code (glam/index_model.bend; the
# Cells plan's cells-freeze.sharing.cursors.index.laws): pseudo-random
# puts and removals on a heap and on the model, after each the heap's
# words realizing the model exactly (M.ix.real over the words' view, as
# the laws read them), the model's invariant, every key present found by
# both at its cursor, a key absent by neither, no error counted, and the
# node a put's branch takes and a removal frees the free list's head, as
# the model has it. The free list is filled first, so that no put grows
# the store. Run by scripts/ladder.py, which expects `ok` alone.
#
#   bend glam/test_index_model.bend

# a present cursor and its key
type Kx is Data:
  Kx{+x: U32, +k: U32}

# The words' view and depth, the words handed back (AD.view's list)
def vw.n(p: Array<U32> & List<&2, U32>, q: Array<U32> & List<&2, U32>) -> Array<U32> & List<&2, U32>:
  (xs, l1) = p
  (ys, l2) = q
  (ANode{xs, ys}, List.append(&2, U32, l1, l2))

def vw(a: Array<U32>) -> Array<U32> & List<&2, U32>:
  match a:
    case ALeaf{+x}:
      (ALeaf{x}, [x])
    case ANode{xs, ys}:
      vw.n(vw(xs), vw(ys))

def dep.n(p: Array<U32> & Nat, ys: Array<U32>) -> Array<U32> & Nat:
  (xs, +n) = p
  (ANode{xs, ys}, 1n+n)

def dep(a: Array<U32>) -> Array<U32> & Nat:
  match a:
    case ALeaf{+x}:
      (ALeaf{x}, 0n)
    case ANode{xs, ys}:
      dep.n(dep(xs), ys)

type Vw is Type:
  Vw{h: P.H, +v: List<&2, U32>, +d: Nat}

def view.v(p: Array<U32> & List<&2, U32>, a: Array<V.Val>, +d: Nat) -> Vw:
  (w, +v) = p
  Vw{P.H{KM.MG{w}, a}, v, d}

def view.d(p: Array<U32> & Nat, a: Array<V.Val>) -> Vw:
  (w, +d) = p
  view.v(vw(w), a, d)

def view(h: P.H) -> Vw:
  match h:
    case P.H{m, a}:
      match m:
        case KM.MG{w}:
          view.d(dep(w), a)

# Building: a situating node, and n nodes taken and given back, the free
# list then holding them
def sn.w(r: P.H & U32) -> P.H & U32:
  (h, +s) = r
  (P.wr(h, (s + 3 : U32), s), s)

def situ(h: P.H) -> P.H & U32:
  sn.w(P.node(h, P.hd2(18, 2, 0), 0))

def fill.c(r: P.H & U32, ns: List<&2, U32>) -> P.H & List<&2, U32>:
  (h, +x) = r
  (h, Con{x, ns})

def fill.s(r: P.H & List<&2, U32>) -> P.H & List<&2, U32>:
  (h, ns) = r
  fill.c(P.node(h, P.hd2(18, 0, 0), 0), ns)

def fill.a(f: Nat, r: P.H & List<&2, U32>) -> P.H & List<&2, U32>:
  match f:
    case 0n:
      r
    case 1n+g:
      fill.a(g, fill.s(r))

def fill.f(ns: List<&2, U32>, h: P.H) -> P.H:
  match ns:
    case Nil{}:
      h
    case Con{+x, t}:
      fill.f(t, P.free(h, x))

def fill.r(r: P.H & List<&2, U32>) -> P.H:
  (h, ns) = r
  fill.f(ns, h)

def fill(h: P.H, +n: Nat) -> P.H:
  fill.r(fill.a(n, (h, [])))

def rng(+s: U32) -> U32:
  ((s * 1664525 : U32) + 1013904223 : U32)

def errs.r(r: P.H & P.HS) -> P.H & U32:
  (h, hs) = r
  match hs:
    case P.HS{+n, +e, +c}:
      (h, e)

def mshow(m: Maybe<&2, U32>) -> String:
  match m:
    case Some{+x}:
      "Some " ++ U32.show(x)
    case None{}:
      "None"

def meq(m: Maybe<&2, U32>, n: Maybe<&2, U32>) -> Bool:
  match m:
    case Some{+x}:
      match n:
        case Some{+y}:
          U32.is_eq(x, y)
        case None{}:
          False{}
    case None{}:
      match n:
        case Some{+y}:
          False{}
        case None{}:
          True{}

def is_some(m: Maybe<&2, U32>) -> Bool:
  match m:
    case Some{+x}:
      True{}
    case None{}:
      False{}

# Checks after an op: the realization and the invariant; every present
# key found by both at its cursor; a probe k found alike by both; no
# error counted
def ck.k(+ok: Bool, +what: String) -> String:
  match ok:
    case True{}:
      ""
    case False{}:
      what

def ck.one(r: P.H & Maybe<&2, U32>, +ml: Maybe<&2, U32>, +x: U32, +k: U32) -> P.H & String:
  (h, +got) = r
  (h, ck.k(meq(got, Some{x}), "find " ++ U32.show(k) ++ ": code " ++ mshow(got) ++ "; ") ++
    ck.k(meq(ml, Some{x}), "look " ++ U32.show(k) ++ ": model " ++ mshow(ml) ++ "; "))

def ck.acc(r: P.H & String, +acc: String) -> P.H & String:
  (h, e) = r
  (h, acc ++ e)

def ck.fstep.r(r: P.H & String, +x: U32, +k: U32, +s: U32, +I: M.Ix) -> P.H & String:
  (h, acc) = r
  ck.acc(ck.one(X.ix.find(h, s, k), M.ix.look(I, k), x, k), acc)

def ck.fstep(p: Kx, r: P.H & String, +s: U32, +I: M.Ix) -> P.H & String:
  match p:
    case Kx{+x, +k}:
      ck.fstep.r(r, x, k, s, I)

def ck.finds(ps: List<&2, Kx>, r: P.H & String, +s: U32, +I: M.Ix) -> P.H & String:
  match ps:
    case Nil{}:
      r
    case Con{+p, t}:
      ck.finds(t, ck.fstep(p, r, s, I), s, I)

def ck.view(w: Vw, +s: U32, +I: M.Ix) -> P.H & String:
  match w:
    case Vw{h, +v, +d}:
      (h, ck.k(M.ix.real(v, d, s, I), "not realized; ") ++ ck.k(M.ix.inv(I), "invariant broken; ") ++ ck.k(M.ix.lay(I, s, d), "not laid out; "))

def ck.absent(r: P.H & Maybe<&2, U32>, +ml: Maybe<&2, U32>, +k: U32) -> P.H & String:
  (h, +got) = r
  (h, ck.k(meq(got, ml), "probe " ++ U32.show(k) ++ ": code " ++ mshow(got) ++ ", model " ++ mshow(ml) ++ "; "))

def ck.errs(r: P.H & U32) -> P.H & String:
  (h, +e) = r
  (h, ck.k(U32.is_eq(e, 0), "errors " ++ U32.show(e) ++ "; "))

def ck.all.c(r: P.H & String) -> P.H & String:
  (h, acc) = r
  ck.acc(ck.errs(errs.r(P.stats(h))), acc)

def ck.all.b(r: P.H & String, +s: U32, +k: U32, +I: M.Ix) -> P.H & String:
  (h, acc) = r
  ck.all.c(ck.acc(ck.absent(X.ix.find(h, s, k), M.ix.look(I, k), k), acc))

def ck.all(h: P.H, +ps: List<&2, Kx>, +s: U32, +k: U32, +I: M.Ix) -> P.H & String:
  ck.all.b(ck.finds(ps, ck.view(view(h), s, I), s, I), s, k, I)

# The run: the heap, the situating node, the model, the cursors present,
# the generator's state, and the first fault found, if any
type St is Type:
  St{h: P.H, +s: U32, +I: M.Ix, +ps: List<&2, Kx>, +seed: U32, +bad: Bool, +msg: String}

def key(+seed: U32) -> U32:
  ((seed >> 4n : U32) .&. 1023 : U32)

def drop(ps: List<&2, Kx>, +j: Nat) -> List<&2, Kx>:
  match ps:
    case Nil{}:
      []
    case Con{+p, t}:
      match j:
        case 0n:
          t
        case 1n+i:
          Con{p, drop(t, i)}

def nth(ps: List<&2, Kx>, +j: Nat) -> Kx:
  match ps:
    case Nil{}:
      Kx{0, 0}
    case Con{+p, t}:
      match j:
        case 0n:
          p
        case 1n+i:
          nth(t, i)

def len(ps: List<&2, Kx>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case Con{+p, t}:
      1n+len(t)

def fault(+e: String) -> Bool:
  Bool.not(String.eq(e, ""))

# a put: a cursor made, its key written, then put; the free list's head,
# read before the put, the node the model's branch takes
def put.e(r: P.H & String, +x: U32, +k: U32, +s: U32, +I: M.Ix, +ps: List<&2, Kx>, +seed: U32) -> St:
  (h, +e) = r
  St{h, s, I, ps, seed, fault(e), "put " ++ U32.show(k) ++ " at " ++ U32.show(x) ++ ": " ++ e}

# the insert law's premises, before a put: x and the free list's head
# fresh, the head the branch's node
def ck.pre(w: Vw, +s: U32, +I: M.Ix, +x: U32, +b: U32) -> P.H & String:
  match w:
    case Vw{h, +v, +d}:
      (h, ck.k(M.ix.fresh(I, s, x, b, d), "not fresh; ") ++ ck.k(M.ix.room(I, v, d, b), "no room; "))

def put.g(r: P.H & String, +x: U32, +k: U32, +fh: U32, +s: U32, +I: M.Ix, +ps: List<&2, Kx>, +seed: U32) -> St:
  (h, +e0) = r
  put.e(ck.acc(ck.all(X.ix.insert(h, s, x), Con{Kx{x, k}, ps}, s, key(rng(seed)), M.ix.put(I, x, k, KMd.at_idx(fh))), e0),
    x, k, s, M.ix.put(I, x, k, KMd.at_idx(fh)), Con{Kx{x, k}, ps}, seed)

def put.f(r: P.H & U32, +x: U32, +k: U32, +s: U32, +I: M.Ix, +ps: List<&2, Kx>, +seed: U32) -> St:
  (h, +fh) = r
  put.g(ck.pre(view(h), s, I, x, KMd.at_idx(fh)), x, k, fh, s, I, ps, seed)

def put.x(r: P.H & U32, +k: U32, +s: U32, +I: M.Ix, +ps: List<&2, Kx>, +seed: U32) -> St:
  (h, +x) = r
  put.f(P.rd(P.wr(h, (x + 2 : U32), k), P.at_fh()), x, k, s, I, ps, seed)

def put.go(h: P.H, +k: U32, +s: U32, +I: M.Ix, +ps: List<&2, Kx>, +seed: U32) -> St:
  put.x(P.node(h, P.hd2(18, 0, 0), 0), k, s, I, ps, seed)

def put.k(+dup: Bool, h: P.H, +k: U32, +s: U32, +I: M.Ix, +ps: List<&2, Kx>, +seed: U32) -> St:
  match dup:
    case True{}:
      St{h, s, I, ps, seed, False{}, ""}
    case False{}:
      put.go(h, k, s, I, ps, seed)

# a removal: the branch the model frees, if any, the free list's head
# after
def rem.fh(+fh: U32, +par: Maybe<&2, U32>) -> String:
  match par:
    case Some{+b}:
      ck.k(U32.is_eq(fh, ((b >> 2n : U32) + 1 : U32)), "free head " ++ U32.show(fh) ++ ", parent " ++ U32.show(b) ++ "; ")
    case None{}:
      ""

def rem.e(r: P.H & String, +e0: String, +x: U32, +k: U32, +s: U32, +I: M.Ix, +ps: List<&2, Kx>, +seed: U32) -> St:
  (h, +e) = r
  St{h, s, I, ps, seed, fault(e0 ++ e), "remove " ++ U32.show(k) ++ " at " ++ U32.show(x) ++ ": " ++ e0 ++ e}

def cut.of(I: M.Ix, +x: U32, +k: U32, +s: U32) -> M.Cut:
  match I:
    case M.Ept{}:
      M.Cut{0, 0, 0}
    case M.Has{+t}:
      M.tr.cutat(t, x, k, (s + 3 : U32))

def cut.ck(r: P.H & U32, +c: M.Cut, +par: Maybe<&2, U32>) -> P.H & String:
  (h, +w) = r
  match c:
    case M.Cut{+loc, +cp, +sib}:
      (h, ck.k(Bool.not(is_some(par)) || (meq(par, Some{cp}) && U32.is_eq(w, sib)), "cut: loc " ++ U32.show(loc) ++ " holds " ++ U32.show(w) ++ ", sib " ++ U32.show(sib) ++ ", par " ++ U32.show(cp) ++ "; "))

def cut.loc(c: M.Cut) -> U32:
  match c:
    case M.Cut{+loc, +cp, +sib}:
      loc

def rem.f2(r: P.H & U32, +e0: String, +x: U32, +k: U32, +s: U32, +I: M.Ix, +ps: List<&2, Kx>, +seed: U32) -> St:
  (h, +fh) = r
  rem.e(ck.all(h, ps, s, k, M.ix.del(I, x, k)), e0 ++ rem.fh(fh, M.ix.par(I, x, k)), x, k, s, M.ix.del(I, x, k), ps, seed)

def rem.c(r: P.H & String, +x: U32, +k: U32, +s: U32, +I: M.Ix, +ps: List<&2, Kx>, +seed: U32) -> St:
  (h, +e0) = r
  rem.f2(P.rd(h, P.at_fh()), e0, x, k, s, I, ps, seed)

def rem.w(h: P.H, +x: U32, +k: U32, +s: U32, +I: M.Ix, +ps: List<&2, Kx>, +seed: U32) -> St:
  rem.c(cut.ck(P.rd(h, cut.loc(cut.of(I, x, k, s))), cut.of(I, x, k, s), M.ix.par(I, x, k)), x, k, s, I, ps, seed)

def rem.go(p: Kx, h: P.H, +j: Nat, +s: U32, +I: M.Ix, +ps: List<&2, Kx>, +seed: U32) -> St:
  match p:
    case Kx{+x, +k}:
      rem.w(X.ix.remove(h, s, x), x, k, s, I, drop(ps, j), seed)

def step.k(+put: Bool, h: P.H, +s: U32, +I: M.Ix, +ps: List<&2, Kx>, +seed: U32) -> St:
  match put:
    case True{}:
      put.k(is_some(M.ix.look(I, key(seed))), h, key(seed), s, I, ps, seed)
    case False{}:
      rem.go(nth(ps, Nat.mod(U32.to_nat((seed >> 12n : U32)), len(ps))), h, Nat.mod(U32.to_nat((seed >> 12n : U32)), len(ps)), s, I, ps, seed)

# puts while few are present, removals while many, else by a coin
def coin(+n: Nat, +seed: U32) -> Bool:
  Nat.is_lt(n, 2n) || (Nat.is_lt(n, 48n) && U32.is_eq(((seed >> 20n : U32) .&. 1 : U32), 1))

def run(f: Nat, st: St) -> St:
  match f:
    case 0n:
      st
    case 1n+g:
      match st:
        case St{h, +s, +I, +ps, +seed, +bad, +msg}:
          match bad:
            case True{}:
              St{h, s, I, ps, seed, True{}, msg}
            case False{}:
              run(g, step.k(coin(len(ps), rng(seed)), h, s, I, ps, rng(seed)))

def result(st: St) -> String:
  match st:
    case St{h, +s, +I, +ps, +seed, +bad, +msg}:
      match bad:
        case True{}:
          msg
        case False{}:
          "ok"

def start.s(r: P.H & U32, +seed: U32) -> St:
  (h, +s) = r
  St{fill(h, 400n), s, M.Ept{}, [], seed, False{}, ""}

def start(+seed: U32) -> St:
  start.s(situ(P.h_new()), seed)

def report(+ok: Bool, +s: String) -> String:
  match ok:
    case True{}:
      "ok"
    case False{}:
      s

def both(+a: String, +b: String) -> String:
  report(String.eq(a, "ok") && String.eq(b, "ok"), a ++ " / " ++ b)

def main() -> String:
  both(result(run(600n, start(12345))), result(run(600n, start(777))))
