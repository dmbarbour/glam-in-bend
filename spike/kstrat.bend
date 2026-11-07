import Base
import ./val.bend as V
import ./kprim.bend as P
import ./krules.bend as KR
import ./knet.bend as KN
import ./kmem_grow.bend as KM
import ./net.bend as N
import ./kdemand.bend as KD

# Strategies over a net (heap-strategies in docs/plans/HeapModel_2026-10-27.fast):
# each wraps a net (knet.bend) with state of its own, decides which pair is
# next, and hands the net back when done. The net records none of its
# active pairs: a strategy finds them itself (heap-strategies.stack).

# Eager
# =====

# Pairs last in first out, from a stack of the strategy's own (kprim.bend's
# Stk): built by walking the net for the lower node of each active pair,
# then fed by the eager rewrites, which note the pairs they make.

def scan.push(c: Bool, st: P.Stk, +i: U32) -> P.Stk:
  match c:
    case True{}:
      P.push(st, i)
    case False{}:
      st

# node i's principal faces q: a pair, recorded once, from its lower node;
# a static, no node, from i
def scan.peer(r: P.H & U32, st: P.Stk, +i: U32) -> P.E:
  (h, +q) = r
  P.E{h, scan.push(P.pri(q) && (P.is_static(q) || U32.is_gt(q, i)), st, i)}

def scan.go(live: Bool, h: P.H, st: P.Stk, +i: U32) -> P.E:
  match live:
    case True{}:
      scan.peer(P.rd(h, (i + 1 : U32)), st, i)
    case False{}:
      P.E{h, st}

def scan.hdr(r: P.H & U32, st: P.Stk, +i: U32) -> P.E:
  (h, +hd) = r
  scan.go(U32.is_ne(hd, 0), h, st, i)

# the active pairs among k nodes from word i, onto the stack in node order
def scan(k: Nat, +i: U32, e: P.E) -> P.E:
  match k:
    case 0n:
      e
    case 1n+p:
      match e:
        case P.E{h, st}:
          scan(p, (i + 4 : U32), scan.hdr(P.rd(h, i), st, i))

# the state after a run, and the fuel it left
type Ran is Type:
  Ran{h: P.H, +left: Nat}

def run(n: Nat, +fast: Bool, pp: P.Pop) -> Ran:
  match n:
    case 0n:
      Ran{P.unpop(pp), 0n}
    case 1n+p:
      match pp:
        case P.Pop{h, st, +x, +y, +ok}:
          match ok:
            case True{}:
              run(p, fast, P.pop(KN.interact.e(~KN.go.none.e, h, st, fast, x, y), KR.most_pairs()))
            case False{}:
              Ran{h, 1n+p}

# the same, running events (knet.bend's Events): a loop of its own, so
# that the one without them compiles as it did
def run.v(n: Nat, +fast: Bool, pp: P.Pop) -> Ran:
  match n:
    case 0n:
      Ran{P.unpop(pp), 0n}
    case 1n+p:
      match pp:
        case P.Pop{h, st, +x, +y, +ok}:
          match ok:
            case True{}:
              run.v(p, fast, P.pop(KN.interact.e(~KN.ev.settle.e, h, st, fast, x, y), KR.most_pairs()))
            case False{}:
              Ran{h, 1n+p}

def ran(r: Ran, +fuel: Nat) -> P.H:
  match r:
    case Ran{h, +left}:
      P.count(h, U32.from_nat(Nat.sub(fuel, left)))

def reduce.pop(st: P.Stk, h: P.H, +wcap: U32) -> P.Pop:
  P.pop(scan(U32.to_nat((wcap - P.first() : U32)), P.iface(), P.E{h, st}), KR.most_pairs())

def reduce.st(r: P.H & P.HS, +fuel: Nat, +fast: Bool, +ev: Bool) -> P.H:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      match ev:
        case True{}:
          ran(run.v(fuel, fast, reduce.pop(P.stk_new(P.rs_words(cap)), h, cap)), fuel)
        case False{}:
          ran(run(fuel, fast, reduce.pop(P.stk_new(P.rs_words(cap)), h, cap)), fuel)

# a run of at most fuel interactions, which counts them by the fuel it
# used; the stack, with room for half the nodes, is let go at the end
def reduce_h(+fuel: Nat, +fast: Bool, h: P.H) -> P.H:
  reduce.st(P.stats(h), fuel, fast, False{})

# the same, running events
def reduce_h.v(+fuel: Nat, +fast: Bool, h: P.H) -> P.H:
  reduce.st(P.stats(h), fuel, fast, True{})

# Collection (heap-strategies.erasure.load, after the maintainer's
# heap-strategies.cascade.nongrow): the eager loop, events on, from every
# active pair, rewriting only those a collection may (KR.collects: never
# stuck, no more nodes made than freed, no builtin applied, no need for a
# lazy value touched, fewer ports left than taken) and leaving the rest,
# which the net does not record: erasures, annihilations, beta at one
# level, copies of data. Every rewrite and event of a collection leaves
# the net fewer ports, so its cascade ends
# (heap-strategies.erasure.load.cycle.shrink); controls passing, which
# leave as many, are demand's. Cheap work that carries erasers as far as
# they go, so that a sweep then finds what is cut off; run where a
# demand's net would grow, not per rewrite.

def sel_b(c: Bool, +x: Bool, +y: Bool) -> Bool:
  match c:
    case True{}:
      x
    case False{}:
      y

def coll.bump(e: P.E) -> P.E:
  match e:
    case P.E{h, st}:
      P.E{P.bump(h), st}

# a pair collected, counted, or left
def coll.do(go: Bool, h: P.H, st: P.Stk, +x: U32, +y: U32) -> P.E:
  match go:
    case True{}:
      coll.bump(KN.interact.e(~KN.ev.settle.e, h, st, True{}, x, y))
    case False{}:
      P.E{h, st}

# the pair x - y collected where a collection may
def coll.hy(r: P.H & U32, st: P.Stk, +x: U32, +y: U32, +hx: U32) -> P.E:
  (h, +hy) = r
  coll.do(U32.is_ne(hx, 0) && U32.is_ne(hy, 0) &&
    sel_b(KR.kind_neg(P.rk(hx)), KR.collects(P.rk(hx), P.rk(hy), hx, hy), KR.collects(P.rk(hy), P.rk(hx), hy, hx)), h, st, x, y)

def coll.hx(r: P.H & U32, st: P.Stk, +x: U32, +y: U32) -> P.E:
  (h, +hx) = r
  coll.hy(KN.rdy(h, x, y, hx), st, x, y, hx)

def collect.fin(r: Ran) -> P.H:
  match r:
    case Ran{h, +left}:
      h

# Under demand (heap-strategies.erasure.load.cycle, the maintainer,
# 2026-11-01): a collection is run where the net would otherwise grow:
# the lean trace below, its pairs taken first in first out (P.popq), so
# that they spread over the net rather than following one cascade down,
# at most twice the net's capacity of them looked at. The net doubles
# unless half of it is free after the sweep, so that each collection,
# linear in the capacity, is paid for by the nodes it frees or by the
# doubling: amortized, a constant per node made, at most one live node
# touched per node made (a quarter would be three, the maintainer: space
# bought with speed).

def run.q(n: Nat, q: P.PopQ) -> Ran:
  match n:
    case 0n:
      Ran{P.unpopq(q), 0n}
    case 1n+p:
      match q:
        case P.PopQ{h, st, +x, +y, +ok, +hd}:
          match ok:
            case True{}:
              run.q(p, P.popq(coll.hx(KN.rdx(h, x), st, x, y), KR.most_pairs(), hd))
            case False{}:
              Ran{h, 1n+p}

# The lean trace (heap-strategies.erasure.load.cycle.trace.lean): the
# marking walk from the interface (below) notes each active pair once and
# each eraser or dead operator whose principal faces an auxiliary port
# (an event's B); the sweep's pass frees what it did not reach and counts
# the nodes free; then the noted events run, noting the pairs they make,
# and the noted pairs a collection may rewrite after them, first in first
# out. What they free goes onto the free list at once; what they cut off
# waits for the next collection, as does their part in deciding growth,
# made on the sweep's count: latency traded for one walk and one pass,
# where a scan, a walk and a pass were (the maintainer, 2026-11-01).
# Collecting while tracing, rewriting as the walk reaches pairs, needed a
# barrier and cost twice as much (`.load.cycle.trace`, branch
# gc-trace-proto).

# after the sweep: the net, what the walk noted, and the nodes free
type Mq is Type:
  Mq{h: P.H, st: P.Stk, ws: List<&2, U32>, +free: U32}

def mq.cnt(r: P.H & U32, +free: U32) -> P.H & U32:
  (h, +k) = r
  (h, (free + k : U32))

def mq.ran(r: Ran, +free: U32, +fh0: U32, +cap: U32) -> P.H & U32:
  mq.cnt(P.freed_since(U32.to_nat(cap), collect.fin(r), fh0), free)

def mq.fh(r: P.H & U32, st: P.Stk, ws: List<&2, U32>, +free: U32, +cap: U32) -> P.H & U32:
  (h, +fh0) = r
  mq.ran(run.q(Nat.mul(U32.to_nat(cap), 2n), P.popq(KN.ev.drain.e(4294967295n, KN.Ev{h, st, ws}), KR.most_pairs(), 0)), free, fh0, cap)

# the noted events, then the noted pairs a collection may rewrite; the
# nodes free after them, the sweep's count and those they freed, counted
# down the free list to its head after the sweep (P.freed_since)
def mq.run(m: Mq, +cap: U32) -> P.H & U32:
  match m:
    case Mq{h, st, ws, +free}:
      mq.fh(P.rd(h, P.at_fh()), st, ws, free, cap)

# The walk (the maintainer's, heap-strategies.erasure.load.cycle.walk, in
# its lean form, `.walk.lean`, directed, `.walk.directed.dataflow.walk`):
# from a reference to enter, its node marked already, the walk reads the
# node's head and the link of o1, its first input, and follows only its
# inputs, data's flow reversed: what feeds the interface, never what a
# node provides by another output, which a valid net's demand never
# steps to (net-scoped-arguments). A node of two inputs first pushes the
# link of the second, o2, unless the node behind is marked, marking it
# (so that none is pushed twice); a node with inputs then follows o1's
# link if the node behind is unmarked, marking it; a node with none (data,
# a void), or one whose o1 leads to a marked node, ends the run, and the
# stack's top is entered next. A node is entered by an output, so never
# by a port it follows, and a leaf costs its mark. A pair is noted by its
# negative node, the only one of the two that follows its principal; a
# void whose principal faces an auxiliary port is noted for its event. An
# eraser, having no output, is never entered: the sweep finds those the
# collection needs, and the outputs kept whose consumers it frees (below).
#
# One array, twice the net's capacity, holds it all: the marks, a word
# per 32 nodes, from word 0; the notes from the word after them, an
# event's tagged by its top bit; the stack from the next to last word
# down, the 0 there ending it. Notes and stack entries are of distinct
# nodes, fewer than the capacity, so they never meet. A static link, nil
# among them, finds its mark in the array's last word, set whole from the
# start (lw.mw): it reads as marked, never followed. A static at a node's
# principal is that node's pair, noted; at its other ports, noted as its
# node would have been (Sx, below). The kernel links no port to nil, so
# nil is a net under a fault (`.walk.nil`). The state is five words, the net's data table set aside, and
# each helper is called from one place, so that clang inlines the step
# whole: Bend returns a helper's result through an array its caller
# copies (docs/BendIssues.md, "Records returned through every level,
# where clang will not inline"), and the maintainer's walk first written
# with a nine-word state and helpers shared cost twice as much in the
# default build (`.walk`).

# the walk's state: the net's words (its data table set aside), the walk's
# array, the reference to enter next (its node marked), 0 once done, the
# stack's lowest word and the next note's word
type Lw is Type:
  Lw{w: KM.M, g: KM.M, +c: U32, +n: U32, +q: U32}

# the net's words, the walk's array and the stack's lowest word, after a
# push; and a note pending, 0 for none (lw.p2)
type Gw is Type:
  Gw{w: KM.M, g: KM.M, +n: U32, +e: U32}

# a node's head and the link of its first input, o1
type Nd is Type:
  Nd{w: KM.M, +hd: U32, +l1: U32}

# the node behind link l marked: the array, and 1 if it was already
def lw.mk.v(r: KM.M & U32, +j: U32, +s: U32) -> KM.M & U32:
  (g, +v) = r
  (KM.m_set(g, j, (v .|. (1 << U32.to_nat(s) : U32) : U32)), ((v >> U32.to_nat(s) : U32) .&. 1 : U32))

# a static's mark, nil's among them, is the array's last word, set whole:
# the word index all ones where the port bits are 3 (bit 31 of the word,
# a static's bits 6 to 2 all ones too)
def lw.mw(+l: U32) -> U32:
  ((l >> 7n : U32) .|. (0 - ((((l .&. 3 : U32) + 1 : U32) >> 2n : U32)) : U32) : U32)

def lw.mk(g: KM.M, +l: U32) -> KM.M & U32:
  lw.mk.v(KM.m_get(g, lw.mw(l)), lw.mw(l), ((l >> 2n : U32) .&. 31 : U32))

def nd.l1(r: KM.M & U32, +hd: U32) -> Nd:
  (w, +l1) = r
  Nd{w, hd, l1}

# node b's head and the link of o1, its first input by its kind (KR.
# kind_dir: 3 where it has none, which reads the next node's head, unused)
def nd.hd(r: KM.M & U32, +b: U32) -> Nd:
  (w, +hd) = r
  nd.l1(KM.m_get(w, ((b + 1 : U32) + (KR.kind_dir(P.rk(hd)) .&. 3 : U32) : U32)), hd)

# a run ended: the stack's top entered next, 0 at its bottom ending the
# walk
def lw.pop(r: KM.M & U32, w: KM.M, +n: U32, +q: U32) -> Lw:
  (g, +c) = r
  Lw{w, g, c, (n + 1 : U32), q}

# the walk's array and the next note's word, after a note
type Gq is Type:
  Gq{g: KM.M, +q: U32}

def lw.one(+v: U32) -> U32:
  match v:
    case 0:
      0
    case _:
      1

# notes v and e, either 0 for none, each word written either way
def lw.np2(+v: U32, +e: U32, g: KM.M, +q: U32) -> Gq:
  Gq{KM.m_set(KM.m_set(g, q, v), (q + lw.one(v) : U32), e), ((q + lw.one(v) : U32) + lw.one(e) : U32)}

# b noted as a pair's node where pair holds
def lw.np(pair: Bool, g: KM.M, +q: U32, +b: U32) -> Gq:
  match pair:
    case True{}:
      Gq{KM.m_set(g, q, b), (q + 1 : U32)}
    case False{}:
      Gq{g, q}

# a static (an eraser, nil's value too)
def lw.st(+l: U32) -> Bool:
  P.is_static(l)

def lw.sel(+c: Bool, +x: U32) -> U32:
  match c:
    case True{}:
      x
    case False{}:
      0

# b noted as a pair's node where o1 is its principal and l1 a principal
# or a static (P.pri), both at once: b's principal is negative, an input,
# so that the pair's other node never notes it, and a static has none
def lw.pair(+o1: U32, +l1: U32) -> Bool:
  U32.is_eq((o1 .|. ((l1 + 1 : U32) .&. 2 : U32) : U32), 0)

# o1's link l1 followed if the node behind was unmarked, else the run ends
def lw.f1o(+old: U32, w: KM.M, s: Gq, +n: U32, +l1: U32) -> Lw:
  match old:
    case 0:
      match s:
        case Gq{g, +q}:
          Lw{w, g, l1, n, q}
    case _:
      match s:
        case Gq{g, +q}:
          lw.pop(KM.m_get(g, n), w, n, q)

# b's pair noted, and the pending note, e, where there is one
def lw.nq(+cold: Bool, g: KM.M, +q: U32, +b: U32, +o1: U32, +l1: U32, +e: U32) -> Gq:
  match cold:
    case True{}:
      lw.np2(lw.sel(lw.pair(o1, l1), b), e, g, q)
    case False{}:
      lw.np(lw.pair(o1, l1), g, q, b)

def lw.f1m(r: KM.M & U32, w: KM.M, +n: U32, +q: U32, +b: U32, +o1: U32, +l1: U32, +e: U32) -> Lw:
  (g, +old) = r
  lw.f1o(old, w, lw.nq(U32.is_ne(e, 0), g, q, b, o1, l1, e), n, l1)

def lw.f1(s: Gw, +q: U32, +b: U32, +o1: U32, +l1: U32) -> Lw:
  match s:
    case Gw{w, g, +n, +e}:
      lw.f1m(lw.mk(g, l1), w, n, q, b, o1, l1, e)

# o2's link pushed unless the node behind was marked (a static reads as
# marked)
def lw.push.o(+old: U32, w: KM.M, g: KM.M, +n: U32, +l2: U32) -> Gw:
  match old:
    case 0:
      Gw{w, KM.m_set(g, (n - 1 : U32), l2), (n - 1 : U32), 0}
    case _:
      Gw{w, g, n, 0}

def lw.push(r: KM.M & U32, w: KM.M, +n: U32, +l2: U32) -> Gw:
  (g, +old) = r
  lw.push.o(old, w, g, n, l2)

def lw.p2r(r: KM.M & U32, g: KM.M, +n: U32) -> Gw:
  (w, +l2) = r
  lw.push(lw.mk(g, l2), w, n, l2)

# a static eraser at the other output of a function or a copy, the one
# the walk did not enter by: the boundary the sweep notes where it frees
# an eraser's node facing a kept output (bd.go), pending
def lw.p2o(r: KM.M & U32, g: KM.M, +n: U32, +e: U32) -> Gw:
  (w, +l) = r
  Gw{w, g, n, lw.sel(lw.st(l), e)}

def lw.p2.o(+oth: U32, w: KM.M, g: KM.M, +n: U32, +b: U32) -> Gw:
  match oth:
    case 3:
      Gw{w, g, n, 0}
    case _:
      lw.p2o(KM.m_get(w, ((b + 1 : U32) + oth : U32)), g, n, ((b + oth : U32) .|. 1073741824 : U32))

# The statics a node faces (`.dead-kinds.links.native`), noted as their
# nodes would have been where the collection needs them: at the principal,
# a pair; a static eraser at the second output of a function or a copy, a
# boundary. A node of one input has two outputs at most, so that its
# notes and the nodes it leads to stay two at most, and the notes and the
# stack, entries for distinct nodes, fit the array. A static void at an
# auxiliary input is no event the walk notes: what its node's event would
# do is left to demand, where it gets there.
def lw.p2(+o2: U32, +k: U32, +p: U32, w: KM.M, g: KM.M, +n: U32, +b: U32) -> Gw:
  match o2:
    case 3:
      lw.p2.o(KR.walk_oth(k, p), w, g, n, b)
    case _:
      lw.p2r(KM.m_get(w, ((b + 1 : U32) + o2 : U32)), g, n)

# a void noted where its principal faces an auxiliary port, the note
# tagged by its top bit (its word written either way); the run ends
def lw.lev(r: KM.M & U32, g: KM.M, +n: U32, +q: U32, +b: U32) -> Lw:
  (w, +src) = r
  lw.pop(KM.m_get(KM.m_set(g, q, (b .|. 2147483648 : U32)), n), w, n, (q + (((src .&. 3 : U32) + 3 : U32) >> 2n : U32) : U32))

def lw.leaf(ev: Bool, w: KM.M, g: KM.M, +n: U32, +q: U32, +b: U32) -> Lw:
  match ev:
    case True{}:
      lw.lev(KM.m_get(w, (b + 1 : U32)), g, n, q, b)
    case False{}:
      lw.pop(KM.m_get(g, n), w, n, q)

# by the node's inputs (KR.kind_dir), o1 and o2, 3 for none: a leaf
# without (a free node is never reached), else the second pushed, if
# any, and the first followed
def lw.ar(+o1: U32, +o2: U32, +p: U32, w: KM.M, g: KM.M, +n: U32, +q: U32, +b: U32, +hd: U32, +l1: U32) -> Lw:
  match o1:
    case 3:
      lw.leaf(KR.ev_end(P.rk(hd), 0), w, g, n, q, b)
    case _:
      lw.f1(lw.p2(o2, P.rk(hd), p, w, g, n, b), q, b, o1, l1)

def lw.at(d: Nd, g: KM.M, +n: U32, +q: U32, +b: U32, +c: U32) -> Lw:
  match d:
    case Nd{w, +hd, +l1}:
      lw.ar((KR.kind_dir(P.rk(hd)) .&. 3 : U32), (KR.kind_dir(P.rk(hd)) >> 2n : U32), P.port(c), w, g, n, q, b, hd, l1)

def lw.go(k: Nat, s: Lw) -> Lw:
  match k:
    case 0n:
      s
    case 1n+p:
      match s:
        case Lw{w, g, +c, +n, +q}:
          match c:
            case 0:
              Lw{w, g, 0, n, q}
            case _:
              lw.go(p, lw.at(nd.hd(KM.m_get(w, P.base(c)), P.base(c)), g, n, q, P.base(c), c))

# The sweep (`.walk.directed.dataflow.walk`): KN's pass over the marks, a
# word of 32 nodes at a time, a word all set passed unread
# (`.sweep-full`), each node the walk left unmarked freed with its table
# entry, the nodes free after it counted; and besides, each input of a
# freed node that faces a marked node noted after the walk's notes,
# tagged by bit 30: an output the walk keeps whose consumer goes, to be
# given an eraser once the pass is done (bd.go). Only a freed node's
# inputs can face a marked node, since a marked node's inputs were all
# followed and an output faces an input. The notes' words lie past the
# marks, which the pass reads as they were.
type Sd is Type:
  Sd{h: P.H, g: KM.M, +f: U32, +q: U32}

def sd.rec(+bnd: Bool, h: P.H, g: KM.M, +f: U32, +q: U32, +y: U32) -> Sd:
  match bnd:
    case True{}:
      Sd{h, KM.m_set(g, q, (y .|. 1073741824 : U32)), f, (q + 1 : U32)}
    case False{}:
      Sd{h, g, f, q}

# y noted where the node behind it is marked; a static, nil among them,
# is no node, and goes with the node freed
def sd.yv(r: KM.M & U32, h: P.H, +f: U32, +q: U32, +y: U32) -> Sd:
  (g, +v) = r
  sd.rec(U32.is_ne(((v >> U32.to_nat(((y >> 2n : U32) .&. 31 : U32)) : U32) .&. 1 : U32), 0) && Bool.not(P.is_static(y)), h, g, f, q, y)

def sd.y(r: P.H & U32, g: KM.M, +f: U32, +q: U32) -> Sd:
  (h, +y) = r
  sd.yv(KM.m_get(g, (y >> 7n : U32)), h, f, q, y)

# the node at word b's input o looked at, 3 for none
def sd.in(+o: U32, s: Sd, +b: U32) -> Sd:
  match o:
    case 3:
      s
    case _:
      match s:
        case Sd{h, g, +f, +q}:
          sd.y(P.rd(h, ((b + 1 : U32) + o : U32)), g, f, q)

def sd.free(s: Sd, +i: U32, +hd: U32) -> Sd:
  match s:
    case Sd{h, g, +f, +q}:
      Sd{P.free(KN.sw.payload(KR.is_data(P.rk(hd)), h, i, hd), (i << 2n : U32)), g, (f + 1 : U32), q}

# node i, unmarked: its inputs (KR.kind_dir) looked at, then it is freed
def sd.dead(+dir: U32, s: Sd, +i: U32, +hd: U32) -> Sd:
  sd.free(sd.in((dir >> 2n : U32), sd.in((dir .&. 3 : U32), s, (i << 2n : U32)), (i << 2n : U32)), i, hd)

def sd.mk(+dead: Bool, s: Sd, +i: U32, +hd: U32) -> Sd:
  match dead:
    case True{}:
      sd.dead(KR.kind_dir(P.rk(hd)), s, i, hd)
    case False{}:
      s

def sd.hd0(+hd: U32, h: P.H, g: KM.M, +f: U32, +q: U32, +i: U32, +v: U32) -> Sd:
  match hd:
    case 0:
      Sd{h, g, (f + 1 : U32), q}
    case _:
      sd.mk(U32.is_eq((v .&. KN.rc.bit(i) : U32), 0), Sd{h, g, f, q}, i, hd)

def sd.hd(r: P.H & U32, g: KM.M, +f: U32, +q: U32, +i: U32, +v: U32) -> Sd:
  (h, +hd) = r
  sd.hd0(hd, h, g, f, q, i, v)

# k nodes from node i, all of them in the block whose marks are v
def sd.blk(k: Nat, s: Sd, +i: U32, +v: U32) -> Sd:
  match k:
    case 0n:
      s
    case 1n+p:
      match s:
        case Sd{h, g, +f, +q}:
          sd.blk(p, sd.hd(P.rd(h, (i << 2n : U32)), g, f, q, i, v), (i + 1 : U32), v)

# a block whose nodes were all reached holds none free or dead: passed
def sd.mw.all(+all: Bool, s: Sd, +k: Nat, +i: U32, +v: U32) -> Sd:
  match all:
    case True{}:
      s
    case False{}:
      sd.blk(k, s, i, v)

def sd.mw(r: KM.M & U32, h: P.H, +f: U32, +q: U32, +k: Nat, +i: U32) -> Sd:
  (g, +v) = r
  sd.mw.all(U32.is_eq(v, 4294967295), Sd{h, g, f, q}, k, i, v)

# nb blocks of 32 nodes from block b
def sd.go(nb: Nat, +b: U32, s: Sd) -> Sd:
  match nb:
    case 0n:
      s
    case 1n+p:
      match s:
        case Sd{h, g, +f, +q}:
          sd.go(p, (b + 1 : U32), sd.mw(KM.m_get(g, b), h, f, q, 32n, (b << 5n : U32)))

# the first block's nodes past the header, then the rest
def sd.first(s: Sd, +cap: U32) -> Sd:
  match s:
    case Sd{h, g, +f, +q}:
      sd.go(U32.to_nat(((cap >> 5n : U32) - 1 : U32)), 1, sd.mw(KM.m_get(g, 0), h, f, q, U32.to_nat((32 - P.first() : U32)), P.first()))

# the notes after the sweep, told apart by their top two bits, which no
# reference sets (net-capacity): the pairs slid down to word 3 on, as a
# stack (P.Stk) holds them, the events onto a list, the outputs to give
# erasers onto another
type Sp is Type:
  Sp{g: KM.M, ws: List<&2, U32>, bs: List<&2, U32>, +j: U32}

def sp.ev(+tag: U32, g: KM.M, ws: List<&2, U32>, bs: List<&2, U32>, +j: U32, +v: U32) -> Sp:
  match tag:
    case 0:
      Sp{KM.m_set(g, (j + 3 : U32), v), ws, bs, (j + 1 : U32)}
    case 1:
      Sp{g, ws, Con{(v .&. 1073741823 : U32), bs}, j}
    case _:
      Sp{g, Con{(v .&. 2147483647 : U32), ws}, bs, j}

def sp.v(r: KM.M & U32, ws: List<&2, U32>, bs: List<&2, U32>, +j: U32) -> Sp:
  (g, +v) = r
  sp.ev((v >> 30n : U32), g, ws, bs, j, v)

def sp.go(k: Nat, s: Sp, +i: U32) -> Sp:
  match k:
    case 0n:
      s
    case 1n+p:
      match s:
        case Sp{g, ws, bs, +j}:
          sp.go(p, sp.v(KM.m_get(g, i), ws, bs, j), (i + 1 : U32))

# Each output the walk kept whose consumer the sweep freed
# (`.dead-kinds`). Only a node with two outputs keeps one while losing
# the other, the walk entering a node by an output: a copy, or a
# function, by its variable or its principal.
#
# A copy's output: the copy made the linear copy keeping its other side,
# in place, as the event an eraser there makes (`.dead-kinds.copy`). The
# sweep writes the eraser, so it makes the event there (erasure-at-write),
# specialized: a static put on the port and the table's event run from
# the events' worklist cost each boundary about 780 instructions more,
# collecting demand 0.36% over plain demand against 0.03%, the work alike
# (gcbench runs 227 and 221; `.links.walk.boundary`).
#
# A function's principal, the function reached by its variable alone: a
# copy of a function whose body copying shared, its variable reaching the
# body through the merge of the copies' variables while its own consumer
# is gone, dead in its sharing context; erasing it voids its variable only
# there. Between the fans copying made, its result fed by a copy's output
# and its variable into a merge's input, it is erased in place: both fans
# made linear, keeping their other sides, and the function freed, as its
# erasure and the two events after it would (`.dead-kinds.copied`).
# Elsewhere a static eraser is put on its principal, the pair noted for
# the eval, which erases the function with no node made
# (KN.static_erase). In a net whose variable is used outside its
# function's body, refused when built, the void may reach the interface,
# where demand reports a void demanded instead of the variable
# (net-void-demanded).
#
# A function's variable, unused now: the function made one with its
# variable dead (KFnD, 17), in place, its level kept (`.dead-kinds.fn`).
#
# The free count is the sweep's, plus the functions freed; an eraser made
# is static, no node.

# a fan's linear kind keeping the side other than p: a copy's KCopyR
# (13) or KCopyL (12), a merge's KMergeR (15) or KMergeL (14)
def lin.base(+k: U32) -> U32:
  match k:
    case 3:
      12
    case _:
      14

def lin.side(+p: U32) -> U32:
  match p:
    case 1:
      1
    case _:
      0

# the kept side, port 2, moved to port 1, its peer told, unless static
def lin.mv(r: P.H & U32, +b: U32) -> P.H:
  (h, +l2) = r
  P.link_x(h, (b + 1 : U32), l2)

def lin.port(+p: U32, h: P.H, +b: U32) -> P.H:
  match p:
    case 1:
      lin.mv(P.rd(h, (b + 3 : U32)), b)
    case _:
      h

# the header's kind changed, its fan identity kept; word 3, a two-port
# node's payload word, cleared; counted as the fan's event
def lin.hd(r: P.H & U32, +b: U32, +p: U32) -> P.H:
  (h, +hd) = r
  P.ev_count(P.wr(P.wr(lin.port(p, h, b), b, ((hd .&. 4294967232 : U32) .|. (lin.base(P.rk(hd)) + lin.side(p) : U32) : U32)), (b + 3 : U32), 0), P.rk(hd))

# the fan behind y made linear, y's side dropped
def lin.drop(h: P.H, +y: U32) -> P.H:
  lin.hd(P.rd(h, P.base(y)), P.base(y), P.port(y))

# the function at b made one with its variable dead: its kind changed,
# its level kept, word 3, its variable's link, cleared, a two-port node's
# payload word
def fnd.hd(r: P.H & U32, +b: U32) -> P.H:
  (h, +hd) = r
  P.wr(P.wr(h, b, ((hd .&. 4294967232 : U32) .|. 17 : U32)), (b + 3 : U32), 0)

def fnd.make(h: P.H, +y: U32) -> P.H:
  fnd.hd(P.rd(h, P.base(y)), P.base(y))

def bd.st(+pr: Bool, st: P.Stk, +e: U32) -> P.Stk:
  match pr:
    case True{}:
      P.push(st, e)
    case False{}:
      st

# a static eraser put on y, no node made (`.links.read`): its pair noted
# by y, its event looked at from y
def bd.era(h: P.H, st: P.Stk, ws: List<&2, U32>, +free: U32, +y: U32) -> Mq:
  Mq{P.wr(h, (y + 1 : U32), P.era()), bd.st(U32.is_eq(P.port(y), 0), st, y), KN.evl.add(U32.is_ne(P.port(y), 0), y, ws), free}

# one interaction more in the header's count (P.at_itrs): the erasure
# done in place
def bd.itr(r: P.H & U32) -> P.H:
  (h, +n) = r
  P.wr(h, P.at_itrs(), (n + 1 : U32))

def bd.cp.go(+ok: Bool, h: P.H, st: P.Stk, ws: List<&2, U32>, +free: U32, +f: U32, +a: U32, +b: U32) -> Mq:
  match ok:
    case True{}:
      Mq{bd.itr(P.rd(P.free(lin.drop(lin.drop(h, a), b), f), P.at_itrs())), st, ws, (free + 1 : U32)}
    case False{}:
      bd.era(h, st, ws, free, f)

def bd.cp.hb(r: P.H & U32, st: P.Stk, ws: List<&2, U32>, +free: U32, +f: U32, +a: U32, +b: U32, +ha: U32) -> Mq:
  (h, +hb) = r
  bd.cp.go(U32.is_eq(P.rk(ha), 3) && U32.is_ne(P.port(a), 0) && U32.is_eq(P.rk(hb), 4) && U32.is_ne(P.port(b), 0), h, st, ws, free, f, a, b)

def bd.cp.ha(r: P.H & U32, st: P.Stk, ws: List<&2, U32>, +free: U32, +f: U32, +a: U32, +b: U32) -> Mq:
  (h, +ha) = r
  bd.cp.hb(P.rd(h, P.base(b)), st, ws, free, f, a, b, ha)

def bd.cp.b(r: P.H & U32, st: P.Stk, ws: List<&2, U32>, +free: U32, +f: U32, +a: U32) -> Mq:
  (h, +b) = r
  bd.cp.ha(P.rd(h, P.base(a)), st, ws, free, f, a, b)

# function f reached by its variable alone: its result's peer, then its
# variable's
def bd.cp.a(r: P.H & U32, st: P.Stk, ws: List<&2, U32>, +free: U32, +f: U32) -> Mq:
  (h, +a) = r
  bd.cp.b(P.rd(h, (f + 3 : U32)), st, ws, free, f, a)

def bd.how.p(+ok: Bool, +k: U32) -> U32:
  match ok:
    case True{}:
      k
    case False{}:
      0

def bd.how.fn(+p: U32) -> U32:
  match p:
    case 0:
      2
    case 2:
      3
    case _:
      0

# by what y is, its node of kind k: 1 a copy's output, 2 a function's
# principal, 3 a function's variable, else 0
def bd.how(+k: U32, +y: U32) -> U32:
  match k:
    case 3:
      bd.how.p(U32.is_ne(P.port(y), 0), 1)
    case 1:
      bd.how.fn(P.port(y))
    case _:
      0

def bd.y.go(+how: U32, h: P.H, st: P.Stk, ws: List<&2, U32>, +free: U32, +y: U32) -> Mq:
  match how:
    case 1:
      Mq{lin.drop(h, y), st, ws, free}
    case 2:
      bd.cp.a(P.rd(h, (y + 2 : U32)), st, ws, free, y)
    case 3:
      Mq{fnd.make(h, y), st, ws, free}
    case _:
      bd.era(h, st, ws, free, y)

def bd.y(r: P.H & U32, st: P.Stk, ws: List<&2, U32>, +free: U32, +y: U32) -> Mq:
  (h, +hy) = r
  bd.y.go(bd.how(P.rk(hy), y), h, st, ws, free, y)

def bd.go(bs: List<&2, U32>, m: Mq) -> Mq:
  match bs:
    case Nil{}:
      m
    case Con{+y, t}:
      match m:
        case Mq{h, st, ws, +free}:
          bd.go(t, bd.y(P.rd(h, P.base(y)), st, ws, free, y))

def lw.sp(s: Sp, h: P.H, +free: U32, +cap: U32) -> Mq:
  match s:
    case Sp{g, ws, bs, +j}:
      bd.go(bs, Mq{h, P.stk.fin((KM.m_set(g, 0, j), (cap * 2 : U32))), ws, free})

def lw.sdd(s: Sd, +cap: U32) -> Mq:
  match s:
    case Sd{h, g, +f, +q}:
      lw.sp(sp.go(U32.to_nat((q - (cap >> 5n : U32) : U32)), Sp{g, Nil{}, Nil{}, 0}, (cap >> 5n : U32)), h, f, cap)

# the walk done, the net swept by its marks
def lw.fin(s: Lw, a: Array<V.Val>, +cap: U32) -> Mq:
  match s:
    case Lw{w, g, +c, +n, +q}:
      lw.sdd(sd.first(Sd{P.H{w, a}, g, 0, q}, cap), cap)

# the walk's start: the interface marked, the array's last word set
# whole, the interface's one link followed; the stack's lowest word the
# next to last, 0
def lw.s1(r: KM.M & U32, w: KM.M, +n: U32, +q: U32, +l: U32) -> Lw:
  (g, +old) = r
  Lw{w, g, (l .&. (old - 1 : U32) : U32), n, q}

def lw.s0(r: KM.M & U32, g: KM.M, +n: U32, +q: U32) -> Lw:
  (w, +l) = r
  lw.s1(lw.mk(g, l), w, n, q, l)

def lw.g0(r: KM.M & U32, w: KM.M, +cap: U32) -> Lw:
  (g, +sz) = r
  lw.s0(KM.m_get(w, (P.iface() + 1 : U32)),
    KM.m_set(KM.m_set(g, (sz - 1 : U32), 4294967295), 0, KN.rc.bit((P.iface() >> 2n : U32))), (sz - 2 : U32), (cap >> 5n : U32))

# the net walked and swept, its data table set aside meanwhile
def lw.h(h: P.H, +cap: U32) -> Mq:
  match h:
    case P.H{w, a}:
      lw.fin(lw.go(4294967295n, lw.g0(KM.m_new(Nat.add(KM.depth(32n, cap, 0n), 1n), P.w_maxd()), w, cap)), a, cap)

def lean.st(r: P.H & P.HS) -> P.H & U32:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      mq.run(lw.h(h, cap), cap)

# a net collected by the lean trace: marked, swept, then its noted events
# and collectable pairs run; the net, and its free nodes after the sweep
def collect_lean(h: P.H) -> P.H & U32:
  lean.st(P.stats(h))

def cyc.grow(+ok: Bool, h: P.H) -> P.H & Bool:
  match ok:
    case True{}:
      (h, True{})
    case False{}:
      P.grow_more(h)

def cyc.cap(r: P.H & P.HS, +free: U32) -> P.H & Bool:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      cyc.grow(U32.is_ge((free * 2 : U32), cap), h)

def cyc.sw(r: P.H & U32) -> P.H & Bool:
  (h, +free) = r
  cyc.cap(P.stats(h), free)

# a collection under demand, counted (P.cycle): the lean trace, and the
# net doubled unless half of it is then free; whether it has room, false
# only where it had to grow and could not
def collect_cycle(h: P.H) -> P.H & Bool:
  cyc.sw(collect_lean(P.cycle(h)))

# Two stacks
# ==========

# Eager, the pairs whose rewrite grows the net put off (heap-strategies.
# twostack): pairs are noted at the near end of the stack's array as the
# eager strategy notes them, and sorted as popped: one that grows (KR.grows,
# from the rule table) moves to the far end, the rest interact, and the
# far end is drained only when the near is empty. Erasures, annihilations
# and their cascades so run before anything is copied. A pair moves once
# at most, so the run takes twice its fuel in steps.

def two.ori(neg: Bool, +hx: U32, +hy: U32) -> Bool:
  match neg:
    case True{}:
      KR.grows(P.rk(hx), P.rk(hy), hx, hy)
    case False{}:
      KR.grows(P.rk(hy), P.rk(hx), hy, hx)

def two.hy(r: P.H & U32, +hx: U32) -> P.H & Bool:
  (h, +hy) = r
  (h, two.ori(KR.kind_neg(P.rk(hx)), hx, hy))

def two.hx(r: P.H & U32, +x: U32, +y: U32) -> P.H & Bool:
  (h, +hx) = r
  two.hy(KN.rdy(h, x, y, hx), hx)

# would the pair x - y grow the net? (either may be static: KN.rdx,
# KN.rdy)
def two.grows(h: P.H, +x: U32, +y: U32) -> P.H & Bool:
  two.hx(KN.rdx(h, x), x, y)

# the pair x - y reduced, unless the fuel's interactions are made: then the
# run ends with the pair left
def two.int(~after: P.E -> @+x:N.Ext -> P.E, more: Bool, h: P.H, st: P.Stk, +fast: Bool, +x: U32, +y: U32, +k: U32) -> P.Pop2:
  match more:
    case True{}:
      P.pop2(KN.interact.e(~after, h, st, fast, x, y), KR.most_pairs(), (k + 1 : U32))
    case False{}:
      P.Pop2{h, st, x, y, 0, k}

def two.go(~after: P.E -> @+x:N.Ext -> P.E, g: Bool, h: P.H, st: P.Stk, +fast: Bool, +x: U32, +y: U32, +k: U32, +lim: U32) -> P.Pop2:
  match g:
    case True{}:
      P.pop2(P.E{h, P.far_push(st, x)}, KR.most_pairs(), k)
    case False{}:
      two.int(~after, U32.is_lt(k, lim), h, st, fast, x, y, k)

# a pair from the near end: deferred if it grows, else reduced
def two.near(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & Bool, st: P.Stk, +fast: Bool, +x: U32, +y: U32, +k: U32, +lim: U32) -> P.Pop2:
  (h, +g) = r
  two.go(~after, g, h, st, fast, x, y, k, lim)

# lim interactions at most, in n steps
def run2(n: Nat, +fast: Bool, +lim: U32, q: P.Pop2) -> P.H:
  match n:
    case 0n:
      P.unpop2(q)
    case 1n+p:
      match q:
        case P.Pop2{h, st, +x, +y, +src, +k}:
          match src:
            case 0:
              P.count(h, k)
            case 1:
              run2(p, fast, lim, two.near(~KN.go.none.e, two.grows(h, x, y), st, fast, x, y, k, lim))
            case _:
              run2(p, fast, lim, two.int(~KN.go.none.e, U32.is_lt(k, lim), h, st, fast, x, y, k))

# the same, running events
def run2.v(n: Nat, +fast: Bool, +lim: U32, q: P.Pop2) -> P.H:
  match n:
    case 0n:
      P.unpop2(q)
    case 1n+p:
      match q:
        case P.Pop2{h, st, +x, +y, +src, +k}:
          match src:
            case 0:
              P.count(h, k)
            case 1:
              run2.v(p, fast, lim, two.near(~KN.ev.settle.e, two.grows(h, x, y), st, fast, x, y, k, lim))
            case _:
              run2.v(p, fast, lim, two.int(~KN.ev.settle.e, U32.is_lt(k, lim), h, st, fast, x, y, k))

def reduce2.pop(h: P.H, +cap: U32) -> P.Pop2:
  P.pop2(scan(U32.to_nat((cap - P.first() : U32)), P.iface(), P.E{h, P.stk_new(P.rs_words(cap))}), KR.most_pairs(), 0)

def reduce2.st(r: P.H & P.HS, +fuel: Nat, +fast: Bool, +ev: Bool) -> P.H:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      match ev:
        case True{}:
          run2.v(Nat.mul(fuel, 2n), fast, U32.from_nat(fuel), reduce2.pop(h, cap))
        case False{}:
          run2(Nat.mul(fuel, 2n), fast, U32.from_nat(fuel), reduce2.pop(h, cap))

# reduce_h with two stacks: at most fuel interactions
def reduce2_h(+fuel: Nat, +fast: Bool, h: P.H) -> P.H:
  reduce2.st(P.stats(h), fuel, fast, False{})

# the same, running events
def reduce2_h.v(+fuel: Nat, +fast: Bool, h: P.H) -> P.H:
  reduce2.st(P.stats(h), fuel, fast, True{})

# Profiling
# =========

# The eager strategy counting what it does (heap-strategies.profile): its
# interactions by pair of kinds, A's principal negative as in the rule
# table, and each as the logical interactions it stands for, were every
# run of raises its unit brackets (ctlwire.py --logical): a run of b
# meeting any other node, b; two runs at different indices, each unit of
# one crossing each unit of the other, b times c; facing at one index,
# what cancels, the shorter of two raises, or else 1, a drop and a unit
# once peeling has split off the rest of a longer run. The logical
# interactions are the unit brackets' interactions, as many in every
# order of a complete reduction whether controls fuse or not; fusion's
# savings are they less the interactions made, and may depend on order.

# interactions by pair of classes (A's class times 32 plus B's: KR.class,
# each base kind its own, the operators one), the logical
# interactions in two words, the pairs peeled, and the interactions whose
# logical count would pass 2^32, left out of it
type Pf is Type:
  Pf{kp: KM.M, +lo: U32, +hi: U32, +peels: U32, +wide: U32}

def pf_new.go(r: KM.M & U32) -> Pf:
  (kp, +cap) = r
  Pf{kp, 0, 0, 0, 0}

def pf_new() -> Pf:
  pf_new.go(KM.m_new(10n, 10n))

def is_ctl(+k: U32) -> Bool:
  U32.is_eq(k, 10) || U32.is_eq(k, 11)

def one_if(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

# runs of b and c crossing: b times c, and whether that passes 2^32
def lg.cross(+b: U32, +c: U32) -> U32 & Bool:
  ((b * c : U32), U32.is_gt(c, (4294967295 / P.sel_u(U32.is_eq(b, 0), 1, b) : U32)))

def lg.same(up: Bool, +b: U32, +c: U32) -> U32:
  match up:
    case True{}:
      P.sel_u(U32.is_lt(b, c), b, c)
    case False{}:
      1

def lg.cc(same: Bool, +oa: U32, +ob: U32) -> U32 & Bool:
  match same:
    case True{}:
      (lg.same(P.off_up(oa) && P.off_up(ob), P.off_by(oa), P.off_by(ob)), False{})
    case False{}:
      lg.cross(P.off_by(oa), P.off_by(ob))

def logical.k(ca: Bool, cb: Bool, +ha: U32, +hb: U32, +oa: U32, +ob: U32) -> U32 & Bool:
  match ca cb:
    case True{} True{}:
      lg.cc(U32.is_eq(P.fld(ha), P.fld(hb)), oa, ob)
    case True{} False{}:
      (P.off_by(oa), False{})
    case False{} True{}:
      (P.off_by(ob), False{})
    case False{} False{}:
      (1, False{})

# the unit interactions A (header ha, word 3 oa) meeting B stands for
def logical(+ha: U32, +hb: U32, +oa: U32, +ob: U32) -> U32 & Bool:
  logical.k(is_ctl(P.rk(ha)), is_ctl(P.rk(hb)), ha, hb, oa, ob)

# does peeling split either control? (kprim.bend's peel_ctl)
def peeled(+ha: U32, +hb: U32, +oa: U32, +ob: U32) -> Bool:
  U32.is_eq(P.rk(ha), 10) && U32.is_eq(P.rk(hb), 11) && U32.is_eq(P.fld(ha), P.fld(hb)) &&
    U32.is_ne((P.peel.amt(P.off_up(oa), P.off_by(oa), P.off_up(ob), P.off_by(ob)) +
      P.peel.amt(P.off_up(ob), P.off_by(ob), P.off_up(oa), P.off_by(oa)) : U32), 0)

def pf.fin(kp: KM.M, +lo: U32, +hi: U32, +peels: U32, +wide: U32, +w: U32, +pl: Bool, +wd: Bool) -> Pf:
  Pf{kp, (lo + w : U32), (hi + one_if(U32.is_lt((lo + w : U32), lo)) : U32), (peels + one_if(pl) : U32), (wide + one_if(wd) : U32)}

def pf.kp(r: KM.M & U32, +i: U32, +lo: U32, +hi: U32, +peels: U32, +wide: U32, +w: U32, +pl: Bool, +wd: Bool) -> Pf:
  (kp, +n) = r
  pf.fin(KM.m_set(kp, i, (n + 1 : U32)), lo, hi, peels, wide, P.sel_u(wd, 0, w), pl, wd)

def pf.w(r: U32 & Bool, pf: Pf, +i: U32, +pl: Bool) -> Pf:
  (+w, +wd) = r
  match pf:
    case Pf{kp, +lo, +hi, +peels, +wide}:
      pf.kp(KM.m_get(kp, i), i, lo, hi, peels, wide, w, pl, wd)

# A (header ha, word 3 oa) meeting B, counted
def pf.add(pf: Pf, +ha: U32, +hb: U32, +oa: U32, +ob: U32) -> Pf:
  pf.w(logical(ha, hb, oa, ob), pf, ((KR.class(P.rk(ha)) << 5n : U32) + KR.class(P.rk(hb)) : U32), peeled(ha, hb, oa, ob))

def pr.or(neg: Bool, pf: Pf, +hx: U32, +hy: U32, +ox: U32, +oy: U32) -> Pf:
  match neg:
    case True{}:
      pf.add(pf, hx, hy, ox, oy)
    case False{}:
      pf.add(pf, hy, hx, oy, ox)

def pr.oy(r: P.H & U32, pf: Pf, +hx: U32, +hy: U32, +ox: U32) -> P.H & Pf:
  (h, +oy) = r
  (h, pr.or(KR.kind_neg(P.rk(hx)), pf, hx, hy, ox, oy))

def pr.ox(r: P.H & U32, pf: Pf, +y: U32, +hx: U32, +hy: U32) -> P.H & Pf:
  (h, +ox) = r
  pr.oy(P.rd(h, (y + 3 : U32)), pf, hx, hy, ox)

def pr.hy(r: P.H & U32, pf: Pf, +x: U32, +y: U32, +hx: U32) -> P.H & Pf:
  (h, +hy) = r
  pr.ox(P.rd(h, (x + 3 : U32)), pf, y, hx, hy)

def pr.hx(r: P.H & U32, pf: Pf, +x: U32, +y: U32) -> P.H & Pf:
  (h, +hx) = r
  pr.hy(KN.rdy(h, x, y, hx), pf, x, y, hx)

# the pair x - y, counted before it interacts, a static by its eraser's
# kind (static-links-count-as-nodes)
def probe(h: P.H, pf: Pf, +x: U32, +y: U32) -> P.H & Pf:
  pr.hx(KN.rdx(h, x), pf, x, y)

# the state after a profiled run, and the fuel it left
type PRan is Type:
  PRan{h: P.H, pf: Pf, +left: Nat}

# the next pair, and the profile
type PPop is Type:
  PPop{pp: P.Pop, pf: Pf}

# the pair x - y, counted, interacts; the next is popped
def pstep(~after: P.E -> @+x:N.Ext -> P.E, r: P.H & Pf, st: P.Stk, +fast: Bool, +x: U32, +y: U32) -> PPop:
  (h, pf) = r
  PPop{P.pop(KN.interact.e(~after, h, st, fast, x, y), KR.most_pairs()), pf}

def prun(n: Nat, +fast: Bool, q: PPop) -> PRan:
  match n:
    case 0n:
      match q:
        case PPop{pp, pf}:
          PRan{P.unpop(pp), pf, 0n}
    case 1n+p:
      match q:
        case PPop{pp, pf}:
          match pp:
            case P.Pop{h, st, +x, +y, +ok}:
              match ok:
                case True{}:
                  prun(p, fast, pstep(~KN.go.none.e, probe(h, pf, x, y), st, fast, x, y))
                case False{}:
                  PRan{h, pf, 1n+p}

# the same, running events, which the net counts by kind (P.evk) and the
# profile leaves out of the logical interactions: they are patterns
# recognized, not interactions (heap-strategies.erasure.kernel)
def prun.v(n: Nat, +fast: Bool, q: PPop) -> PRan:
  match n:
    case 0n:
      match q:
        case PPop{pp, pf}:
          PRan{P.unpop(pp), pf, 0n}
    case 1n+p:
      match q:
        case PPop{pp, pf}:
          match pp:
            case P.Pop{h, st, +x, +y, +ok}:
              match ok:
                case True{}:
                  prun.v(p, fast, pstep(~KN.ev.settle.e, probe(h, pf, x, y), st, fast, x, y))
                case False{}:
                  PRan{h, pf, 1n+p}

def pran(r: PRan, +fuel: Nat) -> P.H & Pf:
  match r:
    case PRan{h, pf, +left}:
      (P.count(h, U32.from_nat(Nat.sub(fuel, left))), pf)

def reduce_p.go(st: P.Stk, h: P.H, +wcap: U32, +fuel: Nat, +fast: Bool, +ev: Bool) -> P.H & Pf:
  match ev:
    case True{}:
      pran(prun.v(fuel, fast, PPop{reduce.pop(st, h, wcap), pf_new()}), fuel)
    case False{}:
      pran(prun(fuel, fast, PPop{reduce.pop(st, h, wcap), pf_new()}), fuel)

def reduce_p.st(r: P.H & P.HS, +fuel: Nat, +fast: Bool, +ev: Bool) -> P.H & Pf:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      reduce_p.go(P.stk_new(P.rs_words(cap)), h, cap, fuel, fast, ev)

# reduce_h, profiled
def reduce_p(+fuel: Nat, +fast: Bool, h: P.H) -> P.H & Pf:
  reduce_p.st(P.stats(h), fuel, fast, False{})

# reduce_h.v, profiled
def reduce_p.v(+fuel: Nat, +fast: Bool, h: P.H) -> P.H & Pf:
  reduce_p.st(P.stats(h), fuel, fast, True{})

def pf.one(+i: U32, +n: U32) -> String:
  match n:
    case 0:
      ""
    case _:
      " " ++ U32.show((i >> 5n : U32)) ++ "." ++ U32.show((i .&. 31 : U32)) ++ ":" ++ U32.show(n)

def pf.pairs(k: Nat, r: KM.M & U32, +i: U32) -> String:
  match k:
    case 0n:
      match r:
        case (kp, +n):
          pf.one(i, n)
    case 1n+p:
      match r:
        case (kp, +n):
          pf.one(i, n) ++ pf.pairs(p, KM.m_get(kp, (i + 1 : U32)), (i + 1 : U32))

def pf.big(small: Bool, +lo: U32, +hi: U32) -> String:
  match small:
    case True{}:
      Nat.show(Nat.add(Nat.mul(Nat.mul(U32.to_nat(hi), 65536n), 65536n), U32.to_nat(lo)))
    case False{}:
      "past 2^48"

# the profile as text: logical interactions, peels, interactions left out
# of them, and interactions by pair of kinds, A's code then B's
def pf_str(pf: Pf) -> String:
  match pf:
    case Pf{kp, +lo, +hi, +peels, +wide}:
      "logical " ++ pf.big(U32.is_lt(hi, 65536), lo, hi) ++ ", " ++ U32.show(peels) ++ " peels, " ++
        U32.show(wide) ++ " wide; pairs" ++ pf.pairs(1023n, KM.m_get(kp, 0), 0)

# Demand
# ======

# Demand's walk toward the interface lives in kdemand.blend, an object
# for each family (KD.Demand, KD.DemandEv) extending the chain of
# kchain.blend (blend-kernel-chain.slice); its path and state are
# kdemand's D. Here, collecting demand's chunks, a demand's start, its
# need and its resume.

# Collecting by chunks (heap-strategies.erasure.load.cycle.reserve, the
# maintainer's batching, 2026-11-01): a step makes one interaction at
# most, and an interaction takes two free nodes at most, so S steps take
# 2S at most. The collecting demand runs plain demand's loop (demand.go)
# S steps at a time, asking nothing; before each chunk it sees a reserve
# of 2S free nodes kept off the free list (P.reserve), which the
# allocator takes where its list runs dry, rather than growing, noting
# that it did (P.at_tap). Where a chunk ends with the reserve taken, the
# net is collected (collect_cycle) and the walk starts again from the
# interface, its path's array kept: a collection comes between steps, so
# it may rewrite any pair it may, the path's own among them, and no pair
# is left out. S is the net's capacity over 64, and at least 16 steps
# (heap-strategies.erasure.load.cycle.chunks.floor: a chunk costs some
# 240 instructions, at most 15 a step so), the reserve twice it: the
# floor binds below 1024 nodes, where the reserve of 32 nodes is more
# than a 32nd.
# A net that had to grow and could not: out of memory (6), the runtime's
# error.

# what a chunk leaves: the walk, its steps left, and whether the next
# chunk's end collects whatever the reserve (the stress test)
type Dl is Type:
  Dl{+left: U32, +force: Bool, d: KD.D}

def rs.k(r: P.H & P.HS) -> P.H & Bool:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      P.reserve(U32.to_nat(U32.max((cap >> 5n : U32), 32)), h)

def rs.grown.go(+ok: Bool, h: P.H) -> P.H & Bool:
  match ok:
    case True{}:
      rs.k(P.stats(h))
    case False{}:
      (h, False{})

def rs.grown(r: P.H & Bool) -> P.H & Bool:
  (h, +ok) = r
  rs.grown.go(ok, h)

def rs.got.go(+ok: Bool, h: P.H) -> P.H & Bool:
  match ok:
    case True{}:
      (h, True{})
    case False{}:
      rs.grown(P.grow_more(h))

def rs.got(r: P.H & Bool) -> P.H & Bool:
  (h, +ok) = r
  rs.got.go(ok, h)

# a reserve kept, a 32nd of the net and 32 nodes at least, the net
# doubled first where its free list lacks one; false where it could not
# grow
def dc.reserve(h: P.H) -> P.H & Bool:
  rs.got(rs.k(P.stats(h)))

def dc.steps(+force: Bool, +cap: U32) -> U32:
  match force:
    case True{}:
      16
    case False{}:
      U32.max((cap >> 6n : U32), 16)

# the loop's next move, planned between moves: 0 the end, 1 a
# collection, 2 a chunk of so many steps from a reserve seen kept. The
# planning reads the net and inlines; the loop makes one call a move into
# what may suspend (demand.go, collect_cycle), where a chunk's helpers,
# each calling into them, had cost some 590 instructions a chunk, now
# some 240 (heap-strategies.erasure.load.cycle.chunks).
type Dp is Type:
  Dp{+act: U32, +steps: U32, +left: U32, +force: Bool, d: KD.D}

def dc.pk.rs(r: P.H & Bool, path: KM.M, +top: U32, +depth: U32, +n: U32, +steps: U32, +left: U32, +force: Bool) -> Dp:
  (h, +ok) = r
  match ok:
    case True{}:
      Dp{2, steps, left, force, KD.D{h, path, top, depth, n, 0}}
    case False{}:
      Dp{0, 0, left, force, KD.d.stop(h, path, top, depth, n, 6)}

# a chunk: S steps, or those left, from a reserve seen kept; a stress test collects at its end whatever the
# reserve where the net holds 1024 nodes or fewer, the chunk then 16
# steps: the walk starting again from the interface after a collection
# takes a step for each power of two in its depth (kdemand.blend's wk.push), at most 11
# in such a net, so a chunk of 4 made no progress
def dc.pk(r: P.H & P.HS, path: KM.M, +top: U32, +depth: U32, +n: U32, +left: U32, +stress: Bool) -> Dp:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      dc.pk.rs(dc.reserve(h), path, top, depth, n, U32.min(dc.steps(stress && U32.is_le(cap, 1024), cap), left),
        left, stress && U32.is_le(cap, 1024))

# a chunk next, unless the walk stopped or its steps ran out
def dc.chunk.go(+stop: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +left: U32, +stress: Bool) -> Dp:
  match stop:
    case True{}:
      Dp{0, 0, left, False{}, KD.D{h, path, top, depth, n, st}}
    case False{}:
      dc.pk(P.stats(h), path, top, depth, n, left, stress)

def dc.chunk(s: Dl, +stress: Bool) -> Dp:
  match s:
    case Dl{+left, +force, d}:
      match d:
        case KD.D{h, path, +top, +depth, +n, +st}:
          dc.chunk.go(U32.is_eq(left, 0) || U32.is_ne(st, 0), h, path, top, depth, n, st, left, stress)

def dc.ok(+ok: Bool, h: P.H, path: KM.M, +n: U32, +left: U32, +force: Bool) -> Dl:
  match ok:
    case True{}:
      Dl{left, force, KD.d.go(h, path, P.iface(), 0, n)}
    case False{}:
      Dl{left, force, KD.d.stop(h, path, P.iface(), 0, n, 6)}

def dc.col(r: P.H & Bool, path: KM.M, +n: U32, +left: U32, +force: Bool) -> Dl:
  (h, +ok) = r
  dc.ok(ok, h, path, n, left, force)

def dc.tap.go(+col: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +left: U32, +force: Bool, +stress: Bool) -> Dp:
  match col:
    case True{}:
      Dp{1, 0, left, force, KD.D{h, path, top, depth, n, st}}
    case False{}:
      dc.chunk.go(U32.is_eq(left, 0) || U32.is_ne(st, 0), h, path, top, depth, n, st, left, stress)

def dc.tap(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +left: U32, +force: Bool, +stress: Bool) -> Dp:
  (h, +tap) = r
  dc.tap.go((U32.is_ne(tap, 0) || force) && U32.is_eq(st, 0), h, path, top, depth, n, st, left, force, stress)

# a chunk's end: the net collected where the reserve was taken, else the
# next chunk
def dc.after(d: KD.D, +left: U32, +force: Bool, +stress: Bool) -> Dp:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      dc.tap(P.rd(h, P.at_tap()), path, top, depth, n, st, left, force, stress)

def dc.loop(k: Nat, s: Dp, +stress: Bool) -> KD.D:
  match k:
    case 0n:
      match s:
        case Dp{+act, +steps, +left, +force, d}:
          KD.d.end(d)
    case 1n+p:
      match s:
        case Dp{+act, +steps, +left, +force, d}:
          match act:
            case 1:
              match d:
                case KD.D{h, path, +top, +depth, +n, +st}:
                  dc.loop(p, dc.chunk(dc.col(collect_cycle(h), path, n, left, force), stress), stress)
            case 2:
              dc.loop(p, dc.after(KD.Demand.demand.go(U32.to_nat(steps), d), (left - steps : U32), force, stress), stress)
            case _:
              KD.d.end(d)

# demand collecting where its net would grow, for at most k steps
def demand.c(+k: Nat, d: KD.D) -> KD.D:
  dc.loop(k, dc.chunk(Dl{U32.from_nat(k), False{}, d}, False{}), False{})

# the same as a stress test (heap-strategies.erasure.load.cycle.stress):
# a net of 1024 nodes or fewer collected every 16 steps
def demand.s(+k: Nat, d: KD.D) -> KD.D:
  dc.loop(k, dc.chunk(Dl{U32.from_nat(k), False{}, d}, True{}), True{})

def d.path(r: KM.M & U32) -> KM.M:
  (m, +cap) = r
  KM.m_set(m, 0, cap)

def d.start(h: P.H) -> KD.D:
  KD.d.go(h, d.path(KM.m_new(6n, P.w_maxd())), P.iface(), 0, 0)

# A demand waiting on a lazy value keeps nothing for it. Stopped (state
# 2), its top is the application or strict call, unchanged, its principal
# port facing the data node that holds the handle: the need is read from
# the net when asked (need), the node found again when the value comes
# (resume). A task reports that it waits and on what; the scheduler holds
# the handle while it does (the maintainer, 2026-10-30).

def at.ori(neg: Bool, +top: U32, +y: U32) -> U32:
  match neg:
    case True{}:
      y
    case False{}:
      top

def at.hx(r: P.H & U32, +top: U32, +y: U32) -> P.H & U32:
  (h, +hx) = r
  (h, at.ori(KR.kind_neg(P.rk(hx)), top, y))

def at.q(r: P.H & U32, +top: U32) -> P.H & U32:
  (h, +q) = r
  at.hx(P.rd(h, top), top, P.base(q))

# the data node a stopped demand waits on: of top and its principal
# partner, the one whose principal port is positive
def d.at(h: P.H, +top: U32) -> P.H & U32:
  at.q(P.rd(h, (top + 1 : U32)), top)

def resume.put(r: P.H & P.PW, +at: U32) -> P.H:
  (h, pw) = r
  match pw:
    case P.PW{+m, +f, +w}:
      P.wr(P.wr(h, at, P.hd2(5, m, f)), (at + 2 : U32), w)

def resume.pb(r: P.H & U32, +at: U32, +hb: U32, v: V.Val) -> P.H:
  (h, +pb) = r
  resume.put(P.put(P.drop(h, P.form(hb), pb), v), at)

def resume.hb(r: P.H & U32, +at: U32, v: V.Val) -> P.H:
  (h, +hb) = r
  resume.pb(P.rd(h, (at + 2 : U32)), at, hb, v)

def resume.b(r: P.H & U32, v: V.Val) -> P.H:
  (h, +at) = r
  resume.hb(P.rd(h, at), at, v)

# a need met: the data node holding the handle holds v instead, and the
# walk goes on where it stopped
def resume(d: KD.D, v: V.Val) -> KD.D:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      KD.d.go(resume.b(d.at(h, top), v), path, top, depth, n)

def need.z(z: P.Lz, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> KD.D & U32:
  match z:
    case P.Lz{h, +lazy, +k}:
      (KD.D{h, path, top, depth, n, st}, k)

def need.pb(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +hb: U32) -> KD.D & U32:
  (h, +pb) = r
  need.z(P.val_lazy(h, P.form(hb), pb), path, top, depth, n, st)

def need.hb(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +b: U32) -> KD.D & U32:
  (h, +hb) = r
  need.pb(P.rd(h, (b + 2 : U32)), path, top, depth, n, st, hb)

def need.b(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> KD.D & U32:
  (h, +b) = r
  need.hb(P.rd(h, b), path, top, depth, n, st, b)

def need.go(w: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> KD.D & U32:
  match w:
    case True{}:
      need.b(d.at(h, top), path, top, depth, n, st)
    case False{}:
      (KD.D{h, path, top, depth, n, st}, 0)

# the handle a demand stopped needing (state 2), read from the net; 0 in
# any other state
def need(d: KD.D) -> KD.D & U32:
  match d:
    case KD.D{h, path, +top, +depth, +n, +st}:
      need.go(U32.is_eq(st, 2), h, path, top, depth, n, st)

