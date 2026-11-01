import Base
import ./val.bend as V
import ./kprim.bend as P
import ./krules.bend as KR
import ./knet.bend as KN
import ./kmem_grow.bend as KM
import ./net.bend as N

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

# node i's principal faces q: a pair, recorded once, from its lower node
def scan.peer(r: P.H & U32, st: P.Stk, +i: U32) -> P.E:
  (h, +q) = r
  P.E{h, scan.push(U32.is_eq(P.port(q), 0) && U32.is_gt(q, i), st, i)}

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
# lazy value touched) and leaving the rest, which the net does not
# record: erasures, annihilations, beta at one level, copies of data,
# controls passing what they may. Cheap work that carries erasers as far
# as they go, so that a sweep then finds what is cut off; run where a
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
  coll.hy(P.rd(h, P.base(y)), st, x, y, hx)

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
              run.q(p, P.popq(coll.hx(P.rd(h, x), st, x, y), KR.most_pairs(), hd))
            case False{}:
              Ran{h, 1n+p}

# The lean trace (heap-strategies.erasure.load.cycle.trace.lean): the
# marking walk from the interface notes, as it reaches them, the active
# pairs (from their lower node) onto the queue and the nodes that may be
# an event's B (KR.ev_end at the principal: an eraser, a dead operator)
# onto the events' worklist; the sweep's pass frees what it did not reach
# and counts the nodes free; then the events run, noting the pairs they
# make, and the queue's collectable pairs after them, first in first out.
# What they free goes onto the free list at
# once; what they cut off waits for the next collection, as does their
# part in deciding growth, made on the sweep's count: latency traded for
# one walk and one pass, where a scan, a walk and a pass were (the
# maintainer, 2026-11-01). Collecting while tracing, rewriting as the
# walk reaches pairs, needed a barrier and cost twice as much
# (`.load.cycle.trace`, branch gc-trace-proto).

type Rq is Type:
  Rq{h: P.H, st: P.Stk, ws: List<&2, U32>, mk: KM.M, wl: KM.M, +n: U32}

def rq.push(new: Bool, h: P.H, st: P.Stk, ws: List<&2, U32>, mk: KM.M, wl: KM.M, +n: U32, +j: U32) -> Rq:
  match new:
    case True{}:
      Rq{h, st, ws, mk, KM.m_set(wl, n, j), (n + 1 : U32)}
    case False{}:
      Rq{h, st, ws, mk, wl, n}

def rq.mark(r: KM.M & U32, h: P.H, st: P.Stk, ws: List<&2, U32>, wl: KM.M, +n: U32, +j: U32) -> Rq:
  (mk, +v) = r
  rq.push(U32.is_eq((v .&. KN.rc.bit(j) : U32), 0), h, st, ws, KM.m_set(mk, (j >> 5n : U32), (v .|. KN.rc.bit(j) : U32)), wl, n, j)

def rq.see.go(ok: Bool, s: Rq, +j: U32) -> Rq:
  match ok:
    case True{}:
      match s:
        case Rq{h, st, ws, mk, wl, +n}:
          rq.mark(KM.m_get(mk, (j >> 5n : U32)), h, st, ws, wl, n, j)
    case False{}:
      s

# the node behind reference p marked, and put on the worklist if new
def rq.see(+p: U32, s: Rq) -> Rq:
  rq.see.go(U32.is_ne(p, P.nil()), s, (p >> 2n : U32))

def rq.port.r(r: P.H & U32, st: P.Stk, ws: List<&2, U32>, mk: KM.M, wl: KM.M, +n: U32) -> Rq:
  (h, +q) = r
  rq.see(q, Rq{h, st, ws, mk, wl, n})

def rq.port(s: Rq, +b: U32, +p: U32) -> Rq:
  match s:
    case Rq{h, st, ws, mk, wl, +n}:
      rq.port.r(P.rd(h, ((b + 1 : U32) + p : U32)), st, ws, mk, wl, n)

# the auxiliary ports of a node of arity a at word b, seen
def rq.aux(+a: U32, s: Rq, +b: U32) -> Rq:
  match a:
    case 1:
      s
    case 2:
      rq.port(s, b, 1)
    case _:
      rq.port(rq.port(s, b, 1), b, 2)

# 1 a pair, noted from its lower node; 2 a node that may be an event's B;
# 0 neither
def rq.k2(pair: Bool, +ev: Bool) -> U32:
  match pair:
    case True{}:
      1
    case False{}:
      match ev:
        case True{}:
          2
        case False{}:
          0

def rq.note(+k: U32, h: P.H, st: P.Stk, ws: List<&2, U32>, mk: KM.M, wl: KM.M, +n: U32, +b: U32) -> Rq:
  match k:
    case 1:
      Rq{h, P.push(st, b), ws, mk, wl, n}
    case 2:
      Rq{h, st, Con{b, ws}, mk, wl, n}
    case _:
      Rq{h, st, ws, mk, wl, n}

def rq.q(r: P.H & U32, st: P.Stk, ws: List<&2, U32>, mk: KM.M, wl: KM.M, +n: U32, +b: U32, +hd: U32) -> Rq:
  (h, +q) = r
  rq.aux(KR.kind_arity(P.rk(hd)), rq.see(q, rq.note(rq.k2(U32.is_eq(P.port(q), 0) && U32.is_gt(q, b), KR.ev_end(P.rk(hd), 0)),
    h, st, ws, mk, wl, n, b)), b)

# a node reached, at word b: what its principal faces noted and seen, then
# its auxiliary ports
def rq.node(r: P.H & U32, st: P.Stk, ws: List<&2, U32>, mk: KM.M, wl: KM.M, +n: U32, +b: U32) -> Rq:
  (h, +hd) = r
  rq.q(P.rd(h, (b + 1 : U32)), st, ws, mk, wl, n, b, hd)

def rq.pop(r: KM.M & U32, h: P.H, st: P.Stk, ws: List<&2, U32>, mk: KM.M, +n: U32) -> Rq:
  (wl, +j) = r
  rq.node(P.rd(h, (j << 2n : U32)), st, ws, mk, wl, n, (j << 2n : U32))

def rq.go(k: Nat, s: Rq) -> Rq:
  match k:
    case 0n:
      s
    case 1n+p:
      match s:
        case Rq{h, st, ws, mk, wl, +n}:
          match n:
            case 0:
              Rq{h, st, ws, mk, wl, 0}
            case _:
              rq.go(p, rq.pop(KM.m_get(wl, (n - 1 : U32)), h, st, ws, mk, (n - 1 : U32)))

# after the sweep: the net, what the walk noted, and the nodes free
type Mq is Type:
  Mq{h: P.H, st: P.Stk, ws: List<&2, U32>, +free: U32}

def mq.sw(r: P.H & U32, st: P.Stk, ws: List<&2, U32>) -> Mq:
  (h, +free) = r
  Mq{h, st, ws, free}

def rq.sweep(s: Rq, +cap: U32) -> Mq:
  match s:
    case Rq{h, st, ws, mk, wl, +n}:
      mq.sw(KN.sw.fin(KN.sw.first(KN.Sw{h, mk, 0}, cap)), st, ws)

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

def rq.wl(r: KM.M & U32, h: P.H, mk: KM.M, +cap: U32) -> Rq:
  (wl, +room) = r
  Rq{h, P.stk_pow(KM.depth(32n, cap, 0n)), Nil{}, mk, wl, 0}

def rq.mk(r: KM.M & U32, h: P.H, +cap: U32) -> Rq:
  (mk, +sz) = r
  rq.wl(KN.rc.at(cap, 0n), h, mk, cap)

# The lean walk (heap-strategies.erasure.load.cycle.walk.lean): the
# maintainer's walk (`.walk`), its state cut to five words and each of its
# helpers called from one place, so that clang inlines the step whole
# (docs/BendIssues.md, "Records returned through every level, where clang
# will not inline"). From a reference to enter, its node marked already,
# the walk reads the node's head and the links of its two other ports, o1
# (the principal, unless entered by it) then o2: a node of three ports
# pushes o2's link, the node behind marked as it is pushed (so that none
# is pushed twice), and follows o1's if the node behind is unmarked,
# marking it; a node of two follows o1's alone; a node of one, or one
# whose o1 leads to a marked node, ends the run, and the stack's top is
# entered next. A pair is noted where a node looks at its principal and
# finds a principal: from it where the node behind was unmarked (entered
# then by its principal, it looks no further), else from the lower; an
# eraser or dead operator whose principal faces an auxiliary port is
# noted for its event. One array holds the marks, a word per 32 nodes from
# word 0, the notes from the word after them, and the stack from its top
# down, the top word 0 ending it: notes and stack entries are of distinct
# nodes, fewer than the capacity, in an array of twice it. A nil link
# reads as node 0, of the header, marked from the start.

# the walk's state: the net's words (its data table set aside), the walk's
# array, the reference to enter next (its node marked), 0 once done, the
# stack's lowest word and the next note's word
type Lw is Type:
  Lw{w: KM.M, g: KM.M, +c: U32, +n: U32, +q: U32}

# the net's words, the walk's array and the stack's lowest word, after a
# push
type Gw is Type:
  Gw{w: KM.M, g: KM.M, +n: U32}

# a node's head and the link of its port o1
type Nd is Type:
  Nd{w: KM.M, +hd: U32, +l1: U32}

# the node behind link l marked: the array, and 1 if it was already
def lw.mk.v(r: KM.M & U32, +j: U32, +s: U32) -> KM.M & U32:
  (g, +v) = r
  (KM.m_set(g, j, (v .|. (1 << U32.to_nat(s) : U32) : U32)), ((v >> U32.to_nat(s) : U32) .&. 1 : U32))

def lw.mk(g: KM.M, +l: U32) -> KM.M & U32:
  lw.mk.v(KM.m_get(g, (l >> 7n : U32)), (l >> 7n : U32), ((l >> 2n : U32) .&. 31 : U32))

def nd.l1(r: KM.M & U32, +hd: U32) -> Nd:
  (w, +l1) = r
  Nd{w, hd, l1}

# node b entered by port p: o1 is 1 if p is 0, else 0 (o2, read where
# there are three ports, is 2 unless p is); for a node of two ports, o1 is
# its other port
def nd.hd(r: KM.M & U32, +b: U32, +p: U32) -> Nd:
  (w, +hd) = r
  nd.l1(KM.m_get(w, ((b + 1 : U32) + (1 >> U32.to_nat(p) : U32) : U32)), hd)

def lw.f1p(pair: Bool, w: KM.M, g: KM.M, +n: U32, +q: U32, +b: U32, +c: U32) -> Lw:
  match pair:
    case True{}:
      Lw{w, KM.m_set(g, q, b), c, n, (q + 1 : U32)}
    case False{}:
      Lw{w, g, c, n, q}

# o1's link l1 followed if the node behind was unmarked, else the stack's
# top next (0); b noted as a pair's lower node where p is not 0 (o1 is
# the principal), l1 is a principal, and the node behind was unmarked or
# is the higher
def lw.f1m(r: KM.M & U32, w: KM.M, +n: U32, +q: U32, +b: U32, +p: U32, +l1: U32) -> Lw:
  (g, +old) = r
  lw.f1p(U32.is_ne(p, 0) && U32.is_eq(P.port(l1), 0) && (U32.is_eq(old, 0) || U32.is_lt(b, P.base(l1))),
    w, g, n, q, b, (l1 .&. (old - 1 : U32) : U32))

def lw.f1(s: Gw, +q: U32, +b: U32, +p: U32, +l1: U32) -> Lw:
  match s:
    case Gw{w, g, +n}:
      lw.f1m(lw.mk(g, l1), w, n, q, b, p, l1)

def lw.push.o(+old: U32, w: KM.M, g: KM.M, +n: U32, +l2: U32) -> Gw:
  match old:
    case 0:
      Gw{w, KM.m_set(g, (n - 1 : U32), l2), (n - 1 : U32)}
    case _:
      Gw{w, g, n}

# o2's link pushed unless the node behind was marked
def lw.push(r: KM.M & U32, w: KM.M, +n: U32, +l2: U32) -> Gw:
  (g, +old) = r
  lw.push.o(old, w, g, n, l2)

def lw.p2r(r: KM.M & U32, g: KM.M, +n: U32) -> Gw:
  (w, +l2) = r
  lw.push(lw.mk(g, l2), w, n, l2)

def lw.p2(three: Bool, w: KM.M, g: KM.M, +n: U32, +b: U32, +p: U32) -> Gw:
  match three:
    case True{}:
      lw.p2r(KM.m_get(w, ((b + 3 : U32) - (p >> 1n : U32) : U32)), g, n)
    case False{}:
      Gw{w, g, n}

# an eraser or dead operator noted where its principal faces an auxiliary
# port, the note tagged by its top bit
def lw.lev(r: KM.M & U32, g: KM.M, +n: U32, +q: U32, +b: U32) -> Lw:
  (w, +src) = r
  Lw{w, KM.m_set(g, q, (b .|. 2147483648 : U32)), 0, n, (q + (((src .&. 3 : U32) + 3 : U32) >> 2n : U32) : U32)}

def lw.leaf(ev: Bool, w: KM.M, g: KM.M, +n: U32, +q: U32, +b: U32) -> Lw:
  match ev:
    case True{}:
      lw.lev(KM.m_get(w, (b + 1 : U32)), g, n, q, b)
    case False{}:
      Lw{w, g, 0, n, q}

def lw.ar(+a: U32, w: KM.M, g: KM.M, +n: U32, +q: U32, +b: U32, +p: U32, +hd: U32, +l1: U32) -> Lw:
  match a:
    case 0:
      Lw{w, g, 0, n, q}
    case 1:
      lw.leaf(KR.ev_end(P.rk(hd), 0), w, g, n, q, b)
    case _:
      lw.f1(lw.p2(U32.is_eq(a, 3), w, g, n, b, p), q, b, p, l1)

def lw.at(d: Nd, g: KM.M, +n: U32, +q: U32, +b: U32, +p: U32) -> Lw:
  match d:
    case Nd{w, +hd, +l1}:
      lw.ar(KR.kind_arity(P.rk(hd)), w, g, n, q, b, p, hd, l1)

def lw.pop(r: KM.M & U32, w: KM.M, +n: U32, +q: U32) -> Lw:
  (g, +c) = r
  Lw{w, g, c, (n + 1 : U32), q}

# where the step ended its run, the stack's top popped
def lw.nx(s: Lw) -> Lw:
  match s:
    case Lw{w, g, +c, +n, +q}:
      match c:
        case 0:
          lw.pop(KM.m_get(g, n), w, n, q)
        case _:
          Lw{w, g, c, n, q}

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
              lw.go(p, lw.nx(lw.at(nd.hd(KM.m_get(w, P.base(c)), P.base(c), P.port(c)), g, n, q, P.base(c), P.port(c))))

# the notes after the sweep: the pairs slid down to word 3 on, as a stack
# (P.Stk) holds them, the events onto a list
type Sp is Type:
  Sp{g: KM.M, ws: List<&2, U32>, +j: U32}

def sp.ev(+ev: U32, g: KM.M, ws: List<&2, U32>, +j: U32, +v: U32) -> Sp:
  match ev:
    case 0:
      Sp{KM.m_set(g, (j + 3 : U32), v), ws, (j + 1 : U32)}
    case _:
      Sp{g, Con{(v .&. 2147483647 : U32), ws}, j}

def sp.v(r: KM.M & U32, ws: List<&2, U32>, +j: U32) -> Sp:
  (g, +v) = r
  sp.ev((v >> 31n : U32), g, ws, j, v)

def sp.go(k: Nat, s: Sp, +i: U32) -> Sp:
  match k:
    case 0n:
      s
    case 1n+p:
      match s:
        case Sp{g, ws, +j}:
          sp.go(p, sp.v(KM.m_get(g, i), ws, j), (i + 1 : U32))

def lw.sp(s: Sp, h: P.H, +free: U32, +cap: U32) -> Mq:
  match s:
    case Sp{g, ws, +j}:
      Mq{h, P.stk.fin((KM.m_set(g, 0, j), (cap * 2 : U32))), ws, free}

def lw.swd(s: KN.Sw, +q: U32, +cap: U32) -> Mq:
  match s:
    case KN.Sw{h, g, +f}:
      lw.sp(sp.go(U32.to_nat((q - (cap >> 5n : U32) : U32)), Sp{g, Nil{}, 0}, (cap >> 5n : U32)), h, f, cap)

# the walk done, the net swept by its marks
def lw.fin(s: Lw, a: Array<V.Val>, +cap: U32) -> Mq:
  match s:
    case Lw{w, g, +c, +n, +q}:
      lw.swd(KN.sw.first(KN.Sw{P.H{w, a}, g, 0}, cap), q, cap)

# the walk's start: nodes 0 and the interface marked, the interface's one
# link followed; the stack's lowest word the array's last, 0
def lw.s1(r: KM.M & U32, w: KM.M, +n: U32, +q: U32, +l: U32) -> Lw:
  (g, +old) = r
  Lw{w, g, (l .&. (old - 1 : U32) : U32), n, q}

def lw.s0(r: KM.M & U32, g: KM.M, +n: U32, +q: U32) -> Lw:
  (w, +l) = r
  lw.s1(lw.mk(g, l), w, n, q, l)

def lw.g0(r: KM.M & U32, w: KM.M, +cap: U32) -> Lw:
  (g, +sz) = r
  lw.s0(KM.m_get(w, (P.iface() + 1 : U32)),
    KM.m_set(KM.m_set(g, (sz - 1 : U32), 4294967295), 0, (1 .|. KN.rc.bit((P.iface() >> 2n : U32)) : U32)), (sz - 2 : U32), (cap >> 5n : U32))

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

def two.hx(r: P.H & U32, +y: U32) -> P.H & Bool:
  (h, +hx) = r
  two.hy(P.rd(h, y), hx)

# would the pair x - y grow the net?
def two.grows(h: P.H, +x: U32, +y: U32) -> P.H & Bool:
  two.hx(P.rd(h, x), y)

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
  pr.hy(P.rd(h, y), pf, x, y, hx)

# the pair x - y, counted before it interacts
def probe(h: P.H, pf: Pf, +x: U32, +y: U32) -> P.H & Pf:
  pr.hx(P.rd(h, x), pf, x, y)

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

# Reducing toward the interface (net-demand-whnf; HeapModel's "Forcing"):
# from the interface, follow principal ports. Where one faces another node's
# auxiliary port, that node must reduce first, and the walk goes on from
# it, keeping a path; where it faces a principal port, that pair is next.
# Only the path's last node can be in a pair, the others facing auxiliary
# ports, so a rewrite there leaves the rest of the path as it was: the
# walk resumes from the node below. The walk finds its pairs itself, its
# rewrites noting none; pairs off its path stay in the net, found where
# they come to lie on the path, garbage where they never do.
# Erasures off the path are not reduced either (the maintainer, 2026-10-28:
# unneeded work is better found by analysing nets ahead of time than by
# erasing eagerly), so dropped values stay in the net. Done when the
# interface faces a principal port but a control's: the value there (an
# error value or a superposition reads as none). A pair on the path stuck
# by its rule stops the walk; so does one needing another cell, an
# application or a strict call meeting a table entry that is a handle,
# the need left in the net for `need` to read.

# the path below its last node, top, in an array, its capacity at word 0
# and the nodes from the interface on from word 1, depth of them;
# interactions; how the walk stands: 0 going; the net's outcomes, 1 done,
# 2 needing a lazy value (need), 3 stuck, 5 a cycle; and the runtime's
# errors, which say nothing of the net (machine-limits-not-errors), 4 out
# of fuel, 6 out of memory (the path's array or a collecting demand's net
# could not grow)
type D is Type:
  D{h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32}

def d.go(h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32) -> D:
  D{h, path, top, depth, n, 0}

def d.stop(h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> D:
  D{h, path, top, depth, n, st}

def wk.pop.r(r: KM.M & U32, h: P.H, +depth: U32, +n: U32) -> D:
  (path, +p) = r
  d.go(h, path, p, (depth - 1 : U32), n)

def wk.pop(h: P.H, path: KM.M, +depth: U32, +n: U32) -> D:
  match depth:
    case 0:
      d.go(h, path, P.iface(), 0, n)
    case _:
      wk.pop.r(KM.m_get(path, depth), h, depth, n)

def wk.past(gone: Bool, h: P.H, path: KM.M, +p: U32, +depth: U32, +n: U32) -> D:
  match gone:
    case True{}:
      wk.pop(h, path, depth, n)
    case False{}:
      d.go(h, path, p, depth, n)

def wk.hp(r: P.H & U32, path: KM.M, +p: U32, +depth: U32, +n: U32) -> D:
  (h, +hp) = r
  wk.past(U32.is_eq(hp, 0), h, path, p, depth, n)

# the path's last node rewritten: the walk goes back to the one below, or
# past it where fusing controls freed it. Fusion tries only the links a
# rule made, the node below's is one, and a fusion there may free that
# node (a lift facing the source keeps the one behind it, a control facing
# consumers the one ahead); at its auxiliary ports a fusion keeps it, and
# the node below it is not touched, its link made by no rule.
def wk.back.r(r: KM.M & U32, h: P.H, +depth: U32, +n: U32) -> D:
  (path, +p) = r
  wk.hp(P.rd(h, p), path, p, (depth - 1 : U32), n)

def wk.back(h: P.H, path: KM.M, +depth: U32, +n: U32) -> D:
  match depth:
    case 0:
      d.go(h, path, P.iface(), 0, n)
    case _:
      wk.back.r(KM.m_get(path, depth), h, depth, n)

def wk.hb.go(gone: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32) -> D:
  match gone:
    case True{}:
      wk.back(h, path, depth, (n + 1 : U32))
    case False{}:
      d.stop(h, path, top, depth, n, 3)

def wk.hb(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32) -> D:
  (h, +hb) = r
  wk.hb.go(U32.is_eq(hb, 0), h, path, top, depth, n)

# rewrite a >< b, unless its rule leaves it as it is (KR.stuck_by). Where
# the payload test decides that, the rule makes at most one node when it
# rewrites (law rules_tested_small), which takes a's slot in place while
# b's is freed (heap-strategies.reuse): b's slot is free after a rewrite
# and held if stuck. The test itself is left to the rewrite, its only
# caller.
def wk.rw(~after: P.H -> @+x:N.Ext -> P.H, +sb: U32, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match sb:
    case 0:
      wk.back(KN.go(~Unit, ~P.H, ~KN.note.u, ~KN.fin.h, ~KN.wd.u, ~after, h, Unit{}, True{}, a, b, ha, hb), path, depth, (n + 1 : U32))
    case 1:
      d.stop(h, path, top, depth, n, 3)
    case _:
      wk.hb(P.rd(KN.go(~Unit, ~P.H, ~KN.note.u, ~KN.fin.h, ~KN.wd.u, ~after, h, Unit{}, True{}, a, b, ha, hb), b), path, top, depth, n)

def nd.lz(~after: P.H -> @+x:N.Ext -> P.H, z: P.Lz, path: KM.M, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match z:
    case P.Lz{h, +lazy, +k}:
      match lazy:
        case True{}:
          D{h, path, top, depth, n, 2}
        case False{}:
          wk.rw(~after, KR.stuck_by(P.rk(ha), P.rk(hb)), h, path, top, depth, n, a, b, ha, hb)

def nd.pb(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  (h, +pb) = r
  nd.lz(~after, P.val_lazy(h, P.form(hb), pb), path, top, depth, n, a, b, ha, hb)

def nd.go(~after: P.H -> @+x:N.Ext -> P.H, chk: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match chk:
    case True{}:
      nd.pb(~after, P.rd(h, (b + 2 : U32)), path, top, depth, n, a, b, ha, hb)
    case False{}:
      wk.rw(~after, KR.stuck_by(P.rk(ha), P.rk(hb)), h, path, top, depth, n, a, b, ha, hb)

# an application or a strict call meeting data in the table
def may_need(+ha: U32, +hb: U32) -> Bool:
  (U32.is_eq(P.rk(ha), 2) || U32.is_eq(P.rk(ha), 9)) && U32.is_eq(P.rk(hb), 5) && U32.is_eq(P.form(hb), 0)

def wk.ori(~after: P.H -> @+x:N.Ext -> P.H, neg: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +x: U32, +y: U32, +hx: U32, +hy: U32) -> D:
  match neg:
    case True{}:
      nd.go(~after, may_need(hx, hy), h, path, top, depth, n, x, y, hx, hy)
    case False{}:
      nd.go(~after, may_need(hy, hx), h, path, top, depth, n, y, x, hy, hx)

def wk.hy(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +y: U32, +hx: U32) -> D:
  (h, +hy) = r
  wk.ori(~after, KR.kind_neg(P.rk(hx)), h, path, top, depth, n, top, y, hx, hy)

def wk.hx(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +y: U32) -> D:
  (h, +hx) = r
  wk.hy(~after, P.rd(h, y), path, top, depth, n, y, hx)

# the interface facing a principal port: a control's moves past it (the
# root's rule keeps the interface), anything else is the value
def wk.root.go(~after: P.H -> @+x:N.Ext -> P.H, c: Bool, h: P.H, path: KM.M, +depth: U32, +n: U32, +y: U32) -> D:
  match c:
    case True{}:
      d.go(KN.interact(~after, h, True{}, P.iface(), y), path, P.iface(), depth, (n + 1 : U32))
    case False{}:
      d.stop(h, path, 0, depth, n, 1)

def wk.root(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, path: KM.M, +depth: U32, +n: U32, +y: U32) -> D:
  (h, +hy) = r
  wk.root.go(~after, U32.is_eq(P.rk(hy), 11), h, path, depth, n, y)

def wk.pair(~after: P.H -> @+x:N.Ext -> P.H, root: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +y: U32) -> D:
  match root:
    case True{}:
      wk.root(~after, P.rd(h, y), path, depth, n, y)
    case False{}:
      wk.hx(~after, P.rd(h, top), path, top, depth, n, y)

# The path's nodes are distinct unless the walk has gone round a vicious
# circle, principal ports each facing an auxiliary one, a deadlock that
# never reduces; and once the walk repeats, it repeats for good, nothing
# on the path changing. So just before the array grows, the node pushed
# is compared with the path's (heap-strategies.demand.cycle.early): the
# first growth after the walk closes a circle finds it, by twice the
# depth where it closes. A push tests only whether the array may be full,
# its words a power of two.

type Sc is Type:
  Sc{m: KM.M, +hit: Bool}

def sc.step(r: KM.M & U32, +x: U32) -> Sc:
  (m, +v) = r
  Sc{m, U32.is_eq(v, x)}

# whether x is in words i .. i + k - 1
def sc.run(k: Nat, s: Sc, +i: U32, +x: U32) -> Sc:
  match k:
    case 0n:
      s
    case 1n+p:
      match s:
        case Sc{m, +hit}:
          match hit:
            case True{}:
              Sc{m, True{}}
            case False{}:
              sc.run(p, sc.step(KM.m_get(m, i), x), (i + 1 : U32), x)

def wk.grown.go(ok: Bool, path: KM.M, h: P.H, +top: U32, +depth: U32, +n: U32, +x: U32, +cap2: U32) -> D:
  match ok:
    case True{}:
      d.go(h, KM.m_set(KM.m_set(path, 0, cap2), (depth + 1 : U32), top), x, (depth + 1 : U32), n)
    case False{}:
      d.stop(P.h_err(h), path, top, depth, n, 6)

# the array doubled, or out of memory where it could not grow
def wk.grown(r: KM.M & U32, h: P.H, +top: U32, +depth: U32, +n: U32, +x: U32, +cap: U32) -> D:
  (path, +cap2) = r
  wk.grown.go(U32.is_gt(cap2, cap), path, h, top, depth, n, x, cap2)

def wk.seen(s: Sc, h: P.H, +top: U32, +depth: U32, +n: U32, +x: U32, +cap: U32) -> D:
  match s:
    case Sc{path, +hit}:
      match hit:
        case True{}:
          d.stop(h, path, top, depth, n, 5)
        case False{}:
          wk.grown(KM.m_ensure(path, (cap * 2 : U32), cap, P.w_maxd()), h, top, depth, n, x, cap)

def wk.full.go(full: Bool, path: KM.M, h: P.H, +top: U32, +depth: U32, +n: U32, +x: U32, +cap: U32) -> D:
  match full:
    case True{}:
      wk.seen(sc.run(U32.to_nat(depth), Sc{path, False{}}, 1, top), h, top, depth, n, x, cap)
    case False{}:
      d.go(h, KM.m_set(path, (depth + 1 : U32), top), x, (depth + 1 : U32), n)

def wk.full(r: KM.M & U32, h: P.H, +top: U32, +depth: U32, +n: U32, +x: U32) -> D:
  (path, +cap) = r
  wk.full.go(U32.is_ge((depth + 1 : U32), cap), path, h, top, depth, n, x, cap)

# top pushed, the walk going on at x
def wk.push(p2: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +x: U32) -> D:
  match p2:
    case True{}:
      wk.full(KM.m_get(path, 0), h, top, depth, n, x)
    case False{}:
      d.go(h, KM.m_set(path, (depth + 1 : U32), top), x, (depth + 1 : U32), n)

def wk.q.go(~after: P.H -> @+x:N.Ext -> P.H, nil: Bool, +pr: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +q: U32) -> D:
  match nil pr:
    case True{} _:
      d.stop(h, path, top, depth, n, 3)
    case False{} True{}:
      wk.pair(~after, U32.is_eq(top, P.iface()), h, path, top, depth, n, q)
    case False{} False{}:
      wk.push(U32.is_eq(((depth + 1 : U32) .&. depth : U32), 0), h, path, top, depth, n, P.base(q))

# Pushes and what follows them in one step: most pushes find a pair at
# once, and a step costs the walk a round through demand's loop. While
# the last node faces an auxiliary port and the array has room, it is
# pushed and the next node's link read (wk.down), before the step looks
# at what the last faces: a pair, rewritten, or an auxiliary port where
# the array is full, pushed as it grows. One place looks, so that the
# rewrite's chain keeps its one caller.

type Dn is Type:
  Dn{+go: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +q: U32}

# whether the walk can push past a node facing q, at depth: an auxiliary
# port, and room in the array
def dn.can(+q: U32, +depth: U32) -> Bool:
  U32.is_ne(q, P.nil()) && U32.is_ne(P.port(q), 0) && U32.is_ne(((depth + 1 : U32) .&. depth : U32), 0)

def dn.r(r: P.H & U32, path: KM.M, +x: U32, +depth: U32) -> Dn:
  (h, +q) = r
  Dn{dn.can(q, depth), h, path, x, depth, q}

def dn.step(h: P.H, path: KM.M, +top: U32, +depth: U32, +q: U32) -> Dn:
  dn.r(P.rd(h, (P.base(q) + 1 : U32)), KM.m_set(path, (depth + 1 : U32), top), P.base(q), (depth + 1 : U32))

def wk.down(f: Nat, s: Dn) -> Dn:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case Dn{+go, h, path, +top, +depth, +q}:
          match go:
            case True{}:
              wk.down(g, dn.step(h, path, top, depth, q))
            case False{}:
              Dn{False{}, h, path, top, depth, q}

def wk.c(~after: P.H -> @+x:N.Ext -> P.H, s: Dn, +n: U32) -> D:
  match s:
    case Dn{+go, h, path, +top, +depth, +q}:
      wk.q.go(~after, U32.is_eq(q, P.nil()), U32.is_eq(P.port(q), 0), h, path, top, depth, n, q)

# what the path's last node's principal port faces
def wk.q(~after: P.H -> @+x:N.Ext -> P.H, r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32) -> D:
  (h, +q) = r
  wk.c(~after, wk.down(4294967295n, Dn{dn.can(q, depth), h, path, top, depth, q}), n)

def d.out(+st: U32) -> U32:
  match st:
    case 0:
      4
    case _:
      st

def d.end(d: D) -> D:
  match d:
    case D{h, path, +top, +depth, +n, +st}:
      D{h, path, top, depth, n, d.out(st)}

# demand's loop: toward the interface for at most k steps, ending where
# it stands, going (0) where the steps ran out; plain demand's, and the
# collecting demand's a chunk at a time, one caller of the walk for both
def demand.go(k: Nat, d: D) -> D:
  match k:
    case 0n:
      d
    case 1n+p:
      match d:
        case D{h, path, +top, +depth, +n, +st}:
          match st:
            case 0:
              demand.go(p, wk.q(~KN.go.none, P.rd(h, (top + 1 : U32)), path, top, depth, n))
            case _:
              D{h, path, top, depth, n, st}

# reduce toward the interface for at most k steps
def demand(k: Nat, d: D) -> D:
  d.end(demand.go(k, d))

# the same, running events (knet.bend's Events), which free no node on
# the path (law events_erase_last)
def demand.v(k: Nat, d: D) -> D:
  match k:
    case 0n:
      d.end(d)
    case 1n+p:
      match d:
        case D{h, path, +top, +depth, +n, +st}:
          match st:
            case 0:
              demand.v(p, wk.q(~KN.ev.settle, P.rd(h, (top + 1 : U32)), path, top, depth, n))
            case _:
              D{h, path, top, depth, n, st}

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
# is left out. S is the net's capacity over 64, the reserve a 32nd of it.
# A net that had to grow and could not: out of memory (6), the runtime's
# error.

# what a chunk leaves: the walk, its steps left, and whether the next
# chunk's end collects whatever the reserve (the stress test)
type Dl is Type:
  Dl{+left: U32, +force: Bool, d: D}

def rs.k(r: P.H & P.HS) -> P.H & Bool:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      P.reserve(U32.to_nat((cap >> 5n : U32)), h)

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

# a reserve kept, a 32nd of the net, the net doubled first where its free
# list lacks one; false where it could not grow
def dc.reserve(h: P.H) -> P.H & Bool:
  rs.got(rs.k(P.stats(h)))

def dc.steps(+force: Bool, +cap: U32) -> U32:
  match force:
    case True{}:
      16
    case False{}:
      U32.max((cap >> 6n : U32), 1)

def dc.run(+ok: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +steps: U32, +left: U32, +force: Bool) -> Dl:
  match ok:
    case True{}:
      Dl{(left - steps : U32), force, demand.go(U32.to_nat(steps), D{h, path, top, depth, n, 0})}
    case False{}:
      Dl{left, force, d.stop(h, path, top, depth, n, 6)}

def dc.rs(r: P.H & Bool, path: KM.M, +top: U32, +depth: U32, +n: U32, +steps: U32, +left: U32, +force: Bool) -> Dl:
  (h, +ok) = r
  dc.run(ok, h, path, top, depth, n, steps, left, force)

# a chunk: S steps, or those left, from a reserve seen kept; a stress test
# collects at its end whatever the reserve where the net holds 1024 nodes
# or fewer, the chunk then 16 steps: the walk starting again from the
# interface after a collection takes a step for each power of two in its
# depth (wk.push), at most 11 in such a net, so a chunk of 4 made no
# progress
def dc.chunk(r: P.H & P.HS, path: KM.M, +top: U32, +depth: U32, +n: U32, +left: U32, +stress: Bool) -> Dl:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      dc.rs(dc.reserve(h), path, top, depth, n,
        U32.min(dc.steps(stress && U32.is_le(cap, 1024), cap), left), left, stress && U32.is_le(cap, 1024))

def dc.ok(+ok: Bool, h: P.H, path: KM.M, +n: U32, +left: U32, +force: Bool) -> Dl:
  match ok:
    case True{}:
      Dl{left, force, d.go(h, path, P.iface(), 0, n)}
    case False{}:
      Dl{left, force, d.stop(h, path, P.iface(), 0, n, 6)}

def dc.col(r: P.H & Bool, path: KM.M, +n: U32, +left: U32, +force: Bool) -> Dl:
  (h, +ok) = r
  dc.ok(ok, h, path, n, left, force)

def dc.tap.go(go: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +left: U32, +force: Bool) -> Dl:
  match go:
    case True{}:
      dc.col(collect_cycle(h), path, n, left, force)
    case False{}:
      Dl{left, force, D{h, path, top, depth, n, st}}

def dc.tap(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +left: U32, +force: Bool) -> Dl:
  (h, +tap) = r
  dc.tap.go((U32.is_ne(tap, 0) || force) && U32.is_eq(st, 0), h, path, top, depth, n, st, left, force)

# a chunk's end: the net collected where the reserve was taken
def dc.after(s: Dl) -> Dl:
  match s:
    case Dl{+left, +force, d}:
      match d:
        case D{h, path, +top, +depth, +n, +st}:
          dc.tap(P.rd(h, P.at_tap()), path, top, depth, n, st, left, force)

def dc.loop(k: Nat, s: Dl, +stress: Bool) -> D:
  match k:
    case 0n:
      match s:
        case Dl{+left, +force, d}:
          d.end(d)
    case 1n+p:
      match s:
        case Dl{+left, +force, d}:
          match left:
            case 0:
              d.end(d)
            case _:
              match d:
                case D{h, path, +top, +depth, +n, +st}:
                  match st:
                    case 0:
                      dc.loop(p, dc.after(dc.chunk(P.stats(h), path, top, depth, n, left, stress)), stress)
                    case _:
                      D{h, path, top, depth, n, st}

# demand collecting where its net would grow, for at most k steps
def demand.c(+k: Nat, d: D) -> D:
  dc.loop(k, Dl{U32.from_nat(k), False{}, d}, False{})

# the same as a stress test (heap-strategies.erasure.load.cycle.stress):
# a net of 1024 nodes or fewer collected every 16 steps
def demand.s(+k: Nat, d: D) -> D:
  dc.loop(k, Dl{U32.from_nat(k), False{}, d}, True{})

def d.path(r: KM.M & U32) -> KM.M:
  (m, +cap) = r
  KM.m_set(m, 0, cap)

def d.start(h: P.H) -> D:
  d.go(h, d.path(KM.m_new(6n, P.w_maxd())), P.iface(), 0, 0)

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
def resume(d: D, v: V.Val) -> D:
  match d:
    case D{h, path, +top, +depth, +n, +st}:
      d.go(resume.b(d.at(h, top), v), path, top, depth, n)

def need.z(z: P.Lz, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> D & U32:
  match z:
    case P.Lz{h, +lazy, +k}:
      (D{h, path, top, depth, n, st}, k)

def need.pb(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +hb: U32) -> D & U32:
  (h, +pb) = r
  need.z(P.val_lazy(h, P.form(hb), pb), path, top, depth, n, st)

def need.hb(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32, +b: U32) -> D & U32:
  (h, +hb) = r
  need.pb(P.rd(h, (b + 2 : U32)), path, top, depth, n, st, hb)

def need.b(r: P.H & U32, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> D & U32:
  (h, +b) = r
  need.hb(P.rd(h, b), path, top, depth, n, st, b)

def need.go(w: Bool, h: P.H, path: KM.M, +top: U32, +depth: U32, +n: U32, +st: U32) -> D & U32:
  match w:
    case True{}:
      need.b(d.at(h, top), path, top, depth, n, st)
    case False{}:
      (D{h, path, top, depth, n, st}, 0)

# the handle a demand stopped needing (state 2), read from the net; 0 in
# any other state
def need(d: D) -> D & U32:
  match d:
    case D{h, path, +top, +depth, +n, +st}:
      need.go(U32.is_eq(st, 2), h, path, top, depth, n, st)

