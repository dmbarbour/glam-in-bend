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

# interactions by pair of kinds (A's kind times 16 plus B's), the logical
# interactions in two words, the pairs peeled, and the interactions whose
# logical count would pass 2^32, left out of it
type Pf is Type:
  Pf{kp: KM.M, +lo: U32, +hi: U32, +peels: U32, +wide: U32}

def pf_new.go(r: KM.M & U32) -> Pf:
  (kp, +cap) = r
  Pf{kp, 0, 0, 0, 0}

def pf_new() -> Pf:
  pf_new.go(KM.m_new(8n, 8n))

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
  pf.w(logical(ha, hb, oa, ob), pf, ((P.rk(ha) << 4n : U32) + P.rk(hb) : U32), peeled(ha, hb, oa, ob))

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
      " " ++ U32.show((i >> 4n : U32)) ++ "." ++ U32.show((i .&. 15 : U32)) ++ ":" ++ U32.show(n)

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
        U32.show(wide) ++ " wide; pairs" ++ pf.pairs(255n, KM.m_get(kp, 0), 0)

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
# interactions; the state, 0 going, 1 done, 2 needing a lazy value (need),
# 3 stuck, 4 out of fuel, 5 a cycle
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
      d.stop(P.h_err(h), path, top, depth, n, 3)

# the array doubled, or the net failed where it could not grow
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

# reduce toward the interface for at most k steps
def demand(k: Nat, d: D) -> D:
  match k:
    case 0n:
      d.end(d)
    case 1n+p:
      match d:
        case D{h, path, +top, +depth, +n, +st}:
          match st:
            case 0:
              demand(p, wk.q(~KN.go.none, P.rd(h, (top + 1 : U32)), path, top, depth, n))
            case _:
              D{h, path, top, depth, n, st}

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

