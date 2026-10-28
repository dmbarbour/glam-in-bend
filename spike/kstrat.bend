import Base
import ./val.bend as V
import ./kprim.bend as P
import ./krules.bend as KR
import ./knet.bend as KN

# Strategies over a net (heap-strategies in docs/plans/HeapModel_2026-10-27.md):
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
        case P.Pop{h, st, +cap, +x, +y, +ok}:
          match ok:
            case True{}:
              run(p, fast, P.pop(KN.interact.e(h, st, fast, x, y), cap, KR.most_pairs()))
            case False{}:
              Ran{h, 1n+p}

def ran(r: Ran, +fuel: Nat) -> P.H:
  match r:
    case Ran{h, +left}:
      P.count(h, U32.from_nat(Nat.sub(fuel, left)))

def reduce.go(r: P.Stk & U32, h: P.H, +wcap: U32, +fuel: Nat, +fast: Bool) -> P.H:
  (st, +room) = r
  ran(run(fuel, fast, P.pop(scan(U32.to_nat(wcap), 0, P.E{h, st}), room, KR.most_pairs())), fuel)

def reduce.st(r: P.H & P.HS, +fuel: Nat, +fast: Bool) -> P.H:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      reduce.go(P.stk_new(P.rs_words(cap)), h, cap, fuel, fast)

# a run of at most fuel interactions, which counts them by the fuel it
# used; the stack, with room for half the nodes, is let go at the end
def reduce_h(+fuel: Nat, +fast: Bool, h: P.H) -> P.H:
  reduce.st(P.stats(h), fuel, fast)

# Demand
# ======

# Reducing toward the interface (net-demand-whnf; HeapModel's "Forcing"):
# from node 0, follow principal ports. Where one faces another node's
# auxiliary port, that node must reduce first, and the walk goes on from
# it, keeping a path; where it faces a principal port, that pair is next.
# Only the path's last node can be in a pair, the others facing auxiliary
# ports, so a rewrite there leaves the rest of the path as it was: the
# walk resumes from the node below. The walk finds its pairs itself, its
# rewrites noting none; pairs off its path stay in the net, found where
# they come to lie on the path, garbage where they never do.
# Erasures off the path are not reduced either (the maintainer, 2026-10-28:
# unneeded work is better found by analysing nets ahead of time than by
# erasing eagerly), so dropped values stay in the net. Done when node 0 faces a
# principal port but a control's: the value there (an error value or a
# superposition reads as none). A pair on the path stuck by its rule stops
# the walk; so does one needing another cell, an application or a strict
# call meeting a table entry that is a handle, the need recorded.

# the path below its last node, top, and its length; interactions; the
# state, 0 going, 1 done, 2 needing a lazy value, 3 stuck, 4 out of fuel;
# for a need, the handle and the data node holding it
type D is Type:
  D{h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +st: U32, +lz: U32, +at: U32}

def d.go(h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32) -> D:
  D{h, path, top, depth, n, 0, 0, 0}

def d.stop(h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +st: U32) -> D:
  D{h, path, top, depth, n, st, 0, 0}

def wk.pop(h: P.H, path: List<&2, U32>, +depth: U32, +n: U32) -> D:
  match path:
    case Con{+p, rest}:
      d.go(h, rest, p, (depth - 1 : U32), n)
    case Nil{}:
      d.go(h, Nil{}, 0, 0, n)

def wk.past(gone: Bool, h: P.H, path: List<&2, U32>, +p: U32, +depth: U32, +n: U32) -> D:
  match gone:
    case True{}:
      wk.pop(h, path, depth, n)
    case False{}:
      d.go(h, path, p, depth, n)

def wk.hp(r: P.H & U32, path: List<&2, U32>, +p: U32, +depth: U32, +n: U32) -> D:
  (h, +hp) = r
  wk.past(U32.is_eq(hp, 0), h, path, p, depth, n)

# the path's last node rewritten: the walk goes back to the one below, or
# past it where fusing controls freed it. Fusion tries only the links a
# rule made, the node below's is one, and a fusion there may free that
# node (a lift facing the source keeps the one behind it, a control facing
# consumers the one ahead); at its auxiliary ports a fusion keeps it, and
# the node below it is not touched, its link made by no rule.
def wk.back(h: P.H, path: List<&2, U32>, +depth: U32, +n: U32) -> D:
  match path:
    case Con{+p, rest}:
      wk.hp(P.rd(h, p), rest, p, (depth - 1 : U32), n)
    case Nil{}:
      d.go(h, Nil{}, 0, 0, n)

def wk.hb.go(gone: Bool, h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32) -> D:
  match gone:
    case True{}:
      wk.back(h, path, depth, (n + 1 : U32))
    case False{}:
      d.stop(h, path, top, depth, n, 3)

def wk.hb(r: P.H & U32, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32) -> D:
  (h, +hb) = r
  wk.hb.go(U32.is_eq(hb, 0), h, path, top, depth, n)

# rewrite a >< b, unless its rule leaves it as it is (KR.stuck_by). Where
# the payload test decides that, the rule makes at most one node when it
# rewrites (law rules_tested_small) and fresh2 frees b first, so the first
# new node takes a's slot: b's slot is free after a rewrite, as it was if
# stuck. The test itself is left to the rewrite, its only caller.
def wk.rw(+sb: U32, h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match sb:
    case 0:
      wk.back(KN.go(h, True{}, a, b, ha, hb), path, depth, (n + 1 : U32))
    case 1:
      d.stop(h, path, top, depth, n, 3)
    case _:
      wk.hb(P.rd(KN.go(h, True{}, a, b, ha, hb), b), path, top, depth, n)

def nd.lz(z: P.Lz, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match z:
    case P.Lz{h, +lazy, +k}:
      match lazy:
        case True{}:
          D{h, path, top, depth, n, 2, k, b}
        case False{}:
          wk.rw(KR.stuck_by(P.rk(ha), P.rk(hb)), h, path, top, depth, n, a, b, ha, hb)

def nd.pb(r: P.H & U32, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  (h, +pb) = r
  nd.lz(P.val_lazy(h, P.form(hb), pb), path, top, depth, n, a, b, ha, hb)

def nd.go(chk: Bool, h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> D:
  match chk:
    case True{}:
      nd.pb(P.rd(h, (b + 2 : U32)), path, top, depth, n, a, b, ha, hb)
    case False{}:
      wk.rw(KR.stuck_by(P.rk(ha), P.rk(hb)), h, path, top, depth, n, a, b, ha, hb)

# an application or a strict call meeting data in the table
def may_need(+ha: U32, +hb: U32) -> Bool:
  (U32.is_eq(P.rk(ha), 2) || U32.is_eq(P.rk(ha), 9)) && U32.is_eq(P.rk(hb), 5) && U32.is_eq(P.form(hb), 0)

def wk.ori(neg: Bool, h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +x: U32, +y: U32, +hx: U32, +hy: U32) -> D:
  match neg:
    case True{}:
      nd.go(may_need(hx, hy), h, path, top, depth, n, x, y, hx, hy)
    case False{}:
      nd.go(may_need(hy, hx), h, path, top, depth, n, y, x, hy, hx)

def wk.hy(r: P.H & U32, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +y: U32, +hx: U32) -> D:
  (h, +hy) = r
  wk.ori(KR.kind_neg(P.rk(hx)), h, path, top, depth, n, top, y, hx, hy)

def wk.hx(r: P.H & U32, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +y: U32) -> D:
  (h, +hx) = r
  wk.hy(P.rd(h, y), path, top, depth, n, y, hx)

# node 0 facing a principal port: a control's moves past it (the root's
# rule keeps node 0), anything else is the value
def wk.root.go(c: Bool, h: P.H, path: List<&2, U32>, +depth: U32, +n: U32, +y: U32) -> D:
  match c:
    case True{}:
      d.go(KN.interact(h, True{}, 0, y), path, 0, depth, (n + 1 : U32))
    case False{}:
      d.stop(h, path, 0, depth, n, 1)

def wk.root(r: P.H & U32, path: List<&2, U32>, +depth: U32, +n: U32, +y: U32) -> D:
  (h, +hy) = r
  wk.root.go(U32.is_eq(P.rk(hy), 11), h, path, depth, n, y)

def wk.pair(root: Bool, h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +y: U32) -> D:
  match root:
    case True{}:
      wk.root(P.rd(h, y), path, depth, n, y)
    case False{}:
      wk.hx(P.rd(h, top), path, top, depth, n, y)

# a path longer than any net's nodes has gone round a cycle
def deep_cap() -> U32:
  4194304

def wk.deeper(over: Bool, h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +q: U32) -> D:
  match over:
    case True{}:
      d.stop(h, path, top, depth, n, 3)
    case False{}:
      d.go(h, Con{top, path}, P.base(q), (depth + 1 : U32), n)

def wk.q.go(nil: Bool, +pr: Bool, h: P.H, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32, +q: U32) -> D:
  match nil pr:
    case True{} _:
      d.stop(h, path, top, depth, n, 3)
    case False{} True{}:
      wk.pair(U32.is_eq(top, 0), h, path, top, depth, n, q)
    case False{} False{}:
      wk.deeper(U32.is_ge(depth, deep_cap()), h, path, top, depth, n, q)

# what the path's last node's principal port faces
def wk.q(r: P.H & U32, path: List<&2, U32>, +top: U32, +depth: U32, +n: U32) -> D:
  (h, +q) = r
  wk.q.go(U32.is_eq(q, P.nil()), U32.is_eq(P.port(q), 0), h, path, top, depth, n, q)

def d.out(+st: U32) -> U32:
  match st:
    case 0:
      4
    case _:
      st

def d.end(d: D) -> D:
  match d:
    case D{h, path, +top, +depth, +n, +st, +lz, +at}:
      D{h, path, top, depth, n, d.out(st), lz, at}

# reduce toward the interface for at most k steps
def demand(k: Nat, d: D) -> D:
  match k:
    case 0n:
      d.end(d)
    case 1n+p:
      match d:
        case D{h, path, +top, +depth, +n, +st, +lz, +at}:
          match st:
            case 0:
              demand(p, wk.q(P.rd(h, (top + 1 : U32)), path, top, depth, n))
            case _:
              D{h, path, top, depth, n, st, lz, at}

def d.start(h: P.H) -> D:
  d.go(h, Nil{}, 0, 0, 0)

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

# a need met: the data node holding the handle holds v instead, and the
# walk goes on where it stopped
def resume(d: D, v: V.Val) -> D:
  match d:
    case D{h, path, +top, +depth, +n, +st, +lz, +at}:
      d.go(resume.hb(P.rd(h, at), at, v), path, top, depth, n)

