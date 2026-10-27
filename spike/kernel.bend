import Base
import ./val.bend as V
import ./rules.bend as R
import ./net.bend as N
import ./tpl.bend as T
import ./nets.bend as X
import ./kmem_flat.bend as KM

# A reducer kernel with the node layout of spike-node-layout
# (docs/plans/EvalSpike_2026-10-26.md), to measure what the layout buys.
# One flat page of four-word nodes: the header holds the kind (8 bits)
# and a 24-bit field (the level; for nets built without levels, a fan's
# site, which pairs them the same way); the other words hold port links
# (node * 4 + port) or, in nodes with spare words, data inline (Data: a
# tag and a value; Call: its function's tag). The free list and the
# active pairs are arrays. The rewrites are written by hand for the rules
# bench_rules.bend's workload uses, in the rule table's order of new
# nodes and links, so the reduction is the spike's, step for step.
#
#   kernel <k>    reduce `k 2 succ 0` (2^k), report value, counts, time

# Capacity: 2^21 nodes, 2^21 active pairs; passing either is an error.
# Words, free list and active pairs are each a KM.M (kmem_*.bend: flat,
# grown by doubling, or paged).

def nil() -> U32:
  4294967295

type H is Type:
  H{w: KM.M, fs: KM.M, +nf: U32, +fresh: U32, rs: KM.M, +nr: U32, +itrs: U32, +errs: U32}

def h_new() -> H:
  H{KM.m_new(23n), KM.m_new(21n), 0, 0, KM.m_new(22n), 0, 0, 0}

def h_err(h: H) -> H:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs}:
      H{w, fs, nf, fresh, rs, nr, itrs, (errs + 1 : U32)}

def err_if(bad: Bool, h: H) -> H:
  match bad:
    case True{}:
      h_err(h)
    case False{}:
      h

# Words
# =====

def rd.fin(r: KM.M & U32, fs: KM.M, +nf: U32, +fresh: U32, rs: KM.M, +nr: U32, +itrs: U32, +errs: U32) -> H & U32:
  (w, +v) = r
  (H{w, fs, nf, fresh, rs, nr, itrs, errs}, v)

def rd(h: H, +i: U32) -> H & U32:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs}:
      rd.fin(KM.m_get(w, i), fs, nf, fresh, rs, nr, itrs, errs)

def wr(h: H, +i: U32, +v: U32) -> H:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs}:
      H{KM.m_set(w, i, v), fs, nf, fresh, rs, nr, itrs, errs}

def push.go(ok: Bool, h: H, +x: U32, +y: U32) -> H:
  match ok:
    case False{}:
      h_err(h)
    case True{}:
      match h:
        case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs}:
          H{w, fs, nf, fresh, KM.m_set(KM.m_set(rs, (nr * 2 : U32), x), ((nr * 2 : U32) + 1 : U32), y), (nr + 1 : U32), itrs, errs}

def push.ens(r: KM.M & Bool, w: KM.M, fs: KM.M, +nf: U32, +fresh: U32, +nr: U32, +itrs: U32, +errs: U32, +x: U32, +y: U32) -> H:
  (rs, +ok) = r
  push.go(ok, H{w, fs, nf, fresh, rs, nr, itrs, errs}, x, y)

def push(h: H, +x: U32, +y: U32) -> H:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs}:
      push.ens(KM.m_ensure(rs, ((nr * 2 : U32) + 2 : U32)), w, fs, nf, fresh, nr, itrs, errs, x, y)

def link.push(both: Bool, h: H, +x: U32, +y: U32) -> H:
  match both:
    case True{}:
      push(h, x, y)
    case False{}:
      h

# port p of node n is the reference n * 4 + p, and its link is word
# n * 4 + 1 + p: the reference plus one
def link(h: H, +x: U32, +y: U32) -> H:
  link.push(U32.is_eq((x .&. 3 : U32), 0) && U32.is_eq((y .&. 3 : U32), 0), wr(wr(h, (x + 1 : U32), y), (y + 1 : U32), x), x, y)

# Nodes
# =====

def alloc.pop(r: KM.M & U32, w: KM.M, +nf: U32, +fresh: U32, rs: KM.M, +nr: U32, +itrs: U32, +errs: U32) -> H & U32:
  (fs, +n) = r
  (H{w, fs, (nf - 1 : U32), fresh, rs, nr, itrs, errs}, (n << 2n : U32))

def alloc.fresh(ok: Bool, h: H) -> H & U32:
  match ok:
    case False{}:
      (h_err(h), 0)
    case True{}:
      match h:
        case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs}:
          (H{w, fs, nf, (fresh + 1 : U32), rs, nr, itrs, errs}, (fresh << 2n : U32))

def alloc.ens.f(r: KM.M & Bool, w: KM.M, +okw: Bool, +nf: U32, +fresh: U32, rs: KM.M, +nr: U32, +itrs: U32, +errs: U32) -> H & U32:
  (fs, +okf) = r
  alloc.fresh(okw && okf, H{w, fs, nf, fresh, rs, nr, itrs, errs})

def alloc.ens.w(r: KM.M & Bool, fs: KM.M, +nf: U32, +fresh: U32, rs: KM.M, +nr: U32, +itrs: U32, +errs: U32) -> H & U32:
  (w, +okw) = r
  alloc.ens.f(KM.m_ensure(fs, (fresh + 1 : U32)), w, okw, nf, fresh, rs, nr, itrs, errs)

def alloc(h: H) -> H & U32:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs}:
      match nf:
        case 0:
          alloc.ens.w(KM.m_ensure(w, ((fresh + 1 : U32) * 4 : U32)), fs, nf, fresh, rs, nr, itrs, errs)
        case _:
          alloc.pop(KM.m_get(fs, (nf - 1 : U32)), w, nf, fresh, rs, nr, itrs, errs)

def node.fin(r: H & U32, +hd: U32) -> H & U32:
  (h, +n) = r
  (wr(h, n, hd), n)

# a node with header hd: its reference (port 0)
def node(h: H, +hd: U32) -> H & U32:
  node.fin(alloc(h), hd)

def node2.fin(r: H & U32, +i: U32, +v: U32) -> H & U32:
  (h, +n) = r
  (wr(h, (n + i : U32), v), n)

# a node with word i set to v too (data inline)
def node2(h: H, +hd: U32, +i: U32, +v: U32) -> H & U32:
  node2.fin(node(h, hd), i, v)

def node3.fin(r: H & U32, +i: U32, +v: U32) -> H & U32:
  (h, +n) = r
  (wr(h, (n + i : U32), v), n)

def node3(h: H, +hd: U32, +i: U32, +v: U32, +j: U32, +u: U32) -> H & U32:
  node3.fin(node2(h, hd, i, v), j, u)

def free.fin(h: H, +r: U32) -> H:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs}:
      H{w, KM.m_set(fs, nf, (r >> 2n : U32)), (nf + 1 : U32), fresh, rs, nr, itrs, errs}

def free(h: H, +r: U32) -> H:
  free.fin(wr(h, r, 0), r)

def hd(+k: U32, +f: U32) -> U32:
  (k .|. (f << 8n : U32) : U32)

def kind(+h: U32) -> U32:
  (h .&. 255 : U32)

def fld(+h: U32) -> U32:
  (h >> 8n : U32)

# kinds: 1 Fn, 2 Ap, 3 Copy, 4 Merge, 5 Data, 6 EraN, 7 EraP, 8 Root,
# 9 Call (as net.bend's kcode). Data: word 2 a tag (1 a number, 2 succ),
# word 3 the value. Call: word 3 its function's tag.
def is_neg(+k: U32) -> Bool:
  match k:
    case 2:
      True{}
    case 3:
      True{}
    case 6:
      True{}
    case 8:
      True{}
    case 9:
      True{}
    case _:
      False{}

def arity(+k: U32) -> U32:
  match k:
    case 1:
      3
    case 2:
      3
    case 3:
      3
    case 4:
      3
    case 9:
      2
    case _:
      1

# Rewrites, by hand
# =================

type M4 is Type:
  M4{h: H, +r0: U32, +r1: U32, +r2: U32, +r3: U32}

def m4.d(r: H & U32, +r0: U32, +r1: U32, +r2: U32) -> M4:
  (h, +r3) = r
  M4{h, r0, r1, r2, r3}

def m4.c(r: H & U32, +r0: U32, +r1: U32, +h3: U32) -> M4:
  (h, +r2) = r
  m4.d(node(h, h3), r0, r1, r2)

def m4.b(r: H & U32, +r0: U32, +h2: U32, +h3: U32) -> M4:
  (h, +r1) = r
  m4.c(node(h, h2), r0, r1, h3)

def m4.a(r: H & U32, +h1: U32, +h2: U32, +h3: U32) -> M4:
  (h, +r0) = r
  m4.b(node(h, h1), r0, h2, h3)

def mk4(h: H, +h0: U32, +h1: U32, +h2: U32, +h3: U32) -> M4:
  m4.a(node(h, h0), h1, h2, h3)

def fresh(h: H, +a: U32, +b: U32) -> H:
  free(free(h, a), b)

def k.two(h: H, +a: U32, +b: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> H:
  link(link(fresh(h, a, b), e0, e1), e2, e3)

def k.cfn(m: M4, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> H:
  match m:
    case M4{h, +r0, +r1, +r2, +r3}:
      link(link(link(link(link(link(link(link(h, r0, e0), r1, e1), e2, r2),
        (r2 + 1 : U32), (r0 + 1 : U32)), (r2 + 2 : U32), (r1 + 1 : U32)), e3, r3), (r3 + 1 : U32), (r0 + 2 : U32)), (r3 + 2 : U32), (r1 + 2 : U32))

def k.comm(m: M4, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> H:
  match m:
    case M4{h, +r0, +r1, +r2, +r3}:
      link(link(link(link(link(link(link(link(h, r0, e0), r1, e1), r2, e2), r3, e3),
        (r2 + 1 : U32), (r0 + 1 : U32)), (r2 + 2 : U32), (r1 + 1 : U32)), (r3 + 1 : U32), (r0 + 2 : U32)), (r3 + 2 : U32), (r1 + 2 : U32))

def k.apsup(m: M4, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> H:
  match m:
    case M4{h, +r0, +r1, +r2, +r3}:
      link(link(link(link(link(link(link(link(h, r0, e2), r1, e3), r2, e0),
        (r2 + 1 : U32), (r0 + 1 : U32)), (r2 + 2 : U32), (r1 + 1 : U32)), r3, e1), (r3 + 1 : U32), (r0 + 2 : U32)), (r3 + 2 : U32), (r1 + 2 : U32))

def k.dist.c(r: H & U32, +r0: U32, +r1: U32, +e0: U32, +e2: U32, +e3: U32) -> H:
  (h, +r2) = r
  link(link(link(link(link(h, r0, e2), r1, e3), r2, e0), (r2 + 1 : U32), (r0 + 1 : U32)), (r2 + 2 : U32), (r1 + 1 : U32))

def k.dist.b(r: H & U32, +r0: U32, +hm: U32, +e0: U32, +e2: U32, +e3: U32) -> H:
  (h, +r1) = r
  k.dist.c(node(h, hm), r0, r1, e0, e2, e3)

def k.dist(r: H & U32, +f: U32, +hm: U32, +e0: U32, +e2: U32, +e3: U32) -> H:
  (h, +r0) = r
  k.dist.b(node2(h, 9, 3, f), r0, hm, e0, e2, e3)

def k.cdata.b(r: H & U32, +r0: U32, +e0: U32, +e1: U32) -> H:
  (h, +r1) = r
  link(link(h, r0, e0), r1, e1)

def k.cdata(r: H & U32, +tag: U32, +v: U32, +e0: U32, +e1: U32) -> H:
  (h, +r0) = r
  k.cdata.b(node3(h, 5, 2, tag, 3, v), r0, e0, e1)

def k.call(r: H & U32, +e0: U32, +e1: U32) -> H:
  (h, +r0) = r
  link(link(h, r0, e0), (r0 + 1 : U32), e1)

def k.compute(r: H & U32, +e0: U32) -> H:
  (h, +r0) = r
  link(h, r0, e0)

# a data node's tag and value, a call's function
type D is Data:
  D{+tag: U32, +v: U32}

def dat.v(r: H & U32, +tag: U32) -> H & D:
  (h, +v) = r
  (h, D{tag, v})

def dat.t(r: H & U32, +b: U32) -> H & D:
  (h, +tag) = r
  dat.v(rd(h, (b + 3 : U32)), tag)

def dat(h: H, +b: U32) -> H & D:
  dat.t(rd(h, (b + 2 : U32)), b)

def apply_tag.t(+f: U32, +tag: U32, +v: U32) -> D:
  match f tag:
    case 2 1:
      D{1, (v + 1 : U32)}
    case _ _:
      D{0, 0}

# succ of a number, else an error (the tag 0)
def apply_tag(+f: U32, d: D) -> D:
  match d:
    case D{+tag, +v}:
      apply_tag.t(f, tag, v)

def r.cdata.d(d: D, h: H, +a: U32, +b: U32, +e0: U32, +e1: U32) -> H:
  match d:
    case D{+tag, +v}:
      k.cdata(node3(fresh(h, a, b), 5, 2, tag, 3, v), tag, v, e0, e1)

def r.cdata(r: H & D, +a: U32, +b: U32, +e0: U32, +e1: U32) -> H:
  (h, d) = r
  r.cdata.d(d, h, a, b, e0, e1)

def r.call.d(d: D, h: H, +a: U32, +b: U32, +e0: U32, +e1: U32) -> H:
  match d:
    case D{+tag, +v}:
      match tag:
        case 2:
          k.call(node2(fresh(h, a, b), 9, 3, tag), e0, e1)
        case _:
          h_err(h)

def r.call(r: H & D, +a: U32, +b: U32, +e0: U32, +e1: U32) -> H:
  (h, d) = r
  r.call.d(d, h, a, b, e0, e1)

def r.compute.e(d: D, h: H, +a: U32, +b: U32, +e0: U32) -> H:
  match d:
    case D{+tag, +v}:
      err_if(U32.is_eq(tag, 0), k.compute(node3(fresh(h, a, b), 5, 2, tag, 3, v), e0))

def r.compute.d(r: H & D, +f: U32, +a: U32, +b: U32, +e0: U32) -> H:
  (h, d) = r
  r.compute.e(apply_tag(f, d), h, a, b, e0)

def r.compute(r: H & U32, +a: U32, +b: U32, +e0: U32) -> H:
  (h, +f) = r
  r.compute.d(dat(h, b), f, a, b, e0)

def r.dist(r: H & U32, +a: U32, +b: U32, +hb: U32, +e0: U32, +e2: U32, +e3: U32) -> H:
  (h, +f) = r
  k.dist(node2(fresh(h, a, b), 9, 3, f), f, hd(4, fld(hb)), e0, e2, e3)

def r.beta(eq: Bool, h: H, +a: U32, +b: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> H:
  match eq:
    case True{}:
      k.two(h, a, b, e0, e3, e1, e2)
    case False{}:
      h_err(h)

def r.fans(eq: Bool, h: H, +a: U32, +b: U32, +ha: U32, +hb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> H:
  match eq:
    case True{}:
      k.two(h, a, b, e0, e2, e1, e3)
    case False{}:
      k.comm(mk4(fresh(h, a, b), hd(4, fld(hb)), hd(4, fld(hb)), hd(3, fld(ha)), hd(3, fld(ha))), e0, e1, e2, e3)

# the rewrite for A (negative principal) meeting B, by kind
def rewrite(+ka: U32, +kb: U32, h: H, +a: U32, +b: U32, +ha: U32, +hb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32) -> H:
  match ka kb:
    case 2 1:
      r.beta(U32.is_eq(fld(ha), fld(hb)), h, a, b, e0, e1, e2, e3)
    case 3 4:
      r.fans(U32.is_eq(fld(ha), fld(hb)), h, a, b, ha, hb, e0, e1, e2, e3)
    case 3 1:
      k.cfn(mk4(fresh(h, a, b), hd(1, fld(hb)), hd(1, fld(hb)), hd(3, fld(ha)), hd(4, fld(ha))), e0, e1, e2, e3)
    case 3 5:
      r.cdata(dat(h, b), a, b, e0, e1)
    case 2 4:
      k.apsup(mk4(fresh(h, a, b), hd(2, fld(ha)), hd(2, fld(ha)), hd(3, fld(hb)), hd(4, fld(hb))), e0, e1, e2, e3)
    case 2 5:
      r.call(dat(h, b), a, b, e0, e1)
    case 9 5:
      r.compute(rd(h, (a + 3 : U32)), a, b, e0)
    case 9 4:
      r.dist(rd(h, (a + 3 : U32)), a, b, hb, e0, e2, e3)
    case 8 _:
      h
    case _ _:
      h_err(h)

# Interaction
# ===========

def mine(+e: U32, +a: U32, +b: U32) -> Bool:
  U32.is_ne(e, nil()) && (U32.is_eq((e >> 2n : U32), (a >> 2n : U32)) || U32.is_eq((e >> 2n : U32), (b >> 2n : U32)))

def aux(+has: Bool, +l: U32) -> U32:
  match has:
    case True{}:
      l
    case False{}:
      nil()

def go.ext2(+a: U32, +b: U32, +ha: U32, +hb: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, h: H) -> H:
  err_if(mine(e0, a, b) || mine(e1, a, b) || mine(e2, a, b) || mine(e3, a, b),
    rewrite(kind(ha), kind(hb), h, a, b, ha, hb, e0, e1, e2, e3))

def go.ext(+a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32, +b1: U32, +b2: U32, h: H) -> H:
  go.ext2(a, b, ha, hb, aux(U32.is_ge(arity(kind(ha)), 2), a1), aux(U32.is_ge(arity(kind(ha)), 3), a2),
    aux(U32.is_ge(arity(kind(hb)), 2), b1), aux(U32.is_ge(arity(kind(hb)), 3), b2), h)

def go.b2(r: H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32, +b1: U32) -> H:
  (h, +b2) = r
  go.ext(a, b, ha, hb, a1, a2, b1, b2, h)

def go.b1(r: H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32, +a2: U32) -> H:
  (h, +b1) = r
  go.b2(rd(h, (b + 3 : U32)), a, b, ha, hb, a1, a2, b1)

def go.a2(r: H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32, +a1: U32) -> H:
  (h, +a2) = r
  go.b1(rd(h, (b + 2 : U32)), a, b, ha, hb, a1, a2)

def go.a1(r: H & U32, +a: U32, +b: U32, +ha: U32, +hb: U32) -> H:
  (h, +a1) = r
  go.a2(rd(h, (a + 3 : U32)), a, b, ha, hb, a1)

# a's principal is negative
def go(h: H, +a: U32, +b: U32, +ha: U32, +hb: U32) -> H:
  go.a1(rd(h, (a + 2 : U32)), a, b, ha, hb)

def ori(neg: Bool, h: H, +x: U32, +y: U32, +hx: U32, +hy: U32) -> H:
  match neg:
    case True{}:
      go(h, x, y, hx, hy)
    case False{}:
      go(h, y, x, hy, hx)

def int.y(r: H & U32, +x: U32, +y: U32, +hx: U32) -> H:
  (h, +hy) = r
  ori(is_neg(kind(hx)), h, x, y, hx, hy)

def int.x(r: H & U32, +x: U32, +y: U32) -> H:
  (h, +hx) = r
  int.y(rd(h, y), x, y, hx)

def interact(h: H, +x: U32, +y: U32) -> H:
  int.x(rd(h, x), x, y)

def pop.y(r: KM.M & U32, w: KM.M, fs: KM.M, +nf: U32, +fresh: U32, +nr: U32, +itrs: U32, +errs: U32, +x: U32) -> H:
  (rs, +y) = r
  interact(H{w, fs, nf, fresh, rs, nr, itrs, errs}, x, y)

def pop.x(r: KM.M & U32, w: KM.M, fs: KM.M, +nf: U32, +fresh: U32, +nr: U32, +itrs: U32, +errs: U32) -> H:
  (rs, +x) = r
  pop.y(KM.m_get(rs, ((nr * 2 : U32) + 1 : U32)), w, fs, nf, fresh, nr, itrs, errs, x)

# reduce active pairs, newest first, until none is left or fuel runs out
def run(n: Nat, h: H) -> H:
  match n:
    case 0n:
      h
    case 1n+p:
      match h:
        case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs}:
          match nr:
            case 0:
              H{w, fs, nf, fresh, rs, nr, itrs, errs}
            case _:
              run(p, pop.x(KM.m_get(rs, ((nr - 1 : U32) * 2 : U32)), w, fs, nf, fresh, (nr - 1 : U32), (itrs + 1 : U32), errs))

# Loading a template
# ==================

def tag_of(v: V.Val) -> D:
  match v:
    case V.VNum{+n}:
      D{1, n}
    case V.VFun{+op, +need, args}:
      D{(op + 1 : U32), 0}
    case _:
      D{0, 0}

def load.data.d(d: D, h: H, +n: U32) -> H:
  match d:
    case D{+tag, +v}:
      wr(wr(h, (n + 2 : U32), tag), (n + 3 : U32), v)

def load.data(r: H & U32, d: D) -> H:
  (h, +n) = r
  load.data.d(d, h, n)

def drop_ref(r: H & U32) -> H:
  (h, +n) = r
  h

def load.node(h: H, t: T.TNode) -> H:
  match t:
    case T.TF{k, +site, +lvl}:
      drop_ref(node(h, hd(N.kcode(k), site)))
    case T.TN{k, p}:
      match p:
        case V.PVal{v}:
          load.data(node(h, hd(N.kcode(k), 0)), tag_of(v))
        case V.PLvl{+l}:
          drop_ref(node(h, hd(N.kcode(k), l)))
        case _:
          drop_ref(node(h, hd(N.kcode(k), 0)))

def load.nodes(ns: List<&2, T.TNode>, h: H) -> H:
  match ns:
    case Nil{}:
      h
    case Con{t, rest}:
      load.nodes(rest, load.node(h, t))

def tref(e: T.TEnd) -> U32:
  match e:
    case T.TE{+n, +p}:
      ((n << 2n : U32) + p : U32)

def load.links(ls: List<&2, T.TLink>, h: H) -> H:
  match ls:
    case Nil{}:
      h
    case Con{T.TL{x, y}, rest}:
      load.links(rest, link(h, tref(x), tref(y)))

type L is Type:
  L{h: H, +root: U32}

def load.root(r: H & U32, +x: U32) -> L:
  (h, +root) = r
  L{link(h, root, x), root}

def load(t: T.Tpl) -> L:
  match t:
    case T.Tpl{nodes, links, root, +size}:
      load.root(node(load.links(links, load.nodes(nodes, h_new())), 8), tref(root))

# Running
# =======

def counts(+itrs: U32, +errs: U32) -> String:
  U32.show(itrs) ++ " interactions, " ++ U32.show(errs) ++ " errors"

def show.dd(d: D, +itrs: U32, +errs: U32) -> String:
  match d:
    case D{+tag, +v}:
      match tag:
        case 1:
          U32.show(v) ++ ", " ++ counts(itrs, errs)
        case _:
          "no value, " ++ counts(itrs, errs)

def show.d(r: H & D, +itrs: U32, +errs: U32) -> String:
  (h, d) = r
  show.dd(d, itrs, errs)

def show.kk(+k: U32, h: H, +pn: U32, +itrs: U32, +errs: U32) -> String:
  match k:
    case 5:
      show.d(dat(h, pn), itrs, errs)
    case _:
      "no value, " ++ counts(itrs, errs)

def show.k2(r: H & U32, +pn: U32, +itrs: U32, +errs: U32) -> String:
  (h, +hp) = r
  show.kk(kind(hp), h, pn, itrs, errs)

def show.p(r: H & U32, +itrs: U32, +errs: U32) -> String:
  (h, +p) = r
  show.k2(rd(h, (p .&. 4294967292 : U32)), (p .&. 4294967292 : U32), itrs, errs)

def show(l: L) -> String:
  match l:
    case L{h, +root}:
      match h:
        case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs}:
          show.p(rd(H{w, fs, nf, fresh, rs, nr, itrs, errs}, (root + 1 : U32)), itrs, errs) ++ ", " ++ U32.show(fresh) ++ " nodes at most"

def run_l(l: L, +fuel: Nat) -> L:
  match l:
    case L{h, +root}:
      L{run(fuel, h), root}

def main.k(+k: U32) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    +res : String = show(run_l(load(X.t_pow(k, 2)), 268435456n))
    +t1 : Nat <- IO.now()
    IO.print("kernel k " ++ U32.show(k) ++ ": " ++ res ++ " in " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{p, r}:
      match r:
        case Con{a, r2}:
          main.k(Maybe.default(&2, U32, U32.read(a), 10))
        case Nil{}:
          IO.print("usage: kernel <k>")
    case Nil{}:
      IO.print("usage: kernel <k>")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
