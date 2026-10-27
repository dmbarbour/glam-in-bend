import Base
import ./val.bend as V
import ./kmem_grow.bend as KM

# The kernel's primitives (spike-node-layout in
# docs/plans/EvalSpike_2026-10-26.md, `net-nodes-double`): a net as four-
# word nodes in storage that doubles, its free list and active pairs, and a
# data table of its own.
#
# A node n is words 4n .. 4n + 3. Word 0, the header: the kind code (8
# bits, as net.bend's kcode) and a 24-bit field: a function's or an
# application's level, a fan's level (its site, in nets built without
# levels), a control's index. Words 1 .. 3: the links of ports 0 .. 2, a
# reference being n * 4 + port. A node with fewer than three ports keeps a
# payload word in word 3: a data node's or a call's value, a control's
# offset (bit 31 set to raise, the amount below). A value word is a number
# below 2^31 inline, or with bit 31 set an index into the data table.

def nil() -> U32:
  4294967295

# Capacity: 2^21 nodes, 2^21 active pairs, 2^20 data entries, 2^24 levels;
# passing any is an error.
def lvl_cap() -> U32:
  16777216

# The data table
# ==============

type DT is Type:
  DT{a: Array<V.Val>, +n: U32, +cap: U32, +d: Nat}

def dt_new() -> DT:
  DT{Array.new(V.Val, 4n, V.VUnit{}), 0, 16, 4n}

def dt_get.fin(r: Array<V.Val> & V.Val, +n: U32, +cap: U32, +d: Nat) -> DT & V.Val:
  (a, v) = r
  (DT{a, n, cap, d}, v)

def dt_get(t: DT, +i: U32) -> DT & V.Val:
  match t:
    case DT{a, +n, +cap, +d}:
      dt_get.fin(Array.get(V.Val, a, i), n, cap, d)

type DC is Type:
  DC{src: Array<V.Val>, dst: Array<V.Val>}

def dc.step(r: Array<V.Val> & V.Val, dst: Array<V.Val>, +i: U32) -> DC:
  (src, v) = r
  DC{src, Array.set(V.Val, dst, i, v)}

def dt_copy(k: Nat, +i: U32, c: DC) -> Array<V.Val>:
  match k:
    case 0n:
      match c:
        case DC{src, dst}:
          dst
    case 1n+p:
      match c:
        case DC{src, dst}:
          dt_copy(p, (i + 1 : U32), dc.step(Array.get(V.Val, src, i), dst, i))

def dt_add.go(full: Bool, t: DT, v: V.Val) -> DT & U32:
  match full:
    case True{}:
      match t:
        case DT{a, +n, +cap, +d}:
          (DT{Array.set(V.Val, dt_copy(U32.to_nat(cap), 0, DC{a, Array.new(V.Val, Nat.add(d, 1n), V.VUnit{})}), n, v),
            (n + 1 : U32), (cap * 2 : U32), Nat.add(d, 1n)}, n)
    case False{}:
      match t:
        case DT{a, +n, +cap, +d}:
          (DT{Array.set(V.Val, a, n, v), (n + 1 : U32), cap, d}, n)

# a new entry for v: its index
def dt_add(t: DT, v: V.Val) -> DT & U32:
  match t:
    case DT{a, +n, +cap, +d}:
      dt_add.go(U32.is_ge(n, cap), DT{a, n, cap, d}, v)

# The state
# =========

type H is Type:
  H{w: KM.M, fs: KM.M, +nf: U32, +fresh: U32, rs: KM.M, +nr: U32, +itrs: U32, +errs: U32, dt: DT}

def h_new() -> H:
  H{KM.m_new(23n), KM.m_new(21n), 0, 0, KM.m_new(22n), 0, 0, 0, dt_new()}

def h_err(h: H) -> H:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      H{w, fs, nf, fresh, rs, nr, itrs, (errs + 1 : U32), dt}

def err_if(bad: Bool, h: H) -> H:
  match bad:
    case True{}:
      h_err(h)
    case False{}:
      h

# Words
# =====

def rd.fin(r: KM.M & U32, fs: KM.M, +nf: U32, +fresh: U32, rs: KM.M, +nr: U32, +itrs: U32, +errs: U32, dt: DT) -> H & U32:
  (w, +v) = r
  (H{w, fs, nf, fresh, rs, nr, itrs, errs, dt}, v)

def rd(h: H, +i: U32) -> H & U32:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      rd.fin(KM.m_get(w, i), fs, nf, fresh, rs, nr, itrs, errs, dt)

def wr(h: H, +i: U32, +v: U32) -> H:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      H{KM.m_set(w, i, v), fs, nf, fresh, rs, nr, itrs, errs, dt}

def push.go(ok: Bool, h: H, +x: U32, +y: U32) -> H:
  match ok:
    case False{}:
      h_err(h)
    case True{}:
      match h:
        case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
          H{w, fs, nf, fresh, KM.m_set(KM.m_set(rs, (nr * 2 : U32), x), ((nr * 2 : U32) + 1 : U32), y), (nr + 1 : U32), itrs, errs, dt}

def push.ens(r: KM.M & Bool, w: KM.M, fs: KM.M, +nf: U32, +fresh: U32, +nr: U32, +itrs: U32, +errs: U32, dt: DT, +x: U32, +y: U32) -> H:
  (rs, +ok) = r
  push.go(ok, H{w, fs, nf, fresh, rs, nr, itrs, errs, dt}, x, y)

def push(h: H, +x: U32, +y: U32) -> H:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      push.ens(KM.m_ensure(rs, ((nr * 2 : U32) + 2 : U32)), w, fs, nf, fresh, nr, itrs, errs, dt, x, y)

def link.push(both: Bool, h: H, +x: U32, +y: U32) -> H:
  match both:
    case True{}:
      push(h, x, y)
    case False{}:
      h

# link two ports (word n * 4 + 1 + p is port p's link: the reference plus
# one), an active pair when both are principal
def link(h: H, +x: U32, +y: U32) -> H:
  link.push(U32.is_eq((x .&. 3 : U32), 0) && U32.is_eq((y .&. 3 : U32), 0), wr(wr(h, (x + 1 : U32), y), (y + 1 : U32), x), x, y)

# Nodes
# =====

def alloc.pop(r: KM.M & U32, w: KM.M, +nf: U32, +fresh: U32, rs: KM.M, +nr: U32, +itrs: U32, +errs: U32, dt: DT) -> H & U32:
  (fs, +n) = r
  (H{w, fs, (nf - 1 : U32), fresh, rs, nr, itrs, errs, dt}, (n << 2n : U32))

def alloc.fresh(ok: Bool, h: H) -> H & U32:
  match ok:
    case False{}:
      (h_err(h), 0)
    case True{}:
      match h:
        case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
          (H{w, fs, nf, (fresh + 1 : U32), rs, nr, itrs, errs, dt}, (fresh << 2n : U32))

def alloc.ens.f(r: KM.M & Bool, w: KM.M, +okw: Bool, +nf: U32, +fresh: U32, rs: KM.M, +nr: U32, +itrs: U32, +errs: U32, dt: DT) -> H & U32:
  (fs, +okf) = r
  alloc.fresh(okw && okf, H{w, fs, nf, fresh, rs, nr, itrs, errs, dt})

def alloc.ens.w(r: KM.M & Bool, fs: KM.M, +nf: U32, +fresh: U32, rs: KM.M, +nr: U32, +itrs: U32, +errs: U32, dt: DT) -> H & U32:
  (w, +okw) = r
  alloc.ens.f(KM.m_ensure(fs, (fresh + 1 : U32)), w, okw, nf, fresh, rs, nr, itrs, errs, dt)

def alloc(h: H) -> H & U32:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      match nf:
        case 0:
          alloc.ens.w(KM.m_ensure(w, ((fresh + 1 : U32) * 4 : U32)), fs, nf, fresh, rs, nr, itrs, errs, dt)
        case _:
          alloc.pop(KM.m_get(fs, (nf - 1 : U32)), w, nf, fresh, rs, nr, itrs, errs, dt)

def node.fin(r: H & U32, +hd: U32, +p: U32) -> H & U32:
  (h, +n) = r
  (wr(wr(h, n, hd), (n + 3 : U32), p), n)

# a node with header hd and payload word p (overwritten by port 2's link
# in a node with three ports): its reference, port 0
def node(h: H, +hd: U32, +p: U32) -> H & U32:
  node.fin(alloc(h), hd, p)

def free.fin(h: H, +r: U32) -> H:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      H{w, KM.m_set(fs, nf, (r >> 2n : U32)), (nf + 1 : U32), fresh, rs, nr, itrs, errs, dt}

def free(h: H, +r: U32) -> H:
  free.fin(wr(h, r, 0), r)

def fresh2(h: H, +a: U32, +b: U32) -> H:
  free(free(h, a), b)

# Headers, levels, data
# =====================

def hd(+k: U32, +f: U32) -> U32:
  (k .|. (f << 8n : U32) : U32)

def kind(+h: U32) -> U32:
  (h .&. 255 : U32)

def fld(+h: U32) -> U32:
  (h >> 8n : U32)

def off_up(+o: U32) -> Bool:
  U32.is_ne((o .&. 2147483648 : U32), 0)

def off_by(+o: U32) -> U32:
  (o .&. 2147483647 : U32)

def lift.go(+above: Bool, +up: Bool, +by: U32, +j: U32) -> U32:
  match above up:
    case True{} True{}:
      (j + by : U32)
    case True{} False{}:
      (j - by : U32)
    case False{} _:
      j

# level or index j after the control with index n and offset o
def lift(+n: U32, +o: U32, +j: U32) -> U32:
  lift.go(U32.is_gt(j, n), off_up(o), off_by(o), j)

# raising j through the control would pass the field's 24 bits
def lift_wraps(+n: U32, +o: U32, +j: U32) -> Bool:
  off_up(o) && U32.is_gt(j, n) && U32.is_ge((j + off_by(o) : U32), lvl_cap())

def dt_op.fin(r: DT & U32, w: KM.M, fs: KM.M, +nf: U32, +fresh: U32, rs: KM.M, +nr: U32, +itrs: U32, +errs: U32) -> H & U32:
  (dt, +i) = r
  (H{w, fs, nf, fresh, rs, nr, itrs, errs, dt}, i)

# a new data entry: its index
def data_add(h: H, v: V.Val) -> H & U32:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      dt_op.fin(dt_add(dt, v), w, fs, nf, fresh, rs, nr, itrs, errs)

def data_get.fin(r: DT & V.Val, w: KM.M, fs: KM.M, +nf: U32, +fresh: U32, rs: KM.M, +nr: U32, +itrs: U32, +errs: U32) -> H & V.Val:
  (dt, v) = r
  (H{w, fs, nf, fresh, rs, nr, itrs, errs, dt}, v)

def data_get(h: H, +i: U32) -> H & V.Val:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      data_get.fin(dt_get(dt, i), w, fs, nf, fresh, rs, nr, itrs, errs)

def is_tix(+w: U32) -> Bool:
  U32.is_ne((w .&. 2147483648 : U32), 0)

def data_get.go(tab: Bool, h: H, +w: U32) -> H & V.Val:
  match tab:
    case True{}:
      data_get(h, (w .&. 2147483647 : U32))
    case False{}:
      (h, V.VNum{w})

# the value a value word stands for
def val_of(h: H, +w: U32) -> H & V.Val:
  data_get.go(is_tix(w), h, w)

def tix(r: H & U32) -> H & U32:
  (h, +i) = r
  (h, (i .|. 2147483648 : U32))

def put.n(small: Bool, h: H, +n: U32) -> H & U32:
  match small:
    case True{}:
      (h, n)
    case False{}:
      tix(data_add(h, V.VNum{n}))

# a value word for v: inline if a small number, else a new entry
def put(h: H, v: V.Val) -> H & U32:
  match v:
    case V.VNum{+n}:
      put.n(U32.is_lt(n, 2147483648), h, n)
    case _:
      tix(data_add(h, v))

def apply.b(r: H & V.Val, vf: V.Val) -> H & U32:
  (h, vx) = r
  put(h, V.apply_fn(vf, vx))

def apply.a(r: H & V.Val, +wb: U32) -> H & U32:
  (h, vf) = r
  apply.b(val_of(h, wb), vf)

# the value word for value word wa's function applied to wb's value
def apply(h: H, +wa: U32, +wb: U32) -> H & U32:
  apply.a(val_of(h, wa), wb)

def is_fn(v: V.Val) -> Bool:
  match v:
    case V.VFun{+op, +need, args}:
      True{}
    case _:
      False{}

def data_is_fn.fin(r: H & V.Val) -> H & Bool:
  (h, v) = r
  (h, is_fn(v))

def data_is_fn.go(tab: Bool, h: H, +w: U32) -> H & Bool:
  match tab:
    case True{}:
      data_is_fn.fin(val_of(h, w))
    case False{}:
      (h, False{})

# does value word w stand for a function? An inline word is a number.
def data_is_fn(h: H, +w: U32) -> H & Bool:
  data_is_fn.go(is_tix(w), h, w)

# Active pairs
# ============

# the newest active pair, counted as an interaction, if any
type Pop is Type:
  Pop{h: H, +x: U32, +y: U32, +ok: Bool}

def pop.y(r: KM.M & U32, w: KM.M, fs: KM.M, +nf: U32, +fresh: U32, +nr: U32, +itrs: U32, +errs: U32, dt: DT, +x: U32) -> Pop:
  (rs, +y) = r
  Pop{H{w, fs, nf, fresh, rs, nr, itrs, errs, dt}, x, y, True{}}

def pop.x(r: KM.M & U32, w: KM.M, fs: KM.M, +nf: U32, +fresh: U32, +nr: U32, +itrs: U32, +errs: U32, dt: DT) -> Pop:
  (rs, +x) = r
  pop.y(KM.m_get(rs, ((nr * 2 : U32) + 1 : U32)), w, fs, nf, fresh, nr, itrs, errs, dt, x)

def pop(h: H) -> Pop:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      match nr:
        case 0:
          Pop{H{w, fs, nf, fresh, rs, nr, itrs, errs, dt}, 0, 0, False{}}
        case _:
          pop.x(KM.m_get(rs, ((nr - 1 : U32) * 2 : U32)), w, fs, nf, fresh, (nr - 1 : U32), (itrs + 1 : U32), errs, dt)

def uncount(h: H) -> H:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      H{w, fs, nf, fresh, rs, nr, (itrs - 1 : U32), errs, dt}

# a pair popped when fuel ran out goes back, uncounted
def unpop(pp: Pop) -> H:
  match pp:
    case Pop{h, +x, +y, +ok}:
      match ok:
        case True{}:
          push(uncount(h), x, y)
        case False{}:
          h
