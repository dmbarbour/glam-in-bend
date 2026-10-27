import Base
import ./val.bend as V
import ./kmem_grow.bend as KM

# The kernel's primitives (spike-node-layout in
# docs/plans/EvalSpike_2026-10-26.md, `net-nodes-double`): a net as four-
# word nodes in storage that doubles, its free list and active pairs, and a
# data table of its own, kept linear.
#
# A node n is words 4n .. 4n + 3. Word 0, the header: the kind code (8
# bits: the rule kind, as net.bend's kcode, in the low 4, the value form in
# the high 4) and a 24-bit field: a function's or an application's level,
# a fan's level (its site, in nets built without levels), a control's
# index, a builtin's op. Words 1 .. 3: the links of ports 0 .. 2, a
# reference being n * 4 + port. A data node, with one port, holds its value
# in words 2 and 3; a call keeps its function in word 3, a control its
# offset (bit 31 set to raise, the amount below).
#
# Value forms: 0, an entry in the data table (the word its index); 1, a
# number (the word); 2, a builtin with no argument collected yet (the
# field its op, the word how many it needs). The table is linear: an entry
# has one owner, is handed on when its owner's value moves, duplicated
# when it is copied, freed when it is dropped.

def nil() -> U32:
  4294967295

# Capacity: 2^21 nodes, 2^21 active pairs, 2^20 data entries, 2^24 levels;
# passing any is an error.
def lvl_cap() -> U32:
  16777216

# The data table
# ==============

# entries, a stack of free indices beside them, the high-water mark
type DT is Type:
  DT{a: Array<V.Val>, fs: Array<U32>, +nf: U32, +n: U32, +cap: U32, +d: Nat}

def dt_new() -> DT:
  DT{Array.new(V.Val, 4n, V.VUnit{}), [0 : U32^4n], 0, 0, 16, 4n}

def dt_get.fin(r: Array<V.Val> & V.Val, fs: Array<U32>, +nf: U32, +n: U32, +cap: U32, +d: Nat) -> DT & V.Val:
  (a, v) = r
  (DT{a, fs, nf, n, cap, d}, v)

# entry i's value, the entry kept
def dt_get(t: DT, +i: U32) -> DT & V.Val:
  match t:
    case DT{a, fs, +nf, +n, +cap, +d}:
      dt_get.fin(Array.get(V.Val, a, i), fs, nf, n, cap, d)

def dt_take.fin(r: Array<V.Val> & V.Val, fs: Array<U32>, +nf: U32, +n: U32, +cap: U32, +d: Nat, +i: U32) -> DT & V.Val:
  (a, v) = r
  (DT{a, Array.set(U32, fs, nf, i), (nf + 1 : U32), n, cap, d}, v)

# entry i's value, the entry freed
def dt_take(t: DT, +i: U32) -> DT & V.Val:
  match t:
    case DT{a, fs, +nf, +n, +cap, +d}:
      dt_take.fin(Array.swap(V.Val, a, i, V.VUnit{}), fs, nf, n, cap, d, i)

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

type FC is Type:
  FC{src: Array<U32>, dst: Array<U32>}

def fc.step(r: Array<U32> & U32, dst: Array<U32>, +i: U32) -> FC:
  (src, +v) = r
  FC{src, Array.set(U32, dst, i, v)}

def fs_copy(k: Nat, +i: U32, c: FC) -> Array<U32>:
  match k:
    case 0n:
      match c:
        case FC{src, dst}:
          dst
    case 1n+p:
      match c:
        case FC{src, dst}:
          fs_copy(p, (i + 1 : U32), fc.step(Array.get(U32, src, i), dst, i))

def dt_grow(t: DT) -> DT:
  match t:
    case DT{a, fs, +nf, +n, +cap, +d}:
      DT{dt_copy(U32.to_nat(cap), 0, DC{a, Array.new(V.Val, Nat.add(d, 1n), V.VUnit{})}),
        fs_copy(U32.to_nat(cap), 0, FC{fs, [0 : U32^Nat.add(d, 1n)]}), nf, n, (cap * 2 : U32), Nat.add(d, 1n)}

def dt_put.app(t: DT, v: V.Val) -> DT & U32:
  match t:
    case DT{a, fs, +nf, +n, +cap, +d}:
      (DT{Array.set(V.Val, a, n, v), fs, nf, (n + 1 : U32), cap, d}, n)

def dt_put.new(full: Bool, t: DT, v: V.Val) -> DT & U32:
  match full:
    case True{}:
      dt_put.app(dt_grow(t), v)
    case False{}:
      dt_put.app(t, v)

def dt_put.reuse(r: Array<U32> & U32, a: Array<V.Val>, +nf: U32, +n: U32, +cap: U32, +d: Nat, v: V.Val) -> DT & U32:
  (fs, +i) = r
  (DT{Array.set(V.Val, a, i, v), fs, (nf - 1 : U32), n, cap, d}, i)

# a new entry for v, reusing a freed one if any: its index
def dt_put(t: DT, v: V.Val) -> DT & U32:
  match t:
    case DT{a, fs, +nf, +n, +cap, +d}:
      match nf:
        case 0:
          dt_put.new(U32.is_ge(n, cap), DT{a, fs, nf, n, cap, d}, v)
        case _:
          dt_put.reuse(Array.get(U32, fs, (nf - 1 : U32)), a, nf, n, cap, d, v)

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

def port(+r: U32) -> U32:
  (r .&. 3 : U32)

# link two ports (word n * 4 + 1 + p is port p's link: the reference plus
# one), an active pair when both are principal
def link(h: H, +x: U32, +y: U32) -> H:
  link.push(U32.is_eq(port(x), 0) && U32.is_eq(port(y), 0), wr(wr(h, (x + 1 : U32), y), (y + 1 : U32), x), x, y)

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

def node.word.k(+k: U32) -> U32:
  match k:
    case 5:
      2
    case _:
      3

def node.word(+hd: U32) -> U32:
  node.word.k((hd .&. 15 : U32))

def node.fin(r: H & U32, +hd: U32, +p: U32) -> H & U32:
  (h, +n) = r
  (wr(wr(h, n, hd), (n + node.word(hd) : U32), p), n)

# a node with header hd and payload word p, word 2 of a data node, word 3
# of others (overwritten by port 2's link in a node with three ports): its
# reference, port 0
def node(h: H, +hd: U32, +p: U32) -> H & U32:
  node.fin(alloc(h), hd, p)

def base(+r: U32) -> U32:
  (r .&. 4294967292 : U32)

def free.fin(h: H, +r: U32) -> H:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      H{w, KM.m_set(fs, nf, (r >> 2n : U32)), (nf + 1 : U32), fresh, rs, nr, itrs, errs, dt}

# free the node behind reference r, whatever its port
def free(h: H, +r: U32) -> H:
  free.fin(wr(h, base(r), 0), r)

def fresh2(h: H, +a: U32, +b: U32) -> H:
  free(free(h, a), b)

# Headers, levels, values
# =======================

def hd(+k: U32, +f: U32) -> U32:
  (k .|. (f << 8n : U32) : U32)

# a header from rule kind k, value form m and field f
def hd2(+k: U32, +m: U32, +f: U32) -> U32:
  ((k .|. (m << 4n : U32) : U32) .|. (f << 8n : U32) : U32)

def kind(+h: U32) -> U32:
  (h .&. 255 : U32)

def rk(+h: U32) -> U32:
  (h .&. 15 : U32)

def form(+h: U32) -> U32:
  ((h >> 4n : U32) .&. 15 : U32)

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

def dt_val.fin(r: DT & V.Val, w: KM.M, fs: KM.M, +nf: U32, +fresh: U32, rs: KM.M, +nr: U32, +itrs: U32, +errs: U32) -> H & V.Val:
  (dt, v) = r
  (H{w, fs, nf, fresh, rs, nr, itrs, errs, dt}, v)

def tab_put(h: H, v: V.Val) -> H & U32:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      dt_op.fin(dt_put(dt, v), w, fs, nf, fresh, rs, nr, itrs, errs)

def tab_get(h: H, +i: U32) -> H & V.Val:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      dt_val.fin(dt_get(dt, i), w, fs, nf, fresh, rs, nr, itrs, errs)

def tab_take(h: H, +i: U32) -> H & V.Val:
  match h:
    case H{w, fs, +nf, +fresh, rs, +nr, +itrs, +errs, dt}:
      dt_val.fin(dt_take(dt, i), w, fs, nf, fresh, rs, nr, itrs, errs)

# a value as a node holds it: its form, field and word
type PW is Data:
  PW{+m: U32, +f: U32, +w: U32}

def pw.tab(r: H & U32) -> H & PW:
  (h, +i) = r
  (h, PW{0, 0, i})

def put.fun(args: List<&2, V.Val>, h: H, +op: U32, +need: U32, v: V.Val) -> H & PW:
  match args:
    case Nil{}:
      (h, PW{2, op, need})
    case _:
      pw.tab(tab_put(h, v))

# a value in the form a node holds it: a number or a bare builtin in the
# node, anything else a new entry
def put(h: H, v: V.Val) -> H & PW:
  match v:
    case V.VNum{+n}:
      (h, PW{1, 0, n})
    case V.VFun{+op, +need, +args}:
      put.fun(args, h, op, need, V.VFun{op, need, args})
    case _:
      pw.tab(tab_put(h, v))

# the value a node of form m, field f, word w holds: taking it, an entry
# leaving the table
def take(h: H, +m: U32, +f: U32, +w: U32) -> H & V.Val:
  match m:
    case 1:
      (h, V.VNum{w})
    case 2:
      (h, V.VFun{f, w, Nil{}})
    case _:
      tab_take(h, w)

# the same, the entry kept
def peek(h: H, +m: U32, +f: U32, +w: U32) -> H & V.Val:
  match m:
    case 1:
      (h, V.VNum{w})
    case 2:
      (h, V.VFun{f, w, Nil{}})
    case _:
      tab_get(h, w)

def dup.e(r: H & V.Val) -> H & U32:
  (h, v) = r
  tab_put(h, v)

# the word for a copy of a value of form m: an entry duplicated (the Bend
# value shared), any other word as it is
def dup(h: H, +m: U32, +w: U32) -> H & U32:
  match m:
    case 0:
      dup.e(tab_get(h, w))
    case _:
      (h, w)

def drop.e(r: H & V.Val) -> H:
  (h, v) = r
  h

# a value dropped: an entry freed
def drop(h: H, +m: U32, +w: U32) -> H:
  match m:
    case 0:
      drop.e(tab_take(h, w))
    case _:
      h

def apply.b(r: H & V.Val, vf: V.Val) -> H & PW:
  (h, vx) = r
  put(h, V.apply_fn(vf, vx))

def apply.a(r: H & V.Val, +hb: U32, +pb: U32) -> H & PW:
  (h, vf) = r
  apply.b(take(h, form(hb), fld(hb), pb), vf)

# A's function (header ha, word pa) applied to B's value: both taken
def apply(h: H, +ha: U32, +pa: U32, +hb: U32, +pb: U32) -> H & PW:
  apply.a(take(h, form(ha), fld(ha), pa), hb, pb)

def is_fn(v: V.Val) -> Bool:
  match v:
    case V.VFun{+op, +need, args}:
      True{}
    case _:
      False{}

def is_fn.fin(r: H & V.Val) -> H & Bool:
  (h, v) = r
  (h, is_fn(v))

# is the value a function? A bare builtin is; a number is not.
def val_is_fn(h: H, +m: U32, +f: U32, +w: U32) -> H & Bool:
  match m:
    case 1:
      (h, False{})
    case 2:
      (h, True{})
    case _:
      is_fn.fin(tab_get(h, w))

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

# a node of rule kind k holding the value pw
def node_pw(h: H, +k: U32, pw: PW) -> H & U32:
  match pw:
    case PW{+m, +f, +w}:
      node(h, hd2(k, m, f), w)

# entries in use: the high-water mark less those freed
def dt_live(t: DT) -> U32:
  match t:
    case DT{a, fs, +nf, +n, +cap, +d}:
      (n - nf : U32)
