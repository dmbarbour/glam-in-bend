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
# field its op, the word how many it needs); 3, a builtin needing one more
# argument, one number collected (the field its op, the word the number).
# A builtin of forms 2 and 3 meeting a number runs natively, by V.num1 and
# V.num2, without building the Bend value. The table is linear: an entry
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

# entries, the high-water mark; a freed entry is a VFree linking the next
# (its index plus one, 0 for none), the head kept here the same way
type DT is Type:
  DT{a: Array<V.Val>, +fh: U32, +n: U32, +cap: U32, +d: Nat}

def dt_new() -> DT:
  DT{Array.new(V.Val, 4n, V.VUnit{}), 0, 0, 16, 4n}

def dt_get.fin(r: Array<V.Val> & V.Val, +fh: U32, +n: U32, +cap: U32, +d: Nat) -> DT & V.Val:
  (a, v) = r
  (DT{a, fh, n, cap, d}, v)

# entry i's value, the entry kept
def dt_get(t: DT, +i: U32) -> DT & V.Val:
  match t:
    case DT{a, +fh, +n, +cap, +d}:
      dt_get.fin(Array.get(V.Val, a, i), fh, n, cap, d)

def dt_take.fin(r: Array<V.Val> & V.Val, +n: U32, +cap: U32, +d: Nat, +i: U32) -> DT & V.Val:
  (a, v) = r
  (DT{a, (i + 1 : U32), n, cap, d}, v)

# entry i's value, the entry freed
def dt_take(t: DT, +i: U32) -> DT & V.Val:
  match t:
    case DT{a, +fh, +n, +cap, +d}:
      dt_take.fin(Array.swap(V.Val, a, i, V.VFree{fh}), n, cap, d, i)

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

def dt_grow(t: DT) -> DT:
  match t:
    case DT{a, +fh, +n, +cap, +d}:
      DT{dt_copy(U32.to_nat(cap), 0, DC{a, Array.new(V.Val, Nat.add(d, 1n), V.VUnit{})}),
        fh, n, (cap * 2 : U32), Nat.add(d, 1n)}

def dt_put.app(t: DT, v: V.Val) -> DT & U32:
  match t:
    case DT{a, +fh, +n, +cap, +d}:
      (DT{Array.set(V.Val, a, n, v), fh, (n + 1 : U32), cap, d}, n)

def dt_put.new(full: Bool, t: DT, v: V.Val) -> DT & U32:
  match full:
    case True{}:
      dt_put.app(dt_grow(t), v)
    case False{}:
      dt_put.app(t, v)

# the link a freed entry holds, VFree{0} in the last. Anything else marks
# a corrupt list: it ends here, and the audit reports the leak.
def dt_link(v: V.Val) -> U32:
  match v:
    case V.VFree{+k}:
      k
    case _:
      0

def dt_put.reuse(r: Array<V.Val> & V.Val, +n: U32, +cap: U32, +d: Nat, +i: U32) -> DT & U32:
  (a, old) = r
  (DT{a, dt_link(old), n, cap, d}, i)

# a new entry for v, reusing a freed one if any: its index
def dt_put(t: DT, v: V.Val) -> DT & U32:
  match t:
    case DT{a, +fh, +n, +cap, +d}:
      match fh:
        case 0:
          dt_put.new(U32.is_ge(n, cap), DT{a, fh, n, cap, d}, v)
        case _:
          dt_put.reuse(Array.swap(V.Val, a, (fh - 1 : U32), v), n, cap, d, (fh - 1 : U32))

def dt_dup.fin(r: Array<V.Val> & V.Val, +fh: U32, +n: U32, +cap: U32, +d: Nat) -> DT & U32:
  (a, v) = r
  dt_put(DT{a, fh, n, cap, d}, v)

# a new entry for a copy of entry i's value (the Bend value shared): its
# index
def dt_dup(t: DT, +i: U32) -> DT & U32:
  match t:
    case DT{a, +fh, +n, +cap, +d}:
      dt_dup.fin(Array.get(V.Val, a, i), fh, n, cap, d)

# The state
# =========
#
# Bend passes a record's fields one by one through every function that
# takes it, so each word of the state costs every step that carries it: at
# k 18 on `k 2 succ 0`, about 30 instructions an interaction a word. The
# state keeps flat what most steps touch; the rest sits in one cold
# record, which a recursive variant (never built) keeps Bend from
# flattening, so it travels as one word and is opened only to count an
# error, use the data table or grow. Opening it costs an allocation, so
# nothing a common path needs may live there.

# errors, interactions (counted by the run's fuel, set when it ends), how
# many nodes fit, the data table
type C is Type:
  C{+errs: U32, +itrs: U32, +wcap: U32, dt: DT}
  CBox{c: C}

# nodes, the free list's head, active pairs, the cold record. Every node
# not in use is on the free list: growing the store threads the new nodes
# onto it, so making a node is a pop, and the capacity, needed only to
# grow, stays cold. The pair stack holds one node of each active pair;
# the other is the peer of its principal port. A pair holds two live
# nodes and a node is in one at most, so the stack never holds more than
# half as many words as nodes fit: it grows with the node store (at least
# 64 words), and a push checks nothing.
type H is Type:
  H{w: KM.M, +fh: U32, rs: KM.M, +nr: U32, c: C}

# A net starts at 128 nodes, 2 KB, and 64 pair words (net-nodes-double);
# node words up to 2^23 (2^21 nodes), active pair words up to 2^22
def w_maxd() -> Nat:
  23n

def rs_maxd() -> Nat:
  22n

def link_of.go(more: Bool, +j: U32) -> U32:
  match more:
    case True{}:
      (j + 1 : U32)
    case False{}:
      0

# nodes i .. to - 1 threaded in order, the last ending the list
def thread(k: Nat, m: KM.M, +i: U32, +to: U32) -> KM.M:
  match k:
    case 0n:
      m
    case 1n+p:
      thread(p, KM.m_set(m, ((i << 2n : U32) + 1 : U32), link_of.go(U32.is_lt((i + 1 : U32), to), (i + 1 : U32))), (i + 1 : U32), to)

def h_new.rs(r: KM.M & U32, w: KM.M, +wcap: U32) -> H:
  (rs, +cr) = r
  H{thread(U32.to_nat(wcap), w, 0, wcap), 1, rs, 0, C{0, 0, wcap, dt_new()}}

def h_new.w(r: KM.M & U32) -> H:
  (w, +cw) = r
  h_new.rs(KM.m_new(6n, rs_maxd()), w, (cw >> 2n : U32))

def h_new() -> H:
  h_new.w(KM.m_new(9n, w_maxd()))

def c_err(c: C) -> C:
  match c:
    case C{+errs, +itrs, +wcap, dt}:
      C{(errs + 1 : U32), itrs, wcap, dt}
    case CBox{d}:
      CBox{d}

def h_err(h: H) -> H:
  match h:
    case H{w, +fh, rs, +nr, c}:
      H{w, fh, rs, nr, c_err(c)}

def err_if(bad: Bool, h: H) -> H:
  match bad:
    case True{}:
      h_err(h)
    case False{}:
      h

# interactions, errors, how many nodes fit, for reports
type HS is Data:
  HS{+itrs: U32, +errs: U32, +wcap: U32}

def c_stats(c: C) -> C & HS:
  match c:
    case C{+errs, +itrs, +wcap, dt}:
      (C{errs, itrs, wcap, dt}, HS{itrs, errs, wcap})
    case CBox{d}:
      (CBox{d}, HS{0, 0, 0})

def stats.fin(r: C & HS, w: KM.M, +fh: U32, rs: KM.M, +nr: U32) -> H & HS:
  (c, st) = r
  (H{w, fh, rs, nr, c}, st)

# interactions, errors and node capacity, the state kept
def stats(h: H) -> H & HS:
  match h:
    case H{w, +fh, rs, +nr, c}:
      stats.fin(c_stats(c), w, fh, rs, nr)

def c_count(c: C, +n: U32) -> C:
  match c:
    case C{+errs, +itrs, +wcap, dt}:
      C{errs, n, wcap, dt}
    case CBox{d}:
      CBox{d}

# the interactions a run made, recorded when it ends
def count(h: H, +n: U32) -> H:
  match h:
    case H{w, +fh, rs, +nr, c}:
      H{w, fh, rs, nr, c_count(c, n)}

# Words
# =====

def rd.fin(r: KM.M & U32, +fh: U32, rs: KM.M, +nr: U32, c: C) -> H & U32:
  (w, +v) = r
  (H{w, fh, rs, nr, c}, v)

def rd(h: H, +i: U32) -> H & U32:
  match h:
    case H{w, +fh, rs, +nr, c}:
      rd.fin(KM.m_get(w, i), fh, rs, nr, c)

def wr(h: H, +i: U32, +v: U32) -> H:
  match h:
    case H{w, +fh, rs, +nr, c}:
      H{KM.m_set(w, i, v), fh, rs, nr, c}

# push an active pair, x >< y, as x: the stack has room for every pair
# the nodes allow
def push(h: H, +x: U32, +y: U32) -> H:
  match h:
    case H{w, +fh, rs, +nr, c}:
      H{w, fh, KM.m_set(rs, nr, x), (nr + 1 : U32), c}

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

def rs_words.go(small: Bool, +half: U32) -> U32:
  match small:
    case True{}:
      64
    case False{}:
      half

# the pair stack's words for wcap nodes
def rs_words(+wcap: U32) -> U32:
  rs_words.go(U32.is_lt((wcap >> 1n : U32), 64), (wcap >> 1n : U32))

# the store doubled to wcap nodes: node wcap0 taken, the rest threaded onto
# the free list; or, if either store could not grow, an error
def grow.done(ok: Bool, w: KM.M, rs: KM.M, +nr: U32, +errs: U32, +itrs: U32, +wcap0: U32, +wcap: U32, dt: DT) -> H & U32:
  match ok:
    case True{}:
      (H{thread(U32.to_nat((wcap - (wcap0 + 1 : U32) : U32)), w, (wcap0 + 1 : U32), wcap), (wcap0 + 2 : U32), rs, nr, C{errs, itrs, wcap, dt}}, (wcap0 << 2n : U32))
    case False{}:
      (H{w, 0, rs, nr, C{(errs + 1 : U32), itrs, wcap0, dt}}, 0)

def grow.rs(r: KM.M & U32, w: KM.M, +nr: U32, +errs: U32, +itrs: U32, +wcap0: U32, +wcap: U32, dt: DT) -> H & U32:
  (rs, +cr) = r
  grow.done(U32.is_gt(wcap, (wcap0 + 1 : U32)) && U32.is_le(rs_words(wcap), cr), w, rs, nr, errs, itrs, wcap0, wcap, dt)

def grow.w(r: KM.M & U32, rs: KM.M, +nr: U32, +errs: U32, +itrs: U32, +wcap0: U32, dt: DT) -> H & U32:
  (w, +cap) = r
  grow.rs(KM.m_ensure(rs, rs_words((cap >> 2n : U32)), rs_words(wcap0), rs_maxd()), w, nr, errs, itrs, wcap0, (cap >> 2n : U32), dt)

# the free list empty: every node is in use, so the store doubles
def alloc.grow(h: H) -> H & U32:
  match h:
    case H{w, +fh, rs, +nr, c}:
      match c:
        case C{+errs, +itrs, +wcap, dt}:
          grow.w(KM.m_ensure(w, ((wcap * 2 : U32) * 4 : U32), (wcap * 4 : U32), w_maxd()), rs, nr, errs, itrs, wcap, dt)
        case CBox{d}:
          (H{w, fh, rs, nr, CBox{d}}, 0)

def alloc.pop(r: KM.M & U32, +n: U32, rs: KM.M, +nr: U32, c: C) -> H & U32:
  (w, +next) = r
  (H{w, next, rs, nr, c}, n)

# a node: the head of the free list, which an intrusive list holds (the
# head a node's index plus one, 0 for none; each free node's word 1 the
# next in the same form)
def alloc(h: H) -> H & U32:
  match h:
    case H{w, +fh, rs, +nr, c}:
      match fh:
        case 0:
          alloc.grow(H{w, fh, rs, nr, c})
        case _:
          alloc.pop(KM.m_get(w, (((fh - 1 : U32) << 2n : U32) + 1 : U32)), ((fh - 1 : U32) << 2n : U32), rs, nr, c)

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

# free the node behind reference r, whatever its port: its header zeroed,
# its word 1 linking the old head of the free list
def free(h: H, +r: U32) -> H:
  match h:
    case H{w, +fh, rs, +nr, c}:
      H{KM.m_set(KM.m_set(w, base(r), 0), (base(r) + 1 : U32), fh), ((r >> 2n : U32) + 1 : U32), rs, nr, c}

# free a redex's two nodes, b first, so that a's slot heads the free list
# and the rule's first new node takes it: the interface, node 0, keeps its
# slot when a rule replaces it
def fresh2(h: H, +a: U32, +b: U32) -> H:
  free(free(h, b), a)

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

def dt_op.fin(r: DT & U32, w: KM.M, +fh: U32, rs: KM.M, +nr: U32, +errs: U32, +itrs: U32, +wcap: U32) -> H & U32:
  (dt, +i) = r
  (H{w, fh, rs, nr, C{errs, itrs, wcap, dt}}, i)

def dt_val.fin(r: DT & V.Val, w: KM.M, +fh: U32, rs: KM.M, +nr: U32, +errs: U32, +itrs: U32, +wcap: U32) -> H & V.Val:
  (dt, v) = r
  (H{w, fh, rs, nr, C{errs, itrs, wcap, dt}}, v)

def tab_put(h: H, v: V.Val) -> H & U32:
  match h:
    case H{w, +fh, rs, +nr, c}:
      match c:
        case C{+errs, +itrs, +wcap, dt}:
          dt_op.fin(dt_put(dt, v), w, fh, rs, nr, errs, itrs, wcap)
        case CBox{d}:
          (H{w, fh, rs, nr, CBox{d}}, 0)

# entry i duplicated, in one opening of the cold record
def tab_dup(h: H, +i: U32) -> H & U32:
  match h:
    case H{w, +fh, rs, +nr, c}:
      match c:
        case C{+errs, +itrs, +wcap, dt}:
          dt_op.fin(dt_dup(dt, i), w, fh, rs, nr, errs, itrs, wcap)
        case CBox{d}:
          (H{w, fh, rs, nr, CBox{d}}, 0)

def tab_get(h: H, +i: U32) -> H & V.Val:
  match h:
    case H{w, +fh, rs, +nr, c}:
      match c:
        case C{+errs, +itrs, +wcap, dt}:
          dt_val.fin(dt_get(dt, i), w, fh, rs, nr, errs, itrs, wcap)
        case CBox{d}:
          (H{w, fh, rs, nr, CBox{d}}, V.VUnit{})

def tab_take(h: H, +i: U32) -> H & V.Val:
  match h:
    case H{w, +fh, rs, +nr, c}:
      match c:
        case C{+errs, +itrs, +wcap, dt}:
          dt_val.fin(dt_take(dt, i), w, fh, rs, nr, errs, itrs, wcap)
        case CBox{d}:
          (H{w, fh, rs, nr, CBox{d}}, V.VUnit{})

# a value as a node holds it: its form, field and word
type PW is Data:
  PW{+m: U32, +f: U32, +w: U32}

def pw.tab(r: H & U32) -> H & PW:
  (h, +i) = r
  (h, PW{0, 0, i})

def put.one(+need: U32, h: H, +op: U32, +n: U32) -> H & PW:
  match need:
    case 1:
      (h, PW{3, op, n})
    case _:
      pw.tab(tab_put(h, V.VP1{op, need, n}))

def put.two(t: List<&2, V.Val>, h: H, +op: U32, +need: U32, +a: U32, v: V.Val) -> H & PW:
  match t:
    case Con{V.VNum{+b}, u}:
      match u:
        case Nil{}:
          pw.tab(tab_put(h, V.VP2{op, need, a, b}))
        case _:
          pw.tab(tab_put(h, v))
    case _:
      pw.tab(tab_put(h, v))

# a builtin with no number collected in the node, one or two in a flat
# form in the table, more as they are
def put.fun.go(args: List<&2, V.Val>, h: H, +op: U32, +need: U32, v: V.Val) -> H & PW:
  match args:
    case Nil{}:
      (h, PW{2, op, need})
    case Con{V.VNum{+n}, t}:
      match t:
        case Nil{}:
          put.one(need, h, op, n)
        case _:
          put.two(t, h, op, need, n, v)
    case _:
      pw.tab(tab_put(h, v))

# a builtin in the node when its op fits the field, else an entry
def put.fun(fits: Bool, args: List<&2, V.Val>, h: H, +op: U32, +need: U32, v: V.Val) -> H & PW:
  match fits:
    case True{}:
      put.fun.go(args, h, op, need, v)
    case False{}:
      pw.tab(tab_put(h, v))

# a value in the form a node holds it: a number, a bare builtin or one
# needing a last argument after a number in the node, anything else a new
# entry
def put(h: H, v: V.Val) -> H & PW:
  match v:
    case V.VNum{+n}:
      (h, PW{1, 0, n})
    case V.VFun{+op, +need, +args}:
      put.fun(U32.is_lt(op, lvl_cap()), args, h, op, need, V.VFun{op, need, args})
    case _:
      pw.tab(tab_put(h, v))

def chk.fin(r: V.Val & Bool, h: H) -> H & V.Val:
  (v, +bad) = r
  (err_if(bad, h), v)

# a table entry read as a value: a free slot there is a kernel fault,
# counted as an error
def chk(r: H & V.Val) -> H & V.Val:
  (h, v) = r
  chk.fin(V.free_chk(v), h)

# the value a node of form m, field f, word w holds: taking it, an entry
# leaving the table
def take(h: H, +m: U32, +f: U32, +w: U32) -> H & V.Val:
  match m:
    case 1:
      (h, V.VNum{w})
    case 2:
      (h, V.VFun{f, w, Nil{}})
    case 3:
      (h, V.VFun{f, 1, [V.VNum{w}]})
    case _:
      chk(tab_take(h, w))

# the same, the entry kept
def peek(h: H, +m: U32, +f: U32, +w: U32) -> H & V.Val:
  match m:
    case 1:
      (h, V.VNum{w})
    case 2:
      (h, V.VFun{f, w, Nil{}})
    case 3:
      (h, V.VFun{f, 1, [V.VNum{w}]})
    case _:
      chk(tab_get(h, w))

# the word for a copy of a value of form m: an entry duplicated (the Bend
# value shared), any other word as it is
def dup(h: H, +m: U32, +w: U32) -> H & U32:
  match m:
    case 0:
      tab_dup(h, w)
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

# the general path: both values taken, V.apply_fn applying them
def apply.gen(h: H, +ha: U32, +pa: U32, +hb: U32, +pb: U32) -> H & PW:
  apply.a(take(h, form(ha), fld(ha), pa), hb, pb)

# a bare builtin needing `need` meets a number
def apply.bare(+need: U32, h: H, +ha: U32, +pa: U32, +hb: U32, +pb: U32) -> H & PW:
  match need:
    case 1:
      put(h, V.num1(fld(ha), pb))
    case 2:
      (h, PW{3, fld(ha), pb})
    case _:
      apply.gen(h, ha, pa, hb, pb)

def apply.n(+ma: U32, +mb: U32, h: H, +ha: U32, +pa: U32, +hb: U32, +pb: U32) -> H & PW:
  match ma mb:
    case 2 1:
      apply.bare(pa, h, ha, pa, hb, pb)
    case 3 1:
      put(h, V.num2(fld(ha), pa, pb))
    case _ _:
      apply.gen(h, ha, pa, hb, pb)

# A's function (header ha, word pa) applied to B's value, both taken: a
# builtin on a number natively, anything else through V.apply_fn
def apply(h: H, +ha: U32, +pa: U32, +hb: U32, +pb: U32) -> H & PW:
  apply.n(form(ha), form(hb), h, ha, pa, hb, pb)

def is_fn(v: V.Val) -> Bool:
  match v:
    case V.VFun{+op, +need, args}:
      True{}
    case V.VP1{+op, +need, +a}:
      True{}
    case V.VP2{+op, +need, +a, +b}:
      True{}
    case _:
      False{}

def is_fn.fin(r: H & V.Val) -> H & Bool:
  (h, v) = r
  (h, is_fn(v))

# is the value a function? A builtin is; a number is not.
def val_is_fn(h: H, +m: U32, +f: U32, +w: U32) -> H & Bool:
  match m:
    case 1:
      (h, False{})
    case 2:
      (h, True{})
    case 3:
      (h, True{})
    case _:
      is_fn.fin(tab_get(h, w))

# a table entry that is a handle, VLazy: a pair meeting it may need
# another cell's value (HeapModel's "Forcing")
type Lz is Type:
  Lz{h: H, +lazy: Bool, +k: U32}

def lazy.v(v: V.Val, h: H) -> Lz:
  match v:
    case V.VLazy{+k}:
      Lz{h, True{}, k}
    case _:
      Lz{h, False{}, 0}

def lazy.fin(r: H & V.Val) -> Lz:
  (h, v) = r
  lazy.v(v, h)

# is the value of form m and word w a handle, and which?
def val_lazy(h: H, +m: U32, +w: U32) -> Lz:
  match m:
    case 0:
      lazy.fin(tab_get(h, w))
    case _:
      Lz{h, False{}, 0}

# Level checks
# ============

# A fan's, a function's or an application's field is its level, unless its
# value form is unlev: then its net was built without levels, a fan's
# field is its site, and the level checks pass it by.
def unlev() -> U32:
  1

# a copy meeting a function at a level not below its own, both leveled
# (net.bend's level checks)
def copy_fn_bad(+ha: U32, +hb: U32) -> Bool:
  U32.is_eq(form(ha), 0) && U32.is_eq(form(hb), 0) && U32.is_ge(fld(ha), fld(hb))

# Fusing controls
# ===============
#
# net.bend's "Fusing controls" on this layout: a control's field is its
# index, its word 3 its offset. Ports: a Lift's 0 is in, 1 out; a LiftC's
# 0 out, 1 in. Only raises fuse, into a run of unit brackets (V.compose);
# the node freed is the one whose principal faces the other's auxiliary,
# so it is in no active pair.

type FZ is Data:
  FzNo{}
  FzTo{+n: U32, +o: U32}

def fz.ok(ok: Bool, +n1: U32, +b1: U32, +b2: U32) -> FZ:
  match ok:
    case True{}:
      FzTo{n1, ((b1 + b2 : U32) .|. 2147483648 : U32)}
    case False{}:
      FzNo{}

# the one control acting as the first (index n1, offset o1) then the
# second, if any (V.compose): both raise, the second's index where the
# first's raise ends; a raise past the field's range is refused
def compose(+n1: U32, +o1: U32, +n2: U32, +o2: U32) -> FZ:
  fz.ok(off_up(o1) && off_up(o2) && U32.is_eq(n2, (n1 + off_by(o1) : U32)) &&
      U32.is_lt((off_by(o1) + off_by(o2) : U32), lvl_cap()),
    n1, off_by(o1), off_by(o2))

def ctl_set(h: H, +r: U32, +k: U32, +n: U32, +o: U32) -> H:
  wr(wr(h, r, hd(k, n)), (r + 3 : U32), o)

def fl.fuse(f: FZ, h: H, +p: U32, +l: U32, +o: U32) -> H:
  match f:
    case FzNo{}:
      h
    case FzTo{+n, +off}:
      free(link(ctl_set(h, p, 10, n, off), (p + 1 : U32), o), l)

def fl.o(r: H & U32, +p: U32, +l: U32, f: FZ) -> H:
  (h, +o) = r
  fl.fuse(f, h, p, l, o)

def fl.ol(r: H & U32, +p: U32, +l: U32, +hp: U32, +op: U32, +hl: U32) -> H:
  (h, +ol) = r
  fl.o(rd(h, (l + 2 : U32)), p, l, compose(fld(hp), op, fld(hl), ol))

def fl.hl(r: H & U32, +p: U32, +l: U32, +hp: U32, +op: U32) -> H:
  (h, +hl) = r
  fl.ol(rd(h, (l + 3 : U32)), p, l, hp, op, hl)

def fl.op(r: H & U32, +p: U32, +l: U32, +hp: U32) -> H:
  (h, +op) = r
  fl.hl(rd(h, l), p, l, hp, op)

def fl.hp(r: H & U32, +p: U32, +l: U32) -> H:
  (h, +hp) = r
  fl.op(rd(h, (p + 3 : U32)), p, l, hp)

# Lifts p and l, p's out feeding l's in (values cross p first): p stays
def fuse_lifts(h: H, +p: U32, +l: U32) -> H:
  fl.hp(rd(h, p), p, l)

def fc.fuse(f: FZ, h: H, +a: U32, +b: U32, +i: U32) -> H:
  match f:
    case FzNo{}:
      h
    case FzTo{+n, +off}:
      free(link(ctl_set(h, b, 11, n, off), i, (b + 1 : U32)), a)

def fc.i(r: H & U32, +a: U32, +b: U32, f: FZ) -> H:
  (h, +i) = r
  fc.fuse(f, h, a, b, i)

def fc.ob(r: H & U32, +a: U32, +b: U32, +ha: U32, +oa: U32, +hb: U32) -> H:
  (h, +ob) = r
  fc.i(rd(h, (a + 2 : U32)), a, b, compose(fld(hb), ob, fld(ha), oa))

def fc.hb(r: H & U32, +a: U32, +b: U32, +ha: U32, +oa: U32) -> H:
  (h, +hb) = r
  fc.ob(rd(h, (b + 3 : U32)), a, b, ha, oa, hb)

def fc.oa(r: H & U32, +a: U32, +b: U32, +ha: U32) -> H:
  (h, +oa) = r
  fc.hb(rd(h, b), a, b, ha, oa)

def fc.ha(r: H & U32, +a: U32, +b: U32) -> H:
  (h, +ha) = r
  fc.oa(rd(h, (a + 3 : U32)), a, b, ha)

# LiftCs a and b, a's out feeding b's in (consumers cross b first): b
# stays
def fuse_liftcs(h: H, +a: U32, +b: U32) -> H:
  fc.ha(rd(h, a), a, b)

# two controls of kind k meeting at ports px and py of nodes x and y:
# fused when principal meets auxiliary in the order they fuse
def fa.go(+k: U32, +px: U32, +py: U32, h: H, +x: U32, +y: U32) -> H:
  match k px py:
    case 10 1 0:
      fuse_lifts(h, x, y)
    case 10 0 1:
      fuse_lifts(h, y, x)
    case 11 0 1:
      fuse_liftcs(h, x, y)
    case 11 1 0:
      fuse_liftcs(h, y, x)
    case _ _ _:
      h

def fa.k(ok: Bool, +k: U32, h: H, +x: U32, +y: U32) -> H:
  match ok:
    case True{}:
      fa.go(k, port(x), port(y), h, base(x), base(y))
    case False{}:
      h

def fa.hy(r: H & U32, +k: U32, +x: U32, +y: U32) -> H:
  (h, +hy) = r
  fa.k(U32.is_eq(rk(hy), k) && U32.is_ne(base(x), base(y)), k, h, x, y)

def fa.y.go(none: Bool, h: H, +k: U32, +x: U32, +y: U32) -> H:
  match none:
    case True{}:
      h
    case False{}:
      fa.hy(rd(h, base(y)), k, x, y)

def fa.y(r: H & U32, +k: U32, +x: U32) -> H:
  (h, +y) = r
  fa.y.go(U32.is_eq(y, nil()), h, k, x, y)

def fa.ctl(ctl: Bool, h: H, +k: U32, +x: U32) -> H:
  match ctl:
    case True{}:
      fa.y(rd(h, (x + 1 : U32)), k, x)
    case False{}:
      h

def fa.hx(r: H & U32, +x: U32) -> H:
  (h, +hx) = r
  fa.ctl(U32.is_eq(rk(hx), 10) || U32.is_eq(rk(hx), 11), h, rk(hx), x)

def fa.go0(none: Bool, h: H, +x: U32) -> H:
  match none:
    case True{}:
      h
    case False{}:
      fa.hx(rd(h, base(x)), x)

# the link at port x: when it joins two controls of one kind, principal to
# auxiliary in the order they fuse, and compose finds one control acting
# as both, fuse them. A rewrite tries each link it made that may join two
# controls (net.bend's fuse_ends). The link a fusion makes is not tried
# again: on 600 random terms that found one more fusion, saving two
# interactions, at more cost than it saved.
def fuse(h: H, +x: U32) -> H:
  fa.go0(U32.is_eq(x, nil()), h, x)


# Peeling
# =======
#
# net.bend's "Peeling" on this layout: a Lift l and a LiftC c facing at
# one index as different controls; the run raising further keeps as many
# units facing as the other raises, or one facing a drop, and a new
# control of its kind takes the rest behind it (a Lift's port 1, out; a
# LiftC's port 1, in), from the index where the kept units end.

def sel_u(c: Bool, +x: U32, +y: U32) -> U32:
  match c:
    case True{}:
      x
    case False{}:
      y

# how much of a run (ua, ba) to keep facing (ub, bb), 0 to peel none
def peel.amt(+ua: Bool, +ba: U32, +ub: Bool, +bb: U32) -> U32:
  match ua ub:
    case True{} True{}:
      sel_u(U32.is_lt(bb, ba), bb, 0)
    case True{} False{}:
      sel_u(U32.is_lt(1, ba), 1, 0)
    case _ _:
      0

# what peeling one control leaves: the state, its offset word, the peer
# of its port 1
type Pe is Type:
  Pe{h: H, +o: U32, +e: U32}

def pe.at(r: H & U32, +x: U32, +e: U32, +o: U32) -> Pe:
  (h, +rest) = r
  Pe{link(link(h, (x + 1 : U32), rest), (rest + 1 : U32), e), o, rest}

# control x, of kind k2 at index n with offset o and port 1's peer e,
# keeps k units of its run; a new control of its kind takes the rest
# behind it, between its port 1 and e
def pe.do(+k: U32, h: H, +x: U32, +k2: U32, +n: U32, +o: U32, +e: U32) -> Pe:
  match k:
    case 0:
      Pe{h, o, e}
    case _:
      pe.at(node(err_if(U32.is_ge((n + k : U32), lvl_cap()), wr(h, (x + 3 : U32), (k .|. 2147483648 : U32))),
          hd(k2, (n + k : U32)), ((off_by(o) - k : U32) .|. 2147483648 : U32)), x, e, (k .|. 2147483648 : U32))

# the rule's payload test (ctl_eq) on what peeling leaves, the offsets,
# and the peers of the two ports 1
type Pl is Type:
  Pl{h: H, +t: Bool, +pa: U32, +pb: U32, +e0: U32, +e2: U32}

def pl.fin(r: Pe, +pa: U32, +e0: U32) -> Pl:
  match r:
    case Pe{h, +pb, +e2}:
      Pl{h, U32.is_eq(pa, pb), pa, pb, e0, e2}

def pl.c(r: Pe, +b: U32, +n: U32, +kc: U32, +pb: U32, +e2: U32) -> Pl:
  match r:
    case Pe{h, +pa, +e0}:
      pl.fin(pe.do(kc, h, b, 11, n, pb, e2), pa, e0)

def peel_ctl.go(same: Bool, h: H, +a: U32, +b: U32, +n: U32, +pa: U32, +pb: U32, +e0: U32, +e2: U32) -> Pl:
  match same:
    case True{}:
      pl.c(pe.do(peel.amt(off_up(pa), off_by(pa), off_up(pb), off_by(pb)), h, a, 10, n, pa, e0), b, n,
        peel.amt(off_up(pb), off_by(pb), off_up(pa), off_by(pa)), pb, e2)
    case False{}:
      Pl{h, False{}, pa, pb, e0, e2}

# Lift a (header ha, offset pa, port 1's peer e0) facing LiftC b (hb, pb,
# e2): peeled where they meet at one index as different runs. The
# generated rewrite for this pair alone calls it (gen_krules.bend), so no
# other pair pays for the test.
def peel_ctl(h: H, +a: U32, +b: U32, +ha: U32, +hb: U32, +pa: U32, +pb: U32, +e0: U32, +e2: U32) -> Pl:
  peel_ctl.go(U32.is_eq(fld(ha), fld(hb)), h, a, b, fld(ha), pa, pb, e0, e2)


# Active pairs
# ============

# the newest active pair, if any
type Pop is Type:
  Pop{h: H, +x: U32, +y: U32, +ok: Bool}

def pop.y(r: KM.M & U32, rs: KM.M, +fh: U32, +nr: U32, c: C, +x: U32) -> Pop:
  (w, +y) = r
  Pop{H{w, fh, rs, nr, c}, x, y, True{}}

# x's partner: the peer of its principal port
def pop.x(r: KM.M & U32, w: KM.M, +fh: U32, +nr: U32, c: C) -> Pop:
  (rs, +x) = r
  pop.y(KM.m_get(w, (x + 1 : U32)), rs, fh, nr, c, x)

def pop(h: H) -> Pop:
  match h:
    case H{w, +fh, rs, +nr, c}:
      match nr:
        case 0:
          Pop{H{w, fh, rs, nr, c}, 0, 0, False{}}
        case _:
          pop.x(KM.m_get(rs, (nr - 1 : U32)), w, fh, (nr - 1 : U32), c)

# a pair popped when fuel ran out goes back
def unpop(pp: Pop) -> H:
  match pp:
    case Pop{h, +x, +y, +ok}:
      match ok:
        case True{}:
          push(h, x, y)
        case False{}:
          h

# a node of rule kind k holding the value pw
def node_pw(h: H, +k: U32, pw: PW) -> H & U32:
  match pw:
    case PW{+m, +f, +w}:
      node(h, hd2(k, m, f), w)

type FW is Type:
  FW{a: Array<V.Val>, +fh: U32, +c: U32}

def fw.step(r: Array<V.Val> & V.Val, +c: U32) -> FW:
  (a, v) = r
  FW{a, dt_link(v), (c + 1 : U32)}

# entries on the free list, following at most k links: c counts them
def dt_free(k: Nat, w: FW) -> FW:
  match k:
    case 0n:
      w
    case 1n+p:
      match w:
        case FW{a, +fh, +c}:
          match fh:
            case 0:
              FW{a, fh, c}
            case _:
              dt_free(p, fw.step(Array.get(V.Val, a, (fh - 1 : U32)), c))

def is_free(v: V.Val) -> U32:
  match v:
    case V.VFree{+k}:
      1
    case _:
      0

def fs.step(r: Array<V.Val> & V.Val, +c: U32) -> FW:
  (a, v) = r
  FW{a, 0, (c + is_free(v) : U32)}

# entries from i that are VFree, k of them scanned: c counts them
def dt_scan(k: Nat, +i: U32, w: FW) -> U32:
  match k:
    case 0n:
      match w:
        case FW{a, +fh, +c}:
          c
    case 1n+p:
      match w:
        case FW{a, +fh, +c}:
          dt_scan(p, (i + 1 : U32), fs.step(Array.get(V.Val, a, i), c))

def dt_live.fin(w: FW, +n: U32) -> U32:
  match w:
    case FW{a, +fh, +c}:
      (n - c : U32)

# entries in use: the high-water mark less those on the free list
def dt_live(t: DT) -> U32:
  match t:
    case DT{a, +fh, +n, +cap, +d}:
      dt_live.fin(dt_free(U32.to_nat(n), FW{a, fh, 0}), n)

def dt_ok.fin(w: FW, +n: U32, +held: U32) -> Bool:
  match w:
    case FW{a, +fh, +c}:
      U32.is_eq((n - c : U32), held) && U32.is_eq(dt_scan(U32.to_nat(n), 0, FW{a, 0, 0}), c)

# the audit: the entries in use are the held ones, and the free list holds
# every VFree entry, so no entry leaked off it and none is free twice
def dt_ok(t: DT, +held: U32) -> Bool:
  match t:
    case DT{a, +fh, +n, +cap, +d}:
      dt_ok.fin(dt_free(U32.to_nat(n), FW{a, fh, 0}), n, held)

def c_live(c: C) -> U32:
  match c:
    case C{+errs, +itrs, +wcap, dt}:
      dt_live(dt)
    case CBox{d}:
      0

def c_ok(c: C, +held: U32) -> Bool:
  match c:
    case C{+errs, +itrs, +wcap, dt}:
      dt_ok(dt, held)
    case CBox{d}:
      False{}

# data entries in use
def h_live(h: H) -> U32:
  match h:
    case H{w, +fh, rs, +nr, c}:
      c_live(c)

# the table's audit (dt_ok) against held entries
def h_ok(h: H, +held: U32) -> Bool:
  match h:
    case H{w, +fh, rs, +nr, c}:
      c_ok(c, held)
