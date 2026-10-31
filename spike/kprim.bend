import Base
import ./val.bend as V
import ./kmem_grow.bend as KM

# The kernel's primitives (spike-node-layout in
# docs/plans/EvalSpike_2026-10-26.md, `net-nodes-double`): a net as four-
# word nodes in storage that doubles, its free list and active pairs, and a
# data table of its own, kept linear.
#
# A node n is words 4n .. 4n + 3. Word 0, the header (header-kind-byte):
# the rule kind, as net.bend's kcode, in the low 8 bits, the value form in
# the next 2, and a 22-bit field: a function's or an application's level,
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

# Capacity: 2^21 nodes, 2^21 active pairs, 2^20 data entries, 2^22 levels;
# passing any is an error.
def lvl_cap() -> U32:
  4194304

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
# k 18 on `k 2 succ 0`, about 30 instructions an interaction a word. So
# the net is two arrays alone, its words and its data table's values; its
# own words (the free list's head, the counts, the table's bookkeeping)
# sit in a header at the start of the words, read and written where they
# are used (heap-strategies.header: 0.3% to 6.3% fewer instructions on
# every workload, the data table no longer behind a record that
# allocated when opened).

# the net: its words, nodes after a header of seven, and the data table's
# values. Every node not in use is on the free list: growing the store
# threads the new nodes onto it, so making a node is a pop. Which pairs
# are active the net does not record; a strategy that wants them keeps
# them (Stk, below).
type H is Type:
  H{w: KM.M, a: Array<V.Val>}

# The header, nodes 0 to 6, which the free list never holds: the free
# list's head (a node's index plus one, 0 for none), errors, interactions
# (counted by the run's fuel, set when it ends), how many nodes fit; the
# data table's free head, its high-water mark, its capacity and the depth
# of its array (DT); four words spare; then the events, by the kind of
# the node each acts on (heap-strategies.erasure.kernel), a word a kind
def at_fh() -> U32:
  0

def at_errs() -> U32:
  1

def at_itrs() -> U32:
  2

def at_wcap() -> U32:
  3

def at_tfh() -> U32:
  4

def at_tn() -> U32:
  5

def at_tcap() -> U32:
  6

def at_td() -> U32:
  7

# events at a node of kind code k, below 16: no kind past them makes one
# (law events_fit_header)
def at_evk(+k: U32) -> U32:
  (12 + k : U32)

# the first node after the header, the interface, and its reference
def first() -> U32:
  7

def iface() -> U32:
  28

# A net starts at 128 nodes, 2 KB (net-nodes-double); node words up to
# 2^23 (2^21 nodes); a strategy's stack of pairs up to 2^22 words
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

# the header of a new net of wcap nodes, the interface first on the free
# list, the data table as dt_new makes it
def hdr_new(w: KM.M, +wcap: U32) -> KM.M:
  KM.m_set(KM.m_set(KM.m_set(KM.m_set(w, at_fh(), (first() + 1 : U32)), at_wcap(), wcap), at_tcap(), 16), at_td(), 4)

def h_new.w(r: KM.M & U32) -> H:
  (w, +cw) = r
  H{hdr_new(thread(U32.to_nat(((cw >> 2n : U32) - first() : U32)), w, first(), (cw >> 2n : U32)), (cw >> 2n : U32)),
    Array.new(V.Val, 4n, V.VUnit{})}

def h_new() -> H:
  h_new.w(KM.m_new(9n, w_maxd()))

def h_err.n(r: KM.M & U32, a: Array<V.Val>) -> H:
  (w, +e) = r
  H{KM.m_set(w, at_errs(), (e + 1 : U32)), a}

def h_err(h: H) -> H:
  match h:
    case H{w, a}:
      h_err.n(KM.m_get(w, at_errs()), a)

def err_if(bad: Bool, h: H) -> H:
  match bad:
    case True{}:
      h_err(h)
    case False{}:
      h

# interactions, errors, how many nodes fit, for reports
type HS is Data:
  HS{+itrs: U32, +errs: U32, +wcap: U32}

def stats.c(r: KM.M & U32, a: Array<V.Val>, +itrs: U32, +errs: U32) -> H & HS:
  (w, +wcap) = r
  (H{w, a}, HS{itrs, errs, wcap})

def stats.e(r: KM.M & U32, a: Array<V.Val>, +itrs: U32) -> H & HS:
  (w, +errs) = r
  stats.c(KM.m_get(w, at_wcap()), a, itrs, errs)

def stats.i(r: KM.M & U32, a: Array<V.Val>) -> H & HS:
  (w, +itrs) = r
  stats.e(KM.m_get(w, at_errs()), a, itrs)

# interactions, errors and node capacity, the state kept
def stats(h: H) -> H & HS:
  match h:
    case H{w, a}:
      stats.i(KM.m_get(w, at_itrs()), a)

# the interactions a run made, recorded when it ends
def count(h: H, +n: U32) -> H:
  match h:
    case H{w, a}:
      H{KM.m_set(w, at_itrs(), n), a}

# Words
# =====

def ev_count.n(r: KM.M & U32, a: Array<V.Val>, +k: U32) -> H:
  (w, +n) = r
  H{KM.m_set(w, at_evk(k), (n + 1 : U32)), a}

# one more event, at a node of kind code k (heap-strategies.erasure.kernel)
def ev_count(h: H, +k: U32) -> H:
  match h:
    case H{w, a}:
      ev_count.n(KM.m_get(w, at_evk(k)), a, k)

def rd.fin(r: KM.M & U32, a: Array<V.Val>) -> H & U32:
  (w, +v) = r
  (H{w, a}, v)

def rd(h: H, +i: U32) -> H & U32:
  match h:
    case H{w, a}:
      rd.fin(KM.m_get(w, i), a)

def wr(h: H, +i: U32, +v: U32) -> H:
  match h:
    case H{w, a}:
      H{KM.m_set(w, i, v), a}

# the events at nodes of kind code k
def evk(h: H, +k: U32) -> H & U32:
  rd(h, at_evk(k))

def evs.add(r: H & U32, +n: U32) -> H & U32:
  (h, +m) = r
  (h, (n + m : U32))

def evs.r(r: H & U32, +i: U32) -> H & U32:
  (h, +n) = r
  evs.add(evk(h, i), n)

def evs.go(k: Nat, r: H & U32, +i: U32) -> H & U32:
  match k:
    case 0n:
      r
    case 1n+p:
      evs.go(p, evs.r(r, i), (i + 1 : U32))

# the events counted, of every kind
def evs(h: H) -> H & U32:
  evs.go(16n, (h, 0), 0)

def port(+r: U32) -> U32:
  (r .&. 3 : U32)

# link two ports (word n * 4 + 1 + p is port p's link: the reference plus
# one); an active pair when both are principal, which the net does not
# record: a strategy that wants its pairs notes them (note, below)
def link(h: H, +x: U32, +y: U32) -> H:
  wr(wr(h, (x + 1 : U32), y), (y + 1 : U32), x)

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

# the store doubled to wcap nodes: node wcap0 taken, the rest threaded
# onto the free list; or, if it could not grow, an error, and the
# interface's reference as the node, so that nothing writes the header
def grow.done(ok: Bool, w: KM.M, a: Array<V.Val>, +wcap0: U32, +wcap: U32) -> H & U32:
  match ok:
    case True{}:
      (H{KM.m_set(KM.m_set(thread(U32.to_nat((wcap - (wcap0 + 1 : U32) : U32)), w, (wcap0 + 1 : U32), wcap),
        at_fh(), (wcap0 + 2 : U32)), at_wcap(), wcap), a}, (wcap0 << 2n : U32))
    case False{}:
      (h_err(H{w, a}), iface())

def grow.w(r: KM.M & U32, a: Array<V.Val>, +wcap0: U32) -> H & U32:
  (w, +cap) = r
  grow.done(U32.is_gt((cap >> 2n : U32), (wcap0 + 1 : U32)), w, a, wcap0, (cap >> 2n : U32))

def grow.c(r: KM.M & U32, a: Array<V.Val>) -> H & U32:
  (w, +wcap) = r
  grow.w(KM.m_ensure(w, ((wcap * 2 : U32) * 4 : U32), (wcap * 4 : U32), w_maxd()), a, wcap)

# the free list empty: every node is in use, so the store doubles
def alloc.grow(h: H) -> H & U32:
  match h:
    case H{w, a}:
      grow.c(KM.m_get(w, at_wcap()), a)

def alloc.pop(r: KM.M & U32, +n: U32, a: Array<V.Val>) -> H & U32:
  (w, +next) = r
  (H{KM.m_set(w, at_fh(), next), a}, n)

def alloc.k(+fh: U32, w: KM.M, a: Array<V.Val>) -> H & U32:
  match fh:
    case 0:
      alloc.grow(H{w, a})
    case _:
      alloc.pop(KM.m_get(w, (((fh - 1 : U32) << 2n : U32) + 1 : U32)), ((fh - 1 : U32) << 2n : U32), a)

def alloc.fh(r: KM.M & U32, a: Array<V.Val>) -> H & U32:
  (w, +fh) = r
  alloc.k(fh, w, a)

# a node: the head of the free list, which an intrusive list holds (the
# head a node's index plus one, 0 for none; each free node's word 1 the
# next in the same form)
def alloc(h: H) -> H & U32:
  match h:
    case H{w, a}:
      alloc.fh(KM.m_get(w, at_fh()), a)

def node.word.k(+k: U32) -> U32:
  match k:
    case 5:
      2
    case _:
      3

def node.word(+hd: U32) -> U32:
  node.word.k((hd .&. 255 : U32))

def node.fin(r: H & U32, +hd: U32, +p: U32) -> H & U32:
  (h, +n) = r
  (wr(wr(h, n, hd), (n + node.word(hd) : U32), p), n)

# a node with header hd and payload word p, word 2 of a data node, word 3
# of others (overwritten by port 2's link in a node with three ports): its
# reference, port 0
def node(h: H, +hd: U32, +p: U32) -> H & U32:
  node.fin(alloc(h), hd, p)

# node r's slot taken in place for a node with header hd and payload word
# p, as node makes one: a rewrite's redex gives its slots to its first two
# new nodes (heap-strategies.reuse)
def renode(h: H, +r: U32, +hd: U32, +p: U32) -> H & U32:
  node.fin((h, r), hd, p)

def base(+r: U32) -> U32:
  (r .&. 4294967292 : U32)

def free.fh(q: KM.M & U32, a: Array<V.Val>, +r: U32) -> H:
  (w, +fh) = q
  H{KM.m_set(KM.m_set(KM.m_set(w, base(r), 0), (base(r) + 1 : U32), fh), at_fh(), ((r >> 2n : U32) + 1 : U32)), a}

# free the node behind reference r, whatever its port: its header zeroed,
# its word 1 linking the old head of the free list
def free(h: H, +r: U32) -> H:
  match h:
    case H{w, a}:
      free.fh(KM.m_get(w, at_fh()), a, r)

# free a redex's two nodes, b first, so that a's slot heads the free list
# and the rule's first new node takes it: the interface, node 3, keeps its
# slot when a rule replaces it
def fresh2(h: H, +a: U32, +b: U32) -> H:
  free(free(h, b), a)

# Headers, levels, values
# =======================

def hd(+k: U32, +f: U32) -> U32:
  (k .|. (f << 10n : U32) : U32)

# a header from rule kind k, value form m and field f
def hd2(+k: U32, +m: U32, +f: U32) -> U32:
  ((k .|. (m << 8n : U32) : U32) .|. (f << 10n : U32) : U32)

# the kind and the form
def kind(+h: U32) -> U32:
  (h .&. 1023 : U32)

def rk(+h: U32) -> U32:
  (h .&. 255 : U32)

def form(+h: U32) -> U32:
  ((h >> 8n : U32) .&. 3 : U32)

# the field, offsets' up flag and amount decode by division, remainder
# and comparison, which have laws relating U32 to Nat (LAWS.bend's
# fld_bits, off_by_bits), where shifts and masks have none, and cost the
# same instructions (docs/BendIssues.md, "Reasoning about U32 in
# proofs")
def fld(+h: U32) -> U32:
  (h / 1024 : U32)

# fans pair, and an application meets its function, when level and
# marker agree (a net without levels: equal sites)
def same_lvl(+ha: U32, +hb: U32) -> Bool:
  U32.is_eq((ha >> 8n : U32), (hb >> 8n : U32))

def off_up(+o: U32) -> Bool:
  U32.is_ge(o, 2147483648)

def off_by(+o: U32) -> U32:
  (o % 2147483648 : U32)

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

# raising j through the control would pass the field's 22 bits
def lift_wraps(+n: U32, +o: U32, +j: U32) -> Bool:
  off_up(o) && U32.is_gt(j, n) && U32.is_ge((j + off_by(o) : U32), lvl_cap())

def dt.d(r: KM.M & U32, a: Array<V.Val>, +fh: U32, +n: U32, +cap: U32) -> KM.M & DT:
  (w, +d) = r
  (w, DT{a, fh, n, cap, U32.to_nat(d)})

def dt.cap(r: KM.M & U32, a: Array<V.Val>, +fh: U32, +n: U32) -> KM.M & DT:
  (w, +cap) = r
  dt.d(KM.m_get(w, at_td()), a, fh, n, cap)

def dt.n(r: KM.M & U32, a: Array<V.Val>, +fh: U32) -> KM.M & DT:
  (w, +n) = r
  dt.cap(KM.m_get(w, at_tcap()), a, fh, n)

def dt.fh(r: KM.M & U32, a: Array<V.Val>) -> KM.M & DT:
  (w, +fh) = r
  dt.n(KM.m_get(w, at_tn()), a, fh)

# the data table as its functions take it, from the header and the values
def dt_of(w: KM.M, a: Array<V.Val>) -> KM.M & DT:
  dt.fh(KM.m_get(w, at_tfh()), a)

# the table's bookkeeping back into the header
def dt_back(w: KM.M, t: DT) -> H:
  match t:
    case DT{a, +fh, +n, +cap, +d}:
      H{KM.m_set(KM.m_set(KM.m_set(KM.m_set(w, at_tfh(), fh), at_tn(), n), at_tcap(), cap), at_td(), U32.from_nat(d)), a}

def dt_op.fin(r: DT & U32, w: KM.M) -> H & U32:
  (t, +i) = r
  (dt_back(w, t), i)

def tab_put.t(r: KM.M & DT, v: V.Val) -> H & U32:
  (w, t) = r
  dt_op.fin(dt_put(t, v), w)

def tab_put(h: H, v: V.Val) -> H & U32:
  match h:
    case H{w, a}:
      tab_put.t(dt_of(w, a), v)

def tab_dup.t(r: KM.M & DT, +i: U32) -> H & U32:
  (w, t) = r
  dt_op.fin(dt_dup(t, i), w)

# entry i duplicated
def tab_dup(h: H, +i: U32) -> H & U32:
  match h:
    case H{w, a}:
      tab_dup.t(dt_of(w, a), i)

def tab_get.fin(r: Array<V.Val> & V.Val, w: KM.M) -> H & V.Val:
  (a, v) = r
  (H{w, a}, v)

# entry i's value, the entry kept: the values alone
def tab_get(h: H, +i: U32) -> H & V.Val:
  match h:
    case H{w, a}:
      tab_get.fin(Array.get(V.Val, a, i), w)

def tab_take.fin(r: Array<V.Val> & V.Val, w: KM.M, +i: U32) -> H & V.Val:
  (a, v) = r
  (H{KM.m_set(w, at_tfh(), (i + 1 : U32)), a}, v)

def tab_take.fh(r: KM.M & U32, a: Array<V.Val>, +i: U32) -> H & V.Val:
  (w, +fh) = r
  tab_take.fin(Array.swap(V.Val, a, i, V.VFree{fh}), w, i)

# entry i's value, the entry freed: the values and the table's free head
def tab_take(h: H, +i: U32) -> H & V.Val:
  match h:
    case H{w, a}:
      tab_take.fh(KM.m_get(w, at_tfh()), a, i)

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


# A strategy's stack
# ==================
#
# The net records none of its active pairs (heap-strategies.stack). A
# strategy taking them last in first out keeps a stack of its own: one
# node of each pair, the other the peer of its principal port. It fills
# the stack by walking the net when it starts (kstrat.bend), then from
# the links its rewrites make between two principal ports, which the
# eager variant of the rewrites notes (gen_krules.bend), in the order
# they make them. A pair holds two nodes and a node is in one at most, so
# the stack never holds more pairs than half the nodes. Noting checks
# nothing: before each pop the stack is grown, if need be, to keep room
# for the most pairs one rewrite makes (krules.bend's most_pairs, which
# the generator counts over the rule table: four, a commutation's new
# nodes each facing an external peer). The interpreter notes no more than
# the generated rewrite would: it links the same ends, or joins two of
# the rule's links into one where an external peer is the redex's own.

# The stack is one array: its count at word 0, the word its far end
# starts at (its room, for the stack alone) at word 1, its capacity at
# word 2, its pairs from word 3. No word of it in the state but the array,
# as the net keeps its own words (heap-strategies.header.stack). A
# two-stack strategy keeps the pairs it defers at the far end, from the
# array's top down to word 1's mark (heap-strategies.twostack).
type Stk is Type:
  Stk{s: KM.M}

# the net and a strategy's stack, as the eager rewrites take and return them
type E is Type:
  E{h: H, st: Stk}

def stk.fin(r: KM.M & U32) -> Stk:
  (s, +cap) = r
  Stk{KM.m_set(KM.m_set(s, 1, cap), 2, cap)}

def stk.ensure(r: KM.M & U32, +words: U32) -> Stk:
  (s, +cap) = r
  stk.fin(KM.m_ensure(s, (words + 3 : U32), cap, rs_maxd()))

# an empty stack with room for `words` pairs at least
def stk_new(+words: U32) -> Stk:
  stk.ensure(KM.m_new(6n, rs_maxd()), words)

def note.n(r: KM.M & U32, +x: U32) -> Stk:
  (s, +n) = r
  Stk{KM.m_set(KM.m_set(s, (n + 3 : U32), x), 0, (n + 1 : U32))}

def note.go(both: Bool, st: Stk, +x: U32) -> Stk:
  match both:
    case True{}:
      match st:
        case Stk{s}:
          note.n(KM.m_get(s, 0), x)
    case False{}:
      st

# x onto the stack, a pair already known active
def push(st: Stk, +x: U32) -> Stk:
  note.go(True{}, st, x)

# a link x - y a rewrite made: if both ports are principal, the pair
# goes on the stack as x
def note(st: Stk, +x: U32, +y: U32) -> Stk:
  note.go(U32.is_eq(port(x), 0) && U32.is_eq(port(y), 0), st, x)

# the newest pair on the stack, if any
type Pop is Type:
  Pop{h: H, st: Stk, +x: U32, +y: U32, +ok: Bool}

def pop.y(r: KM.M & U32, s: KM.M, a: Array<V.Val>, +x: U32) -> Pop:
  (w, +y) = r
  Pop{H{w, a}, Stk{s}, x, y, True{}}

# x's partner: the peer of its principal port
def pop.x(r: KM.M & U32, w: KM.M, a: Array<V.Val>) -> Pop:
  (s, +x) = r
  pop.y(KM.m_get(w, (x + 1 : U32)), s, a, x)

def pop.k(+n: U32, h: H, s: KM.M) -> Pop:
  match n:
    case 0:
      Pop{h, Stk{s}, 0, 0, False{}}
    case _:
      match h:
        case H{w, a}:
          pop.x(KM.m_get(KM.m_set(s, 0, (n - 1 : U32)), (n + 2 : U32)), w, a)

def pop.room(r: KM.M & U32, h: H, +n: U32) -> Pop:
  (s, +cap) = r
  pop.k(n, h, KM.m_set(KM.m_set(s, 1, cap), 2, cap))

def pop.grow(full: Bool, h: H, s: KM.M, +n: U32, +cap: U32) -> Pop:
  match full:
    case True{}:
      pop.room(KM.m_ensure(s, (cap * 2 : U32), cap, rs_maxd()), h, n)
    case False{}:
      pop.k(n, h, s)

def pop.cap(r: KM.M & U32, h: H, +n: U32, +most: U32) -> Pop:
  (s, +cap) = r
  pop.grow(U32.is_lt(cap, ((n + most : U32) + 3 : U32)), h, s, n, cap)

def pop.n(r: KM.M & U32, h: H, +most: U32) -> Pop:
  (s, +n) = r
  pop.cap(KM.m_get(s, 1), h, n, most)

# the newest pair on the stack of e, grown first unless it has room for
# most more pairs, the most a rewrite makes
def pop(e: E, +most: U32) -> Pop:
  match e:
    case E{h, st}:
      match st:
        case Stk{s}:
          pop.n(KM.m_get(s, 0), h, most)

# The far end (heap-strategies.twostack): the pairs a two-stack strategy
# defers, from the array's top down to the mark at word 1, the near end's
# limit. A pop reads the near end's count and the mark, and the capacity
# only when the near end is empty; both ends fit before each pop with
# room for the most pairs a rewrite makes and one pair moved, and
# doubling the array moves the far end to the new top.

def far.m(r: KM.M & U32, +x: U32) -> Stk:
  (s, +m) = r
  Stk{KM.m_set(KM.m_set(s, (m - 1 : U32), x), 1, (m - 1 : U32))}

# x deferred: onto the far end
def far_push(st: Stk, +x: U32) -> Stk:
  match st:
    case Stk{s}:
      far.m(KM.m_get(s, 1), x)

# the next pair, the end it came from (0 none, 1 near, 2 far), and the
# interactions made so far
type Pop2 is Type:
  Pop2{h: H, st: Stk, +x: U32, +y: U32, +src: U32, +k: U32}

def p2.y(r: KM.M & U32, s: KM.M, a: Array<V.Val>, +x: U32, +src: U32, +k: U32) -> Pop2:
  (w, +y) = r
  Pop2{H{w, a}, Stk{s}, x, y, src, k}

def p2.x(r: KM.M & U32, w: KM.M, a: Array<V.Val>, +src: U32, +k: U32) -> Pop2:
  (s, +x) = r
  p2.y(KM.m_get(w, (x + 1 : U32)), s, a, x, src, k)

def p2.far(more: Bool, h: H, s: KM.M, +m: U32, +k: U32) -> Pop2:
  match more:
    case False{}:
      Pop2{h, Stk{s}, 0, 0, 0, k}
    case True{}:
      match h:
        case H{w, a}:
          p2.x(KM.m_get(KM.m_set(s, 1, (m + 1 : U32)), m), w, a, 2, k)

def p2.cap(r: KM.M & U32, h: H, +m: U32, +k: U32) -> Pop2:
  (s, +cap) = r
  p2.far(U32.is_lt(m, cap), h, s, m, k)

def p2.pick(+n: U32, h: H, s: KM.M, +m: U32, +k: U32) -> Pop2:
  match n:
    case 0:
      p2.cap(KM.m_get(s, 2), h, m, k)
    case _:
      match h:
        case H{w, a}:
          p2.x(KM.m_get(KM.m_set(s, 0, (n - 1 : U32)), (n + 2 : U32)), w, a, 1, k)

def rl.step(r: KM.M & U32, +to: U32) -> KM.M:
  (s, +v) = r
  KM.m_set(s, to, v)

# j words from word `from` down copied to word `to` down
def relocate(j: Nat, s: KM.M, +from: U32, +to: U32) -> KM.M:
  match j:
    case 0n:
      s
    case 1n+p:
      relocate(p, rl.step(KM.m_get(s, from), to), (from - 1 : U32), (to - 1 : U32))

def p2.grown(r: KM.M & U32, h: H, +n: U32, +m: U32, +cap0: U32, +k: U32) -> Pop2:
  (s, +cap) = r
  p2.pick(n, h, KM.m_set(KM.m_set(relocate(U32.to_nat((cap0 - m : U32)), s, (cap0 - 1 : U32), (cap - 1 : U32)),
    1, ((m + cap : U32) - cap0 : U32)), 2, cap), ((m + cap : U32) - cap0 : U32), k)

def p2.c0(r: KM.M & U32, h: H, +n: U32, +m: U32, +k: U32) -> Pop2:
  (s, +cap) = r
  p2.grown(KM.m_ensure(s, (cap * 2 : U32), cap, rs_maxd()), h, n, m, cap, k)

def p2.grow(full: Bool, h: H, s: KM.M, +n: U32, +m: U32, +k: U32) -> Pop2:
  match full:
    case True{}:
      p2.c0(KM.m_get(s, 2), h, n, m, k)
    case False{}:
      p2.pick(n, h, s, m, k)

def p2.m(r: KM.M & U32, h: H, +n: U32, +most: U32, +k: U32) -> Pop2:
  (s, +m) = r
  p2.grow(U32.is_lt(m, ((n + most : U32) + 4 : U32)), h, s, n, m, k)

def p2.n(r: KM.M & U32, h: H, +most: U32, +k: U32) -> Pop2:
  (s, +n) = r
  p2.m(KM.m_get(s, 1), h, n, most, k)

# the near end's newest pair, else the far end's, the array grown first
# unless both ends fit with room for most more pairs
def pop2(e: E, +most: U32, +k: U32) -> Pop2:
  match e:
    case E{h, st}:
      match st:
        case Stk{s}:
          p2.n(KM.m_get(s, 0), h, most, k)

# Room for an event's notes (heap-strategies.erasure.kernel): a cascade of
# events notes more pairs than a pop leaves room for, so each event is
# given room first, the array grown as pop2 grows it, its far end moved to
# the new top (none for the stack alone, whose mark is its capacity).

def room.grown(r: KM.M & U32, +m: U32, +cap0: U32) -> Stk:
  (s, +cap) = r
  Stk{KM.m_set(KM.m_set(relocate(U32.to_nat((cap0 - m : U32)), s, (cap0 - 1 : U32), (cap - 1 : U32)),
    1, ((m + cap : U32) - cap0 : U32)), 2, cap)}

def room.c(r: KM.M & U32, +m: U32) -> Stk:
  (s, +cap) = r
  room.grown(KM.m_ensure(s, (cap * 2 : U32), cap, rs_maxd()), m, cap)

def room.go(full: Bool, s: KM.M, +m: U32) -> Stk:
  match full:
    case True{}:
      room.c(KM.m_get(s, 2), m)
    case False{}:
      Stk{s}

def room.m(r: KM.M & U32, +n: U32, +most: U32) -> Stk:
  (s, +m) = r
  room.go(U32.is_lt(m, ((n + most : U32) + 4 : U32)), s, m)

def room.n(r: KM.M & U32, +most: U32) -> Stk:
  (s, +n) = r
  room.m(KM.m_get(s, 1), n, most)

# st with room for most more pairs at its near end
def room(st: Stk, +most: U32) -> Stk:
  match st:
    case Stk{s}:
      room.n(KM.m_get(s, 0), most)

# a two-stack run's end: the net, its interactions counted
def unpop2(q: Pop2) -> H:
  match q:
    case Pop2{h, st, +x, +y, +src, +k}:
      count(h, k)

# a run's end: the net, the stack let go
def unpop(pp: Pop) -> H:
  match pp:
    case Pop{h, st, +x, +y, +ok}:
      h

# a node of rule kind k holding the value pw
def node_pw(h: H, +k: U32, pw: PW) -> H & U32:
  match pw:
    case PW{+m, +f, +w}:
      node(h, hd2(k, m, f), w)

# node_pw in slot r (renode)
def renode_pw(h: H, +r: U32, +k: U32, pw: PW) -> H & U32:
  match pw:
    case PW{+m, +f, +w}:
      renode(h, r, hd2(k, m, f), w)

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

def h_live.t(r: KM.M & DT) -> U32:
  (w, t) = r
  dt_live(t)

# data entries in use
def h_live(h: H) -> U32:
  match h:
    case H{w, a}:
      h_live.t(dt_of(w, a))

def h_ok.t(r: KM.M & DT, +held: U32) -> Bool:
  (w, t) = r
  dt_ok(t, held)

# the table's audit (dt_ok) against held entries
def h_ok(h: H, +held: U32) -> Bool:
  match h:
    case H{w, a}:
      h_ok.t(dt_of(w, a), held)
