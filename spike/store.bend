import Base
import ./val.bend as V

# The store: pages of 4096 slots. A node takes one slot: four words of its
# page's word array (a header, then the links of its three ports) and one
# payload. A port reference is one U32:
#
#   ref = page << 14 | slot << 2 | port
#
# so a node's words sit at (ref & 16380) | k in its page. Cells never move.
# The page being worked on is held out of the page table, so accesses to
# it never touch the table.

# Allocator metadata
# ==================

# A page's allocator, as plain data: its recycled slots, how many slots it
# has never handed out, and how many are live. live + |free| + fresh is
# the page's capacity, always (laws alloc_conserves, free_conserves).
type Meta is Data:
  Meta{free: List<&2, U32>, fresh: Nat, live: Nat}

type Got is Data:
  Got{m: Meta, slot: Maybe<&2, U32>}

def cap() -> Nat:
  4096n

def meta_new() -> Meta:
  Meta{Nil{}, cap(), 0n}

# a recycled slot if any, else the next fresh one; fresh counts down from
# cap, so the next fresh slot is cap - fresh
def meta_alloc(m: Meta) -> Got:
  match m:
    case Meta{free, fresh, live}:
      match free:
        case Con{s, rest}:
          Got{Meta{rest, fresh, 1n+live}, Some{s}}
        case Nil{}:
          match fresh:
            case 0n:
              Got{Meta{Nil{}, 0n, live}, None{}}
            case 1n++p:
              Got{Meta{Nil{}, p, 1n+live}, Some{U32.from_nat(Nat.sub(cap(), 1n+p))}}

def got_meta(g: Got) -> Meta:
  match g:
    case Got{m, s}:
      m

# a free with nothing live is ignored, a double free that would break the
# count
def meta_free(m: Meta, +s: U32) -> Meta:
  match m:
    case Meta{free, fresh, live}:
      match live:
        case 0n:
          Meta{free, fresh, 0n}
        case 1n+q:
          Meta{Con{s, free}, fresh, q}

def len(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+len(t)

def meta_count(m: Meta) -> Nat:
  match m:
    case Meta{free, fresh, live}:
      Nat.add(live, Nat.add(len(free), fresh))

def meta_live(m: Meta) -> Nat:
  match m:
    case Meta{free, fresh, live}:
      live

# References
# ==========

def nil() -> U32:
  4294967295

def ref_page(+r: U32) -> U32:
  (r >> 14n : U32)

def ref_slot(+r: U32) -> U32:
  ((r >> 2n : U32) .&. 4095 : U32)

def ref_port(+r: U32) -> U32:
  (r .&. 3 : U32)

# the index of word k (0..3) of r's node in its page
def ref_word(+r: U32, +k: U32) -> U32:
  ((r .&. 16380 : U32) .|. k : U32)

def mk_ref(+page: U32, +slot: U32, +port: U32) -> U32:
  (((page << 14n : U32) .|. (slot << 2n : U32) : U32) .|. port : U32)

# the same node, another port
def ref_at(+r: U32, +port: U32) -> U32:
  ((r .&. 4294967292 : U32) .|. port : U32)

# Pages
# =====

type Page is Type:
  Pg{w: Array<U32>, v: Array<V.Pay>, m: Meta}

def pg_new() -> Page:
  Pg{[0 : U32^14n], Array.new(V.Pay, 12n, V.PNone{}), meta_new()}

def pg_live(pg: Page) -> Page & Nat:
  match pg:
    case Pg{w, v, +m}:
      (Pg{w, v, m}, meta_live(m))

# The store
# =========

# tbl holds every page but the current one, cur, whose slot holds None;
# np pages exist, 2^td fit; errs counts references to missing pages
type Store is Type:
  St{tbl: Array<Maybe<&1, Page>>, cur: Page, +curp: U32, +np: U32, +td: Nat, +errs: U32}

def tbl_new(+d: Nat) -> Array<Maybe<&1, Page>>:
  match d:
    case 0n:
      ALeaf{None{}}
    case 1n+p:
      ANode{tbl_new(p), tbl_new(p)}

def st_new() -> Store:
  St{tbl_new(4n), pg_new(), 0, 1, 4n, 0}

def st_errs(st: Store) -> Store & U32:
  match st:
    case St{tbl, cur, +curp, +np, +td, +errs}:
      (St{tbl, cur, curp, np, td, errs}, errs)

def st_pages(st: Store) -> Store & U32:
  match st:
    case St{tbl, cur, +curp, +np, +td, +errs}:
      (St{tbl, cur, curp, np, td, errs}, np)

# Focus: make page p the current one
# ----------------------------------

def st_focus.take(r: Array<Maybe<&1, Page>> & Maybe<&1, Page>, +p: U32, +np: U32, +td: Nat, +errs: U32) -> Store:
  (tbl, mp) = r
  match mp:
    case Some{pg}:
      St{tbl, pg, p, np, td, errs}
    case None{}:
      St{tbl, pg_new(), p, np, td, (errs + 1 : U32)}

def st_focus.go(same: Bool, st: Store, +p: U32) -> Store:
  match same:
    case True{}:
      st
    case False{}:
      match st:
        case St{tbl, cur, +curp, +np, +td, +errs}:
          st_focus.take(Array.swap(Maybe<&1, Page>, Array.set(Maybe<&1, Page>, tbl, curp, Some{cur}), p, None{}), p, np, td, errs)

def st_focus(st: Store, +p: U32) -> Store:
  match st:
    case St{tbl, cur, +curp, +np, +td, +errs}:
      st_focus.go(U32.is_eq(curp, p), St{tbl, cur, curp, np, td, errs}, p)

# Words and payloads of the current page
# --------------------------------------

def pg_get.fin(+v_m: Unit, r: Array<U32> & U32, v: Array<V.Pay>, m: Meta) -> Page & U32:
  (w, +x) = r
  (Pg{w, v, m}, x)

def pg_get(pg: Page, +i: U32) -> Page & U32:
  match pg:
    case Pg{w, v, m}:
      pg_get.fin(Unit{}, Array.get(U32, w, i), v, m)

def pg_set(pg: Page, +i: U32, +x: U32) -> Page:
  match pg:
    case Pg{w, v, m}:
      Pg{Array.set(U32, w, i, x), v, m}

def pg_pay.fin(r: Array<V.Pay> & V.Pay, w: Array<U32>, m: Meta) -> Page & V.Pay:
  (v, x) = r
  (Pg{w, v, m}, x)

def pg_pay(pg: Page, +i: U32) -> Page & V.Pay:
  match pg:
    case Pg{w, v, m}:
      pg_pay.fin(Array.get(V.Pay, v, i), w, m)

def pg_set_pay(pg: Page, +i: U32, x: V.Pay) -> Page:
  match pg:
    case Pg{w, v, m}:
      Pg{w, Array.set(V.Pay, v, i, x), m}

def st_with_cur(r: Page & U32, tbl: Array<Maybe<&1, Page>>, +curp: U32, +np: U32, +td: Nat, +errs: U32) -> Store & U32:
  (pg, +x) = r
  (St{tbl, pg, curp, np, td, errs}, x)

def st_with_pay(r: Page & V.Pay, tbl: Array<Maybe<&1, Page>>, +curp: U32, +np: U32, +td: Nat, +errs: U32) -> Store & V.Pay:
  (pg, x) = r
  (St{tbl, pg, curp, np, td, errs}, x)

# word k of r's node
def st_get.at(st: Store, +r: U32, +k: U32) -> Store & U32:
  match st:
    case St{tbl, cur, +curp, +np, +td, +errs}:
      st_with_cur(pg_get(cur, ref_word(r, k)), tbl, curp, np, td, errs)

def st_get(st: Store, +r: U32, +k: U32) -> Store & U32:
  st_get.at(st_focus(st, ref_page(r)), r, k)

def st_set.at(st: Store, +r: U32, +k: U32, +x: U32) -> Store:
  match st:
    case St{tbl, cur, +curp, +np, +td, +errs}:
      St{tbl, pg_set(cur, ref_word(r, k), x), curp, np, td, errs}

def st_set(st: Store, +r: U32, +k: U32, +x: U32) -> Store:
  st_set.at(st_focus(st, ref_page(r)), r, k, x)

def st_pay.at(st: Store, +r: U32) -> Store & V.Pay:
  match st:
    case St{tbl, cur, +curp, +np, +td, +errs}:
      st_with_pay(pg_pay(cur, ref_slot(r)), tbl, curp, np, td, errs)

def st_pay(st: Store, +r: U32) -> Store & V.Pay:
  st_pay.at(st_focus(st, ref_page(r)), r)

def st_set_pay.at(st: Store, +r: U32, x: V.Pay) -> Store:
  match st:
    case St{tbl, cur, +curp, +np, +td, +errs}:
      St{tbl, pg_set_pay(cur, ref_slot(r), x), curp, np, td, errs}

def st_set_pay(st: Store, +r: U32, x: V.Pay) -> Store:
  st_set_pay.at(st_focus(st, ref_page(r)), r, x)

# Allocation
# ----------

# move pages 0 .. n-1 from one table into another
type Tbls is Type:
  Tbls{old: Array<Maybe<&1, Page>>, new: Array<Maybe<&1, Page>>}

def tbl_move.fin(+i: U32, r: Array<Maybe<&1, Page>> & Maybe<&1, Page>, new: Array<Maybe<&1, Page>>) -> Tbls:
  (old, mp) = r
  Tbls{old, Array.set(Maybe<&1, Page>, new, i, mp)}

def tbl_move.step(+i: U32, ts: Tbls) -> Tbls:
  match ts:
    case Tbls{old, new}:
      tbl_move.fin(i, Array.swap(Maybe<&1, Page>, old, i, None{}), new)

def tbl_move(n: Nat, +i: U32, ts: Tbls) -> Tbls:
  match n:
    case 0n:
      ts
    case 1n+p:
      tbl_move(p, (i + 1 : U32), tbl_move.step(i, ts))

def tbls_new(ts: Tbls) -> Array<Maybe<&1, Page>>:
  match ts:
    case Tbls{old, new}:
      new

# a table with room for one more page: doubled when full
def tbl_room(full: Bool, tbl: Array<Maybe<&1, Page>>, +np: U32, +td: Nat) -> Array<Maybe<&1, Page>> & Nat:
  match full:
    case True{}:
      (tbls_new(tbl_move(U32.to_nat(np), 0, Tbls{tbl, tbl_new(1n+td)})), 1n+td)
    case False{}:
      (tbl, td)

def st_open.alloc(g: Got, tbl: Array<Maybe<&1, Page>>, +np: U32, +td: Nat, +errs: U32) -> Store & U32:
  match g:
    case Got{m, slot}:
      (St{tbl, Pg{[0 : U32^14n], Array.new(V.Pay, 12n, V.PNone{}), m}, np, (np + 1 : U32), td, errs}, mk_ref(np, Maybe.default(&2, U32, slot, 0), 0))

# the current page is full: put it back and start a fresh page, np
def st_open.fin(r: Array<Maybe<&1, Page>> & Nat, +np: U32, +errs: U32) -> Store & U32:
  (tbl, +td) = r
  st_open.alloc(meta_alloc(meta_new()), tbl, np, td, errs)

def st_open(st: Store) -> Store & U32:
  match st:
    case St{tbl, cur, +curp, +np, +td, +errs}:
      st_open.fin(tbl_room(U32.is_eq(np, U32.from_nat(Nat.pow(2n, td))), Array.set(Maybe<&1, Page>, tbl, curp, Some{cur}), np, td), np, errs)

def st_alloc.got(g: Got, tbl: Array<Maybe<&1, Page>>, w: Array<U32>, v: Array<V.Pay>, +curp: U32, +np: U32, +td: Nat, +errs: U32) -> Store & U32:
  match g:
    case Got{m, slot}:
      match slot:
        case Some{+s}:
          (St{tbl, Pg{w, v, m}, curp, np, td, errs}, mk_ref(curp, s, 0))
        case None{}:
          st_open(St{tbl, Pg{w, v, m}, curp, np, td, errs})

# a fresh node: port 0's reference; its words are zero and its payload none
def st_alloc(st: Store) -> Store & U32:
  match st:
    case St{tbl, cur, +curp, +np, +td, +errs}:
      match cur:
        case Pg{w, v, m}:
          st_alloc.got(meta_alloc(m), tbl, w, v, curp, np, td, errs)

def st_free.at(st: Store, +r: U32) -> Store:
  match st:
    case St{tbl, cur, +curp, +np, +td, +errs}:
      match cur:
        case Pg{w, v, m}:
          +i = ref_word(r, 0)
          w1 = Array.set(U32, w, i, 0)
          w2 = Array.set(U32, w1, (i + 1 : U32), 0)
          w3 = Array.set(U32, w2, (i + 2 : U32), 0)
          w4 = Array.set(U32, w3, (i + 3 : U32), 0)
          St{tbl, Pg{w4, Array.set(V.Pay, v, ref_slot(r), V.PNone{}), meta_free(m, ref_slot(r))}, curp, np, td, errs}

# free r's node: its words zeroed, its payload dropped, its slot recycled
def st_free(st: Store, +r: U32) -> Store:
  st_free.at(st_focus(st, ref_page(r)), r)
