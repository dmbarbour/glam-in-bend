import Base
import ../spike/kprim.bend as P

# A copy's index (the Cells plan's cells-freeze.sharing.cursors.index;
# `cursors-indexed`): the copy's cursors kept in a crit-bit tree of the
# net's own nodes, keyed by their source positions, in place of a ring.
#
# - The situating node's word 3 holds the tree's root, or the situating
#   node itself when the tree is empty (as an empty ring's word 3 did).
# - A leaf is a cursor (kind 18, form 0 or 1): word 2 its position, the
#   key; word 3 its situating node, its home. A tree of one leaf is the
#   words of a ring of one: the situating node and the cursor naming
#   each other.
# - A branch is a node of kind 18 and form 3: its field the bit it tests,
#   its word 1 a static eraser (no port, as the situating node's), words
#   2 and 3 its children for that bit clear and set. Bits tested fall
#   from root to leaf, so a tree's shape is a function of its keys.
#   Nothing links to a branch through a port, so no walk of the kernel's
#   meets one.
# - A key is a source reference, below 2^30; a descent tests at most 32
#   bits, and one that does not end at a leaf within 33 steps is a
#   corrupt tree, reported (corruption-reported-when-cheap).
# - Keys are distinct: an insert meeting its own key is an error, the
#   tree unchanged (one cursor a position in a copy, a law to come).

def ix.fuel() -> Nat:
  33n

# a branch's header: kind 18, form 3
def ix.branch(+hd: U32) -> Bool:
  U32.is_eq(P.rk(hd), 18) && U32.is_eq(P.form(hd), 3)

# bit b of k, 0 or 1
def ix.bit(+k: U32, +b: U32) -> U32:
  ((k >> U32.to_nat(b) : U32) .&. 1 : U32)

# the highest bit set in x among the f from bit i up, best the highest
# found below i; 0 if none
def ix.hb(f: Nat, +i: U32, +x: U32, +best: U32) -> U32:
  match f:
    case 0n:
      best
    case 1n+g:
      ix.hb(g, (i + 1 : U32), x, P.sel_u(U32.is_eq(ix.bit(x, i), 1), i, best))

# Descent
# =======

# a descent for key k: the net, the node reached, whether it goes on
type Ds is Type:
  Ds{h: P.H, +x: U32, +go: Bool}

def ds.c(r: P.H & U32) -> Ds:
  (h, +c) = r
  Ds{h, c, True{}}

def ds.k(+br: Bool, h: P.H, +x: U32, +b: U32, +k: U32) -> Ds:
  match br:
    case True{}:
      ds.c(P.rd(h, ((x + 2 : U32) + ix.bit(k, b) : U32)))
    case False{}:
      Ds{h, x, False{}}

def ds.hd(r: P.H & U32, +x: U32, +k: U32) -> Ds:
  (h, +hd) = r
  ds.k(ix.branch(hd), h, x, P.fld(hd), k)

# fuel spent: a descent still going is a corrupt tree
def ds.out(d: Ds) -> Ds:
  match d:
    case Ds{h, +x, +go}:
      Ds{P.err_if(go, h), x, False{}}

# down from x to the leaf key k leads to
def ds.run(f: Nat, d: Ds, +k: U32) -> Ds:
  match f:
    case 0n:
      ds.out(d)
    case 1n+g:
      match d:
        case Ds{h, +x, +go}:
          match go:
            case False{}:
              Ds{h, x, False{}}
            case True{}:
              ds.run(g, ds.hd(P.rd(h, x), x, k), k)

# Find
# ====

def ix.found.s(+same: Bool, h: P.H, +x: U32) -> P.H & Maybe<&2, U32>:
  match same:
    case True{}:
      (h, Some{x})
    case False{}:
      (h, None{})

def ix.found.k(r: P.H & U32, +x: U32, +k: U32) -> P.H & Maybe<&2, U32>:
  (h, +key) = r
  ix.found.s(U32.is_eq(key, k), h, x)

def ix.found(d: Ds, +k: U32) -> P.H & Maybe<&2, U32>:
  match d:
    case Ds{h, +x, +go}:
      ix.found.k(P.rd(h, (x + 2 : U32)), x, k)

def ix.find.k(+empty: Bool, h: P.H, +root: U32, +k: U32) -> P.H & Maybe<&2, U32>:
  match empty:
    case True{}:
      (h, None{})
    case False{}:
      ix.found(ds.run(ix.fuel(), Ds{h, root, True{}}, k), k)

def ix.find.r(r: P.H & U32, +s: U32, +k: U32) -> P.H & Maybe<&2, U32>:
  (h, +root) = r
  ix.find.k(U32.is_eq(root, s), h, root, k)

# the cursor of situating node s's tree at position k, if any
def ix.find(h: P.H, +s: U32, +k: U32) -> P.H & Maybe<&2, U32>:
  ix.find.r(P.rd(h, (s + 3 : U32)), s, k)

# Insert
# ======

# placing a new branch of bit c: the net, the word holding the pointer
# to cur, and cur, while cur is a branch testing a higher bit
type Pl is Type:
  Pl{h: P.H, +loc: U32, +cur: U32, +go: Bool}

def pl.c(r: P.H & U32, +loc: U32) -> Pl:
  (h, +c) = r
  Pl{h, loc, c, True{}}

def pl.k(+down: Bool, h: P.H, +loc: U32, +cur: U32, +b: U32, +k: U32) -> Pl:
  match down:
    case True{}:
      pl.c(P.rd(h, ((cur + 2 : U32) + ix.bit(k, b) : U32)), ((cur + 2 : U32) + ix.bit(k, b) : U32))
    case False{}:
      Pl{h, loc, cur, False{}}

def pl.hd(r: P.H & U32, +loc: U32, +cur: U32, +c: U32, +k: U32) -> Pl:
  (h, +hd) = r
  pl.k(ix.branch(hd) && U32.is_gt(P.fld(hd), c), h, loc, cur, P.fld(hd), k)

def pl.out(p: Pl) -> Pl:
  match p:
    case Pl{h, +loc, +cur, +go}:
      Pl{P.err_if(go, h), loc, cur, False{}}

def pl.run(f: Nat, p: Pl, +c: U32, +k: U32) -> Pl:
  match f:
    case 0n:
      pl.out(p)
    case 1n+g:
      match p:
        case Pl{h, +loc, +cur, +go}:
          match go:
            case False{}:
              Pl{h, loc, cur, False{}}
            case True{}:
              pl.run(g, pl.hd(P.rd(h, cur), loc, cur, c, k), c, k)

# branch b of bit c in place at loc: x on k's side, cur on the other
def ix.put.b(r: P.H & U32, +loc: U32, +cur: U32, +c: U32, +k: U32, +x: U32, +s: U32) -> P.H:
  (h, +b) = r
  P.wr(P.wr(P.wr(P.wr(P.wr(h, (b + 1 : U32), P.era()),
    (b + 2 : U32), P.sel_u(U32.is_eq(ix.bit(k, c), 0), x, cur)),
    (b + 3 : U32), P.sel_u(U32.is_eq(ix.bit(k, c), 0), cur, x)),
    loc, b), (x + 3 : U32), s)

def ix.put.p(p: Pl, +c: U32, +k: U32, +x: U32, +s: U32) -> P.H:
  match p:
    case Pl{h, +loc, +cur, +go}:
      ix.put.b(P.node(h, P.hd2(18, 3, c), 0), loc, cur, c, k, x, s)

def ix.put.n(+same: Bool, h: P.H, +nk: U32, +root: U32, +k: U32, +x: U32, +s: U32) -> P.H:
  match same:
    case True{}:
      P.err_if(True{}, h)
    case False{}:
      ix.put.p(pl.run(ix.fuel(), Pl{h, (s + 3 : U32), root, True{}}, ix.hb(32n, 0, (k .^. nk : U32), 0), k),
        ix.hb(32n, 0, (k .^. nk : U32), 0), k, x, s)

def ix.put.l(r: P.H & U32, +root: U32, +k: U32, +x: U32, +s: U32) -> P.H:
  (h, +nk) = r
  ix.put.n(U32.is_eq(nk, k), h, nk, root, k, x, s)

def ix.put.d(d: Ds, +root: U32, +k: U32, +x: U32, +s: U32) -> P.H:
  match d:
    case Ds{h, +l, +go}:
      ix.put.l(P.rd(h, (l + 2 : U32)), root, k, x, s)

def ix.put.k(+empty: Bool, h: P.H, +root: U32, +k: U32, +x: U32, +s: U32) -> P.H:
  match empty:
    case True{}:
      P.wr(P.wr(h, (s + 3 : U32), x), (x + 3 : U32), s)
    case False{}:
      ix.put.d(ds.run(ix.fuel(), Ds{h, root, True{}}, k), root, k, x, s)

def ix.put.r(r: P.H & U32, +s: U32, +x: U32, +k: U32) -> P.H:
  (h, +root) = r
  ix.put.k(U32.is_eq(root, s), h, root, k, x, s)

def ix.put.x(r: P.H & U32, +s: U32, +x: U32) -> P.H:
  (h, +k) = r
  ix.put.r(P.rd(h, (s + 3 : U32)), s, x, k)

# cursor x, its position in word 2, put in situating node s's tree
def ix.insert(h: P.H, +s: U32, +x: U32) -> P.H:
  ix.put.x(P.rd(h, (x + 2 : U32)), s, x)

# Remove
# ======

# looking for x's parent: the net, the word holding the pointer to cur,
# cur a branch, whether it goes on
type Rm is Type:
  Rm{h: P.H, +loc: U32, +cur: U32, +go: Bool}

def rm.found(r: P.H & U32, +loc: U32, +cur: U32) -> Rm:
  (h, +sib) = r
  Rm{P.free(P.wr(h, loc, sib), cur), loc, cur, False{}}

def rm.child(+hit: Bool, h: P.H, +loc: U32, +cur: U32, +side: U32, +child: U32) -> Rm:
  match hit:
    case True{}:
      rm.found(P.rd(h, ((cur + 2 : U32) + (1 - side : U32) : U32)), loc, cur)
    case False{}:
      Rm{h, ((cur + 2 : U32) + side : U32), child, True{}}

def rm.c(r: P.H & U32, +loc: U32, +cur: U32, +side: U32, +x: U32) -> Rm:
  (h, +child) = r
  rm.child(U32.is_eq(child, x), h, loc, cur, side, child)

def rm.br(+br: Bool, h: P.H, +loc: U32, +cur: U32, +b: U32, +k: U32, +x: U32) -> Rm:
  match br:
    case True{}:
      rm.c(P.rd(h, ((cur + 2 : U32) + ix.bit(k, b) : U32)), loc, cur, ix.bit(k, b), x)
    case False{}:
      Rm{P.err_if(True{}, h), loc, cur, False{}}

def rm.hd(r: P.H & U32, +loc: U32, +cur: U32, +k: U32, +x: U32) -> Rm:
  (h, +hd) = r
  rm.br(ix.branch(hd), h, loc, cur, P.fld(hd), k, x)

def rm.out(m: Rm) -> Rm:
  match m:
    case Rm{h, +loc, +cur, +go}:
      Rm{P.err_if(go, h), loc, cur, False{}}

def rm.run(f: Nat, m: Rm, +k: U32, +x: U32) -> Rm:
  match f:
    case 0n:
      rm.out(m)
    case 1n+g:
      match m:
        case Rm{h, +loc, +cur, +go}:
          match go:
            case False{}:
              Rm{h, loc, cur, False{}}
            case True{}:
              rm.run(g, rm.hd(P.rd(h, cur), loc, cur, k, x), k, x)

def rm.h(m: Rm) -> P.H:
  match m:
    case Rm{h, +loc, +cur, +go}:
      h

def ix.rm.k(+only: Bool, h: P.H, +root: U32, +s: U32, +k: U32, +x: U32) -> P.H:
  match only:
    case True{}:
      P.wr(h, (s + 3 : U32), s)
    case False{}:
      rm.h(rm.run(ix.fuel(), Rm{h, (s + 3 : U32), root, True{}}, k, x))

def ix.rm.r(r: P.H & U32, +s: U32, +k: U32, +x: U32) -> P.H:
  (h, +root) = r
  ix.rm.k(U32.is_eq(root, x), h, root, s, k, x)

def ix.rm.x(r: P.H & U32, +s: U32, +x: U32) -> P.H:
  (h, +k) = r
  ix.rm.r(P.rd(h, (s + 3 : U32)), s, k, x)

# cursor x taken out of situating node s's tree, its parent branch freed
def ix.remove(h: P.H, +s: U32, +x: U32) -> P.H:
  ix.rm.x(P.rd(h, (x + 2 : U32)), s, x)

# Home
# ====

# a cursor's situating node: its word 3
def ix.home(h: P.H, +x: U32) -> P.H & U32:
  P.rd(h, (x + 3 : U32))
