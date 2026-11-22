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
#   2 and 3 its children for that bit clear and set. Bits are tested from
#   the lowest, rising from root to leaf, and every key below a branch
#   agrees with the others on the bits beneath its own, so that a tree's
#   shape is a function of its keys. Nothing links to a branch through a
#   port, so no walk of the kernel's meets one.
# - A descent tests at most 32 bits, and one that does not end at a leaf
#   within 33 steps is a corrupt tree, reported
#   (corruption-reported-when-cheap).
# - Keys are distinct: an insert meeting its own key is an error, the
#   tree unchanged (one cursor a position in a copy, a law to come).
# - The tests are Bools and their choices made by helpers matching them
#   (ix.kid, ix.pick), and a branch's bit is a Nat below 32, so that the
#   laws follow a descent by cases, without arithmetic on bits
#   (glam/INDEX_PROOF.bend).

def ix.fuel() -> Nat:
  33n

# a branch's header: kind 18, form 3
def ix.branch(+hd: U32) -> Bool:
  U32.is_eq(P.rk(hd), 18) && U32.is_eq(P.form(hd), 3)

# the bit a branch with header hd tests
def ix.bitof(+hd: U32) -> Nat:
  U32.to_nat(P.fld(hd))

# a branch testing bit i
def ix.hd(+i: Nat) -> U32:
  P.hd2(18, 3, U32.from_nat(i))

# bit i of k set
def ix.side(+k: U32, +i: Nat) -> Bool:
  U32.is_eq(((k >> i : U32) .&. 1 : U32), 1)

# the word of branch x holding its child on side s
def ix.kid(+s: Bool, +x: U32) -> U32:
  match s:
    case True{}:
      (x + 3 : U32)
    case False{}:
      (x + 2 : U32)

def ix.pick(+s: Bool, +a: U32, +b: U32) -> U32:
  match s:
    case True{}:
      a
    case False{}:
      b

# The lowest bit two keys differ at
# =================================

# Bools alike
def ix.same(+p: Bool, +q: Bool) -> Bool:
  match p:
    case True{}:
      q
    case False{}:
      Bool.not(q)

# a scan of two keys' bits from the lowest: the bit it is at, and whether
# the keys have agreed so far
type Cr is Type:
  Cr{+i: Nat, +go: Bool}

def cr.k(+eq: Bool, +i: Nat) -> Cr:
  match eq:
    case True{}:
      Cr{1n+i, True{}}
    case False{}:
      Cr{i, False{}}

def cr.step(+a: U32, +b: U32, +i: Nat) -> Cr:
  cr.k(ix.same(ix.side(a, i), ix.side(b, i)), i)

# at most f bits looked at
def ix.crit(f: Nat, c: Cr, +a: U32, +b: U32) -> Cr:
  match f:
    case 0n:
      c
    case 1n+g:
      match c:
        case Cr{+i, +go}:
          match go:
            case False{}:
              Cr{i, False{}}
            case True{}:
              ix.crit(g, cr.step(a, b, i), a, b)

# the 32 bits of a and b looked at: stopped at the lowest they differ at,
# or still going, which unequal keys never are (INDEX_PROOF's ne_found)
def ix.diff(+a: U32, +b: U32) -> Cr:
  ix.crit(32n, Cr{0n, True{}}, a, b)

# Descent
# =======

# a descent for key k: the net, the node reached, whether it goes on
type Ds is Type:
  Ds{h: P.H, +x: U32, +go: Bool}

def ds.c(r: P.H & U32) -> Ds:
  (h, +c) = r
  Ds{h, c, True{}}

def ds.k(+br: Bool, h: P.H, +x: U32, +i: Nat, +k: U32) -> Ds:
  match br:
    case True{}:
      ds.c(P.rd(h, ix.kid(ix.side(k, i), x)))
    case False{}:
      Ds{h, x, False{}}

def ds.hd(r: P.H & U32, +x: U32, +k: U32) -> Ds:
  (h, +hd) = r
  ds.k(ix.branch(hd), h, x, ix.bitof(hd), k)

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
# to cur, and cur, while cur is a branch testing a lower bit
type Pl is Type:
  Pl{h: P.H, +loc: U32, +cur: U32, +go: Bool}

def pl.c(r: P.H & U32, +loc: U32) -> Pl:
  (h, +c) = r
  Pl{h, loc, c, True{}}

def pl.k(+down: Bool, h: P.H, +loc: U32, +cur: U32, +i: Nat, +k: U32) -> Pl:
  match down:
    case True{}:
      pl.c(P.rd(h, ix.kid(ix.side(k, i), cur)), ix.kid(ix.side(k, i), cur))
    case False{}:
      Pl{h, loc, cur, False{}}

def pl.hd(r: P.H & U32, +loc: U32, +cur: U32, +c: Nat, +k: U32) -> Pl:
  (h, +hd) = r
  pl.k(ix.branch(hd) && Nat.is_lt(ix.bitof(hd), c), h, loc, cur, ix.bitof(hd), k)

def pl.out(p: Pl) -> Pl:
  match p:
    case Pl{h, +loc, +cur, +go}:
      Pl{P.err_if(go, h), loc, cur, False{}}

def pl.run(f: Nat, p: Pl, +c: Nat, +k: U32) -> Pl:
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

# branch b of bit c in place at loc: x on k's side, cur on the other,
# the child set the node's payload word 3
def ix.put.b(r: P.H & U32, +loc: U32, +cur: U32, +c: Nat, +k: U32, +x: U32, +s: U32) -> P.H:
  (h, +b) = r
  P.wr(P.wr(P.wr(P.wr(h, (b + 1 : U32), P.era()),
    (b + 2 : U32), ix.pick(ix.side(k, c), cur, x)),
    loc, b), (x + 3 : U32), s)

def ix.put.p(p: Pl, +c: Nat, +k: U32, +x: U32, +s: U32) -> P.H:
  match p:
    case Pl{h, +loc, +cur, +go}:
      ix.put.b(P.node(h, ix.hd(c), ix.pick(ix.side(k, c), x, cur)), loc, cur, c, k, x, s)

# the keys' lowest differing bit c, the new branch's; none found an error
def ix.put.c(c: Cr, h: P.H, +root: U32, +k: U32, +x: U32, +s: U32) -> P.H:
  match c:
    case Cr{+i, +go}:
      match go:
        case True{}:
          P.err_if(True{}, h)
        case False{}:
          ix.put.p(pl.run(ix.fuel(), Pl{h, (s + 3 : U32), root, True{}}, i, k), i, k, x, s)

def ix.put.n(+same: Bool, h: P.H, +nk: U32, +root: U32, +k: U32, +x: U32, +s: U32) -> P.H:
  match same:
    case True{}:
      P.err_if(True{}, h)
    case False{}:
      ix.put.c(ix.diff(k, nk), h, root, k, x, s)

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

# x found on side sd of cur: the pointer at loc given x's sibling, cur
# freed
def rm.found(r: P.H & U32, +loc: U32, +cur: U32) -> Rm:
  (h, +sib) = r
  Rm{P.free(P.wr(h, loc, sib), cur), loc, cur, False{}}

def rm.child(+hit: Bool, h: P.H, +loc: U32, +cur: U32, +sd: Bool, +child: U32) -> Rm:
  match hit:
    case True{}:
      rm.found(P.rd(h, ix.kid(Bool.not(sd), cur)), loc, cur)
    case False{}:
      Rm{h, ix.kid(sd, cur), child, True{}}

def rm.c(r: P.H & U32, +loc: U32, +cur: U32, +sd: Bool, +x: U32) -> Rm:
  (h, +child) = r
  rm.child(U32.is_eq(child, x), h, loc, cur, sd, child)

def rm.br(+br: Bool, h: P.H, +loc: U32, +cur: U32, +i: Nat, +k: U32, +x: U32) -> Rm:
  match br:
    case True{}:
      rm.c(P.rd(h, ix.kid(ix.side(k, i), cur)), loc, cur, ix.side(k, i), x)
    case False{}:
      Rm{P.err_if(True{}, h), loc, cur, False{}}

def rm.hd(r: P.H & U32, +loc: U32, +cur: U32, +k: U32, +x: U32) -> Rm:
  (h, +hd) = r
  rm.br(ix.branch(hd), h, loc, cur, ix.bitof(hd), k, x)

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
