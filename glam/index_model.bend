import Base
import ../spike/kprim.bend as P
import ../spike/kmodel.bend as KMd
import ./index.bend as X

# The model of a copy's index (glam/index.bend; the Cells plan's
# cells-freeze.sharing.cursors.index.laws): its tree as a value, the
# heap's words realizing it, the invariant that makes a descent find a
# key, and the code's three operations on the value. The model shares the
# code's decisions on bits (X.ix.side, X.ix.diff), so that the laws claim
# the tree's handling of words and its shape, and the bit facts are
# proved apart (glam/INDEX_PROOF.bend). Each choice a test makes is a
# helper matching the test's Bool (docs/Proving.md); each recursion
# structural, both children computed where a descent takes one.

# a tree: a leaf, cursor x at key k; a branch, node b testing bit i, its
# children for the bit clear and set
type Tr is Data:
  Lf{+x: U32, +k: U32}
  Br{+b: U32, +i: Nat, l: Tr, r: Tr}

# an index: empty, or a tree
type Ix is Data:
  Ept{}
  Has{t: Tr}

def tr.addr(t: Tr) -> U32:
  match t:
    case Lf{+x, +k}:
      x
    case Br{+b, +i, l, r}:
      b

def mb.pick(+s: Bool, a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match s:
    case True{}:
      a
    case False{}:
      b

def mb.hit(+same: Bool, +x: U32) -> Maybe<&2, U32>:
  match same:
    case True{}:
      Some{x}
    case False{}:
      None{}

# Find: the leaf key k leads to, if its key is k
def tr.look(t: Tr, +k: U32) -> Maybe<&2, U32>:
  match t:
    case Lf{+x, +kk}:
      mb.hit(U32.is_eq(kk, k), x)
    case Br{+b, +i, l, r}:
      mb.pick(X.ix.side(k, i), tr.look(r, k), tr.look(l, k))

def ix.look(I: Ix, +k: U32) -> Maybe<&2, U32>:
  match I:
    case Ept{}:
      None{}
    case Has{t}:
      tr.look(t, k)

# The leaf at key k, the leftmost if any were two: what a find should
# give, whatever the tree's shape (the law look_at: the descent finds it)
def mb.or(a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match a:
    case Some{+x}:
      Some{x}
    case None{}:
      b

def tr.at(t: Tr, +k: U32) -> Maybe<&2, U32>:
  match t:
    case Lf{+x, +kk}:
      mb.hit(U32.is_eq(kk, k), x)
    case Br{+b, +i, l, r}:
      mb.or(tr.at(l, k), tr.at(r, k))

def ix.at(I: Ix, +k: U32) -> Maybe<&2, U32>:
  match I:
    case Ept{}:
      None{}
    case Has{t}:
      tr.at(t, k)

# Insert: the key at the leaf k leads to; the new branch b at bit c, the
# leaf x on k's side; placed above the first node on k's way not a
# branch of a lower bit
def tr.near(t: Tr, +k: U32) -> U32:
  match t:
    case Lf{+x, +kk}:
      kk
    case Br{+b, +i, l, r}:
      X.ix.pick(X.ix.side(k, i), tr.near(r, k), tr.near(l, k))

def tr.join(+s: Bool, cur: Tr, +x: U32, +k: U32, +b: U32, +c: Nat) -> Tr:
  match s:
    case True{}:
      Br{b, c, cur, Lf{x, k}}
    case False{}:
      Br{b, c, Lf{x, k}, cur}

def tr.down(+sd: Bool, +b2: U32, +i: Nat, +l: Tr, +r: Tr, pl: Tr, pr: Tr) -> Tr:
  match sd:
    case True{}:
      Br{b2, i, l, pr}
    case False{}:
      Br{b2, i, pl, r}

def tr.place.k(+lt: Bool, +sd: Bool, +b2: U32, +i: Nat, +l: Tr, +r: Tr, pl: Tr, pr: Tr, +x: U32, +k: U32, +b: U32, +c: Nat) -> Tr:
  match lt:
    case True{}:
      tr.down(sd, b2, i, l, r, pl, pr)
    case False{}:
      tr.join(X.ix.side(k, c), Br{b2, i, l, r}, x, k, b, c)

def tr.place(t: Tr, +x: U32, +k: U32, +b: U32, +c: Nat) -> Tr:
  match t:
    case Lf{+y, +ky}:
      tr.join(X.ix.side(k, c), Lf{y, ky}, x, k, b, c)
    case Br{+b2, +i, +l, +r}:
      tr.place.k(Nat.is_lt(i, c), X.ix.side(k, i), b2, i, l, r, tr.place(l, x, k, b, c), tr.place(r, x, k, b, c), x, k, b, c)

def cr.i(c: X.Cr) -> Nat:
  match c:
    case X.Cr{+i, +go}:
      i

def cr.go(c: X.Cr) -> Bool:
  match c:
    case X.Cr{+i, +go}:
      go

def ix.put(I: Ix, +x: U32, +k: U32, +b: U32) -> Ix:
  match I:
    case Ept{}:
      Has{Lf{x, k}}
    case Has{+t}:
      Has{tr.place(t, x, k, b, cr.i(X.ix.diff(k, tr.near(t, k))))}

# Remove: x's parent replaced by x's sibling; the branch freed, if any
def tr.cut.r(+hit: Bool, +b: U32, +i: Nat, +l: Tr, cr: Tr) -> Tr:
  match hit:
    case True{}:
      l
    case False{}:
      Br{b, i, l, cr}

def tr.cut.l(+hit: Bool, +b: U32, +i: Nat, +r: Tr, cl: Tr) -> Tr:
  match hit:
    case True{}:
      r
    case False{}:
      Br{b, i, cl, r}

def tr.cut.k(+sd: Bool, +b: U32, +i: Nat, +l: Tr, +r: Tr, +x: U32, cl: Tr, cr: Tr) -> Tr:
  match sd:
    case True{}:
      tr.cut.r(U32.is_eq(tr.addr(r), x), b, i, l, cr)
    case False{}:
      tr.cut.l(U32.is_eq(tr.addr(l), x), b, i, r, cl)

def tr.cut(t: Tr, +x: U32, +k: U32) -> Tr:
  match t:
    case Lf{+y, +ky}:
      Lf{y, ky}
    case Br{+b, +i, +l, +r}:
      tr.cut.k(X.ix.side(k, i), b, i, l, r, x, tr.cut(l, x, k), tr.cut(r, x, k))

def ix.del.k(+only: Bool, t: Tr, +x: U32, +k: U32) -> Ix:
  match only:
    case True{}:
      Ept{}
    case False{}:
      Has{tr.cut(t, x, k)}

def ix.del(I: Ix, +x: U32, +k: U32) -> Ix:
  match I:
    case Ept{}:
      Ept{}
    case Has{+t}:
      ix.del.k(U32.is_eq(tr.addr(t), x), t, x, k)

# the branch a removal of x frees: x's parent, or none where x is the root
def tr.par.k(+sd: Bool, +b: U32, +hl: Bool, +hr: Bool, pl: Maybe<&2, U32>, pr: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match sd:
    case True{}:
      match hr:
        case True{}:
          Some{b}
        case False{}:
          pr
    case False{}:
      match hl:
        case True{}:
          Some{b}
        case False{}:
          pl

def tr.par(t: Tr, +x: U32, +k: U32) -> Maybe<&2, U32>:
  match t:
    case Lf{+y, +ky}:
      None{}
    case Br{+b, +i, +l, +r}:
      tr.par.k(X.ix.side(k, i), b, U32.is_eq(tr.addr(l), x), U32.is_eq(tr.addr(r), x), tr.par(l, x, k), tr.par(r, x, k))

def ix.par(I: Ix, +x: U32, +k: U32) -> Maybe<&2, U32>:
  match I:
    case Ept{}:
      None{}
    case Has{t}:
      tr.par(t, x, k)

# The heap's words realizing a tree (v the words' view, d its depth): the
# pointer p to it (the tree before it, as the recursion wants); a leaf's header no branch's, its word 2 its key, its
# word 3 the situating node s; a branch's header a branch's, testing its
# bit, its words 2 and 3 pointers to its children
def tr.real(+v: List<&2, U32>, +d: Nat, t: Tr, +p: U32, +s: U32) -> Bool:
  match t:
    case Lf{+x, +k}:
      U32.is_eq(p, x) && (Bool.not(X.ix.branch(KMd.word(v, d, x))) && (U32.is_eq(KMd.word(v, d, (x + 2 : U32)), k) && U32.is_eq(KMd.word(v, d, (x + 3 : U32)), s)))
    case Br{+b, +i, l, r}:
      U32.is_eq(p, b) && (X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s))))

# situating node s's word 3 itself where the index is empty, else the
# pointer to its tree, which is not s
def ix.real(+v: List<&2, U32>, +d: Nat, +s: U32, I: Ix) -> Bool:
  match I:
    case Ept{}:
      U32.is_eq(KMd.word(v, d, (s + 3 : U32)), s)
    case Has{t}:
      Bool.not(U32.is_eq(KMd.word(v, d, (s + 3 : U32)), s)) && tr.real(v, d, t, KMd.word(v, d, (s + 3 : U32)), s)

# The invariant: each branch's bit below 32 and below its children's;
# every key below it alike below its bit, on its child's side at it

# keys a and b alike below bit i
def tr.agree(+a: U32, +b: U32, i: Nat) -> Bool:
  match i:
    case 0n:
      True{}
    case 1n+(+j):
      X.ix.same(X.ix.side(a, j), X.ix.side(b, j)) && tr.agree(a, b, j)

# the leftmost key
def tr.first(t: Tr) -> U32:
  match t:
    case Lf{+x, +k}:
      k
    case Br{+b, +i, l, r}:
      tr.first(l)

# every key of t alike with p below bit i, and bit i of it s
def tr.all(t: Tr, +p: U32, +i: Nat, +s: Bool) -> Bool:
  match t:
    case Lf{+x, +k}:
      tr.agree(k, p, i) && X.ix.same(X.ix.side(k, i), s)
    case Br{+b, +j, l, r}:
      tr.all(l, p, i, s) && tr.all(r, p, i, s)

# t's branches testing bits from lo up, each below 32 and below its
# children's, every key below one alike below its bit and on its child's
# side at it; lo at most 32 at a leaf, so that a descent's fuel follows
# (33 steps from lo 0)
def tr.ok(t: Tr, +lo: Nat) -> Bool:
  match t:
    case Lf{+x, +k}:
      Nat.is_le(lo, 32n)
    case Br{+b, +i, +l, +r}:
      Nat.is_le(lo, i) && (Nat.is_lt(i, 32n) && (tr.all(l, tr.first(l), i, False{}) && (tr.all(r, tr.first(l), i, True{}) && (tr.ok(l, 1n+i) && tr.ok(r, 1n+i)))))

def ix.inv(I: Ix) -> Bool:
  match I:
    case Ept{}:
      True{}
    case Has{t}:
      tr.ok(t, 0n)

# The tree's nodes: its leaves, the cursors; its branches
def tr.leaves(t: Tr) -> List<&2, U32>:
  match t:
    case Lf{+x, +k}:
      [x]
    case Br{+b, +i, l, r}:
      List.append(&2, U32, tr.leaves(l), tr.leaves(r))

def tr.branches(t: Tr) -> List<&2, U32>:
  match t:
    case Lf{+x, +k}:
      []
    case Br{+b, +i, l, r}:
      Con{b, List.append(&2, U32, tr.branches(l), tr.branches(r))}

def ix.leaves(I: Ix) -> List<&2, U32>:
  match I:
    case Ept{}:
      []
    case Has{t}:
      tr.leaves(t)

def ix.branches(I: Ix) -> List<&2, U32>:
  match I:
    case Ept{}:
      []
    case Has{t}:
      tr.branches(t)
