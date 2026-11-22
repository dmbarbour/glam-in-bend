# A copy's index's proofs (glam/INDEX_LAWS.bend; the Cells plan's
# cells-freeze.sharing.cursors.index.laws).
#
# Lessons, beside docs/Proving.md's and glam/PROOF.bend's: a U32 is a
# Word(32n) of Bools, the lowest first, and its and, xor and shifts are
# structural on it, so that a bit fact is an induction on the word's
# width, generic in n (a word's head and tail as projections; Equal.cong
# through them for a constructor's injectivity), with no arithmetic and
# no bound of 2^32. The code's bit test (X.ix.side) unfolds to the low bit
# of a shift, which the zero word's lemmas reduce to the word's head. A
# header's encoding and decoding, divisions and shifts on a variable, are
# left to the checker's evaluation, case by case over the 32 bits a branch
# may test. A scan of bits that may stop (X.ix.crit) is followed with its
# test's Bool a parameter matched and the caller passing {==} for its
# equation, so that the recursion needs no step lemma.

import Base
import ./INDEX_LAWS.bend as Laws
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/kmodel.bend as KMd
import ./index.bend as X
import ./index_model.bend as IM
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import 0x8ae61ec3a6615abd35f196c07232ad28/string.bend as MS
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MN
import 0x8ae61ec3a6615abd35f196c07232ad28/u32.bend as MU
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/LAWS.bend as LA
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/PROOF.bend as LAP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_base.bend as LAB
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

# Bits
# ====

def low(+k: U32) -> Bool:
  U32.is_eq((k .&. 1 : U32), 1)

def zeros(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{False{}, zeros(p)}

def bool_and_false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def and_zeros(n: Nat, t: Word(n)) -> {Word.and(n, t, zeros(n)) == zeros(n) : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{b, r}:
          %Equal.sym(Word(p), Word.and(p, r, zeros(p)), zeros(p), and_zeros(p, r)) : {WCon{Bool.and(b, False{}), _} == WCon{False{}, zeros(p)} : Word(1n+p)}
          %Equal.sym(Bool, Bool.and(b, False{}), False{}, bool_and_false(b)) : {WCon{_, zeros(p)} == WCon{False{}, zeros(p)} : Word(1n+p)}
          {==}

def low_fin(h: Bool) -> {Cmp.is_eq(Word.cmp.fin(Bool.and(h, True{}), True{}, EQ{})) == h : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def low_con(h: Bool, t: Word(31n)) -> {low(U32{WCon{h, t}}) == h : Bool}:
  %Equal.sym(Word(31n), Word.and(31n, t, zeros(31n)), zeros(31n), and_zeros(31n, t)) : {Cmp.is_eq(Word.cmp.fin(Bool.and(h, True{}), True{}, Word.cmp(31n, _, zeros(31n)))) == h : Bool}
  low_fin(h)

# a word's head and tail
def wh(p: Nat, w: Word(1n+p)) -> Bool:
  match w:
    case WCon{b, t}:
      b

def wt(p: Nat, w: Word(1n+p)) -> Word(p):
  match w:
    case WCon{b, t}:
      t

# two words alike in head and tail are one
def wcon_eq(-p: Nat, b: Bool, c: Bool, s: Word(p), t: Word(p), hb: {b == c : Bool}, ht: {s == t : Word(p)}) -> {WCon{b, s} == WCon{c, t} : Word(1n+p)}:
  %ht : {WCon{b, s} == WCon{c, _} : Word(1n+p)}
  %hb : {WCon{b, s} == WCon{_, s} : Word(1n+p)}
  {==}

# shifting right pads a word's tail with a zero at the top: one tail, one
# padding
def pad_inj(+n: Nat, +s: Word(n), +t: Word(n), +e: {Word.shr.pad(n, s) == Word.shr.pad(n, t) : Word(1n+n)}) -> {s == t : Word(n)}:
  match n:
    case 0n:
      match s:
        case WNil{}:
          match t:
            case WNil{}:
              {==}
    case 1n+p:
      match s:
        case WCon{b, s2}:
          match t:
            case WCon{c, t2}:
              wcon_eq(p, b, c, s2, t2,
                Equal.cong(Word(2n+p), Bool, w => wh(1n+p, w), WCon{b, Word.shr.pad(p, s2)}, WCon{c, Word.shr.pad(p, t2)}, e),
                pad_inj(p, s2, t2, Equal.cong(Word(2n+p), Word(1n+p), w => wt(1n+p, w), WCon{b, Word.shr.pad(p, s2)}, WCon{c, Word.shr.pad(p, t2)}, e)))

def ext_fin(p: Bool, q: Bool, s: Word(31n), t: Word(31n), hb: {p == q : Bool}, ht: {s == t : Word(31n)}) -> {U32{WCon{p, s}} == U32{WCon{q, t}} : U32}:
  Equal.cong(Word(32n), U32, w => U32{w}, WCon{p, s}, WCon{q, t}, wcon_eq(31n, p, q, s, t, hb, ht))

def uw(x: U32) -> Word(32n):
  match x:
    case U32{w}:
      w

# a U32 is its low bit and its shift right
def ext_bits(+x: U32, +y: U32, hl: {low(x) == low(y) : Bool}, hs: {U32.shr(x) == U32.shr(y) : U32}) -> {x == y : U32}:
  match x:
    case U32{wx}:
      match wx:
        case WCon{p, s}:
          match y:
            case U32{wy}:
              match wy:
                case WCon{q, t}:
                  ext_fin(p, q, s, t,
                    Equal.trans(Bool, p, low(U32{WCon{p, s}}), q, Equal.sym(Bool, low(U32{WCon{p, s}}), p, low_con(p, s)),
                      Equal.trans(Bool, low(U32{WCon{p, s}}), low(U32{WCon{q, t}}), q, hl, low_con(q, t))),
                    pad_inj(31n, s, t, Equal.cong(U32, Word(32n), z => uw(z), U32{Word.shr.pad(31n, s)}, U32{Word.shr.pad(31n, t)}, hs)))

# Thirty-two shifts right leave nothing

def wshrn(+n: Nat, w: Word(n), k: Nat) -> Word(n):
  match k:
    case 0n:
      w
    case 1n+j:
      Word.shr(n, wshrn(n, w, j))

def u32_shrn(+w: Word(32n), +k: Nat) -> {U32.shrn(U32{w}, k) == U32{wshrn(32n, w, k)} : U32}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(U32, U32.shrn(U32{w}, j), U32{wshrn(32n, w, j)}, u32_shrn(w, j)) : {U32.shr(_) == U32{Word.shr(32n, wshrn(32n, w, j))} : U32}
      {==}

def shr_pad(+p: Nat, +t: Word(p)) -> {Word.shr(1n+p, Word.shr.pad(p, t)) == Word.shr.pad(p, Word.shr(p, t)) : Word(1n+p)}:
  match p:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+q:
      match t:
        case WCon{b, t2}:
          {==}

def wshrn_pad(+p: Nat, +t: Word(p), +k: Nat) -> {wshrn(1n+p, Word.shr.pad(p, t), k) == Word.shr.pad(p, wshrn(p, t, k)) : Word(1n+p)}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(Word(1n+p), wshrn(1n+p, Word.shr.pad(p, t), j), Word.shr.pad(p, wshrn(p, t, j)), wshrn_pad(p, t, j)) : {Word.shr(1n+p, _) == Word.shr.pad(p, Word.shr(p, wshrn(p, t, j))) : Word(1n+p)}
      shr_pad(p, wshrn(p, t, j))

def wshrn_in(+n: Nat, +w: Word(n), +k: Nat) -> {wshrn(n, w, 1n+k) == wshrn(n, Word.shr(n, w), k) : Word(n)}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(Word(n), wshrn(n, w, 1n+j), wshrn(n, Word.shr(n, w), j), wshrn_in(n, w, j)) : {Word.shr(n, _) == Word.shr(n, wshrn(n, Word.shr(n, w), j)) : Word(n)}
      {==}

def pad_zeros(+p: Nat) -> {Word.shr.pad(p, zeros(p)) == zeros(1n+p) : Word(1n+p)}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(Word(1n+q), Word.shr.pad(q, zeros(q)), zeros(1n+q), pad_zeros(q)) : {WCon{False{}, _} == zeros(2n+q) : Word(2n+q)}
      {==}

def wshrn_all(+n: Nat, +w: Word(n)) -> {wshrn(n, w, n) == zeros(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Equal.trans(Word(1n+p), wshrn(1n+p, WCon{b, t}, 1n+p), wshrn(1n+p, Word.shr.pad(p, t), p), zeros(1n+p), wshrn_in(1n+p, WCon{b, t}, p),
            Equal.trans(Word(1n+p), wshrn(1n+p, Word.shr.pad(p, t), p), Word.shr.pad(p, wshrn(p, t, p)), zeros(1n+p), wshrn_pad(p, t, p),
              Equal.trans(Word(1n+p), Word.shr.pad(p, wshrn(p, t, p)), Word.shr.pad(p, zeros(p)), zeros(1n+p),
                Equal.cong(Word(p), Word(1n+p), z => Word.shr.pad(p, z), wshrn(p, t, p), zeros(p), wshrn_all(p, t)), pad_zeros(p))))

def shr32(+x: U32) -> {U32.shrn(x, 32n) == 0 : U32}:
  match x:
    case U32{w}:
      Equal.trans(U32, U32.shrn(U32{w}, 32n), U32{wshrn(32n, w, 32n)}, 0, u32_shrn(w, 32n),
        Equal.cong(Word(32n), U32, z => U32{z}, wshrn(32n, w, 32n), zeros(32n), wshrn_all(32n, w)))

# The scan for the lowest bit two keys differ at

def side_low(+k: U32, +i: Nat) -> {X.ix.side(k, i) == low(U32.shrn(k, i)) : Bool}:
  {==}

def crit_stays(+f: Nat, +i: Nat, +a: U32, +b: U32) -> {X.ix.crit(f, X.Cr{i, False{}}, a, b) == X.Cr{i, False{}} : X.Cr}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

def same_eq(+p: Bool, +q: Bool, h: {X.ix.same(p, q) == True{} : Bool}) -> {p == q : Bool}:
  match p:
    case True{}:
      Equal.sym(Bool, q, True{}, h)
    case False{}:
      match q:
        case True{}:
          Empty.absurd({False{} == True{} : Bool}, MB.false_ne_true()(h))
        case False{}:
          {==}

# a scan run to its fuel f from bit i finding no difference: the keys
# shifted by i are one, given that shifted by f + i they are
def ext_go(+f: Nat, +i: Nat, +a: U32, +b: U32, +eq: Bool, +heq: {X.ix.same(X.ix.side(a, i), X.ix.side(b, i)) == eq : Bool},
  +he: {U32.shrn(a, Nat.add(f, i)) == U32.shrn(b, Nat.add(f, i)) : U32},
  +hg: {IM.cr.go(X.ix.crit(f, X.Cr{i, True{}}, a, b)) == True{} : Bool}) -> {U32.shrn(a, i) == U32.shrn(b, i) : U32}:
  match f:
    case 0n:
      he
    case 1n+g:
      match eq:
        case True{}:
          ext_bits(U32.shrn(a, i), U32.shrn(b, i), same_eq(X.ix.side(a, i), X.ix.side(b, i), heq),
            ext_go(g, 1n+i, a, b, X.ix.same(X.ix.side(a, 1n+i), X.ix.side(b, 1n+i)), {==},
              ME.subst(Nat, z => {U32.shrn(a, z) == U32.shrn(b, z) : U32}, 1n+Nat.add(g, i), Nat.add(g, 1n+i),
                Equal.sym(Nat, Nat.add(g, 1n+i), 1n+Nat.add(g, i), MN.add_succ(g, i)), he),
              ME.subst(Bool, z => {IM.cr.go(X.ix.crit(g, X.cr.k(z, i), a, b)) == True{} : Bool}, X.ix.same(X.ix.side(a, i), X.ix.side(b, i)), True{}, heq, hg)))
        case False{}:
          Empty.absurd({U32.shrn(a, i) == U32.shrn(b, i) : U32},
            MB.false_ne_true()(Equal.trans(Bool, False{}, IM.cr.go(X.ix.crit(g, X.cr.k(X.ix.same(X.ix.side(a, i), X.ix.side(b, i)), i), a, b)), True{},
              ME.subst(Bool, z => {False{} == IM.cr.go(X.ix.crit(g, X.cr.k(z, i), a, b)) : Bool}, False{}, X.ix.same(X.ix.side(a, i), X.ix.side(b, i)), Equal.sym(Bool, X.ix.same(X.ix.side(a, i), X.ix.side(b, i)), False{}, heq),
                Equal.cong(X.Cr, Bool, z => IM.cr.go(z), X.Cr{i, False{}}, X.ix.crit(g, X.Cr{i, False{}}, a, b), Equal.sym(X.Cr, X.ix.crit(g, X.Cr{i, False{}}, a, b), X.Cr{i, False{}}, crit_stays(g, i, a, b)))),
              hg)))

# U32.is_eq(x, x)
def is_eq_self(+x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  Equal.trans(Bool, U32.is_eq(x, x), Nat.is_eq(U32.to_nat(x), U32.to_nat(x)), True{}, MU.u32_is_eq_to_nat(x, x), MN.is_eq_refl(U32.to_nat(x)))

def ne_found.k(+a: U32, +b: U32, +g: Bool, +hg: {IM.cr.go(X.ix.crit(32n, X.Cr{0n, True{}}, a, b)) == g : Bool}, +hne: {U32.is_eq(a, b) == False{} : Bool}) -> {IM.cr.go(X.ix.crit(32n, X.Cr{0n, True{}}, a, b)) == False{} : Bool}:
  match g:
    case False{}:
      hg
    case True{}:
      Empty.absurd({IM.cr.go(X.ix.crit(32n, X.Cr{0n, True{}}, a, b)) == False{} : Bool},
        MB.false_ne_true()(Equal.trans(Bool, False{}, U32.is_eq(a, a), True{},
          Equal.sym(Bool, U32.is_eq(a, a), False{},
            ME.subst(U32, z => {U32.is_eq(a, z) == False{} : Bool}, b, a,
              Equal.sym(U32, a, b, ext_go(32n, 0n, a, b, X.ix.same(X.ix.side(a, 0n), X.ix.side(b, 0n)), {==},
                Equal.trans(U32, U32.shrn(a, 32n), 0, U32.shrn(b, 32n), shr32(a), Equal.sym(U32, U32.shrn(b, 32n), 0, shr32(b))), hg)),
              hne)),
          is_eq_self(a))))

# LAW-to-be: two keys unequal, the scan of their 32 bits from the lowest
# stops at a bit they differ at
def ne_found(+a: U32, +b: U32, +hne: {U32.is_eq(a, b) == False{} : Bool}) -> {IM.cr.go(X.ix.crit(32n, X.Cr{0n, True{}}, a, b)) == False{} : Bool}:
  ne_found.k(a, b, IM.cr.go(X.ix.crit(32n, X.Cr{0n, True{}}, a, b)), {==}, hne)

def Laws.ne_found(a, b, hne):
  ne_found(a, b, hne)


# Conjunctions' parts
# ===================

def and_l(+a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  MB.eq_true_of_and_left(a, b, h)

def and_r(+a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  MB.eq_true_of_and_right(a, b, h)

# Order on Nats, as Bools
# =======================

def zero_le_b(+n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def le_trans_b(+a: Nat, +b: Nat, +c: Nat, +hab: {Nat.is_le(a, b) == True{} : Bool}, +hbc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a:
    case 0n:
      zero_le_b(c)
    case 1n+(+ap):
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, MB.false_ne_true()(hab))
        case 1n+(+bp):
          match c:
            case 0n:
              Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, MB.false_ne_true()(hbc))
            case 1n+(+cp):
              le_trans_b(ap, bp, cp, hab, hbc)

def lt_le(+i: Nat, +n: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {Nat.is_le(1n+i, n) == True{} : Bool}:
  match i:
    case 0n:
      match n:
        case 0n:
          Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, MB.false_ne_true()(h))
        case 1n+(+m):
          zero_le_b(m)
    case 1n+(+ip):
      match n:
        case 0n:
          Empty.absurd({Nat.is_le(2n+ip, 0n) == True{} : Bool}, MB.false_ne_true()(h))
        case 1n+(+m):
          lt_le(ip, m, h)

def le_add_l(+g: Nat, +x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(g, x), Nat.add(g, y)) == True{} : Bool}:
  match g:
    case 0n:
      h
    case 1n+(+q):
      le_add_l(q, x, y, h)

def le_succ_b(+i: Nat) -> {Nat.is_le(i, 1n+i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+(+j):
      le_succ_b(j)

# a branch's fuel: 33 bits from lo, the children's from i + 1, one step
# spent
def fuel_down(+g: Nat, +lo: Nat, +i: Nat, +hfu: {Nat.is_le(33n, Nat.add(1n+g, lo)) == True{} : Bool}, +hli: {Nat.is_le(lo, i) == True{} : Bool}) ->
  {Nat.is_le(33n, Nat.add(g, 1n+i)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(g, 1n+i), 1n+Nat.add(g, i), MN.add_succ(g, i)) : {Nat.is_le(33n, _) == True{} : Bool}
  le_trans_b(33n, 1n+Nat.add(g, lo), 1n+Nat.add(g, i), hfu, le_add_l(g, lo, i, hli))

def not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MB.false_ne_true()(h))
    case False{}:
      {==}

# The heap's words
# ================

# a word of the view, as a read gives it
def wd(+t0: LAT.Tree<U32>, +d: Nat, +i: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
  {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, i) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), i)) : U32}:
  %LA.get_view(U32, LAT.fromT(U32, t0), d, i, hft, hd32) : {KMd.word.m(_) == Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), i)) : U32}
  {==}

# a read hands the heap back
def rd_eq(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +i: U32) -> {P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, i) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), i))) : P.H & U32}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), i), (LAT.fromT(U32, t0), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), i))), LA.get_pair(U32, LAT.fromT(U32, t0), i)) :
    {P.rd.fin(KM.m_get.fin(_), a) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), i))) : P.H & U32}
  {==}

# Find
# ====

# a descent stopped stays stopped, its heap as it was
def ds_stays(+f: Nat, -h: P.H, +x: U32, +k: U32) -> {X.ds.run(f, X.Ds{h, x, False{}}, k) == X.Ds{h, x, False{}} : X.Ds}:
  match f:
    case 0n:
      {==}
    case 1n+(+g):
      {==}

def found_hit(+b: Bool, -h: P.H, +x: U32) -> {X.ix.found.s(b, h, x) == (h, IM.mb.hit(b, x)) : P.H & Maybe<&2, U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a branch at bit i: the descent goes on to the child k's bit gives, the
# found as the model's look below it
def dsc.k(+sd: Bool, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +b: U32, +i: Nat, +k: U32, +g: Nat, +l: IM.Tr, +r: IM.Tr, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +ihl: {X.ix.found(X.ds.run(g, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), True{}}, k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.look(l, k)) : P.H & Maybe<&2, U32>},
  +ihr: {X.ix.found(X.ds.run(g, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), True{}}, k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.look(r, k)) : P.H & Maybe<&2, U32>}) ->
  {X.ix.found(X.ds.run(g, X.ds.c(P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.kid(X.ix.side(k, i), b))), k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k))) : P.H & Maybe<&2, U32>}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) :
        {X.ix.found(X.ds.run(g, X.ds.c(P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.kid(_, b))), k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.pick(_, IM.tr.look(r, k), IM.tr.look(l, k))) : P.H & Maybe<&2, U32>}
      %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 3 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 3 : U32)))), rd_eq(t0, a, (b + 3 : U32))) :
        {X.ix.found(X.ds.run(g, X.ds.c(_), k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.look(r, k)) : P.H & Maybe<&2, U32>}
      %wd(t0, d, (b + 3 : U32), hft, hd32) : {X.ix.found(X.ds.run(g, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, True{}}, k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.look(r, k)) : P.H & Maybe<&2, U32>}
      ihr
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) :
        {X.ix.found(X.ds.run(g, X.ds.c(P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.kid(_, b))), k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.pick(_, IM.tr.look(r, k), IM.tr.look(l, k))) : P.H & Maybe<&2, U32>}
      %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 2 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 2 : U32)))), rd_eq(t0, a, (b + 2 : U32))) :
        {X.ix.found(X.ds.run(g, X.ds.c(_), k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.look(l, k)) : P.H & Maybe<&2, U32>}
      %wd(t0, d, (b + 2 : U32), hft, hd32) : {X.ix.found(X.ds.run(g, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, True{}}, k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.look(l, k)) : P.H & Maybe<&2, U32>}
      ihl

# a descent from the pointer p to a tree the words realize, on its
# invariant from bit lo, with fuel f that lo leaves enough (33 in all),
# gives the model's look, the heap as it was
def dsc(T: IM.Tr, f: Nat, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +k: U32, +p: U32, +lo: Nat,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, T, p, s) == True{} : Bool}, +hok: {IM.tr.ok(T, lo) == True{} : Bool},
  +hfu: {Nat.is_le(33n, Nat.add(f, lo)) == True{} : Bool}) ->
  {X.ix.found(X.ds.run(f, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, p, True{}}, k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.look(T, k)) : P.H & Maybe<&2, U32>}:
  match T:
    case IM.Lf{+x, +kk}:
      match f:
        case 0n:
          Empty.absurd({X.ix.found(X.ds.run(0n, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, p, True{}}, k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.look(IM.Lf{x, kk}, k)) : P.H & Maybe<&2, U32>},
            MB.false_ne_true()(le_trans_b(33n, lo, 32n, hfu, hok)))
        case 1n+(+g):
          +h1 = and_r(U32.is_eq(p, x), Bool.not(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x))) && (U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), kk) && U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 3 : U32)), s)), hre)
          +h2 = and_r(Bool.not(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x))), U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), kk) && U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 3 : U32)), s), h1)
          +hpx = MS.u32_eq_of_is_eq(p, x, and_l(U32.is_eq(p, x), Bool.not(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x))) && (U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), kk) && U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 3 : U32)), s)), hre))
          +hnb = not_true(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)), and_l(Bool.not(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x))), U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), kk) && U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 3 : U32)), s), h1))
          +hk2 = MS.u32_eq_of_is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), kk, and_l(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), kk), U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 3 : U32)), s), h2))
          %Equal.sym(U32, p, x, hpx) : {X.ix.found(X.ds.run(1n+g, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, True{}}, k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.hit(U32.is_eq(kk, k), x)) : P.H & Maybe<&2, U32>}
          %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, x), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), x))), rd_eq(t0, a, x)) :
            {X.ix.found(X.ds.run(g, X.ds.hd(_, x, k), k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.hit(U32.is_eq(kk, k), x)) : P.H & Maybe<&2, U32>}
          %wd(t0, d, x, hft, hd32) : {X.ix.found(X.ds.run(g, X.ds.k(X.ix.branch(_), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, x, X.ix.bitof(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), x))), k), k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.hit(U32.is_eq(kk, k), x)) : P.H & Maybe<&2, U32>}
          %Equal.sym(Bool, X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)), False{}, hnb) :
            {X.ix.found(X.ds.run(g, X.ds.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, x, X.ix.bitof(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), x))), k), k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.hit(U32.is_eq(kk, k), x)) : P.H & Maybe<&2, U32>}
          %Equal.sym(X.Ds, X.ds.run(g, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, x, False{}}, k), X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, x, False{}}, ds_stays(g, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, x, k)) :
            {X.ix.found(_, k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.hit(U32.is_eq(kk, k), x)) : P.H & Maybe<&2, U32>}
          %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (x + 2 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32)))), rd_eq(t0, a, (x + 2 : U32))) :
            {X.ix.found.k(_, x, k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.hit(U32.is_eq(kk, k), x)) : P.H & Maybe<&2, U32>}
          %wd(t0, d, (x + 2 : U32), hft, hd32) : {X.ix.found.s(U32.is_eq(_, k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, x) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.hit(U32.is_eq(kk, k), x)) : P.H & Maybe<&2, U32>}
          %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), kk, hk2) : {X.ix.found.s(U32.is_eq(_, k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, x) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.hit(U32.is_eq(kk, k), x)) : P.H & Maybe<&2, U32>}
          found_hit(U32.is_eq(kk, k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, x)
    case IM.Br{+b, +i, +l, +r}:
      match f:
        case 0n:
          Empty.absurd({X.ix.found(X.ds.run(0n, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, p, True{}}, k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.look(IM.Br{b, i, l, r}, k)) : P.H & Maybe<&2, U32>},
            MB.false_ne_true()(le_trans_b(33n, 1n+i, 32n, le_trans_b(33n, lo, 1n+i, hfu, le_trans_b(lo, i, 1n+i, and_l(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok), le_succ_b(i))), lt_le(i, 32n, and_l(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok))))))
        case 1n+(+g):
          +r1 = and_r(U32.is_eq(p, b), X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s))), hre)
          +r2 = and_r(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s)), r1)
          +r3 = and_r(Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r2)
          +o1 = and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok)
          +o2 = and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i))), o1)
          +o3 = and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)), o2)
          +o4 = and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i), o3)
          +hli = and_l(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok)
          +hi32 = and_l(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i))), o1)
          +hpb = MS.u32_eq_of_is_eq(p, b, and_l(U32.is_eq(p, b), X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s))), hre))
          +hbr = and_l(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s)), r1)
          +hbi = MN.eq_of_is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i, and_l(Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r2))
          +hfg = fuel_down(g, lo, i, hfu, hli)
          %Equal.sym(U32, p, b, hpb) : {X.ix.found(X.ds.run(1n+g, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, True{}}, k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k))) : P.H & Maybe<&2, U32>}
          %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, b), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), b))), rd_eq(t0, a, b)) :
            {X.ix.found(X.ds.run(g, X.ds.hd(_, b, k), k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k))) : P.H & Maybe<&2, U32>}
          %wd(t0, d, b, hft, hd32) : {X.ix.found(X.ds.run(g, X.ds.k(X.ix.branch(_), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, b, X.ix.bitof(_), k), k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k))) : P.H & Maybe<&2, U32>}
          %Equal.sym(Bool, X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), True{}, hbr) :
            {X.ix.found(X.ds.run(g, X.ds.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, b, X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), k), k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k))) : P.H & Maybe<&2, U32>}
          %Equal.sym(Nat, X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i, hbi) :
            {X.ix.found(X.ds.run(g, X.ds.k(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, b, _, k), k), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k))) : P.H & Maybe<&2, U32>}
          dsc.k(X.ix.side(k, i), t0, a, d, b, i, k, g, l, r, {==}, hft, hd32,
            dsc(l, g, t0, a, d, s, k, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), 1n+i, hft, hd32, and_l(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r3), and_l(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), o4), hfg),
            dsc(r, g, t0, a, d, s, k, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), 1n+i, hft, hd32, and_r(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r3), and_r(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), o4), hfg))

def find_tree.k(I: IM.Ix, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +k: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, I) == True{} : Bool}, +hi: {IM.ix.inv(I) == True{} : Bool}) ->
  {X.ix.find(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.ix.look(I, k)) : P.H & Maybe<&2, U32>}:
  match I:
    case IM.Ept{}:
      %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (s + 3 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32)))), rd_eq(t0, a, (s + 3 : U32))) : {X.ix.find.r(_, s, k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, None{}) : P.H & Maybe<&2, U32>}
      %wd(t0, d, (s + 3 : U32), hft, hd32) : {X.ix.find.k(U32.is_eq(_, s), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, None{}) : P.H & Maybe<&2, U32>}
      %Equal.sym(Bool, U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), True{}, hre) : {X.ix.find.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, None{}) : P.H & Maybe<&2, U32>}
      {==}
    case IM.Has{+t}:
      +hne = not_true(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), and_l(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, t, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre))
      +hrt = and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, t, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre)
      %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (s + 3 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32)))), rd_eq(t0, a, (s + 3 : U32))) : {X.ix.find.r(_, s, k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.look(t, k)) : P.H & Maybe<&2, U32>}
      %wd(t0, d, (s + 3 : U32), hft, hd32) : {X.ix.find.k(U32.is_eq(_, s), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.look(t, k)) : P.H & Maybe<&2, U32>}
      %Equal.sym(Bool, U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), False{}, hne) : {X.ix.find.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), k) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.look(t, k)) : P.H & Maybe<&2, U32>}
      dsc(t, 33n, t0, a, d, s, k, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), 0n, hft, hd32, hrt, hi, {==})

def find_tree.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +k: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}, hi: {IM.ix.inv(I) == True{} : Bool}, m: LAT.Mirror(U32, w)) ->
  {X.ix.find(P.H{KM.MG{w}, a}, s, k) == (P.H{KM.MG{w}, a}, IM.ix.look(I, k)) : P.H & Maybe<&2, U32>}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {IM.ix.real(AD.view(U32, q), d, s, I) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e), hr)
  %e : {X.ix.find(P.H{KM.MG{_}, a}, s, k) == (P.H{KM.MG{_}, a}, IM.ix.look(I, k)) : P.H & Maybe<&2, U32>}
  find_tree.k(I, t0, a, d, s, k, hft, hd32, hrt, hi)

def Laws.find_tree(w, a, d, s, I, k, hf, hd32, hr, hi):
  find_tree.m(w, a, d, s, I, k, hf, hd32, hr, hi, LAT.mirror(U32, w))

# Lookups
# =======

# a leaf on side s at bit i, k on the other: not k's
def at_none.lf(+x: U32, +kk: U32, +i: Nat, +s: Bool, +k: U32, +e: Bool, +he: {U32.is_eq(kk, k) == e : Bool},
  +ha: {X.ix.same(X.ix.side(kk, i), s) == True{} : Bool}, +hk: {X.ix.same(X.ix.side(k, i), s) == False{} : Bool}) -> {IM.mb.hit(U32.is_eq(kk, k), x) == None{} : Maybe<&2, U32>}:
  match e:
    case False{}:
      %Equal.sym(Bool, U32.is_eq(kk, k), False{}, he) : {IM.mb.hit(_, x) == None{} : Maybe<&2, U32>}
      {==}
    case True{}:
      Empty.absurd({IM.mb.hit(U32.is_eq(kk, k), x) == None{} : Maybe<&2, U32>},
        MB.false_ne_true()(Equal.trans(Bool, False{}, X.ix.same(X.ix.side(k, i), s), True{},
          Equal.sym(Bool, X.ix.same(X.ix.side(k, i), s), False{}, hk),
          ME.subst(U32, z => {X.ix.same(X.ix.side(z, i), s) == True{} : Bool}, kk, k, MS.u32_eq_of_is_eq(kk, k, he), ha))))

# no key of t is k: every key of t on side s at bit i, k on the other
def at_none(t: IM.Tr, +p: U32, +i: Nat, +s: Bool, +k: U32, +ha: {IM.tr.all(t, p, i, s) == True{} : Bool}, +hk: {X.ix.same(X.ix.side(k, i), s) == False{} : Bool}) -> {IM.tr.at(t, k) == None{} : Maybe<&2, U32>}:
  match t:
    case IM.Lf{+x, +kk}:
      at_none.lf(x, kk, i, s, k, U32.is_eq(kk, k), {==}, and_r(IM.tr.agree(kk, p, i), X.ix.same(X.ix.side(kk, i), s), ha), hk)
    case IM.Br{+b, +j, +l, +r}:
      %Equal.sym(Maybe<&2, U32>, IM.tr.at(l, k), None{}, at_none(l, p, i, s, k, and_l(IM.tr.all(l, p, i, s), IM.tr.all(r, p, i, s), ha), hk)) :
        {IM.mb.or(_, IM.tr.at(r, k)) == None{} : Maybe<&2, U32>}
      at_none(r, p, i, s, k, and_r(IM.tr.all(l, p, i, s), IM.tr.all(r, p, i, s), ha), hk)

def or_none(+m: Maybe<&2, U32>) -> {IM.mb.or(m, None{}) == m : Maybe<&2, U32>}:
  match m:
    case Some{+x}:
      {==}
    case None{}:
      {==}

# a branch at bit i: the descent's child the side k's bit gives, the
# other child holding no key k
def look_at.k(+sd: Bool, +k: U32, +i: Nat, +p: U32, +l: IM.Tr, +r: IM.Tr, +hsd: {X.ix.side(k, i) == sd : Bool},
  +ihl: {IM.tr.look(l, k) == IM.tr.at(l, k) : Maybe<&2, U32>}, +ihr: {IM.tr.look(r, k) == IM.tr.at(r, k) : Maybe<&2, U32>},
  +hal: {IM.tr.all(l, p, i, False{}) == True{} : Bool}, +har: {IM.tr.all(r, p, i, True{}) == True{} : Bool}) ->
  {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == IM.mb.or(IM.tr.at(l, k), IM.tr.at(r, k)) : Maybe<&2, U32>}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {IM.mb.pick(_, IM.tr.look(r, k), IM.tr.look(l, k)) == IM.mb.or(IM.tr.at(l, k), IM.tr.at(r, k)) : Maybe<&2, U32>}
      %Equal.sym(Maybe<&2, U32>, IM.tr.at(l, k), None{}, at_none(l, p, i, False{}, k, hal,
        ME.subst(Bool, z => {X.ix.same(z, False{}) == False{} : Bool}, True{}, X.ix.side(k, i), Equal.sym(Bool, X.ix.side(k, i), True{}, hsd), {==}))) :
        {IM.tr.look(r, k) == IM.mb.or(_, IM.tr.at(r, k)) : Maybe<&2, U32>}
      ihr
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {IM.mb.pick(_, IM.tr.look(r, k), IM.tr.look(l, k)) == IM.mb.or(IM.tr.at(l, k), IM.tr.at(r, k)) : Maybe<&2, U32>}
      %Equal.sym(Maybe<&2, U32>, IM.tr.at(r, k), None{}, at_none(r, p, i, True{}, k, har,
        ME.subst(Bool, z => {X.ix.same(z, True{}) == False{} : Bool}, False{}, X.ix.side(k, i), Equal.sym(Bool, X.ix.side(k, i), False{}, hsd), {==}))) :
        {IM.tr.look(l, k) == IM.mb.or(IM.tr.at(l, k), _) : Maybe<&2, U32>}
      %Equal.sym(Maybe<&2, U32>, IM.mb.or(IM.tr.at(l, k), None{}), IM.tr.at(l, k), or_none(IM.tr.at(l, k))) : {IM.tr.look(l, k) == _ : Maybe<&2, U32>}
      ihl

def look_at.t(t: IM.Tr, +lo: Nat, +k: U32, +hok: {IM.tr.ok(t, lo) == True{} : Bool}) -> {IM.tr.look(t, k) == IM.tr.at(t, k) : Maybe<&2, U32>}:
  match t:
    case IM.Lf{+x, +kk}:
      {==}
    case IM.Br{+b, +i, +l, +r}:
      +h1 = and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok)
      +h2 = and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i))), h1)
      +h3 = and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)), h2)
      +h4 = and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i), h3)
      look_at.k(X.ix.side(k, i), k, i, IM.tr.first(l), l, r, {==},
        look_at.t(l, 1n+i, k, and_l(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), h4)),
        look_at.t(r, 1n+i, k, and_r(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), h4)),
        and_l(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)), h2),
        and_l(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i), h3))

def Laws.look_at(I, k, hi):
  match I:
    case IM.Ept{}:
      {==}
    case IM.Has{+t}:
      look_at.t(t, 0n, k, hi)
