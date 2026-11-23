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
#
# More, from the tree's laws (find, removal, insert):
# - `%e : {M}` with e: A == B turns a goal in B into one in A; to take a
#   written read back to the plain one, state the lemma plain == written.
# - No match may follow a let or a rewrite, in a proof or in code; a let
#   may not bind a call's result in code (a helper destructures its
#   parameter); match the Bool first, then rewrite and bind in each case.
# - A definition used above its own fails at the call, with no message:
#   keep helpers above their users (and_l above dsc cost an hour).
# - Arguments pass unchanged, left to right, until the one that shrinks:
#   a tree before the pointer that follows it (tr.real(v, d, t, p, s)).
# - A value used twice must be `+`, its type Data (a model tree, X.Cr); a
#   function premise cannot be `+`, so it is applied once.
# - A wrapper of a hub lemma keeps the hub's erasure (and_l's and and_r's
#   second Bool `-`); a relevant one fails at its callers.
# - A comparison of a Nat stuck on a variable (is_lt(32 + c, 32)) needs
#   one more match before it reduces.
# - An induction hypothesis whose premises hold only on one side (the
#   cursor's way) is passed as a function of them; one whose premises hold
#   on both is computed for both children, eagerly, and needs no function.
# - A long conjunction is built by and_intro, each part shown alone,
#   rather than rewritten under one long motive; the realization after a
#   step names the words written as parameters tied to the model by
#   equations, so that the view's term stays one of variables.
# - The mutants' runner matches whole lines.
# - An array is not Data: a lemma over a write chain takes the mirror's
#   tree (+t0, its words LAT.fromT(U32, t0) and writes on them as terms)
#   or the words' view (a List, Data), and turns one into the other by
#   LA.set_view; an erased array (-A) may not be passed at all, a plain
#   one only once. A list's tail passed to and_intro twice wants `+` too.
# - The free list's round trip (a node freed is the next taken, its head
#   never 0: fl_idx, fl_nz) holds of every word, by its bits alone: r >> 2
#   computes to a padded word, x + 1 - 1 is an induction on the carries,
#   << 2 of a padded word is the word below two zeros, and a mask with all
#   ones leaves a word as it was. No 2^32 enters, whose unary unfolding
#   the checker cannot afford.
# - About half of this file was written by authoring aids under
#   results/index_bits/ (gen_*.py, out of git): text written once,
#   kept by hand since; not generated sources.

import Base
import ./INDEX_LAWS.bend as Laws
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/kmodel.bend as KMd
import ./index.bend as X
import ./index_model.bend as IM
import ./ring_model.bend as RG
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import 0x8ae61ec3a6615abd35f196c07232ad28/string.bend as MS
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MN
import 0x8ae61ec3a6615abd35f196c07232ad28/u32.bend as MU
import 0x8ae61ec3a6615abd35f196c07232ad28/list.bend as ML
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

# Writes on the view
# ==================

# a word of a view not written reads as before (stated plain, then
# written, so that a rewrite by it takes a written view's read back)
def wl_ne(+v: List<&2, U32>, +d: Nat, +j: U32, +i: U32, +val: U32, +h: {Nat.is_eq(AD.slot(j, d), AD.slot(i, d)) == False{} : Bool}) ->
  {KMd.word(v, d, i) == KMd.word(List.set(&2, U32, v, AD.slot(j, d), val), d, i) : U32}:
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, AD.slot(j, d), val), AD.slot(i, d)), List.get(&2, U32, v, AD.slot(i, d)), LAB.get_set_ne(U32, v, AD.slot(j, d), AD.slot(i, d), val, h)) :
    {KMd.word(v, d, i) == KMd.word.m(_) : U32}
  {==}

# the word written reads the value written, where the view holds a word
def wl_eq(+v: List<&2, U32>, +d: Nat, +j: U32, +val: U32, +q: U32, +h: {List.get(&2, U32, v, AD.slot(j, d)) == Some{q} : Maybe<&2, U32>}) ->
  {KMd.word(List.set(&2, U32, v, AD.slot(j, d), val), d, j) == val : U32}:
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, AD.slot(j, d), val), AD.slot(j, d)), Maybe.map(&2, U32, U32, y => val, List.get(&2, U32, v, AD.slot(j, d))), ML.get_set_self(&2, U32, v, AD.slot(j, d), val)) :
    {KMd.word.m(_) == val : U32}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, v, AD.slot(j, d)), Some{q}, h) : {KMd.word.m(Maybe.map(&2, U32, U32, y => val, _)) == val : U32}
  {==}

# word j off node x's words: each of x's words' slots, written j's not
def offk(+a: Nat, +b: Nat, +h: {Bool.not(Nat.is_eq(a, b)) == True{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  %MN.is_eq_comm(a, b) : {_ == False{} : Bool}
  not_true(Nat.is_eq(a, b), h)

def off0(+x: U32, +d: Nat, +j: U32, +h: {KMd.off.words(KMd.nw(x), d, j) == True{} : Bool}) -> {Nat.is_eq(AD.slot(j, d), AD.slot(x, d)) == False{} : Bool}:
  offk(AD.slot(x, d), AD.slot(j, d), and_l(Bool.not(Nat.is_eq(AD.slot(x, d), AD.slot(j, d))), KMd.off.words([(x + 1 : U32), (x + 2 : U32), (x + 3 : U32)], d, j), h))

def off1(+x: U32, +d: Nat, +j: U32, +h: {KMd.off.words(KMd.nw(x), d, j) == True{} : Bool}) -> {Nat.is_eq(AD.slot(j, d), AD.slot((x + 1 : U32), d)) == False{} : Bool}:
  offk(AD.slot((x + 1 : U32), d), AD.slot(j, d), and_l(Bool.not(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(j, d))), KMd.off.words([(x + 2 : U32), (x + 3 : U32)], d, j),
    and_r(Bool.not(Nat.is_eq(AD.slot(x, d), AD.slot(j, d))), KMd.off.words([(x + 1 : U32), (x + 2 : U32), (x + 3 : U32)], d, j), h)))

def off23(+x: U32, +d: Nat, +j: U32, +h: {KMd.off.words(KMd.nw(x), d, j) == True{} : Bool}) -> {KMd.off.words([(x + 2 : U32), (x + 3 : U32)], d, j) == True{} : Bool}:
  and_r(Bool.not(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(j, d))), KMd.off.words([(x + 2 : U32), (x + 3 : U32)], d, j),
    and_r(Bool.not(Nat.is_eq(AD.slot(x, d), AD.slot(j, d))), KMd.off.words([(x + 1 : U32), (x + 2 : U32), (x + 3 : U32)], d, j), h))

def off2(+x: U32, +d: Nat, +j: U32, +h: {KMd.off.words(KMd.nw(x), d, j) == True{} : Bool}) -> {Nat.is_eq(AD.slot(j, d), AD.slot((x + 2 : U32), d)) == False{} : Bool}:
  offk(AD.slot((x + 2 : U32), d), AD.slot(j, d), and_l(Bool.not(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(j, d))), KMd.off.words([(x + 3 : U32)], d, j), off23(x, d, j, h)))

def off3(+x: U32, +d: Nat, +j: U32, +h: {KMd.off.words(KMd.nw(x), d, j) == True{} : Bool}) -> {Nat.is_eq(AD.slot(j, d), AD.slot((x + 3 : U32), d)) == False{} : Bool}:
  offk(AD.slot((x + 3 : U32), d), AD.slot(j, d), and_l(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(j, d))), True{},
    and_r(Bool.not(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(j, d))), KMd.off.words([(x + 3 : U32)], d, j), off23(x, d, j, h))))

# a write off every node of a tree leaves its realization as it was
def real_set(T: IM.Tr, +v: List<&2, U32>, +d: Nat, +j: U32, +val: U32, +p: U32, +s: U32, +ho: {IM.tr.off(T, d, j) == True{} : Bool}) ->
  {IM.tr.real(v, d, T, p, s) == IM.tr.real(List.set(&2, U32, v, AD.slot(j, d), val), d, T, p, s) : Bool}:
  match T:
    case IM.Lf{+x, +kk}:
      %wl_ne(v, d, j, x, val, off0(x, d, j, ho)) :
        {IM.tr.real(v, d, IM.Lf{x, kk}, p, s) == (U32.is_eq(p, x) && (Bool.not(X.ix.branch(_)) && (U32.is_eq(KMd.word(List.set(&2, U32, v, AD.slot(j, d), val), d, (x + 2 : U32)), kk) && U32.is_eq(KMd.word(List.set(&2, U32, v, AD.slot(j, d), val), d, (x + 3 : U32)), s)))) : Bool}
      %wl_ne(v, d, j, (x + 2 : U32), val, off2(x, d, j, ho)) :
        {IM.tr.real(v, d, IM.Lf{x, kk}, p, s) == (U32.is_eq(p, x) && (Bool.not(X.ix.branch(KMd.word(v, d, x))) && (U32.is_eq(_, kk) && U32.is_eq(KMd.word(List.set(&2, U32, v, AD.slot(j, d), val), d, (x + 3 : U32)), s)))) : Bool}
      %wl_ne(v, d, j, (x + 3 : U32), val, off3(x, d, j, ho)) :
        {IM.tr.real(v, d, IM.Lf{x, kk}, p, s) == (U32.is_eq(p, x) && (Bool.not(X.ix.branch(KMd.word(v, d, x))) && (U32.is_eq(KMd.word(v, d, (x + 2 : U32)), kk) && U32.is_eq(_, s)))) : Bool}
      {==}
    case IM.Br{+b, +i, +l, +r}:
      +hb = and_l(KMd.off.words(KMd.nw(b), d, j), IM.tr.off(l, d, j) && IM.tr.off(r, d, j), ho)
      +hlr = and_r(KMd.off.words(KMd.nw(b), d, j), IM.tr.off(l, d, j) && IM.tr.off(r, d, j), ho)
      %wl_ne(v, d, j, b, val, off0(b, d, j, hb)) :
        {IM.tr.real(v, d, IM.Br{b, i, l, r}, p, s) == (U32.is_eq(p, b) && (X.ix.branch(_) && (Nat.is_eq(X.ix.bitof(_), i) && (IM.tr.real(List.set(&2, U32, v, AD.slot(j, d), val), d, l, KMd.word(List.set(&2, U32, v, AD.slot(j, d), val), d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, v, AD.slot(j, d), val), d, r, KMd.word(List.set(&2, U32, v, AD.slot(j, d), val), d, (b + 3 : U32)), s))))) : Bool}
      %wl_ne(v, d, j, (b + 2 : U32), val, off2(b, d, j, hb)) :
        {IM.tr.real(v, d, IM.Br{b, i, l, r}, p, s) == (U32.is_eq(p, b) && (X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(List.set(&2, U32, v, AD.slot(j, d), val), d, l, _, s) && IM.tr.real(List.set(&2, U32, v, AD.slot(j, d), val), d, r, KMd.word(List.set(&2, U32, v, AD.slot(j, d), val), d, (b + 3 : U32)), s))))) : Bool}
      %wl_ne(v, d, j, (b + 3 : U32), val, off3(b, d, j, hb)) :
        {IM.tr.real(v, d, IM.Br{b, i, l, r}, p, s) == (U32.is_eq(p, b) && (X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(List.set(&2, U32, v, AD.slot(j, d), val), d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, v, AD.slot(j, d), val), d, r, _, s))))) : Bool}
      %real_set(l, v, d, j, val, KMd.word(v, d, (b + 2 : U32)), s, and_l(IM.tr.off(l, d, j), IM.tr.off(r, d, j), hlr)) :
        {IM.tr.real(v, d, IM.Br{b, i, l, r}, p, s) == (U32.is_eq(p, b) && (X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (_ && IM.tr.real(List.set(&2, U32, v, AD.slot(j, d), val), d, r, KMd.word(v, d, (b + 3 : U32)), s))))) : Bool}
      %real_set(r, v, d, j, val, KMd.word(v, d, (b + 3 : U32)), s, and_r(IM.tr.off(l, d, j), IM.tr.off(r, d, j), hlr)) :
        {IM.tr.real(v, d, IM.Br{b, i, l, r}, p, s) == (U32.is_eq(p, b) && (X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && _)))) : Bool}
      {==}

# Removal
# =======

def cut.lo(c: IM.Cut) -> U32:
  match c:
    case IM.Cut{+loc, +par, +sib}:
      loc

def cut.pa(c: IM.Cut) -> U32:
  match c:
    case IM.Cut{+loc, +par, +sib}:
      par

def cut.si(c: IM.Cut) -> U32:
  match c:
    case IM.Cut{+loc, +par, +sib}:
      sib

def is_some(m: Maybe<&2, U32>) -> Bool:
  match m:
    case Some{+q}:
      True{}
    case None{}:
      False{}

def un_some(m: Maybe<&2, U32>, +z: U32) -> U32:
  match m:
    case Some{+q}:
      q
    case None{}:
      z

# a leaf's hit giving x: the leaf is x
def hit_some(+b: Bool, +y: U32, +x: U32, +h: {IM.mb.hit(b, y) == Some{x} : Maybe<&2, U32>}) -> {y == x : U32}:
  match b:
    case True{}:
      Equal.cong(Maybe<&2, U32>, U32, m => un_some(m, y), Some{y}, Some{x}, h)
    case False{}:
      Empty.absurd({y == x : U32}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, m => is_some(m), None{}, Some{x}, h)))

# a realized tree's pointer is its root's address
def real_addr(T: IM.Tr, +v: List<&2, U32>, +d: Nat, +p: U32, +s: U32, +h: {IM.tr.real(v, d, T, p, s) == True{} : Bool}) -> {p == IM.tr.addr(T) : U32}:
  match T:
    case IM.Lf{+x, +kk}:
      MS.u32_eq_of_is_eq(p, x, and_l(U32.is_eq(p, x), Bool.not(X.ix.branch(KMd.word(v, d, x))) && (U32.is_eq(KMd.word(v, d, (x + 2 : U32)), kk) && U32.is_eq(KMd.word(v, d, (x + 3 : U32)), s)), h))
    case IM.Br{+b, +i, +l, +r}:
      MS.u32_eq_of_is_eq(p, b, and_l(U32.is_eq(p, b), X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s))), h))

def rm_stays(+f: Nat, -h: P.H, +loc: U32, +cur: U32, +k: U32, +x: U32) -> {X.rm.run(f, X.Rm{h, loc, cur, False{}}, k, x) == X.Rm{h, loc, cur, False{}} : X.Rm}:
  match f:
    case 0n:
      {==}
    case 1n+(+g):
      {==}

# the child on the key's side, its address tested against x: x there,
# its sibling written where loc points and the branch b freed; else on
# down from the child, as the model's cut follows
def rmA.h(+hit: Bool, +sd: Bool, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +b: U32, +k: U32, +x: U32, +g: Nat, +loc: U32, +l: IM.Tr, +r: IM.Tr, +s: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hhit: {U32.is_eq(IM.tr.addr(IM.pick.t(sd, r, l)), x) == hit : Bool},
  +hq: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(sd, b)) == IM.tr.addr(IM.pick.t(sd, r, l)) : U32},
  +hq2: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(Bool.not(sd), b)) == IM.tr.addr(IM.pick.t(sd, l, r)) : U32},
  ih: {U32.is_eq(IM.tr.addr(IM.pick.t(sd, r, l)), x) == False{} : Bool} -> {X.rm.h(X.rm.run(g, X.Rm{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.kid(sd, b), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(sd, b)), True{}}, k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b))), cut.si(IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b)))), cut.pa(IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b)))) : P.H}) ->
  {X.rm.h(X.rm.run(g, X.rm.child(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(sd, b)), x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, sd, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(sd, b))), k, x)) ==
    P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.k.of(U32.is_eq(IM.tr.addr(IM.pick.t(sd, r, l)), x), b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b)))), cut.si(IM.cut.k.of(U32.is_eq(IM.tr.addr(IM.pick.t(sd, r, l)), x), b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b))))), cut.pa(IM.cut.k.of(U32.is_eq(IM.tr.addr(IM.pick.t(sd, r, l)), x), b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b))))) : P.H}:
  match hit:
    case True{}:
      %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(sd, b)), IM.tr.addr(IM.pick.t(sd, r, l)), hq) :
        {X.rm.h(X.rm.run(g, X.rm.child(U32.is_eq(_, x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, sd, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(sd, b))), k, x)) ==
          P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.k.of(U32.is_eq(IM.tr.addr(IM.pick.t(sd, r, l)), x), b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b)))), cut.si(IM.cut.k.of(U32.is_eq(IM.tr.addr(IM.pick.t(sd, r, l)), x), b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b))))), cut.pa(IM.cut.k.of(U32.is_eq(IM.tr.addr(IM.pick.t(sd, r, l)), x), b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b))))) : P.H}
      %Equal.sym(Bool, U32.is_eq(IM.tr.addr(IM.pick.t(sd, r, l)), x), True{}, hhit) :
        {X.rm.h(X.rm.run(g, X.rm.child(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, sd, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(sd, b))), k, x)) ==
          P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.k.of(_, b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b)))), cut.si(IM.cut.k.of(_, b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b))))), cut.pa(IM.cut.k.of(_, b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b))))) : P.H}
      %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.kid(Bool.not(sd), b)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), X.ix.kid(Bool.not(sd), b)))), rd_eq(t0, a, X.ix.kid(Bool.not(sd), b))) :
        {X.rm.h(X.rm.run(g, X.rm.found(_, loc, b), k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.Cut{loc, b, IM.tr.addr(IM.pick.t(sd, l, r))}), cut.si(IM.Cut{loc, b, IM.tr.addr(IM.pick.t(sd, l, r))})), cut.pa(IM.Cut{loc, b, IM.tr.addr(IM.pick.t(sd, l, r))})) : P.H}
      %wd(t0, d, X.ix.kid(Bool.not(sd), b), hft, hd32) :
        {X.rm.h(X.rm.run(g, X.Rm{P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, _), b), loc, b, False{}}, k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.Cut{loc, b, IM.tr.addr(IM.pick.t(sd, l, r))}), cut.si(IM.Cut{loc, b, IM.tr.addr(IM.pick.t(sd, l, r))})), cut.pa(IM.Cut{loc, b, IM.tr.addr(IM.pick.t(sd, l, r))})) : P.H}
      %Equal.sym(X.Rm, X.rm.run(g, X.Rm{P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(Bool.not(sd), b))), b), loc, b, False{}}, k, x), X.Rm{P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(Bool.not(sd), b))), b), loc, b, False{}},
        rm_stays(g, P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(Bool.not(sd), b))), b), loc, b, k, x)) :
        {X.rm.h(_) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.Cut{loc, b, IM.tr.addr(IM.pick.t(sd, l, r))}), cut.si(IM.Cut{loc, b, IM.tr.addr(IM.pick.t(sd, l, r))})), cut.pa(IM.Cut{loc, b, IM.tr.addr(IM.pick.t(sd, l, r))})) : P.H}
      %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(Bool.not(sd), b)), IM.tr.addr(IM.pick.t(sd, l, r)), hq2) :
        {P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, _), b) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.Cut{loc, b, IM.tr.addr(IM.pick.t(sd, l, r))}), cut.si(IM.Cut{loc, b, IM.tr.addr(IM.pick.t(sd, l, r))})), cut.pa(IM.Cut{loc, b, IM.tr.addr(IM.pick.t(sd, l, r))})) : P.H}
      {==}
    case False{}:
      %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(sd, b)), IM.tr.addr(IM.pick.t(sd, r, l)), hq) :
        {X.rm.h(X.rm.run(g, X.rm.child(U32.is_eq(_, x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, sd, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(sd, b))), k, x)) ==
          P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.k.of(U32.is_eq(IM.tr.addr(IM.pick.t(sd, r, l)), x), b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b)))), cut.si(IM.cut.k.of(U32.is_eq(IM.tr.addr(IM.pick.t(sd, r, l)), x), b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b))))), cut.pa(IM.cut.k.of(U32.is_eq(IM.tr.addr(IM.pick.t(sd, r, l)), x), b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b))))) : P.H}
      %Equal.sym(Bool, U32.is_eq(IM.tr.addr(IM.pick.t(sd, r, l)), x), False{}, hhit) :
        {X.rm.h(X.rm.run(g, X.rm.child(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, sd, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, X.ix.kid(sd, b))), k, x)) ==
          P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.k.of(_, b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b)))), cut.si(IM.cut.k.of(_, b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b))))), cut.pa(IM.cut.k.of(_, b, IM.tr.addr(IM.pick.t(sd, l, r)), loc, IM.tr.cutat(IM.pick.t(sd, r, l), x, k, X.ix.kid(sd, b))))) : P.H}
      ih(hhit)

# a branch at bit i, its children l and r realized below its words 2
# and 3: the removal's walk on the key's side
def rmA.k(+sd: Bool, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +b: U32, +i: Nat, +k: U32, +x: U32, +g: Nat, +loc: U32, +l: IM.Tr, +r: IM.Tr, +s: U32,
  +hsd: {X.ix.side(k, i) == sd : Bool},
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  +hrl: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) == True{} : Bool}, +hrr: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s) == True{} : Bool},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(l), x) == False{} : Bool} -> {X.rm.h(X.rm.run(g, X.Rm{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 2 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), True{}}, k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.tr.cutat(l, x, k, (b + 2 : U32))), cut.si(IM.tr.cutat(l, x, k, (b + 2 : U32)))), cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32)))) : P.H},
  ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(r), x) == False{} : Bool} -> {X.rm.h(X.rm.run(g, X.Rm{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), True{}}, k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.tr.cutat(r, x, k, (b + 3 : U32))), cut.si(IM.tr.cutat(r, x, k, (b + 3 : U32)))), cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32)))) : P.H}) ->
  {X.rm.h(X.rm.run(g, X.rm.c(P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.kid(X.ix.side(k, i), b)), loc, b, X.ix.side(k, i), x), k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), cut.si(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) : P.H}:
  match sd:
    case True{}:
      +hxr = ME.subst(Bool, z => {IM.mb.pick(z, IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>}, X.ix.side(k, i), True{}, hsd, hx)
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) :
        {X.rm.h(X.rm.run(g, X.rm.c(P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.kid(_, b)), loc, b, _, x), k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), cut.si(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) : P.H}
      %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 3 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 3 : U32)))), rd_eq(t0, a, (b + 3 : U32))) :
        {X.rm.h(X.rm.run(g, X.rm.c(_, loc, b, True{}, x), k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.at.k(True{}, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), cut.si(IM.cut.at.k(True{}, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(True{}, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) : P.H}
      %wd(t0, d, (b + 3 : U32), hft, hd32) :
        {X.rm.h(X.rm.run(g, X.rm.child(U32.is_eq(_, x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, True{}, _), k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.at.k(True{}, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), cut.si(IM.cut.at.k(True{}, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(True{}, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) : P.H}
      rmA.h(U32.is_eq(IM.tr.addr(r), x), True{}, t0, a, d, b, k, x, g, loc, l, r, s, hft, hd32, {==},
        real_addr(r, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s, hrr), real_addr(l, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s, hrl), hn => ihr(hxr)(hn))
    case False{}:
      +hxl = ME.subst(Bool, z => {IM.mb.pick(z, IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>}, X.ix.side(k, i), False{}, hsd, hx)
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) :
        {X.rm.h(X.rm.run(g, X.rm.c(P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.kid(_, b)), loc, b, _, x), k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), cut.si(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) : P.H}
      %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 2 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 2 : U32)))), rd_eq(t0, a, (b + 2 : U32))) :
        {X.rm.h(X.rm.run(g, X.rm.c(_, loc, b, False{}, x), k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.at.k(False{}, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), cut.si(IM.cut.at.k(False{}, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(False{}, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) : P.H}
      %wd(t0, d, (b + 2 : U32), hft, hd32) :
        {X.rm.h(X.rm.run(g, X.rm.child(U32.is_eq(_, x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, False{}, _), k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.at.k(False{}, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), cut.si(IM.cut.at.k(False{}, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(False{}, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) : P.H}
      rmA.h(U32.is_eq(IM.tr.addr(l), x), False{}, t0, a, d, b, k, x, g, loc, l, r, s, hft, hd32, {==},
        real_addr(l, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s, hrl), real_addr(r, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s, hrr), hn => ihl(hxl)(hn))

# The removal's walk from the pointer p, held at loc, to a tree the words
# realize, x a leaf on k's way below its root: the heap as the model's
# cut has it, x's sibling written at the word holding the parent's
# pointer, the parent freed
def rmA(T: IM.Tr, f: Nat, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +k: U32, +x: U32, +loc: U32, +p: U32, +lo: Nat,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, T, p, s) == True{} : Bool}, +hok: {IM.tr.ok(T, lo) == True{} : Bool},
  +hfu: {Nat.is_le(33n, Nat.add(f, lo)) == True{} : Bool},
  +hx: {IM.tr.look(T, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(T), x) == False{} : Bool}) ->
  {X.rm.h(X.rm.run(f, X.Rm{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, p, True{}}, k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.tr.cutat(T, x, k, loc)), cut.si(IM.tr.cutat(T, x, k, loc))), cut.pa(IM.tr.cutat(T, x, k, loc))) : P.H}:
  match T:
    case IM.Lf{+y, +ky}:
      Empty.absurd({X.rm.h(X.rm.run(f, X.Rm{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, p, True{}}, k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc)), cut.si(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc))), cut.pa(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc))) : P.H},
        MB.false_ne_true()(Equal.trans(Bool, False{}, U32.is_eq(x, x), True{},
          Equal.sym(Bool, U32.is_eq(x, x), False{}, ME.subst(U32, z => {U32.is_eq(z, x) == False{} : Bool}, y, x, hit_some(U32.is_eq(ky, k), y, x, hx), hne)),
          is_eq_self(x))))
    case IM.Br{+b, +i, +l, +r}:
      match f:
        case 0n:
          Empty.absurd({X.rm.h(X.rm.run(0n, X.Rm{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, p, True{}}, k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, loc)), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, loc))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, loc))) : P.H},
            MB.false_ne_true()(le_trans_b(33n, 1n+i, 32n, le_trans_b(33n, lo, 1n+i, hfu, le_trans_b(lo, i, 1n+i,
              and_l(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok), le_succ_b(i))),
              lt_le(i, 32n, and_l(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i))),
                and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok))))))
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
          %Equal.sym(U32, p, b, hpb) : {X.rm.h(X.rm.run(1n+g, X.Rm{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, _, True{}}, k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), cut.si(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) : P.H}
          %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, b), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), b))), rd_eq(t0, a, b)) :
            {X.rm.h(X.rm.run(g, X.rm.hd(_, loc, b, k, x), k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), cut.si(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) : P.H}
          %wd(t0, d, b, hft, hd32) : {X.rm.h(X.rm.run(g, X.rm.br(X.ix.branch(_), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, X.ix.bitof(_), k, x), k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), cut.si(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) : P.H}
          %Equal.sym(Bool, X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), True{}, hbr) :
            {X.rm.h(X.rm.run(g, X.rm.br(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), k, x), k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), cut.si(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) : P.H}
          %Equal.sym(Nat, X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i, hbi) :
            {X.rm.h(X.rm.run(g, X.rm.br(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, _, k, x), k, x)) == P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), cut.si(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) : P.H}
          rmA.k(X.ix.side(k, i), t0, a, d, b, i, k, x, g, loc, l, r, s, {==}, hft, hd32, hx,
            and_l(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r3), and_r(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r3),
            hxl => hnl => rmA(l, g, t0, a, d, s, k, x, (b + 2 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), 1n+i, hft, hd32, and_l(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r3), and_l(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), o4), hfg, hxl, hnl),
            hxr => hnr => rmA(r, g, t0, a, d, s, k, x, (b + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), 1n+i, hft, hd32, and_r(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r3), and_r(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), o4), hfg, hxr, hnr))

# Where a cut lands
# =================

def hx_side(+sd: Bool, +k: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>}) ->
  {IM.mb.pick(sd, IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>}:
  ME.subst(Bool, z => {IM.mb.pick(z, IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>}, X.ix.side(k, i), sd, hsd, hx)

# C1: the parent a cut frees is a node of the tree, so off any word the
# tree's nodes are off
def c1.h(+hit: Bool, +b: U32, +sib: U32, +loc: U32, +d: Nat, +j: U32, cd: IM.Cut, +hb: {KMd.off.words(KMd.nw(b), d, j) == True{} : Bool},
  ih: {hit == False{} : Bool} -> {KMd.off.words(KMd.nw(cut.pa(cd)), d, j) == True{} : Bool}) ->
  {KMd.off.words(KMd.nw(cut.pa(IM.cut.k.of(hit, b, sib, loc, cd))), d, j) == True{} : Bool}:
  match hit:
    case True{}:
      hb
    case False{}:
      ih({==})

def c1.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +j: U32, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hb: {KMd.off.words(KMd.nw(b), d, j) == True{} : Bool},
  +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(l), x) == False{} : Bool} -> {KMd.off.words(KMd.nw(cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32)))), d, j) == True{} : Bool},
  ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(r), x) == False{} : Bool} -> {KMd.off.words(KMd.nw(cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32)))), d, j) == True{} : Bool}) ->
  {KMd.off.words(KMd.nw(cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), d, j) == True{} : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {KMd.off.words(KMd.nw(cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), d, j) == True{} : Bool}
      c1.h(U32.is_eq(IM.tr.addr(r), x), b, IM.tr.addr(l), loc, d, j, IM.tr.cutat(r, x, k, (b + 3 : U32)), hb, hn => ihr(hx_side(True{}, k, i, l, r, x, hsd, hx))(hn))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {KMd.off.words(KMd.nw(cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), d, j) == True{} : Bool}
      c1.h(U32.is_eq(IM.tr.addr(l), x), b, IM.tr.addr(r), loc, d, j, IM.tr.cutat(l, x, k, (b + 2 : U32)), hb, hn => ihl(hx_side(False{}, k, i, l, r, x, hsd, hx))(hn))

def lf_absurd(-A: Type, +y: U32, +ky: U32, +x: U32, +k: U32, +hx: {IM.tr.look(IM.Lf{y, ky}, k) == Some{x} : Maybe<&2, U32>},
  +hne: {U32.is_eq(IM.tr.addr(IM.Lf{y, ky}), x) == False{} : Bool}) -> A:
  Empty.absurd(A, MB.false_ne_true()(Equal.trans(Bool, False{}, U32.is_eq(x, x), True{},
    Equal.sym(Bool, U32.is_eq(x, x), False{}, ME.subst(U32, z => {U32.is_eq(z, x) == False{} : Bool}, y, x, hit_some(U32.is_eq(ky, k), y, x, hx), hne)),
    is_eq_self(x))))

def c1(T: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +j: U32, +ho: {IM.tr.off(T, d, j) == True{} : Bool},
  +hx: {IM.tr.look(T, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(T), x) == False{} : Bool}) ->
  {KMd.off.words(KMd.nw(cut.pa(IM.tr.cutat(T, x, k, loc))), d, j) == True{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      lf_absurd({KMd.off.words(KMd.nw(cut.pa(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc))), d, j) == True{} : Bool}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      +hlr = and_r(KMd.off.words(KMd.nw(b), d, j), IM.tr.off(l, d, j) && IM.tr.off(r, d, j), ho)
      c1.k(X.ix.side(k, i), b, i, l, r, x, k, loc, d, j, {==}, and_l(KMd.off.words(KMd.nw(b), d, j), IM.tr.off(l, d, j) && IM.tr.off(r, d, j), ho), hx,
        hxl => hnl => c1(l, x, k, (b + 2 : U32), d, j, and_l(IM.tr.off(l, d, j), IM.tr.off(r, d, j), hlr), hxl, hnl),
        hxr => hnr => c1(r, x, k, (b + 3 : U32), d, j, and_r(IM.tr.off(l, d, j), IM.tr.off(r, d, j), hlr), hxr, hnr))

def and_intro(+p: Bool, +q: Bool, +hp: {p == True{} : Bool}, +hq: {q == True{} : Bool}) -> {Bool.and(p, q) == True{} : Bool}:
  %Equal.sym(Bool, p, True{}, hp) : {Bool.and(_, q) == True{} : Bool}
  hq

# apartness both ways round, swapped
def sep_sym(+d: Nat, +a: U32, +b: U32, +h: {IM.nd.sep(d, a, b) == True{} : Bool}) -> {IM.nd.sep(d, b, a) == True{} : Bool}:
  and_intro(IM.nd.disj(d, b, a), IM.nd.disj(d, a, b), and_r(IM.nd.disj(d, a, b), IM.nd.disj(d, b, a), h), and_l(IM.nd.disj(d, a, b), IM.nd.disj(d, b, a), h))

# every node of U apart from node b: U off each of b's four words
def onw(U: IM.Tr, +d: Nat, +b: U32, +h: {IM.tr.offn(U, d, b) == True{} : Bool}) -> {IM.tr.off(U, d, b) && (IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && IM.tr.off(U, d, (b + 3 : U32)))) == True{} : Bool}:
  match U:
    case IM.Lf{+y, +ky}:
      and_r(IM.nd.disj(d, y, b), IM.nd.disj(d, b, y), h)
    case IM.Br{+u, +ui, +ul, +ur}:
      +hu = and_r(IM.nd.disj(d, u, b), IM.nd.disj(d, b, u), and_l(IM.nd.sep(d, u, b), IM.tr.offn(ul, d, b) && IM.tr.offn(ur, d, b), h))
      +hlr = and_r(IM.nd.sep(d, u, b), IM.tr.offn(ul, d, b) && IM.tr.offn(ur, d, b), h)
      +il = onw(ul, d, b, and_l(IM.tr.offn(ul, d, b), IM.tr.offn(ur, d, b), hlr))
      +ir = onw(ur, d, b, and_r(IM.tr.offn(ul, d, b), IM.tr.offn(ur, d, b), hlr))
      +u1 = and_r(KMd.off.words(KMd.nw(u), d, b), KMd.off.words(KMd.nw(u), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(u), d, (b + 2 : U32)) && KMd.off.words(KMd.nw(u), d, (b + 3 : U32))), hu)
      +u2 = and_r(KMd.off.words(KMd.nw(u), d, (b + 1 : U32)), KMd.off.words(KMd.nw(u), d, (b + 2 : U32)) && KMd.off.words(KMd.nw(u), d, (b + 3 : U32)), u1)
      +l1 = and_r(IM.tr.off(ul, d, b), IM.tr.off(ul, d, (b + 1 : U32)) && (IM.tr.off(ul, d, (b + 2 : U32)) && IM.tr.off(ul, d, (b + 3 : U32))), il)
      +l2 = and_r(IM.tr.off(ul, d, (b + 1 : U32)), IM.tr.off(ul, d, (b + 2 : U32)) && IM.tr.off(ul, d, (b + 3 : U32)), l1)
      +r1 = and_r(IM.tr.off(ur, d, b), IM.tr.off(ur, d, (b + 1 : U32)) && (IM.tr.off(ur, d, (b + 2 : U32)) && IM.tr.off(ur, d, (b + 3 : U32))), ir)
      +r2 = and_r(IM.tr.off(ur, d, (b + 1 : U32)), IM.tr.off(ur, d, (b + 2 : U32)) && IM.tr.off(ur, d, (b + 3 : U32)), r1)
      and_intro(IM.tr.off(IM.Br{u, ui, ul, ur}, d, b), IM.tr.off(IM.Br{u, ui, ul, ur}, d, (b + 1 : U32)) && (IM.tr.off(IM.Br{u, ui, ul, ur}, d, (b + 2 : U32)) && IM.tr.off(IM.Br{u, ui, ul, ur}, d, (b + 3 : U32))),
        and_intro(KMd.off.words(KMd.nw(u), d, b), IM.tr.off(ul, d, b) && IM.tr.off(ur, d, b), and_l(KMd.off.words(KMd.nw(u), d, b), KMd.off.words(KMd.nw(u), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(u), d, (b + 2 : U32)) && KMd.off.words(KMd.nw(u), d, (b + 3 : U32))), hu),
          and_intro(IM.tr.off(ul, d, b), IM.tr.off(ur, d, b), and_l(IM.tr.off(ul, d, b), IM.tr.off(ul, d, (b + 1 : U32)) && (IM.tr.off(ul, d, (b + 2 : U32)) && IM.tr.off(ul, d, (b + 3 : U32))), il), and_l(IM.tr.off(ur, d, b), IM.tr.off(ur, d, (b + 1 : U32)) && (IM.tr.off(ur, d, (b + 2 : U32)) && IM.tr.off(ur, d, (b + 3 : U32))), ir))),
        and_intro(IM.tr.off(IM.Br{u, ui, ul, ur}, d, (b + 1 : U32)), IM.tr.off(IM.Br{u, ui, ul, ur}, d, (b + 2 : U32)) && IM.tr.off(IM.Br{u, ui, ul, ur}, d, (b + 3 : U32)),
          and_intro(KMd.off.words(KMd.nw(u), d, (b + 1 : U32)), IM.tr.off(ul, d, (b + 1 : U32)) && IM.tr.off(ur, d, (b + 1 : U32)), and_l(KMd.off.words(KMd.nw(u), d, (b + 1 : U32)), KMd.off.words(KMd.nw(u), d, (b + 2 : U32)) && KMd.off.words(KMd.nw(u), d, (b + 3 : U32)), u1),
            and_intro(IM.tr.off(ul, d, (b + 1 : U32)), IM.tr.off(ur, d, (b + 1 : U32)), and_l(IM.tr.off(ul, d, (b + 1 : U32)), IM.tr.off(ul, d, (b + 2 : U32)) && IM.tr.off(ul, d, (b + 3 : U32)), l1), and_l(IM.tr.off(ur, d, (b + 1 : U32)), IM.tr.off(ur, d, (b + 2 : U32)) && IM.tr.off(ur, d, (b + 3 : U32)), r1))),
          and_intro(IM.tr.off(IM.Br{u, ui, ul, ur}, d, (b + 2 : U32)), IM.tr.off(IM.Br{u, ui, ul, ur}, d, (b + 3 : U32)),
            and_intro(KMd.off.words(KMd.nw(u), d, (b + 2 : U32)), IM.tr.off(ul, d, (b + 2 : U32)) && IM.tr.off(ur, d, (b + 2 : U32)), and_l(KMd.off.words(KMd.nw(u), d, (b + 2 : U32)), KMd.off.words(KMd.nw(u), d, (b + 3 : U32)), u2),
              and_intro(IM.tr.off(ul, d, (b + 2 : U32)), IM.tr.off(ur, d, (b + 2 : U32)), and_l(IM.tr.off(ul, d, (b + 2 : U32)), IM.tr.off(ul, d, (b + 3 : U32)), l2), and_l(IM.tr.off(ur, d, (b + 2 : U32)), IM.tr.off(ur, d, (b + 3 : U32)), r2))),
            and_intro(KMd.off.words(KMd.nw(u), d, (b + 3 : U32)), IM.tr.off(ul, d, (b + 3 : U32)) && IM.tr.off(ur, d, (b + 3 : U32)), and_r(KMd.off.words(KMd.nw(u), d, (b + 2 : U32)), KMd.off.words(KMd.nw(u), d, (b + 3 : U32)), u2),
              and_intro(IM.tr.off(ul, d, (b + 3 : U32)), IM.tr.off(ur, d, (b + 3 : U32)), and_r(IM.tr.off(ul, d, (b + 2 : U32)), IM.tr.off(ul, d, (b + 3 : U32)), l2), and_r(IM.tr.off(ur, d, (b + 2 : U32)), IM.tr.off(ur, d, (b + 3 : U32)), r2))))))

# U apart from a branch: from its node b and from each child
def ap_b(U: IM.Tr, +d: Nat, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +h: {IM.tr.apart(U, IM.Br{b, i, l, r}, d) == True{} : Bool}) ->
  {Bool.and(IM.tr.offn(U, d, b), Bool.and(IM.tr.apart(U, l, d), IM.tr.apart(U, r, d))) == True{} : Bool}:
  match U:
    case IM.Lf{+y, +ky}:
      and_intro(IM.tr.offn(IM.Lf{y, ky}, d, b), IM.tr.apart(IM.Lf{y, ky}, l, d) && IM.tr.apart(IM.Lf{y, ky}, r, d),
        sep_sym(d, b, y, and_l(IM.nd.sep(d, b, y), IM.tr.offn(l, d, y) && IM.tr.offn(r, d, y), h)),
        and_r(IM.nd.sep(d, b, y), IM.tr.offn(l, d, y) && IM.tr.offn(r, d, y), h))
    case IM.Br{+u, +ui, +ul, +ur}:
      +hu = and_l(IM.tr.offn(IM.Br{b, i, l, r}, d, u), IM.tr.apart(ul, IM.Br{b, i, l, r}, d) && IM.tr.apart(ur, IM.Br{b, i, l, r}, d), h)
      +hs = and_r(IM.tr.offn(IM.Br{b, i, l, r}, d, u), IM.tr.apart(ul, IM.Br{b, i, l, r}, d) && IM.tr.apart(ur, IM.Br{b, i, l, r}, d), h)
      +il = ap_b(ul, d, b, i, l, r, and_l(IM.tr.apart(ul, IM.Br{b, i, l, r}, d), IM.tr.apart(ur, IM.Br{b, i, l, r}, d), hs))
      +ir = ap_b(ur, d, b, i, l, r, and_r(IM.tr.apart(ul, IM.Br{b, i, l, r}, d), IM.tr.apart(ur, IM.Br{b, i, l, r}, d), hs))
      +hlr = and_r(IM.nd.sep(d, b, u), IM.tr.offn(l, d, u) && IM.tr.offn(r, d, u), hu)
      +il2 = and_r(IM.tr.offn(ul, d, b), IM.tr.apart(ul, l, d) && IM.tr.apart(ul, r, d), il)
      +ir2 = and_r(IM.tr.offn(ur, d, b), IM.tr.apart(ur, l, d) && IM.tr.apart(ur, r, d), ir)
      and_intro(IM.tr.offn(IM.Br{u, ui, ul, ur}, d, b), IM.tr.apart(IM.Br{u, ui, ul, ur}, l, d) && IM.tr.apart(IM.Br{u, ui, ul, ur}, r, d),
        and_intro(IM.nd.sep(d, u, b), IM.tr.offn(ul, d, b) && IM.tr.offn(ur, d, b), sep_sym(d, b, u, and_l(IM.nd.sep(d, b, u), IM.tr.offn(l, d, u) && IM.tr.offn(r, d, u), hu)),
          and_intro(IM.tr.offn(ul, d, b), IM.tr.offn(ur, d, b), and_l(IM.tr.offn(ul, d, b), IM.tr.apart(ul, l, d) && IM.tr.apart(ul, r, d), il), and_l(IM.tr.offn(ur, d, b), IM.tr.apart(ur, l, d) && IM.tr.apart(ur, r, d), ir))),
        and_intro(IM.tr.apart(IM.Br{u, ui, ul, ur}, l, d), IM.tr.apart(IM.Br{u, ui, ul, ur}, r, d),
          and_intro(IM.tr.offn(l, d, u), IM.tr.apart(ul, l, d) && IM.tr.apart(ur, l, d), and_l(IM.tr.offn(l, d, u), IM.tr.offn(r, d, u), hlr),
            and_intro(IM.tr.apart(ul, l, d), IM.tr.apart(ur, l, d), and_l(IM.tr.apart(ul, l, d), IM.tr.apart(ul, r, d), il2), and_l(IM.tr.apart(ur, l, d), IM.tr.apart(ur, r, d), ir2))),
          and_intro(IM.tr.offn(r, d, u), IM.tr.apart(ul, r, d) && IM.tr.apart(ur, r, d), and_r(IM.tr.offn(l, d, u), IM.tr.offn(r, d, u), hlr),
            and_intro(IM.tr.apart(ul, r, d), IM.tr.apart(ur, r, d), and_r(IM.tr.apart(ul, l, d), IM.tr.apart(ul, r, d), il2), and_r(IM.tr.apart(ur, l, d), IM.tr.apart(ur, r, d), ir2)))))

# C2: the word a cut rewrites, where loc is not j's slot, is not either
def c2.h(+hit: Bool, +b: U32, +sib: U32, +loc: U32, +d: Nat, +j: U32, cd: IM.Cut, +hj: {Nat.is_eq(AD.slot(j, d), AD.slot(loc, d)) == False{} : Bool},
  ih: {hit == False{} : Bool} -> {Nat.is_eq(AD.slot(j, d), AD.slot(cut.lo(cd), d)) == False{} : Bool}) ->
  {Nat.is_eq(AD.slot(j, d), AD.slot(cut.lo(IM.cut.k.of(hit, b, sib, loc, cd)), d)) == False{} : Bool}:
  match hit:
    case True{}:
      hj
    case False{}:
      ih({==})

def c2.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +j: U32, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hj: {Nat.is_eq(AD.slot(j, d), AD.slot(loc, d)) == False{} : Bool},
  +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(l), x) == False{} : Bool} -> {Nat.is_eq(AD.slot(j, d), AD.slot(cut.lo(IM.tr.cutat(l, x, k, (b + 2 : U32))), d)) == False{} : Bool},
  ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(r), x) == False{} : Bool} -> {Nat.is_eq(AD.slot(j, d), AD.slot(cut.lo(IM.tr.cutat(r, x, k, (b + 3 : U32))), d)) == False{} : Bool}) ->
  {Nat.is_eq(AD.slot(j, d), AD.slot(cut.lo(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), d)) == False{} : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {Nat.is_eq(AD.slot(j, d), AD.slot(cut.lo(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), d)) == False{} : Bool}
      c2.h(U32.is_eq(IM.tr.addr(r), x), b, IM.tr.addr(l), loc, d, j, IM.tr.cutat(r, x, k, (b + 3 : U32)), hj, hn => ihr(hx_side(True{}, k, i, l, r, x, hsd, hx))(hn))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {Nat.is_eq(AD.slot(j, d), AD.slot(cut.lo(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), d)) == False{} : Bool}
      c2.h(U32.is_eq(IM.tr.addr(l), x), b, IM.tr.addr(r), loc, d, j, IM.tr.cutat(l, x, k, (b + 2 : U32)), hj, hn => ihl(hx_side(False{}, k, i, l, r, x, hsd, hx))(hn))

def c2(T: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +j: U32, +ho: {IM.tr.off(T, d, j) == True{} : Bool}, +hj: {Nat.is_eq(AD.slot(j, d), AD.slot(loc, d)) == False{} : Bool},
  +hx: {IM.tr.look(T, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(T), x) == False{} : Bool}) ->
  {Nat.is_eq(AD.slot(j, d), AD.slot(cut.lo(IM.tr.cutat(T, x, k, loc)), d)) == False{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      lf_absurd({Nat.is_eq(AD.slot(j, d), AD.slot(cut.lo(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc)), d)) == False{} : Bool}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      +hb = and_l(KMd.off.words(KMd.nw(b), d, j), IM.tr.off(l, d, j) && IM.tr.off(r, d, j), ho)
      +hlr = and_r(KMd.off.words(KMd.nw(b), d, j), IM.tr.off(l, d, j) && IM.tr.off(r, d, j), ho)
      c2.k(X.ix.side(k, i), b, i, l, r, x, k, loc, d, j, {==}, hj, hx,
        hxl => hnl => c2(l, x, k, (b + 2 : U32), d, j, and_l(IM.tr.off(l, d, j), IM.tr.off(r, d, j), hlr), off2(b, d, j, hb), hxl, hnl),
        hxr => hnr => c2(r, x, k, (b + 3 : U32), d, j, and_r(IM.tr.off(l, d, j), IM.tr.off(r, d, j), hlr), off3(b, d, j, hb), hxr, hnr))

# C3, C4: a tree U apart from the tree cut, off the word the cut
# rewrites (U off loc) and off the parent's words
def c34.h(+hit: Bool, +U: IM.Tr, +b: U32, +sib: U32, +loc: U32, +d: Nat, cd: IM.Cut,
  +hU: {IM.tr.off(U, d, loc) == True{} : Bool}, +hb: {IM.tr.off(U, d, b) && (IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && IM.tr.off(U, d, (b + 3 : U32)))) == True{} : Bool},
  ih: {hit == False{} : Bool} -> {Bool.and(IM.tr.off(U, d, cut.lo(cd)), Bool.and(IM.tr.off(U, d, cut.pa(cd)), IM.tr.off(U, d, (cut.pa(cd) + 1 : U32)))) == True{} : Bool}) ->
  {Bool.and(IM.tr.off(U, d, cut.lo(IM.cut.k.of(hit, b, sib, loc, cd))), Bool.and(IM.tr.off(U, d, cut.pa(IM.cut.k.of(hit, b, sib, loc, cd))), IM.tr.off(U, d, (cut.pa(IM.cut.k.of(hit, b, sib, loc, cd)) + 1 : U32)))) == True{} : Bool}:
  match hit:
    case True{}:
      and_intro(IM.tr.off(U, d, loc), IM.tr.off(U, d, b) && IM.tr.off(U, d, (b + 1 : U32)), hU,
        and_intro(IM.tr.off(U, d, b), IM.tr.off(U, d, (b + 1 : U32)), and_l(IM.tr.off(U, d, b), IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && IM.tr.off(U, d, (b + 3 : U32))), hb),
          and_l(IM.tr.off(U, d, (b + 1 : U32)), IM.tr.off(U, d, (b + 2 : U32)) && IM.tr.off(U, d, (b + 3 : U32)), and_r(IM.tr.off(U, d, b), IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && IM.tr.off(U, d, (b + 3 : U32))), hb))))
    case False{}:
      ih({==})

def c34.k(+sd: Bool, +U: IM.Tr, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hU: {IM.tr.off(U, d, loc) == True{} : Bool}, +hb: {IM.tr.off(U, d, b) && (IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && IM.tr.off(U, d, (b + 3 : U32)))) == True{} : Bool},
  +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(l), x) == False{} : Bool} -> {Bool.and(IM.tr.off(U, d, cut.lo(IM.tr.cutat(l, x, k, (b + 2 : U32)))), Bool.and(IM.tr.off(U, d, cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32)))), IM.tr.off(U, d, (cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32))) + 1 : U32)))) == True{} : Bool},
  ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(r), x) == False{} : Bool} -> {Bool.and(IM.tr.off(U, d, cut.lo(IM.tr.cutat(r, x, k, (b + 3 : U32)))), Bool.and(IM.tr.off(U, d, cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32)))), IM.tr.off(U, d, (cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32))) + 1 : U32)))) == True{} : Bool}) ->
  {Bool.and(IM.tr.off(U, d, cut.lo(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), Bool.and(IM.tr.off(U, d, cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), IM.tr.off(U, d, (cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))) + 1 : U32)))) == True{} : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {Bool.and(IM.tr.off(U, d, cut.lo(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), Bool.and(IM.tr.off(U, d, cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), IM.tr.off(U, d, (cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))) + 1 : U32)))) == True{} : Bool}
      c34.h(U32.is_eq(IM.tr.addr(r), x), U, b, IM.tr.addr(l), loc, d, IM.tr.cutat(r, x, k, (b + 3 : U32)), hU, hb, hn => ihr(hx_side(True{}, k, i, l, r, x, hsd, hx))(hn))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {Bool.and(IM.tr.off(U, d, cut.lo(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), Bool.and(IM.tr.off(U, d, cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), IM.tr.off(U, d, (cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))) + 1 : U32)))) == True{} : Bool}
      c34.h(U32.is_eq(IM.tr.addr(l), x), U, b, IM.tr.addr(r), loc, d, IM.tr.cutat(l, x, k, (b + 2 : U32)), hU, hb, hn => ihl(hx_side(False{}, k, i, l, r, x, hsd, hx))(hn))

def c34(T: IM.Tr, +U: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +hU: {IM.tr.off(U, d, loc) == True{} : Bool}, +ha: {IM.tr.apart(U, T, d) == True{} : Bool},
  +hx: {IM.tr.look(T, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(T), x) == False{} : Bool}) ->
  {Bool.and(IM.tr.off(U, d, cut.lo(IM.tr.cutat(T, x, k, loc))), Bool.and(IM.tr.off(U, d, cut.pa(IM.tr.cutat(T, x, k, loc))), IM.tr.off(U, d, (cut.pa(IM.tr.cutat(T, x, k, loc)) + 1 : U32)))) == True{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      lf_absurd({Bool.and(IM.tr.off(U, d, cut.lo(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc))), Bool.and(IM.tr.off(U, d, cut.pa(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc))), IM.tr.off(U, d, (cut.pa(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc)) + 1 : U32)))) == True{} : Bool}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      +hab = ap_b(U, d, b, i, l, r, ha)
      +hb = onw(U, d, b, and_l(IM.tr.offn(U, d, b), IM.tr.apart(U, l, d) && IM.tr.apart(U, r, d), hab))
      +hlr = and_r(IM.tr.offn(U, d, b), IM.tr.apart(U, l, d) && IM.tr.apart(U, r, d), hab)
      +h1 = and_r(IM.tr.off(U, d, b), IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && IM.tr.off(U, d, (b + 3 : U32))), hb)
      +h2 = and_r(IM.tr.off(U, d, (b + 1 : U32)), IM.tr.off(U, d, (b + 2 : U32)) && IM.tr.off(U, d, (b + 3 : U32)), h1)
      c34.k(X.ix.side(k, i), U, b, i, l, r, x, k, loc, d, {==}, hU, hb, hx,
        hxl => hnl => c34(l, U, x, k, (b + 2 : U32), d, and_l(IM.tr.off(U, d, (b + 2 : U32)), IM.tr.off(U, d, (b + 3 : U32)), h2), and_l(IM.tr.apart(U, l, d), IM.tr.apart(U, r, d), hlr), hxl, hnl),
        hxr => hnr => c34(r, U, x, k, (b + 3 : U32), d, and_r(IM.tr.off(U, d, (b + 2 : U32)), IM.tr.off(U, d, (b + 3 : U32)), h2), and_r(IM.tr.apart(U, l, d), IM.tr.apart(U, r, d), hlr), hxr, hnr))

# Through a removal's four writes
# ===============================

def neq_comm(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  %MN.is_eq_comm(a, b) : {_ == False{} : Bool}
  h

# word j off node x's first two words, x's slot first
def offs0(+x: U32, +d: Nat, +j: U32, +h: {KMd.off.words(KMd.nw(x), d, j) == True{} : Bool}) -> {Nat.is_eq(AD.slot(x, d), AD.slot(j, d)) == False{} : Bool}:
  neq_comm(AD.slot(j, d), AD.slot(x, d), off0(x, d, j, h))

def offs1(+x: U32, +d: Nat, +j: U32, +h: {KMd.off.words(KMd.nw(x), d, j) == True{} : Bool}) -> {Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}:
  neq_comm(AD.slot(j, d), AD.slot((x + 1 : U32), d), off1(x, d, j, h))

# a node's own words apart: its words 0, 2 and 3 from one another
def own.ws(+b: U32, +d: Nat, +h: {IM.nd.ok(b, d) == True{} : Bool}) -> {IM.ws.apart(KMd.nw(b), d) == True{} : Bool}:
  and_l(IM.ws.apart(KMd.nw(b), d), KMd.off.words(KMd.nw(b), d, P.at_fh()), and_r(U32.is_eq(P.base(b), b), IM.ws.apart(KMd.nw(b), d) && KMd.off.words(KMd.nw(b), d, P.at_fh()), h))

def own.fh(+b: U32, +d: Nat, +h: {IM.nd.ok(b, d) == True{} : Bool}) -> {KMd.off.words(KMd.nw(b), d, P.at_fh()) == True{} : Bool}:
  and_r(IM.ws.apart(KMd.nw(b), d), KMd.off.words(KMd.nw(b), d, P.at_fh()), and_r(U32.is_eq(P.base(b), b), IM.ws.apart(KMd.nw(b), d) && KMd.off.words(KMd.nw(b), d, P.at_fh()), h))

def own.b0(+b: U32, +d: Nat, +h: {IM.ws.apart(KMd.nw(b), d) == True{} : Bool}) -> {KMd.off.words([(b + 1 : U32), (b + 2 : U32), (b + 3 : U32)], d, b) == True{} : Bool}:
  and_l(KMd.off.words([(b + 1 : U32), (b + 2 : U32), (b + 3 : U32)], d, b), IM.ws.apart([(b + 1 : U32), (b + 2 : U32), (b + 3 : U32)], d), h)

def own.b2(+b: U32, +d: Nat, +h: {IM.ws.apart(KMd.nw(b), d) == True{} : Bool}) -> {KMd.off.words([(b + 3 : U32)], d, (b + 2 : U32)) == True{} : Bool}:
  and_l(KMd.off.words([(b + 3 : U32)], d, (b + 2 : U32)), IM.ws.apart([(b + 3 : U32)], d),
    and_r(KMd.off.words([(b + 2 : U32), (b + 3 : U32)], d, (b + 1 : U32)), IM.ws.apart([(b + 2 : U32), (b + 3 : U32)], d),
      and_r(KMd.off.words([(b + 1 : U32), (b + 2 : U32), (b + 3 : U32)], d, b), IM.ws.apart([(b + 1 : U32), (b + 2 : U32), (b + 3 : U32)], d), h)))

def own03(+b: U32, +d: Nat, +h: {IM.ws.apart(KMd.nw(b), d) == True{} : Bool}) -> {Nat.is_eq(AD.slot(b, d), AD.slot((b + 3 : U32), d)) == False{} : Bool}:
  offk(AD.slot((b + 3 : U32), d), AD.slot(b, d), and_l(Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(b, d))), True{},
    and_r(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(b, d))), KMd.off.words([(b + 3 : U32)], d, b),
      and_r(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(b, d))), KMd.off.words([(b + 2 : U32), (b + 3 : U32)], d, b), own.b0(b, d, h)))))

def own02(+b: U32, +d: Nat, +h: {IM.ws.apart(KMd.nw(b), d) == True{} : Bool}) -> {Nat.is_eq(AD.slot(b, d), AD.slot((b + 2 : U32), d)) == False{} : Bool}:
  offk(AD.slot((b + 2 : U32), d), AD.slot(b, d), and_l(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(b, d))), KMd.off.words([(b + 3 : U32)], d, b),
    and_r(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(b, d))), KMd.off.words([(b + 2 : U32), (b + 3 : U32)], d, b), own.b0(b, d, h))))

def own23(+b: U32, +d: Nat, +h: {IM.ws.apart(KMd.nw(b), d) == True{} : Bool}) -> {Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((b + 3 : U32), d)) == False{} : Bool}:
  offk(AD.slot((b + 3 : U32), d), AD.slot((b + 2 : U32), d), and_l(Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((b + 2 : U32), d))), True{}, own.b2(b, d, h)))

def own32(+b: U32, +d: Nat, +h: {IM.ws.apart(KMd.nw(b), d) == True{} : Bool}) -> {Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((b + 2 : U32), d)) == False{} : Bool}:
  not_true(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((b + 2 : U32), d)), and_l(Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((b + 2 : U32), d))), True{}, own.b2(b, d, h)))

# every node of a laid-out tree off the free list's head
def lay_fh(T: IM.Tr, +d: Nat, +h: {IM.tr.lay(T, d) == True{} : Bool}) -> {IM.tr.off(T, d, P.at_fh()) == True{} : Bool}:
  match T:
    case IM.Lf{+x, +kk}:
      own.fh(x, d, h)
    case IM.Br{+b, +i, +l, +r}:
      +h1 = and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), h)
      +h4 = and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), h1)))
      and_intro(KMd.off.words(KMd.nw(b), d, P.at_fh()), IM.tr.off(l, d, P.at_fh()) && IM.tr.off(r, d, P.at_fh()),
        own.fh(b, d, and_l(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), h)),
        and_intro(IM.tr.off(l, d, P.at_fh()), IM.tr.off(r, d, P.at_fh()), lay_fh(l, d, and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), h4)), lay_fh(r, d, and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), h4))))

# a word through the four writes: off each, as it was
def w4(+v: List<&2, U32>, +d: Nat, +L: U32, +P: U32, +S: U32, +f1: U32, +f2: U32, +j: U32,
  +hL: {Nat.is_eq(AD.slot(L, d), AD.slot(j, d)) == False{} : Bool}, +hP0: {Nat.is_eq(AD.slot(P, d), AD.slot(j, d)) == False{} : Bool}, +hP1: {Nat.is_eq(AD.slot((P + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hF: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}) ->
  {KMd.word(v, d, j) == KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, j) : U32}:
  Equal.trans(U32, KMd.word(v, d, j), KMd.word(List.set(&2, U32, v, AD.slot(L, d), S), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, j), wl_ne(v, d, L, j, S, hL),
    Equal.trans(U32, KMd.word(List.set(&2, U32, v, AD.slot(L, d), S), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, j), wl_ne(List.set(&2, U32, v, AD.slot(L, d), S), d, P, j, 0, hP0),
      Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, j), wl_ne(List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), d, (P + 1 : U32), j, f1, hP1),
        wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), d, P.at_fh(), j, f2, hF))))

# a tree through the four writes: off each, realized as it was
def r4(+T: IM.Tr, +v: List<&2, U32>, +d: Nat, +L: U32, +P: U32, +S: U32, +f1: U32, +f2: U32, +p: U32, +s: U32,
  +hL: {IM.tr.off(T, d, L) == True{} : Bool}, +hP0: {IM.tr.off(T, d, P) == True{} : Bool}, +hP1: {IM.tr.off(T, d, (P + 1 : U32)) == True{} : Bool}, +hF: {IM.tr.off(T, d, P.at_fh()) == True{} : Bool}) ->
  {IM.tr.real(v, d, T, p, s) == IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, T, p, s) : Bool}:
  Equal.trans(Bool, IM.tr.real(v, d, T, p, s), IM.tr.real(List.set(&2, U32, v, AD.slot(L, d), S), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, T, p, s), real_set(T, v, d, L, S, p, s, hL),
    Equal.trans(Bool, IM.tr.real(List.set(&2, U32, v, AD.slot(L, d), S), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, T, p, s), real_set(T, List.set(&2, U32, v, AD.slot(L, d), S), d, P, 0, p, s, hP0),
      Equal.trans(Bool, IM.tr.real(List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, T, p, s), real_set(T, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), d, (P + 1 : U32), f1, p, s, hP1),
        real_set(T, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), d, P.at_fh(), f2, p, s, hF))))

# C5: the parent a cut frees is its own base
def c5.h(+hit: Bool, +b: U32, +sib: U32, +loc: U32, cd: IM.Cut, +hb: {U32.is_eq(P.base(b), b) == True{} : Bool},
  ih: {hit == False{} : Bool} -> {U32.is_eq(P.base(cut.pa(cd)), cut.pa(cd)) == True{} : Bool}) ->
  {U32.is_eq(P.base(cut.pa(IM.cut.k.of(hit, b, sib, loc, cd))), cut.pa(IM.cut.k.of(hit, b, sib, loc, cd))) == True{} : Bool}:
  match hit:
    case True{}:
      hb
    case False{}:
      ih({==})

def c5.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +loc: U32, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hb: {U32.is_eq(P.base(b), b) == True{} : Bool},
  +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(l), x) == False{} : Bool} -> {U32.is_eq(P.base(cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32)))), cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32)))) == True{} : Bool},
  ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(r), x) == False{} : Bool} -> {U32.is_eq(P.base(cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32)))), cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32)))) == True{} : Bool}) ->
  {U32.is_eq(P.base(cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) == True{} : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {U32.is_eq(P.base(cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) == True{} : Bool}
      c5.h(U32.is_eq(IM.tr.addr(r), x), b, IM.tr.addr(l), loc, IM.tr.cutat(r, x, k, (b + 3 : U32)), hb, hn => ihr(hx_side(True{}, k, i, l, r, x, hsd, hx))(hn))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {U32.is_eq(P.base(cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))), cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) == True{} : Bool}
      c5.h(U32.is_eq(IM.tr.addr(l), x), b, IM.tr.addr(r), loc, IM.tr.cutat(l, x, k, (b + 2 : U32)), hb, hn => ihl(hx_side(False{}, k, i, l, r, x, hsd, hx))(hn))

def c5(T: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +hl: {IM.tr.lay(T, d) == True{} : Bool},
  +hx: {IM.tr.look(T, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(T), x) == False{} : Bool}) ->
  {U32.is_eq(P.base(cut.pa(IM.tr.cutat(T, x, k, loc))), cut.pa(IM.tr.cutat(T, x, k, loc))) == True{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      lf_absurd({U32.is_eq(P.base(cut.pa(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc))), cut.pa(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc))) == True{} : Bool}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      +h1 = and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl)
      +h4 = and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), h1)))
      c5.k(X.ix.side(k, i), b, i, l, r, x, k, loc, {==},
        and_l(U32.is_eq(P.base(b), b), IM.ws.apart(KMd.nw(b), d) && KMd.off.words(KMd.nw(b), d, P.at_fh()), and_l(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl)), hx,
        hxl => hnl => c5(l, x, k, (b + 2 : U32), d, and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), h4), hxl, hnl),
        hxr => hnr => c5(r, x, k, (b + 3 : U32), d, and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), h4), hxr, hnr))

# a tree apart from a leaf: the leaf apart from each of its nodes
def ap_lf(T: IM.Tr, +d: Nat, +y: U32, +ky: U32, +h: {IM.tr.apart(T, IM.Lf{y, ky}, d) == True{} : Bool}) -> {IM.tr.offn(T, d, y) == True{} : Bool}:
  match T:
    case IM.Lf{+z, +kz}:
      sep_sym(d, y, z, h)
    case IM.Br{+u, +ui, +ul, +ur}:
      +hs = and_r(IM.nd.sep(d, y, u), IM.tr.apart(ul, IM.Lf{y, ky}, d) && IM.tr.apart(ur, IM.Lf{y, ky}, d), h)
      and_intro(IM.nd.sep(d, u, y), IM.tr.offn(ul, d, y) && IM.tr.offn(ur, d, y), sep_sym(d, y, u, and_l(IM.nd.sep(d, y, u), IM.tr.apart(ul, IM.Lf{y, ky}, d) && IM.tr.apart(ur, IM.Lf{y, ky}, d), h)),
        and_intro(IM.tr.offn(ul, d, y), IM.tr.offn(ur, d, y), ap_lf(ul, d, y, ky, and_l(IM.tr.apart(ul, IM.Lf{y, ky}, d), IM.tr.apart(ur, IM.Lf{y, ky}, d), hs)), ap_lf(ur, d, y, ky, and_r(IM.tr.apart(ul, IM.Lf{y, ky}, d), IM.tr.apart(ur, IM.Lf{y, ky}, d), hs))))

# apartness of two trees, swapped
def apart_sym(R: IM.Tr, +l: IM.Tr, +d: Nat, +h: {IM.tr.apart(l, R, d) == True{} : Bool}) -> {IM.tr.apart(R, l, d) == True{} : Bool}:
  match R:
    case IM.Lf{+y, +ky}:
      ap_lf(l, d, y, ky, h)
    case IM.Br{+b, +i, +r1, +r2}:
      +hb = ap_b(l, d, b, i, r1, r2, h)
      +h12 = and_r(IM.tr.offn(l, d, b), IM.tr.apart(l, r1, d) && IM.tr.apart(l, r2, d), hb)
      and_intro(IM.tr.offn(l, d, b), IM.tr.apart(r1, l, d) && IM.tr.apart(r2, l, d), and_l(IM.tr.offn(l, d, b), IM.tr.apart(l, r1, d) && IM.tr.apart(l, r2, d), hb),
        and_intro(IM.tr.apart(r1, l, d), IM.tr.apart(r2, l, d), apart_sym(r1, l, d, and_l(IM.tr.apart(l, r1, d), IM.tr.apart(l, r2, d), h12)), apart_sym(r2, l, d, and_r(IM.tr.apart(l, r1, d), IM.tr.apart(l, r2, d), h12))))

# a word through the last three writes
def w3(+V1: List<&2, U32>, +d: Nat, +P: U32, +f1: U32, +f2: U32, +j: U32,
  +hP0: {Nat.is_eq(AD.slot(P, d), AD.slot(j, d)) == False{} : Bool}, +hP1: {Nat.is_eq(AD.slot((P + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hF: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}) ->
  {KMd.word(V1, d, j) == KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, V1, AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, j) : U32}:
  Equal.trans(U32, KMd.word(V1, d, j), KMd.word(List.set(&2, U32, V1, AD.slot(P, d), 0), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, V1, AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, j), wl_ne(V1, d, P, j, 0, hP0),
    Equal.trans(U32, KMd.word(List.set(&2, U32, V1, AD.slot(P, d), 0), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, V1, AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, V1, AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, j), wl_ne(List.set(&2, U32, V1, AD.slot(P, d), 0), d, (P + 1 : U32), j, f1, hP1),
      wl_ne(List.set(&2, U32, List.set(&2, U32, V1, AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), d, P.at_fh(), j, f2, hF)))
def rmB.r(+hit: Bool, +v: List<&2, U32>, +d: Nat, +s: U32, +k: U32, +x: U32, +loc: U32, +L: U32, +P: U32, +S: U32, +f1: U32, +f2: U32, +q: U32,
  +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr,
  +hhit: {U32.is_eq(IM.tr.addr(r), x) == hit : Bool},
  +hc: {IM.cut.k.of(U32.is_eq(IM.tr.addr(r), x), b, IM.tr.addr(l), loc, IM.tr.cutat(r, x, k, (b + 3 : U32))) == IM.Cut{L, P, S} : IM.Cut},
  +hvL: {List.get(&2, U32, v, AD.slot(L, d)) == Some{q} : Maybe<&2, U32>},
  +hp: {KMd.word(v, d, loc) == b : U32},
  +hrl: {IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) == True{} : Bool}, +hrr: {IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s) == True{} : Bool},
  +hbr: {X.ix.branch(KMd.word(v, d, b)) == True{} : Bool}, +hbi: {Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) == True{} : Bool},
  +hokb: {IM.nd.ok(b, d) == True{} : Bool}, +hol: {IM.tr.offn(l, d, b) == True{} : Bool}, +hor: {IM.tr.offn(r, d, b) == True{} : Bool},
  +hap: {IM.tr.apart(l, r, d) == True{} : Bool}, +hlay_l: {IM.tr.lay(l, d) == True{} : Bool}, +hlay_r: {IM.tr.lay(r, d) == True{} : Bool},
  +hlb: {KMd.off.words(KMd.nw(b), d, loc) == True{} : Bool}, +hll: {IM.tr.off(l, d, loc) == True{} : Bool}, +hlr: {IM.tr.off(r, d, loc) == True{} : Bool},
  +hlf: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(loc, d)) == False{} : Bool},
  +hxc: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>},
  ih: {hit == False{} : Bool} -> {IM.tr.cutat(r, x, k, (b + 3 : U32)) == IM.Cut{L, P, S} : IM.Cut} -> {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(r, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 3 : U32)), s) == True{} : Bool}) ->
  {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut.r(U32.is_eq(IM.tr.addr(r), x), b, i, l, IM.tr.cut(r, x, k)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}:
  match hit:
    case True{}:
      +hc1 = ME.subst(Bool, z => {IM.cut.k.of(z, b, IM.tr.addr(l), loc, IM.tr.cutat(r, x, k, (b + 3 : U32))) == IM.Cut{L, P, S} : IM.Cut}, U32.is_eq(IM.tr.addr(r), x), True{}, hhit, hc)
      +hL = Equal.cong(IM.Cut, U32, z => cut.lo(z), IM.Cut{loc, b, IM.tr.addr(l)}, IM.Cut{L, P, S}, hc1)
      +hP = Equal.cong(IM.Cut, U32, z => cut.pa(z), IM.Cut{loc, b, IM.tr.addr(l)}, IM.Cut{L, P, S}, hc1)
      +hS = Equal.cong(IM.Cut, U32, z => cut.si(z), IM.Cut{loc, b, IM.tr.addr(l)}, IM.Cut{L, P, S}, hc1)
      %Equal.sym(Bool, U32.is_eq(IM.tr.addr(r), x), True{}, hhit) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut.r(_, b, i, l, IM.tr.cut(r, x, k)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}
      %hL : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(_, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, l, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(_, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}
      %hP : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), S), AD.slot(_, d), 0), AD.slot((_ + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, l, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), S), AD.slot(_, d), 0), AD.slot((_ + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}
      %hS : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), _), AD.slot(b, d), 0), AD.slot((b + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, l, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), _), AD.slot(b, d), 0), AD.slot((b + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}
      %Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), IM.tr.addr(l)), AD.slot(b, d), 0), AD.slot((b + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), IM.tr.addr(l), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), IM.tr.addr(l)), AD.slot(b, d), 0), AD.slot((b + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), KMd.word(List.set(&2, U32, v, AD.slot(loc, d), IM.tr.addr(l)), d, loc), IM.tr.addr(l), Equal.sym(U32, KMd.word(List.set(&2, U32, v, AD.slot(loc, d), IM.tr.addr(l)), d, loc), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), IM.tr.addr(l)), AD.slot(b, d), 0), AD.slot((b + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), w3(List.set(&2, U32, v, AD.slot(loc, d), IM.tr.addr(l)), d, b, f1, f2, loc, offs0(b, d, loc, hlb), offs1(b, d, loc, hlb), hlf)), wl_eq(v, d, loc, IM.tr.addr(l), q, ME.subst(U32, z => {List.get(&2, U32, v, AD.slot(z, d)) == Some{q} : Maybe<&2, U32>}, L, loc, Equal.sym(U32, loc, L, hL), hvL)))) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), IM.tr.addr(l)), AD.slot(b, d), 0), AD.slot((b + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, l, _, s) == True{} : Bool}
      %r4(l, v, d, loc, b, IM.tr.addr(l), f1, f2, IM.tr.addr(l), s, hll, and_l(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hol)), and_l(IM.tr.off(l, d, (b + 1 : U32)), IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32))), and_r(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hol))), lay_fh(l, d, hlay_l)) : {_ == True{} : Bool}
      ME.subst(U32, z => {IM.tr.real(v, d, l, z, s) == True{} : Bool}, KMd.word(v, d, (b + 2 : U32)), IM.tr.addr(l), real_addr(l, v, d, KMd.word(v, d, (b + 2 : U32)), s, hrl), hrl)
    case False{}:
      +hc1 = ME.subst(Bool, z => {IM.cut.k.of(z, b, IM.tr.addr(l), loc, IM.tr.cutat(r, x, k, (b + 3 : U32))) == IM.Cut{L, P, S} : IM.Cut}, U32.is_eq(IM.tr.addr(r), x), False{}, hhit, hc)
      %Equal.sym(Bool, U32.is_eq(IM.tr.addr(r), x), False{}, hhit) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut.r(_, b, i, l, IM.tr.cut(r, x, k)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}
      %w4(v, d, L, P, S, f1, f2, loc, neq_comm(AD.slot(loc, d), AD.slot(L, d), ME.subst(IM.Cut, z => {Nat.is_eq(AD.slot(loc, d), AD.slot(cut.lo(z), d)) == False{} : Bool}, IM.tr.cutat(r, x, k, (b + 3 : U32)), IM.Cut{L, P, S}, hc1, c2(r, x, k, (b + 3 : U32), d, loc, hlr, off3(b, d, loc, hlb), hxc, hhit))), offs0(P, d, loc, ME.subst(IM.Cut, z => {KMd.off.words(KMd.nw(cut.pa(z)), d, loc) == True{} : Bool}, IM.tr.cutat(r, x, k, (b + 3 : U32)), IM.Cut{L, P, S}, hc1, c1(r, x, k, (b + 3 : U32), d, loc, hlr, hxc, hhit))), offs1(P, d, loc, ME.subst(IM.Cut, z => {KMd.off.words(KMd.nw(cut.pa(z)), d, loc) == True{} : Bool}, IM.tr.cutat(r, x, k, (b + 3 : U32)), IM.Cut{L, P, S}, hc1, c1(r, x, k, (b + 3 : U32), d, loc, hlr, hxc, hhit))), hlf) : {U32.is_eq(_, b) && (X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, b)), i) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, l, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(r, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 3 : U32)), s)))) == True{} : Bool}
      %Equal.sym(U32, KMd.word(v, d, loc), b, hp) : {U32.is_eq(_, b) && (X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, b)), i) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, l, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(r, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 3 : U32)), s)))) == True{} : Bool}
      %w4(v, d, L, P, S, f1, f2, b, neq_comm(AD.slot(b, d), AD.slot(L, d), ME.subst(IM.Cut, z => {Nat.is_eq(AD.slot(b, d), AD.slot(cut.lo(z), d)) == False{} : Bool}, IM.tr.cutat(r, x, k, (b + 3 : U32)), IM.Cut{L, P, S}, hc1, c2(r, x, k, (b + 3 : U32), d, b, and_l(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hor)), own03(b, d, own.ws(b, d, hokb)), hxc, hhit))), offs0(P, d, b, ME.subst(IM.Cut, z => {KMd.off.words(KMd.nw(cut.pa(z)), d, b) == True{} : Bool}, IM.tr.cutat(r, x, k, (b + 3 : U32)), IM.Cut{L, P, S}, hc1, c1(r, x, k, (b + 3 : U32), d, b, and_l(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hor)), hxc, hhit))), offs1(P, d, b, ME.subst(IM.Cut, z => {KMd.off.words(KMd.nw(cut.pa(z)), d, b) == True{} : Bool}, IM.tr.cutat(r, x, k, (b + 3 : U32)), IM.Cut{L, P, S}, hc1, c1(r, x, k, (b + 3 : U32), d, b, and_l(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hor)), hxc, hhit))), off0(b, d, P.at_fh(), own.fh(b, d, hokb))) : {U32.is_eq(b, b) && (X.ix.branch(_) && (Nat.is_eq(X.ix.bitof(_), i) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, l, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(r, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 3 : U32)), s)))) == True{} : Bool}
      %w4(v, d, L, P, S, f1, f2, (b + 2 : U32), neq_comm(AD.slot((b + 2 : U32), d), AD.slot(L, d), ME.subst(IM.Cut, z => {Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(cut.lo(z), d)) == False{} : Bool}, IM.tr.cutat(r, x, k, (b + 3 : U32)), IM.Cut{L, P, S}, hc1, c2(r, x, k, (b + 3 : U32), d, (b + 2 : U32), and_l(IM.tr.off(r, d, (b + 2 : U32)), IM.tr.off(r, d, (b + 3 : U32)), and_r(IM.tr.off(r, d, (b + 1 : U32)), IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32))), and_r(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hor)))), own23(b, d, own.ws(b, d, hokb)), hxc, hhit))), offs0(P, d, (b + 2 : U32), ME.subst(IM.Cut, z => {KMd.off.words(KMd.nw(cut.pa(z)), d, (b + 2 : U32)) == True{} : Bool}, IM.tr.cutat(r, x, k, (b + 3 : U32)), IM.Cut{L, P, S}, hc1, c1(r, x, k, (b + 3 : U32), d, (b + 2 : U32), and_l(IM.tr.off(r, d, (b + 2 : U32)), IM.tr.off(r, d, (b + 3 : U32)), and_r(IM.tr.off(r, d, (b + 1 : U32)), IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32))), and_r(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hor)))), hxc, hhit))), offs1(P, d, (b + 2 : U32), ME.subst(IM.Cut, z => {KMd.off.words(KMd.nw(cut.pa(z)), d, (b + 2 : U32)) == True{} : Bool}, IM.tr.cutat(r, x, k, (b + 3 : U32)), IM.Cut{L, P, S}, hc1, c1(r, x, k, (b + 3 : U32), d, (b + 2 : U32), and_l(IM.tr.off(r, d, (b + 2 : U32)), IM.tr.off(r, d, (b + 3 : U32)), and_r(IM.tr.off(r, d, (b + 1 : U32)), IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32))), and_r(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hor)))), hxc, hhit))), off2(b, d, P.at_fh(), own.fh(b, d, hokb))) : {U32.is_eq(b, b) && (X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, l, _, s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(r, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 3 : U32)), s)))) == True{} : Bool}
      %r4(l, v, d, L, P, S, f1, f2, KMd.word(v, d, (b + 2 : U32)), s, and_l(IM.tr.off(l, d, L), IM.tr.off(l, d, P) && IM.tr.off(l, d, (P + 1 : U32)), ME.subst(IM.Cut, z => {Bool.and(IM.tr.off(l, d, cut.lo(z)), Bool.and(IM.tr.off(l, d, cut.pa(z)), IM.tr.off(l, d, (cut.pa(z) + 1 : U32)))) == True{} : Bool}, IM.tr.cutat(r, x, k, (b + 3 : U32)), IM.Cut{L, P, S}, hc1, c34(r, l, x, k, (b + 3 : U32), d, and_r(IM.tr.off(l, d, (b + 2 : U32)), IM.tr.off(l, d, (b + 3 : U32)), and_r(IM.tr.off(l, d, (b + 1 : U32)), IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32))), and_r(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hol)))), hap, hxc, hhit))), and_l(IM.tr.off(l, d, P), IM.tr.off(l, d, (P + 1 : U32)), and_r(IM.tr.off(l, d, L), IM.tr.off(l, d, P) && IM.tr.off(l, d, (P + 1 : U32)), ME.subst(IM.Cut, z => {Bool.and(IM.tr.off(l, d, cut.lo(z)), Bool.and(IM.tr.off(l, d, cut.pa(z)), IM.tr.off(l, d, (cut.pa(z) + 1 : U32)))) == True{} : Bool}, IM.tr.cutat(r, x, k, (b + 3 : U32)), IM.Cut{L, P, S}, hc1, c34(r, l, x, k, (b + 3 : U32), d, and_r(IM.tr.off(l, d, (b + 2 : U32)), IM.tr.off(l, d, (b + 3 : U32)), and_r(IM.tr.off(l, d, (b + 1 : U32)), IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32))), and_r(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hol)))), hap, hxc, hhit)))), and_r(IM.tr.off(l, d, P), IM.tr.off(l, d, (P + 1 : U32)), and_r(IM.tr.off(l, d, L), IM.tr.off(l, d, P) && IM.tr.off(l, d, (P + 1 : U32)), ME.subst(IM.Cut, z => {Bool.and(IM.tr.off(l, d, cut.lo(z)), Bool.and(IM.tr.off(l, d, cut.pa(z)), IM.tr.off(l, d, (cut.pa(z) + 1 : U32)))) == True{} : Bool}, IM.tr.cutat(r, x, k, (b + 3 : U32)), IM.Cut{L, P, S}, hc1, c34(r, l, x, k, (b + 3 : U32), d, and_r(IM.tr.off(l, d, (b + 2 : U32)), IM.tr.off(l, d, (b + 3 : U32)), and_r(IM.tr.off(l, d, (b + 1 : U32)), IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32))), and_r(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hol)))), hap, hxc, hhit)))), lay_fh(l, d, hlay_l)) : {U32.is_eq(b, b) && (X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (_ && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(r, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 3 : U32)), s)))) == True{} : Bool}
      %Equal.sym(Bool, IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(r, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 3 : U32)), s), True{}, ih({==})(hc1)) : {U32.is_eq(b, b) && (X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && _))) == True{} : Bool}
      %Equal.sym(Bool, X.ix.branch(KMd.word(v, d, b)), True{}, hbr) : {U32.is_eq(b, b) && (_ && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && True{}))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i), True{}, hbi) : {U32.is_eq(b, b) && (True{} && (_ && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && True{}))) == True{} : Bool}
      %Equal.sym(Bool, IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s), True{}, hrl) : {U32.is_eq(b, b) && (True{} && (True{} && (_ && True{}))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(b, b), True{}, is_eq_self(b)) : {_ && (True{} && (True{} && (True{} && True{}))) == True{} : Bool}
      {==}

def rmB.l(+hit: Bool, +v: List<&2, U32>, +d: Nat, +s: U32, +k: U32, +x: U32, +loc: U32, +L: U32, +P: U32, +S: U32, +f1: U32, +f2: U32, +q: U32,
  +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr,
  +hhit: {U32.is_eq(IM.tr.addr(l), x) == hit : Bool},
  +hc: {IM.cut.k.of(U32.is_eq(IM.tr.addr(l), x), b, IM.tr.addr(r), loc, IM.tr.cutat(l, x, k, (b + 2 : U32))) == IM.Cut{L, P, S} : IM.Cut},
  +hvL: {List.get(&2, U32, v, AD.slot(L, d)) == Some{q} : Maybe<&2, U32>},
  +hp: {KMd.word(v, d, loc) == b : U32},
  +hrl: {IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) == True{} : Bool}, +hrr: {IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s) == True{} : Bool},
  +hbr: {X.ix.branch(KMd.word(v, d, b)) == True{} : Bool}, +hbi: {Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) == True{} : Bool},
  +hokb: {IM.nd.ok(b, d) == True{} : Bool}, +hol: {IM.tr.offn(l, d, b) == True{} : Bool}, +hor: {IM.tr.offn(r, d, b) == True{} : Bool},
  +hap: {IM.tr.apart(l, r, d) == True{} : Bool}, +hlay_l: {IM.tr.lay(l, d) == True{} : Bool}, +hlay_r: {IM.tr.lay(r, d) == True{} : Bool},
  +hlb: {KMd.off.words(KMd.nw(b), d, loc) == True{} : Bool}, +hll: {IM.tr.off(l, d, loc) == True{} : Bool}, +hlr: {IM.tr.off(r, d, loc) == True{} : Bool},
  +hlf: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(loc, d)) == False{} : Bool},
  +hxc: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>},
  ih: {hit == False{} : Bool} -> {IM.tr.cutat(l, x, k, (b + 2 : U32)) == IM.Cut{L, P, S} : IM.Cut} -> {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(l, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 2 : U32)), s) == True{} : Bool}) ->
  {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut.l(U32.is_eq(IM.tr.addr(l), x), b, i, r, IM.tr.cut(l, x, k)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}:
  match hit:
    case True{}:
      +hc1 = ME.subst(Bool, z => {IM.cut.k.of(z, b, IM.tr.addr(r), loc, IM.tr.cutat(l, x, k, (b + 2 : U32))) == IM.Cut{L, P, S} : IM.Cut}, U32.is_eq(IM.tr.addr(l), x), True{}, hhit, hc)
      +hL = Equal.cong(IM.Cut, U32, z => cut.lo(z), IM.Cut{loc, b, IM.tr.addr(r)}, IM.Cut{L, P, S}, hc1)
      +hP = Equal.cong(IM.Cut, U32, z => cut.pa(z), IM.Cut{loc, b, IM.tr.addr(r)}, IM.Cut{L, P, S}, hc1)
      +hS = Equal.cong(IM.Cut, U32, z => cut.si(z), IM.Cut{loc, b, IM.tr.addr(r)}, IM.Cut{L, P, S}, hc1)
      %Equal.sym(Bool, U32.is_eq(IM.tr.addr(l), x), True{}, hhit) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut.l(_, b, i, r, IM.tr.cut(l, x, k)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}
      %hL : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(_, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, r, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(_, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}
      %hP : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), S), AD.slot(_, d), 0), AD.slot((_ + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, r, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), S), AD.slot(_, d), 0), AD.slot((_ + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}
      %hS : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), _), AD.slot(b, d), 0), AD.slot((b + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, r, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), _), AD.slot(b, d), 0), AD.slot((b + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}
      %Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), IM.tr.addr(r)), AD.slot(b, d), 0), AD.slot((b + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), IM.tr.addr(r), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), IM.tr.addr(r)), AD.slot(b, d), 0), AD.slot((b + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), KMd.word(List.set(&2, U32, v, AD.slot(loc, d), IM.tr.addr(r)), d, loc), IM.tr.addr(r), Equal.sym(U32, KMd.word(List.set(&2, U32, v, AD.slot(loc, d), IM.tr.addr(r)), d, loc), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), IM.tr.addr(r)), AD.slot(b, d), 0), AD.slot((b + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), w3(List.set(&2, U32, v, AD.slot(loc, d), IM.tr.addr(r)), d, b, f1, f2, loc, offs0(b, d, loc, hlb), offs1(b, d, loc, hlb), hlf)), wl_eq(v, d, loc, IM.tr.addr(r), q, ME.subst(U32, z => {List.get(&2, U32, v, AD.slot(z, d)) == Some{q} : Maybe<&2, U32>}, L, loc, Equal.sym(U32, loc, L, hL), hvL)))) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(loc, d), IM.tr.addr(r)), AD.slot(b, d), 0), AD.slot((b + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, r, _, s) == True{} : Bool}
      %r4(r, v, d, loc, b, IM.tr.addr(r), f1, f2, IM.tr.addr(r), s, hlr, and_l(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hor)), and_l(IM.tr.off(r, d, (b + 1 : U32)), IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32))), and_r(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hor))), lay_fh(r, d, hlay_r)) : {_ == True{} : Bool}
      ME.subst(U32, z => {IM.tr.real(v, d, r, z, s) == True{} : Bool}, KMd.word(v, d, (b + 3 : U32)), IM.tr.addr(r), real_addr(r, v, d, KMd.word(v, d, (b + 3 : U32)), s, hrr), hrr)
    case False{}:
      +hc1 = ME.subst(Bool, z => {IM.cut.k.of(z, b, IM.tr.addr(r), loc, IM.tr.cutat(l, x, k, (b + 2 : U32))) == IM.Cut{L, P, S} : IM.Cut}, U32.is_eq(IM.tr.addr(l), x), False{}, hhit, hc)
      %Equal.sym(Bool, U32.is_eq(IM.tr.addr(l), x), False{}, hhit) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut.l(_, b, i, r, IM.tr.cut(l, x, k)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}
      %w4(v, d, L, P, S, f1, f2, loc, neq_comm(AD.slot(loc, d), AD.slot(L, d), ME.subst(IM.Cut, z => {Nat.is_eq(AD.slot(loc, d), AD.slot(cut.lo(z), d)) == False{} : Bool}, IM.tr.cutat(l, x, k, (b + 2 : U32)), IM.Cut{L, P, S}, hc1, c2(l, x, k, (b + 2 : U32), d, loc, hll, off2(b, d, loc, hlb), hxc, hhit))), offs0(P, d, loc, ME.subst(IM.Cut, z => {KMd.off.words(KMd.nw(cut.pa(z)), d, loc) == True{} : Bool}, IM.tr.cutat(l, x, k, (b + 2 : U32)), IM.Cut{L, P, S}, hc1, c1(l, x, k, (b + 2 : U32), d, loc, hll, hxc, hhit))), offs1(P, d, loc, ME.subst(IM.Cut, z => {KMd.off.words(KMd.nw(cut.pa(z)), d, loc) == True{} : Bool}, IM.tr.cutat(l, x, k, (b + 2 : U32)), IM.Cut{L, P, S}, hc1, c1(l, x, k, (b + 2 : U32), d, loc, hll, hxc, hhit))), hlf) : {U32.is_eq(_, b) && (X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, b)), i) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(l, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, r, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 3 : U32)), s)))) == True{} : Bool}
      %Equal.sym(U32, KMd.word(v, d, loc), b, hp) : {U32.is_eq(_, b) && (X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, b)), i) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(l, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, r, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 3 : U32)), s)))) == True{} : Bool}
      %w4(v, d, L, P, S, f1, f2, b, neq_comm(AD.slot(b, d), AD.slot(L, d), ME.subst(IM.Cut, z => {Nat.is_eq(AD.slot(b, d), AD.slot(cut.lo(z), d)) == False{} : Bool}, IM.tr.cutat(l, x, k, (b + 2 : U32)), IM.Cut{L, P, S}, hc1, c2(l, x, k, (b + 2 : U32), d, b, and_l(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hol)), own02(b, d, own.ws(b, d, hokb)), hxc, hhit))), offs0(P, d, b, ME.subst(IM.Cut, z => {KMd.off.words(KMd.nw(cut.pa(z)), d, b) == True{} : Bool}, IM.tr.cutat(l, x, k, (b + 2 : U32)), IM.Cut{L, P, S}, hc1, c1(l, x, k, (b + 2 : U32), d, b, and_l(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hol)), hxc, hhit))), offs1(P, d, b, ME.subst(IM.Cut, z => {KMd.off.words(KMd.nw(cut.pa(z)), d, b) == True{} : Bool}, IM.tr.cutat(l, x, k, (b + 2 : U32)), IM.Cut{L, P, S}, hc1, c1(l, x, k, (b + 2 : U32), d, b, and_l(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hol)), hxc, hhit))), off0(b, d, P.at_fh(), own.fh(b, d, hokb))) : {U32.is_eq(b, b) && (X.ix.branch(_) && (Nat.is_eq(X.ix.bitof(_), i) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(l, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, r, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 3 : U32)), s)))) == True{} : Bool}
      %w4(v, d, L, P, S, f1, f2, (b + 3 : U32), neq_comm(AD.slot((b + 3 : U32), d), AD.slot(L, d), ME.subst(IM.Cut, z => {Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(cut.lo(z), d)) == False{} : Bool}, IM.tr.cutat(l, x, k, (b + 2 : U32)), IM.Cut{L, P, S}, hc1, c2(l, x, k, (b + 2 : U32), d, (b + 3 : U32), and_r(IM.tr.off(l, d, (b + 2 : U32)), IM.tr.off(l, d, (b + 3 : U32)), and_r(IM.tr.off(l, d, (b + 1 : U32)), IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32))), and_r(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hol)))), own32(b, d, own.ws(b, d, hokb)), hxc, hhit))), offs0(P, d, (b + 3 : U32), ME.subst(IM.Cut, z => {KMd.off.words(KMd.nw(cut.pa(z)), d, (b + 3 : U32)) == True{} : Bool}, IM.tr.cutat(l, x, k, (b + 2 : U32)), IM.Cut{L, P, S}, hc1, c1(l, x, k, (b + 2 : U32), d, (b + 3 : U32), and_r(IM.tr.off(l, d, (b + 2 : U32)), IM.tr.off(l, d, (b + 3 : U32)), and_r(IM.tr.off(l, d, (b + 1 : U32)), IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32))), and_r(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hol)))), hxc, hhit))), offs1(P, d, (b + 3 : U32), ME.subst(IM.Cut, z => {KMd.off.words(KMd.nw(cut.pa(z)), d, (b + 3 : U32)) == True{} : Bool}, IM.tr.cutat(l, x, k, (b + 2 : U32)), IM.Cut{L, P, S}, hc1, c1(l, x, k, (b + 2 : U32), d, (b + 3 : U32), and_r(IM.tr.off(l, d, (b + 2 : U32)), IM.tr.off(l, d, (b + 3 : U32)), and_r(IM.tr.off(l, d, (b + 1 : U32)), IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32))), and_r(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hol)))), hxc, hhit))), off3(b, d, P.at_fh(), own.fh(b, d, hokb))) : {U32.is_eq(b, b) && (X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(l, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, r, _, s)))) == True{} : Bool}
      %r4(r, v, d, L, P, S, f1, f2, KMd.word(v, d, (b + 3 : U32)), s, and_l(IM.tr.off(r, d, L), IM.tr.off(r, d, P) && IM.tr.off(r, d, (P + 1 : U32)), ME.subst(IM.Cut, z => {Bool.and(IM.tr.off(r, d, cut.lo(z)), Bool.and(IM.tr.off(r, d, cut.pa(z)), IM.tr.off(r, d, (cut.pa(z) + 1 : U32)))) == True{} : Bool}, IM.tr.cutat(l, x, k, (b + 2 : U32)), IM.Cut{L, P, S}, hc1, c34(l, r, x, k, (b + 2 : U32), d, and_l(IM.tr.off(r, d, (b + 2 : U32)), IM.tr.off(r, d, (b + 3 : U32)), and_r(IM.tr.off(r, d, (b + 1 : U32)), IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32))), and_r(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hor)))), apart_sym(r, l, d, hap), hxc, hhit))), and_l(IM.tr.off(r, d, P), IM.tr.off(r, d, (P + 1 : U32)), and_r(IM.tr.off(r, d, L), IM.tr.off(r, d, P) && IM.tr.off(r, d, (P + 1 : U32)), ME.subst(IM.Cut, z => {Bool.and(IM.tr.off(r, d, cut.lo(z)), Bool.and(IM.tr.off(r, d, cut.pa(z)), IM.tr.off(r, d, (cut.pa(z) + 1 : U32)))) == True{} : Bool}, IM.tr.cutat(l, x, k, (b + 2 : U32)), IM.Cut{L, P, S}, hc1, c34(l, r, x, k, (b + 2 : U32), d, and_l(IM.tr.off(r, d, (b + 2 : U32)), IM.tr.off(r, d, (b + 3 : U32)), and_r(IM.tr.off(r, d, (b + 1 : U32)), IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32))), and_r(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hor)))), apart_sym(r, l, d, hap), hxc, hhit)))), and_r(IM.tr.off(r, d, P), IM.tr.off(r, d, (P + 1 : U32)), and_r(IM.tr.off(r, d, L), IM.tr.off(r, d, P) && IM.tr.off(r, d, (P + 1 : U32)), ME.subst(IM.Cut, z => {Bool.and(IM.tr.off(r, d, cut.lo(z)), Bool.and(IM.tr.off(r, d, cut.pa(z)), IM.tr.off(r, d, (cut.pa(z) + 1 : U32)))) == True{} : Bool}, IM.tr.cutat(l, x, k, (b + 2 : U32)), IM.Cut{L, P, S}, hc1, c34(l, r, x, k, (b + 2 : U32), d, and_l(IM.tr.off(r, d, (b + 2 : U32)), IM.tr.off(r, d, (b + 3 : U32)), and_r(IM.tr.off(r, d, (b + 1 : U32)), IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32))), and_r(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hor)))), apart_sym(r, l, d, hap), hxc, hhit)))), lay_fh(r, d, hlay_r)) : {U32.is_eq(b, b) && (X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(l, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 2 : U32)), s) && _))) == True{} : Bool}
      %Equal.sym(Bool, IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(l, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 2 : U32)), s), True{}, ih({==})(hc1)) : {U32.is_eq(b, b) && (X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (_ && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s)))) == True{} : Bool}
      %Equal.sym(Bool, X.ix.branch(KMd.word(v, d, b)), True{}, hbr) : {U32.is_eq(b, b) && (_ && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (True{} && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s)))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i), True{}, hbi) : {U32.is_eq(b, b) && (True{} && (_ && (True{} && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s)))) == True{} : Bool}
      %Equal.sym(Bool, IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), True{}, hrr) : {U32.is_eq(b, b) && (True{} && (True{} && (True{} && _))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(b, b), True{}, is_eq_self(b)) : {_ && (True{} && (True{} && (True{} && True{}))) == True{} : Bool}
      {==}

def rmB.k(+sd: Bool, +v: List<&2, U32>, +d: Nat, +s: U32, +k: U32, +x: U32, +loc: U32, +L: U32, +P: U32, +S: U32, +f1: U32, +f2: U32, +q: U32,
  +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hc: {IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))) == IM.Cut{L, P, S} : IM.Cut},
  +hvL: {List.get(&2, U32, v, AD.slot(L, d)) == Some{q} : Maybe<&2, U32>},
  +hp: {KMd.word(v, d, loc) == b : U32},
  +hrl: {IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) == True{} : Bool}, +hrr: {IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s) == True{} : Bool},
  +hbr: {X.ix.branch(KMd.word(v, d, b)) == True{} : Bool}, +hbi: {Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) == True{} : Bool},
  +hokb: {IM.nd.ok(b, d) == True{} : Bool}, +hol: {IM.tr.offn(l, d, b) == True{} : Bool}, +hor: {IM.tr.offn(r, d, b) == True{} : Bool},
  +hap: {IM.tr.apart(l, r, d) == True{} : Bool}, +hlay_l: {IM.tr.lay(l, d) == True{} : Bool}, +hlay_r: {IM.tr.lay(r, d) == True{} : Bool},
  +hlb: {KMd.off.words(KMd.nw(b), d, loc) == True{} : Bool}, +hll: {IM.tr.off(l, d, loc) == True{} : Bool}, +hlr: {IM.tr.off(r, d, loc) == True{} : Bool},
  +hlf: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(loc, d)) == False{} : Bool},
  +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(l), x) == False{} : Bool} -> {IM.tr.cutat(l, x, k, (b + 2 : U32)) == IM.Cut{L, P, S} : IM.Cut} -> {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(l, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 2 : U32)), s) == True{} : Bool},
  ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(r), x) == False{} : Bool} -> {IM.tr.cutat(r, x, k, (b + 3 : U32)) == IM.Cut{L, P, S} : IM.Cut} -> {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(r, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, (b + 3 : U32)), s) == True{} : Bool}) ->
  {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut.k(X.ix.side(k, i), b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}:
  match sd:
    case True{}:
      +hc1 = ME.subst(Bool, z => {IM.cut.at.k(z, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))) == IM.Cut{L, P, S} : IM.Cut}, X.ix.side(k, i), True{}, hsd, hc)
      +hxr = hx_side(True{}, k, i, l, r, x, hsd, hx)
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut.k(_, b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}
      rmB.r(U32.is_eq(IM.tr.addr(r), x), v, d, s, k, x, loc, L, P, S, f1, f2, q, b, i, l, r, {==}, hc1, hvL, hp, hrl, hrr, hbr, hbi, hokb, hol, hor, hap, hlay_l, hlay_r, hlb, hll, hlr, hlf, hxr,
        hn => hcc => ihr(hxr)(hn)(hcc))
    case False{}:
      +hc1 = ME.subst(Bool, z => {IM.cut.at.k(z, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))) == IM.Cut{L, P, S} : IM.Cut}, X.ix.side(k, i), False{}, hsd, hc)
      +hxl = hx_side(False{}, k, i, l, r, x, hsd, hx)
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut.k(_, b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}
      rmB.l(U32.is_eq(IM.tr.addr(l), x), v, d, s, k, x, loc, L, P, S, f1, f2, q, b, i, l, r, {==}, hc1, hvL, hp, hrl, hrr, hbr, hbi, hokb, hol, hor, hap, hlay_l, hlay_r, hlb, hll, hlr, hlf, hxl,
        hn => hcc => ihl(hxl)(hn)(hcc))

# The realization after a removal's writes: the tree without x realized
# by the words, from the word loc that held the tree's pointer p, the
# writes' words and values L, P, S, f1 and f2 those of the model's cut,
# the view holding a word at L
def rmB(T: IM.Tr, +v: List<&2, U32>, +d: Nat, +s: U32, +k: U32, +x: U32, +loc: U32, +p: U32, +L: U32, +P: U32, +S: U32, +f1: U32, +f2: U32, +q: U32,
  +hre: {IM.tr.real(v, d, T, p, s) == True{} : Bool}, +hx: {IM.tr.look(T, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(T), x) == False{} : Bool},
  +hlay: {IM.tr.lay(T, d) == True{} : Bool}, +hloc: {IM.tr.off(T, d, loc) == True{} : Bool}, +hlf: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(loc, d)) == False{} : Bool}, +hp: {KMd.word(v, d, loc) == p : U32},
  +hc: {IM.tr.cutat(T, x, k, loc) == IM.Cut{L, P, S} : IM.Cut}, +hvL: {List.get(&2, U32, v, AD.slot(L, d)) == Some{q} : Maybe<&2, U32>}) ->
  {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(T, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      lf_absurd({IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, IM.tr.cut(IM.Lf{y, ky}, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(L, d), S), AD.slot(P, d), 0), AD.slot((P + 1 : U32), d), f1), AD.slot(P.at_fh(), d), f2), d, loc), s) == True{} : Bool}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      +hr1 = and_r(U32.is_eq(p, b), X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s))), hre)
      +hr2 = and_r(X.ix.branch(KMd.word(v, d, b)), Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s)), hr1)
      +hr3 = and_r(Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i), IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), hr2)
      +hl1 = and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hlay)
      +hl2 = and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), hl1)
      +hl3 = and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), hl2)
      +hl4 = and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), hl3)
      +hc1 = and_r(KMd.off.words(KMd.nw(b), d, loc), IM.tr.off(l, d, loc) && IM.tr.off(r, d, loc), hloc)
      +hokb = and_l(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hlay)
      +hol = and_l(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), hl1)
      +hor = and_l(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), hl2)
      +hrl = and_l(IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s), IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), hr3)
      +hrr = and_r(IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s), IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), hr3)
      +hlay_l = and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), hl4)
      +hlay_r = and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), hl4)
      rmB.k(X.ix.side(k, i), v, d, s, k, x, loc, L, P, S, f1, f2, q, b, i, l, r, {==}, hc, hvL,
        Equal.trans(U32, KMd.word(v, d, loc), p, b, hp, real_addr(IM.Br{b, i, l, r}, v, d, p, s, hre)),
        hrl, hrr, and_l(X.ix.branch(KMd.word(v, d, b)), Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s)), hr1), and_l(Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i), IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), hr2),
        hokb, hol, hor, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), hl3), hlay_l, hlay_r,
        and_l(KMd.off.words(KMd.nw(b), d, loc), IM.tr.off(l, d, loc) && IM.tr.off(r, d, loc), hloc), and_l(IM.tr.off(l, d, loc), IM.tr.off(r, d, loc), hc1), and_r(IM.tr.off(l, d, loc), IM.tr.off(r, d, loc), hc1),
        hlf, hx,
        hxl => hnl => hcl => rmB(l, v, d, s, k, x, (b + 2 : U32), KMd.word(v, d, (b + 2 : U32)), L, P, S, f1, f2, q, hrl, hxl, hnl, hlay_l, and_l(IM.tr.off(l, d, (b + 2 : U32)), IM.tr.off(l, d, (b + 3 : U32)), and_r(IM.tr.off(l, d, (b + 1 : U32)), IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32))), and_r(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hol)))),
          off2(b, d, P.at_fh(), own.fh(b, d, hokb)), {==}, hcl, hvL),
        hxr => hnr => hcr => rmB(r, v, d, s, k, x, (b + 3 : U32), KMd.word(v, d, (b + 3 : U32)), L, P, S, f1, f2, q, hrr, hxr, hnr, hlay_r, and_r(IM.tr.off(r, d, (b + 2 : U32)), IM.tr.off(r, d, (b + 3 : U32)), and_r(IM.tr.off(r, d, (b + 1 : U32)), IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32))), and_r(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hor)))),
          off3(b, d, P.at_fh(), own.fh(b, d, hokb)), {==}, hcr, hvL))

# The removal's law
# =================

def hit_true(+b: Bool, +y: U32, +x: U32, +h: {IM.mb.hit(b, y) == Some{x} : Maybe<&2, U32>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, m => is_some(m), None{}, Some{x}, h)))

def lk.k(+sd: Bool, +v: List<&2, U32>, +d: Nat, +i: Nat, +l: IM.Tr, +r: IM.Tr, +k: U32, +x: U32, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {KMd.word(v, d, (x + 2 : U32)) == k : U32},
  ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {KMd.word(v, d, (x + 2 : U32)) == k : U32}) -> {KMd.word(v, d, (x + 2 : U32)) == k : U32}:
  match sd:
    case True{}:
      ihr(hx_side(True{}, k, i, l, r, x, hsd, hx))
    case False{}:
      ihl(hx_side(False{}, k, i, l, r, x, hsd, hx))

# the cursor a lookup finds holds the key in its word 2
def look_key(T: IM.Tr, +v: List<&2, U32>, +d: Nat, +p: U32, +s: U32, +k: U32, +x: U32,
  +hre: {IM.tr.real(v, d, T, p, s) == True{} : Bool}, +hx: {IM.tr.look(T, k) == Some{x} : Maybe<&2, U32>}) -> {KMd.word(v, d, (x + 2 : U32)) == k : U32}:
  match T:
    case IM.Lf{+y, +ky}:
      ME.subst(U32, z => {KMd.word(v, d, (z + 2 : U32)) == k : U32}, y, x, hit_some(U32.is_eq(ky, k), y, x, hx),
        Equal.trans(U32, KMd.word(v, d, (y + 2 : U32)), ky, k,
          MS.u32_eq_of_is_eq(KMd.word(v, d, (y + 2 : U32)), ky, and_l(U32.is_eq(KMd.word(v, d, (y + 2 : U32)), ky), U32.is_eq(KMd.word(v, d, (y + 3 : U32)), s),
            and_r(Bool.not(X.ix.branch(KMd.word(v, d, y))), U32.is_eq(KMd.word(v, d, (y + 2 : U32)), ky) && U32.is_eq(KMd.word(v, d, (y + 3 : U32)), s),
              and_r(U32.is_eq(p, y), Bool.not(X.ix.branch(KMd.word(v, d, y))) && (U32.is_eq(KMd.word(v, d, (y + 2 : U32)), ky) && U32.is_eq(KMd.word(v, d, (y + 3 : U32)), s)), hre)))),
          MS.u32_eq_of_is_eq(ky, k, hit_true(U32.is_eq(ky, k), y, x, hx))))
    case IM.Br{+b, +i, +l, +r}:
      +hr3 = and_r(Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i), IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), and_r(X.ix.branch(KMd.word(v, d, b)), Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s)), and_r(U32.is_eq(p, b), X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s))), hre)))
      lk.k(X.ix.side(k, i), v, d, i, l, r, k, x, {==}, hx,
        hxl => look_key(l, v, d, KMd.word(v, d, (b + 2 : U32)), s, k, x, and_l(IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s), IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), hr3), hxl),
        hxr => look_key(r, v, d, KMd.word(v, d, (b + 3 : U32)), s, k, x, and_r(IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s), IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), hr3), hxr))

def ls.k(+sd: Bool, +d: Nat, +i: Nat, +l: IM.Tr, +r: IM.Tr, +k: U32, +x: U32, +a: U32, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {IM.nd.sep(d, x, a) == True{} : Bool},
  ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {IM.nd.sep(d, x, a) == True{} : Bool}) -> {IM.nd.sep(d, x, a) == True{} : Bool}:
  match sd:
    case True{}:
      ihr(hx_side(True{}, k, i, l, r, x, hsd, hx))
    case False{}:
      ihl(hx_side(False{}, k, i, l, r, x, hsd, hx))

# the cursor a lookup finds is a node of the tree: apart from what all
# of them are
def look_sep(T: IM.Tr, +a: U32, +d: Nat, +k: U32, +x: U32, +h: {IM.tr.offn(T, d, a) == True{} : Bool}, +hx: {IM.tr.look(T, k) == Some{x} : Maybe<&2, U32>}) ->
  {IM.nd.sep(d, x, a) == True{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      ME.subst(U32, z => {IM.nd.sep(d, z, a) == True{} : Bool}, y, x, hit_some(U32.is_eq(ky, k), y, x, hx), h)
    case IM.Br{+b, +i, +l, +r}:
      +hlr = and_r(IM.nd.sep(d, b, a), IM.tr.offn(l, d, a) && IM.tr.offn(r, d, a), h)
      ls.k(X.ix.side(k, i), d, i, l, r, k, x, a, {==}, hx,
        hxl => look_sep(l, a, d, k, x, and_l(IM.tr.offn(l, d, a), IM.tr.offn(r, d, a), hlr), hxl),
        hxr => look_sep(r, a, d, k, x, and_r(IM.tr.offn(l, d, a), IM.tr.offn(r, d, a), hlr), hxr))

def ne_of_slot.k(+a: U32, +b: U32, +d: Nat, +e: Bool, +he: {U32.is_eq(a, b) == e : Bool}, +h: {Nat.is_eq(AD.slot(a, d), AD.slot(b, d)) == False{} : Bool}) -> {U32.is_eq(a, b) == False{} : Bool}:
  match e:
    case False{}:
      he
    case True{}:
      Empty.absurd({U32.is_eq(a, b) == False{} : Bool}, MB.false_ne_true()(Equal.trans(Bool, False{}, Nat.is_eq(AD.slot(a, d), AD.slot(a, d)), True{},
        Equal.sym(Bool, Nat.is_eq(AD.slot(a, d), AD.slot(a, d)), False{}, ME.subst(U32, z => {Nat.is_eq(AD.slot(a, d), AD.slot(z, d)) == False{} : Bool}, b, a, Equal.sym(U32, a, b, MS.u32_eq_of_is_eq(a, b, he)), h)),
        MN.is_eq_refl(AD.slot(a, d)))))

# two words in different slots are different words
def ne_of_slot(+a: U32, +b: U32, +d: Nat, +h: {Nat.is_eq(AD.slot(a, d), AD.slot(b, d)) == False{} : Bool}) -> {U32.is_eq(a, b) == False{} : Bool}:
  ne_of_slot.k(a, b, d, U32.is_eq(a, b), {==}, h)

# nodes apart: their bases different words
def sep_ne(+d: Nat, +a: U32, +b: U32, +h: {IM.nd.sep(d, a, b) == True{} : Bool}) -> {U32.is_eq(b, a) == False{} : Bool}:
  ne_of_slot(b, a, d, not_true(Nat.is_eq(AD.slot(b, d), AD.slot(a, d)), and_l(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot(a, d))), KMd.off.words([(b + 1 : U32), (b + 2 : U32), (b + 3 : U32)], d, a),
    and_l(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))),
      and_l(IM.nd.disj(d, a, b), IM.nd.disj(d, b, a), h)))))

# a cut tree's nodes among the tree's
def co.r(+hit: Bool, +b: U32, +i: Nat, +l: IM.Tr, +cr: IM.Tr, +d: Nat, +a: U32, +hb: {IM.nd.sep(d, b, a) == True{} : Bool}, +hl: {IM.tr.offn(l, d, a) == True{} : Bool}, +hcr: {IM.tr.offn(cr, d, a) == True{} : Bool}) ->
  {IM.tr.offn(IM.tr.cut.r(hit, b, i, l, cr), d, a) == True{} : Bool}:
  match hit:
    case True{}:
      hl
    case False{}:
      and_intro(IM.nd.sep(d, b, a), IM.tr.offn(l, d, a) && IM.tr.offn(cr, d, a), hb, and_intro(IM.tr.offn(l, d, a), IM.tr.offn(cr, d, a), hl, hcr))

def co.l(+hit: Bool, +b: U32, +i: Nat, +r: IM.Tr, +cl: IM.Tr, +d: Nat, +a: U32, +hb: {IM.nd.sep(d, b, a) == True{} : Bool}, +hr: {IM.tr.offn(r, d, a) == True{} : Bool}, +hcl: {IM.tr.offn(cl, d, a) == True{} : Bool}) ->
  {IM.tr.offn(IM.tr.cut.l(hit, b, i, r, cl), d, a) == True{} : Bool}:
  match hit:
    case True{}:
      hr
    case False{}:
      and_intro(IM.nd.sep(d, b, a), IM.tr.offn(cl, d, a) && IM.tr.offn(r, d, a), hb, and_intro(IM.tr.offn(cl, d, a), IM.tr.offn(r, d, a), hcl, hr))

def co.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +cl: IM.Tr, +cr: IM.Tr, +d: Nat, +a: U32, +hb: {IM.nd.sep(d, b, a) == True{} : Bool},
  +hl: {IM.tr.offn(l, d, a) == True{} : Bool}, +hr: {IM.tr.offn(r, d, a) == True{} : Bool}, +hcl: {IM.tr.offn(cl, d, a) == True{} : Bool}, +hcr: {IM.tr.offn(cr, d, a) == True{} : Bool}) ->
  {IM.tr.offn(IM.tr.cut.k(sd, b, i, l, r, x, cl, cr), d, a) == True{} : Bool}:
  match sd:
    case True{}:
      co.r(U32.is_eq(IM.tr.addr(r), x), b, i, l, cr, d, a, hb, hl, hcr)
    case False{}:
      co.l(U32.is_eq(IM.tr.addr(l), x), b, i, r, cl, d, a, hb, hr, hcl)

def cut_offn(T: IM.Tr, +x: U32, +k: U32, +d: Nat, +a: U32, +h: {IM.tr.offn(T, d, a) == True{} : Bool}) -> {IM.tr.offn(IM.tr.cut(T, x, k), d, a) == True{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      h
    case IM.Br{+b, +i, +l, +r}:
      +hlr = and_r(IM.nd.sep(d, b, a), IM.tr.offn(l, d, a) && IM.tr.offn(r, d, a), h)
      co.k(X.ix.side(k, i), b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k), d, a, and_l(IM.nd.sep(d, b, a), IM.tr.offn(l, d, a) && IM.tr.offn(r, d, a), h),
        and_l(IM.tr.offn(l, d, a), IM.tr.offn(r, d, a), hlr), and_r(IM.tr.offn(l, d, a), IM.tr.offn(r, d, a), hlr),
        cut_offn(l, x, k, d, a, and_l(IM.tr.offn(l, d, a), IM.tr.offn(r, d, a), hlr)), cut_offn(r, x, k, d, a, and_r(IM.tr.offn(l, d, a), IM.tr.offn(r, d, a), hlr)))

def root_sep(U: IM.Tr, +d: Nat, +a: U32, +h: {IM.tr.offn(U, d, a) == True{} : Bool}) -> {IM.nd.sep(d, IM.tr.addr(U), a) == True{} : Bool}:
  match U:
    case IM.Lf{+y, +ky}:
      h
    case IM.Br{+b, +i, +l, +r}:
      and_l(IM.nd.sep(d, b, a), IM.tr.offn(l, d, a) && IM.tr.offn(r, d, a), h)

def cut_eta(+c: IM.Cut) -> {c == IM.Cut{cut.lo(c), cut.pa(c), cut.si(c)} : IM.Cut}:
  match c:
    case IM.Cut{+lo, +pa, +si}:
      {==}

# the words a free after a write leaves
def fw(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +L: U32, +S: U32, +Pn: U32) ->
  {KMd.words(P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, L, S), Pn)) == Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.base(Pn), 0), (P.base(Pn) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32)) : Array<U32>}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()), (Array.set(U32, LAT.fromT(U32, t0), L, S), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), LA.get_pair(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())) :
    {KMd.words(P.free.fh(KM.m_get.fin(_), a, Pn)) == Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.base(Pn), 0), (P.base(Pn) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32)) : Array<U32>}
  {==}

def remove.br(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hreT: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Br{b, i, l, r}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s) == True{} : Bool}, +hi: {IM.tr.ok(IM.Br{b, i, l, r}, 0n) == True{} : Bool},
  +hoks: {IM.nd.ok(s, d) == True{} : Bool}, +hoffT: {IM.tr.offn(IM.Br{b, i, l, r}, d, s) == True{} : Bool}, +hlayT: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool},
  +hx: {IM.tr.look(IM.Br{b, i, l, r}, k) == Some{x} : Maybe<&2, U32>}) ->
  {IM.ix.real(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, s, IM.ix.del(IM.Has{IM.Br{b, i, l, r}}, x, k)) == True{} : Bool}:
  +hol = and_l(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hlayT))
  +hor = and_l(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hlayT)))
  +hneT = sep_ne(d, x, b, ls.k(X.ix.side(k, i), d, i, l, r, k, x, b, {==}, hx, hxl => look_sep(l, b, d, k, x, hol, hxl), hxr => look_sep(r, b, d, k, x, hor, hxr)))
  +hpb = real_addr(IM.Br{b, i, l, r}, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s, hreT)
  +hne0 = ME.subst(U32, z => {U32.is_eq(z, x) == False{} : Bool}, b, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), b, hpb), hneT)
  +hkey = look_key(IM.Br{b, i, l, r}, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s, k, x, hreT, hx)
  +hA = rmA(IM.Br{b, i, l, r}, 33n, t0, a, d, s, k, x, (s + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), 0n, hft, hd32, hreT, hi, {==}, hx, hneT)
  +hbase = MS.u32_eq_of_is_eq(P.base(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), c5(IM.Br{b, i, l, r}, x, k, (s + 3 : U32), d, hlayT, hx, hneT))
  +hfA1 = LA.set_full(U32, LAT.fromT(U32, t0), d, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), hft)
  +hfA2 = LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), d, cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0, hfA1)
  +hfA3 = LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), d, (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh())), hfA2)
  +hrB = rmB(IM.Br{b, i, l, r}, AD.view(U32, LAT.fromT(U32, t0)), d, s, k, x, (s + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh())), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))))), hreT, hx, hneT, hlayT,
    and_r(IM.tr.off(IM.Br{b, i, l, r}, d, (s + 2 : U32)), IM.tr.off(IM.Br{b, i, l, r}, d, (s + 3 : U32)), and_r(IM.tr.off(IM.Br{b, i, l, r}, d, (s + 1 : U32)), IM.tr.off(IM.Br{b, i, l, r}, d, (s + 2 : U32)) && IM.tr.off(IM.Br{b, i, l, r}, d, (s + 3 : U32)), and_r(IM.tr.off(IM.Br{b, i, l, r}, d, s), IM.tr.off(IM.Br{b, i, l, r}, d, (s + 1 : U32)) && (IM.tr.off(IM.Br{b, i, l, r}, d, (s + 2 : U32)) && IM.tr.off(IM.Br{b, i, l, r}, d, (s + 3 : U32))), onw(IM.Br{b, i, l, r}, d, s, hoffT)))),
    off3(s, d, P.at_fh(), own.fh(s, d, hoks)), {==}, cut_eta(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))),
    Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d)), LA.get_view(U32, LAT.fromT(U32, t0), d, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), hft, hd32)))
  +haddr = real_addr(IM.tr.cut(IM.Br{b, i, l, r}, x, k), List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), AD.slot(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), 0), AD.slot((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), AD.slot(P.at_fh(), d), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), d, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), AD.slot(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), 0), AD.slot((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), AD.slot(P.at_fh(), d), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), d, (s + 3 : U32)), s, hrB)
  +hns = sep_ne(d, s, IM.tr.addr(IM.tr.cut(IM.Br{b, i, l, r}, x, k)), sep_sym(d, IM.tr.addr(IM.tr.cut(IM.Br{b, i, l, r}, x, k)), s, root_sep(IM.tr.cut(IM.Br{b, i, l, r}, x, k), d, s, cut_offn(IM.Br{b, i, l, r}, x, k, d, s, hoffT))))
  %Equal.sym(Bool, U32.is_eq(b, x), False{}, hneT) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, s, IM.ix.del.k(_, IM.Br{b, i, l, r}, x, k)) == True{} : Bool}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (x + 2 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32)))), rd_eq(t0, a, (x + 2 : U32))) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.rm.x(_, s, x))), d, s, IM.Has{IM.tr.cut(IM.Br{b, i, l, r}, x, k)}) == True{} : Bool}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (s + 3 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32)))), rd_eq(t0, a, (s + 3 : U32))) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.rm.r(_, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32))), x))), d, s, IM.Has{IM.tr.cut(IM.Br{b, i, l, r}, x, k)}) == True{} : Bool}
  %wd(t0, d, (x + 2 : U32), hft, hd32) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.rm.k(U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), s, _, x))), d, s, IM.Has{IM.tr.cut(IM.Br{b, i, l, r}, x, k)}) == True{} : Bool}
  %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), k, hkey) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.rm.k(U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), s, _, x))), d, s, IM.Has{IM.tr.cut(IM.Br{b, i, l, r}, x, k)}) == True{} : Bool}
  %wd(t0, d, (s + 3 : U32), hft, hd32) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.rm.k(U32.is_eq(_, x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, s, k, x))), d, s, IM.Has{IM.tr.cut(IM.Br{b, i, l, r}, x, k)}) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), x), False{}, hne0) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.rm.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s, k, x))), d, s, IM.Has{IM.tr.cut(IM.Br{b, i, l, r}, x, k)}) == True{} : Bool}
  %Equal.sym(P.H, X.rm.h(X.rm.run(33n, X.Rm{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (s + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), True{}}, k, x)), P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), hA) : {IM.ix.real(AD.view(U32, KMd.words(_)), d, s, IM.Has{IM.tr.cut(IM.Br{b, i, l, r}, x, k)}) == True{} : Bool}
  %Equal.sym(Array<U32>, KMd.words(P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))))), Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.base(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), 0), (P.base(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), fw(t0, a, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))))) :
    {IM.ix.real(AD.view(U32, _), d, s, IM.Has{IM.tr.cut(IM.Br{b, i, l, r}, x, k)}) == True{} : Bool}
  %Equal.sym(U32, P.base(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), hbase) : {IM.ix.real(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), _, 0), (_ + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))), d, s, IM.Has{IM.tr.cut(IM.Br{b, i, l, r}, x, k)}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh())))), AD.slot(P.at_fh(), d), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), LA.set_view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), d, P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32), hfA3, hd32)) :
    {IM.ix.real(_, d, s, IM.Has{IM.tr.cut(IM.Br{b, i, l, r}, x, k)}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh())))), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0)), AD.slot((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), LA.set_view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), d, (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh())), hfA2, hd32)) :
    {IM.ix.real(List.set(&2, U32, _, AD.slot(P.at_fh(), d), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), d, s, IM.Has{IM.tr.cut(IM.Br{b, i, l, r}, x, k)}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))))), AD.slot(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), 0), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), d, cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0, hfA1, hd32)) :
    {IM.ix.real(List.set(&2, U32, List.set(&2, U32, _, AD.slot((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), AD.slot(P.at_fh(), d), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), d, s, IM.Has{IM.tr.cut(IM.Br{b, i, l, r}, x, k)}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), LA.set_view(U32, LAT.fromT(U32, t0), d, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), hft, hd32)) :
    {IM.ix.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, _, AD.slot(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), 0), AD.slot((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), AD.slot(P.at_fh(), d), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), d, s, IM.Has{IM.tr.cut(IM.Br{b, i, l, r}, x, k)}) == True{} : Bool}
  %Equal.sym(Bool, IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), AD.slot(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), 0), AD.slot((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), AD.slot(P.at_fh(), d), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), d, IM.tr.cut(IM.Br{b, i, l, r}, x, k), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), AD.slot(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), 0), AD.slot((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), AD.slot(P.at_fh(), d), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), d, (s + 3 : U32)), s), True{}, hrB) : {Bool.not(U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), AD.slot(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), 0), AD.slot((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), AD.slot(P.at_fh(), d), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), d, (s + 3 : U32)), s)) && _ == True{} : Bool}
  %Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), AD.slot(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), 0), AD.slot((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), AD.slot(P.at_fh(), d), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), d, (s + 3 : U32)), IM.tr.addr(IM.tr.cut(IM.Br{b, i, l, r}, x, k)), haddr) : {Bool.not(U32.is_eq(_, s)) && True{} == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(IM.tr.addr(IM.tr.cut(IM.Br{b, i, l, r}, x, k)), s), False{}, hns) : {Bool.not(_) && True{} == True{} : Bool}
  {==}

def remove.lf(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +y: U32, +ky: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hreT: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Lf{y, ky}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s) == True{} : Bool},
  +hx: {IM.tr.look(IM.Lf{y, ky}, k) == Some{x} : Maybe<&2, U32>}) ->
  {IM.ix.real(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, s, IM.ix.del(IM.Has{IM.Lf{y, ky}}, x, k)) == True{} : Bool}:
  +hpy = real_addr(IM.Lf{y, ky}, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s, hreT)
  +hyx = hit_some(U32.is_eq(ky, k), y, x, hx)
  +hkey = look_key(IM.Lf{y, ky}, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s, k, x, hreT, hx)
  +hyxb = ME.subst(U32, z => {U32.is_eq(z, x) == True{} : Bool}, x, y, Equal.sym(U32, y, x, hyx), is_eq_self(x))
  +heq = ME.subst(U32, z => {U32.is_eq(z, x) == True{} : Bool}, y, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), y, hpy), hyxb)
  %Equal.sym(Bool, U32.is_eq(y, x), True{}, hyxb) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, s, IM.ix.del.k(_, IM.Lf{y, ky}, x, k)) == True{} : Bool}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (x + 2 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32)))), rd_eq(t0, a, (x + 2 : U32))) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.rm.x(_, s, x))), d, s, IM.Ept{}) == True{} : Bool}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (s + 3 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32)))), rd_eq(t0, a, (s + 3 : U32))) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.rm.r(_, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32))), x))), d, s, IM.Ept{}) == True{} : Bool}
  %wd(t0, d, (x + 2 : U32), hft, hd32) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.rm.k(U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), s, _, x))), d, s, IM.Ept{}) == True{} : Bool}
  %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), k, hkey) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.rm.k(U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), s, _, x))), d, s, IM.Ept{}) == True{} : Bool}
  %wd(t0, d, (s + 3 : U32), hft, hd32) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.rm.k(U32.is_eq(_, x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, s, k, x))), d, s, IM.Ept{}) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), x), True{}, heq) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.rm.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s, k, x))), d, s, IM.Ept{}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), s), LA.set_view(U32, LAT.fromT(U32, t0), d, (s + 3 : U32), s, hft, hd32)) :
    {U32.is_eq(KMd.word(_, d, (s + 3 : U32)), s) == True{} : Bool}
  %Equal.sym(U32, KMd.word(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), s), d, (s + 3 : U32)), s, wl_eq(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32), s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d)), LA.get_view(U32, LAT.fromT(U32, t0), d, (s + 3 : U32), hft, hd32)))) :
    {U32.is_eq(_, s) == True{} : Bool}
  is_eq_self(s)

def remove.k(I: IM.Ix, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, I) == True{} : Bool}, +hi: {IM.ix.inv(I) == True{} : Bool}, +hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  +hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}) ->
  {IM.ix.real(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, s, IM.ix.del(I, x, k)) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      Empty.absurd({IM.ix.real(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, s, IM.ix.del(IM.Ept{}, x, k)) == True{} : Bool}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, m => is_some(m), None{}, Some{x}, hx)))
    case IM.Has{+t}:
      match t:
        case IM.Lf{+y, +ky}:
          remove.lf(t0, a, d, s, x, k, y, ky, hft, hd32, and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Lf{y, ky}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre), hx)
        case IM.Br{+b, +i, +l, +r}:
          remove.br(t0, a, d, s, x, k, b, i, l, r, hft, hd32, and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Br{b, i, l, r}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre), hi,
            and_l(IM.nd.ok(s, d), IM.tr.offn(IM.Br{b, i, l, r}, d, s) && IM.tr.lay(IM.Br{b, i, l, r}, d), hl), and_l(IM.tr.offn(IM.Br{b, i, l, r}, d, s), IM.tr.lay(IM.Br{b, i, l, r}, d), and_r(IM.nd.ok(s, d), IM.tr.offn(IM.Br{b, i, l, r}, d, s) && IM.tr.lay(IM.Br{b, i, l, r}, d), hl)),
            and_r(IM.tr.offn(IM.Br{b, i, l, r}, d, s), IM.tr.lay(IM.Br{b, i, l, r}, d), and_r(IM.nd.ok(s, d), IM.tr.offn(IM.Br{b, i, l, r}, d, s) && IM.tr.lay(IM.Br{b, i, l, r}, d), hl)), hx)

def remove.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +x: U32, +k: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}, hi: {IM.ix.inv(I) == True{} : Bool}, hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}, m: LAT.Mirror(U32, w)) ->
  {IM.ix.real(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{w}, a}, s, x))), d, s, IM.ix.del(I, x, k)) == True{} : Bool}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +hrt = LAB.subst(Array<U32>, q => {IM.ix.real(AD.view(U32, q), d, s, I) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e), hr)
  %e : {IM.ix.real(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{_}, a}, s, x))), d, s, IM.ix.del(I, x, k)) == True{} : Bool}
  remove.k(I, t0, a, d, s, x, k, hft, hd32, hrt, hi, hl, hx)

def Laws.remove_tree(w, a, d, s, I, x, k, hf, hd32, hr, hi, hl, hx):
  remove.m(w, a, d, s, I, x, k, hf, hd32, hr, hi, hl, hx, LAT.mirror(U32, w))

# Insert
# ======

# a branch's header, for each of the 32 bits it may test: a branch's,
# decoding to its bit, its payload in word 3; the checker's evaluation,
# case by case
def hd_ok(+c: Nat, +h: {Nat.is_lt(c, 32n) == True{} : Bool}) -> {Bool.and(X.ix.branch(X.ix.hd(c)), Bool.and(Nat.is_eq(X.ix.bitof(X.ix.hd(c)), c), U32.is_eq(P.node.word(X.ix.hd(c)), 3))) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+(+c1):
      match c1:
        case 0n:
          {==}
        case 1n+(+c2):
          match c2:
            case 0n:
              {==}
            case 1n+(+c3):
              match c3:
                case 0n:
                  {==}
                case 1n+(+c4):
                  match c4:
                    case 0n:
                      {==}
                    case 1n+(+c5):
                      match c5:
                        case 0n:
                          {==}
                        case 1n+(+c6):
                          match c6:
                            case 0n:
                              {==}
                            case 1n+(+c7):
                              match c7:
                                case 0n:
                                  {==}
                                case 1n+(+c8):
                                  match c8:
                                    case 0n:
                                      {==}
                                    case 1n+(+c9):
                                      match c9:
                                        case 0n:
                                          {==}
                                        case 1n+(+c10):
                                          match c10:
                                            case 0n:
                                              {==}
                                            case 1n+(+c11):
                                              match c11:
                                                case 0n:
                                                  {==}
                                                case 1n+(+c12):
                                                  match c12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+(+c13):
                                                      match c13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+(+c14):
                                                          match c14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+(+c15):
                                                              match c15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+(+c16):
                                                                  match c16:
                                                                    case 0n:
                                                                      {==}
                                                                    case 1n+(+c17):
                                                                      match c17:
                                                                        case 0n:
                                                                          {==}
                                                                        case 1n+(+c18):
                                                                          match c18:
                                                                            case 0n:
                                                                              {==}
                                                                            case 1n+(+c19):
                                                                              match c19:
                                                                                case 0n:
                                                                                  {==}
                                                                                case 1n+(+c20):
                                                                                  match c20:
                                                                                    case 0n:
                                                                                      {==}
                                                                                    case 1n+(+c21):
                                                                                      match c21:
                                                                                        case 0n:
                                                                                          {==}
                                                                                        case 1n+(+c22):
                                                                                          match c22:
                                                                                            case 0n:
                                                                                              {==}
                                                                                            case 1n+(+c23):
                                                                                              match c23:
                                                                                                case 0n:
                                                                                                  {==}
                                                                                                case 1n+(+c24):
                                                                                                  match c24:
                                                                                                    case 0n:
                                                                                                      {==}
                                                                                                    case 1n+(+c25):
                                                                                                      match c25:
                                                                                                        case 0n:
                                                                                                          {==}
                                                                                                        case 1n+(+c26):
                                                                                                          match c26:
                                                                                                            case 0n:
                                                                                                              {==}
                                                                                                            case 1n+(+c27):
                                                                                                              match c27:
                                                                                                                case 0n:
                                                                                                                  {==}
                                                                                                                case 1n+(+c28):
                                                                                                                  match c28:
                                                                                                                    case 0n:
                                                                                                                      {==}
                                                                                                                    case 1n+(+c29):
                                                                                                                      match c29:
                                                                                                                        case 0n:
                                                                                                                          {==}
                                                                                                                        case 1n+(+c30):
                                                                                                                          match c30:
                                                                                                                            case 0n:
                                                                                                                              {==}
                                                                                                                            case 1n+(+c31):
                                                                                                                              match c31:
                                                                                                                                case 0n:
                                                                                                                                  {==}
                                                                                                                                case 1n+(+c32):
                                                                                                                                  match c32:
                                                                                                                                    case 0n:
                                                                                                                                      Empty.absurd({Bool.and(X.ix.branch(X.ix.hd(32n)), Bool.and(Nat.is_eq(X.ix.bitof(X.ix.hd(32n)), 32n), U32.is_eq(P.node.word(X.ix.hd(32n)), 3))) == True{} : Bool}, MB.false_ne_true()(h))
                                                                                                                                    case 1n+(+c33):
                                                                                                                                      Empty.absurd({Bool.and(X.ix.branch(X.ix.hd(33n+c33)), Bool.and(Nat.is_eq(X.ix.bitof(X.ix.hd(33n+c33)), 33n+c33), U32.is_eq(P.node.word(X.ix.hd(33n+c33)), 3))) == True{} : Bool}, MB.false_ne_true()(h))

def le_refl_b(+i: Nat) -> {Nat.is_le(i, i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+(+j):
      le_refl_b(j)

def le_add_b(+q: Nat, +i: Nat) -> {Nat.is_le(i, Nat.add(q, i)) == True{} : Bool}:
  match q:
    case 0n:
      le_refl_b(i)
    case 1n+(+r):
      le_trans_b(i, Nat.add(r, i), 1n+Nat.add(r, i), le_add_b(r, i), le_succ_b(Nat.add(r, i)))

def lt_of_le(+i: Nat, +n: Nat, +h: {Nat.is_le(i, n) == True{} : Bool}) -> {Nat.is_lt(i, 1n+n) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+(+j):
      match n:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+j, 1n) == True{} : Bool}, MB.false_ne_true()(h))
        case 1n+(+m):
          lt_of_le(j, m, h)

# a scan from bit i that stopped, stopped below i plus its fuel
def crit_lt(+f: Nat, +i: Nat, +a: U32, +b: U32, +eq: Bool, +heq: {X.ix.same(X.ix.side(a, i), X.ix.side(b, i)) == eq : Bool},
  +hg: {IM.cr.go(X.ix.crit(f, X.Cr{i, True{}}, a, b)) == False{} : Bool}) ->
  {Nat.is_lt(IM.cr.i(X.ix.crit(f, X.Cr{i, True{}}, a, b)), Nat.add(f, i)) == True{} : Bool}:
  match f:
    case 0n:
      Empty.absurd({Nat.is_lt(i, i) == True{} : Bool}, MB.true_ne_false()(hg))
    case 1n+(+q):
      match eq:
        case True{}:
          %Equal.sym(Bool, X.ix.same(X.ix.side(a, i), X.ix.side(b, i)), True{}, heq) :
            {Nat.is_lt(IM.cr.i(X.ix.crit(q, X.cr.k(_, i), a, b)), 1n+Nat.add(q, i)) == True{} : Bool}
          %MN.add_succ(q, i) : {Nat.is_lt(IM.cr.i(X.ix.crit(q, X.Cr{1n+i, True{}}, a, b)), _) == True{} : Bool}
          crit_lt(q, 1n+i, a, b, X.ix.same(X.ix.side(a, 1n+i), X.ix.side(b, 1n+i)), {==},
            ME.subst(Bool, z => {IM.cr.go(X.ix.crit(q, X.cr.k(z, i), a, b)) == False{} : Bool}, X.ix.same(X.ix.side(a, i), X.ix.side(b, i)), True{}, heq, hg))
        case False{}:
          %Equal.sym(Bool, X.ix.same(X.ix.side(a, i), X.ix.side(b, i)), False{}, heq) :
            {Nat.is_lt(IM.cr.i(X.ix.crit(q, X.cr.k(_, i), a, b)), 1n+Nat.add(q, i)) == True{} : Bool}
          %Equal.sym(X.Cr, X.ix.crit(q, X.Cr{i, False{}}, a, b), X.Cr{i, False{}}, crit_stays(q, i, a, b)) :
            {Nat.is_lt(IM.cr.i(_), 1n+Nat.add(q, i)) == True{} : Bool}
          lt_of_le(i, Nat.add(q, i), le_add_b(q, i))

# the bit a scan of unequal keys stops at, below 32
def diff_lt(+a: U32, +b: U32, +hg: {IM.cr.go(X.ix.diff(a, b)) == False{} : Bool}) -> {Nat.is_lt(IM.cr.i(X.ix.diff(a, b)), 32n) == True{} : Bool}:
  crit_lt(32n, 0n, a, b, X.ix.same(X.ix.side(a, 0n), X.ix.side(b, 0n)), {==}, hg)

def cr_eta(+c: X.Cr) -> {c == X.Cr{IM.cr.i(c), IM.cr.go(c)} : X.Cr}:
  match c:
    case X.Cr{+i, +go}:
      {==}

# an insert's first descent: to the key its leaf holds (the model's near)
def dsn.k(+sd: Bool, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +b: U32, +i: Nat, +k: U32, +g: Nat, +l: IM.Tr, +r: IM.Tr, +root: U32, +x: U32, +s: U32, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +ihl: {X.ix.put.d(X.ds.run(g, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), True{}}, k), root, k, x, s) == X.ix.put.n(U32.is_eq(IM.tr.near(l, k), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.near(l, k), root, k, x, s) : P.H},
  +ihr: {X.ix.put.d(X.ds.run(g, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), True{}}, k), root, k, x, s) == X.ix.put.n(U32.is_eq(IM.tr.near(r, k), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.near(r, k), root, k, x, s) : P.H}) ->
  {X.ix.put.d(X.ds.run(g, X.ds.c(P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.kid(X.ix.side(k, i), b))), k), root, k, x, s) == X.ix.put.n(U32.is_eq(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), root, k, x, s) : P.H}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) :
        {X.ix.put.d(X.ds.run(g, X.ds.c(P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.kid(_, b))), k), root, k, x, s) == X.ix.put.n(U32.is_eq(X.ix.pick(_, IM.tr.near(r, k), IM.tr.near(l, k)), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.pick(_, IM.tr.near(r, k), IM.tr.near(l, k)), root, k, x, s) : P.H}
      %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 3 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 3 : U32)))), rd_eq(t0, a, (b + 3 : U32))) :
        {X.ix.put.d(X.ds.run(g, X.ds.c(_), k), root, k, x, s) == X.ix.put.n(U32.is_eq(IM.tr.near(r, k), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.near(r, k), root, k, x, s) : P.H}
      %wd(t0, d, (b + 3 : U32), hft, hd32) : {X.ix.put.d(X.ds.run(g, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, True{}}, k), root, k, x, s) == X.ix.put.n(U32.is_eq(IM.tr.near(r, k), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.near(r, k), root, k, x, s) : P.H}
      ihr
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) :
        {X.ix.put.d(X.ds.run(g, X.ds.c(P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.kid(_, b))), k), root, k, x, s) == X.ix.put.n(U32.is_eq(X.ix.pick(_, IM.tr.near(r, k), IM.tr.near(l, k)), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.pick(_, IM.tr.near(r, k), IM.tr.near(l, k)), root, k, x, s) : P.H}
      %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 2 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 2 : U32)))), rd_eq(t0, a, (b + 2 : U32))) :
        {X.ix.put.d(X.ds.run(g, X.ds.c(_), k), root, k, x, s) == X.ix.put.n(U32.is_eq(IM.tr.near(l, k), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.near(l, k), root, k, x, s) : P.H}
      %wd(t0, d, (b + 2 : U32), hft, hd32) : {X.ix.put.d(X.ds.run(g, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, True{}}, k), root, k, x, s) == X.ix.put.n(U32.is_eq(IM.tr.near(l, k), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.near(l, k), root, k, x, s) : P.H}
      ihl

def dsn(T: IM.Tr, f: Nat, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +k: U32, +p: U32, +lo: Nat, +root: U32, +x: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, T, p, s) == True{} : Bool}, +hok: {IM.tr.ok(T, lo) == True{} : Bool},
  +hfu: {Nat.is_le(33n, Nat.add(f, lo)) == True{} : Bool}) ->
  {X.ix.put.d(X.ds.run(f, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, p, True{}}, k), root, k, x, s) == X.ix.put.n(U32.is_eq(IM.tr.near(T, k), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.near(T, k), root, k, x, s) : P.H}:
  match T:
    case IM.Lf{+y, +ky}:
      match f:
        case 0n:
          Empty.absurd({X.ix.put.d(X.ds.run(0n, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, p, True{}}, k), root, k, x, s) == X.ix.put.n(U32.is_eq(IM.tr.near(IM.Lf{y, ky}, k), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.near(IM.Lf{y, ky}, k), root, k, x, s) : P.H}, MB.false_ne_true()(le_trans_b(33n, lo, 32n, hfu, hok)))
        case 1n+(+q):
          +h1 = and_r(U32.is_eq(p, y), Bool.not(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y))) && (U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky) && U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 3 : U32)), s)), hre)
          +h2 = and_r(Bool.not(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y))), U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky) && U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 3 : U32)), s), h1)
          +hpy = MS.u32_eq_of_is_eq(p, y, and_l(U32.is_eq(p, y), Bool.not(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y))) && (U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky) && U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 3 : U32)), s)), hre))
          +hnb = not_true(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y)), and_l(Bool.not(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y))), U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky) && U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 3 : U32)), s), h1))
          +hk2 = MS.u32_eq_of_is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky, and_l(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky), U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 3 : U32)), s), h2))
          %Equal.sym(U32, p, y, hpy) : {X.ix.put.d(X.ds.run(1n+q, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, True{}}, k), root, k, x, s) == X.ix.put.n(U32.is_eq(ky, k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, ky, root, k, x, s) : P.H}
          %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, y), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), y))), rd_eq(t0, a, y)) :
            {X.ix.put.d(X.ds.run(q, X.ds.hd(_, y, k), k), root, k, x, s) == X.ix.put.n(U32.is_eq(ky, k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, ky, root, k, x, s) : P.H}
          %wd(t0, d, y, hft, hd32) : {X.ix.put.d(X.ds.run(q, X.ds.k(X.ix.branch(_), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, y, X.ix.bitof(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), y))), k), k), root, k, x, s) == X.ix.put.n(U32.is_eq(ky, k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, ky, root, k, x, s) : P.H}
          %Equal.sym(Bool, X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y)), False{}, hnb) :
            {X.ix.put.d(X.ds.run(q, X.ds.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, y, X.ix.bitof(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), y))), k), k), root, k, x, s) == X.ix.put.n(U32.is_eq(ky, k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, ky, root, k, x, s) : P.H}
          %Equal.sym(X.Ds, X.ds.run(q, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, y, False{}}, k), X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, y, False{}}, ds_stays(q, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, y, k)) :
            {X.ix.put.d(_, root, k, x, s) == X.ix.put.n(U32.is_eq(ky, k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, ky, root, k, x, s) : P.H}
          %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (y + 2 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (y + 2 : U32)))), rd_eq(t0, a, (y + 2 : U32))) :
            {X.ix.put.l(_, root, k, x, s) == X.ix.put.n(U32.is_eq(ky, k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, ky, root, k, x, s) : P.H}
          %wd(t0, d, (y + 2 : U32), hft, hd32) : {X.ix.put.n(U32.is_eq(_, k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, root, k, x, s) == X.ix.put.n(U32.is_eq(ky, k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, ky, root, k, x, s) : P.H}
          %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky, hk2) : {X.ix.put.n(U32.is_eq(_, k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, root, k, x, s) == X.ix.put.n(U32.is_eq(ky, k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, ky, root, k, x, s) : P.H}
          {==}
    case IM.Br{+b, +i, +l, +r}:
      match f:
        case 0n:
          Empty.absurd({X.ix.put.d(X.ds.run(0n, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, p, True{}}, k), root, k, x, s) == X.ix.put.n(U32.is_eq(IM.tr.near(IM.Br{b, i, l, r}, k), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.near(IM.Br{b, i, l, r}, k), root, k, x, s) : P.H},
            MB.false_ne_true()(le_trans_b(33n, 1n+i, 32n, le_trans_b(33n, lo, 1n+i, hfu, le_trans_b(lo, i, 1n+i,
              and_l(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok), le_succ_b(i))),
              lt_le(i, 32n, and_l(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok))))))
        case 1n+(+q):
          +r1 = and_r(U32.is_eq(p, b), X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s))), hre)
          +r2 = and_r(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s)), r1)
          +r3 = and_r(Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r2)
          +o1 = and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok)
          +o4 = and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i))), o1)))
          +hpb = MS.u32_eq_of_is_eq(p, b, and_l(U32.is_eq(p, b), X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s))), hre))
          +hbr = and_l(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s)), r1)
          +hbi = MN.eq_of_is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i, and_l(Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r2))
          +hfg = fuel_down(q, lo, i, hfu, and_l(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok))
          %Equal.sym(U32, p, b, hpb) : {X.ix.put.d(X.ds.run(1n+q, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, True{}}, k), root, k, x, s) == X.ix.put.n(U32.is_eq(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), root, k, x, s) : P.H}
          %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, b), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), b))), rd_eq(t0, a, b)) :
            {X.ix.put.d(X.ds.run(q, X.ds.hd(_, b, k), k), root, k, x, s) == X.ix.put.n(U32.is_eq(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), root, k, x, s) : P.H}
          %wd(t0, d, b, hft, hd32) : {X.ix.put.d(X.ds.run(q, X.ds.k(X.ix.branch(_), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, b, X.ix.bitof(_), k), k), root, k, x, s) == X.ix.put.n(U32.is_eq(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), root, k, x, s) : P.H}
          %Equal.sym(Bool, X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), True{}, hbr) :
            {X.ix.put.d(X.ds.run(q, X.ds.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, b, X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), k), k), root, k, x, s) == X.ix.put.n(U32.is_eq(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), root, k, x, s) : P.H}
          %Equal.sym(Nat, X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i, hbi) :
            {X.ix.put.d(X.ds.run(q, X.ds.k(True{}, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, b, _, k), k), root, k, x, s) == X.ix.put.n(U32.is_eq(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), root, k, x, s) : P.H}
          dsn.k(X.ix.side(k, i), t0, a, d, b, i, k, q, l, r, root, x, s, {==}, hft, hd32,
            dsn(l, q, t0, a, d, s, k, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), 1n+i, root, x, hft, hd32, and_l(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r3), and_l(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), o4), hfg),
            dsn(r, q, t0, a, d, s, k, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), 1n+i, root, x, hft, hd32, and_r(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r3), and_r(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), o4), hfg))

# k absent from a tree: the key its descent meets is not k
def nn.k(+sd: Bool, +k: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +hsd: {X.ix.side(k, i) == sd : Bool},
  +ha: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == None{} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == None{} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.near(l, k), k) == False{} : Bool},
  ihr: {IM.tr.look(r, k) == None{} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.near(r, k), k) == False{} : Bool}) ->
  {U32.is_eq(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), k) == False{} : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {U32.is_eq(X.ix.pick(_, IM.tr.near(r, k), IM.tr.near(l, k)), k) == False{} : Bool}
      ihr(ME.subst(Bool, z => {IM.mb.pick(z, IM.tr.look(r, k), IM.tr.look(l, k)) == None{} : Maybe<&2, U32>}, X.ix.side(k, i), True{}, hsd, ha))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {U32.is_eq(X.ix.pick(_, IM.tr.near(r, k), IM.tr.near(l, k)), k) == False{} : Bool}
      ihl(ME.subst(Bool, z => {IM.mb.pick(z, IM.tr.look(r, k), IM.tr.look(l, k)) == None{} : Maybe<&2, U32>}, X.ix.side(k, i), False{}, hsd, ha))

def hit_none(+b: Bool, +y: U32, +h: {IM.mb.hit(b, y) == None{} : Maybe<&2, U32>}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MB.true_ne_false()(Equal.cong(Maybe<&2, U32>, Bool, m => is_some(m), Some{y}, None{}, h)))
    case False{}:
      {==}

def near_ne(T: IM.Tr, +k: U32, +ha: {IM.tr.look(T, k) == None{} : Maybe<&2, U32>}) -> {U32.is_eq(IM.tr.near(T, k), k) == False{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      hit_none(U32.is_eq(ky, k), y, ha)
    case IM.Br{+b, +i, +l, +r}:
      nn.k(X.ix.side(k, i), k, i, l, r, {==}, ha, hl => near_ne(l, k, hl), hr => near_ne(r, k, hr))

def plc.lo(q: IM.Plc) -> U32:
  match q:
    case IM.Plc{+loc, +cur}:
      loc

def plc.cu(q: IM.Plc) -> U32:
  match q:
    case IM.Plc{+loc, +cur}:
      cur

def pl_stays(+f: Nat, -h: P.H, +loc: U32, +cur: U32, +c: Nat, +k: U32) -> {X.pl.run(f, X.Pl{h, loc, cur, False{}}, c, k) == X.Pl{h, loc, cur, False{}} : X.Pl}:
  match f:
    case 0n:
      {==}
    case 1n+(+q):
      {==}

# a branch at bit i on the placement's way: below c, the walk goes on to
# the child k's bit gives; else it stops at the branch
def pla.k(+lt: Bool, +sd: Bool, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +b: U32, +i: Nat, +c: Nat, +k: U32, +q: Nat, +loc: U32, +l: IM.Tr, +r: IM.Tr,
  +hlt: {Nat.is_lt(i, c) == lt : Bool}, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +ihl: {X.pl.run(q, X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 2 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), True{}}, c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(l, c, k, (b + 2 : U32))), plc.cu(IM.tr.plc(l, c, k, (b + 2 : U32))), False{}} : X.Pl},
  +ihr: {X.pl.run(q, X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), True{}}, c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(r, c, k, (b + 3 : U32))), plc.cu(IM.tr.plc(r, c, k, (b + 3 : U32))), False{}} : X.Pl}) ->
  {X.pl.run(q, X.pl.k(Nat.is_lt(i, c), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, i, k), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.plc.k(Nat.is_lt(i, c), X.ix.side(k, i), b, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b)))), plc.cu(IM.plc.k(Nat.is_lt(i, c), X.ix.side(k, i), b, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b)))), False{}} : X.Pl}:
  match lt:
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(i, c), False{}, hlt) :
        {X.pl.run(q, X.pl.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, i, k), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.plc.k(_, X.ix.side(k, i), b, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b)))), plc.cu(IM.plc.k(_, X.ix.side(k, i), b, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b)))), False{}} : X.Pl}
      pl_stays(q, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, c, k)
    case True{}:
      match sd:
        case True{}:
          %Equal.sym(Bool, Nat.is_lt(i, c), True{}, hlt) :
            {X.pl.run(q, X.pl.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, i, k), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.plc.k(_, X.ix.side(k, i), b, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b)))), plc.cu(IM.plc.k(_, X.ix.side(k, i), b, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b)))), False{}} : X.Pl}
          %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) :
            {X.pl.run(q, X.pl.c(P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.kid(_, b)), X.ix.kid(_, b)), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.plc.k(True{}, _, b, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b)))), plc.cu(IM.plc.k(True{}, _, b, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b)))), False{}} : X.Pl}
          %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 3 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 3 : U32)))), rd_eq(t0, a, (b + 3 : U32))) :
            {X.pl.run(q, X.pl.c(_, (b + 3 : U32)), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(r, c, k, (b + 3 : U32))), plc.cu(IM.tr.plc(r, c, k, (b + 3 : U32))), False{}} : X.Pl}
          %wd(t0, d, (b + 3 : U32), hft, hd32) : {X.pl.run(q, X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 3 : U32), _, True{}}, c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(r, c, k, (b + 3 : U32))), plc.cu(IM.tr.plc(r, c, k, (b + 3 : U32))), False{}} : X.Pl}
          ihr
        case False{}:
          %Equal.sym(Bool, Nat.is_lt(i, c), True{}, hlt) :
            {X.pl.run(q, X.pl.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, i, k), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.plc.k(_, X.ix.side(k, i), b, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b)))), plc.cu(IM.plc.k(_, X.ix.side(k, i), b, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b)))), False{}} : X.Pl}
          %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) :
            {X.pl.run(q, X.pl.c(P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.kid(_, b)), X.ix.kid(_, b)), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.plc.k(True{}, _, b, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b)))), plc.cu(IM.plc.k(True{}, _, b, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b)))), False{}} : X.Pl}
          %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 2 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 2 : U32)))), rd_eq(t0, a, (b + 2 : U32))) :
            {X.pl.run(q, X.pl.c(_, (b + 2 : U32)), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(l, c, k, (b + 2 : U32))), plc.cu(IM.tr.plc(l, c, k, (b + 2 : U32))), False{}} : X.Pl}
          %wd(t0, d, (b + 2 : U32), hft, hd32) : {X.pl.run(q, X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 2 : U32), _, True{}}, c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(l, c, k, (b + 2 : U32))), plc.cu(IM.tr.plc(l, c, k, (b + 2 : U32))), False{}} : X.Pl}
          ihl

# the placement walk from the pointer p held at loc stops where the
# model's placement says, the heap as it was
def pla(T: IM.Tr, f: Nat, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +k: U32, +c: Nat, +loc: U32, +p: U32, +lo: Nat,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, T, p, s) == True{} : Bool}, +hok: {IM.tr.ok(T, lo) == True{} : Bool},
  +hfu: {Nat.is_le(33n, Nat.add(f, lo)) == True{} : Bool}) ->
  {X.pl.run(f, X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, p, True{}}, c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(T, c, k, loc)), plc.cu(IM.tr.plc(T, c, k, loc)), False{}} : X.Pl}:
  match T:
    case IM.Lf{+y, +ky}:
      match f:
        case 0n:
          Empty.absurd({X.pl.run(0n, X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, p, True{}}, c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(IM.Lf{y, ky}, c, k, loc)), plc.cu(IM.tr.plc(IM.Lf{y, ky}, c, k, loc)), False{}} : X.Pl}, MB.false_ne_true()(le_trans_b(33n, lo, 32n, hfu, hok)))
        case 1n+(+q):
          +h1 = and_r(U32.is_eq(p, y), Bool.not(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y))) && (U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky) && U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 3 : U32)), s)), hre)
          +hpy = MS.u32_eq_of_is_eq(p, y, and_l(U32.is_eq(p, y), Bool.not(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y))) && (U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky) && U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 3 : U32)), s)), hre))
          +hnb = not_true(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y)), and_l(Bool.not(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y))), U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky) && U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 3 : U32)), s), h1))
          %Equal.sym(U32, p, y, hpy) : {X.pl.run(1n+q, X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, _, True{}}, c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.Plc{loc, y}), plc.cu(IM.Plc{loc, y}), False{}} : X.Pl}
          %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, y), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), y))), rd_eq(t0, a, y)) :
            {X.pl.run(q, X.pl.hd(_, loc, y, c, k), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.Plc{loc, y}), plc.cu(IM.Plc{loc, y}), False{}} : X.Pl}
          %wd(t0, d, y, hft, hd32) : {X.pl.run(q, X.pl.k(X.ix.branch(_) && Nat.is_lt(X.ix.bitof(_), c), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, y, X.ix.bitof(_), k), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.Plc{loc, y}), plc.cu(IM.Plc{loc, y}), False{}} : X.Pl}
          %Equal.sym(Bool, X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y)), False{}, hnb) :
            {X.pl.run(q, X.pl.k(_ && Nat.is_lt(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y)), c), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, y, X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y)), k), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.Plc{loc, y}), plc.cu(IM.Plc{loc, y}), False{}} : X.Pl}
          pl_stays(q, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, y, c, k)
    case IM.Br{+b, +i, +l, +r}:
      match f:
        case 0n:
          Empty.absurd({X.pl.run(0n, X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, p, True{}}, c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(IM.Br{b, i, l, r}, c, k, loc)), plc.cu(IM.tr.plc(IM.Br{b, i, l, r}, c, k, loc)), False{}} : X.Pl},
            MB.false_ne_true()(le_trans_b(33n, 1n+i, 32n, le_trans_b(33n, lo, 1n+i, hfu, le_trans_b(lo, i, 1n+i,
              and_l(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok), le_succ_b(i))),
              lt_le(i, 32n, and_l(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok))))))
        case 1n+(+q):
          +r1 = and_r(U32.is_eq(p, b), X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s))), hre)
          +r2 = and_r(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s)), r1)
          +r3 = and_r(Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r2)
          +o1 = and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok)
          +o4 = and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i))), o1)))
          +hpb = MS.u32_eq_of_is_eq(p, b, and_l(U32.is_eq(p, b), X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s))), hre))
          +hbr = and_l(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s)), r1)
          +hbi = MN.eq_of_is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i, and_l(Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r2))
          +hfg = fuel_down(q, lo, i, hfu, and_l(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hok))
          %Equal.sym(U32, p, b, hpb) : {X.pl.run(1n+q, X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, _, True{}}, c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(IM.Br{b, i, l, r}, c, k, loc)), plc.cu(IM.tr.plc(IM.Br{b, i, l, r}, c, k, loc)), False{}} : X.Pl}
          %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, b), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), b))), rd_eq(t0, a, b)) :
            {X.pl.run(q, X.pl.hd(_, loc, b, c, k), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(IM.Br{b, i, l, r}, c, k, loc)), plc.cu(IM.tr.plc(IM.Br{b, i, l, r}, c, k, loc)), False{}} : X.Pl}
          %wd(t0, d, b, hft, hd32) : {X.pl.run(q, X.pl.k(X.ix.branch(_) && Nat.is_lt(X.ix.bitof(_), c), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, X.ix.bitof(_), k), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(IM.Br{b, i, l, r}, c, k, loc)), plc.cu(IM.tr.plc(IM.Br{b, i, l, r}, c, k, loc)), False{}} : X.Pl}
          %Equal.sym(Bool, X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), True{}, hbr) :
            {X.pl.run(q, X.pl.k(_ && Nat.is_lt(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), c), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), k), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(IM.Br{b, i, l, r}, c, k, loc)), plc.cu(IM.tr.plc(IM.Br{b, i, l, r}, c, k, loc)), False{}} : X.Pl}
          %Equal.sym(Nat, X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i, hbi) :
            {X.pl.run(q, X.pl.k(True{} && Nat.is_lt(_, c), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, loc, b, _, k), c, k) == X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(IM.Br{b, i, l, r}, c, k, loc)), plc.cu(IM.tr.plc(IM.Br{b, i, l, r}, c, k, loc)), False{}} : X.Pl}
          pla.k(Nat.is_lt(i, c), X.ix.side(k, i), t0, a, d, b, i, c, k, q, loc, l, r, {==}, {==}, hft, hd32,
            pla(l, q, t0, a, d, s, k, c, (b + 2 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), 1n+i, hft, hd32, and_l(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r3), and_l(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), o4), hfg),
            pla(r, q, t0, a, d, s, k, c, (b + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), 1n+i, hft, hd32, and_r(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), r3), and_r(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), o4), hfg))

# Where the placement's word lands: the word given, or a branch's
# below it

def plc2.k(+lt: Bool, +sd: Bool, +b: U32, +i: Nat, +c: Nat, +k: U32, +loc: U32, +l: IM.Tr, +r: IM.Tr, +d: Nat, +j: U32,
  +hj: {Nat.is_eq(AD.slot(j, d), AD.slot(loc, d)) == False{} : Bool},
  +ihl: {Nat.is_eq(AD.slot(j, d), AD.slot(plc.lo(IM.tr.plc(l, c, k, (b + 2 : U32))), d)) == False{} : Bool},
  +ihr: {Nat.is_eq(AD.slot(j, d), AD.slot(plc.lo(IM.tr.plc(r, c, k, (b + 3 : U32))), d)) == False{} : Bool}) ->
  {Nat.is_eq(AD.slot(j, d), AD.slot(plc.lo(IM.plc.k(lt, sd, b, loc, IM.tr.plc(l, c, k, (b + 2 : U32)), IM.tr.plc(r, c, k, (b + 3 : U32)))), d)) == False{} : Bool}:
  match lt:
    case False{}:
      hj
    case True{}:
      match sd:
        case True{}:
          ihr
        case False{}:
          ihl

def plc2(T: IM.Tr, +c: Nat, +k: U32, +loc: U32, +d: Nat, +j: U32, +ho: {IM.tr.off(T, d, j) == True{} : Bool}, +hj: {Nat.is_eq(AD.slot(j, d), AD.slot(loc, d)) == False{} : Bool}) ->
  {Nat.is_eq(AD.slot(j, d), AD.slot(plc.lo(IM.tr.plc(T, c, k, loc)), d)) == False{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      hj
    case IM.Br{+b, +i, +l, +r}:
      +hb = and_l(KMd.off.words(KMd.nw(b), d, j), IM.tr.off(l, d, j) && IM.tr.off(r, d, j), ho)
      +hlr = and_r(KMd.off.words(KMd.nw(b), d, j), IM.tr.off(l, d, j) && IM.tr.off(r, d, j), ho)
      plc2.k(Nat.is_lt(i, c), X.ix.side(k, i), b, i, c, k, loc, l, r, d, j, hj,
        plc2(l, c, k, (b + 2 : U32), d, j, and_l(IM.tr.off(l, d, j), IM.tr.off(r, d, j), hlr), off2(b, d, j, hb)),
        plc2(r, c, k, (b + 3 : U32), d, j, and_r(IM.tr.off(l, d, j), IM.tr.off(r, d, j), hlr), off3(b, d, j, hb)))

def plc34.k(+lt: Bool, +sd: Bool, +U: IM.Tr, +b: U32, +i: Nat, +c: Nat, +k: U32, +loc: U32, +l: IM.Tr, +r: IM.Tr, +d: Nat,
  +hU: {IM.tr.off(U, d, loc) == True{} : Bool},
  +ihl: {IM.tr.off(U, d, plc.lo(IM.tr.plc(l, c, k, (b + 2 : U32)))) == True{} : Bool},
  +ihr: {IM.tr.off(U, d, plc.lo(IM.tr.plc(r, c, k, (b + 3 : U32)))) == True{} : Bool}) ->
  {IM.tr.off(U, d, plc.lo(IM.plc.k(lt, sd, b, loc, IM.tr.plc(l, c, k, (b + 2 : U32)), IM.tr.plc(r, c, k, (b + 3 : U32))))) == True{} : Bool}:
  match lt:
    case False{}:
      hU
    case True{}:
      match sd:
        case True{}:
          ihr
        case False{}:
          ihl

def plc34(T: IM.Tr, +U: IM.Tr, +c: Nat, +k: U32, +loc: U32, +d: Nat, +hU: {IM.tr.off(U, d, loc) == True{} : Bool}, +ha: {IM.tr.apart(U, T, d) == True{} : Bool}) ->
  {IM.tr.off(U, d, plc.lo(IM.tr.plc(T, c, k, loc))) == True{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      hU
    case IM.Br{+b, +i, +l, +r}:
      +hab = ap_b(U, d, b, i, l, r, ha)
      +hb = onw(U, d, b, and_l(IM.tr.offn(U, d, b), IM.tr.apart(U, l, d) && IM.tr.apart(U, r, d), hab))
      +hlr = and_r(IM.tr.offn(U, d, b), IM.tr.apart(U, l, d) && IM.tr.apart(U, r, d), hab)
      +h2 = and_r(IM.tr.off(U, d, (b + 1 : U32)), IM.tr.off(U, d, (b + 2 : U32)) && IM.tr.off(U, d, (b + 3 : U32)), and_r(IM.tr.off(U, d, b), IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && IM.tr.off(U, d, (b + 3 : U32))), hb))
      plc34.k(Nat.is_lt(i, c), X.ix.side(k, i), U, b, i, c, k, loc, l, r, d, hU,
        plc34(l, U, c, k, (b + 2 : U32), d, and_l(IM.tr.off(U, d, (b + 2 : U32)), IM.tr.off(U, d, (b + 3 : U32)), h2), and_l(IM.tr.apart(U, l, d), IM.tr.apart(U, r, d), hlr)),
        plc34(r, U, c, k, (b + 3 : U32), d, and_r(IM.tr.off(U, d, (b + 2 : U32)), IM.tr.off(U, d, (b + 3 : U32)), h2), and_r(IM.tr.apart(U, l, d), IM.tr.apart(U, r, d), hlr)))

# a word written into a view that holds one there reads the value, as a
# set preserves which slots hold one
def some_map(+m: Maybe<&2, U32>, +v: U32) -> {is_some(Maybe.map(&2, U32, U32, y => v, m)) == is_some(m) : Bool}:
  match m:
    case Some{+q}:
      {==}
    case None{}:
      {==}

def some_set.k(+xs: List<&2, U32>, +i: Nat, +j: Nat, +v: U32, +e: Bool, +he: {Nat.is_eq(i, j) == e : Bool}) ->
  {is_some(List.get(&2, U32, List.set(&2, U32, xs, i, v), j)) == is_some(List.get(&2, U32, xs, j)) : Bool}:
  match e:
    case False{}:
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, xs, i, v), j), List.get(&2, U32, xs, j), LAB.get_set_ne(U32, xs, i, j, v, he)) :
        {is_some(_) == is_some(List.get(&2, U32, xs, j)) : Bool}
      {==}
    case True{}:
      ME.subst(Nat, z => {is_some(List.get(&2, U32, List.set(&2, U32, xs, z, v), j)) == is_some(List.get(&2, U32, xs, j)) : Bool}, j, i, Equal.sym(Nat, i, j, MN.eq_of_is_eq(i, j, he)),
        Equal.trans(Bool, is_some(List.get(&2, U32, List.set(&2, U32, xs, j, v), j)), is_some(Maybe.map(&2, U32, U32, y => v, List.get(&2, U32, xs, j))), is_some(List.get(&2, U32, xs, j)),
          Equal.cong(Maybe<&2, U32>, Bool, m => is_some(m), List.get(&2, U32, List.set(&2, U32, xs, j, v), j), Maybe.map(&2, U32, U32, y => v, List.get(&2, U32, xs, j)), ML.get_set_self(&2, U32, xs, j, v)),
          some_map(List.get(&2, U32, xs, j), v)))

def some_set(+xs: List<&2, U32>, +i: Nat, +j: Nat, +v: U32, +h: {is_some(List.get(&2, U32, xs, j)) == True{} : Bool}) ->
  {is_some(List.get(&2, U32, List.set(&2, U32, xs, i, v), j)) == True{} : Bool}:
  Equal.trans(Bool, is_some(List.get(&2, U32, List.set(&2, U32, xs, i, v), j)), is_some(List.get(&2, U32, xs, j)), True{}, some_set.k(xs, i, j, v, Nat.is_eq(i, j), {==}), h)

def wl_eq2.k(+m: Maybe<&2, U32>, +val: U32, +h: {is_some(m) == True{} : Bool}) -> {KMd.word.m(Maybe.map(&2, U32, U32, y => val, m)) == val : U32}:
  match m:
    case Some{+q}:
      {==}
    case None{}:
      Empty.absurd({KMd.word.m(Maybe.map(&2, U32, U32, y => val, None{})) == val : U32}, MB.false_ne_true()(h))

def wl_eq2(+v: List<&2, U32>, +d: Nat, +j: U32, +val: U32, +h: {is_some(List.get(&2, U32, v, AD.slot(j, d))) == True{} : Bool}) ->
  {KMd.word(List.set(&2, U32, v, AD.slot(j, d), val), d, j) == val : U32}:
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, AD.slot(j, d), val), AD.slot(j, d)), Maybe.map(&2, U32, U32, y => val, List.get(&2, U32, v, AD.slot(j, d))), ML.get_set_self(&2, U32, v, AD.slot(j, d), val)) :
    {KMd.word.m(_) == val : U32}
  wl_eq2.k(List.get(&2, U32, v, AD.slot(j, d)), val, h)

def offs2(+x: U32, +d: Nat, +j: U32, +h: {KMd.off.words(KMd.nw(x), d, j) == True{} : Bool}) -> {Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(j, d)) == False{} : Bool}:
  neq_comm(AD.slot(j, d), AD.slot((x + 2 : U32), d), off2(x, d, j, h))

def offs3(+x: U32, +d: Nat, +j: U32, +h: {KMd.off.words(KMd.nw(x), d, j) == True{} : Bool}) -> {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}:
  neq_comm(AD.slot(j, d), AD.slot((x + 3 : U32), d), off3(x, d, j, h))

# a node's own words, written order first
def own30(+b: U32, +d: Nat, +h: {IM.ws.apart(KMd.nw(b), d) == True{} : Bool}) -> {Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(b, d)) == False{} : Bool}:
  neq_comm(AD.slot(b, d), AD.slot((b + 3 : U32), d), own03(b, d, h))

def own20(+b: U32, +d: Nat, +h: {IM.ws.apart(KMd.nw(b), d) == True{} : Bool}) -> {Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(b, d)) == False{} : Bool}:
  neq_comm(AD.slot(b, d), AD.slot((b + 2 : U32), d), own02(b, d, h))

def own10(+b: U32, +d: Nat, +h: {IM.ws.apart(KMd.nw(b), d) == True{} : Bool}) -> {Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(b, d)) == False{} : Bool}:
  not_true(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(b, d)), and_l(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(b, d))), KMd.off.words([(b + 2 : U32), (b + 3 : U32)], d, b), own.b0(b, d, h)))

def own13(+b: U32, +d: Nat, +h: {IM.ws.apart(KMd.nw(b), d) == True{} : Bool}) -> {Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((b + 3 : U32), d)) == False{} : Bool}:
  offk(AD.slot((b + 3 : U32), d), AD.slot((b + 1 : U32), d), and_l(Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((b + 1 : U32), d))), True{},
    and_r(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((b + 1 : U32), d))), KMd.off.words([(b + 3 : U32)], d, (b + 1 : U32)),
      and_l(KMd.off.words([(b + 2 : U32), (b + 3 : U32)], d, (b + 1 : U32)), IM.ws.apart([(b + 2 : U32), (b + 3 : U32)], d),
        and_r(KMd.off.words([(b + 1 : U32), (b + 2 : U32), (b + 3 : U32)], d, b), IM.ws.apart([(b + 1 : U32), (b + 2 : U32), (b + 3 : U32)], d), h)))))

# a word through an insert's seven writes, off each, as it was
def w7(+v: List<&2, U32>, +d: Nat, +nx: U32, +H: U32, +pv: U32, +p2: U32, +L: U32, +b: U32, +x: U32, +s: U32, +j: U32, +h0: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}, +h1: {Nat.is_eq(AD.slot(b, d), AD.slot(j, d)) == False{} : Bool}, +h2: {Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, +h3: {Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(j, d)) == False{} : Bool}, +h4: {Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(j, d)) == False{} : Bool}, +h5: {Nat.is_eq(AD.slot(L, d), AD.slot(j, d)) == False{} : Bool}, +h6: {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}) -> {KMd.word(v, d, j) == KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, j) : U32}:
  Equal.trans(U32, KMd.word(v, d, j), KMd.word(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, j), wl_ne(v, d, P.at_fh(), j, nx, h0), Equal.trans(U32, KMd.word(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, j), wl_ne(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), d, b, j, H, h1), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, j), wl_ne(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, (b + 3 : U32), j, pv, h2), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, j), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, (b + 1 : U32), j, P.era(), h3), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, j), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 2 : U32), j, p2, h4), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), d, j), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, j), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, L, j, b, h5), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), d, (x + 3 : U32), j, s, h6)))))))

# a tree through them, off each, realized as it was
def r7(+T: IM.Tr, +v: List<&2, U32>, +d: Nat, +nx: U32, +H: U32, +pv: U32, +p2: U32, +L: U32, +b: U32, +x: U32, +s: U32, +p: U32, +h0: {IM.tr.off(T, d, P.at_fh()) == True{} : Bool}, +h1: {IM.tr.off(T, d, b) == True{} : Bool}, +h2: {IM.tr.off(T, d, (b + 3 : U32)) == True{} : Bool}, +h3: {IM.tr.off(T, d, (b + 1 : U32)) == True{} : Bool}, +h4: {IM.tr.off(T, d, (b + 2 : U32)) == True{} : Bool}, +h5: {IM.tr.off(T, d, L) == True{} : Bool}, +h6: {IM.tr.off(T, d, (x + 3 : U32)) == True{} : Bool}) -> {IM.tr.real(v, d, T, p, s) == IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, T, p, s) : Bool}:
  Equal.trans(Bool, IM.tr.real(v, d, T, p, s), IM.tr.real(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, T, p, s), real_set(T, v, d, P.at_fh(), nx, p, s, h0), Equal.trans(Bool, IM.tr.real(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, T, p, s), real_set(T, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), d, b, H, p, s, h1), Equal.trans(Bool, IM.tr.real(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, T, p, s), real_set(T, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, (b + 3 : U32), pv, p, s, h2), Equal.trans(Bool, IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, T, p, s), real_set(T, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, (b + 1 : U32), P.era(), p, s, h3), Equal.trans(Bool, IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, T, p, s), real_set(T, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 2 : U32), p2, p, s, h4), Equal.trans(Bool, IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), d, T, p, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, T, p, s), real_set(T, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, L, b, p, s, h5), real_set(T, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), d, (x + 3 : U32), s, p, s, h6)))))))

# The insert's realization after: where the placement stops, at the
# tree U the word loc points to, the new branch b joined above it, the
# leaf x on k's side at bit c (IM.tr.join); the writes' words and values
# parameters, tied to the model by their equations
def insJ(+sdc: Bool, +U: IM.Tr, +v: List<&2, U32>, +d: Nat, +nx: U32, +H: U32, +pv: U32, +p2: U32, +L: U32, +b: U32, +x: U32, +s: U32,
  +k: U32, +c: Nat, +loc: U32, +C: U32,
  +hsdc: {X.ix.side(k, c) == sdc : Bool}, +hL: {loc == L : U32},
  +hpv: {pv == X.ix.pick(X.ix.side(k, c), x, C) : U32}, +hp2: {p2 == X.ix.pick(X.ix.side(k, c), C, x) : U32},
  +hH1: {X.ix.branch(H) == True{} : Bool}, +hH2: {Nat.is_eq(X.ix.bitof(H), c) == True{} : Bool},
  +hre: {IM.tr.real(v, d, U, C, s) == True{} : Bool},
  +hlayU: {IM.tr.lay(U, d) == True{} : Bool}, +hlocU: {IM.tr.off(U, d, loc) == True{} : Bool},
  +hlb: {KMd.off.words(KMd.nw(b), d, loc) == True{} : Bool}, +hlx: {KMd.off.words(KMd.nw(x), d, loc) == True{} : Bool},
  +hokb: {IM.nd.ok(b, d) == True{} : Bool}, +hokx: {IM.nd.ok(x, d) == True{} : Bool}, +hsxb: {IM.nd.sep(d, x, b) == True{} : Bool},
  +hUb: {IM.tr.offn(U, d, b) == True{} : Bool}, +hUx: {IM.tr.offn(U, d, x) == True{} : Bool},
  +hnb: {X.ix.branch(KMd.word(v, d, x)) == False{} : Bool}, +hk: {KMd.word(v, d, (x + 2 : U32)) == k : U32},
  +hvL: {is_some(List.get(&2, U32, v, AD.slot(loc, d))) == True{} : Bool}, +hvb: {is_some(List.get(&2, U32, v, AD.slot(b, d))) == True{} : Bool},
  +hvb3: {is_some(List.get(&2, U32, v, AD.slot((b + 3 : U32), d))) == True{} : Bool}, +hvb2: {is_some(List.get(&2, U32, v, AD.slot((b + 2 : U32), d))) == True{} : Bool},
  +hvx3: {is_some(List.get(&2, U32, v, AD.slot((x + 3 : U32), d))) == True{} : Bool}) ->
  {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.join(X.ix.side(k, c), U, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), s) == True{} : Bool}:
  match sdc:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, c), True{}, hsdc) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.join(_, U, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), s) == True{} : Bool}
      %hL : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(_, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.join(True{}, U, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(_, d), b), AD.slot((x + 3 : U32), d), s), d, loc), s) == True{} : Bool}
      and_intro(U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, loc), b), X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b)), c) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, U, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, IM.Lf{x, k}, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), s))),
        ME.subst(U32, z => {U32.is_eq(z, b) == True{} : Bool}, b, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, loc), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, loc), b, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, loc), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, loc), b, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, loc), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, loc), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (x + 3 : U32), loc, s, offs3(x, d, loc, hlx))), wl_eq2(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, loc, b, some_set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), AD.slot(loc, d), p2, some_set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), AD.slot(loc, d), P.era(), some_set(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), AD.slot(loc, d), pv, some_set(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), AD.slot(loc, d), H, some_set(v, AD.slot(P.at_fh(), d), AD.slot(loc, d), nx, hvL)))))))), is_eq_self(b)),
        and_intro(X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b)), Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b)), c) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, U, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, IM.Lf{x, k}, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), s)),
          ME.subst(U32, z => {X.ix.branch(z) == True{} : Bool}, H, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), H, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (x + 3 : U32), b, s, off0(b, d, (x + 3 : U32), and_r(KMd.off.words(KMd.nw(b), d, (x + 2 : U32)), KMd.off.words(KMd.nw(b), d, (x + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (x + 1 : U32)), KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, x), KMd.off.words(KMd.nw(b), d, (x + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32)))), and_l(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, loc, b, b, off0(b, d, loc, hlb))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 2 : U32), b, p2, own20(b, d, own.ws(b, d, hokb)))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, (b + 1 : U32), b, P.era(), own10(b, d, own.ws(b, d, hokb)))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, (b + 3 : U32), b, pv, own30(b, d, own.ws(b, d, hokb)))), wl_eq2(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), d, b, H, some_set(v, AD.slot(P.at_fh(), d), AD.slot(b, d), nx, hvb)))))))), hH1),
          and_intro(Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b)), c), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, U, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, IM.Lf{x, k}, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), s),
            ME.subst(U32, z => {Nat.is_eq(X.ix.bitof(z), c) == True{} : Bool}, H, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), H, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (x + 3 : U32), b, s, off0(b, d, (x + 3 : U32), and_r(KMd.off.words(KMd.nw(b), d, (x + 2 : U32)), KMd.off.words(KMd.nw(b), d, (x + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (x + 1 : U32)), KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, x), KMd.off.words(KMd.nw(b), d, (x + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32)))), and_l(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, loc, b, b, off0(b, d, loc, hlb))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 2 : U32), b, p2, own20(b, d, own.ws(b, d, hokb)))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, (b + 1 : U32), b, P.era(), own10(b, d, own.ws(b, d, hokb)))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, (b + 3 : U32), b, pv, own30(b, d, own.ws(b, d, hokb)))), wl_eq2(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), d, b, H, some_set(v, AD.slot(P.at_fh(), d), AD.slot(b, d), nx, hvb)))))))), hH2),
            and_intro(IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, U, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, IM.Lf{x, k}, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), s), ME.subst(U32, z => {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, U, z, s) == True{} : Bool}, C, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), C, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), p2, C, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 2 : U32)), p2, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 2 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (x + 3 : U32), (b + 2 : U32), s, off2(b, d, (x + 3 : U32), and_r(KMd.off.words(KMd.nw(b), d, (x + 2 : U32)), KMd.off.words(KMd.nw(b), d, (x + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (x + 1 : U32)), KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, x), KMd.off.words(KMd.nw(b), d, (x + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32)))), and_l(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 2 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, (b + 2 : U32)), p2, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, (b + 2 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 2 : U32)), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, loc, (b + 2 : U32), b, off2(b, d, loc, hlb))), wl_eq2(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 2 : U32), p2, some_set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), AD.slot((b + 2 : U32), d), P.era(), some_set(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), AD.slot((b + 2 : U32), d), pv, some_set(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), AD.slot((b + 2 : U32), d), H, some_set(v, AD.slot(P.at_fh(), d), AD.slot((b + 2 : U32), d), nx, hvb2))))))), ME.subst(Bool, z => {p2 == X.ix.pick(z, C, x) : U32}, X.ix.side(k, c), True{}, hsdc, hp2))), Equal.trans(Bool, IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, U, C, s), IM.tr.real(v, d, U, C, s), True{}, Equal.sym(Bool, IM.tr.real(v, d, U, C, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, U, C, s), r7(U, v, d, nx, H, pv, p2, loc, b, x, s, C, lay_fh(U, d, hlayU), and_l(IM.tr.off(U, d, b), IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && (IM.tr.off(U, d, (b + 3 : U32)))), onw(U, d, b, hUb)), and_r(IM.tr.off(U, d, (b + 2 : U32)), IM.tr.off(U, d, (b + 3 : U32)), and_r(IM.tr.off(U, d, (b + 1 : U32)), IM.tr.off(U, d, (b + 2 : U32)) && (IM.tr.off(U, d, (b + 3 : U32))), and_r(IM.tr.off(U, d, b), IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && (IM.tr.off(U, d, (b + 3 : U32)))), onw(U, d, b, hUb)))), and_l(IM.tr.off(U, d, (b + 1 : U32)), IM.tr.off(U, d, (b + 2 : U32)) && (IM.tr.off(U, d, (b + 3 : U32))), and_r(IM.tr.off(U, d, b), IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && (IM.tr.off(U, d, (b + 3 : U32)))), onw(U, d, b, hUb))), and_l(IM.tr.off(U, d, (b + 2 : U32)), IM.tr.off(U, d, (b + 3 : U32)), and_r(IM.tr.off(U, d, (b + 1 : U32)), IM.tr.off(U, d, (b + 2 : U32)) && (IM.tr.off(U, d, (b + 3 : U32))), and_r(IM.tr.off(U, d, b), IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && (IM.tr.off(U, d, (b + 3 : U32)))), onw(U, d, b, hUb)))), hlocU, and_r(IM.tr.off(U, d, (x + 2 : U32)), IM.tr.off(U, d, (x + 3 : U32)), and_r(IM.tr.off(U, d, (x + 1 : U32)), IM.tr.off(U, d, (x + 2 : U32)) && (IM.tr.off(U, d, (x + 3 : U32))), and_r(IM.tr.off(U, d, x), IM.tr.off(U, d, (x + 1 : U32)) && (IM.tr.off(U, d, (x + 2 : U32)) && (IM.tr.off(U, d, (x + 3 : U32)))), onw(U, d, x, hUx)))))), hre)), ME.subst(U32, z => {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, IM.Lf{x, k}, z, s) == True{} : Bool}, x, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), x, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), pv, x, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 3 : U32)), pv, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (x + 3 : U32), (b + 3 : U32), s, off3(b, d, (x + 3 : U32), and_r(KMd.off.words(KMd.nw(b), d, (x + 2 : U32)), KMd.off.words(KMd.nw(b), d, (x + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (x + 1 : U32)), KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, x), KMd.off.words(KMd.nw(b), d, (x + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32)))), and_l(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, (b + 3 : U32)), pv, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 3 : U32)), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, loc, (b + 3 : U32), b, off3(b, d, loc, hlb))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 3 : U32)), pv, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, (b + 3 : U32)), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 2 : U32), (b + 3 : U32), p2, own23(b, d, own.ws(b, d, hokb)))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, (b + 3 : U32)), pv, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 3 : U32)), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, (b + 1 : U32), (b + 3 : U32), P.era(), own13(b, d, own.ws(b, d, hokb)))), wl_eq2(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, (b + 3 : U32), pv, some_set(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), AD.slot((b + 3 : U32), d), H, some_set(v, AD.slot(P.at_fh(), d), AD.slot((b + 3 : U32), d), nx, hvb3))))))), ME.subst(Bool, z => {pv == X.ix.pick(z, x, C) : U32}, X.ix.side(k, c), True{}, hsdc, hpv))), and_intro(U32.is_eq(x, x), Bool.not(X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, x))) && (U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), k) && U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), s)), is_eq_self(x),
        and_intro(Bool.not(X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, x))), U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), k) && U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), s),
          ME.subst(U32, z => {Bool.not(X.ix.branch(z)) == True{} : Bool}, KMd.word(v, d, x), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, x), w7(v, d, nx, H, pv, p2, loc, b, x, s, x, off0(x, d, P.at_fh(), own.fh(x, d, hokx)), off0(x, d, b, and_l(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))), off0(x, d, (b + 3 : U32), and_r(KMd.off.words(KMd.nw(x), d, (b + 2 : U32)), KMd.off.words(KMd.nw(x), d, (b + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (b + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))), off0(x, d, (b + 1 : U32), and_l(KMd.off.words(KMd.nw(x), d, (b + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb)))), off0(x, d, (b + 2 : U32), and_l(KMd.off.words(KMd.nw(x), d, (b + 2 : U32)), KMd.off.words(KMd.nw(x), d, (b + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (b + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))), off0(x, d, loc, hlx), own30(x, d, own.ws(x, d, hokx))), ME.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, X.ix.branch(KMd.word(v, d, x)), Equal.sym(Bool, X.ix.branch(KMd.word(v, d, x)), False{}, hnb), {==})),
          and_intro(U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), k), U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), s),
            ME.subst(U32, z => {U32.is_eq(z, k) == True{} : Bool}, k, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), Equal.trans(U32, k, KMd.word(v, d, (x + 2 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), Equal.sym(U32, KMd.word(v, d, (x + 2 : U32)), k, hk), w7(v, d, nx, H, pv, p2, loc, b, x, s, (x + 2 : U32), off2(x, d, P.at_fh(), own.fh(x, d, hokx)), off2(x, d, b, and_l(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))), off2(x, d, (b + 3 : U32), and_r(KMd.off.words(KMd.nw(x), d, (b + 2 : U32)), KMd.off.words(KMd.nw(x), d, (b + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (b + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))), off2(x, d, (b + 1 : U32), and_l(KMd.off.words(KMd.nw(x), d, (b + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb)))), off2(x, d, (b + 2 : U32), and_l(KMd.off.words(KMd.nw(x), d, (b + 2 : U32)), KMd.off.words(KMd.nw(x), d, (b + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (b + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))), off2(x, d, loc, hlx), own32(x, d, own.ws(x, d, hokx)))), is_eq_self(k)),
            ME.subst(U32, z => {U32.is_eq(z, s) == True{} : Bool}, s, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), s, wl_eq2(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (x + 3 : U32), s, some_set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), AD.slot((x + 3 : U32), d), b, some_set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), AD.slot((x + 3 : U32), d), p2, some_set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), AD.slot((x + 3 : U32), d), P.era(), some_set(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), AD.slot((x + 3 : U32), d), pv, some_set(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), AD.slot((x + 3 : U32), d), H, some_set(v, AD.slot(P.at_fh(), d), AD.slot((x + 3 : U32), d), nx, hvx3)))))))), is_eq_self(s))))))))))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, c), False{}, hsdc) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.join(_, U, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), s) == True{} : Bool}
      %hL : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(_, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.join(False{}, U, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(_, d), b), AD.slot((x + 3 : U32), d), s), d, loc), s) == True{} : Bool}
      and_intro(U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, loc), b), X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b)), c) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, IM.Lf{x, k}, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, U, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), s))),
        ME.subst(U32, z => {U32.is_eq(z, b) == True{} : Bool}, b, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, loc), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, loc), b, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, loc), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, loc), b, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, loc), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, loc), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (x + 3 : U32), loc, s, offs3(x, d, loc, hlx))), wl_eq2(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, loc, b, some_set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), AD.slot(loc, d), p2, some_set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), AD.slot(loc, d), P.era(), some_set(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), AD.slot(loc, d), pv, some_set(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), AD.slot(loc, d), H, some_set(v, AD.slot(P.at_fh(), d), AD.slot(loc, d), nx, hvL)))))))), is_eq_self(b)),
        and_intro(X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b)), Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b)), c) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, IM.Lf{x, k}, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, U, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), s)),
          ME.subst(U32, z => {X.ix.branch(z) == True{} : Bool}, H, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), H, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (x + 3 : U32), b, s, off0(b, d, (x + 3 : U32), and_r(KMd.off.words(KMd.nw(b), d, (x + 2 : U32)), KMd.off.words(KMd.nw(b), d, (x + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (x + 1 : U32)), KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, x), KMd.off.words(KMd.nw(b), d, (x + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32)))), and_l(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, loc, b, b, off0(b, d, loc, hlb))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 2 : U32), b, p2, own20(b, d, own.ws(b, d, hokb)))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, (b + 1 : U32), b, P.era(), own10(b, d, own.ws(b, d, hokb)))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, (b + 3 : U32), b, pv, own30(b, d, own.ws(b, d, hokb)))), wl_eq2(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), d, b, H, some_set(v, AD.slot(P.at_fh(), d), AD.slot(b, d), nx, hvb)))))))), hH1),
          and_intro(Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b)), c), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, IM.Lf{x, k}, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, U, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), s),
            ME.subst(U32, z => {Nat.is_eq(X.ix.bitof(z), c) == True{} : Bool}, H, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), H, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (x + 3 : U32), b, s, off0(b, d, (x + 3 : U32), and_r(KMd.off.words(KMd.nw(b), d, (x + 2 : U32)), KMd.off.words(KMd.nw(b), d, (x + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (x + 1 : U32)), KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, x), KMd.off.words(KMd.nw(b), d, (x + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32)))), and_l(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, loc, b, b, off0(b, d, loc, hlb))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 2 : U32), b, p2, own20(b, d, own.ws(b, d, hokb)))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, (b + 1 : U32), b, P.era(), own10(b, d, own.ws(b, d, hokb)))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, b), H, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, b), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, b), wl_ne(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, (b + 3 : U32), b, pv, own30(b, d, own.ws(b, d, hokb)))), wl_eq2(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), d, b, H, some_set(v, AD.slot(P.at_fh(), d), AD.slot(b, d), nx, hvb)))))))), hH2),
            and_intro(IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, IM.Lf{x, k}, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, U, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), s), ME.subst(U32, z => {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, IM.Lf{x, k}, z, s) == True{} : Bool}, x, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), x, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), p2, x, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 2 : U32)), p2, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 2 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 2 : U32)), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (x + 3 : U32), (b + 2 : U32), s, off2(b, d, (x + 3 : U32), and_r(KMd.off.words(KMd.nw(b), d, (x + 2 : U32)), KMd.off.words(KMd.nw(b), d, (x + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (x + 1 : U32)), KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, x), KMd.off.words(KMd.nw(b), d, (x + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32)))), and_l(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 2 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, (b + 2 : U32)), p2, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, (b + 2 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 2 : U32)), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, loc, (b + 2 : U32), b, off2(b, d, loc, hlb))), wl_eq2(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 2 : U32), p2, some_set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), AD.slot((b + 2 : U32), d), P.era(), some_set(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), AD.slot((b + 2 : U32), d), pv, some_set(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), AD.slot((b + 2 : U32), d), H, some_set(v, AD.slot(P.at_fh(), d), AD.slot((b + 2 : U32), d), nx, hvb2))))))), ME.subst(Bool, z => {p2 == X.ix.pick(z, C, x) : U32}, X.ix.side(k, c), False{}, hsdc, hp2))), and_intro(U32.is_eq(x, x), Bool.not(X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, x))) && (U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), k) && U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), s)), is_eq_self(x),
        and_intro(Bool.not(X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, x))), U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), k) && U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), s),
          ME.subst(U32, z => {Bool.not(X.ix.branch(z)) == True{} : Bool}, KMd.word(v, d, x), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, x), w7(v, d, nx, H, pv, p2, loc, b, x, s, x, off0(x, d, P.at_fh(), own.fh(x, d, hokx)), off0(x, d, b, and_l(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))), off0(x, d, (b + 3 : U32), and_r(KMd.off.words(KMd.nw(x), d, (b + 2 : U32)), KMd.off.words(KMd.nw(x), d, (b + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (b + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))), off0(x, d, (b + 1 : U32), and_l(KMd.off.words(KMd.nw(x), d, (b + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb)))), off0(x, d, (b + 2 : U32), and_l(KMd.off.words(KMd.nw(x), d, (b + 2 : U32)), KMd.off.words(KMd.nw(x), d, (b + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (b + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))), off0(x, d, loc, hlx), own30(x, d, own.ws(x, d, hokx))), ME.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, X.ix.branch(KMd.word(v, d, x)), Equal.sym(Bool, X.ix.branch(KMd.word(v, d, x)), False{}, hnb), {==})),
          and_intro(U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), k), U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), s),
            ME.subst(U32, z => {U32.is_eq(z, k) == True{} : Bool}, k, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), Equal.trans(U32, k, KMd.word(v, d, (x + 2 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), Equal.sym(U32, KMd.word(v, d, (x + 2 : U32)), k, hk), w7(v, d, nx, H, pv, p2, loc, b, x, s, (x + 2 : U32), off2(x, d, P.at_fh(), own.fh(x, d, hokx)), off2(x, d, b, and_l(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))), off2(x, d, (b + 3 : U32), and_r(KMd.off.words(KMd.nw(x), d, (b + 2 : U32)), KMd.off.words(KMd.nw(x), d, (b + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (b + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))), off2(x, d, (b + 1 : U32), and_l(KMd.off.words(KMd.nw(x), d, (b + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb)))), off2(x, d, (b + 2 : U32), and_l(KMd.off.words(KMd.nw(x), d, (b + 2 : U32)), KMd.off.words(KMd.nw(x), d, (b + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (b + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b), KMd.off.words(KMd.nw(x), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b + 3 : U32)))), and_r(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))), off2(x, d, loc, hlx), own32(x, d, own.ws(x, d, hokx)))), is_eq_self(k)),
            ME.subst(U32, z => {U32.is_eq(z, s) == True{} : Bool}, s, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), s, wl_eq2(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (x + 3 : U32), s, some_set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), AD.slot((x + 3 : U32), d), b, some_set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), AD.slot((x + 3 : U32), d), p2, some_set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), AD.slot((x + 3 : U32), d), P.era(), some_set(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), AD.slot((x + 3 : U32), d), pv, some_set(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), AD.slot((x + 3 : U32), d), H, some_set(v, AD.slot(P.at_fh(), d), AD.slot((x + 3 : U32), d), nx, hvx3)))))))), is_eq_self(s)))))), ME.subst(U32, z => {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, U, z, s) == True{} : Bool}, C, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), C, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), pv, C, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 3 : U32)), pv, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, (b + 3 : U32)), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (x + 3 : U32), (b + 3 : U32), s, off3(b, d, (x + 3 : U32), and_r(KMd.off.words(KMd.nw(b), d, (x + 2 : U32)), KMd.off.words(KMd.nw(b), d, (x + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (x + 1 : U32)), KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, x), KMd.off.words(KMd.nw(b), d, (x + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (x + 3 : U32)))), and_l(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb))))))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, (b + 3 : U32)), pv, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), d, (b + 3 : U32)), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, loc, (b + 3 : U32), b, off3(b, d, loc, hlb))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 3 : U32)), pv, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), d, (b + 3 : U32)), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 2 : U32), (b + 3 : U32), p2, own23(b, d, own.ws(b, d, hokb)))), Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, (b + 3 : U32)), pv, Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, (b + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), d, (b + 3 : U32)), wl_ne(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), d, (b + 1 : U32), (b + 3 : U32), P.era(), own13(b, d, own.ws(b, d, hokb)))), wl_eq2(List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), d, (b + 3 : U32), pv, some_set(List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), AD.slot((b + 3 : U32), d), H, some_set(v, AD.slot(P.at_fh(), d), AD.slot((b + 3 : U32), d), nx, hvb3))))))), ME.subst(Bool, z => {pv == X.ix.pick(z, x, C) : U32}, X.ix.side(k, c), False{}, hsdc, hpv))), Equal.trans(Bool, IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, U, C, s), IM.tr.real(v, d, U, C, s), True{}, Equal.sym(Bool, IM.tr.real(v, d, U, C, s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, v, AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(loc, d), b), AD.slot((x + 3 : U32), d), s), d, U, C, s), r7(U, v, d, nx, H, pv, p2, loc, b, x, s, C, lay_fh(U, d, hlayU), and_l(IM.tr.off(U, d, b), IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && (IM.tr.off(U, d, (b + 3 : U32)))), onw(U, d, b, hUb)), and_r(IM.tr.off(U, d, (b + 2 : U32)), IM.tr.off(U, d, (b + 3 : U32)), and_r(IM.tr.off(U, d, (b + 1 : U32)), IM.tr.off(U, d, (b + 2 : U32)) && (IM.tr.off(U, d, (b + 3 : U32))), and_r(IM.tr.off(U, d, b), IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && (IM.tr.off(U, d, (b + 3 : U32)))), onw(U, d, b, hUb)))), and_l(IM.tr.off(U, d, (b + 1 : U32)), IM.tr.off(U, d, (b + 2 : U32)) && (IM.tr.off(U, d, (b + 3 : U32))), and_r(IM.tr.off(U, d, b), IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && (IM.tr.off(U, d, (b + 3 : U32)))), onw(U, d, b, hUb))), and_l(IM.tr.off(U, d, (b + 2 : U32)), IM.tr.off(U, d, (b + 3 : U32)), and_r(IM.tr.off(U, d, (b + 1 : U32)), IM.tr.off(U, d, (b + 2 : U32)) && (IM.tr.off(U, d, (b + 3 : U32))), and_r(IM.tr.off(U, d, b), IM.tr.off(U, d, (b + 1 : U32)) && (IM.tr.off(U, d, (b + 2 : U32)) && (IM.tr.off(U, d, (b + 3 : U32)))), onw(U, d, b, hUb)))), hlocU, and_r(IM.tr.off(U, d, (x + 2 : U32)), IM.tr.off(U, d, (x + 3 : U32)), and_r(IM.tr.off(U, d, (x + 1 : U32)), IM.tr.off(U, d, (x + 2 : U32)) && (IM.tr.off(U, d, (x + 3 : U32))), and_r(IM.tr.off(U, d, x), IM.tr.off(U, d, (x + 1 : U32)) && (IM.tr.off(U, d, (x + 2 : U32)) && (IM.tr.off(U, d, (x + 3 : U32)))), onw(U, d, x, hUx)))))), hre))))))

def vs(+t0: LAT.Tree<U32>, +d: Nat, +j: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
  {is_some(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(j, d))) == True{} : Bool}:
  %LA.get_view(U32, LAT.fromT(U32, t0), d, j, hft, hd32) : {is_some(_) == True{} : Bool}
  {==}

def insD.r(+t0: LAT.Tree<U32>, +d: Nat, +nx: U32, +H: U32, +pv: U32, +p2: U32, +L: U32, +b: U32, +x: U32, +s: U32, +k: U32, +c: Nat, +C: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hpv: {pv == X.ix.pick(X.ix.side(k, c), x, C) : U32}, +hp2: {p2 == X.ix.pick(X.ix.side(k, c), C, x) : U32},
  +hH1: {X.ix.branch(H) == True{} : Bool}, +hH2: {Nat.is_eq(X.ix.bitof(H), c) == True{} : Bool},
  +hokb: {IM.nd.ok(b, d) == True{} : Bool}, +hokx: {IM.nd.ok(x, d) == True{} : Bool}, +hsxb: {IM.nd.sep(d, x, b) == True{} : Bool},
  +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool}, +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32},
  +loc: U32, +b2: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr,
  +hp: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, loc) == b2 : U32}, +hbr: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2)) == True{} : Bool}, +hbi: {Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2)), i) == True{} : Bool},
  +hrl: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s) == True{} : Bool}, +hrr: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s) == True{} : Bool},
  +hokb2: {IM.nd.ok(b2, d) == True{} : Bool}, +hol: {IM.tr.offn(l, d, b2) == True{} : Bool}, +hor: {IM.tr.offn(r, d, b2) == True{} : Bool},
  +hap: {IM.tr.apart(l, r, d) == True{} : Bool}, +hlay_l: {IM.tr.lay(l, d) == True{} : Bool}, +hlay_r: {IM.tr.lay(r, d) == True{} : Bool},
  +hlb2: {KMd.off.words(KMd.nw(b2), d, loc) == True{} : Bool}, +hll: {IM.tr.off(l, d, loc) == True{} : Bool}, +hlr: {IM.tr.off(r, d, loc) == True{} : Bool}, +hlf: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(loc, d)) == False{} : Bool},
  +hlb: {KMd.off.words(KMd.nw(b), d, loc) == True{} : Bool}, +hlx: {KMd.off.words(KMd.nw(x), d, loc) == True{} : Bool},
  +hsb: {IM.nd.sep(d, b2, b) == True{} : Bool}, +hlb_: {IM.tr.offn(l, d, b) == True{} : Bool}, +hrb_: {IM.tr.offn(r, d, b) == True{} : Bool},
  +hsx: {IM.nd.sep(d, b2, x) == True{} : Bool}, +hlx_: {IM.tr.offn(l, d, x) == True{} : Bool}, +hrx_: {IM.tr.offn(r, d, x) == True{} : Bool},
  +hcc: {IM.tr.plc(r, c, k, (b2 + 3 : U32)) == IM.Plc{L, C} : IM.Plc},
  +ih: {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place(r, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 3 : U32)), s) == True{} : Bool}) ->
  {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.Br{b2, i, l, IM.tr.place(r, x, k, b, c)}, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), s) == True{} : Bool}:
  and_intro(U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), b2), X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, b2)) && (Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, b2)), i) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, l, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place(r, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 3 : U32)), s))),
    ME.subst(U32, z => {U32.is_eq(z, b2) == True{} : Bool}, b2, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), Equal.trans(U32, b2, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, loc), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, loc), b2, hp), w7(AD.view(U32, LAT.fromT(U32, t0)), d, nx, H, pv, p2, L, b, x, s, loc, hlf, offs0(b, d, loc, hlb), offs3(b, d, loc, hlb), offs1(b, d, loc, hlb), offs2(b, d, loc, hlb), neq_comm(AD.slot(loc, d), AD.slot(L, d), ME.subst(IM.Plc, z => {Nat.is_eq(AD.slot(loc, d), AD.slot(plc.lo(z), d)) == False{} : Bool}, IM.tr.plc(r, c, k, (b2 + 3 : U32)), IM.Plc{L, C}, hcc, plc2(r, c, k, (b2 + 3 : U32), d, loc, hlr, off3(b2, d, loc, hlb2)))), offs3(x, d, loc, hlx))), is_eq_self(b2)),
    and_intro(X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, b2)), Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, b2)), i) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, l, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place(r, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 3 : U32)), s)),
      ME.subst(U32, z => {X.ix.branch(z) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, b2), w7(AD.view(U32, LAT.fromT(U32, t0)), d, nx, H, pv, p2, L, b, x, s, b2, off0(b2, d, P.at_fh(), own.fh(b2, d, hokb2)), offs0(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), offs3(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), offs1(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), offs2(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), neq_comm(AD.slot(b2, d), AD.slot(L, d), ME.subst(IM.Plc, z => {Nat.is_eq(AD.slot(b2, d), AD.slot(plc.lo(z), d)) == False{} : Bool}, IM.tr.plc(r, c, k, (b2 + 3 : U32)), IM.Plc{L, C}, hcc, plc2(r, c, k, (b2 + 3 : U32), d, b2, and_l(IM.tr.off(r, d, b2), IM.tr.off(r, d, (b2 + 1 : U32)) && (IM.tr.off(r, d, (b2 + 2 : U32)) && (IM.tr.off(r, d, (b2 + 3 : U32)))), onw(r, d, b2, hor)), own03(b2, d, own.ws(b2, d, hokb2))))), offs3(x, d, b2, and_l(KMd.off.words(KMd.nw(x), d, b2), KMd.off.words(KMd.nw(x), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, x), IM.nd.disj(d, x, b2), hsx)))), hbr),
      and_intro(Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, b2)), i), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, l, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place(r, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 3 : U32)), s),
        ME.subst(U32, z => {Nat.is_eq(X.ix.bitof(z), i) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, b2), w7(AD.view(U32, LAT.fromT(U32, t0)), d, nx, H, pv, p2, L, b, x, s, b2, off0(b2, d, P.at_fh(), own.fh(b2, d, hokb2)), offs0(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), offs3(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), offs1(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), offs2(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), neq_comm(AD.slot(b2, d), AD.slot(L, d), ME.subst(IM.Plc, z => {Nat.is_eq(AD.slot(b2, d), AD.slot(plc.lo(z), d)) == False{} : Bool}, IM.tr.plc(r, c, k, (b2 + 3 : U32)), IM.Plc{L, C}, hcc, plc2(r, c, k, (b2 + 3 : U32), d, b2, and_l(IM.tr.off(r, d, b2), IM.tr.off(r, d, (b2 + 1 : U32)) && (IM.tr.off(r, d, (b2 + 2 : U32)) && (IM.tr.off(r, d, (b2 + 3 : U32)))), onw(r, d, b2, hor)), own03(b2, d, own.ws(b2, d, hokb2))))), offs3(x, d, b2, and_l(KMd.off.words(KMd.nw(x), d, b2), KMd.off.words(KMd.nw(x), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, x), IM.nd.disj(d, x, b2), hsx)))), hbi),
        and_intro(IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, l, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 2 : U32)), s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place(r, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 3 : U32)), s), ME.subst(U32, z => {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, l, z, s) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 2 : U32)), w7(AD.view(U32, LAT.fromT(U32, t0)), d, nx, H, pv, p2, L, b, x, s, (b2 + 2 : U32), off2(b2, d, P.at_fh(), own.fh(b2, d, hokb2)), offs0(b, d, (b2 + 2 : U32), and_l(KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))))), offs3(b, d, (b2 + 2 : U32), and_l(KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))))), offs1(b, d, (b2 + 2 : U32), and_l(KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))))), offs2(b, d, (b2 + 2 : U32), and_l(KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))))), neq_comm(AD.slot((b2 + 2 : U32), d), AD.slot(L, d), ME.subst(IM.Plc, z => {Nat.is_eq(AD.slot((b2 + 2 : U32), d), AD.slot(plc.lo(z), d)) == False{} : Bool}, IM.tr.plc(r, c, k, (b2 + 3 : U32)), IM.Plc{L, C}, hcc, plc2(r, c, k, (b2 + 3 : U32), d, (b2 + 2 : U32), and_l(IM.tr.off(r, d, (b2 + 2 : U32)), IM.tr.off(r, d, (b2 + 3 : U32)), and_r(IM.tr.off(r, d, (b2 + 1 : U32)), IM.tr.off(r, d, (b2 + 2 : U32)) && (IM.tr.off(r, d, (b2 + 3 : U32))), and_r(IM.tr.off(r, d, b2), IM.tr.off(r, d, (b2 + 1 : U32)) && (IM.tr.off(r, d, (b2 + 2 : U32)) && (IM.tr.off(r, d, (b2 + 3 : U32)))), onw(r, d, b2, hor)))), own23(b2, d, own.ws(b2, d, hokb2))))), offs3(x, d, (b2 + 2 : U32), and_l(KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)), KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (b2 + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b2), KMd.off.words(KMd.nw(x), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, x), IM.nd.disj(d, x, b2), hsx)))))), Equal.trans(Bool, IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s), True{}, Equal.sym(Bool, IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s), r7(l, AD.view(U32, LAT.fromT(U32, t0)), d, nx, H, pv, p2, L, b, x, s, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), lay_fh(l, d, hlay_l), and_l(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hlb_)), and_r(IM.tr.off(l, d, (b + 2 : U32)), IM.tr.off(l, d, (b + 3 : U32)), and_r(IM.tr.off(l, d, (b + 1 : U32)), IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32))), and_r(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hlb_)))), and_l(IM.tr.off(l, d, (b + 1 : U32)), IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32))), and_r(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hlb_))), and_l(IM.tr.off(l, d, (b + 2 : U32)), IM.tr.off(l, d, (b + 3 : U32)), and_r(IM.tr.off(l, d, (b + 1 : U32)), IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32))), and_r(IM.tr.off(l, d, b), IM.tr.off(l, d, (b + 1 : U32)) && (IM.tr.off(l, d, (b + 2 : U32)) && (IM.tr.off(l, d, (b + 3 : U32)))), onw(l, d, b, hlb_)))), ME.subst(IM.Plc, z => {IM.tr.off(l, d, plc.lo(z)) == True{} : Bool}, IM.tr.plc(r, c, k, (b2 + 3 : U32)), IM.Plc{L, C}, hcc, plc34(r, l, c, k, (b2 + 3 : U32), d, and_r(IM.tr.off(l, d, (b2 + 2 : U32)), IM.tr.off(l, d, (b2 + 3 : U32)), and_r(IM.tr.off(l, d, (b2 + 1 : U32)), IM.tr.off(l, d, (b2 + 2 : U32)) && (IM.tr.off(l, d, (b2 + 3 : U32))), and_r(IM.tr.off(l, d, b2), IM.tr.off(l, d, (b2 + 1 : U32)) && (IM.tr.off(l, d, (b2 + 2 : U32)) && (IM.tr.off(l, d, (b2 + 3 : U32)))), onw(l, d, b2, hol)))), hap)), and_r(IM.tr.off(l, d, (x + 2 : U32)), IM.tr.off(l, d, (x + 3 : U32)), and_r(IM.tr.off(l, d, (x + 1 : U32)), IM.tr.off(l, d, (x + 2 : U32)) && (IM.tr.off(l, d, (x + 3 : U32))), and_r(IM.tr.off(l, d, x), IM.tr.off(l, d, (x + 1 : U32)) && (IM.tr.off(l, d, (x + 2 : U32)) && (IM.tr.off(l, d, (x + 3 : U32)))), onw(l, d, x, hlx_)))))), hrl)), ih))))

def insD.l(+t0: LAT.Tree<U32>, +d: Nat, +nx: U32, +H: U32, +pv: U32, +p2: U32, +L: U32, +b: U32, +x: U32, +s: U32, +k: U32, +c: Nat, +C: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hpv: {pv == X.ix.pick(X.ix.side(k, c), x, C) : U32}, +hp2: {p2 == X.ix.pick(X.ix.side(k, c), C, x) : U32},
  +hH1: {X.ix.branch(H) == True{} : Bool}, +hH2: {Nat.is_eq(X.ix.bitof(H), c) == True{} : Bool},
  +hokb: {IM.nd.ok(b, d) == True{} : Bool}, +hokx: {IM.nd.ok(x, d) == True{} : Bool}, +hsxb: {IM.nd.sep(d, x, b) == True{} : Bool},
  +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool}, +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32},
  +loc: U32, +b2: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr,
  +hp: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, loc) == b2 : U32}, +hbr: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2)) == True{} : Bool}, +hbi: {Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2)), i) == True{} : Bool},
  +hrl: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s) == True{} : Bool}, +hrr: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s) == True{} : Bool},
  +hokb2: {IM.nd.ok(b2, d) == True{} : Bool}, +hol: {IM.tr.offn(l, d, b2) == True{} : Bool}, +hor: {IM.tr.offn(r, d, b2) == True{} : Bool},
  +hap: {IM.tr.apart(l, r, d) == True{} : Bool}, +hlay_l: {IM.tr.lay(l, d) == True{} : Bool}, +hlay_r: {IM.tr.lay(r, d) == True{} : Bool},
  +hlb2: {KMd.off.words(KMd.nw(b2), d, loc) == True{} : Bool}, +hll: {IM.tr.off(l, d, loc) == True{} : Bool}, +hlr: {IM.tr.off(r, d, loc) == True{} : Bool}, +hlf: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(loc, d)) == False{} : Bool},
  +hlb: {KMd.off.words(KMd.nw(b), d, loc) == True{} : Bool}, +hlx: {KMd.off.words(KMd.nw(x), d, loc) == True{} : Bool},
  +hsb: {IM.nd.sep(d, b2, b) == True{} : Bool}, +hlb_: {IM.tr.offn(l, d, b) == True{} : Bool}, +hrb_: {IM.tr.offn(r, d, b) == True{} : Bool},
  +hsx: {IM.nd.sep(d, b2, x) == True{} : Bool}, +hlx_: {IM.tr.offn(l, d, x) == True{} : Bool}, +hrx_: {IM.tr.offn(r, d, x) == True{} : Bool},
  +hcc: {IM.tr.plc(l, c, k, (b2 + 2 : U32)) == IM.Plc{L, C} : IM.Plc},
  +ih: {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place(l, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 2 : U32)), s) == True{} : Bool}) ->
  {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.Br{b2, i, IM.tr.place(l, x, k, b, c), r}, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), s) == True{} : Bool}:
  and_intro(U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), b2), X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, b2)) && (Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, b2)), i) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place(l, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, r, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 3 : U32)), s))),
    ME.subst(U32, z => {U32.is_eq(z, b2) == True{} : Bool}, b2, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), Equal.trans(U32, b2, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, loc), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, loc), b2, hp), w7(AD.view(U32, LAT.fromT(U32, t0)), d, nx, H, pv, p2, L, b, x, s, loc, hlf, offs0(b, d, loc, hlb), offs3(b, d, loc, hlb), offs1(b, d, loc, hlb), offs2(b, d, loc, hlb), neq_comm(AD.slot(loc, d), AD.slot(L, d), ME.subst(IM.Plc, z => {Nat.is_eq(AD.slot(loc, d), AD.slot(plc.lo(z), d)) == False{} : Bool}, IM.tr.plc(l, c, k, (b2 + 2 : U32)), IM.Plc{L, C}, hcc, plc2(l, c, k, (b2 + 2 : U32), d, loc, hll, off2(b2, d, loc, hlb2)))), offs3(x, d, loc, hlx))), is_eq_self(b2)),
    and_intro(X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, b2)), Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, b2)), i) && (IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place(l, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, r, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 3 : U32)), s)),
      ME.subst(U32, z => {X.ix.branch(z) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, b2), w7(AD.view(U32, LAT.fromT(U32, t0)), d, nx, H, pv, p2, L, b, x, s, b2, off0(b2, d, P.at_fh(), own.fh(b2, d, hokb2)), offs0(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), offs3(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), offs1(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), offs2(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), neq_comm(AD.slot(b2, d), AD.slot(L, d), ME.subst(IM.Plc, z => {Nat.is_eq(AD.slot(b2, d), AD.slot(plc.lo(z), d)) == False{} : Bool}, IM.tr.plc(l, c, k, (b2 + 2 : U32)), IM.Plc{L, C}, hcc, plc2(l, c, k, (b2 + 2 : U32), d, b2, and_l(IM.tr.off(l, d, b2), IM.tr.off(l, d, (b2 + 1 : U32)) && (IM.tr.off(l, d, (b2 + 2 : U32)) && (IM.tr.off(l, d, (b2 + 3 : U32)))), onw(l, d, b2, hol)), own02(b2, d, own.ws(b2, d, hokb2))))), offs3(x, d, b2, and_l(KMd.off.words(KMd.nw(x), d, b2), KMd.off.words(KMd.nw(x), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, x), IM.nd.disj(d, x, b2), hsx)))), hbr),
      and_intro(Nat.is_eq(X.ix.bitof(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, b2)), i), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place(l, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 2 : U32)), s) && IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, r, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 3 : U32)), s),
        ME.subst(U32, z => {Nat.is_eq(X.ix.bitof(z), i) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, b2), w7(AD.view(U32, LAT.fromT(U32, t0)), d, nx, H, pv, p2, L, b, x, s, b2, off0(b2, d, P.at_fh(), own.fh(b2, d, hokb2)), offs0(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), offs3(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), offs1(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), offs2(b, d, b2, and_l(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))), neq_comm(AD.slot(b2, d), AD.slot(L, d), ME.subst(IM.Plc, z => {Nat.is_eq(AD.slot(b2, d), AD.slot(plc.lo(z), d)) == False{} : Bool}, IM.tr.plc(l, c, k, (b2 + 2 : U32)), IM.Plc{L, C}, hcc, plc2(l, c, k, (b2 + 2 : U32), d, b2, and_l(IM.tr.off(l, d, b2), IM.tr.off(l, d, (b2 + 1 : U32)) && (IM.tr.off(l, d, (b2 + 2 : U32)) && (IM.tr.off(l, d, (b2 + 3 : U32)))), onw(l, d, b2, hol)), own02(b2, d, own.ws(b2, d, hokb2))))), offs3(x, d, b2, and_l(KMd.off.words(KMd.nw(x), d, b2), KMd.off.words(KMd.nw(x), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, x), IM.nd.disj(d, x, b2), hsx)))), hbi),
        and_intro(IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place(l, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 2 : U32)), s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, r, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 3 : U32)), s), ih, ME.subst(U32, z => {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, r, z, s) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 3 : U32)), w7(AD.view(U32, LAT.fromT(U32, t0)), d, nx, H, pv, p2, L, b, x, s, (b2 + 3 : U32), off3(b2, d, P.at_fh(), own.fh(b2, d, hokb2)), offs0(b, d, (b2 + 3 : U32), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))))), offs3(b, d, (b2 + 3 : U32), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))))), offs1(b, d, (b2 + 3 : U32), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))))), offs2(b, d, (b2 + 3 : U32), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb))))), neq_comm(AD.slot((b2 + 3 : U32), d), AD.slot(L, d), ME.subst(IM.Plc, z => {Nat.is_eq(AD.slot((b2 + 3 : U32), d), AD.slot(plc.lo(z), d)) == False{} : Bool}, IM.tr.plc(l, c, k, (b2 + 2 : U32)), IM.Plc{L, C}, hcc, plc2(l, c, k, (b2 + 2 : U32), d, (b2 + 3 : U32), and_r(IM.tr.off(l, d, (b2 + 2 : U32)), IM.tr.off(l, d, (b2 + 3 : U32)), and_r(IM.tr.off(l, d, (b2 + 1 : U32)), IM.tr.off(l, d, (b2 + 2 : U32)) && (IM.tr.off(l, d, (b2 + 3 : U32))), and_r(IM.tr.off(l, d, b2), IM.tr.off(l, d, (b2 + 1 : U32)) && (IM.tr.off(l, d, (b2 + 2 : U32)) && (IM.tr.off(l, d, (b2 + 3 : U32)))), onw(l, d, b2, hol)))), own32(b2, d, own.ws(b2, d, hokb2))))), offs3(x, d, (b2 + 3 : U32), and_r(KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)), KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (b2 + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b2), KMd.off.words(KMd.nw(x), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, x), IM.nd.disj(d, x, b2), hsx)))))), Equal.trans(Bool, IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s), True{}, Equal.sym(Bool, IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s), r7(r, AD.view(U32, LAT.fromT(U32, t0)), d, nx, H, pv, p2, L, b, x, s, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), lay_fh(r, d, hlay_r), and_l(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hrb_)), and_r(IM.tr.off(r, d, (b + 2 : U32)), IM.tr.off(r, d, (b + 3 : U32)), and_r(IM.tr.off(r, d, (b + 1 : U32)), IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32))), and_r(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hrb_)))), and_l(IM.tr.off(r, d, (b + 1 : U32)), IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32))), and_r(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hrb_))), and_l(IM.tr.off(r, d, (b + 2 : U32)), IM.tr.off(r, d, (b + 3 : U32)), and_r(IM.tr.off(r, d, (b + 1 : U32)), IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32))), and_r(IM.tr.off(r, d, b), IM.tr.off(r, d, (b + 1 : U32)) && (IM.tr.off(r, d, (b + 2 : U32)) && (IM.tr.off(r, d, (b + 3 : U32)))), onw(r, d, b, hrb_)))), ME.subst(IM.Plc, z => {IM.tr.off(r, d, plc.lo(z)) == True{} : Bool}, IM.tr.plc(l, c, k, (b2 + 2 : U32)), IM.Plc{L, C}, hcc, plc34(l, r, c, k, (b2 + 2 : U32), d, and_l(IM.tr.off(r, d, (b2 + 2 : U32)), IM.tr.off(r, d, (b2 + 3 : U32)), and_r(IM.tr.off(r, d, (b2 + 1 : U32)), IM.tr.off(r, d, (b2 + 2 : U32)) && (IM.tr.off(r, d, (b2 + 3 : U32))), and_r(IM.tr.off(r, d, b2), IM.tr.off(r, d, (b2 + 1 : U32)) && (IM.tr.off(r, d, (b2 + 2 : U32)) && (IM.tr.off(r, d, (b2 + 3 : U32)))), onw(r, d, b2, hor)))), apart_sym(r, l, d, hap))), and_r(IM.tr.off(r, d, (x + 2 : U32)), IM.tr.off(r, d, (x + 3 : U32)), and_r(IM.tr.off(r, d, (x + 1 : U32)), IM.tr.off(r, d, (x + 2 : U32)) && (IM.tr.off(r, d, (x + 3 : U32))), and_r(IM.tr.off(r, d, x), IM.tr.off(r, d, (x + 1 : U32)) && (IM.tr.off(r, d, (x + 2 : U32)) && (IM.tr.off(r, d, (x + 3 : U32)))), onw(r, d, x, hrx_)))))), hrr))))))

# a branch on the placement's way: its test below c and k's side split
def insK(+lt: Bool, +sd: Bool, +t0: LAT.Tree<U32>, +d: Nat, +nx: U32, +H: U32, +pv: U32, +p2: U32, +L: U32, +b: U32, +x: U32, +s: U32, +k: U32, +c: Nat, +C: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hpv: {pv == X.ix.pick(X.ix.side(k, c), x, C) : U32}, +hp2: {p2 == X.ix.pick(X.ix.side(k, c), C, x) : U32},
  +hH1: {X.ix.branch(H) == True{} : Bool}, +hH2: {Nat.is_eq(X.ix.bitof(H), c) == True{} : Bool},
  +hokb: {IM.nd.ok(b, d) == True{} : Bool}, +hokx: {IM.nd.ok(x, d) == True{} : Bool}, +hsxb: {IM.nd.sep(d, x, b) == True{} : Bool},
  +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool}, +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32},
  +loc: U32, +b2: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr,
  +hp: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, loc) == b2 : U32}, +hbr: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2)) == True{} : Bool}, +hbi: {Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2)), i) == True{} : Bool},
  +hrl: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s) == True{} : Bool}, +hrr: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s) == True{} : Bool},
  +hokb2: {IM.nd.ok(b2, d) == True{} : Bool}, +hol: {IM.tr.offn(l, d, b2) == True{} : Bool}, +hor: {IM.tr.offn(r, d, b2) == True{} : Bool},
  +hap: {IM.tr.apart(l, r, d) == True{} : Bool}, +hlay_l: {IM.tr.lay(l, d) == True{} : Bool}, +hlay_r: {IM.tr.lay(r, d) == True{} : Bool},
  +hlb2: {KMd.off.words(KMd.nw(b2), d, loc) == True{} : Bool}, +hll: {IM.tr.off(l, d, loc) == True{} : Bool}, +hlr: {IM.tr.off(r, d, loc) == True{} : Bool}, +hlf: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(loc, d)) == False{} : Bool},
  +hlb: {KMd.off.words(KMd.nw(b), d, loc) == True{} : Bool}, +hlx: {KMd.off.words(KMd.nw(x), d, loc) == True{} : Bool},
  +hsb: {IM.nd.sep(d, b2, b) == True{} : Bool}, +hlb_: {IM.tr.offn(l, d, b) == True{} : Bool}, +hrb_: {IM.tr.offn(r, d, b) == True{} : Bool},
  +hsx: {IM.nd.sep(d, b2, x) == True{} : Bool}, +hlx_: {IM.tr.offn(l, d, x) == True{} : Bool}, +hrx_: {IM.tr.offn(r, d, x) == True{} : Bool},
  +hlt: {Nat.is_lt(i, c) == lt : Bool}, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hreB: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Br{b2, i, l, r}, b2, s) == True{} : Bool}, +hlayB: {IM.tr.lay(IM.Br{b2, i, l, r}, d) == True{} : Bool}, +hlocB: {IM.tr.off(IM.Br{b2, i, l, r}, d, loc) == True{} : Bool},
  +hBb: {IM.tr.offn(IM.Br{b2, i, l, r}, d, b) == True{} : Bool}, +hBx: {IM.tr.offn(IM.Br{b2, i, l, r}, d, x) == True{} : Bool},
  +hc: {IM.plc.k(Nat.is_lt(i, c), X.ix.side(k, i), b2, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b2)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b2))) == IM.Plc{L, C} : IM.Plc},
  ihl: {IM.tr.plc(l, c, k, (b2 + 2 : U32)) == IM.Plc{L, C} : IM.Plc} -> {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place(l, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 2 : U32)), s) == True{} : Bool},
  ihr: {IM.tr.plc(r, c, k, (b2 + 3 : U32)) == IM.Plc{L, C} : IM.Plc} -> {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place(r, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, (b2 + 3 : U32)), s) == True{} : Bool}) ->
  {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place.k(Nat.is_lt(i, c), X.ix.side(k, i), b2, i, l, r, IM.tr.place(l, x, k, b, c), IM.tr.place(r, x, k, b, c), x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), s) == True{} : Bool}:
  match lt:
    case False{}:
      +hc1 = ME.subst(Bool, z => {IM.plc.k(z, X.ix.side(k, i), b2, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b2)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b2))) == IM.Plc{L, C} : IM.Plc}, Nat.is_lt(i, c), False{}, hlt, hc)
      +hL = Equal.cong(IM.Plc, U32, z => plc.lo(z), IM.Plc{loc, b2}, IM.Plc{L, C}, hc1)
      +hC = Equal.cong(IM.Plc, U32, z => plc.cu(z), IM.Plc{loc, b2}, IM.Plc{L, C}, hc1)
      %Equal.sym(Bool, Nat.is_lt(i, c), False{}, hlt) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place.k(_, X.ix.side(k, i), b2, i, l, r, IM.tr.place(l, x, k, b, c), IM.tr.place(r, x, k, b, c), x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), s) == True{} : Bool}
      insJ(X.ix.side(k, c), IM.Br{b2, i, l, r}, AD.view(U32, LAT.fromT(U32, t0)), d, nx, H, pv, p2, L, b, x, s, k, c, loc, C, {==}, hL, hpv, hp2, hH1, hH2, ME.subst(U32, z => {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Br{b2, i, l, r}, z, s) == True{} : Bool}, b2, C, hC, hreB), hlayB, hlocB, hlb, hlx, hokb, hokx, hsxb, hBb, hBx, hnb, hk, vs(t0, d, loc, hft, hd32), vs(t0, d, b, hft, hd32), vs(t0, d, (b + 3 : U32), hft, hd32), vs(t0, d, (b + 2 : U32), hft, hd32), vs(t0, d, (x + 3 : U32), hft, hd32))
    case True{}:
      match sd:
        case True{}:
          +hc1 = ME.subst(Bool, z => {IM.plc.k(True{}, z, b2, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b2)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b2))) == IM.Plc{L, C} : IM.Plc}, X.ix.side(k, i), True{}, hsd,
            ME.subst(Bool, z => {IM.plc.k(z, X.ix.side(k, i), b2, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b2)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b2))) == IM.Plc{L, C} : IM.Plc}, Nat.is_lt(i, c), True{}, hlt, hc))
          %Equal.sym(Bool, Nat.is_lt(i, c), True{}, hlt) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place.k(_, X.ix.side(k, i), b2, i, l, r, IM.tr.place(l, x, k, b, c), IM.tr.place(r, x, k, b, c), x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), s) == True{} : Bool}
          %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place.k(True{}, _, b2, i, l, r, IM.tr.place(l, x, k, b, c), IM.tr.place(r, x, k, b, c), x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), s) == True{} : Bool}
          insD.r(t0, d, nx, H, pv, p2, L, b, x, s, k, c, C, hft, hd32, hpv, hp2, hH1, hH2, hokb, hokx, hsxb, hnb, hk, loc, b2, i, l, r, hp, hbr, hbi, hrl, hrr, hokb2, hol, hor, hap, hlay_l, hlay_r, hlb2, hll, hlr, hlf, hlb, hlx, hsb, hlb_, hrb_, hsx, hlx_, hrx_, hc1, ihr(hc1))
        case False{}:
          +hc1 = ME.subst(Bool, z => {IM.plc.k(True{}, z, b2, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b2)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b2))) == IM.Plc{L, C} : IM.Plc}, X.ix.side(k, i), False{}, hsd,
            ME.subst(Bool, z => {IM.plc.k(z, X.ix.side(k, i), b2, loc, IM.tr.plc(l, c, k, X.ix.kid(False{}, b2)), IM.tr.plc(r, c, k, X.ix.kid(True{}, b2))) == IM.Plc{L, C} : IM.Plc}, Nat.is_lt(i, c), True{}, hlt, hc))
          %Equal.sym(Bool, Nat.is_lt(i, c), True{}, hlt) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place.k(_, X.ix.side(k, i), b2, i, l, r, IM.tr.place(l, x, k, b, c), IM.tr.place(r, x, k, b, c), x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), s) == True{} : Bool}
          %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place.k(True{}, _, b2, i, l, r, IM.tr.place(l, x, k, b, c), IM.tr.place(r, x, k, b, c), x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), s) == True{} : Bool}
          insD.l(t0, d, nx, H, pv, p2, L, b, x, s, k, c, C, hft, hd32, hpv, hp2, hH1, hH2, hokb, hokx, hsxb, hnb, hk, loc, b2, i, l, r, hp, hbr, hbi, hrl, hrr, hokb2, hol, hor, hap, hlay_l, hlay_r, hlb2, hll, hlr, hlf, hlb, hlx, hsb, hlb_, hrb_, hsx, hlx_, hrx_, hc1, ihl(hc1))

# the realization after an insert's writes, by induction along the
# placement's way from the word loc holding the tree's pointer p
def insB(T: IM.Tr, +t0: LAT.Tree<U32>, +d: Nat, +nx: U32, +H: U32, +pv: U32, +p2: U32, +L: U32, +b: U32, +x: U32, +s: U32, +k: U32, +c: Nat, +C: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hpv: {pv == X.ix.pick(X.ix.side(k, c), x, C) : U32}, +hp2: {p2 == X.ix.pick(X.ix.side(k, c), C, x) : U32},
  +hH1: {X.ix.branch(H) == True{} : Bool}, +hH2: {Nat.is_eq(X.ix.bitof(H), c) == True{} : Bool},
  +hokb: {IM.nd.ok(b, d) == True{} : Bool}, +hokx: {IM.nd.ok(x, d) == True{} : Bool}, +hsxb: {IM.nd.sep(d, x, b) == True{} : Bool},
  +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool}, +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32}, +loc: U32, +p: U32,
  +hre: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, T, p, s) == True{} : Bool}, +hlay: {IM.tr.lay(T, d) == True{} : Bool}, +hloc: {IM.tr.off(T, d, loc) == True{} : Bool}, +hlf: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(loc, d)) == False{} : Bool},
  +hlb: {KMd.off.words(KMd.nw(b), d, loc) == True{} : Bool}, +hlx: {KMd.off.words(KMd.nw(x), d, loc) == True{} : Bool}, +hTb: {IM.tr.offn(T, d, b) == True{} : Bool}, +hTx: {IM.tr.offn(T, d, x) == True{} : Bool},
  +hp: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, loc) == p : U32}, +hc: {IM.tr.plc(T, c, k, loc) == IM.Plc{L, C} : IM.Plc}) ->
  {IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place(T, x, k, b, c), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), nx), AD.slot(b, d), H), AD.slot((b + 3 : U32), d), pv), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), p2), AD.slot(L, d), b), AD.slot((x + 3 : U32), d), s), d, loc), s) == True{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      +hL = Equal.cong(IM.Plc, U32, z => plc.lo(z), IM.Plc{loc, y}, IM.Plc{L, C}, hc)
      +hC = Equal.cong(IM.Plc, U32, z => plc.cu(z), IM.Plc{loc, y}, IM.Plc{L, C}, hc)
      insJ(X.ix.side(k, c), IM.Lf{y, ky}, AD.view(U32, LAT.fromT(U32, t0)), d, nx, H, pv, p2, L, b, x, s, k, c, loc, C, {==}, hL, hpv, hp2, hH1, hH2, ME.subst(U32, z => {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Lf{y, ky}, z, s) == True{} : Bool}, p, C, Equal.trans(U32, p, y, C, real_addr(IM.Lf{y, ky}, AD.view(U32, LAT.fromT(U32, t0)), d, p, s, hre), hC), hre), hlay, hloc, hlb, hlx, hokb, hokx, hsxb, hTb, hTx, hnb, hk, vs(t0, d, loc, hft, hd32), vs(t0, d, b, hft, hd32), vs(t0, d, (b + 3 : U32), hft, hd32), vs(t0, d, (b + 2 : U32), hft, hd32), vs(t0, d, (x + 3 : U32), hft, hd32))
    case IM.Br{+b2, +i, +l, +r}:
      +hpb = real_addr(IM.Br{b2, i, l, r}, AD.view(U32, LAT.fromT(U32, t0)), d, p, s, hre)
      +hr1 = and_r(U32.is_eq(p, b2), X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2)) && (Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s))), hre)
      +hr2 = and_r(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2)), Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s)), hr1)
      +hr3 = and_r(Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2)), i), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s), hr2)
      +hl1 = and_r(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hlay)
      +hl2 = and_r(IM.tr.offn(l, d, b2), IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), hl1)
      +hl3 = and_r(IM.tr.offn(r, d, b2), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), hl2)
      +hl4 = and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), hl3)
      +hc1 = and_r(KMd.off.words(KMd.nw(b2), d, loc), IM.tr.off(l, d, loc) && IM.tr.off(r, d, loc), hloc)
      +hokb2 = and_l(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hlay)
      +hol = and_l(IM.tr.offn(l, d, b2), IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), hl1)
      +hor = and_l(IM.tr.offn(r, d, b2), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), hl2)
      +hlay_l = and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), hl4)
      +hlay_r = and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), hl4)
      +hbx = and_r(IM.nd.sep(d, b2, b), IM.tr.offn(l, d, b) && IM.tr.offn(r, d, b), hTb)
      +hxx = and_r(IM.nd.sep(d, b2, x), IM.tr.offn(l, d, x) && IM.tr.offn(r, d, x), hTx)
      +hlb_ = and_l(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b), hbx)
      +hrb_ = and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b), hbx)
      +hlx_ = and_l(IM.tr.offn(l, d, x), IM.tr.offn(r, d, x), hxx)
      +hrx_ = and_r(IM.tr.offn(l, d, x), IM.tr.offn(r, d, x), hxx)
      +hsb = and_l(IM.nd.sep(d, b2, b), IM.tr.offn(l, d, b) && IM.tr.offn(r, d, b), hTb)
      +hsx = and_l(IM.nd.sep(d, b2, x), IM.tr.offn(l, d, x) && IM.tr.offn(r, d, x), hTx)
      insK(Nat.is_lt(i, c), X.ix.side(k, i), t0, d, nx, H, pv, p2, L, b, x, s, k, c, C, hft, hd32, hpv, hp2, hH1, hH2, hokb, hokx, hsxb, hnb, hk, loc, b2, i, l, r, Equal.trans(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, loc), p, b2, hp, hpb),
        and_l(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2)), Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s)), hr1), and_l(Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b2)), i), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s), hr2),
        and_l(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s), hr3), and_r(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s), hr3),
        hokb2, hol, hor, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), hl3), hlay_l, hlay_r,
        and_l(KMd.off.words(KMd.nw(b2), d, loc), IM.tr.off(l, d, loc) && IM.tr.off(r, d, loc), hloc), and_l(IM.tr.off(l, d, loc), IM.tr.off(r, d, loc), hc1), and_r(IM.tr.off(l, d, loc), IM.tr.off(r, d, loc), hc1), hlf,
        hlb, hlx, hsb, hlb_, hrb_, hsx, hlx_, hrx_, {==}, {==},
        ME.subst(U32, z => {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Br{b2, i, l, r}, z, s) == True{} : Bool}, p, b2, hpb, hre), hlay, hloc, hTb, hTx, hc,
        hcl => insB(l, t0, d, nx, H, pv, p2, L, b, x, s, k, c, C, hft, hd32, hpv, hp2, hH1, hH2, hokb, hokx, hsxb, hnb, hk, (b2 + 2 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), and_l(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s), hr3), hlay_l, and_l(IM.tr.off(l, d, (b2 + 2 : U32)), IM.tr.off(l, d, (b2 + 3 : U32)), and_r(IM.tr.off(l, d, (b2 + 1 : U32)), IM.tr.off(l, d, (b2 + 2 : U32)) && (IM.tr.off(l, d, (b2 + 3 : U32))), and_r(IM.tr.off(l, d, b2), IM.tr.off(l, d, (b2 + 1 : U32)) && (IM.tr.off(l, d, (b2 + 2 : U32)) && (IM.tr.off(l, d, (b2 + 3 : U32)))), onw(l, d, b2, hol)))), off2(b2, d, P.at_fh(), own.fh(b2, d, hokb2)), and_l(KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb)))), and_l(KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)), KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (b2 + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b2), KMd.off.words(KMd.nw(x), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, x), IM.nd.disj(d, x, b2), hsx)))), hlb_, hlx_, {==}, hcl),
        hcr => insB(r, t0, d, nx, H, pv, p2, L, b, x, s, k, c, C, hft, hd32, hpv, hp2, hH1, hH2, hokb, hokx, hsxb, hnb, hk, (b2 + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), and_r(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b2 + 3 : U32)), s), hr3), hlay_r, and_r(IM.tr.off(r, d, (b2 + 2 : U32)), IM.tr.off(r, d, (b2 + 3 : U32)), and_r(IM.tr.off(r, d, (b2 + 1 : U32)), IM.tr.off(r, d, (b2 + 2 : U32)) && (IM.tr.off(r, d, (b2 + 3 : U32))), and_r(IM.tr.off(r, d, b2), IM.tr.off(r, d, (b2 + 1 : U32)) && (IM.tr.off(r, d, (b2 + 2 : U32)) && (IM.tr.off(r, d, (b2 + 3 : U32)))), onw(r, d, b2, hor)))), off3(b2, d, P.at_fh(), own.fh(b2, d, hokb2)), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)), KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, b2), KMd.off.words(KMd.nw(b), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, b), IM.nd.disj(d, b, b2), hsb)))), and_r(KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)), KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (b2 + 1 : U32)), KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, b2), KMd.off.words(KMd.nw(x), d, (b2 + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (b2 + 3 : U32)))), and_l(IM.nd.disj(d, b2, x), IM.nd.disj(d, x, b2), hsx)))), hrb_, hrx_, {==}, hcr))

def ueq_comm(+a: U32, +b: U32) -> {U32.is_eq(a, b) == U32.is_eq(b, a) : Bool}:
  Equal.trans(Bool, U32.is_eq(a, b), Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), U32.is_eq(b, a), MU.u32_is_eq_to_nat(a, b),
    Equal.trans(Bool, Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), Nat.is_eq(U32.to_nat(b), U32.to_nat(a)), U32.is_eq(b, a), MN.is_eq_comm(U32.to_nat(a), U32.to_nat(b)),
      Equal.sym(Bool, U32.is_eq(b, a), Nat.is_eq(U32.to_nat(b), U32.to_nat(a)), MU.u32_is_eq_to_nat(b, a))))

def plc_eta(+q: IM.Plc) -> {q == IM.Plc{plc.lo(q), plc.cu(q)} : IM.Plc}:
  match q:
    case IM.Plc{+lo, +cu}:
      {==}

# a node taken from a free list whose head is not 0: the head's node,
# the head moved on to its word 1, the node's header and payload written
def alloc_eq(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +hd: U32, +pv: U32, +hne: {U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), 0) == False{} : Bool}) ->
  {P.node(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, hd, pv) == (P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + 1 : U32)))), KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), hd), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + P.node.word(hd) : U32), pv)}, a}, KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())))) : P.H & U32}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()), (LAT.fromT(U32, t0), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), LA.get_pair(U32, LAT.fromT(U32, t0), P.at_fh())) :
    {P.node.fin(P.alloc.fh(KM.m_get.fin(_), a), hd, pv) == (P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + 1 : U32)))), KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), hd), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + P.node.word(hd) : U32), pv)}, a}, KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())))) : P.H & U32}
  %Equal.sym(Bool, U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), 0), False{}, hne) :
    {P.node.fin(P.alloc.k(_, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), KM.MG{LAT.fromT(U32, t0)}, a), hd, pv) == (P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + 1 : U32)))), KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), hd), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + P.node.word(hd) : U32), pv)}, a}, KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())))) : P.H & U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + 1 : U32)), (LAT.fromT(U32, t0), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + 1 : U32)))), LA.get_pair(U32, LAT.fromT(U32, t0), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + 1 : U32))) :
    {P.node.fin(P.alloc.pop(KM.m_get.fin(_), KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), a), hd, pv) == (P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + 1 : U32)))), KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), hd), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + P.node.word(hd) : U32), pv)}, a}, KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())))) : P.H & U32}
  {==}

# a placed tree's nodes: the tree's, the new leaf's and the new branch's
def join_offn(+sd: Bool, +U: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +d: Nat, +a: U32,
  +hU: {IM.tr.offn(U, d, a) == True{} : Bool}, +hx: {IM.nd.sep(d, x, a) == True{} : Bool}, +hb: {IM.nd.sep(d, b, a) == True{} : Bool}) ->
  {IM.tr.offn(IM.tr.join(sd, U, x, k, b, c), d, a) == True{} : Bool}:
  match sd:
    case True{}:
      and_intro(IM.nd.sep(d, b, a), IM.tr.offn(U, d, a) && IM.nd.sep(d, x, a), hb, and_intro(IM.tr.offn(U, d, a), IM.nd.sep(d, x, a), hU, hx))
    case False{}:
      and_intro(IM.nd.sep(d, b, a), IM.nd.sep(d, x, a) && IM.tr.offn(U, d, a), hb, and_intro(IM.nd.sep(d, x, a), IM.tr.offn(U, d, a), hx, hU))

def po.k(+lt: Bool, +sd: Bool, +b2: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +d: Nat, +a: U32,
  +h: {IM.tr.offn(IM.Br{b2, i, l, r}, d, a) == True{} : Bool}, +hx: {IM.nd.sep(d, x, a) == True{} : Bool}, +hb: {IM.nd.sep(d, b, a) == True{} : Bool},
  +ihl: {IM.tr.offn(IM.tr.place(l, x, k, b, c), d, a) == True{} : Bool}, +ihr: {IM.tr.offn(IM.tr.place(r, x, k, b, c), d, a) == True{} : Bool}) ->
  {IM.tr.offn(IM.tr.place.k(lt, sd, b2, i, l, r, IM.tr.place(l, x, k, b, c), IM.tr.place(r, x, k, b, c), x, k, b, c), d, a) == True{} : Bool}:
  match lt:
    case False{}:
      join_offn(X.ix.side(k, c), IM.Br{b2, i, l, r}, x, k, b, c, d, a, h, hx, hb)
    case True{}:
      match sd:
        case True{}:
          and_intro(IM.nd.sep(d, b2, a), IM.tr.offn(l, d, a) && IM.tr.offn(IM.tr.place(r, x, k, b, c), d, a), and_l(IM.nd.sep(d, b2, a), IM.tr.offn(l, d, a) && IM.tr.offn(r, d, a), h),
            and_intro(IM.tr.offn(l, d, a), IM.tr.offn(IM.tr.place(r, x, k, b, c), d, a), and_l(IM.tr.offn(l, d, a), IM.tr.offn(r, d, a), and_r(IM.nd.sep(d, b2, a), IM.tr.offn(l, d, a) && IM.tr.offn(r, d, a), h)), ihr))
        case False{}:
          and_intro(IM.nd.sep(d, b2, a), IM.tr.offn(IM.tr.place(l, x, k, b, c), d, a) && IM.tr.offn(r, d, a), and_l(IM.nd.sep(d, b2, a), IM.tr.offn(l, d, a) && IM.tr.offn(r, d, a), h),
            and_intro(IM.tr.offn(IM.tr.place(l, x, k, b, c), d, a), IM.tr.offn(r, d, a), ihl, and_r(IM.tr.offn(l, d, a), IM.tr.offn(r, d, a), and_r(IM.nd.sep(d, b2, a), IM.tr.offn(l, d, a) && IM.tr.offn(r, d, a), h))))

def place_offn(T: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +d: Nat, +a: U32,
  +h: {IM.tr.offn(T, d, a) == True{} : Bool}, +hx: {IM.nd.sep(d, x, a) == True{} : Bool}, +hb: {IM.nd.sep(d, b, a) == True{} : Bool}) ->
  {IM.tr.offn(IM.tr.place(T, x, k, b, c), d, a) == True{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      join_offn(X.ix.side(k, c), IM.Lf{y, ky}, x, k, b, c, d, a, h, hx, hb)
    case IM.Br{+b2, +i, +l, +r}:
      +hlr = and_r(IM.nd.sep(d, b2, a), IM.tr.offn(l, d, a) && IM.tr.offn(r, d, a), h)
      po.k(Nat.is_lt(i, c), X.ix.side(k, i), b2, i, l, r, x, k, b, c, d, a, h, hx, hb,
        place_offn(l, x, k, b, c, d, a, and_l(IM.tr.offn(l, d, a), IM.tr.offn(r, d, a), hlr), hx, hb), place_offn(r, x, k, b, c, d, a, and_r(IM.tr.offn(l, d, a), IM.tr.offn(r, d, a), hlr), hx, hb))

def insert.has(+T: IM.Tr, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +b: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, IM.Has{T}) == True{} : Bool}, +hi: {IM.tr.ok(T, 0n) == True{} : Bool},
  +hoks: {IM.nd.ok(s, d) == True{} : Bool}, +hoffT: {IM.tr.offn(T, d, s) == True{} : Bool}, +hlayT: {IM.tr.lay(T, d) == True{} : Bool},
  +hfr: {IM.nd.ok(x, d) && (IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && IM.tr.offn(T, d, b)))))) == True{} : Bool},
  +hm: {Bool.and(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b), True{})) == True{} : Bool},
  +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32}, +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool},
  +ha: {IM.tr.look(T, k) == None{} : Maybe<&2, U32>}) ->
  {IM.ix.real(AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}:
  +hne_s = not_true(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), and_l(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, T, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre))
  +hreT = and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, T, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre)
  +hgo = ne_found(k, IM.tr.near(T, k), Equal.trans(Bool, U32.is_eq(k, IM.tr.near(T, k)), U32.is_eq(IM.tr.near(T, k), k), False{}, ueq_comm(k, IM.tr.near(T, k)), near_ne(T, k, ha)))
  +hfh0 = ME.subst(U32, z => {U32.is_eq(z, 0) == False{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), wd(t0, d, P.at_fh(), hft, hd32), not_true(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0), and_l(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b), True{}), hm)))
  +hbi = ME.subst(U32, z => {KMd.at_idx(z) == b : U32}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), wd(t0, d, P.at_fh(), hft, hd32),
    MS.u32_eq_of_is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b, and_l(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b), True{}, and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b), True{}), hm))))
  +hrB = insB(T, t0, d, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b, x, s, k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), hft, hd32, {==}, {==}, and_l(X.ix.branch(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), Bool.and(Nat.is_eq(X.ix.bitof(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), U32.is_eq(P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), 3)), hd_ok(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), diff_lt(k, IM.tr.near(T, k), hgo))), and_l(Nat.is_eq(X.ix.bitof(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), U32.is_eq(P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), 3), and_r(X.ix.branch(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), Bool.and(Nat.is_eq(X.ix.bitof(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), U32.is_eq(P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), 3)), hd_ok(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), diff_lt(k, IM.tr.near(T, k), hgo)))), and_l(IM.nd.ok(b, d), IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b))))), and_r(IM.nd.ok(x, d), IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))))), hfr)), and_l(IM.nd.ok(x, d), IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))))), hfr), and_l(IM.nd.sep(d, x, b), IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))), and_r(IM.nd.ok(b, d), IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b))))), and_r(IM.nd.ok(x, d), IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))))), hfr))), hnb, hk, (s + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), hreT, hlayT, and_r(IM.tr.off(T, d, (s + 2 : U32)), IM.tr.off(T, d, (s + 3 : U32)), and_r(IM.tr.off(T, d, (s + 1 : U32)), IM.tr.off(T, d, (s + 2 : U32)) && (IM.tr.off(T, d, (s + 3 : U32))), and_r(IM.tr.off(T, d, s), IM.tr.off(T, d, (s + 1 : U32)) && (IM.tr.off(T, d, (s + 2 : U32)) && (IM.tr.off(T, d, (s + 3 : U32)))), onw(T, d, s, hoffT)))), off3(s, d, P.at_fh(), own.fh(s, d, hoks)), and_r(KMd.off.words(KMd.nw(b), d, (s + 2 : U32)), KMd.off.words(KMd.nw(b), d, (s + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (s + 1 : U32)), KMd.off.words(KMd.nw(b), d, (s + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (s + 3 : U32))), and_r(KMd.off.words(KMd.nw(b), d, s), KMd.off.words(KMd.nw(b), d, (s + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (s + 2 : U32)) && (KMd.off.words(KMd.nw(b), d, (s + 3 : U32)))), and_r(IM.nd.disj(d, b, s), IM.nd.disj(d, s, b), and_l(IM.nd.sep(d, b, s), IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)), and_r(IM.nd.sep(d, x, s), IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b))), and_r(IM.nd.sep(d, x, b), IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))), and_r(IM.nd.ok(b, d), IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b))))), and_r(IM.nd.ok(x, d), IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))))), hfr))))))))), and_r(KMd.off.words(KMd.nw(x), d, (s + 2 : U32)), KMd.off.words(KMd.nw(x), d, (s + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (s + 1 : U32)), KMd.off.words(KMd.nw(x), d, (s + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (s + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, s), KMd.off.words(KMd.nw(x), d, (s + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (s + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (s + 3 : U32)))), and_r(IM.nd.disj(d, x, s), IM.nd.disj(d, s, x), and_l(IM.nd.sep(d, x, s), IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b))), and_r(IM.nd.sep(d, x, b), IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))), and_r(IM.nd.ok(b, d), IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b))))), and_r(IM.nd.ok(x, d), IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))))), hfr)))))))), and_r(IM.tr.offn(T, d, x), IM.tr.offn(T, d, b), and_r(IM.nd.sep(d, b, s), IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)), and_r(IM.nd.sep(d, x, s), IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b))), and_r(IM.nd.sep(d, x, b), IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))), and_r(IM.nd.ok(b, d), IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b))))), and_r(IM.nd.ok(x, d), IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))))), hfr)))))), and_l(IM.tr.offn(T, d, x), IM.tr.offn(T, d, b), and_r(IM.nd.sep(d, b, s), IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)), and_r(IM.nd.sep(d, x, s), IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b))), and_r(IM.nd.sep(d, x, b), IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))), and_r(IM.nd.ok(b, d), IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b))))), and_r(IM.nd.ok(x, d), IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))))), hfr)))))), {==}, plc_eta(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hft)
  +hf2 = LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), hf1)
  +hf3 = LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), d, (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))), hf2)
  +hf4 = LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), d, (b + 1 : U32), P.era(), hf3)
  +hf5 = LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), d, (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x), hf4)
  +hf6 = LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), d, plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b, hf5)
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (x + 2 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32)))), rd_eq(t0, a, (x + 2 : U32))) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.x(_, s, x))), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (s + 3 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32)))), rd_eq(t0, a, (s + 3 : U32))) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.r(_, s, x, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32)))))), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %wd(t0, d, (x + 2 : U32), hft, hd32) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.k(U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), s), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), _, x, s))), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), k, hk) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.k(U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), s), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), _, x, s))), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %wd(t0, d, (s + 3 : U32), hft, hd32) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.k(U32.is_eq(_, s), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, k, x, s))), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), False{}, hne_s) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), k, x, s))), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(P.H, X.ix.put.d(X.ds.run(33n, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), True{}}, k), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), k, x, s), X.ix.put.n(U32.is_eq(IM.tr.near(T, k), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.near(T, k), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), k, x, s),
    dsn(T, 33n, t0, a, d, s, k, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), 0n, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), x, hft, hd32, hreT, hi, {==})) : {IM.ix.real(AD.view(U32, KMd.words(_)), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(IM.tr.near(T, k), k), False{}, near_ne(T, k, ha)) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.n(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.near(T, k), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), k, x, s))), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(X.Cr, X.ix.diff(k, IM.tr.near(T, k)), X.Cr{IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), IM.cr.go(X.ix.diff(k, IM.tr.near(T, k)))}, cr_eta(X.ix.diff(k, IM.tr.near(T, k)))) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.c(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), k, x, s))), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(Bool, IM.cr.go(X.ix.diff(k, IM.tr.near(T, k))), False{}, hgo) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.c(X.Cr{IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), _}, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), k, x, s))), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(X.Pl, X.pl.run(33n, X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (s + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), True{}}, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k), X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), False{}},
    pla(T, 33n, t0, a, d, s, k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), (s + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), 0n, hft, hd32, hreT, hi, {==})) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.p(_, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, x, s))), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(P.H & U32, P.node(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + 1 : U32)))), KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))) : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))))}, a}, KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())))), alloc_eq(t0, a, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))), hfh0)) :
    {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.b(_, plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, x, s))), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(U32, KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), b, hbi) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.b((P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (_ + 1 : U32)))), _, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (_ + P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))) : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))))}, a}, _), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, x, s))), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(U32, P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), 3, MS.u32_eq_of_is_eq(P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), 3, and_r(Nat.is_eq(X.ix.bitof(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), U32.is_eq(P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), 3), and_r(X.ix.branch(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), Bool.and(Nat.is_eq(X.ix.bitof(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), U32.is_eq(P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), 3)), hd_ok(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), diff_lt(k, IM.tr.near(T, k), hgo)))))) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.b((P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + _ : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))))}, a}, b), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, x, s))), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b)), AD.slot((x + 3 : U32), d), s), LA.set_view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), d, (x + 3 : U32), s, hf6, hd32)) :
    {IM.ix.real(_, d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b)), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x))), AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), b), LA.set_view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), d, plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b, hf5, hd32)) :
    {IM.ix.real(List.set(&2, U32, _, AD.slot((x + 3 : U32), d), s), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x))), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era())), AD.slot((b + 2 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), LA.set_view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), d, (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x), hf4, hd32)) :
    {IM.ix.real(List.set(&2, U32, List.set(&2, U32, _, AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), b), AD.slot((x + 3 : U32), d), s), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era())), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))))), AD.slot((b + 1 : U32), d), P.era()), LA.set_view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), d, (b + 1 : U32), P.era(), hf3, hd32)) :
    {IM.ix.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, _, AD.slot((b + 2 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), b), AD.slot((x + 3 : U32), d), s), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))))), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))))), AD.slot((b + 3 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), LA.set_view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), d, (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))), hf2, hd32)) :
    {IM.ix.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, _, AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), b), AD.slot((x + 3 : U32), d), s), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))))), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))))), AD.slot(b, d), X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), hf1, hd32)) :
    {IM.ix.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, _, AD.slot((b + 3 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), b), AD.slot((x + 3 : U32), d), s), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), LA.set_view(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hft, hd32)) :
    {IM.ix.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, _, AD.slot(b, d), X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), AD.slot((b + 3 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), b), AD.slot((x + 3 : U32), d), s), d, s, IM.Has{IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))}) == True{} : Bool}
  and_intro(Bool.not(U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), AD.slot(b, d), X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), AD.slot((b + 3 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), b), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), s)), IM.tr.real(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), AD.slot(b, d), X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), AD.slot((b + 3 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), b), AD.slot((x + 3 : U32), d), s), d, IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), AD.slot(b, d), X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), AD.slot((b + 3 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), b), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), s),
    ME.subst(U32, z => {Bool.not(U32.is_eq(z, s)) == True{} : Bool}, IM.tr.addr(IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), AD.slot(b, d), X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), AD.slot((b + 3 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), b), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)),
      Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), AD.slot(b, d), X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), AD.slot((b + 3 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), b), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), IM.tr.addr(IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), real_addr(IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), AD.slot(b, d), X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), AD.slot((b + 3 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), b), AD.slot((x + 3 : U32), d), s), d, KMd.word(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), AD.slot(b, d), X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), AD.slot((b + 3 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), AD.slot((b + 1 : U32), d), P.era()), AD.slot((b + 2 : U32), d), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), b), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), s, hrB)),
      ME.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, U32.is_eq(IM.tr.addr(IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), s), Equal.sym(Bool, U32.is_eq(IM.tr.addr(IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), s), False{}, sep_ne(d, s, IM.tr.addr(IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), sep_sym(d, IM.tr.addr(IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), s, root_sep(IM.tr.place(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), d, s, place_offn(T, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), d, s, hoffT, and_l(IM.nd.sep(d, x, s), IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b))), and_r(IM.nd.sep(d, x, b), IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))), and_r(IM.nd.ok(b, d), IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b))))), and_r(IM.nd.ok(x, d), IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))))), hfr)))), and_l(IM.nd.sep(d, b, s), IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)), and_r(IM.nd.sep(d, x, s), IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b))), and_r(IM.nd.sep(d, x, b), IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))), and_r(IM.nd.ok(b, d), IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b))))), and_r(IM.nd.ok(x, d), IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && (IM.tr.offn(T, d, b)))))), hfr)))))))))), {==})),
    hrB)

def insert.ept(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s) == True{} : Bool}, +hokx: {IM.nd.ok(x, d) == True{} : Bool}, +hsxs: {IM.nd.sep(d, x, s) == True{} : Bool},
  +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32}, +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool}) ->
  {IM.ix.real(AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, s, IM.Has{IM.Lf{x, k}}) == True{} : Bool}:
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (x + 2 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32)))), rd_eq(t0, a, (x + 2 : U32))) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.x(_, s, x))), d, s, IM.Has{IM.Lf{x, k}}) == True{} : Bool}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (s + 3 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32)))), rd_eq(t0, a, (s + 3 : U32))) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.r(_, s, x, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32)))))), d, s, IM.Has{IM.Lf{x, k}}) == True{} : Bool}
  %wd(t0, d, (s + 3 : U32), hft, hd32) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.k(U32.is_eq(_, s), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32))), x, s))), d, s, IM.Has{IM.Lf{x, k}}) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), True{}, hre) : {IM.ix.real(AD.view(U32, KMd.words(X.ix.put.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32))), x, s))), d, s, IM.Has{IM.Lf{x, k}}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x)), AD.slot((x + 3 : U32), d), s),
    LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), d, (x + 3 : U32), s, LA.set_full(U32, LAT.fromT(U32, t0), d, (s + 3 : U32), x, hft), hd32)) :
    {IM.ix.real(_, d, s, IM.Has{IM.Lf{x, k}}) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), LA.set_view(U32, LAT.fromT(U32, t0), d, (s + 3 : U32), x, hft, hd32)) :
    {IM.ix.real(List.set(&2, U32, _, AD.slot((x + 3 : U32), d), s), d, s, IM.Has{IM.Lf{x, k}}) == True{} : Bool}
  and_intro(Bool.not(U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), s)), U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), x) && (Bool.not(X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, x))) && (U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), k) && U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), s))),
    ME.subst(U32, z => {Bool.not(U32.is_eq(z, s)) == True{} : Bool}, x, KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), x, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), KMd.word(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), d, (s + 3 : U32)), x, Equal.sym(U32, KMd.word(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), d, (s + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), wl_ne(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), d, (x + 3 : U32), (s + 3 : U32), s, off3(s, d, (x + 3 : U32), and_r(KMd.off.words(KMd.nw(s), d, (x + 2 : U32)), KMd.off.words(KMd.nw(s), d, (x + 3 : U32)), and_r(KMd.off.words(KMd.nw(s), d, (x + 1 : U32)), KMd.off.words(KMd.nw(s), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(s), d, (x + 3 : U32))), and_r(KMd.off.words(KMd.nw(s), d, x), KMd.off.words(KMd.nw(s), d, (x + 1 : U32)) && (KMd.off.words(KMd.nw(s), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(s), d, (x + 3 : U32)))), and_l(IM.nd.disj(d, x, s), IM.nd.disj(d, s, x), hsxs))))))), wl_eq2(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32), x, vs(t0, d, (s + 3 : U32), hft, hd32)))),
      ME.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, U32.is_eq(x, s), Equal.sym(Bool, U32.is_eq(x, s), False{}, sep_ne(d, s, x, sep_sym(d, x, s, hsxs))), {==})),
    and_intro(U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), x), Bool.not(X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, x))) && (U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), k) && U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), s)),
      ME.subst(U32, z => {U32.is_eq(z, x) == True{} : Bool}, x, KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), x, Equal.trans(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), KMd.word(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), d, (s + 3 : U32)), x, Equal.sym(U32, KMd.word(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), d, (s + 3 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (s + 3 : U32)), wl_ne(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), d, (x + 3 : U32), (s + 3 : U32), s, off3(s, d, (x + 3 : U32), and_r(KMd.off.words(KMd.nw(s), d, (x + 2 : U32)), KMd.off.words(KMd.nw(s), d, (x + 3 : U32)), and_r(KMd.off.words(KMd.nw(s), d, (x + 1 : U32)), KMd.off.words(KMd.nw(s), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(s), d, (x + 3 : U32))), and_r(KMd.off.words(KMd.nw(s), d, x), KMd.off.words(KMd.nw(s), d, (x + 1 : U32)) && (KMd.off.words(KMd.nw(s), d, (x + 2 : U32)) && (KMd.off.words(KMd.nw(s), d, (x + 3 : U32)))), and_l(IM.nd.disj(d, x, s), IM.nd.disj(d, s, x), hsxs))))))), wl_eq2(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32), x, vs(t0, d, (s + 3 : U32), hft, hd32)))), is_eq_self(x)),
      and_intro(Bool.not(X.ix.branch(KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, x))), U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), k) && U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), s),
        ME.subst(U32, z => {Bool.not(X.ix.branch(z)) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x), KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, x), Equal.trans(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x), KMd.word(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), d, x), KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, x), wl_ne(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32), x, x, off0(x, d, (s + 3 : U32), and_r(KMd.off.words(KMd.nw(x), d, (s + 2 : U32)), KMd.off.words(KMd.nw(x), d, (s + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (s + 1 : U32)), KMd.off.words(KMd.nw(x), d, (s + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (s + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, s), KMd.off.words(KMd.nw(x), d, (s + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (s + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (s + 3 : U32)))), and_r(IM.nd.disj(d, x, s), IM.nd.disj(d, s, x), hsxs)))))), wl_ne(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), d, (x + 3 : U32), x, s, own30(x, d, own.ws(x, d, hokx)))), ME.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)), Equal.sym(Bool, X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)), False{}, hnb), {==})),
        and_intro(U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), k), U32.is_eq(KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), s),
          ME.subst(U32, z => {U32.is_eq(z, k) == True{} : Bool}, k, KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), Equal.trans(U32, k, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), k, hk), Equal.trans(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), KMd.word(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), d, (x + 2 : U32)), KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (x + 2 : U32)), wl_ne(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32), (x + 2 : U32), x, off2(x, d, (s + 3 : U32), and_r(KMd.off.words(KMd.nw(x), d, (s + 2 : U32)), KMd.off.words(KMd.nw(x), d, (s + 3 : U32)), and_r(KMd.off.words(KMd.nw(x), d, (s + 1 : U32)), KMd.off.words(KMd.nw(x), d, (s + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (s + 3 : U32))), and_r(KMd.off.words(KMd.nw(x), d, s), KMd.off.words(KMd.nw(x), d, (s + 1 : U32)) && (KMd.off.words(KMd.nw(x), d, (s + 2 : U32)) && (KMd.off.words(KMd.nw(x), d, (s + 3 : U32)))), and_r(IM.nd.disj(d, x, s), IM.nd.disj(d, s, x), hsxs)))))), wl_ne(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), d, (x + 3 : U32), (x + 2 : U32), s, own32(x, d, own.ws(x, d, hokx))))), is_eq_self(k)),
          ME.subst(U32, z => {U32.is_eq(z, s) == True{} : Bool}, s, KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), Equal.sym(U32, KMd.word(List.set(&2, U32, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), AD.slot((x + 3 : U32), d), s), d, (x + 3 : U32)), s, wl_eq2(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), d, (x + 3 : U32), s, some_set(AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), AD.slot((x + 3 : U32), d), x, vs(t0, d, (x + 3 : U32), hft, hd32)))), is_eq_self(s))))))

def insert.k(I: IM.Ix, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +b: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, I) == True{} : Bool}, +hi: {IM.ix.inv(I) == True{} : Bool}, +hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  +hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}, +hm: {IM.ix.room(I, AD.view(U32, LAT.fromT(U32, t0)), d, b) == True{} : Bool},
  +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32}, +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool},
  +ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}) ->
  {IM.ix.real(AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, s, IM.ix.put(I, x, k, b)) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      insert.ept(t0, a, d, s, x, k, hft, hd32, hre, and_l(IM.nd.ok(x, d), IM.nd.sep(d, x, s), hfr), and_r(IM.nd.ok(x, d), IM.nd.sep(d, x, s), hfr), hk, hnb)
    case IM.Has{+t}:
      insert.has(t, t0, a, d, s, x, k, b, hft, hd32, hre, hi,
        and_l(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl), and_l(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl)),
        and_r(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl)), hfr, hm, hk, hnb, ha)

def insert.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +x: U32, +k: U32, +b: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}, hi: {IM.ix.inv(I) == True{} : Bool}, hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}, hm: {IM.ix.room(I, AD.view(U32, w), d, b) == True{} : Bool},
  hk: {KMd.word(AD.view(U32, w), d, (x + 2 : U32)) == k : U32}, hb: {X.ix.branch(KMd.word(AD.view(U32, w), d, x)) == False{} : Bool},
  ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}, m: LAT.Mirror(U32, w)) ->
  {IM.ix.real(AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{w}, a}, s, x))), d, s, IM.ix.put(I, x, k, b)) == True{} : Bool}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e)
  %e : {IM.ix.real(AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{_}, a}, s, x))), d, s, IM.ix.put(I, x, k, b)) == True{} : Bool}
  insert.k(I, t0, a, d, s, x, k, b, hft, hd32,
    LAB.subst(Array<U32>, q => {IM.ix.real(AD.view(U32, q), d, s, I) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hr), hi, hl, hfr,
    LAB.subst(Array<U32>, q => {IM.ix.room(I, AD.view(U32, q), d, b) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hm),
    LAB.subst(Array<U32>, q => {KMd.word(AD.view(U32, q), d, (x + 2 : U32)) == k : U32}, w, LAT.fromT(U32, t0), ew, hk),
    LAB.subst(Array<U32>, q => {X.ix.branch(KMd.word(AD.view(U32, q), d, x)) == False{} : Bool}, w, LAT.fromT(U32, t0), ew, hb), ha)

def Laws.insert_tree(w, a, d, s, I, x, k, b, hf, hd32, hr, hi, hl, hfr, hm, hk, hb, ha):
  insert.m(w, a, d, s, I, x, k, b, hf, hd32, hr, hi, hl, hfr, hm, hk, hb, ha, LAT.mirror(U32, w))

# Frames
# ======

def c1b(T: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +j: U32, +ho: {IM.tr.offb(T, d, j) == True{} : Bool},
  +hx: {IM.tr.look(T, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(T), x) == False{} : Bool}) ->
  {KMd.off.words(KMd.nw(cut.pa(IM.tr.cutat(T, x, k, loc))), d, j) == True{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      lf_absurd({KMd.off.words(KMd.nw(cut.pa(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc))), d, j) == True{} : Bool}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      +hlr = and_r(KMd.off.words(KMd.nw(b), d, j), IM.tr.offb(l, d, j) && IM.tr.offb(r, d, j), ho)
      c1.k(X.ix.side(k, i), b, i, l, r, x, k, loc, d, j, {==}, and_l(KMd.off.words(KMd.nw(b), d, j), IM.tr.offb(l, d, j) && IM.tr.offb(r, d, j), ho), hx,
        hxl => hnl => c1b(l, x, k, (b + 2 : U32), d, j, and_l(IM.tr.offb(l, d, j), IM.tr.offb(r, d, j), hlr), hxl, hnl),
        hxr => hnr => c1b(r, x, k, (b + 3 : U32), d, j, and_r(IM.tr.offb(l, d, j), IM.tr.offb(r, d, j), hlr), hxr, hnr))

def c2b(T: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +j: U32, +ho: {IM.tr.offb(T, d, j) == True{} : Bool}, +hj: {Nat.is_eq(AD.slot(j, d), AD.slot(loc, d)) == False{} : Bool},
  +hx: {IM.tr.look(T, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(T), x) == False{} : Bool}) ->
  {Nat.is_eq(AD.slot(j, d), AD.slot(cut.lo(IM.tr.cutat(T, x, k, loc)), d)) == False{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      lf_absurd({Nat.is_eq(AD.slot(j, d), AD.slot(cut.lo(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc)), d)) == False{} : Bool}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      +hb = and_l(KMd.off.words(KMd.nw(b), d, j), IM.tr.offb(l, d, j) && IM.tr.offb(r, d, j), ho)
      +hlr = and_r(KMd.off.words(KMd.nw(b), d, j), IM.tr.offb(l, d, j) && IM.tr.offb(r, d, j), ho)
      c2.k(X.ix.side(k, i), b, i, l, r, x, k, loc, d, j, {==}, hj, hx,
        hxl => hnl => c2b(l, x, k, (b + 2 : U32), d, j, and_l(IM.tr.offb(l, d, j), IM.tr.offb(r, d, j), hlr), off2(b, d, j, hb), hxl, hnl),
        hxr => hnr => c2b(r, x, k, (b + 3 : U32), d, j, and_r(IM.tr.offb(l, d, j), IM.tr.offb(r, d, j), hlr), off3(b, d, j, hb), hxr, hnr))

def plc2b(T: IM.Tr, +c: Nat, +k: U32, +loc: U32, +d: Nat, +j: U32, +ho: {IM.tr.offb(T, d, j) == True{} : Bool}, +hj: {Nat.is_eq(AD.slot(j, d), AD.slot(loc, d)) == False{} : Bool}) ->
  {Nat.is_eq(AD.slot(j, d), AD.slot(plc.lo(IM.tr.plc(T, c, k, loc)), d)) == False{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      hj
    case IM.Br{+b, +i, +l, +r}:
      +hb = and_l(KMd.off.words(KMd.nw(b), d, j), IM.tr.offb(l, d, j) && IM.tr.offb(r, d, j), ho)
      +hlr = and_r(KMd.off.words(KMd.nw(b), d, j), IM.tr.offb(l, d, j) && IM.tr.offb(r, d, j), ho)
      plc2.k(Nat.is_lt(i, c), X.ix.side(k, i), b, i, c, k, loc, l, r, d, j, hj,
        plc2b(l, c, k, (b + 2 : U32), d, j, and_l(IM.tr.offb(l, d, j), IM.tr.offb(r, d, j), hlr), off2(b, d, j, hb)),
        plc2b(r, c, k, (b + 3 : U32), d, j, and_r(IM.tr.offb(l, d, j), IM.tr.offb(r, d, j), hlr), off3(b, d, j, hb)))

# a read of a heap whose words are A
def rd_eqA(A: Array<U32>, -a: Array<V.Val>, +i: U32) -> {P.rd(P.H{KM.MG{A}, a}, i) == (P.H{KM.MG{A}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, A, i))) : P.H & U32}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, A, i), (A, Pair.snd(Array<U32>, U32, Array.get(U32, A, i))), LA.get_pair(U32, A, i)) :
    {P.rd.fin(KM.m_get.fin(_), a) == (P.H{KM.MG{A}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, A, i))) : P.H & U32}
  {==}

# the heap a free after a write leaves
def fwh(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +L: U32, +S: U32, +Pn: U32) ->
  {P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, L, S), Pn) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.base(Pn), 0), (P.base(Pn) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))}, a} : P.H}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()), (Array.set(U32, LAT.fromT(U32, t0), L, S), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), LA.get_pair(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())) :
    {P.free.fh(KM.m_get.fin(_), a, Pn) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.base(Pn), 0), (P.base(Pn) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))}, a} : P.H}
  {==}

def rm.heap.br(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hreT: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Br{b, i, l, r}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s) == True{} : Bool}, +hi: {IM.tr.ok(IM.Br{b, i, l, r}, 0n) == True{} : Bool},
  +hoks: {IM.nd.ok(s, d) == True{} : Bool}, +hoffT: {IM.tr.offn(IM.Br{b, i, l, r}, d, s) == True{} : Bool}, +hlayT: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool},
  +hx: {IM.tr.look(IM.Br{b, i, l, r}, k) == Some{x} : Maybe<&2, U32>}) ->
  {X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a} : P.H}:
  +hol = and_l(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hlayT))
  +hor = and_l(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hlayT)))
  +hneT = sep_ne(d, x, b, ls.k(X.ix.side(k, i), d, i, l, r, k, x, b, {==}, hx, hxl => look_sep(l, b, d, k, x, hol, hxl), hxr => look_sep(r, b, d, k, x, hor, hxr)))
  +hpb = real_addr(IM.Br{b, i, l, r}, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s, hreT)
  +hne0 = ME.subst(U32, z => {U32.is_eq(z, x) == False{} : Bool}, b, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), b, hpb), hneT)
  +hkey = look_key(IM.Br{b, i, l, r}, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s, k, x, hreT, hx)
  +hA = rmA(IM.Br{b, i, l, r}, 33n, t0, a, d, s, k, x, (s + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), 0n, hft, hd32, hreT, hi, {==}, hx, hneT)
  +hbase = MS.u32_eq_of_is_eq(P.base(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), c5(IM.Br{b, i, l, r}, x, k, (s + 3 : U32), d, hlayT, hx, hneT))
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (x + 2 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32)))), rd_eq(t0, a, (x + 2 : U32))) : {X.ix.rm.x(_, s, x) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a} : P.H}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (s + 3 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32)))), rd_eq(t0, a, (s + 3 : U32))) : {X.ix.rm.r(_, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32))), x) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a} : P.H}
  %wd(t0, d, (x + 2 : U32), hft, hd32) : {X.ix.rm.k(U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), s, _, x) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a} : P.H}
  %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), k, hkey) : {X.ix.rm.k(U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), s, _, x) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a} : P.H}
  %wd(t0, d, (s + 3 : U32), hft, hd32) : {X.ix.rm.k(U32.is_eq(_, x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, s, k, x) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a} : P.H}
  %Equal.sym(Bool, U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), x), False{}, hne0) : {X.ix.rm.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s, k, x) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a} : P.H}
  %Equal.sym(P.H, X.rm.h(X.rm.run(33n, X.Rm{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (s + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), True{}}, k, x)), P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), hA) : {_ == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a} : P.H}
  %Equal.sym(P.H, P.free(P.wr(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.base(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), 0), (P.base(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a}, fwh(t0, a, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))))) : {_ == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a} : P.H}
  %Equal.sym(U32, P.base(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), hbase) : {P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), _, 0), (_ + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a} == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a} : P.H}
  {==}

def rm.heap.lf(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +y: U32, +ky: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hreT: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Lf{y, ky}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s) == True{} : Bool},
  +hx: {IM.tr.look(IM.Lf{y, ky}, k) == Some{x} : Maybe<&2, U32>}) ->
  {X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x) == P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s)}, a} : P.H}:
  +hpy = real_addr(IM.Lf{y, ky}, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s, hreT)
  +hyx = hit_some(U32.is_eq(ky, k), y, x, hx)
  +hkey = look_key(IM.Lf{y, ky}, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s, k, x, hreT, hx)
  +hyxb = ME.subst(U32, z => {U32.is_eq(z, x) == True{} : Bool}, x, y, Equal.sym(U32, y, x, hyx), is_eq_self(x))
  +heq = ME.subst(U32, z => {U32.is_eq(z, x) == True{} : Bool}, y, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), y, hpy), hyxb)
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (x + 2 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32)))), rd_eq(t0, a, (x + 2 : U32))) : {X.ix.rm.x(_, s, x) == P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s)}, a} : P.H}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (s + 3 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32)))), rd_eq(t0, a, (s + 3 : U32))) : {X.ix.rm.r(_, s, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32))), x) == P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s)}, a} : P.H}
  %wd(t0, d, (x + 2 : U32), hft, hd32) : {X.ix.rm.k(U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), s, _, x) == P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s)}, a} : P.H}
  %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), k, hkey) : {X.ix.rm.k(U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), s, _, x) == P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s)}, a} : P.H}
  %wd(t0, d, (s + 3 : U32), hft, hd32) : {X.ix.rm.k(U32.is_eq(_, x), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, s, k, x) == P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s)}, a} : P.H}
  %Equal.sym(Bool, U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), x), True{}, heq) : {X.ix.rm.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s, k, x) == P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s)}, a} : P.H}
  {==}

def ins.heap.ept(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s) == True{} : Bool}, +hokx: {IM.nd.ok(x, d) == True{} : Bool}, +hsxs: {IM.nd.sep(d, x, s) == True{} : Bool},
  +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32}, +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool}) ->
  {X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x) == P.H{KM.MG{Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s)}, a} : P.H}:

  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (x + 2 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32)))), rd_eq(t0, a, (x + 2 : U32))) : {X.ix.put.x(_, s, x) == P.H{KM.MG{Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s)}, a} : P.H}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (s + 3 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32)))), rd_eq(t0, a, (s + 3 : U32))) : {X.ix.put.r(_, s, x, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32)))) == P.H{KM.MG{Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s)}, a} : P.H}
  %wd(t0, d, (s + 3 : U32), hft, hd32) : {X.ix.put.k(U32.is_eq(_, s), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32))), x, s) == P.H{KM.MG{Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s)}, a} : P.H}
  %Equal.sym(Bool, U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), True{}, hre) : {X.ix.put.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32))), x, s) == P.H{KM.MG{Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s)}, a} : P.H}
  {==}

def ins.heap.has(+T: IM.Tr, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +b: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, IM.Has{T}) == True{} : Bool}, +hi: {IM.tr.ok(T, 0n) == True{} : Bool},
  +hoks: {IM.nd.ok(s, d) == True{} : Bool}, +hoffT: {IM.tr.offn(T, d, s) == True{} : Bool}, +hlayT: {IM.tr.lay(T, d) == True{} : Bool},
  +hfr: {IM.nd.ok(x, d) && (IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && IM.tr.offn(T, d, b)))))) == True{} : Bool},
  +hm: {Bool.and(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b), True{})) == True{} : Bool},
  +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32}, +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool},
  +ha: {IM.tr.look(T, k) == None{} : Maybe<&2, U32>}) ->
  {X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}:
  +hne_s = not_true(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), and_l(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, T, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre))
  +hreT = and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, T, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre)
  +hgo = ne_found(k, IM.tr.near(T, k), Equal.trans(Bool, U32.is_eq(k, IM.tr.near(T, k)), U32.is_eq(IM.tr.near(T, k), k), False{}, ueq_comm(k, IM.tr.near(T, k)), near_ne(T, k, ha)))
  +hfh0 = ME.subst(U32, z => {U32.is_eq(z, 0) == False{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), wd(t0, d, P.at_fh(), hft, hd32), not_true(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0), and_l(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b), True{}), hm)))
  +hbi = ME.subst(U32, z => {KMd.at_idx(z) == b : U32}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), wd(t0, d, P.at_fh(), hft, hd32),
    MS.u32_eq_of_is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b, and_l(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b), True{}, and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b), True{}), hm))))
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (x + 2 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32)))), rd_eq(t0, a, (x + 2 : U32))) : {X.ix.put.x(_, s, x) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (s + 3 : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32)))), rd_eq(t0, a, (s + 3 : U32))) : {X.ix.put.r(_, s, x, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (x + 2 : U32)))) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}
  %wd(t0, d, (x + 2 : U32), hft, hd32) : {X.ix.put.k(U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), s), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), _, x, s) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}
  %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)), k, hk) : {X.ix.put.k(U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), s), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (s + 3 : U32))), _, x, s) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}
  %wd(t0, d, (s + 3 : U32), hft, hd32) : {X.ix.put.k(U32.is_eq(_, s), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, _, k, x, s) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}
  %Equal.sym(Bool, U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), False{}, hne_s) : {X.ix.put.k(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), k, x, s) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}
  %Equal.sym(P.H, X.ix.put.d(X.ds.run(33n, X.Ds{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), True{}}, k), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), k, x, s), X.ix.put.n(U32.is_eq(IM.tr.near(T, k), k), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.near(T, k), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), k, x, s),
    dsn(T, 33n, t0, a, d, s, k, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), 0n, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), x, hft, hd32, hreT, hi, {==})) : {_ == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}
  %Equal.sym(Bool, U32.is_eq(IM.tr.near(T, k), k), False{}, near_ne(T, k, ha)) : {X.ix.put.n(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, IM.tr.near(T, k), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), k, x, s) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}
  %Equal.sym(X.Cr, X.ix.diff(k, IM.tr.near(T, k)), X.Cr{IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), IM.cr.go(X.ix.diff(k, IM.tr.near(T, k)))}, cr_eta(X.ix.diff(k, IM.tr.near(T, k)))) : {X.ix.put.c(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), k, x, s) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}
  %Equal.sym(Bool, IM.cr.go(X.ix.diff(k, IM.tr.near(T, k))), False{}, hgo) : {X.ix.put.c(X.Cr{IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), _}, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), k, x, s) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}
  %Equal.sym(X.Pl, X.pl.run(33n, X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (s + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), True{}}, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k), X.Pl{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), False{}},
    pla(T, 33n, t0, a, d, s, k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), (s + 3 : U32), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), 0n, hft, hd32, hreT, hi, {==})) : {X.ix.put.p(_, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, x, s) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}
  %Equal.sym(P.H & U32, P.node(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + 1 : U32)))), KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))) + P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))) : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))))}, a}, KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())))), alloc_eq(t0, a, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))), hfh0)) :
    {X.ix.put.b(_, plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, x, s) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}
  %Equal.sym(U32, KMd.at_idx(Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), b, hbi) : {X.ix.put.b((P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (_ + 1 : U32)))), _, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (_ + P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))) : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))))}, a}, _), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, x, s) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}
  %Equal.sym(U32, P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), 3, MS.u32_eq_of_is_eq(P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), 3, and_r(Nat.is_eq(X.ix.bitof(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), U32.is_eq(P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), 3), and_r(X.ix.branch(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), Bool.and(Nat.is_eq(X.ix.bitof(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), U32.is_eq(P.node.word(X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), 3)), hd_ok(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), diff_lt(k, IM.tr.near(T, k), hgo)))))) : {X.ix.put.b((P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + _ : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))))}, a}, b), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, x, s) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a} : P.H}
  {==}

def rk.br(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hreT: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Br{b, i, l, r}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s) == True{} : Bool}, +hi: {IM.tr.ok(IM.Br{b, i, l, r}, 0n) == True{} : Bool},
  +hoks: {IM.nd.ok(s, d) == True{} : Bool}, +hoffT: {IM.tr.offn(IM.Br{b, i, l, r}, d, s) == True{} : Bool}, +hlayT: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool},
  +hx: {IM.tr.look(IM.Br{b, i, l, r}, k) == Some{x} : Maybe<&2, U32>}, +j: U32, +hjs: {Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hjT: {IM.tr.offb(IM.Br{b, i, l, r}, d, j) == True{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}) ->
  {Pair.snd(P.H, U32, P.rd(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}:
  +hol = and_l(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hlayT))
  +hor = and_l(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hlayT)))
  +hneT = sep_ne(d, x, b, ls.k(X.ix.side(k, i), d, i, l, r, k, x, b, {==}, hx, hxl => look_sep(l, b, d, k, x, hol, hxl), hxr => look_sep(r, b, d, k, x, hor, hxr)))
  %Equal.sym(P.H, X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a}, rm.heap.br(t0, a, d, s, x, k, b, i, l, r, hft, hd32, hreT, hi, hoks, hoffT, hlayT, hx)) : {Pair.snd(P.H, U32, P.rd(_, j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a}, j), (P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), j))), rd_eqA(Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), a, j)) : {Pair.snd(P.H, U32, _) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j))), rd_eq(t0, a, j)) : {Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), j)) == Pair.snd(P.H, U32, _) : U32}
  Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), d, P.at_fh(), j, ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), d, (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh())), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), d, cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0, LA.set_full(U32, LAT.fromT(U32, t0), d, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), hft))), hd32, hjh), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), d, (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), j, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh())), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), d, cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0, LA.set_full(U32, LAT.fromT(U32, t0), d, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), hft)), hd32, offs1(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d, j, c1b(IM.Br{b, i, l, r}, x, k, (s + 3 : U32), d, j, hjT, hx, hneT))), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), LA.get_set_other(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), d, cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), j, 0, LA.set_full(U32, LAT.fromT(U32, t0), d, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), hft), hd32, offs0(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d, j, c1b(IM.Br{b, i, l, r}, x, k, (s + 3 : U32), d, j, hjT, hx, hneT))), LA.get_set_other(U32, LAT.fromT(U32, t0), d, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), j, cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), hft, hd32, neq_comm(AD.slot(j, d), AD.slot(cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), c2b(IM.Br{b, i, l, r}, x, k, (s + 3 : U32), d, j, hjT, neq_comm(AD.slot((s + 3 : U32), d), AD.slot(j, d), hjs), hx, hneT))))))

def rk.lf(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +y: U32, +ky: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hreT: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Lf{y, ky}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s) == True{} : Bool},
  +hx: {IM.tr.look(IM.Lf{y, ky}, k) == Some{x} : Maybe<&2, U32>}, +j: U32, +hjs: {Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}) ->
  {Pair.snd(P.H, U32, P.rd(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}:
  %Equal.sym(P.H, X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s)}, a}, rm.heap.lf(t0, a, d, s, x, k, y, ky, hft, hd32, hreT, hx)) : {Pair.snd(P.H, U32, P.rd(_, j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s)}, a}, j), (P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s), j))), rd_eqA(Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s), a, j)) : {Pair.snd(P.H, U32, _) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j))), rd_eq(t0, a, j)) : {Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s), j)) == Pair.snd(P.H, U32, _) : U32}
  LA.get_set_other(U32, LAT.fromT(U32, t0), d, (s + 3 : U32), j, s, hft, hd32, hjs)

def ik.ept(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s) == True{} : Bool}, +hokx: {IM.nd.ok(x, d) == True{} : Bool}, +hsxs: {IM.nd.sep(d, x, s) == True{} : Bool},
  +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32}, +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool}, +j: U32, +hjs: {Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hjx: {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}) ->
  {Pair.snd(P.H, U32, P.rd(X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}:
  %Equal.sym(P.H, X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), P.H{KM.MG{Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s)}, a}, ins.heap.ept(t0, a, d, s, x, k, hft, hd32, hre, hokx, hsxs, hk, hnb)) : {Pair.snd(P.H, U32, P.rd(_, j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s)}, a}, j), (P.H{KM.MG{Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s), j))), rd_eqA(Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s), a, j)) : {Pair.snd(P.H, U32, _) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j))), rd_eq(t0, a, j)) : {Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s), j)) == Pair.snd(P.H, U32, _) : U32}
  Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), LA.get_set_other(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), d, (x + 3 : U32), j, s, LA.set_full(U32, LAT.fromT(U32, t0), d, (s + 3 : U32), x, hft), hd32, hjx), LA.get_set_other(U32, LAT.fromT(U32, t0), d, (s + 3 : U32), j, x, hft, hd32, hjs))

def ik.has(+T: IM.Tr, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +b: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, IM.Has{T}) == True{} : Bool}, +hi: {IM.tr.ok(T, 0n) == True{} : Bool},
  +hoks: {IM.nd.ok(s, d) == True{} : Bool}, +hoffT: {IM.tr.offn(T, d, s) == True{} : Bool}, +hlayT: {IM.tr.lay(T, d) == True{} : Bool},
  +hfr: {IM.nd.ok(x, d) && (IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && IM.tr.offn(T, d, b)))))) == True{} : Bool},
  +hm: {Bool.and(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b), True{})) == True{} : Bool},
  +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32}, +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool},
  +ha: {IM.tr.look(T, k) == None{} : Maybe<&2, U32>}, +j: U32, +hjs: {Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, +hjT: {IM.tr.offb(T, d, j) == True{} : Bool},
  +hjb: {KMd.off.words(KMd.nw(b), d, j) == True{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}, +hjx: {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}) ->
  {Pair.snd(P.H, U32, P.rd(X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}:
  +hf1 = LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hft)
  +hf2 = LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), hf1)
  +hf3 = LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), d, (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))), hf2)
  +hf4 = LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), d, (b + 1 : U32), P.era(), hf3)
  +hf5 = LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), d, (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x), hf4)
  +hf6 = LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), d, plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b, hf5)
  %Equal.sym(P.H, X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a}, ins.heap.has(T, t0, a, d, s, x, k, b, hft, hd32, hre, hi, hoks, hoffT, hlayT, hfr, hm, hk, hnb, ha)) : {Pair.snd(P.H, U32, P.rd(_, j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a}, j), (P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s), j))), rd_eqA(Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s), a, j)) : {Pair.snd(P.H, U32, _) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}
  %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j))), rd_eq(t0, a, j)) : {Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s), j)) == Pair.snd(P.H, U32, _) : U32}
  Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), d, (x + 3 : U32), j, s, hf6, hd32, hjx), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), d, plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), j, b, hf5, hd32, neq_comm(AD.slot(j, d), AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), plc2b(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32), d, j, hjT, neq_comm(AD.slot((s + 3 : U32), d), AD.slot(j, d), hjs)))), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), d, (b + 2 : U32), j, X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x), hf4, hd32, offs2(b, d, j, hjb)), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), d, (b + 1 : U32), j, P.era(), hf3, hd32, offs1(b, d, j, hjb)), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), d, (b + 3 : U32), j, X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))), hf2, hd32, offs3(b, d, j, hjb)), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), j)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), j)), LA.get_set_other(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, j, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), hf1, hd32, offs0(b, d, j, hjb)), LA.get_set_other(U32, LAT.fromT(U32, t0), d, P.at_fh(), j, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hft, hd32, hjh)))))))

def rk.k(I: IM.Ix, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +j: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, I) == True{} : Bool}, +hi: {IM.ix.inv(I) == True{} : Bool}, +hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  +hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}, +hj: {IM.ix.offb(I, s, d, j) == True{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}) ->
  {Pair.snd(P.H, U32, P.rd(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}:
  match I:
    case IM.Ept{}:
      Empty.absurd({Pair.snd(P.H, U32, P.rd(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, m => is_some(m), None{}, Some{x}, hx)))
    case IM.Has{+t}:
      match t:
        case IM.Lf{+y, +ky}:
          rk.lf(t0, a, d, s, x, k, y, ky, hft, hd32, and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Lf{y, ky}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre), hx, j,
            not_true(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d)), and_l(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d))), IM.tr.offb(IM.Lf{y, ky}, d, j), hj)))
        case IM.Br{+b, +i, +l, +r}:
          rk.br(t0, a, d, s, x, k, b, i, l, r, hft, hd32, and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Br{b, i, l, r}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre), hi,
            and_l(IM.nd.ok(s, d), IM.tr.offn(IM.Br{b, i, l, r}, d, s) && IM.tr.lay(IM.Br{b, i, l, r}, d), hl), and_l(IM.tr.offn(IM.Br{b, i, l, r}, d, s), IM.tr.lay(IM.Br{b, i, l, r}, d), and_r(IM.nd.ok(s, d), IM.tr.offn(IM.Br{b, i, l, r}, d, s) && IM.tr.lay(IM.Br{b, i, l, r}, d), hl)),
            and_r(IM.tr.offn(IM.Br{b, i, l, r}, d, s), IM.tr.lay(IM.Br{b, i, l, r}, d), and_r(IM.nd.ok(s, d), IM.tr.offn(IM.Br{b, i, l, r}, d, s) && IM.tr.lay(IM.Br{b, i, l, r}, d), hl)), hx, j,
            not_true(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d)), and_l(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d))), IM.tr.offb(IM.Br{b, i, l, r}, d, j), hj)), and_r(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d))), IM.tr.offb(IM.Br{b, i, l, r}, d, j), hj), hjh)

def rk.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +x: U32, +k: U32, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}, hi: {IM.ix.inv(I) == True{} : Bool}, hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}, hj: {IM.ix.offb(I, s, d, j) == True{} : Bool}, hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}, m: LAT.Mirror(U32, w)) ->
  {Pair.snd(P.H, U32, P.rd(X.ix.remove(P.H{KM.MG{w}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  %e : {Pair.snd(P.H, U32, P.rd(X.ix.remove(P.H{KM.MG{_}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  rk.k(I, t0, a, d, s, x, k, j, hft, hd32, LAB.subst(Array<U32>, q => {IM.ix.real(AD.view(U32, q), d, s, I) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e), hr), hi, hl, hx, hj, hjh)

def Laws.remove_keeps(w, a, d, s, I, x, k, j, hf, hd32, hr, hi, hl, hx, hj, hjh):
  rk.m(w, a, d, s, I, x, k, j, hf, hd32, hr, hi, hl, hx, hj, hjh, LAT.mirror(U32, w))

def ik.k(I: IM.Ix, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +b: U32, +j: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, I) == True{} : Bool}, +hi: {IM.ix.inv(I) == True{} : Bool}, +hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  +hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}, +hm: {IM.ix.room(I, AD.view(U32, LAT.fromT(U32, t0)), d, b) == True{} : Bool},
  +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32}, +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool},
  +ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>},
  +hj: {IM.ix.offb(I, s, d, j) == True{} : Bool}, +hjb: {IM.ix.newb(I, b, d, j) == True{} : Bool}, +hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}, +hjx: {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}) ->
  {Pair.snd(P.H, U32, P.rd(X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, j)) : U32}:
  match I:
    case IM.Ept{}:
      ik.ept(t0, a, d, s, x, k, hft, hd32, hre, and_l(IM.nd.ok(x, d), IM.nd.sep(d, x, s), hfr), and_r(IM.nd.ok(x, d), IM.nd.sep(d, x, s), hfr), hk, hnb, j,
        not_true(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d)), hj), hjx)
    case IM.Has{+t}:
      ik.has(t, t0, a, d, s, x, k, b, hft, hd32, hre, hi,
        and_l(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl), and_l(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl)),
        and_r(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl)), hfr, hm, hk, hnb, ha, j,
        not_true(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d)), and_l(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d))), IM.tr.offb(t, d, j), hj)), and_r(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d))), IM.tr.offb(t, d, j), hj), hjb, hjh, hjx)

def ik.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +x: U32, +k: U32, +b: U32, +j: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}, hi: {IM.ix.inv(I) == True{} : Bool}, hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}, hm: {IM.ix.room(I, AD.view(U32, w), d, b) == True{} : Bool},
  hk: {KMd.word(AD.view(U32, w), d, (x + 2 : U32)) == k : U32}, hb: {X.ix.branch(KMd.word(AD.view(U32, w), d, x)) == False{} : Bool},
  ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}, hj: {IM.ix.offb(I, s, d, j) == True{} : Bool}, hjb: {IM.ix.newb(I, b, d, j) == True{} : Bool},
  hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}, hjx: {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(j, d)) == False{} : Bool}, m: LAT.Mirror(U32, w)) ->
  {Pair.snd(P.H, U32, P.rd(X.ix.insert(P.H{KM.MG{w}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e)
  %e : {Pair.snd(P.H, U32, P.rd(X.ix.insert(P.H{KM.MG{_}, a}, s, x), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{_}, a}, j)) : U32}
  ik.k(I, t0, a, d, s, x, k, b, j, hft, hd32,
    LAB.subst(Array<U32>, q => {IM.ix.real(AD.view(U32, q), d, s, I) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hr), hi, hl, hfr,
    LAB.subst(Array<U32>, q => {IM.ix.room(I, AD.view(U32, q), d, b) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hm),
    LAB.subst(Array<U32>, q => {KMd.word(AD.view(U32, q), d, (x + 2 : U32)) == k : U32}, w, LAT.fromT(U32, t0), ew, hk),
    LAB.subst(Array<U32>, q => {X.ix.branch(KMd.word(AD.view(U32, q), d, x)) == False{} : Bool}, w, LAT.fromT(U32, t0), ew, hb), ha, hj, hjb, hjh, hjx)

def Laws.insert_keeps(w, a, d, s, I, x, k, b, j, hf, hd32, hr, hi, hl, hfr, hm, hk, hb, ha, hj, hjb, hjh, hjx):
  ik.m(w, a, d, s, I, x, k, b, j, hf, hd32, hr, hi, hl, hfr, hm, hk, hb, ha, hj, hjb, hjh, hjx, LAT.mirror(U32, w))

# Agreement
# =========

def same_sym(+p: Bool, +q: Bool) -> {X.ix.same(p, q) == X.ix.same(q, p) : Bool}:
  match p:
    case True{}:
      match q:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match q:
        case True{}:
          {==}
        case False{}:
          {==}

def same_trans(+p: Bool, +q: Bool, +r: Bool, +h1: {X.ix.same(p, q) == True{} : Bool}, +h2: {X.ix.same(q, r) == True{} : Bool}) -> {X.ix.same(p, r) == True{} : Bool}:
  match p:
    case True{}:
      match q:
        case True{}:
          h2
        case False{}:
          Empty.absurd({X.ix.same(True{}, r) == True{} : Bool}, MB.false_ne_true()(h1))
    case False{}:
      match q:
        case True{}:
          Empty.absurd({X.ix.same(False{}, r) == True{} : Bool}, MB.false_ne_true()(h1))
        case False{}:
          h2

def same_refl(+p: Bool) -> {X.ix.same(p, p) == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# a and c differ where a and b agree and b and c differ
def same_ne(+p: Bool, +q: Bool, +r: Bool, +h1: {X.ix.same(p, q) == True{} : Bool}, +h2: {X.ix.same(q, r) == False{} : Bool}) -> {X.ix.same(p, r) == False{} : Bool}:
  match p:
    case True{}:
      match q:
        case True{}:
          h2
        case False{}:
          Empty.absurd({X.ix.same(True{}, r) == False{} : Bool}, MB.false_ne_true()(h1))
    case False{}:
      match q:
        case True{}:
          Empty.absurd({X.ix.same(False{}, r) == False{} : Bool}, MB.false_ne_true()(h1))
        case False{}:
          h2

def agree_sym(+a: U32, +b: U32, +i: Nat, +h: {IM.tr.agree(a, b, i) == True{} : Bool}) -> {IM.tr.agree(b, a, i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+(+j):
      and_intro(X.ix.same(X.ix.side(b, j), X.ix.side(a, j)), IM.tr.agree(b, a, j),
        Equal.trans(Bool, X.ix.same(X.ix.side(b, j), X.ix.side(a, j)), X.ix.same(X.ix.side(a, j), X.ix.side(b, j)), True{}, same_sym(X.ix.side(b, j), X.ix.side(a, j)), and_l(X.ix.same(X.ix.side(a, j), X.ix.side(b, j)), IM.tr.agree(a, b, j), h)),
        agree_sym(a, b, j, and_r(X.ix.same(X.ix.side(a, j), X.ix.side(b, j)), IM.tr.agree(a, b, j), h)))

def agree_trans(+a: U32, +b: U32, +c: U32, +i: Nat, +h1: {IM.tr.agree(a, b, i) == True{} : Bool}, +h2: {IM.tr.agree(b, c, i) == True{} : Bool}) -> {IM.tr.agree(a, c, i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+(+j):
      and_intro(X.ix.same(X.ix.side(a, j), X.ix.side(c, j)), IM.tr.agree(a, c, j),
        same_trans(X.ix.side(a, j), X.ix.side(b, j), X.ix.side(c, j), and_l(X.ix.same(X.ix.side(a, j), X.ix.side(b, j)), IM.tr.agree(a, b, j), h1), and_l(X.ix.same(X.ix.side(b, j), X.ix.side(c, j)), IM.tr.agree(b, c, j), h2)),
        agree_trans(a, b, c, j, and_r(X.ix.same(X.ix.side(a, j), X.ix.side(b, j)), IM.tr.agree(a, b, j), h1), and_r(X.ix.same(X.ix.side(b, j), X.ix.side(c, j)), IM.tr.agree(b, c, j), h2)))

def agree_refl(+a: U32, +i: Nat) -> {IM.tr.agree(a, a, i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+(+j):
      and_intro(X.ix.same(X.ix.side(a, j), X.ix.side(a, j)), IM.tr.agree(a, a, j), same_refl(X.ix.side(a, j)), agree_refl(a, j))

# agreement below a bit holds below any lower one
def agree_down(+a: U32, +b: U32, +i: Nat, +n: Nat, +h: {IM.tr.agree(a, b, Nat.add(n, i)) == True{} : Bool}) -> {IM.tr.agree(a, b, i) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+(+m):
      agree_down(a, b, i, m, and_r(X.ix.same(X.ix.side(a, Nat.add(m, i)), X.ix.side(b, Nat.add(m, i))), IM.tr.agree(a, b, Nat.add(m, i)), h))

# below i, given i at most j: j is i plus their difference
def le_wit(+i: Nat, +j: Nat, +h: {Nat.is_le(i, j) == True{} : Bool}) -> {j == Nat.add(Nat.sub(j, i), i) : Nat}:
  match i:
    case 0n:
      match j:
        case 0n:
          {==}
        case 1n+(+q):
          Equal.cong(Nat, Nat, z => 1n+z, q, Nat.add(q, 0n), MN.add_zero_sym(q))
    case 1n+(+p):
      match j:
        case 0n:
          Empty.absurd({0n == Nat.add(Nat.sub(0n, 1n+p), 1n+p) : Nat}, MB.false_ne_true()(h))
        case 1n+(+q):
          %MN.add_succ_sym(Nat.sub(q, p), p) : {1n+q == _ : Nat}
          Equal.cong(Nat, Nat, z => 1n+z, q, Nat.add(Nat.sub(q, p), p), le_wit(p, q, h))

def agree_le(+a: U32, +b: U32, +i: Nat, +j: Nat, +hij: {Nat.is_le(i, j) == True{} : Bool}, +h: {IM.tr.agree(a, b, j) == True{} : Bool}) -> {IM.tr.agree(a, b, i) == True{} : Bool}:
  agree_down(a, b, i, Nat.sub(j, i), ME.subst(Nat, z => {IM.tr.agree(a, b, z) == True{} : Bool}, j, Nat.add(Nat.sub(j, i), i), le_wit(i, j, hij), h))

# The scan's stop: the keys alike below the bit it stops at, unalike at it
def crit_ag(+f: Nat, +i: Nat, +a: U32, +b: U32, +eq: Bool, +heq: {X.ix.same(X.ix.side(a, i), X.ix.side(b, i)) == eq : Bool},
  +hag: {IM.tr.agree(a, b, i) == True{} : Bool}, +hg: {IM.cr.go(X.ix.crit(f, X.Cr{i, True{}}, a, b)) == False{} : Bool}) ->
  {Bool.and(IM.tr.agree(a, b, IM.cr.i(X.ix.crit(f, X.Cr{i, True{}}, a, b))), Bool.not(X.ix.same(X.ix.side(a, IM.cr.i(X.ix.crit(f, X.Cr{i, True{}}, a, b))), X.ix.side(b, IM.cr.i(X.ix.crit(f, X.Cr{i, True{}}, a, b)))))) == True{} : Bool}:
  match f:
    case 0n:
      Empty.absurd({Bool.and(IM.tr.agree(a, b, i), Bool.not(X.ix.same(X.ix.side(a, i), X.ix.side(b, i)))) == True{} : Bool}, MB.true_ne_false()(hg))
    case 1n+(+q):
      match eq:
        case True{}:
          %Equal.sym(Bool, X.ix.same(X.ix.side(a, i), X.ix.side(b, i)), True{}, heq) :
            {Bool.and(IM.tr.agree(a, b, IM.cr.i(X.ix.crit(q, X.cr.k(_, i), a, b))), Bool.not(X.ix.same(X.ix.side(a, IM.cr.i(X.ix.crit(q, X.cr.k(_, i), a, b))), X.ix.side(b, IM.cr.i(X.ix.crit(q, X.cr.k(_, i), a, b)))))) == True{} : Bool}
          crit_ag(q, 1n+i, a, b, X.ix.same(X.ix.side(a, 1n+i), X.ix.side(b, 1n+i)), {==}, and_intro(X.ix.same(X.ix.side(a, i), X.ix.side(b, i)), IM.tr.agree(a, b, i), heq, hag),
            ME.subst(Bool, z => {IM.cr.go(X.ix.crit(q, X.cr.k(z, i), a, b)) == False{} : Bool}, X.ix.same(X.ix.side(a, i), X.ix.side(b, i)), True{}, heq, hg))
        case False{}:
          %Equal.sym(Bool, X.ix.same(X.ix.side(a, i), X.ix.side(b, i)), False{}, heq) :
            {Bool.and(IM.tr.agree(a, b, IM.cr.i(X.ix.crit(q, X.cr.k(_, i), a, b))), Bool.not(X.ix.same(X.ix.side(a, IM.cr.i(X.ix.crit(q, X.cr.k(_, i), a, b))), X.ix.side(b, IM.cr.i(X.ix.crit(q, X.cr.k(_, i), a, b)))))) == True{} : Bool}
          %Equal.sym(X.Cr, X.ix.crit(q, X.Cr{i, False{}}, a, b), X.Cr{i, False{}}, crit_stays(q, i, a, b)) :
            {Bool.and(IM.tr.agree(a, b, IM.cr.i(_)), Bool.not(X.ix.same(X.ix.side(a, IM.cr.i(_)), X.ix.side(b, IM.cr.i(_))))) == True{} : Bool}
          %Equal.sym(Bool, X.ix.same(X.ix.side(a, i), X.ix.side(b, i)), False{}, heq) : {Bool.and(IM.tr.agree(a, b, i), Bool.not(_)) == True{} : Bool}
          and_intro(IM.tr.agree(a, b, i), True{}, hag, {==})

# Keys below a branch
# ===================

# every key alike with p alike with q, p and q alike
def all_rep(t: IM.Tr, +p: U32, +q: U32, +i: Nat, +sd: Bool, +h: {IM.tr.all(t, p, i, sd) == True{} : Bool}, +hpq: {IM.tr.agree(p, q, i) == True{} : Bool}) -> {IM.tr.all(t, q, i, sd) == True{} : Bool}:
  match t:
    case IM.Lf{+x, +k}:
      and_intro(IM.tr.agree(k, q, i), X.ix.same(X.ix.side(k, i), sd), agree_trans(k, p, q, i, and_l(IM.tr.agree(k, p, i), X.ix.same(X.ix.side(k, i), sd), h), hpq), and_r(IM.tr.agree(k, p, i), X.ix.same(X.ix.side(k, i), sd), h))
    case IM.Br{+b, +j, +l, +r}:
      and_intro(IM.tr.all(l, q, i, sd), IM.tr.all(r, q, i, sd), all_rep(l, p, q, i, sd, and_l(IM.tr.all(l, p, i, sd), IM.tr.all(r, p, i, sd), h), hpq),
        all_rep(r, p, q, i, sd, and_r(IM.tr.all(l, p, i, sd), IM.tr.all(r, p, i, sd), h), hpq))

# the leftmost key among them
def all_first(t: IM.Tr, +p: U32, +i: Nat, +sd: Bool, +h: {IM.tr.all(t, p, i, sd) == True{} : Bool}) -> {IM.tr.agree(IM.tr.first(t), p, i) == True{} : Bool}:
  match t:
    case IM.Lf{+x, +k}:
      and_l(IM.tr.agree(k, p, i), X.ix.same(X.ix.side(k, i), sd), h)
    case IM.Br{+b, +j, +l, +r}:
      all_first(l, p, i, sd, and_l(IM.tr.all(l, p, i, sd), IM.tr.all(r, p, i, sd), h))

# and the key k's descent meets
def an.k(+sd: Bool, +k: U32, +j: Nat, +l: IM.Tr, +r: IM.Tr, +p: U32, +i: Nat, +s2: Bool, +hsd: {X.ix.side(k, j) == sd : Bool},
  +ihl: {Bool.and(IM.tr.agree(IM.tr.near(l, k), p, i), X.ix.same(X.ix.side(IM.tr.near(l, k), i), s2)) == True{} : Bool},
  +ihr: {Bool.and(IM.tr.agree(IM.tr.near(r, k), p, i), X.ix.same(X.ix.side(IM.tr.near(r, k), i), s2)) == True{} : Bool}) ->
  {Bool.and(IM.tr.agree(X.ix.pick(X.ix.side(k, j), IM.tr.near(r, k), IM.tr.near(l, k)), p, i), X.ix.same(X.ix.side(X.ix.pick(X.ix.side(k, j), IM.tr.near(r, k), IM.tr.near(l, k)), i), s2)) == True{} : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, j), True{}, hsd) : {Bool.and(IM.tr.agree(X.ix.pick(_, IM.tr.near(r, k), IM.tr.near(l, k)), p, i), X.ix.same(X.ix.side(X.ix.pick(_, IM.tr.near(r, k), IM.tr.near(l, k)), i), s2)) == True{} : Bool}
      ihr
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, j), False{}, hsd) : {Bool.and(IM.tr.agree(X.ix.pick(_, IM.tr.near(r, k), IM.tr.near(l, k)), p, i), X.ix.same(X.ix.side(X.ix.pick(_, IM.tr.near(r, k), IM.tr.near(l, k)), i), s2)) == True{} : Bool}
      ihl

def all_near(t: IM.Tr, +k: U32, +p: U32, +i: Nat, +sd: Bool, +h: {IM.tr.all(t, p, i, sd) == True{} : Bool}) ->
  {Bool.and(IM.tr.agree(IM.tr.near(t, k), p, i), X.ix.same(X.ix.side(IM.tr.near(t, k), i), sd)) == True{} : Bool}:
  match t:
    case IM.Lf{+x, +kk}:
      h
    case IM.Br{+b, +j, +l, +r}:
      an.k(X.ix.side(k, j), k, j, l, r, p, i, sd, {==},
        all_near(l, k, p, i, sd, and_l(IM.tr.all(l, p, i, sd), IM.tr.all(r, p, i, sd), h)),
        all_near(r, k, p, i, sd, and_r(IM.tr.all(l, p, i, sd), IM.tr.all(r, p, i, sd), h)))

# a put adds its key alone: what every key holds, the tree after holds,
# its key holding it too
def pall.join(+sdc: Bool, +U: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +p: U32, +i: Nat, +sd: Bool,
  +hU: {IM.tr.all(U, p, i, sd) == True{} : Bool}, +hk: {Bool.and(IM.tr.agree(k, p, i), X.ix.same(X.ix.side(k, i), sd)) == True{} : Bool}) ->
  {IM.tr.all(IM.tr.join(sdc, U, x, k, b, c), p, i, sd) == True{} : Bool}:
  match sdc:
    case True{}:
      and_intro(IM.tr.all(U, p, i, sd), IM.tr.all(IM.Lf{x, k}, p, i, sd), hU, hk)
    case False{}:
      and_intro(IM.tr.all(IM.Lf{x, k}, p, i, sd), IM.tr.all(U, p, i, sd), hk, hU)

def pall.k(+lt: Bool, +sdi: Bool, +b2: U32, +j: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +p: U32, +i: Nat, +sd: Bool,
  +h: {IM.tr.all(IM.Br{b2, j, l, r}, p, i, sd) == True{} : Bool}, +hk: {Bool.and(IM.tr.agree(k, p, i), X.ix.same(X.ix.side(k, i), sd)) == True{} : Bool},
  +ihl: {IM.tr.all(IM.tr.place(l, x, k, b, c), p, i, sd) == True{} : Bool}, +ihr: {IM.tr.all(IM.tr.place(r, x, k, b, c), p, i, sd) == True{} : Bool}) ->
  {IM.tr.all(IM.tr.place.k(lt, sdi, b2, j, l, r, IM.tr.place(l, x, k, b, c), IM.tr.place(r, x, k, b, c), x, k, b, c), p, i, sd) == True{} : Bool}:
  match lt:
    case False{}:
      pall.join(X.ix.side(k, c), IM.Br{b2, j, l, r}, x, k, b, c, p, i, sd, h, hk)
    case True{}:
      match sdi:
        case True{}:
          and_intro(IM.tr.all(l, p, i, sd), IM.tr.all(IM.tr.place(r, x, k, b, c), p, i, sd), and_l(IM.tr.all(l, p, i, sd), IM.tr.all(r, p, i, sd), h), ihr)
        case False{}:
          and_intro(IM.tr.all(IM.tr.place(l, x, k, b, c), p, i, sd), IM.tr.all(r, p, i, sd), ihl, and_r(IM.tr.all(l, p, i, sd), IM.tr.all(r, p, i, sd), h))

def place_all(t: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +p: U32, +i: Nat, +sd: Bool,
  +h: {IM.tr.all(t, p, i, sd) == True{} : Bool}, +hk: {Bool.and(IM.tr.agree(k, p, i), X.ix.same(X.ix.side(k, i), sd)) == True{} : Bool}) ->
  {IM.tr.all(IM.tr.place(t, x, k, b, c), p, i, sd) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      pall.join(X.ix.side(k, c), IM.Lf{y, ky}, x, k, b, c, p, i, sd, h, hk)
    case IM.Br{+b2, +j, +l, +r}:
      pall.k(Nat.is_lt(j, c), X.ix.side(k, j), b2, j, l, r, x, k, b, c, p, i, sd, h, hk,
        place_all(l, x, k, b, c, p, i, sd, and_l(IM.tr.all(l, p, i, sd), IM.tr.all(r, p, i, sd), h), hk),
        place_all(r, x, k, b, c, p, i, sd, and_r(IM.tr.all(l, p, i, sd), IM.tr.all(r, p, i, sd), h), hk))

# a branch's keys on their sides: the key k's descent meets lies on k's
def ns.k(+sd: Bool, +k: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +p: U32, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hl: {IM.tr.all(l, p, i, False{}) == True{} : Bool}, +hr: {IM.tr.all(r, p, i, True{}) == True{} : Bool}) ->
  {X.ix.same(X.ix.side(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), i), X.ix.side(k, i)) == True{} : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {X.ix.same(X.ix.side(X.ix.pick(_, IM.tr.near(r, k), IM.tr.near(l, k)), i), _) == True{} : Bool}
      and_r(IM.tr.agree(IM.tr.near(r, k), p, i), X.ix.same(X.ix.side(IM.tr.near(r, k), i), True{}), all_near(r, k, p, i, True{}, hr))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {X.ix.same(X.ix.side(X.ix.pick(_, IM.tr.near(r, k), IM.tr.near(l, k)), i), _) == True{} : Bool}
      and_r(IM.tr.agree(IM.tr.near(l, k), p, i), X.ix.same(X.ix.side(IM.tr.near(l, k), i), False{}), all_near(l, k, p, i, False{}, hl))

def near_side(+k: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +p: U32, +hl: {IM.tr.all(l, p, i, False{}) == True{} : Bool}, +hr: {IM.tr.all(r, p, i, True{}) == True{} : Bool}) ->
  {X.ix.same(X.ix.side(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), i), X.ix.side(k, i)) == True{} : Bool}:
  ns.k(X.ix.side(k, i), k, i, l, r, p, {==}, hl, hr)

# i not below c and not c: c below i
def lt_of_nlt(+i: Nat, +c: Nat, +h1: {Nat.is_lt(i, c) == False{} : Bool}, +h2: {Nat.is_eq(i, c) == False{} : Bool}) -> {Nat.is_lt(c, i) == True{} : Bool}:
  match i:
    case 0n:
      match c:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, MB.true_ne_false()(h2))
        case 1n+(+q):
          Empty.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, MB.true_ne_false()(h1))
    case 1n+(+j):
      match c:
        case 0n:
          {==}
        case 1n+(+q):
          lt_of_nlt(j, q, h1, h2)

# where the placement stops at a branch, its bit is above c: at c, the
# key k's descent meets would lie on k's side, where k and it differ
def sb.k(+e: Bool, +k: U32, +i: Nat, +c: Nat, +l: IM.Tr, +r: IM.Tr, +p: U32, +he: {Nat.is_eq(i, c) == e : Bool},
  +hlt: {Nat.is_lt(i, c) == False{} : Bool}, +hl: {IM.tr.all(l, p, i, False{}) == True{} : Bool}, +hr: {IM.tr.all(r, p, i, True{}) == True{} : Bool},
  +hne: {X.ix.same(X.ix.side(k, c), X.ix.side(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), c)) == False{} : Bool}) -> {Nat.is_lt(c, i) == True{} : Bool}:
  match e:
    case False{}:
      lt_of_nlt(i, c, hlt, he)
    case True{}:
      Empty.absurd({Nat.is_lt(c, i) == True{} : Bool}, MB.true_ne_false()(Equal.trans(Bool, True{}, X.ix.same(X.ix.side(k, c), X.ix.side(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), c)), False{},
        ME.subst(Nat, z => {True{} == X.ix.same(X.ix.side(k, z), X.ix.side(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), z)) : Bool}, i, c, MN.eq_of_is_eq(i, c, he),
          Equal.sym(Bool, X.ix.same(X.ix.side(k, i), X.ix.side(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), i)), True{},
            Equal.trans(Bool, X.ix.same(X.ix.side(k, i), X.ix.side(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), i)), X.ix.same(X.ix.side(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), i), X.ix.side(k, i)), True{},
              same_sym(X.ix.side(k, i), X.ix.side(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), i)), near_side(k, i, l, r, p, hl, hr)))),
        hne)))

def stop_bit(+k: U32, +i: Nat, +c: Nat, +l: IM.Tr, +r: IM.Tr, +p: U32, +hlt: {Nat.is_lt(i, c) == False{} : Bool},
  +hl: {IM.tr.all(l, p, i, False{}) == True{} : Bool}, +hr: {IM.tr.all(r, p, i, True{}) == True{} : Bool},
  +hne: {X.ix.same(X.ix.side(k, c), X.ix.side(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), c)) == False{} : Bool}) -> {Nat.is_lt(c, i) == True{} : Bool}:
  sb.k(Nat.is_eq(i, c), k, i, c, l, r, p, {==}, hlt, hl, hr, hne)

# keys alike with p below a bit i above c, the key n alike with p below
# c + 1: each alike with n below c, and at c
def all_down(t: IM.Tr, +p: U32, +n: U32, +i: Nat, +c: Nat, +sd: Bool, +h: {IM.tr.all(t, p, i, sd) == True{} : Bool}, +hci: {Nat.is_le(1n+c, i) == True{} : Bool},
  +hn: {IM.tr.agree(n, p, 1n+c) == True{} : Bool}) -> {IM.tr.all(t, n, c, X.ix.side(n, c)) == True{} : Bool}:
  match t:
    case IM.Lf{+x, +k}:
      +hkn = agree_trans(k, p, n, 1n+c, agree_le(k, p, 1n+c, i, hci, and_l(IM.tr.agree(k, p, i), X.ix.same(X.ix.side(k, i), sd), h)), agree_sym(n, p, 1n+c, hn))
      and_intro(IM.tr.agree(k, n, c), X.ix.same(X.ix.side(k, c), X.ix.side(n, c)), and_r(X.ix.same(X.ix.side(k, c), X.ix.side(n, c)), IM.tr.agree(k, n, c), hkn), and_l(X.ix.same(X.ix.side(k, c), X.ix.side(n, c)), IM.tr.agree(k, n, c), hkn))
    case IM.Br{+b, +j, +l, +r}:
      and_intro(IM.tr.all(l, n, c, X.ix.side(n, c)), IM.tr.all(r, n, c, X.ix.side(n, c)), all_down(l, p, n, i, c, sd, and_l(IM.tr.all(l, p, i, sd), IM.tr.all(r, p, i, sd), h), hci, hn),
        all_down(r, p, n, i, c, sd, and_r(IM.tr.all(l, p, i, sd), IM.tr.all(r, p, i, sd), h), hci, hn))

# a tree's invariant from a lower bit: a leaf's below 32, a branch's below its own
def ok_lo.br(+b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +lo: Nat, +lo2: Nat, +h: {IM.tr.ok(IM.Br{b, i, l, r}, lo) == True{} : Bool}, +hle: {Nat.is_le(lo2, i) == True{} : Bool}) ->
  {IM.tr.ok(IM.Br{b, i, l, r}, lo2) == True{} : Bool}:
  and_intro(Nat.is_le(lo2, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), hle,
    and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(r, 1n+i)))), h))

def not_false(+b: Bool, +h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, MB.true_ne_false()(h))

def na.k(+sd: Bool, +k: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +p: U32, +hsd: {X.ix.side(k, i) == sd : Bool},
  +ihl: {IM.tr.agree(IM.tr.near(l, k), p, i) == True{} : Bool}, +ihr: {IM.tr.agree(IM.tr.near(r, k), p, i) == True{} : Bool}) -> {IM.tr.agree(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), p, i) == True{} : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {IM.tr.agree(X.ix.pick(_, IM.tr.near(r, k), IM.tr.near(l, k)), p, i) == True{} : Bool}
      ihr
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {IM.tr.agree(X.ix.pick(_, IM.tr.near(r, k), IM.tr.near(l, k)), p, i) == True{} : Bool}
      ihl

# the key a branch's descent meets alike with what every key below it is
def near_agree(+k: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +p: U32, +hl: {IM.tr.all(l, p, i, False{}) == True{} : Bool}, +hr: {IM.tr.all(r, p, i, True{}) == True{} : Bool}) -> {IM.tr.agree(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), p, i) == True{} : Bool}:
  na.k(X.ix.side(k, i), k, i, l, r, p, {==},
    and_l(IM.tr.agree(IM.tr.near(l, k), p, i), X.ix.same(X.ix.side(IM.tr.near(l, k), i), False{}), all_near(l, k, p, i, False{}, hl)),
    and_l(IM.tr.agree(IM.tr.near(r, k), p, i), X.ix.same(X.ix.side(IM.tr.near(r, k), i), True{}), all_near(r, k, p, i, True{}, hr)))

# the new branch at bit c above the node U the placement stops at: k's
# leaf on k's side, U's keys on the other, all alike below c
def ok_join(+sdc: Bool, +U: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +lo: Nat, +n: U32, +hsdc: {X.ix.side(k, c) == sdc : Bool},
  +hlo: {Nat.is_le(lo, c) == True{} : Bool}, +hc32: {Nat.is_lt(c, 32n) == True{} : Bool},
  +hS1: {IM.tr.all(U, n, c, X.ix.side(n, c)) == True{} : Bool}, +hag: {IM.tr.agree(k, n, c) == True{} : Bool}, +hne: {X.ix.same(X.ix.side(k, c), X.ix.side(n, c)) == False{} : Bool},
  +hokU: {IM.tr.ok(U, 1n+c) == True{} : Bool}) -> {IM.tr.ok(IM.tr.join(X.ix.side(k, c), U, x, k, b, c), lo) == True{} : Bool}:
  match sdc:
    case True{}:
      +hn = ME.subst(Bool, z => {X.ix.same(z, X.ix.side(n, c)) == False{} : Bool}, X.ix.side(k, c), True{}, hsdc, hne)
      +hU0 = ME.subst(Bool, z => {IM.tr.all(U, n, c, z) == True{} : Bool}, X.ix.side(n, c), False{}, hn, hS1)
      +hfn = agree_sym(IM.tr.first(U), n, c, all_first(U, n, c, False{}, hU0))
      %Equal.sym(Bool, X.ix.side(k, c), True{}, hsdc) : {IM.tr.ok(IM.tr.join(_, U, x, k, b, c), lo) == True{} : Bool}
      and_intro(Nat.is_le(lo, c), Nat.is_lt(c, 32n) && (IM.tr.all(U, IM.tr.first(U), c, False{}) && (IM.tr.all(IM.Lf{x, k}, IM.tr.first(U), c, True{}) && (IM.tr.ok(U, 1n+c) && IM.tr.ok(IM.Lf{x, k}, 1n+c)))), hlo, and_intro(Nat.is_lt(c, 32n), IM.tr.all(U, IM.tr.first(U), c, False{}) && (IM.tr.all(IM.Lf{x, k}, IM.tr.first(U), c, True{}) && (IM.tr.ok(U, 1n+c) && IM.tr.ok(IM.Lf{x, k}, 1n+c))), hc32, and_intro(IM.tr.all(U, IM.tr.first(U), c, False{}), IM.tr.all(IM.Lf{x, k}, IM.tr.first(U), c, True{}) && (IM.tr.ok(U, 1n+c) && IM.tr.ok(IM.Lf{x, k}, 1n+c)), all_rep(U, n, IM.tr.first(U), c, False{}, hU0, hfn), and_intro(IM.tr.all(IM.Lf{x, k}, IM.tr.first(U), c, True{}), IM.tr.ok(U, 1n+c) && IM.tr.ok(IM.Lf{x, k}, 1n+c), and_intro(IM.tr.agree(k, IM.tr.first(U), c), X.ix.same(X.ix.side(k, c), True{}), agree_trans(k, n, IM.tr.first(U), c, hag, hfn), ME.subst(Bool, z => {X.ix.same(z, True{}) == True{} : Bool}, True{}, X.ix.side(k, c), Equal.sym(Bool, X.ix.side(k, c), True{}, hsdc), {==})), and_intro(IM.tr.ok(U, 1n+c), IM.tr.ok(IM.Lf{x, k}, 1n+c), hokU, lt_le(c, 32n, hc32))))))
    case False{}:
      +hn = not_false(X.ix.side(n, c), ME.subst(Bool, z => {X.ix.same(z, X.ix.side(n, c)) == False{} : Bool}, X.ix.side(k, c), False{}, hsdc, hne))
      +hU1 = ME.subst(Bool, z => {IM.tr.all(U, n, c, z) == True{} : Bool}, X.ix.side(n, c), True{}, hn, hS1)
      %Equal.sym(Bool, X.ix.side(k, c), False{}, hsdc) : {IM.tr.ok(IM.tr.join(_, U, x, k, b, c), lo) == True{} : Bool}
      and_intro(Nat.is_le(lo, c), Nat.is_lt(c, 32n) && (IM.tr.all(IM.Lf{x, k}, k, c, False{}) && (IM.tr.all(U, k, c, True{}) && (IM.tr.ok(IM.Lf{x, k}, 1n+c) && IM.tr.ok(U, 1n+c)))), hlo, and_intro(Nat.is_lt(c, 32n), IM.tr.all(IM.Lf{x, k}, k, c, False{}) && (IM.tr.all(U, k, c, True{}) && (IM.tr.ok(IM.Lf{x, k}, 1n+c) && IM.tr.ok(U, 1n+c))), hc32, and_intro(IM.tr.all(IM.Lf{x, k}, k, c, False{}), IM.tr.all(U, k, c, True{}) && (IM.tr.ok(IM.Lf{x, k}, 1n+c) && IM.tr.ok(U, 1n+c)), and_intro(IM.tr.agree(k, k, c), X.ix.same(X.ix.side(k, c), False{}), agree_refl(k, c), ME.subst(Bool, z => {X.ix.same(z, False{}) == True{} : Bool}, False{}, X.ix.side(k, c), Equal.sym(Bool, X.ix.side(k, c), False{}, hsdc), {==})), and_intro(IM.tr.all(U, k, c, True{}), IM.tr.ok(IM.Lf{x, k}, 1n+c) && IM.tr.ok(U, 1n+c), all_rep(U, n, k, c, True{}, hU1, agree_sym(k, n, c, hag)), and_intro(IM.tr.ok(IM.Lf{x, k}, 1n+c), IM.tr.ok(U, 1n+c), lt_le(c, 32n, hc32), hokU)))))

def pok.k(+lt: Bool, +sd: Bool, +b2: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +lo: Nat,
  +hlt: {Nat.is_lt(i, c) == lt : Bool}, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hok: {IM.tr.ok(IM.Br{b2, i, l, r}, lo) == True{} : Bool}, +hlo: {Nat.is_le(lo, c) == True{} : Bool}, +hc32: {Nat.is_lt(c, 32n) == True{} : Bool},
  +hag: {IM.tr.agree(k, X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), c) == True{} : Bool}, +hne: {X.ix.same(X.ix.side(k, c), X.ix.side(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), c)) == False{} : Bool},
  ihl: {IM.tr.agree(k, IM.tr.near(l, k), c) == True{} : Bool} -> {X.ix.same(X.ix.side(k, c), X.ix.side(IM.tr.near(l, k), c)) == False{} : Bool} -> {Nat.is_le(1n+i, c) == True{} : Bool} -> {IM.tr.ok(IM.tr.place(l, x, k, b, c), 1n+i) == True{} : Bool},
  ihr: {IM.tr.agree(k, IM.tr.near(r, k), c) == True{} : Bool} -> {X.ix.same(X.ix.side(k, c), X.ix.side(IM.tr.near(r, k), c)) == False{} : Bool} -> {Nat.is_le(1n+i, c) == True{} : Bool} -> {IM.tr.ok(IM.tr.place(r, x, k, b, c), 1n+i) == True{} : Bool}) ->
  {IM.tr.ok(IM.tr.place.k(lt, sd, b2, i, l, r, IM.tr.place(l, x, k, b, c), IM.tr.place(r, x, k, b, c), x, k, b, c), lo) == True{} : Bool}:
  match lt:
    case False{}:
      +hal = and_l(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok)))
      +har = and_l(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))
      +hci = stop_bit(k, i, c, l, r, IM.tr.first(l), hlt, hal, har, hne)
      +hNp = agree_le(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), IM.tr.first(l), 1n+c, i, lt_le(c, i, hci), near_agree(k, i, l, r, IM.tr.first(l), hal, har))
      ok_join(X.ix.side(k, c), IM.Br{b2, i, l, r}, x, k, b, c, lo, X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), {==}, hlo, hc32,
        and_intro(IM.tr.all(l, X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), c, X.ix.side(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), c)), IM.tr.all(r, X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), c, X.ix.side(X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), c)), all_down(l, IM.tr.first(l), X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), i, c, False{}, hal, lt_le(c, i, hci), hNp),
          all_down(r, IM.tr.first(l), X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), i, c, True{}, har, lt_le(c, i, hci), hNp)),
        hag, hne, ok_lo.br(b2, i, l, r, lo, 1n+c, hok, lt_le(c, i, hci)))
    case True{}:
      match sd:
        case True{}:
          +hal = and_l(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok)))
          +har = and_l(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))
          +hka = agree_trans(k, X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), IM.tr.first(l), i, agree_le(k, X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), i, c, le_trans_b(i, 1n+i, c, le_succ_b(i), lt_le(i, c, hlt)), hag), near_agree(k, i, l, r, IM.tr.first(l), hal, har))
          and_intro(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(IM.tr.place(r, x, k, b, c), IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(IM.tr.place(r, x, k, b, c), 1n+i)))), and_l(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok), and_intro(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(IM.tr.place(r, x, k, b, c), IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(IM.tr.place(r, x, k, b, c), 1n+i))), and_l(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok)), and_intro(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(IM.tr.place(r, x, k, b, c), IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(IM.tr.place(r, x, k, b, c), 1n+i)), hal, and_intro(IM.tr.all(IM.tr.place(r, x, k, b, c), IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && IM.tr.ok(IM.tr.place(r, x, k, b, c), 1n+i), place_all(r, x, k, b, c, IM.tr.first(l), i, True{}, har, and_intro(IM.tr.agree(k, IM.tr.first(l), i), X.ix.same(X.ix.side(k, i), True{}), hka, ME.subst(Bool, z => {X.ix.same(z, True{}) == True{} : Bool}, True{}, X.ix.side(k, i), Equal.sym(Bool, X.ix.side(k, i), True{}, hsd), {==}))), and_intro(IM.tr.ok(l, 1n+i), IM.tr.ok(IM.tr.place(r, x, k, b, c), 1n+i), and_l(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))), ihr(ME.subst(Bool, z => {IM.tr.agree(k, X.ix.pick(z, IM.tr.near(r, k), IM.tr.near(l, k)), c) == True{} : Bool}, X.ix.side(k, i), True{}, hsd, hag))(ME.subst(Bool, z => {X.ix.same(X.ix.side(k, c), X.ix.side(X.ix.pick(z, IM.tr.near(r, k), IM.tr.near(l, k)), c)) == False{} : Bool}, X.ix.side(k, i), True{}, hsd, hne))(lt_le(i, c, hlt)))))))
        case False{}:
          +hal = and_l(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok)))
          +har = and_l(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))
          +hka = agree_trans(k, X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), IM.tr.first(l), i, agree_le(k, X.ix.pick(X.ix.side(k, i), IM.tr.near(r, k), IM.tr.near(l, k)), i, c, le_trans_b(i, 1n+i, c, le_succ_b(i), lt_le(i, c, hlt)), hag), near_agree(k, i, l, r, IM.tr.first(l), hal, har))
          +hpl = place_all(l, x, k, b, c, IM.tr.first(l), i, False{}, hal, and_intro(IM.tr.agree(k, IM.tr.first(l), i), X.ix.same(X.ix.side(k, i), False{}), hka, ME.subst(Bool, z => {X.ix.same(z, False{}) == True{} : Bool}, False{}, X.ix.side(k, i), Equal.sym(Bool, X.ix.side(k, i), False{}, hsd), {==})))
          +hfl = agree_sym(IM.tr.first(IM.tr.place(l, x, k, b, c)), IM.tr.first(l), i, all_first(IM.tr.place(l, x, k, b, c), IM.tr.first(l), i, False{}, hpl))
          and_intro(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(IM.tr.place(l, x, k, b, c), IM.tr.first(IM.tr.place(l, x, k, b, c)), i, False{}) && (IM.tr.all(r, IM.tr.first(IM.tr.place(l, x, k, b, c)), i, True{}) && (IM.tr.ok(IM.tr.place(l, x, k, b, c), 1n+i) && IM.tr.ok(r, 1n+i)))), and_l(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok), and_intro(Nat.is_lt(i, 32n), IM.tr.all(IM.tr.place(l, x, k, b, c), IM.tr.first(IM.tr.place(l, x, k, b, c)), i, False{}) && (IM.tr.all(r, IM.tr.first(IM.tr.place(l, x, k, b, c)), i, True{}) && (IM.tr.ok(IM.tr.place(l, x, k, b, c), 1n+i) && IM.tr.ok(r, 1n+i))), and_l(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok)), and_intro(IM.tr.all(IM.tr.place(l, x, k, b, c), IM.tr.first(IM.tr.place(l, x, k, b, c)), i, False{}), IM.tr.all(r, IM.tr.first(IM.tr.place(l, x, k, b, c)), i, True{}) && (IM.tr.ok(IM.tr.place(l, x, k, b, c), 1n+i) && IM.tr.ok(r, 1n+i)), all_rep(IM.tr.place(l, x, k, b, c), IM.tr.first(l), IM.tr.first(IM.tr.place(l, x, k, b, c)), i, False{}, hpl, hfl), and_intro(IM.tr.all(r, IM.tr.first(IM.tr.place(l, x, k, b, c)), i, True{}), IM.tr.ok(IM.tr.place(l, x, k, b, c), 1n+i) && IM.tr.ok(r, 1n+i), all_rep(r, IM.tr.first(l), IM.tr.first(IM.tr.place(l, x, k, b, c)), i, True{}, har, hfl), and_intro(IM.tr.ok(IM.tr.place(l, x, k, b, c), 1n+i), IM.tr.ok(r, 1n+i), ihl(ME.subst(Bool, z => {IM.tr.agree(k, X.ix.pick(z, IM.tr.near(r, k), IM.tr.near(l, k)), c) == True{} : Bool}, X.ix.side(k, i), False{}, hsd, hag))(ME.subst(Bool, z => {X.ix.same(X.ix.side(k, c), X.ix.side(X.ix.pick(z, IM.tr.near(r, k), IM.tr.near(l, k)), c)) == False{} : Bool}, X.ix.side(k, i), False{}, hsd, hne))(lt_le(i, c, hlt)), and_r(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))))))))

# a put keeps the invariant, along the placement's way
def pok(T: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +lo: Nat, +hok: {IM.tr.ok(T, lo) == True{} : Bool}, +hlo: {Nat.is_le(lo, c) == True{} : Bool},
  +hc32: {Nat.is_lt(c, 32n) == True{} : Bool}, +hag: {IM.tr.agree(k, IM.tr.near(T, k), c) == True{} : Bool}, +hne: {X.ix.same(X.ix.side(k, c), X.ix.side(IM.tr.near(T, k), c)) == False{} : Bool}) ->
  {IM.tr.ok(IM.tr.place(T, x, k, b, c), lo) == True{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      ok_join(X.ix.side(k, c), IM.Lf{y, ky}, x, k, b, c, lo, ky, {==}, hlo, hc32,
        and_intro(IM.tr.agree(ky, ky, c), X.ix.same(X.ix.side(ky, c), X.ix.side(ky, c)), agree_refl(ky, c), same_refl(X.ix.side(ky, c))), hag, hne, lt_le(c, 32n, hc32))
    case IM.Br{+b2, +i, +l, +r}:
      pok.k(Nat.is_lt(i, c), X.ix.side(k, i), b2, i, l, r, x, k, b, c, lo, {==}, {==}, hok, hlo, hc32, hag, hne,
        hal => hnl => hll => pok(l, x, k, b, c, 1n+i, and_l(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))), hll, hc32, hal, hnl),
        har => hnr => hlr => pok(r, x, k, b, c, 1n+i, and_r(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))), hlr, hc32, har, hnr))

def put_inv.k(I: IM.Ix, +x: U32, +k: U32, +b: U32, +hi: {IM.ix.inv(I) == True{} : Bool}, +ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}) ->
  {IM.ix.inv(IM.ix.put(I, x, k, b)) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      {==}
    case IM.Has{+t}:
      +hgo = ne_found(k, IM.tr.near(t, k), Equal.trans(Bool, U32.is_eq(k, IM.tr.near(t, k)), U32.is_eq(IM.tr.near(t, k), k), False{}, ueq_comm(k, IM.tr.near(t, k)), near_ne(t, k, ha)))
      +hca = crit_ag(32n, 0n, k, IM.tr.near(t, k), X.ix.same(X.ix.side(k, 0n), X.ix.side(IM.tr.near(t, k), 0n)), {==}, {==}, hgo)
      pok(t, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k))), 0n, hi, zero_le_b(IM.cr.i(X.ix.diff(k, IM.tr.near(t, k)))), diff_lt(k, IM.tr.near(t, k), hgo),
        and_l(IM.tr.agree(k, IM.tr.near(t, k), IM.cr.i(X.ix.diff(k, IM.tr.near(t, k)))), Bool.not(X.ix.same(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k)))), X.ix.side(IM.tr.near(t, k), IM.cr.i(X.ix.diff(k, IM.tr.near(t, k)))))), hca),
        not_true(X.ix.same(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k)))), X.ix.side(IM.tr.near(t, k), IM.cr.i(X.ix.diff(k, IM.tr.near(t, k))))), and_r(IM.tr.agree(k, IM.tr.near(t, k), IM.cr.i(X.ix.diff(k, IM.tr.near(t, k)))), Bool.not(X.ix.same(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k)))), X.ix.side(IM.tr.near(t, k), IM.cr.i(X.ix.diff(k, IM.tr.near(t, k)))))), hca)))

def Laws.put_inv(I, x, k, b, hi, ha):
  put_inv.k(I, x, k, b, hi, ha)

# A removal's tree: its keys among the tree's; a subtree's invariant from
# a lower bit
def ok_lower(t: IM.Tr, +lo: Nat, +lo2: Nat, +h: {IM.tr.ok(t, lo) == True{} : Bool}, +hle: {Nat.is_le(lo2, lo) == True{} : Bool}) -> {IM.tr.ok(t, lo2) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      le_trans_b(lo2, lo, 32n, hle, h)
    case IM.Br{+b, +i, +l, +r}:
      ok_lo.br(b, i, l, r, lo, lo2, h, le_trans_b(lo2, lo, i, hle, and_l(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), h)))

def ca.r(+hit: Bool, +b: U32, +i: Nat, +l: IM.Tr, +cr: IM.Tr, +p: U32, +j: Nat, +sd: Bool, +hl: {IM.tr.all(l, p, j, sd) == True{} : Bool}, +hcr: {IM.tr.all(cr, p, j, sd) == True{} : Bool}) ->
  {IM.tr.all(IM.tr.cut.r(hit, b, i, l, cr), p, j, sd) == True{} : Bool}:
  match hit:
    case True{}:
      hl
    case False{}:
      and_intro(IM.tr.all(l, p, j, sd), IM.tr.all(cr, p, j, sd), hl, hcr)

def ca.l(+hit: Bool, +b: U32, +i: Nat, +r: IM.Tr, +cl: IM.Tr, +p: U32, +j: Nat, +sd: Bool, +hr: {IM.tr.all(r, p, j, sd) == True{} : Bool}, +hcl: {IM.tr.all(cl, p, j, sd) == True{} : Bool}) ->
  {IM.tr.all(IM.tr.cut.l(hit, b, i, r, cl), p, j, sd) == True{} : Bool}:
  match hit:
    case True{}:
      hr
    case False{}:
      and_intro(IM.tr.all(cl, p, j, sd), IM.tr.all(r, p, j, sd), hcl, hr)

def ca.k(+sdk: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +cl: IM.Tr, +cr: IM.Tr, +p: U32, +j: Nat, +sd: Bool,
  +hl: {IM.tr.all(l, p, j, sd) == True{} : Bool}, +hr: {IM.tr.all(r, p, j, sd) == True{} : Bool}, +hcl: {IM.tr.all(cl, p, j, sd) == True{} : Bool}, +hcr: {IM.tr.all(cr, p, j, sd) == True{} : Bool}) ->
  {IM.tr.all(IM.tr.cut.k(sdk, b, i, l, r, x, cl, cr), p, j, sd) == True{} : Bool}:
  match sdk:
    case True{}:
      ca.r(U32.is_eq(IM.tr.addr(r), x), b, i, l, cr, p, j, sd, hl, hcr)
    case False{}:
      ca.l(U32.is_eq(IM.tr.addr(l), x), b, i, r, cl, p, j, sd, hr, hcl)

def cut_all(t: IM.Tr, +x: U32, +k: U32, +p: U32, +j: Nat, +sd: Bool, +h: {IM.tr.all(t, p, j, sd) == True{} : Bool}) -> {IM.tr.all(IM.tr.cut(t, x, k), p, j, sd) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      h
    case IM.Br{+b, +i, +l, +r}:
      ca.k(X.ix.side(k, i), b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k), p, j, sd,
        and_l(IM.tr.all(l, p, j, sd), IM.tr.all(r, p, j, sd), h), and_r(IM.tr.all(l, p, j, sd), IM.tr.all(r, p, j, sd), h),
        cut_all(l, x, k, p, j, sd, and_l(IM.tr.all(l, p, j, sd), IM.tr.all(r, p, j, sd), h)), cut_all(r, x, k, p, j, sd, and_r(IM.tr.all(l, p, j, sd), IM.tr.all(r, p, j, sd), h)))

# a removal keeps the invariant: its parent given up for the sibling, from
# the parent's bound; else the cut below
def cok.r(+hit: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +lo: Nat, +hok: {IM.tr.ok(IM.Br{b, i, l, r}, lo) == True{} : Bool},
  ih: {hit == False{} : Bool} -> {IM.tr.ok(IM.tr.cut(r, x, k), 1n+i) == True{} : Bool}) -> {IM.tr.ok(IM.tr.cut.r(hit, b, i, l, IM.tr.cut(r, x, k)), lo) == True{} : Bool}:
  match hit:
    case True{}:
      ok_lower(l, 1n+i, lo, and_l(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))), le_trans_b(lo, i, 1n+i, and_l(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok), le_succ_b(i)))
    case False{}:
      and_intro(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(IM.tr.cut(r, x, k), IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(IM.tr.cut(r, x, k), 1n+i)))), and_l(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok), and_intro(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(IM.tr.cut(r, x, k), IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(IM.tr.cut(r, x, k), 1n+i))), and_l(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok)), and_intro(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(IM.tr.cut(r, x, k), IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && IM.tr.ok(IM.tr.cut(r, x, k), 1n+i)), and_l(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))), and_intro(IM.tr.all(IM.tr.cut(r, x, k), IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && IM.tr.ok(IM.tr.cut(r, x, k), 1n+i), cut_all(r, x, k, IM.tr.first(l), i, True{}, and_l(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))), and_intro(IM.tr.ok(l, 1n+i), IM.tr.ok(IM.tr.cut(r, x, k), 1n+i), and_l(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))), ih({==}))))))

def cok.l(+hit: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +lo: Nat, +hok: {IM.tr.ok(IM.Br{b, i, l, r}, lo) == True{} : Bool},
  ih: {hit == False{} : Bool} -> {IM.tr.ok(IM.tr.cut(l, x, k), 1n+i) == True{} : Bool}) -> {IM.tr.ok(IM.tr.cut.l(hit, b, i, r, IM.tr.cut(l, x, k)), lo) == True{} : Bool}:
  match hit:
    case True{}:
      ok_lower(r, 1n+i, lo, and_r(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))), le_trans_b(lo, i, 1n+i, and_l(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok), le_succ_b(i)))
    case False{}:
      +hcl = cut_all(l, x, k, IM.tr.first(l), i, False{}, and_l(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))
      +hf = agree_sym(IM.tr.first(IM.tr.cut(l, x, k)), IM.tr.first(l), i, all_first(IM.tr.cut(l, x, k), IM.tr.first(l), i, False{}, hcl))
      and_intro(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(IM.tr.cut(l, x, k), IM.tr.first(IM.tr.cut(l, x, k)), i, False{}) && (IM.tr.all(r, IM.tr.first(IM.tr.cut(l, x, k)), i, True{}) && (IM.tr.ok(IM.tr.cut(l, x, k), 1n+i) && IM.tr.ok(r, 1n+i)))), and_l(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok), and_intro(Nat.is_lt(i, 32n), IM.tr.all(IM.tr.cut(l, x, k), IM.tr.first(IM.tr.cut(l, x, k)), i, False{}) && (IM.tr.all(r, IM.tr.first(IM.tr.cut(l, x, k)), i, True{}) && (IM.tr.ok(IM.tr.cut(l, x, k), 1n+i) && IM.tr.ok(r, 1n+i))), and_l(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok)), and_intro(IM.tr.all(IM.tr.cut(l, x, k), IM.tr.first(IM.tr.cut(l, x, k)), i, False{}), IM.tr.all(r, IM.tr.first(IM.tr.cut(l, x, k)), i, True{}) && (IM.tr.ok(IM.tr.cut(l, x, k), 1n+i) && IM.tr.ok(r, 1n+i)), all_rep(IM.tr.cut(l, x, k), IM.tr.first(l), IM.tr.first(IM.tr.cut(l, x, k)), i, False{}, hcl, hf), and_intro(IM.tr.all(r, IM.tr.first(IM.tr.cut(l, x, k)), i, True{}), IM.tr.ok(IM.tr.cut(l, x, k), 1n+i) && IM.tr.ok(r, 1n+i), all_rep(r, IM.tr.first(l), IM.tr.first(IM.tr.cut(l, x, k)), i, True{}, and_l(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok)))), hf), and_intro(IM.tr.ok(IM.tr.cut(l, x, k), 1n+i), IM.tr.ok(r, 1n+i), ih({==}), and_r(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))))))))

def cok.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +lo: Nat, +hsd: {X.ix.side(k, i) == sd : Bool}, +hok: {IM.tr.ok(IM.Br{b, i, l, r}, lo) == True{} : Bool},
  +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(l), x) == False{} : Bool} -> {IM.tr.ok(IM.tr.cut(l, x, k), 1n+i) == True{} : Bool},
  ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(r), x) == False{} : Bool} -> {IM.tr.ok(IM.tr.cut(r, x, k), 1n+i) == True{} : Bool}) ->
  {IM.tr.ok(IM.tr.cut.k(X.ix.side(k, i), b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k)), lo) == True{} : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {IM.tr.ok(IM.tr.cut.k(_, b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k)), lo) == True{} : Bool}
      cok.r(U32.is_eq(IM.tr.addr(r), x), b, i, l, r, x, k, lo, hok, hn => ihr(hx_side(True{}, k, i, l, r, x, hsd, hx))(hn))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {IM.tr.ok(IM.tr.cut.k(_, b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k)), lo) == True{} : Bool}
      cok.l(U32.is_eq(IM.tr.addr(l), x), b, i, l, r, x, k, lo, hok, hn => ihl(hx_side(False{}, k, i, l, r, x, hsd, hx))(hn))

def cok(t: IM.Tr, +x: U32, +k: U32, +lo: Nat, +hok: {IM.tr.ok(t, lo) == True{} : Bool}, +hx: {IM.tr.look(t, k) == Some{x} : Maybe<&2, U32>},
  +hne: {U32.is_eq(IM.tr.addr(t), x) == False{} : Bool}) -> {IM.tr.ok(IM.tr.cut(t, x, k), lo) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      lf_absurd({IM.tr.ok(IM.tr.cut(IM.Lf{y, ky}, x, k), lo) == True{} : Bool}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      cok.k(X.ix.side(k, i), b, i, l, r, x, k, lo, {==}, hok, hx,
        hxl => hnl => cok(l, x, k, 1n+i, and_l(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))), hxl, hnl),
        hxr => hnr => cok(r, x, k, 1n+i, and_r(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))), hxr, hnr))

def del_inv.h(+only: Bool, +t: IM.Tr, +x: U32, +k: U32, +he: {U32.is_eq(IM.tr.addr(t), x) == only : Bool}, +hi: {IM.tr.ok(t, 0n) == True{} : Bool},
  +hx: {IM.tr.look(t, k) == Some{x} : Maybe<&2, U32>}) -> {IM.ix.inv(IM.ix.del.k(only, t, x, k)) == True{} : Bool}:
  match only:
    case True{}:
      {==}
    case False{}:
      cok(t, x, k, 0n, hi, hx, he)

def del_inv.k(I: IM.Ix, +x: U32, +k: U32, +hi: {IM.ix.inv(I) == True{} : Bool}, +hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}) ->
  {IM.ix.inv(IM.ix.del(I, x, k)) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      {==}
    case IM.Has{+t}:
      del_inv.h(U32.is_eq(IM.tr.addr(t), x), t, x, k, {==}, hi, hx)

def Laws.del_inv(I, x, k, hi, hx):
  del_inv.k(I, x, k, hi, hx)

# Layouts kept
# ============

# a tree whose nodes are apart from node x apart from x's leaf
def offn_apart(U: IM.Tr, +d: Nat, +x: U32, +k: U32, +h: {IM.tr.offn(U, d, x) == True{} : Bool}) -> {IM.tr.apart(U, IM.Lf{x, k}, d) == True{} : Bool}:
  match U:
    case IM.Lf{+y, +ky}:
      sep_sym(d, y, x, h)
    case IM.Br{+u, +j, +ul, +ur}:
      and_intro(IM.tr.offn(IM.Lf{x, k}, d, u), IM.tr.apart(ul, IM.Lf{x, k}, d) && IM.tr.apart(ur, IM.Lf{x, k}, d), sep_sym(d, u, x, and_l(IM.nd.sep(d, u, x), IM.tr.offn(ul, d, x) && IM.tr.offn(ur, d, x), h)),
        and_intro(IM.tr.apart(ul, IM.Lf{x, k}, d), IM.tr.apart(ur, IM.Lf{x, k}, d), offn_apart(ul, d, x, k, and_l(IM.tr.offn(ul, d, x), IM.tr.offn(ur, d, x), and_r(IM.nd.sep(d, u, x), IM.tr.offn(ul, d, x) && IM.tr.offn(ur, d, x), h))), offn_apart(ur, d, x, k, and_r(IM.tr.offn(ul, d, x), IM.tr.offn(ur, d, x), and_r(IM.nd.sep(d, u, x), IM.tr.offn(ul, d, x) && IM.tr.offn(ur, d, x), h)))))

# a tree apart from r and from the new nodes x and b, apart from r after a put
def apart_place(l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +d: Nat,
  +hap: {IM.tr.apart(l, r, d) == True{} : Bool}, +hlx: {IM.tr.offn(l, d, x) == True{} : Bool}, +hlb: {IM.tr.offn(l, d, b) == True{} : Bool}) -> {IM.tr.apart(l, IM.tr.place(r, x, k, b, c), d) == True{} : Bool}:
  match l:
    case IM.Lf{+y, +ky}:
      place_offn(r, x, k, b, c, d, y, hap, sep_sym(d, y, x, hlx), sep_sym(d, y, b, hlb))
    case IM.Br{+u, +j, +ul, +ur}:
      +hs = and_r(IM.tr.offn(r, d, u), IM.tr.apart(ul, r, d) && IM.tr.apart(ur, r, d), hap)
      and_intro(IM.tr.offn(IM.tr.place(r, x, k, b, c), d, u), IM.tr.apart(ul, IM.tr.place(r, x, k, b, c), d) && IM.tr.apart(ur, IM.tr.place(r, x, k, b, c), d),
        place_offn(r, x, k, b, c, d, u, and_l(IM.tr.offn(r, d, u), IM.tr.apart(ul, r, d) && IM.tr.apart(ur, r, d), hap), sep_sym(d, u, x, and_l(IM.nd.sep(d, u, x), IM.tr.offn(ul, d, x) && IM.tr.offn(ur, d, x), hlx)), sep_sym(d, u, b, and_l(IM.nd.sep(d, u, b), IM.tr.offn(ul, d, b) && IM.tr.offn(ur, d, b), hlb))),
        and_intro(IM.tr.apart(ul, IM.tr.place(r, x, k, b, c), d), IM.tr.apart(ur, IM.tr.place(r, x, k, b, c), d),
          apart_place(ul, r, x, k, b, c, d, and_l(IM.tr.apart(ul, r, d), IM.tr.apart(ur, r, d), hs), and_l(IM.tr.offn(ul, d, x), IM.tr.offn(ur, d, x), and_r(IM.nd.sep(d, u, x), IM.tr.offn(ul, d, x) && IM.tr.offn(ur, d, x), hlx)), and_l(IM.tr.offn(ul, d, b), IM.tr.offn(ur, d, b), and_r(IM.nd.sep(d, u, b), IM.tr.offn(ul, d, b) && IM.tr.offn(ur, d, b), hlb))),
          apart_place(ur, r, x, k, b, c, d, and_r(IM.tr.apart(ul, r, d), IM.tr.apart(ur, r, d), hs), and_r(IM.tr.offn(ul, d, x), IM.tr.offn(ur, d, x), and_r(IM.nd.sep(d, u, x), IM.tr.offn(ul, d, x) && IM.tr.offn(ur, d, x), hlx)), and_r(IM.tr.offn(ul, d, b), IM.tr.offn(ur, d, b), and_r(IM.nd.sep(d, u, b), IM.tr.offn(ul, d, b) && IM.tr.offn(ur, d, b), hlb)))))

def lay_join(+sd: Bool, +U: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +d: Nat, +hU: {IM.tr.lay(U, d) == True{} : Bool}, +hokx: {IM.nd.ok(x, d) == True{} : Bool}, +hokb: {IM.nd.ok(b, d) == True{} : Bool},
  +hsxb: {IM.nd.sep(d, x, b) == True{} : Bool}, +hUx: {IM.tr.offn(U, d, x) == True{} : Bool}, +hUb: {IM.tr.offn(U, d, b) == True{} : Bool}) -> {IM.tr.lay(IM.tr.join(sd, U, x, k, b, c), d) == True{} : Bool}:
  match sd:
    case True{}:
      and_intro(IM.nd.ok(b, d), IM.tr.offn(U, d, b) && (IM.tr.offn(IM.Lf{x, k}, d, b) && (IM.tr.apart(U, IM.Lf{x, k}, d) && (IM.tr.lay(U, d) && IM.tr.lay(IM.Lf{x, k}, d)))), hokb, and_intro(IM.tr.offn(U, d, b), IM.tr.offn(IM.Lf{x, k}, d, b) && (IM.tr.apart(U, IM.Lf{x, k}, d) && (IM.tr.lay(U, d) && IM.tr.lay(IM.Lf{x, k}, d))), hUb, and_intro(IM.tr.offn(IM.Lf{x, k}, d, b), IM.tr.apart(U, IM.Lf{x, k}, d) && (IM.tr.lay(U, d) && IM.tr.lay(IM.Lf{x, k}, d)), hsxb, and_intro(IM.tr.apart(U, IM.Lf{x, k}, d), IM.tr.lay(U, d) && IM.tr.lay(IM.Lf{x, k}, d), offn_apart(U, d, x, k, hUx), and_intro(IM.tr.lay(U, d), IM.tr.lay(IM.Lf{x, k}, d), hU, hokx)))))
    case False{}:
      and_intro(IM.nd.ok(b, d), IM.tr.offn(IM.Lf{x, k}, d, b) && (IM.tr.offn(U, d, b) && (IM.tr.apart(IM.Lf{x, k}, U, d) && (IM.tr.lay(IM.Lf{x, k}, d) && IM.tr.lay(U, d)))), hokb, and_intro(IM.tr.offn(IM.Lf{x, k}, d, b), IM.tr.offn(U, d, b) && (IM.tr.apart(IM.Lf{x, k}, U, d) && (IM.tr.lay(IM.Lf{x, k}, d) && IM.tr.lay(U, d))), hsxb, and_intro(IM.tr.offn(U, d, b), IM.tr.apart(IM.Lf{x, k}, U, d) && (IM.tr.lay(IM.Lf{x, k}, d) && IM.tr.lay(U, d)), hUb, and_intro(IM.tr.apart(IM.Lf{x, k}, U, d), IM.tr.lay(IM.Lf{x, k}, d) && IM.tr.lay(U, d), hUx, and_intro(IM.tr.lay(IM.Lf{x, k}, d), IM.tr.lay(U, d), hokx, hU)))))

def lay.k(+lt: Bool, +sdi: Bool, +b2: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +d: Nat,
  +hl: {IM.tr.lay(IM.Br{b2, i, l, r}, d) == True{} : Bool}, +hokx: {IM.nd.ok(x, d) == True{} : Bool}, +hokb: {IM.nd.ok(b, d) == True{} : Bool}, +hsxb: {IM.nd.sep(d, x, b) == True{} : Bool},
  +hTx: {IM.tr.offn(IM.Br{b2, i, l, r}, d, x) == True{} : Bool}, +hTb: {IM.tr.offn(IM.Br{b2, i, l, r}, d, b) == True{} : Bool},
  +ihl: {IM.tr.lay(IM.tr.place(l, x, k, b, c), d) == True{} : Bool}, +ihr: {IM.tr.lay(IM.tr.place(r, x, k, b, c), d) == True{} : Bool}) ->
  {IM.tr.lay(IM.tr.place.k(lt, sdi, b2, i, l, r, IM.tr.place(l, x, k, b, c), IM.tr.place(r, x, k, b, c), x, k, b, c), d) == True{} : Bool}:
  match lt:
    case False{}:
      lay_join(X.ix.side(k, c), IM.Br{b2, i, l, r}, x, k, b, c, d, hl, hokx, hokb, hsxb, hTx, hTb)
    case True{}:
      match sdi:
        case True{}:
          and_intro(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(IM.tr.place(r, x, k, b, c), d, b2) && (IM.tr.apart(l, IM.tr.place(r, x, k, b, c), d) && (IM.tr.lay(l, d) && IM.tr.lay(IM.tr.place(r, x, k, b, c), d)))), and_l(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl), and_intro(IM.tr.offn(l, d, b2), IM.tr.offn(IM.tr.place(r, x, k, b, c), d, b2) && (IM.tr.apart(l, IM.tr.place(r, x, k, b, c), d) && (IM.tr.lay(l, d) && IM.tr.lay(IM.tr.place(r, x, k, b, c), d))), and_l(IM.tr.offn(l, d, b2), IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl)), and_intro(IM.tr.offn(IM.tr.place(r, x, k, b, c), d, b2), IM.tr.apart(l, IM.tr.place(r, x, k, b, c), d) && (IM.tr.lay(l, d) && IM.tr.lay(IM.tr.place(r, x, k, b, c), d)), place_offn(r, x, k, b, c, d, b2, and_l(IM.tr.offn(r, d, b2), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b2), IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))), sep_sym(d, b2, x, and_l(IM.nd.sep(d, b2, x), IM.tr.offn(l, d, x) && IM.tr.offn(r, d, x), hTx)), sep_sym(d, b2, b, and_l(IM.nd.sep(d, b2, b), IM.tr.offn(l, d, b) && IM.tr.offn(r, d, b), hTb))), and_intro(IM.tr.apart(l, IM.tr.place(r, x, k, b, c), d), IM.tr.lay(l, d) && IM.tr.lay(IM.tr.place(r, x, k, b, c), d), apart_place(l, r, x, k, b, c, d, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b2), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b2), IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl)))), and_l(IM.tr.offn(l, d, x), IM.tr.offn(r, d, x), and_r(IM.nd.sep(d, b2, x), IM.tr.offn(l, d, x) && IM.tr.offn(r, d, x), hTx)), and_l(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b), and_r(IM.nd.sep(d, b2, b), IM.tr.offn(l, d, b) && IM.tr.offn(r, d, b), hTb))), and_intro(IM.tr.lay(l, d), IM.tr.lay(IM.tr.place(r, x, k, b, c), d), and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b2), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b2), IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))), ihr)))))
        case False{}:
          and_intro(IM.nd.ok(b2, d), IM.tr.offn(IM.tr.place(l, x, k, b, c), d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(IM.tr.place(l, x, k, b, c), r, d) && (IM.tr.lay(IM.tr.place(l, x, k, b, c), d) && IM.tr.lay(r, d)))), and_l(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl), and_intro(IM.tr.offn(IM.tr.place(l, x, k, b, c), d, b2), IM.tr.offn(r, d, b2) && (IM.tr.apart(IM.tr.place(l, x, k, b, c), r, d) && (IM.tr.lay(IM.tr.place(l, x, k, b, c), d) && IM.tr.lay(r, d))), place_offn(l, x, k, b, c, d, b2, and_l(IM.tr.offn(l, d, b2), IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl)), sep_sym(d, b2, x, and_l(IM.nd.sep(d, b2, x), IM.tr.offn(l, d, x) && IM.tr.offn(r, d, x), hTx)), sep_sym(d, b2, b, and_l(IM.nd.sep(d, b2, b), IM.tr.offn(l, d, b) && IM.tr.offn(r, d, b), hTb))), and_intro(IM.tr.offn(r, d, b2), IM.tr.apart(IM.tr.place(l, x, k, b, c), r, d) && (IM.tr.lay(IM.tr.place(l, x, k, b, c), d) && IM.tr.lay(r, d)), and_l(IM.tr.offn(r, d, b2), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b2), IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))), and_intro(IM.tr.apart(IM.tr.place(l, x, k, b, c), r, d), IM.tr.lay(IM.tr.place(l, x, k, b, c), d) && IM.tr.lay(r, d), apart_sym(IM.tr.place(l, x, k, b, c), r, d, apart_place(r, l, x, k, b, c, d, apart_sym(r, l, d, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b2), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b2), IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))), and_r(IM.tr.offn(l, d, x), IM.tr.offn(r, d, x), and_r(IM.nd.sep(d, b2, x), IM.tr.offn(l, d, x) && IM.tr.offn(r, d, x), hTx)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b), and_r(IM.nd.sep(d, b2, b), IM.tr.offn(l, d, b) && IM.tr.offn(r, d, b), hTb)))), and_intro(IM.tr.lay(IM.tr.place(l, x, k, b, c), d), IM.tr.lay(r, d), ihl, and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b2), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b2), IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))))))))

def place_lay(T: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +d: Nat, +hl: {IM.tr.lay(T, d) == True{} : Bool}, +hokx: {IM.nd.ok(x, d) == True{} : Bool}, +hokb: {IM.nd.ok(b, d) == True{} : Bool}, +hsxb: {IM.nd.sep(d, x, b) == True{} : Bool},
  +hTx: {IM.tr.offn(T, d, x) == True{} : Bool}, +hTb: {IM.tr.offn(T, d, b) == True{} : Bool}) -> {IM.tr.lay(IM.tr.place(T, x, k, b, c), d) == True{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      lay_join(X.ix.side(k, c), IM.Lf{y, ky}, x, k, b, c, d, hl, hokx, hokb, hsxb, hTx, hTb)
    case IM.Br{+b2, +i, +l, +r}:
      lay.k(Nat.is_lt(i, c), X.ix.side(k, i), b2, i, l, r, x, k, b, c, d, hl, hokx, hokb, hsxb, hTx, hTb,
        place_lay(l, x, k, b, c, d, and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b2), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b2), IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))), hokx, hokb, hsxb, and_l(IM.tr.offn(l, d, x), IM.tr.offn(r, d, x), and_r(IM.nd.sep(d, b2, x), IM.tr.offn(l, d, x) && IM.tr.offn(r, d, x), hTx)), and_l(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b), and_r(IM.nd.sep(d, b2, b), IM.tr.offn(l, d, b) && IM.tr.offn(r, d, b), hTb))),
        place_lay(r, x, k, b, c, d, and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b2), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b2), IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b2, d), IM.tr.offn(l, d, b2) && (IM.tr.offn(r, d, b2) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))), hokx, hokb, hsxb, and_r(IM.tr.offn(l, d, x), IM.tr.offn(r, d, x), and_r(IM.nd.sep(d, b2, x), IM.tr.offn(l, d, x) && IM.tr.offn(r, d, x), hTx)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b), and_r(IM.nd.sep(d, b2, b), IM.tr.offn(l, d, b) && IM.tr.offn(r, d, b), hTb))))

def put_lay.k(I: IM.Ix, +s: U32, +x: U32, +k: U32, +b: U32, +d: Nat, +hl: {IM.ix.lay(I, s, d) == True{} : Bool}, +hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}) ->
  {IM.ix.lay(IM.ix.put(I, x, k, b), s, d) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      and_intro(IM.nd.ok(s, d), IM.tr.offn(IM.Lf{x, k}, d, s) && IM.tr.lay(IM.Lf{x, k}, d), hl,
        and_intro(IM.tr.offn(IM.Lf{x, k}, d, s), IM.tr.lay(IM.Lf{x, k}, d), and_r(IM.nd.ok(x, d), IM.nd.sep(d, x, s), hfr), and_l(IM.nd.ok(x, d), IM.nd.sep(d, x, s), hfr)))
    case IM.Has{+t}:
      +f0 = and_l(IM.nd.ok(x, d), IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(t, d, x) && IM.tr.offn(t, d, b))))), hfr)
      +f1 = and_r(IM.nd.ok(x, d), IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(t, d, x) && IM.tr.offn(t, d, b))))), hfr)
      +f2 = and_r(IM.nd.ok(b, d), IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(t, d, x) && IM.tr.offn(t, d, b)))), f1)
      +f3 = and_r(IM.nd.sep(d, x, b), IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(t, d, x) && IM.tr.offn(t, d, b))), f2)
      +f4 = and_r(IM.nd.sep(d, x, s), IM.nd.sep(d, b, s) && (IM.tr.offn(t, d, x) && IM.tr.offn(t, d, b)), f3)
      +f5 = and_r(IM.nd.sep(d, b, s), IM.tr.offn(t, d, x) && IM.tr.offn(t, d, b), f4)
      +h1 = and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl)
      and_intro(IM.nd.ok(s, d), IM.tr.offn(IM.tr.place(t, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k)))), d, s) && IM.tr.lay(IM.tr.place(t, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k)))), d), and_l(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl),
        and_intro(IM.tr.offn(IM.tr.place(t, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k)))), d, s), IM.tr.lay(IM.tr.place(t, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k)))), d),
          place_offn(t, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k))), d, s, and_l(IM.tr.offn(t, d, s), IM.tr.lay(t, d), h1), and_l(IM.nd.sep(d, x, s), IM.nd.sep(d, b, s) && (IM.tr.offn(t, d, x) && IM.tr.offn(t, d, b)), f3), and_l(IM.nd.sep(d, b, s), IM.tr.offn(t, d, x) && IM.tr.offn(t, d, b), f4)),
          place_lay(t, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k))), d, and_r(IM.tr.offn(t, d, s), IM.tr.lay(t, d), h1), f0, and_l(IM.nd.ok(b, d), IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(t, d, x) && IM.tr.offn(t, d, b)))), f1),
            and_l(IM.nd.sep(d, x, b), IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(t, d, x) && IM.tr.offn(t, d, b))), f2), and_l(IM.tr.offn(t, d, x), IM.tr.offn(t, d, b), f5), and_r(IM.tr.offn(t, d, x), IM.tr.offn(t, d, b), f5))))

def Laws.put_lay(I, s, x, k, b, d, hl, hfr):
  put_lay.k(I, s, x, k, b, d, hl, hfr)

# a removal's tree: its nodes among the tree's
def apart_cut(l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +d: Nat, +h: {IM.tr.apart(l, r, d) == True{} : Bool}) -> {IM.tr.apart(l, IM.tr.cut(r, x, k), d) == True{} : Bool}:
  match l:
    case IM.Lf{+y, +ky}:
      cut_offn(r, x, k, d, y, h)
    case IM.Br{+u, +j, +ul, +ur}:
      +hs = and_r(IM.tr.offn(r, d, u), IM.tr.apart(ul, r, d) && IM.tr.apart(ur, r, d), h)
      and_intro(IM.tr.offn(IM.tr.cut(r, x, k), d, u), IM.tr.apart(ul, IM.tr.cut(r, x, k), d) && IM.tr.apart(ur, IM.tr.cut(r, x, k), d), cut_offn(r, x, k, d, u, and_l(IM.tr.offn(r, d, u), IM.tr.apart(ul, r, d) && IM.tr.apart(ur, r, d), h)),
        and_intro(IM.tr.apart(ul, IM.tr.cut(r, x, k), d), IM.tr.apart(ur, IM.tr.cut(r, x, k), d), apart_cut(ul, r, x, k, d, and_l(IM.tr.apart(ul, r, d), IM.tr.apart(ur, r, d), hs)), apart_cut(ur, r, x, k, d, and_r(IM.tr.apart(ul, r, d), IM.tr.apart(ur, r, d), hs))))

def cl.r(+hit: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +d: Nat, +hl: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool}, +ih: {IM.tr.lay(IM.tr.cut(r, x, k), d) == True{} : Bool}) ->
  {IM.tr.lay(IM.tr.cut.r(hit, b, i, l, IM.tr.cut(r, x, k)), d) == True{} : Bool}:
  match hit:
    case True{}:
      and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl)))))
    case False{}:
      and_intro(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(IM.tr.cut(r, x, k), d, b) && (IM.tr.apart(l, IM.tr.cut(r, x, k), d) && (IM.tr.lay(l, d) && IM.tr.lay(IM.tr.cut(r, x, k), d)))), and_l(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl), and_intro(IM.tr.offn(l, d, b), IM.tr.offn(IM.tr.cut(r, x, k), d, b) && (IM.tr.apart(l, IM.tr.cut(r, x, k), d) && (IM.tr.lay(l, d) && IM.tr.lay(IM.tr.cut(r, x, k), d))), and_l(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl)), and_intro(IM.tr.offn(IM.tr.cut(r, x, k), d, b), IM.tr.apart(l, IM.tr.cut(r, x, k), d) && (IM.tr.lay(l, d) && IM.tr.lay(IM.tr.cut(r, x, k), d)), cut_offn(r, x, k, d, b, and_l(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl)))), and_intro(IM.tr.apart(l, IM.tr.cut(r, x, k), d), IM.tr.lay(l, d) && IM.tr.lay(IM.tr.cut(r, x, k), d), apart_cut(l, r, x, k, d, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))), and_intro(IM.tr.lay(l, d), IM.tr.lay(IM.tr.cut(r, x, k), d), and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))), ih)))))

def cl.l(+hit: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +d: Nat, +hl: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool}, +ih: {IM.tr.lay(IM.tr.cut(l, x, k), d) == True{} : Bool}) ->
  {IM.tr.lay(IM.tr.cut.l(hit, b, i, r, IM.tr.cut(l, x, k)), d) == True{} : Bool}:
  match hit:
    case True{}:
      and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl)))))
    case False{}:
      and_intro(IM.nd.ok(b, d), IM.tr.offn(IM.tr.cut(l, x, k), d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(IM.tr.cut(l, x, k), r, d) && (IM.tr.lay(IM.tr.cut(l, x, k), d) && IM.tr.lay(r, d)))), and_l(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl), and_intro(IM.tr.offn(IM.tr.cut(l, x, k), d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(IM.tr.cut(l, x, k), r, d) && (IM.tr.lay(IM.tr.cut(l, x, k), d) && IM.tr.lay(r, d))), cut_offn(l, x, k, d, b, and_l(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))), and_intro(IM.tr.offn(r, d, b), IM.tr.apart(IM.tr.cut(l, x, k), r, d) && (IM.tr.lay(IM.tr.cut(l, x, k), d) && IM.tr.lay(r, d)), and_l(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))), and_intro(IM.tr.apart(IM.tr.cut(l, x, k), r, d), IM.tr.lay(IM.tr.cut(l, x, k), d) && IM.tr.lay(r, d), apart_sym(IM.tr.cut(l, x, k), r, d, apart_cut(r, l, x, k, d, apart_sym(r, l, d, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))))), and_intro(IM.tr.lay(IM.tr.cut(l, x, k), d), IM.tr.lay(r, d), ih, and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))))))))

def cl.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +d: Nat, +hl: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool}, +ihl: {IM.tr.lay(IM.tr.cut(l, x, k), d) == True{} : Bool}, +ihr: {IM.tr.lay(IM.tr.cut(r, x, k), d) == True{} : Bool}) ->
  {IM.tr.lay(IM.tr.cut.k(sd, b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k)), d) == True{} : Bool}:
  match sd:
    case True{}:
      cl.r(U32.is_eq(IM.tr.addr(r), x), b, i, l, r, x, k, d, hl, ihr)
    case False{}:
      cl.l(U32.is_eq(IM.tr.addr(l), x), b, i, l, r, x, k, d, hl, ihl)

def cut_lay(T: IM.Tr, +x: U32, +k: U32, +d: Nat, +hl: {IM.tr.lay(T, d) == True{} : Bool}) -> {IM.tr.lay(IM.tr.cut(T, x, k), d) == True{} : Bool}:
  match T:
    case IM.Lf{+y, +ky}:
      hl
    case IM.Br{+b, +i, +l, +r}:
      cl.k(X.ix.side(k, i), b, i, l, r, x, k, d, hl, cut_lay(l, x, k, d, and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl)))))), cut_lay(r, x, k, d, and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl)))))))

def del_lay.h(+only: Bool, +t: IM.Tr, +s: U32, +x: U32, +k: U32, +d: Nat, +hl: {IM.ix.lay(IM.Has{t}, s, d) == True{} : Bool}) -> {IM.ix.lay(IM.ix.del.k(only, t, x, k), s, d) == True{} : Bool}:
  match only:
    case True{}:
      and_l(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl)
    case False{}:
      +h1 = and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl)
      and_intro(IM.nd.ok(s, d), IM.tr.offn(IM.tr.cut(t, x, k), d, s) && IM.tr.lay(IM.tr.cut(t, x, k), d), and_l(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl),
        and_intro(IM.tr.offn(IM.tr.cut(t, x, k), d, s), IM.tr.lay(IM.tr.cut(t, x, k), d), cut_offn(t, x, k, d, s, and_l(IM.tr.offn(t, d, s), IM.tr.lay(t, d), h1)), cut_lay(t, x, k, d, and_r(IM.tr.offn(t, d, s), IM.tr.lay(t, d), h1))))

def del_lay.k(I: IM.Ix, +s: U32, +x: U32, +k: U32, +d: Nat, +hl: {IM.ix.lay(I, s, d) == True{} : Bool}) -> {IM.ix.lay(IM.ix.del(I, x, k), s, d) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      hl
    case IM.Has{+t}:
      del_lay.h(U32.is_eq(IM.tr.addr(t), x), t, s, x, k, d, hl)

def Laws.del_lay(I, s, x, k, d, hl):
  del_lay.k(I, s, x, k, d, hl)

# The ring's lists
# ================

def fa.k(+e: Bool, +y: U32, +r1: Maybe<&2, U32>, +r2: Maybe<&2, U32>) -> {RG.first.k(e, y, IM.mb.or(r1, r2)) == IM.mb.or(RG.first.k(e, y, r1), r2) : Maybe<&2, U32>}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

# a first match over two lists: the first's, else the second's
def first_app(xs: List<&2, U32>, +ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +k: U32) ->
  {RG.first(List.append(&2, U32, xs, ys), v, d, k) == IM.mb.or(RG.first(xs, v, d, k), RG.first(ys, v, d, k)) : Maybe<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %Equal.sym(Maybe<&2, U32>, RG.first(List.append(&2, U32, t, ys), v, d, k), IM.mb.or(RG.first(t, v, d, k), RG.first(ys, v, d, k)), first_app(t, ys, v, d, k)) :
        {RG.first.k(RG.pos.is(v, d, y, k), y, _) == IM.mb.or(RG.first.k(RG.pos.is(v, d, y, k), y, RG.first(t, v, d, k)), RG.first(ys, v, d, k)) : Maybe<&2, U32>}
      fa.k(RG.pos.is(v, d, y, k), y, RG.first(t, v, d, k), RG.first(ys, v, d, k))

def hit_fk(+e: Bool, +y: U32) -> {IM.mb.hit(e, y) == RG.first.k(e, y, None{}) : Maybe<&2, U32>}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def at_first.t(T: IM.Tr, +t0: LAT.Tree<U32>, +d: Nat, +p: U32, +s: U32, +k: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, T, p, s) == True{} : Bool}) -> {IM.tr.at(T, k) == RG.first(IM.tr.leaves(T), AD.view(U32, LAT.fromT(U32, t0)), d, k) : Maybe<&2, U32>}:
  match T:
    case IM.Lf{+y, +ky}:
      +hk2 = MS.u32_eq_of_is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky, and_l(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky), U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 3 : U32)), s),
        and_r(Bool.not(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y))), U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky) && U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 3 : U32)), s),
          and_r(U32.is_eq(p, y), Bool.not(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, y))) && (U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky) && U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 3 : U32)), s)), hre))))
      %LA.get_view(U32, LAT.fromT(U32, t0), d, (y + 2 : U32), hft, hd32) : {IM.mb.hit(U32.is_eq(ky, k), y) == RG.first.k(RG.pos.is.m(_, k), y, None{}) : Maybe<&2, U32>}
      %wd(t0, d, (y + 2 : U32), hft, hd32) :
        {IM.mb.hit(U32.is_eq(ky, k), y) == RG.first.k(U32.is_eq(_, k), y, None{}) : Maybe<&2, U32>}
      %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 2 : U32)), ky, hk2) : {IM.mb.hit(U32.is_eq(ky, k), y) == RG.first.k(U32.is_eq(_, k), y, None{}) : Maybe<&2, U32>}
      hit_fk(U32.is_eq(ky, k), y)
    case IM.Br{+b, +i, +l, +r}:
      +hr3 = and_r(Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), and_r(X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s)), and_r(U32.is_eq(p, b), X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, b)), i) && (IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s) && IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s))), hre)))
      %Equal.sym(Maybe<&2, U32>, RG.first(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), AD.view(U32, LAT.fromT(U32, t0)), d, k), IM.mb.or(RG.first(IM.tr.leaves(l), AD.view(U32, LAT.fromT(U32, t0)), d, k), RG.first(IM.tr.leaves(r), AD.view(U32, LAT.fromT(U32, t0)), d, k)),
        first_app(IM.tr.leaves(l), IM.tr.leaves(r), AD.view(U32, LAT.fromT(U32, t0)), d, k)) : {IM.mb.or(IM.tr.at(l, k), IM.tr.at(r, k)) == _ : Maybe<&2, U32>}
      %Equal.sym(Maybe<&2, U32>, IM.tr.at(l, k), RG.first(IM.tr.leaves(l), AD.view(U32, LAT.fromT(U32, t0)), d, k), at_first.t(l, t0, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s, k, hft, hd32, and_l(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), hr3))) :
        {IM.mb.or(_, IM.tr.at(r, k)) == IM.mb.or(RG.first(IM.tr.leaves(l), AD.view(U32, LAT.fromT(U32, t0)), d, k), RG.first(IM.tr.leaves(r), AD.view(U32, LAT.fromT(U32, t0)), d, k)) : Maybe<&2, U32>}
      %Equal.sym(Maybe<&2, U32>, IM.tr.at(r, k), RG.first(IM.tr.leaves(r), AD.view(U32, LAT.fromT(U32, t0)), d, k), at_first.t(r, t0, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s, k, hft, hd32, and_r(IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, l, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 2 : U32)), s), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, r, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 3 : U32)), s), hr3))) :
        {IM.mb.or(RG.first(IM.tr.leaves(l), AD.view(U32, LAT.fromT(U32, t0)), d, k), _) == IM.mb.or(RG.first(IM.tr.leaves(l), AD.view(U32, LAT.fromT(U32, t0)), d, k), RG.first(IM.tr.leaves(r), AD.view(U32, LAT.fromT(U32, t0)), d, k)) : Maybe<&2, U32>}
      {==}

def at_first.k(I: IM.Ix, +t0: LAT.Tree<U32>, +d: Nat, +s: U32, +k: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, I) == True{} : Bool}) -> {IM.ix.at(I, k) == RG.first(IM.ix.leaves(I), AD.view(U32, LAT.fromT(U32, t0)), d, k) : Maybe<&2, U32>}:
  match I:
    case IM.Ept{}:
      {==}
    case IM.Has{+t}:
      at_first.t(t, t0, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s, k, hft, hd32,
        and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, t, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre))

def at_first.m(-w: Array<U32>, +d: Nat, +s: U32, +I: IM.Ix, +k: U32, hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}, m: LAT.Mirror(U32, w)) -> {IM.ix.at(I, k) == RG.first(IM.ix.leaves(I), AD.view(U32, w), d, k) : Maybe<&2, U32>}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  %e : {IM.ix.at(I, k) == RG.first(IM.ix.leaves(I), AD.view(U32, _), d, k) : Maybe<&2, U32>}
  at_first.k(I, t0, d, s, k, hft, hd32, LAB.subst(Array<U32>, q => {IM.ix.real(AD.view(U32, q), d, s, I) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e), hr))

def Laws.at_first(w, d, s, I, k, hf, hd32, hr):
  at_first.m(w, d, s, I, k, hf, hd32, hr, LAT.mirror(U32, w))

# Leaves
# ======

def or_swap3(+a: Bool, +b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match b:
        case True{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}

def or_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match b:
        case True{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}

def or_j1(+a: Bool, +e: Bool) -> {Bool.or(a, Bool.or(e, False{})) == Bool.or(e, a) : Bool}:
  match a:
    case True{}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}


def orf_l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MB.true_ne_false()(h))
    case False{}:
      {==}

def orf_r(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, MB.true_ne_false()(h))
    case False{}:
      h

def has_app(xs: List<&2, U32>, +ys: List<&2, U32>, +z: U32) -> {RG.has(List.append(&2, U32, xs, ys), z) == Bool.or(RG.has(xs, z), RG.has(ys, z)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %Equal.sym(Bool, RG.has(List.append(&2, U32, t, ys), z), Bool.or(RG.has(t, z), RG.has(ys, z)), has_app(t, ys, z)) : {Bool.or(U32.is_eq(y, z), _) == Bool.or(Bool.or(U32.is_eq(y, z), RG.has(t, z)), RG.has(ys, z)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(U32.is_eq(y, z), RG.has(t, z)), RG.has(ys, z)), Bool.or(U32.is_eq(y, z), Bool.or(RG.has(t, z), RG.has(ys, z))), or_assoc(U32.is_eq(y, z), RG.has(t, z), RG.has(ys, z)))

def wo_app(xs: List<&2, U32>, +ys: List<&2, U32>, +x: U32) -> {RG.without(List.append(&2, U32, xs, ys), x) == List.append(&2, U32, RG.without(xs, x), RG.without(ys, x)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %Equal.sym(List<&2, U32>, RG.without(List.append(&2, U32, t, ys), x), List.append(&2, U32, RG.without(t, x), RG.without(ys, x)), wo_app(t, ys, x)) : {List.append(&2, U32, RG.keep(U32.is_eq(y, x), y), _) == List.append(&2, U32, List.append(&2, U32, RG.keep(U32.is_eq(y, x), y), RG.without(t, x)), RG.without(ys, x)) : List<&2, U32>}
      Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, RG.keep(U32.is_eq(y, x), y), RG.without(t, x)), RG.without(ys, x)), List.append(&2, U32, RG.keep(U32.is_eq(y, x), y), List.append(&2, U32, RG.without(t, x), RG.without(ys, x))), ML.append_assoc(&2, U32, RG.keep(U32.is_eq(y, x), y), RG.without(t, x), RG.without(ys, x)))

def wo_absent(xs: List<&2, U32>, +x: U32, +h: {RG.has(xs, x) == False{} : Bool}) -> {RG.without(xs, x) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %Equal.sym(Bool, U32.is_eq(y, x), False{}, orf_l(U32.is_eq(y, x), RG.has(t, x), h)) : {List.append(&2, U32, RG.keep(_, y), RG.without(t, x)) == Con{y, t} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, RG.without(t, x), t, wo_absent(t, x, orf_r(U32.is_eq(y, x), RG.has(t, x), h))) : {Con{y, _} == Con{y, t} : List<&2, U32>}
      {==}

# a tree apart from x: x none of its leaves
def absent_of_offn(t: IM.Tr, +d: Nat, +x: U32, +h: {IM.tr.offn(t, d, x) == True{} : Bool}) -> {RG.has(IM.tr.leaves(t), x) == False{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      %Equal.sym(Bool, U32.is_eq(y, x), False{}, sep_ne(d, x, y, sep_sym(d, y, x, h))) : {Bool.or(_, False{}) == False{} : Bool}
      {==}
    case IM.Br{+u, +j, +l, +r}:
      %Equal.sym(Bool, RG.has(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), x), Bool.or(RG.has(IM.tr.leaves(l), x), RG.has(IM.tr.leaves(r), x)), has_app(IM.tr.leaves(l), IM.tr.leaves(r), x)) : {_ == False{} : Bool}
      %Equal.sym(Bool, RG.has(IM.tr.leaves(l), x), False{}, absent_of_offn(l, d, x, and_l(IM.tr.offn(l, d, x), IM.tr.offn(r, d, x), and_r(IM.nd.sep(d, u, x), IM.tr.offn(l, d, x) && IM.tr.offn(r, d, x), h)))) : {Bool.or(_, RG.has(IM.tr.leaves(r), x)) == False{} : Bool}
      absent_of_offn(r, d, x, and_r(IM.tr.offn(l, d, x), IM.tr.offn(r, d, x), and_r(IM.nd.sep(d, u, x), IM.tr.offn(l, d, x) && IM.tr.offn(r, d, x), h)))

# a tree apart from one in which x is the cursor at a key: apart from x
def apart_look(l: IM.Tr, +r: IM.Tr, +d: Nat, +k: U32, +x: U32, +hap: {IM.tr.apart(l, r, d) == True{} : Bool}, +hx: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>}) -> {IM.tr.offn(l, d, x) == True{} : Bool}:
  match l:
    case IM.Lf{+y, +ky}:
      sep_sym(d, x, y, look_sep(r, y, d, k, x, hap, hx))
    case IM.Br{+u, +j, +ul, +ur}:
      +hs = and_r(IM.tr.offn(r, d, u), IM.tr.apart(ul, r, d) && IM.tr.apart(ur, r, d), hap)
      and_intro(IM.nd.sep(d, u, x), IM.tr.offn(ul, d, x) && IM.tr.offn(ur, d, x), sep_sym(d, x, u, look_sep(r, u, d, k, x, and_l(IM.tr.offn(r, d, u), IM.tr.apart(ul, r, d) && IM.tr.apart(ur, r, d), hap), hx)),
        and_intro(IM.tr.offn(ul, d, x), IM.tr.offn(ur, d, x), apart_look(ul, r, d, k, x, and_l(IM.tr.apart(ul, r, d), IM.tr.apart(ur, r, d), hs), hx), apart_look(ur, r, d, k, x, and_r(IM.tr.apart(ul, r, d), IM.tr.apart(ur, r, d), hs), hx)))

# no node apart from itself
def sep_irr(-A: Type, +d: Nat, +a: U32, +h: {IM.nd.sep(d, a, a) == True{} : Bool}) -> A:
  Empty.absurd(A, MB.false_ne_true()(Equal.trans(Bool, False{}, Nat.is_eq(AD.slot(a, d), AD.slot(a, d)), True{},
    Equal.sym(Bool, Nat.is_eq(AD.slot(a, d), AD.slot(a, d)), False{}, off0(a, d, a, and_l(KMd.off.words(KMd.nw(a), d, a), KMd.off.words(KMd.nw(a), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(a), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(a), d, (a + 3 : U32))),
      and_l(IM.nd.disj(d, a, a), IM.nd.disj(d, a, a), h)))),
    MN.is_eq_refl(AD.slot(a, d)))))

# the tree at x, x the cursor at a key below it, laid out apart: x's leaf
def hit_leaves(r: IM.Tr, +x: U32, +k: U32, +d: Nat, +hl: {IM.tr.lay(r, d) == True{} : Bool}, +hx: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>},
  +hh: {U32.is_eq(IM.tr.addr(r), x) == True{} : Bool}) -> {IM.tr.leaves(r) == [x] : List<&2, U32>}:
  match r:
    case IM.Lf{+y, +ky}:
      Equal.cong(U32, List<&2, U32>, z => [z], y, x, MS.u32_eq_of_is_eq(y, x, hh))
    case IM.Br{+b, +i, +rl, +rr}:
      sep_irr({IM.tr.leaves(IM.Br{b, i, rl, rr}) == [x] : List<&2, U32>}, d, x,
        ME.subst(U32, z => {IM.nd.sep(d, x, z) == True{} : Bool}, b, x, MS.u32_eq_of_is_eq(b, x, hh),
          ls.k(X.ix.side(k, i), d, i, rl, rr, k, x, b, {==}, hx, hxl => look_sep(rl, b, d, k, x, and_l(IM.tr.offn(rl, d, b), IM.tr.offn(rr, d, b) && (IM.tr.apart(rl, rr, d) && (IM.tr.lay(rl, d) && (IM.tr.lay(rr, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(rl, d, b) && (IM.tr.offn(rr, d, b) && (IM.tr.apart(rl, rr, d) && (IM.tr.lay(rl, d) && (IM.tr.lay(rr, d))))), hl)), hxl), hxr => look_sep(rr, b, d, k, x, and_l(IM.tr.offn(rr, d, b), IM.tr.apart(rl, rr, d) && (IM.tr.lay(rl, d) && (IM.tr.lay(rr, d))), and_r(IM.tr.offn(rl, d, b), IM.tr.offn(rr, d, b) && (IM.tr.apart(rl, rr, d) && (IM.tr.lay(rl, d) && (IM.tr.lay(rr, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(rl, d, b) && (IM.tr.offn(rr, d, b) && (IM.tr.apart(rl, rr, d) && (IM.tr.lay(rl, d) && (IM.tr.lay(rr, d))))), hl))), hxr))))

def wo_self(+x: U32) -> {RG.without([x], x) == [] : List<&2, U32>}:
  %Equal.sym(Bool, U32.is_eq(x, x), True{}, is_eq_self(x)) : {List.append(&2, U32, RG.keep(_, x), []) == [] : List<&2, U32>}
  {==}

def dl.r(+hit: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +d: Nat, +hhit: {U32.is_eq(IM.tr.addr(r), x) == hit : Bool},
  +hl: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool}, +hxr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>},
  ih: {hit == False{} : Bool} -> {IM.tr.leaves(IM.tr.cut(r, x, k)) == RG.without(IM.tr.leaves(r), x) : List<&2, U32>}) ->
  {IM.tr.leaves(IM.tr.cut.r(hit, b, i, l, IM.tr.cut(r, x, k))) == RG.without(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), x) : List<&2, U32>}:
  match hit:
    case True{}:
      %Equal.sym(List<&2, U32>, RG.without(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), x), List.append(&2, U32, RG.without(IM.tr.leaves(l), x), RG.without(IM.tr.leaves(r), x)), wo_app(IM.tr.leaves(l), IM.tr.leaves(r), x)) : {IM.tr.leaves(l) == _ : List<&2, U32>}
      %Equal.sym(List<&2, U32>, RG.without(IM.tr.leaves(l), x), IM.tr.leaves(l), wo_absent(IM.tr.leaves(l), x, absent_of_offn(l, d, x, apart_look(l, r, d, k, x, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl)))), hxr)))) : {IM.tr.leaves(l) == List.append(&2, U32, _, RG.without(IM.tr.leaves(r), x)) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, IM.tr.leaves(r), [x], hit_leaves(r, x, k, d, and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))), hxr, hhit)) : {IM.tr.leaves(l) == List.append(&2, U32, IM.tr.leaves(l), RG.without(_, x)) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, RG.without([x], x), [], wo_self(x)) : {IM.tr.leaves(l) == List.append(&2, U32, IM.tr.leaves(l), _) : List<&2, U32>}
      Equal.sym(List<&2, U32>, List.append(&2, U32, IM.tr.leaves(l), []), IM.tr.leaves(l), ML.append_nil(&2, U32, IM.tr.leaves(l)))
    case False{}:
      %Equal.sym(List<&2, U32>, RG.without(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), x), List.append(&2, U32, RG.without(IM.tr.leaves(l), x), RG.without(IM.tr.leaves(r), x)), wo_app(IM.tr.leaves(l), IM.tr.leaves(r), x)) : {List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(IM.tr.cut(r, x, k))) == _ : List<&2, U32>}
      %Equal.sym(List<&2, U32>, RG.without(IM.tr.leaves(l), x), IM.tr.leaves(l), wo_absent(IM.tr.leaves(l), x, absent_of_offn(l, d, x, apart_look(l, r, d, k, x, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl)))), hxr)))) : {List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(IM.tr.cut(r, x, k))) == List.append(&2, U32, _, RG.without(IM.tr.leaves(r), x)) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, IM.tr.leaves(IM.tr.cut(r, x, k)), RG.without(IM.tr.leaves(r), x), ih({==})) : {List.append(&2, U32, IM.tr.leaves(l), _) == List.append(&2, U32, IM.tr.leaves(l), RG.without(IM.tr.leaves(r), x)) : List<&2, U32>}
      {==}

def dl.l(+hit: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +d: Nat, +hhit: {U32.is_eq(IM.tr.addr(l), x) == hit : Bool},
  +hl: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool}, +hxl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>},
  ih: {hit == False{} : Bool} -> {IM.tr.leaves(IM.tr.cut(l, x, k)) == RG.without(IM.tr.leaves(l), x) : List<&2, U32>}) ->
  {IM.tr.leaves(IM.tr.cut.l(hit, b, i, r, IM.tr.cut(l, x, k))) == RG.without(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), x) : List<&2, U32>}:
  match hit:
    case True{}:
      %Equal.sym(List<&2, U32>, RG.without(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), x), List.append(&2, U32, RG.without(IM.tr.leaves(l), x), RG.without(IM.tr.leaves(r), x)), wo_app(IM.tr.leaves(l), IM.tr.leaves(r), x)) : {IM.tr.leaves(r) == _ : List<&2, U32>}
      %Equal.sym(List<&2, U32>, RG.without(IM.tr.leaves(r), x), IM.tr.leaves(r), wo_absent(IM.tr.leaves(r), x, absent_of_offn(r, d, x, apart_look(r, l, d, k, x, apart_sym(r, l, d, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))), hxl)))) : {IM.tr.leaves(r) == List.append(&2, U32, RG.without(IM.tr.leaves(l), x), _) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, IM.tr.leaves(l), [x], hit_leaves(l, x, k, d, and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))), hxl, hhit)) : {IM.tr.leaves(r) == List.append(&2, U32, RG.without(_, x), IM.tr.leaves(r)) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, RG.without([x], x), [], wo_self(x)) : {IM.tr.leaves(r) == List.append(&2, U32, _, IM.tr.leaves(r)) : List<&2, U32>}
      {==}
    case False{}:
      %Equal.sym(List<&2, U32>, RG.without(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), x), List.append(&2, U32, RG.without(IM.tr.leaves(l), x), RG.without(IM.tr.leaves(r), x)), wo_app(IM.tr.leaves(l), IM.tr.leaves(r), x)) : {List.append(&2, U32, IM.tr.leaves(IM.tr.cut(l, x, k)), IM.tr.leaves(r)) == _ : List<&2, U32>}
      %Equal.sym(List<&2, U32>, RG.without(IM.tr.leaves(r), x), IM.tr.leaves(r), wo_absent(IM.tr.leaves(r), x, absent_of_offn(r, d, x, apart_look(r, l, d, k, x, apart_sym(r, l, d, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))), hxl)))) : {List.append(&2, U32, IM.tr.leaves(IM.tr.cut(l, x, k)), IM.tr.leaves(r)) == List.append(&2, U32, RG.without(IM.tr.leaves(l), x), _) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, IM.tr.leaves(IM.tr.cut(l, x, k)), RG.without(IM.tr.leaves(l), x), ih({==})) : {List.append(&2, U32, _, IM.tr.leaves(r)) == List.append(&2, U32, RG.without(IM.tr.leaves(l), x), IM.tr.leaves(r)) : List<&2, U32>}
      {==}

def dl.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +d: Nat, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hl: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool}, +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(l), x) == False{} : Bool} -> {IM.tr.leaves(IM.tr.cut(l, x, k)) == RG.without(IM.tr.leaves(l), x) : List<&2, U32>},
  ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(r), x) == False{} : Bool} -> {IM.tr.leaves(IM.tr.cut(r, x, k)) == RG.without(IM.tr.leaves(r), x) : List<&2, U32>}) ->
  {IM.tr.leaves(IM.tr.cut.k(X.ix.side(k, i), b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k))) == RG.without(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), x) : List<&2, U32>}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {IM.tr.leaves(IM.tr.cut.k(_, b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k))) == RG.without(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), x) : List<&2, U32>}
      dl.r(U32.is_eq(IM.tr.addr(r), x), b, i, l, r, x, k, d, {==}, hl, hx_side(True{}, k, i, l, r, x, hsd, hx), hn => ihr(hx_side(True{}, k, i, l, r, x, hsd, hx))(hn))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {IM.tr.leaves(IM.tr.cut.k(_, b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k))) == RG.without(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), x) : List<&2, U32>}
      dl.l(U32.is_eq(IM.tr.addr(l), x), b, i, l, r, x, k, d, {==}, hl, hx_side(False{}, k, i, l, r, x, hsd, hx), hn => ihl(hx_side(False{}, k, i, l, r, x, hsd, hx))(hn))

def dl(t: IM.Tr, +x: U32, +k: U32, +d: Nat, +hl: {IM.tr.lay(t, d) == True{} : Bool}, +hx: {IM.tr.look(t, k) == Some{x} : Maybe<&2, U32>},
  +hne: {U32.is_eq(IM.tr.addr(t), x) == False{} : Bool}) -> {IM.tr.leaves(IM.tr.cut(t, x, k)) == RG.without(IM.tr.leaves(t), x) : List<&2, U32>}:
  match t:
    case IM.Lf{+y, +ky}:
      lf_absurd({IM.tr.leaves(IM.tr.cut(IM.Lf{y, ky}, x, k)) == RG.without(IM.tr.leaves(IM.Lf{y, ky}), x) : List<&2, U32>}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      dl.k(X.ix.side(k, i), b, i, l, r, x, k, d, {==}, hl, hx,
        hxl => hnl => dl(l, x, k, d, and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))), hxl, hnl),
        hxr => hnr => dl(r, x, k, d, and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && (IM.tr.lay(r, d)), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d)))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && (IM.tr.lay(r, d))))), hl))))), hxr, hnr))

def del_leaves.h(+only: Bool, +t: IM.Tr, +s: U32, +x: U32, +k: U32, +d: Nat, +he: {U32.is_eq(IM.tr.addr(t), x) == only : Bool},
  +hl: {IM.tr.lay(t, d) == True{} : Bool}, +hx: {IM.tr.look(t, k) == Some{x} : Maybe<&2, U32>}) ->
  {IM.ix.leaves(IM.ix.del.k(only, t, x, k)) == RG.without(IM.tr.leaves(t), x) : List<&2, U32>}:
  match only:
    case True{}:
      %Equal.sym(List<&2, U32>, IM.tr.leaves(t), [x], hit_leaves(t, x, k, d, hl, hx, he)) : {[] == RG.without(_, x) : List<&2, U32>}
      Equal.sym(List<&2, U32>, RG.without([x], x), [], wo_self(x))
    case False{}:
      dl(t, x, k, d, hl, hx, he)

def del_leaves.k(I: IM.Ix, +s: U32, +x: U32, +k: U32, +d: Nat, +hl: {IM.ix.lay(I, s, d) == True{} : Bool}, +hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}) ->
  {IM.ix.leaves(IM.ix.del(I, x, k)) == RG.without(IM.ix.leaves(I), x) : List<&2, U32>}:
  match I:
    case IM.Ept{}:
      {==}
    case IM.Has{+t}:
      del_leaves.h(U32.is_eq(IM.tr.addr(t), x), t, s, x, k, d, {==}, and_r(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl)), hx)

def Laws.del_leaves(I, s, x, k, d, hl, hx):
  del_leaves.k(I, s, x, k, d, hl, hx)

def lj(+sd: Bool, +U: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +z: U32) -> {RG.has(IM.tr.leaves(IM.tr.join(sd, U, x, k, b, c)), z) == Bool.or(U32.is_eq(x, z), RG.has(IM.tr.leaves(U), z)) : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, RG.has(List.append(&2, U32, IM.tr.leaves(U), [x]), z), Bool.or(RG.has(IM.tr.leaves(U), z), RG.has([x], z)), has_app(IM.tr.leaves(U), [x], z)) : {_ == Bool.or(U32.is_eq(x, z), RG.has(IM.tr.leaves(U), z)) : Bool}
      or_j1(RG.has(IM.tr.leaves(U), z), U32.is_eq(x, z))
    case False{}:
      {==}

def lp.k(+lt: Bool, +sdi: Bool, +b2: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +z: U32,
  +ihl: {RG.has(IM.tr.leaves(IM.tr.place(l, x, k, b, c)), z) == Bool.or(U32.is_eq(x, z), RG.has(IM.tr.leaves(l), z)) : Bool}, +ihr: {RG.has(IM.tr.leaves(IM.tr.place(r, x, k, b, c)), z) == Bool.or(U32.is_eq(x, z), RG.has(IM.tr.leaves(r), z)) : Bool}) ->
  {RG.has(IM.tr.leaves(IM.tr.place.k(lt, sdi, b2, i, l, r, IM.tr.place(l, x, k, b, c), IM.tr.place(r, x, k, b, c), x, k, b, c)), z) == Bool.or(U32.is_eq(x, z), RG.has(IM.tr.leaves(IM.Br{b2, i, l, r}), z)) : Bool}:
  match lt:
    case False{}:
      lj(X.ix.side(k, c), IM.Br{b2, i, l, r}, x, k, b, c, z)
    case True{}:
      match sdi:
        case True{}:
          %Equal.sym(Bool, RG.has(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(IM.tr.place(r, x, k, b, c))), z), Bool.or(RG.has(IM.tr.leaves(l), z), RG.has(IM.tr.leaves(IM.tr.place(r, x, k, b, c)), z)), has_app(IM.tr.leaves(l), IM.tr.leaves(IM.tr.place(r, x, k, b, c)), z)) : {_ == Bool.or(U32.is_eq(x, z), RG.has(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), z)) : Bool}
          %Equal.sym(Bool, RG.has(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), z), Bool.or(RG.has(IM.tr.leaves(l), z), RG.has(IM.tr.leaves(r), z)), has_app(IM.tr.leaves(l), IM.tr.leaves(r), z)) : {Bool.or(RG.has(IM.tr.leaves(l), z), RG.has(IM.tr.leaves(IM.tr.place(r, x, k, b, c)), z)) == Bool.or(U32.is_eq(x, z), _) : Bool}
          %Equal.sym(Bool, RG.has(IM.tr.leaves(IM.tr.place(r, x, k, b, c)), z), Bool.or(U32.is_eq(x, z), RG.has(IM.tr.leaves(r), z)), ihr) : {Bool.or(RG.has(IM.tr.leaves(l), z), _) == Bool.or(U32.is_eq(x, z), Bool.or(RG.has(IM.tr.leaves(l), z), RG.has(IM.tr.leaves(r), z))) : Bool}
          or_swap3(RG.has(IM.tr.leaves(l), z), U32.is_eq(x, z), RG.has(IM.tr.leaves(r), z))
        case False{}:
          %Equal.sym(Bool, RG.has(List.append(&2, U32, IM.tr.leaves(IM.tr.place(l, x, k, b, c)), IM.tr.leaves(r)), z), Bool.or(RG.has(IM.tr.leaves(IM.tr.place(l, x, k, b, c)), z), RG.has(IM.tr.leaves(r), z)), has_app(IM.tr.leaves(IM.tr.place(l, x, k, b, c)), IM.tr.leaves(r), z)) : {_ == Bool.or(U32.is_eq(x, z), RG.has(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), z)) : Bool}
          %Equal.sym(Bool, RG.has(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), z), Bool.or(RG.has(IM.tr.leaves(l), z), RG.has(IM.tr.leaves(r), z)), has_app(IM.tr.leaves(l), IM.tr.leaves(r), z)) : {Bool.or(RG.has(IM.tr.leaves(IM.tr.place(l, x, k, b, c)), z), RG.has(IM.tr.leaves(r), z)) == Bool.or(U32.is_eq(x, z), _) : Bool}
          %Equal.sym(Bool, RG.has(IM.tr.leaves(IM.tr.place(l, x, k, b, c)), z), Bool.or(U32.is_eq(x, z), RG.has(IM.tr.leaves(l), z)), ihl) : {Bool.or(_, RG.has(IM.tr.leaves(r), z)) == Bool.or(U32.is_eq(x, z), Bool.or(RG.has(IM.tr.leaves(l), z), RG.has(IM.tr.leaves(r), z))) : Bool}
          or_assoc(U32.is_eq(x, z), RG.has(IM.tr.leaves(l), z), RG.has(IM.tr.leaves(r), z))

def place_leaves(t: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +z: U32) -> {RG.has(IM.tr.leaves(IM.tr.place(t, x, k, b, c)), z) == Bool.or(U32.is_eq(x, z), RG.has(IM.tr.leaves(t), z)) : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      lj(X.ix.side(k, c), IM.Lf{y, ky}, x, k, b, c, z)
    case IM.Br{+b2, +i, +l, +r}:
      lp.k(Nat.is_lt(i, c), X.ix.side(k, i), b2, i, l, r, x, k, b, c, z, place_leaves(l, x, k, b, c, z), place_leaves(r, x, k, b, c, z))

def put_leaves.k(I: IM.Ix, +x: U32, +k: U32, +b: U32, +z: U32) -> {RG.has(IM.ix.leaves(IM.ix.put(I, x, k, b)), z) == Bool.or(U32.is_eq(x, z), RG.has(IM.ix.leaves(I), z)) : Bool}:
  match I:
    case IM.Ept{}:
      {==}
    case IM.Has{+t}:
      place_leaves(t, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k))), z)

def Laws.put_leaves(I, x, k, b, z):
  put_leaves.k(I, x, k, b, z)

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

# The free list after an insert and a removal
# ===========================================

# a word of a full array, read through its view
def wg(w: Array<U32>, +d: Nat, +i: U32, hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
  {KMd.word(AD.view(U32, w), d, i) == Pair.snd(Array<U32>, U32, Array.get(U32, w, i)) : U32}:
  %LA.get_view(U32, w, d, i, hf, hd32) : {KMd.word.m(_) == Pair.snd(Array<U32>, U32, Array.get(U32, w, i)) : U32}
  {==}

def nf(+b: Bool, +h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

# The round trip: a node freed is the one the free list's head names
# next, its head never 0 (P.free, KMd.at_idx), for any word, by its bits

def ones(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, ones(p)}

def and_ones(+n: Nat, +t: Word(n)) -> {Word.and(n, t, ones(n)) == t : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{b, u}:
          match b:
            case True{}:
              Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.and(p, u, ones(p)), u, and_ones(p, u))
            case False{}:
              Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.and(p, u, ones(p)), u, and_ones(p, u))

def shlput_pad(+p: Nat, +c: Bool, +y: Word(p)) -> {Word.shl.put(1n+p, c, Word.shr.pad(p, y)) == WCon{c, y} : Word(1n+p)}:
  match p:
    case 0n:
      match y:
        case WNil{}:
          {==}
    case 1n+q:
      match y:
        case WCon{y0, y1}:
          Equal.cong(Word(1n+q), Word(2n+q), z => WCon{c, z}, Word.shl.put(1n+q, y0, Word.shr.pad(q, y1)), WCon{y0, y1}, shlput_pad(q, y0, y1))

def shl_pad(+p: Nat, +y: Word(p)) -> {Word.shl(1n+p, Word.shr.pad(p, y)) == WCon{False{}, y} : Word(1n+p)}:
  match p:
    case 0n:
      match y:
        case WNil{}:
          {==}
    case 1n+q:
      match y:
        case WCon{y0, y1}:
          Equal.cong(Word(1n+q), Word(2n+q), z => WCon{False{}, z}, Word.shl.put(1n+q, y0, Word.shr.pad(q, y1)), WCon{y0, y1}, shlput_pad(q, y0, y1))

# adding c and taking it back: the rest of a word after its first bit
def sub_add_go(+p: Nat, +t: Word(p), +c: Bool) -> {Word.adc(p, Word.adc(p, t, zeros(p), False{}, c), zeros(p), True{}, Bool.not(c)) == t : Word(p)}:
  match p:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+q:
      match t:
        case WCon{a, u}:
          match a:
            case False{}:
              match c:
                case False{}:
                  Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.adc(q, Word.adc(q, u, zeros(q), False{}, False{}), zeros(q), True{}, True{}), u, sub_add_go(q, u, False{}))
                case True{}:
                  Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.adc(q, Word.adc(q, u, zeros(q), False{}, False{}), zeros(q), True{}, True{}), u, sub_add_go(q, u, False{}))
            case True{}:
              match c:
                case False{}:
                  Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.adc(q, Word.adc(q, u, zeros(q), False{}, False{}), zeros(q), True{}, True{}), u, sub_add_go(q, u, False{}))
                case True{}:
                  Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.adc(q, Word.adc(q, u, zeros(q), False{}, True{}), zeros(q), True{}, False{}), u, sub_add_go(q, u, True{}))

def sub_add1(+x: U32) -> {U32.sub(U32.add(x, 1), 1) == x : U32}:
  match x:
    case U32{w}:
      match w:
        case WCon{a, t}:
          match a:
            case False{}:
              Equal.cong(Word(31n), U32, z => U32{WCon{False{}, z}}, Word.adc(31n, Word.adc(31n, t, zeros(31n), False{}, False{}), zeros(31n), True{}, True{}), t, sub_add_go(31n, t, False{}))
            case True{}:
              Equal.cong(Word(31n), U32, z => U32{WCon{True{}, z}}, Word.adc(31n, Word.adc(31n, t, zeros(31n), False{}, True{}), zeros(31n), True{}, False{}), t, sub_add_go(31n, t, True{}))

# the free list's head after a node is freed names that node's base
def fl_shape(+t: Word(30n)) -> {KMd.at_idx(((U32{Word.shr.pad(31n, Word.shr.pad(30n, t))} + 1 : U32))) == U32{WCon{False{}, WCon{False{}, t}}} : U32}:
  %Equal.sym(U32, U32.sub(U32.add(U32{Word.shr.pad(31n, Word.shr.pad(30n, t))}, 1), 1), U32{Word.shr.pad(31n, Word.shr.pad(30n, t))}, sub_add1(U32{Word.shr.pad(31n, Word.shr.pad(30n, t))})) : {U32.shln(_, 2n) == U32{WCon{False{}, WCon{False{}, t}}} : U32}
  %Equal.sym(Word(32n), Word.shl(32n, Word.shr.pad(31n, Word.shr.pad(30n, t))), WCon{False{}, Word.shr.pad(30n, t)}, shl_pad(31n, Word.shr.pad(30n, t))) : {U32{Word.shl(32n, _)} == U32{WCon{False{}, WCon{False{}, t}}} : U32}
  %Equal.sym(Word(31n), Word.shl.put(31n, False{}, Word.shr.pad(30n, t)), WCon{False{}, t}, shlput_pad(30n, False{}, t)) : {U32{WCon{False{}, _}} == U32{WCon{False{}, WCon{False{}, t}}} : U32}
  {==}

def base_shape(+b0: Bool, +b1: Bool, +t: Word(30n)) -> {P.base(U32{WCon{b0, WCon{b1, t}}}) == U32{WCon{False{}, WCon{False{}, t}}} : U32}:
  match b0:
    case True{}:
      match b1:
        case True{}:
          Equal.cong(Word(30n), U32, z => U32{WCon{False{}, WCon{False{}, z}}}, Word.and(30n, t, ones(30n)), t, and_ones(30n, t))
        case False{}:
          Equal.cong(Word(30n), U32, z => U32{WCon{False{}, WCon{False{}, z}}}, Word.and(30n, t, ones(30n)), t, and_ones(30n, t))
    case False{}:
      match b1:
        case True{}:
          Equal.cong(Word(30n), U32, z => U32{WCon{False{}, WCon{False{}, z}}}, Word.and(30n, t, ones(30n)), t, and_ones(30n, t))
        case False{}:
          Equal.cong(Word(30n), U32, z => U32{WCon{False{}, WCon{False{}, z}}}, Word.and(30n, t, ones(30n)), t, and_ones(30n, t))

def fl_idx(+r: U32) -> {KMd.at_idx(((r >> 2n : U32) + 1 : U32)) == P.base(r) : U32}:
  match r:
    case U32{w}:
      match w:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, t}:
              Equal.trans(U32, KMd.at_idx(((U32{Word.shr.pad(31n, Word.shr.pad(30n, t))} + 1 : U32))), U32{WCon{False{}, WCon{False{}, t}}}, P.base(U32{WCon{b0, WCon{b1, t}}}),
                fl_shape(t), Equal.sym(U32, P.base(U32{WCon{b0, WCon{b1, t}}}), U32{WCon{False{}, WCon{False{}, t}}}, base_shape(b0, b1, t)))

# that head is not 0: a word shifted right has its top bit clear, and
# all ones its top bit set
def top(p: Nat, w: Word(1n+p)) -> Bool:
  match p:
    case 0n:
      match w:
        case WCon{b, t}:
          b
    case 1n+q:
      match w:
        case WCon{b, t}:
          top(q, t)

def top_pad(+p: Nat, +y: Word(p)) -> {top(p, Word.shr.pad(p, y)) == False{} : Bool}:
  match p:
    case 0n:
      match y:
        case WNil{}:
          {==}
    case 1n+q:
      match y:
        case WCon{y0, y1}:
          top_pad(q, y1)

def fl_nz.k(+t: Word(30n), +e: Bool, +he: {U32.is_eq(((U32{Word.shr.pad(31n, Word.shr.pad(30n, t))} + 1 : U32)), 0) == e : Bool}) -> {U32.is_eq(((U32{Word.shr.pad(31n, Word.shr.pad(30n, t))} + 1 : U32)), 0) == False{} : Bool}:
  match e:
    case False{}:
      he
    case True{}:
      Empty.absurd({U32.is_eq(((U32{Word.shr.pad(31n, Word.shr.pad(30n, t))} + 1 : U32)), 0) == False{} : Bool},
        MB.true_ne_false()(Equal.trans(Bool, True{}, top(31n, uw(U32{Word.shr.pad(31n, Word.shr.pad(30n, t))})), False{},
          Equal.cong(U32, Bool, z => top(31n, uw(z)), U32.sub(0, 1), U32{Word.shr.pad(31n, Word.shr.pad(30n, t))},
            Equal.trans(U32, U32.sub(0, 1), U32.sub(U32.add(U32{Word.shr.pad(31n, Word.shr.pad(30n, t))}, 1), 1), U32{Word.shr.pad(31n, Word.shr.pad(30n, t))},
              Equal.cong(U32, U32, z => U32.sub(z, 1), 0, U32.add(U32{Word.shr.pad(31n, Word.shr.pad(30n, t))}, 1), Equal.sym(U32, U32.add(U32{Word.shr.pad(31n, Word.shr.pad(30n, t))}, 1), 0, MS.u32_eq_of_is_eq(U32.add(U32{Word.shr.pad(31n, Word.shr.pad(30n, t))}, 1), 0, he))),
              sub_add1(U32{Word.shr.pad(31n, Word.shr.pad(30n, t))}))),
          top_pad(31n, Word.shr.pad(30n, t)))))

def fl_nz(+r: U32) -> {U32.is_eq(((r >> 2n : U32) + 1 : U32), 0) == False{} : Bool}:
  match r:
    case U32{w}:
      match w:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, t}:
              fl_nz.k(t, U32.is_eq(((U32{Word.shr.pad(31n, Word.shr.pad(30n, t))} + 1 : U32)), 0), {==})


# word j's slot none of ns's words 1, the words a free list's chain reads
def offw(ns: List<&2, U32>, +d: Nat, +j: U32) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+n, +r}:
      Bool.not(Nat.is_eq(AD.slot(j, d), AD.slot((n + 1 : U32), d))) && offw(r, d, j)

# a write off the nodes' words 1 keeps the free list's chain
def chain_set(ns: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +h: U32, +j: U32, +val: U32,
  +ho: {offw(ns, d, j) == True{} : Bool}, +hc: {KMd.chain(ns, v, d, h) == True{} : Bool}) -> {KMd.chain(ns, List.set(&2, U32, v, AD.slot(j, d), val), d, h) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      +hjn = not_true(Nat.is_eq(AD.slot(j, d), AD.slot((n + 1 : U32), d)), and_l(Bool.not(Nat.is_eq(AD.slot(j, d), AD.slot((n + 1 : U32), d))), offw(r, d, j), ho))
      %wl_ne(v, d, j, (n + 1 : U32), val, hjn) : {(Bool.not(U32.is_eq(h, 0)) && (U32.is_eq(KMd.at_idx(h), n) && KMd.chain(r, List.set(&2, U32, v, AD.slot(j, d), val), d, _))) == True{} : Bool}
      and_intro(Bool.not(U32.is_eq(h, 0)), U32.is_eq(KMd.at_idx(h), n) && KMd.chain(r, List.set(&2, U32, v, AD.slot(j, d), val), d, KMd.word(v, d, (n + 1 : U32))), and_l(Bool.not(U32.is_eq(h, 0)), U32.is_eq(KMd.at_idx(h), n) && KMd.chain(r, v, d, KMd.word(v, d, (n + 1 : U32))), hc),
        and_intro(U32.is_eq(KMd.at_idx(h), n), KMd.chain(r, List.set(&2, U32, v, AD.slot(j, d), val), d, KMd.word(v, d, (n + 1 : U32))), and_l(U32.is_eq(KMd.at_idx(h), n), KMd.chain(r, v, d, KMd.word(v, d, (n + 1 : U32))), and_r(Bool.not(U32.is_eq(h, 0)), U32.is_eq(KMd.at_idx(h), n) && KMd.chain(r, v, d, KMd.word(v, d, (n + 1 : U32))), hc)),
          chain_set(r, v, d, KMd.word(v, d, (n + 1 : U32)), j, val, and_r(Bool.not(Nat.is_eq(AD.slot(j, d), AD.slot((n + 1 : U32), d))), offw(r, d, j), ho),
            and_r(U32.is_eq(KMd.at_idx(h), n), KMd.chain(r, v, d, KMd.word(v, d, (n + 1 : U32))), and_r(Bool.not(U32.is_eq(h, 0)), U32.is_eq(KMd.at_idx(h), n) && KMd.chain(r, v, d, KMd.word(v, d, (n + 1 : U32))), hc)))))

# and, off the head too, keeps the head
def fl_keepv(+ns: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +j: U32, +val: U32,
  +hjh: {Nat.is_eq(AD.slot(j, d), AD.slot(P.at_fh(), d)) == False{} : Bool}, +ho: {offw(ns, d, j) == True{} : Bool}, +hc: {KMd.chain(ns, v, d, KMd.word(v, d, P.at_fh())) == True{} : Bool}) -> {KMd.chain(ns, List.set(&2, U32, v, AD.slot(j, d), val), d, KMd.word(List.set(&2, U32, v, AD.slot(j, d), val), d, P.at_fh())) == True{} : Bool}:
  %wl_ne(v, d, j, P.at_fh(), val, hjh) : {KMd.chain(ns, List.set(&2, U32, v, AD.slot(j, d), val), d, _) == True{} : Bool}
  chain_set(ns, v, d, KMd.word(v, d, P.at_fh()), j, val, ho, hc)

# a node Pn freed after a write at L (P.free, P.wr), the nodes ns the free
# list's first before: Pn, then ns, the first after
def fl_free(+t0: LAT.Tree<U32>, +d: Nat, +L: U32, +S: U32, +Pn: U32, +ns: List<&2, U32>, +hf: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hb: {P.base(Pn) == Pn : U32}, +hLh: {Nat.is_eq(AD.slot(L, d), AD.slot(P.at_fh(), d)) == False{} : Bool}, +hPh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((Pn + 1 : U32), d)) == False{} : Bool},
  +hoL: {offw(ns, d, L) == True{} : Bool}, +hoP: {offw(ns, d, Pn) == True{} : Bool}, +hoP1: {offw(ns, d, (Pn + 1 : U32)) == True{} : Bool}, +hoH: {offw(ns, d, P.at_fh()) == True{} : Bool},
  +hc: {KMd.chain(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}) -> {KMd.chain(Con{Pn, ns}, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, P.at_fh())) == True{} : Bool}:
  %Equal.sym(U32, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, P.at_fh()), ((Pn >> 2n : U32) + 1 : U32), Equal.trans(U32, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32)), P.at_fh())), ((Pn >> 2n : U32) + 1 : U32), wg(Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32)), d, P.at_fh(), LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), d, P.at_fh(), ((Pn >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), d, (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), d, Pn, 0, LA.set_full(U32, LAT.fromT(U32, t0), d, L, S, hf)))), hd32), LA.get_set_same(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32)))) : {KMd.chain(Con{Pn, ns}, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, _) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(((Pn >> 2n : U32) + 1 : U32), 0), False{}, fl_nz(Pn)) : {(Bool.not(_) && (U32.is_eq(KMd.at_idx(((Pn >> 2n : U32) + 1 : U32)), Pn) && KMd.chain(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, (Pn + 1 : U32))))) == True{} : Bool}
  %Equal.sym(U32, KMd.at_idx(((Pn >> 2n : U32) + 1 : U32)), P.base(Pn), fl_idx(Pn)) : {(Bool.not(False{}) && (U32.is_eq(_, Pn) && KMd.chain(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, (Pn + 1 : U32))))) == True{} : Bool}
  %Equal.sym(U32, P.base(Pn), Pn, hb) : {(Bool.not(False{}) && (U32.is_eq(_, Pn) && KMd.chain(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, (Pn + 1 : U32))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(Pn, Pn), True{}, is_eq_self(Pn)) : {(Bool.not(False{}) && (_ && KMd.chain(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, (Pn + 1 : U32))))) == True{} : Bool}
  %Equal.sym(U32, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, (Pn + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Equal.trans(U32, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, (Pn + 1 : U32)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32)), (Pn + 1 : U32))), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), wg(Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32)), d, (Pn + 1 : U32), LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), d, P.at_fh(), ((Pn >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), d, (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), d, Pn, 0, LA.set_full(U32, LAT.fromT(U32, t0), d, L, S, hf)))), hd32), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32)), (Pn + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), (Pn + 1 : U32))), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), LA.get_set_other(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), d, P.at_fh(), (Pn + 1 : U32), ((Pn >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), d, (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), d, Pn, 0, LA.set_full(U32, LAT.fromT(U32, t0), d, L, S, hf))), hd32, hPh), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), (Pn + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), LA.get_set_same(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), LA.get_set_other(U32, LAT.fromT(U32, t0), d, L, P.at_fh(), S, hf, hd32, hLh), Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), wg(LAT.fromT(U32, t0), d, P.at_fh(), hf, hd32))))))) : {KMd.chain(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, _) == True{} : Bool}
  ME.subst(List<&2, U32>, z => {KMd.chain(ns, z, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())))), AD.slot(P.at_fh(), d), ((Pn >> 2n : U32) + 1 : U32)), AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())))), AD.slot(P.at_fh(), d), ((Pn >> 2n : U32) + 1 : U32)), LA.set_view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), d, P.at_fh(), ((Pn >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), d, (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), d, Pn, 0, LA.set_full(U32, LAT.fromT(U32, t0), d, L, S, hf))), hd32)), chain_set(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())))), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32), hoH, ME.subst(List<&2, U32>, z => {KMd.chain(ns, z, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0)), AD.slot((Pn + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())))), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())))), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0)), AD.slot((Pn + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh()))), LA.set_view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0), d, (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), d, Pn, 0, LA.set_full(U32, LAT.fromT(U32, t0), d, L, S, hf)), hd32)), chain_set(ns, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), P.at_fh())), hoP1, ME.subst(List<&2, U32>, z => {KMd.chain(ns, z, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), L, S)), AD.slot(Pn, d), 0), AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0)), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), Pn, 0)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), L, S)), AD.slot(Pn, d), 0), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t0), L, S), d, Pn, 0, LA.set_full(U32, LAT.fromT(U32, t0), d, L, S, hf), hd32)), chain_set(ns, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), L, S)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pn, 0, hoP, ME.subst(List<&2, U32>, z => {KMd.chain(ns, z, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(L, d), S), AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), L, S)), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), L, S)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(L, d), S), LA.set_view(U32, LAT.fromT(U32, t0), d, L, S, hf, hd32)), chain_set(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), L, S, hoL, hc))))))))

# the insert's writes (ins.heap.has), the free list's first nodes b then
# ns before: ns the first after
def fl_take(+t0: LAT.Tree<U32>, +d: Nat, +b: U32, +HD: U32, +V3: U32, +V2: U32, +LO: U32, +x: U32, +s: U32, +ns: List<&2, U32>, +hf: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hc: {KMd.chain(Con{b, ns}, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool},
  +hb0: {Nat.is_eq(AD.slot(b, d), AD.slot(P.at_fh(), d)) == False{} : Bool}, +hb3: {Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(P.at_fh(), d)) == False{} : Bool}, +hb1: {Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(P.at_fh(), d)) == False{} : Bool}, +hb2: {Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(P.at_fh(), d)) == False{} : Bool}, +hlo: {Nat.is_eq(AD.slot(LO, d), AD.slot(P.at_fh(), d)) == False{} : Bool}, +hx3: {Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(P.at_fh(), d)) == False{} : Bool},
  +ohh: {offw(ns, d, P.at_fh()) == True{} : Bool}, +ob0: {offw(ns, d, b) == True{} : Bool}, +ob3: {offw(ns, d, (b + 3 : U32)) == True{} : Bool}, +ob1: {offw(ns, d, (b + 1 : U32)) == True{} : Bool}, +ob2: {offw(ns, d, (b + 2 : U32)) == True{} : Bool}, +olo: {offw(ns, d, LO) == True{} : Bool}, +ox3: {offw(ns, d, (x + 3 : U32)) == True{} : Bool}) -> {KMd.chain(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), (x + 3 : U32), s)), d, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), (x + 3 : U32), s)), d, P.at_fh())) == True{} : Bool}:
  %Equal.sym(U32, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), (x + 3 : U32), s)), d, P.at_fh()), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), Equal.trans(U32, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), (x + 3 : U32), s)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), (x + 3 : U32), s), P.at_fh())), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), wg(Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), (x + 3 : U32), s), d, P.at_fh(), LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), d, (x + 3 : U32), s, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), d, LO, b, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), d, (b + 2 : U32), V2, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), d, (b + 1 : U32), P.era(), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), d, (b + 3 : U32), V3, LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, HD, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hf))))))), hd32), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), (x + 3 : U32), s), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), P.at_fh())), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), d, (x + 3 : U32), P.at_fh(), s, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), d, LO, b, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), d, (b + 2 : U32), V2, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), d, (b + 1 : U32), P.era(), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), d, (b + 3 : U32), V3, LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, HD, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hf)))))), hd32, hx3), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), P.at_fh())), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), d, LO, P.at_fh(), b, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), d, (b + 2 : U32), V2, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), d, (b + 1 : U32), P.era(), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), d, (b + 3 : U32), V3, LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, HD, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hf))))), hd32, hlo), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), P.at_fh())), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), d, (b + 2 : U32), P.at_fh(), V2, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), d, (b + 1 : U32), P.era(), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), d, (b + 3 : U32), V3, LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, HD, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hf)))), hd32, hb2), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), P.at_fh())), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), d, (b + 1 : U32), P.at_fh(), P.era(), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), d, (b + 3 : U32), V3, LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, HD, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hf))), hd32, hb1), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), P.at_fh())), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), LA.get_set_other(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), d, (b + 3 : U32), P.at_fh(), V3, LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, HD, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hf)), hd32, hb3), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), P.at_fh())), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), LA.get_set_other(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, P.at_fh(), HD, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hf), hd32, hb0), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), P.at_fh())), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), LA.get_set_same(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), wg(LAT.fromT(U32, t0), d, (b + 1 : U32), hf, hd32))))))))))) : {KMd.chain(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), (x + 3 : U32), s)), d, _) == True{} : Bool}
  ME.subst(List<&2, U32>, z => {KMd.chain(ns, z, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32))) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b)), AD.slot((x + 3 : U32), d), s), AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), (x + 3 : U32), s)), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), (x + 3 : U32), s)), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b)), AD.slot((x + 3 : U32), d), s), LA.set_view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b), d, (x + 3 : U32), s, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), d, LO, b, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), d, (b + 2 : U32), V2, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), d, (b + 1 : U32), P.era(), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), d, (b + 3 : U32), V3, LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, HD, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hf)))))), hd32)), chain_set(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), (x + 3 : U32), s, ox3, ME.subst(List<&2, U32>, z => {KMd.chain(ns, z, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32))) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2)), AD.slot(LO, d), b), AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b)), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), LO, b)), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2)), AD.slot(LO, d), b), LA.set_view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2), d, LO, b, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), d, (b + 2 : U32), V2, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), d, (b + 1 : U32), P.era(), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), d, (b + 3 : U32), V3, LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, HD, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hf))))), hd32)), chain_set(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), LO, b, olo, ME.subst(List<&2, U32>, z => {KMd.chain(ns, z, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32))) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era())), AD.slot((b + 2 : U32), d), V2), AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2)), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), (b + 2 : U32), V2)), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era())), AD.slot((b + 2 : U32), d), V2), LA.set_view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era()), d, (b + 2 : U32), V2, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), d, (b + 1 : U32), P.era(), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), d, (b + 3 : U32), V3, LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, HD, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hf)))), hd32)), chain_set(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era())), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), (b + 2 : U32), V2, ob2, ME.subst(List<&2, U32>, z => {KMd.chain(ns, z, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32))) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3)), AD.slot((b + 1 : U32), d), P.era()), AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era())), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), (b + 1 : U32), P.era())), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3)), AD.slot((b + 1 : U32), d), P.era()), LA.set_view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3), d, (b + 1 : U32), P.era(), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), d, (b + 3 : U32), V3, LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, HD, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hf))), hd32)), chain_set(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), (b + 1 : U32), P.era(), ob1, ME.subst(List<&2, U32>, z => {KMd.chain(ns, z, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32))) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD)), AD.slot((b + 3 : U32), d), V3), AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3)), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), (b + 3 : U32), V3)), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD)), AD.slot((b + 3 : U32), d), V3), LA.set_view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD), d, (b + 3 : U32), V3, LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, HD, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hf)), hd32)), chain_set(ns, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), (b + 3 : U32), V3, ob3, ME.subst(List<&2, U32>, z => {KMd.chain(ns, z, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32))) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))))), AD.slot(b, d), HD), AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD)), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, HD)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))))), AD.slot(b, d), HD), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, HD, LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hf), hd32)), chain_set(ns, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))))), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), b, HD, ob0, ME.subst(List<&2, U32>, z => {KMd.chain(ns, z, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32))) == True{} : Bool}, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))))), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(P.at_fh(), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), LA.set_view(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hf, hd32)), chain_set(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32)), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), ohh, and_r(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b), KMd.chain(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32))), and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b) && KMd.chain(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32))), hc))))))))))))))))

# a tree laid out: the free list's head off its branches' words
def lay_offb_fh(t: IM.Tr, +d: Nat, +hl: {IM.tr.lay(t, d) == True{} : Bool}) -> {IM.tr.offb(t, d, P.at_fh()) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      {==}
    case IM.Br{+b, +i, +l, +r}:
      +hok = and_l(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl)
      +hlr = and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl))))
      and_intro(KMd.off.words(KMd.nw(b), d, P.at_fh()), IM.tr.offb(l, d, P.at_fh()) && IM.tr.offb(r, d, P.at_fh()), and_r(IM.ws.apart(KMd.nw(b), d), KMd.off.words(KMd.nw(b), d, P.at_fh()), and_r(U32.is_eq(P.base(b), b), IM.ws.apart(KMd.nw(b), d) && KMd.off.words(KMd.nw(b), d, P.at_fh()), hok)),
        and_intro(IM.tr.offb(l, d, P.at_fh()), IM.tr.offb(r, d, P.at_fh()), lay_offb_fh(l, d, and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), hlr)), lay_offb_fh(r, d, and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), hlr))))

# node a apart from n: n's word 1 off a's words
def sep_w1(+d: Nat, +a: U32, +n: U32, +h: {IM.nd.sep(d, a, n) == True{} : Bool}) -> {KMd.off.words(KMd.nw(a), d, (n + 1 : U32)) == True{} : Bool}:
  and_l(KMd.off.words(KMd.nw(a), d, (n + 1 : U32)), KMd.off.words(KMd.nw(a), d, (n + 2 : U32)) && KMd.off.words(KMd.nw(a), d, (n + 3 : U32)), and_r(KMd.off.words(KMd.nw(a), d, n), KMd.off.words(KMd.nw(a), d, (n + 1 : U32)) && (KMd.off.words(KMd.nw(a), d, (n + 2 : U32)) && KMd.off.words(KMd.nw(a), d, (n + 3 : U32))), and_r(IM.nd.disj(d, a, n), IM.nd.disj(d, n, a), h)))

# a tree apart from n: n's word 1 off its branches' words
def offn_offb1(t: IM.Tr, +d: Nat, +n: U32, +h: {IM.tr.offn(t, d, n) == True{} : Bool}) -> {IM.tr.offb(t, d, (n + 1 : U32)) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      {==}
    case IM.Br{+b, +i, +l, +r}:
      +hlr = and_r(IM.nd.sep(d, b, n), IM.tr.offn(l, d, n) && IM.tr.offn(r, d, n), h)
      and_intro(KMd.off.words(KMd.nw(b), d, (n + 1 : U32)), IM.tr.offb(l, d, (n + 1 : U32)) && IM.tr.offb(r, d, (n + 1 : U32)), sep_w1(d, b, n, and_l(IM.nd.sep(d, b, n), IM.tr.offn(l, d, n) && IM.tr.offn(r, d, n), h)),
        and_intro(IM.tr.offb(l, d, (n + 1 : U32)), IM.tr.offb(r, d, (n + 1 : U32)), offn_offb1(l, d, n, and_l(IM.tr.offn(l, d, n), IM.tr.offn(r, d, n), hlr)), offn_offb1(r, d, n, and_r(IM.tr.offn(l, d, n), IM.tr.offn(r, d, n), hlr))))

# the head off the words 1 of nodes each their own
def offw_fh(ns: List<&2, U32>, +d: Nat, +h: {IM.fl.ok(ns, d) == True{} : Bool}) -> {offw(ns, d, P.at_fh()) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      and_intro(Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((n + 1 : U32), d))), offw(r, d, P.at_fh()),
        nf(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((n + 1 : U32), d)), off1(n, d, P.at_fh(), and_r(IM.ws.apart(KMd.nw(n), d), KMd.off.words(KMd.nw(n), d, P.at_fh()), and_r(U32.is_eq(P.base(n), n), IM.ws.apart(KMd.nw(n), d) && KMd.off.words(KMd.nw(n), d, P.at_fh()), and_l(IM.nd.ok(n, d), IM.fl.ok(r, d), h))))),
        offw_fh(r, d, and_r(IM.nd.ok(n, d), IM.fl.ok(r, d), h)))

# word 0 of a node apart from each of ns off their words 1
def offw_sep0(ns: List<&2, U32>, +d: Nat, +a: U32, +h: {IM.fl.sep(ns, d, a) == True{} : Bool}) -> {offw(ns, d, a) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      and_intro(Bool.not(Nat.is_eq(AD.slot(a, d), AD.slot((n + 1 : U32), d))), offw(r, d, a),
        nf(Nat.is_eq(AD.slot(a, d), AD.slot((n + 1 : U32), d)), neq_comm(AD.slot((n + 1 : U32), d), AD.slot(a, d), off0(a, d, (n + 1 : U32), sep_w1(d, a, n, and_l(IM.nd.sep(d, a, n), IM.fl.sep(r, d, a), h))))),
        offw_sep0(r, d, a, and_r(IM.nd.sep(d, a, n), IM.fl.sep(r, d, a), h)))

# word 1 of a node apart from each of ns off their words 1
def offw_sep1(ns: List<&2, U32>, +d: Nat, +a: U32, +h: {IM.fl.sep(ns, d, a) == True{} : Bool}) -> {offw(ns, d, (a + 1 : U32)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      and_intro(Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((n + 1 : U32), d))), offw(r, d, (a + 1 : U32)),
        nf(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((n + 1 : U32), d)), neq_comm(AD.slot((n + 1 : U32), d), AD.slot((a + 1 : U32), d), off1(a, d, (n + 1 : U32), sep_w1(d, a, n, and_l(IM.nd.sep(d, a, n), IM.fl.sep(r, d, a), h))))),
        offw_sep1(r, d, a, and_r(IM.nd.sep(d, a, n), IM.fl.sep(r, d, a), h)))

# word 2 of a node apart from each of ns off their words 1
def offw_sep2(ns: List<&2, U32>, +d: Nat, +a: U32, +h: {IM.fl.sep(ns, d, a) == True{} : Bool}) -> {offw(ns, d, (a + 2 : U32)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      and_intro(Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((n + 1 : U32), d))), offw(r, d, (a + 2 : U32)),
        nf(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((n + 1 : U32), d)), neq_comm(AD.slot((n + 1 : U32), d), AD.slot((a + 2 : U32), d), off2(a, d, (n + 1 : U32), sep_w1(d, a, n, and_l(IM.nd.sep(d, a, n), IM.fl.sep(r, d, a), h))))),
        offw_sep2(r, d, a, and_r(IM.nd.sep(d, a, n), IM.fl.sep(r, d, a), h)))

# word 3 of a node apart from each of ns off their words 1
def offw_sep3(ns: List<&2, U32>, +d: Nat, +a: U32, +h: {IM.fl.sep(ns, d, a) == True{} : Bool}) -> {offw(ns, d, (a + 3 : U32)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      and_intro(Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((n + 1 : U32), d))), offw(r, d, (a + 3 : U32)),
        nf(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((n + 1 : U32), d)), neq_comm(AD.slot((n + 1 : U32), d), AD.slot((a + 3 : U32), d), off3(a, d, (n + 1 : U32), sep_w1(d, a, n, and_l(IM.nd.sep(d, a, n), IM.fl.sep(r, d, a), h))))),
        offw_sep3(r, d, a, and_r(IM.nd.sep(d, a, n), IM.fl.sep(r, d, a), h)))

# the word a removal writes the sibling at off the free nodes' words 1
def offw_lo(ns: List<&2, U32>, +t: IM.Tr, +x: U32, +k: U32, +s: U32, +d: Nat, +hs: {IM.fl.sep(ns, d, s) == True{} : Bool}, +ht: {IM.fl.offt(ns, t, d) == True{} : Bool},
  +hx: {IM.tr.look(t, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(t), x) == False{} : Bool}) -> {offw(ns, d, cut.lo(IM.tr.cutat(t, x, k, (s + 3 : U32)))) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      and_intro(Bool.not(Nat.is_eq(AD.slot(cut.lo(IM.tr.cutat(t, x, k, (s + 3 : U32))), d), AD.slot((n + 1 : U32), d))), offw(r, d, cut.lo(IM.tr.cutat(t, x, k, (s + 3 : U32)))),
        nf(Nat.is_eq(AD.slot(cut.lo(IM.tr.cutat(t, x, k, (s + 3 : U32))), d), AD.slot((n + 1 : U32), d)), neq_comm(AD.slot((n + 1 : U32), d), AD.slot(cut.lo(IM.tr.cutat(t, x, k, (s + 3 : U32))), d),
          c2b(t, x, k, (s + 3 : U32), d, (n + 1 : U32), offn_offb1(t, d, n, and_l(IM.tr.offn(t, d, n), IM.fl.offt(r, t, d), ht)), off3(s, d, (n + 1 : U32), sep_w1(d, s, n, and_l(IM.nd.sep(d, s, n), IM.fl.sep(r, d, s), hs))), hx, hne))),
        offw_lo(r, t, x, k, s, d, and_r(IM.nd.sep(d, s, n), IM.fl.sep(r, d, s), hs), and_r(IM.tr.offn(t, d, n), IM.fl.offt(r, t, d), ht), hx, hne))

# and the word an insert writes its branch at
def offw_plo(ns: List<&2, U32>, +t: IM.Tr, +c: Nat, +k: U32, +s: U32, +d: Nat, +hs: {IM.fl.sep(ns, d, s) == True{} : Bool}, +ht: {IM.fl.offt(ns, t, d) == True{} : Bool}) -> {offw(ns, d, plc.lo(IM.tr.plc(t, c, k, (s + 3 : U32)))) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      and_intro(Bool.not(Nat.is_eq(AD.slot(plc.lo(IM.tr.plc(t, c, k, (s + 3 : U32))), d), AD.slot((n + 1 : U32), d))), offw(r, d, plc.lo(IM.tr.plc(t, c, k, (s + 3 : U32)))),
        nf(Nat.is_eq(AD.slot(plc.lo(IM.tr.plc(t, c, k, (s + 3 : U32))), d), AD.slot((n + 1 : U32), d)), neq_comm(AD.slot((n + 1 : U32), d), AD.slot(plc.lo(IM.tr.plc(t, c, k, (s + 3 : U32))), d),
          plc2b(t, c, k, (s + 3 : U32), d, (n + 1 : U32), offn_offb1(t, d, n, and_l(IM.tr.offn(t, d, n), IM.fl.offt(r, t, d), ht)), off3(s, d, (n + 1 : U32), sep_w1(d, s, n, and_l(IM.nd.sep(d, s, n), IM.fl.sep(r, d, s), hs)))))),
        offw_plo(r, t, c, k, s, d, and_r(IM.nd.sep(d, s, n), IM.fl.sep(r, d, s), hs), and_r(IM.tr.offn(t, d, n), IM.fl.offt(r, t, d), ht)))

# what holds of every branch of a tree holds of the parent a removal frees

def cut_pa_ok.h(+hit: Bool, +b: U32, +sib: U32, +loc: U32, cd: IM.Cut, +d: Nat, +hb: {IM.nd.ok(b, d) == True{} : Bool},
  ih: {hit == False{} : Bool} -> {IM.nd.ok(cut.pa(cd), d) == True{} : Bool}) -> {IM.nd.ok(cut.pa(IM.cut.k.of(hit, b, sib, loc, cd)), d) == True{} : Bool}:
  match hit:
    case True{}:
      hb
    case False{}:
      ih({==})

def cut_pa_ok.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hb: {IM.nd.ok(b, d) == True{} : Bool},
  +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(l), x) == False{} : Bool} -> {IM.nd.ok(cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32))), d) == True{} : Bool},
  ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(r), x) == False{} : Bool} -> {IM.nd.ok(cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32))), d) == True{} : Bool}) ->
  {IM.nd.ok(cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), d) == True{} : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {IM.nd.ok(cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), d) == True{} : Bool}
      cut_pa_ok.h(U32.is_eq(IM.tr.addr(r), x), b, IM.tr.addr(l), loc, IM.tr.cutat(r, x, k, (b + 3 : U32)), d, hb, hn => ihr(hx_side(True{}, k, i, l, r, x, hsd, hx))(hn))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {IM.nd.ok(cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), d) == True{} : Bool}
      cut_pa_ok.h(U32.is_eq(IM.tr.addr(l), x), b, IM.tr.addr(r), loc, IM.tr.cutat(l, x, k, (b + 2 : U32)), d, hb, hn => ihl(hx_side(False{}, k, i, l, r, x, hsd, hx))(hn))

def cut_pa_ok(t: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +ho: {IM.tr.lay(t, d) == True{} : Bool},
  +hx: {IM.tr.look(t, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(t), x) == False{} : Bool}) -> {IM.nd.ok(cut.pa(IM.tr.cutat(t, x, k, loc)), d) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      lf_absurd({IM.nd.ok(cut.pa(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc)), d) == True{} : Bool}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      cut_pa_ok.k(X.ix.side(k, i), b, i, l, r, x, k, loc, d, {==}, and_l(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), ho), hx,
        hxl => hnl => cut_pa_ok(l, x, k, (b + 2 : U32), d, and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), ho))))), hxl, hnl),
        hxr => hnr => cut_pa_ok(r, x, k, (b + 3 : U32), d, and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), ho))))), hxr, hnr))

def cut_pa_sep.h(+hit: Bool, +b: U32, +sib: U32, +loc: U32, cd: IM.Cut, +d: Nat, +n: U32, +hb: {IM.nd.sep(d, b, n) == True{} : Bool},
  ih: {hit == False{} : Bool} -> {IM.nd.sep(d, cut.pa(cd), n) == True{} : Bool}) -> {IM.nd.sep(d, cut.pa(IM.cut.k.of(hit, b, sib, loc, cd)), n) == True{} : Bool}:
  match hit:
    case True{}:
      hb
    case False{}:
      ih({==})

def cut_pa_sep.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +n: U32, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hb: {IM.nd.sep(d, b, n) == True{} : Bool},
  +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(l), x) == False{} : Bool} -> {IM.nd.sep(d, cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32))), n) == True{} : Bool},
  ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(r), x) == False{} : Bool} -> {IM.nd.sep(d, cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32))), n) == True{} : Bool}) ->
  {IM.nd.sep(d, cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), n) == True{} : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {IM.nd.sep(d, cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), n) == True{} : Bool}
      cut_pa_sep.h(U32.is_eq(IM.tr.addr(r), x), b, IM.tr.addr(l), loc, IM.tr.cutat(r, x, k, (b + 3 : U32)), d, n, hb, hn => ihr(hx_side(True{}, k, i, l, r, x, hsd, hx))(hn))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {IM.nd.sep(d, cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b)))), n) == True{} : Bool}
      cut_pa_sep.h(U32.is_eq(IM.tr.addr(l), x), b, IM.tr.addr(r), loc, IM.tr.cutat(l, x, k, (b + 2 : U32)), d, n, hb, hn => ihl(hx_side(False{}, k, i, l, r, x, hsd, hx))(hn))

def cut_pa_sep(t: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +n: U32, +ho: {IM.tr.offn(t, d, n) == True{} : Bool},
  +hx: {IM.tr.look(t, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(t), x) == False{} : Bool}) -> {IM.nd.sep(d, cut.pa(IM.tr.cutat(t, x, k, loc)), n) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      lf_absurd({IM.nd.sep(d, cut.pa(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc)), n) == True{} : Bool}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      cut_pa_sep.k(X.ix.side(k, i), b, i, l, r, x, k, loc, d, n, {==}, and_l(IM.nd.sep(d, b, n), IM.tr.offn(l, d, n) && IM.tr.offn(r, d, n), ho), hx,
        hxl => hnl => cut_pa_sep(l, x, k, (b + 2 : U32), d, n, and_l(IM.tr.offn(l, d, n), IM.tr.offn(r, d, n), and_r(IM.nd.sep(d, b, n), IM.tr.offn(l, d, n) && IM.tr.offn(r, d, n), ho)), hxl, hnl),
        hxr => hnr => cut_pa_sep(r, x, k, (b + 3 : U32), d, n, and_r(IM.tr.offn(l, d, n), IM.tr.offn(r, d, n), and_r(IM.nd.sep(d, b, n), IM.tr.offn(l, d, n) && IM.tr.offn(r, d, n), ho)), hxr, hnr))

# the free nodes apart from the branch a removal frees
def flsep_pa(ns: List<&2, U32>, +t: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +ht: {IM.fl.offt(ns, t, d) == True{} : Bool},
  +hx: {IM.tr.look(t, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(t), x) == False{} : Bool}) -> {IM.fl.sep(ns, d, cut.pa(IM.tr.cutat(t, x, k, loc))) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      and_intro(IM.nd.sep(d, cut.pa(IM.tr.cutat(t, x, k, loc)), n), IM.fl.sep(r, d, cut.pa(IM.tr.cutat(t, x, k, loc))), cut_pa_sep(t, x, k, loc, d, n, and_l(IM.tr.offn(t, d, n), IM.fl.offt(r, t, d), ht), hx, hne),
        flsep_pa(r, t, x, k, loc, d, and_r(IM.tr.offn(t, d, n), IM.fl.offt(r, t, d), ht), hx, hne))

# the branch the model's removal names freed (IM.tr.par) the cut's
def par_cut.hr(+hit: Bool, +b: U32, +hl: Bool, +sib: U32, +loc: U32, cd: IM.Cut, pl: Maybe<&2, U32>, pr: Maybe<&2, U32>,
  ih: {hit == False{} : Bool} -> {pr == Some{cut.pa(cd)} : Maybe<&2, U32>}) ->
  {IM.tr.par.k(True{}, b, hl, hit, pl, pr) == Some{cut.pa(IM.cut.k.of(hit, b, sib, loc, cd))} : Maybe<&2, U32>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      ih({==})

def par_cut.hl(+hit: Bool, +b: U32, +hr: Bool, +sib: U32, +loc: U32, cd: IM.Cut, pl: Maybe<&2, U32>, pr: Maybe<&2, U32>,
  ih: {hit == False{} : Bool} -> {pl == Some{cut.pa(cd)} : Maybe<&2, U32>}) ->
  {IM.tr.par.k(False{}, b, hit, hr, pl, pr) == Some{cut.pa(IM.cut.k.of(hit, b, sib, loc, cd))} : Maybe<&2, U32>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      ih({==})

def par_cut.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +loc: U32, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(l), x) == False{} : Bool} -> {IM.tr.par(l, x, k) == Some{cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32)))} : Maybe<&2, U32>},
  ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(r), x) == False{} : Bool} -> {IM.tr.par(r, x, k) == Some{cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32)))} : Maybe<&2, U32>}) ->
  {IM.tr.par.k(X.ix.side(k, i), b, U32.is_eq(IM.tr.addr(l), x), U32.is_eq(IM.tr.addr(r), x), IM.tr.par(l, x, k), IM.tr.par(r, x, k)) == Some{cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))} : Maybe<&2, U32>}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {IM.tr.par.k(_, b, U32.is_eq(IM.tr.addr(l), x), U32.is_eq(IM.tr.addr(r), x), IM.tr.par(l, x, k), IM.tr.par(r, x, k)) == Some{cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))} : Maybe<&2, U32>}
      par_cut.hr(U32.is_eq(IM.tr.addr(r), x), b, U32.is_eq(IM.tr.addr(l), x), IM.tr.addr(l), loc, IM.tr.cutat(r, x, k, (b + 3 : U32)), IM.tr.par(l, x, k), IM.tr.par(r, x, k), hn => ihr(hx_side(True{}, k, i, l, r, x, hsd, hx))(hn))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {IM.tr.par.k(_, b, U32.is_eq(IM.tr.addr(l), x), U32.is_eq(IM.tr.addr(r), x), IM.tr.par(l, x, k), IM.tr.par(r, x, k)) == Some{cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))} : Maybe<&2, U32>}
      par_cut.hl(U32.is_eq(IM.tr.addr(l), x), b, U32.is_eq(IM.tr.addr(r), x), IM.tr.addr(r), loc, IM.tr.cutat(l, x, k, (b + 2 : U32)), IM.tr.par(l, x, k), IM.tr.par(r, x, k), hn => ihl(hx_side(False{}, k, i, l, r, x, hsd, hx))(hn))

def par_cut(t: IM.Tr, +x: U32, +k: U32, +loc: U32, +hx: {IM.tr.look(t, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(t), x) == False{} : Bool}) ->
  {IM.tr.par(t, x, k) == Some{cut.pa(IM.tr.cutat(t, x, k, loc))} : Maybe<&2, U32>}:
  match t:
    case IM.Lf{+y, +ky}:
      lf_absurd({IM.tr.par(IM.Lf{y, ky}, x, k) == Some{cut.pa(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc))} : Maybe<&2, U32>}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      par_cut.k(X.ix.side(k, i), b, i, l, r, x, k, loc, {==}, hx,
        hxl => hnl => par_cut(l, x, k, (b + 2 : U32), hxl, hnl),
        hxr => hnr => par_cut(r, x, k, (b + 3 : U32), hxr, hnr))

# A removal's free list
def rf.br(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +ns: List<&2, U32>,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hreT: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Br{b, i, l, r}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s) == True{} : Bool}, +hi: {IM.tr.ok(IM.Br{b, i, l, r}, 0n) == True{} : Bool},
  +hoks: {IM.nd.ok(s, d) == True{} : Bool}, +hoffT: {IM.tr.offn(IM.Br{b, i, l, r}, d, s) == True{} : Bool}, +hlayT: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool},
  +hx: {IM.tr.look(IM.Br{b, i, l, r}, k) == Some{x} : Maybe<&2, U32>}, +hno: {IM.fl.ok(ns, d) == True{} : Bool}, +hnsS: {IM.fl.sep(ns, d, s) == True{} : Bool}, +hnsT: {IM.fl.offt(ns, IM.Br{b, i, l, r}, d) == True{} : Bool},
  +hc: {KMd.chain(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}) -> {KMd.chain(IM.mb.cons(IM.ix.par(IM.Has{IM.Br{b, i, l, r}}, x, k), ns), AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, KMd.word(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, P.at_fh())) == True{} : Bool}:
  +hol = and_l(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hlayT))
  +hor = and_l(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hlayT)))
  +hneT = sep_ne(d, x, b, ls.k(X.ix.side(k, i), d, i, l, r, k, x, b, {==}, hx, hxl => look_sep(l, b, d, k, x, hol, hxl), hxr => look_sep(r, b, d, k, x, hor, hxr)))
  +hokpa = cut_pa_ok(IM.Br{b, i, l, r}, x, k, (s + 3 : U32), d, hlayT, hx, hneT)
  +hspa = flsep_pa(ns, IM.Br{b, i, l, r}, x, k, (s + 3 : U32), d, hnsT, hx, hneT)
  %Equal.sym(P.H, X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a}, rm.heap.br(t0, a, d, s, x, k, b, i, l, r, hft, hd32, hreT, hi, hoks, hoffT, hlayT, hx)) : {KMd.chain(IM.mb.cons(IM.ix.par(IM.Has{IM.Br{b, i, l, r}}, x, k), ns), AD.view(U32, KMd.words(_)), d, KMd.word(AD.view(U32, KMd.words(_)), d, P.at_fh())) == True{} : Bool}
  %Equal.sym(Maybe<&2, U32>, IM.tr.par(IM.Br{b, i, l, r}, x, k), Some{cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))}, par_cut(IM.Br{b, i, l, r}, x, k, (s + 3 : U32), hx, hneT)) : {KMd.chain(IM.mb.cons(_, ns), AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))), d, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))), d, P.at_fh())) == True{} : Bool}
  fl_free(t0, d, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), ns, hft, hd32, MS.u32_eq_of_is_eq(P.base(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), c5(IM.Br{b, i, l, r}, x, k, (s + 3 : U32), d, hlayT, hx, hneT)),
    neq_comm(AD.slot(P.at_fh(), d), AD.slot(cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d), c2b(IM.Br{b, i, l, r}, x, k, (s + 3 : U32), d, P.at_fh(), lay_offb_fh(IM.Br{b, i, l, r}, d, hlayT), off3(s, d, P.at_fh(), and_r(IM.ws.apart(KMd.nw(s), d), KMd.off.words(KMd.nw(s), d, P.at_fh()), and_r(U32.is_eq(P.base(s), s), IM.ws.apart(KMd.nw(s), d) && KMd.off.words(KMd.nw(s), d, P.at_fh()), hoks))), hx, hneT)),
    off1(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), d, P.at_fh(), and_r(IM.ws.apart(KMd.nw(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), d), KMd.off.words(KMd.nw(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), d, P.at_fh()), and_r(U32.is_eq(P.base(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), IM.ws.apart(KMd.nw(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), d) && KMd.off.words(KMd.nw(cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), d, P.at_fh()), hokpa))),
    offw_lo(ns, IM.Br{b, i, l, r}, x, k, s, d, hnsS, hnsT, hx, hneT), offw_sep0(ns, d, cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), hspa), offw_sep1(ns, d, cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), hspa), offw_fh(ns, d, hno), hc)

def rf.lf(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +y: U32, +ky: U32, +ns: List<&2, U32>,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hreT: {IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Lf{y, ky}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s) == True{} : Bool},
  +hx: {IM.tr.look(IM.Lf{y, ky}, k) == Some{x} : Maybe<&2, U32>}, +hoks: {IM.nd.ok(s, d) == True{} : Bool}, +hnsS: {IM.fl.sep(ns, d, s) == True{} : Bool},
  +hc: {KMd.chain(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}) -> {KMd.chain(IM.mb.cons(IM.ix.par(IM.Has{IM.Lf{y, ky}}, x, k), ns), AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, KMd.word(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, P.at_fh())) == True{} : Bool}:
  %Equal.sym(P.H, X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s)}, a}, rm.heap.lf(t0, a, d, s, x, k, y, ky, hft, hd32, hreT, hx)) : {KMd.chain(IM.mb.cons(IM.ix.par(IM.Has{IM.Lf{y, ky}}, x, k), ns), AD.view(U32, KMd.words(_)), d, KMd.word(AD.view(U32, KMd.words(_)), d, P.at_fh())) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), s), LA.set_view(U32, LAT.fromT(U32, t0), d, (s + 3 : U32), s, hft, hd32)) : {KMd.chain(ns, _, d, KMd.word(_, d, P.at_fh())) == True{} : Bool}
  fl_keepv(ns, AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32), s, neq_comm(AD.slot(P.at_fh(), d), AD.slot((s + 3 : U32), d), off3(s, d, P.at_fh(), and_r(IM.ws.apart(KMd.nw(s), d), KMd.off.words(KMd.nw(s), d, P.at_fh()), and_r(U32.is_eq(P.base(s), s), IM.ws.apart(KMd.nw(s), d) && KMd.off.words(KMd.nw(s), d, P.at_fh()), hoks)))), offw_sep3(ns, d, s, hnsS), hc)

def rf.k(I: IM.Ix, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +ns: List<&2, U32>,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, I) == True{} : Bool}, +hi: {IM.ix.inv(I) == True{} : Bool}, +hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  +hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}, +hno: {IM.fl.ok(ns, d) == True{} : Bool}, +hns: {IM.ix.flsep(I, s, d, ns) == True{} : Bool},
  +hc: {KMd.chain(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}) -> {KMd.chain(IM.mb.cons(IM.ix.par(I, x, k), ns), AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, KMd.word(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, P.at_fh())) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      Empty.absurd({KMd.chain(IM.mb.cons(IM.ix.par(IM.Ept{}, x, k), ns), AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, KMd.word(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, P.at_fh())) == True{} : Bool}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, m => is_some(m), None{}, Some{x}, hx)))
    case IM.Has{+t}:
      match t:
        case IM.Lf{+y, +ky}:
          rf.lf(t0, a, d, s, x, k, y, ky, ns, hft, hd32, and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Lf{y, ky}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre), hx,
            and_l(IM.nd.ok(s, d), IM.tr.offn(IM.Lf{y, ky}, d, s) && IM.tr.lay(IM.Lf{y, ky}, d), hl), and_l(IM.fl.sep(ns, d, s), IM.fl.offt(ns, IM.Lf{y, ky}, d), hns), hc)
        case IM.Br{+b, +i, +l, +r}:
          rf.br(t0, a, d, s, x, k, b, i, l, r, ns, hft, hd32, and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Br{b, i, l, r}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre), hi,
            and_l(IM.nd.ok(s, d), IM.tr.offn(IM.Br{b, i, l, r}, d, s) && IM.tr.lay(IM.Br{b, i, l, r}, d), hl), and_l(IM.tr.offn(IM.Br{b, i, l, r}, d, s), IM.tr.lay(IM.Br{b, i, l, r}, d), and_r(IM.nd.ok(s, d), IM.tr.offn(IM.Br{b, i, l, r}, d, s) && IM.tr.lay(IM.Br{b, i, l, r}, d), hl)),
            and_r(IM.tr.offn(IM.Br{b, i, l, r}, d, s), IM.tr.lay(IM.Br{b, i, l, r}, d), and_r(IM.nd.ok(s, d), IM.tr.offn(IM.Br{b, i, l, r}, d, s) && IM.tr.lay(IM.Br{b, i, l, r}, d), hl)), hx, hno,
            and_l(IM.fl.sep(ns, d, s), IM.fl.offt(ns, IM.Br{b, i, l, r}, d), hns), and_r(IM.fl.sep(ns, d, s), IM.fl.offt(ns, IM.Br{b, i, l, r}, d), hns), hc)

def rf.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +x: U32, +k: U32, +ns: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}, hi: {IM.ix.inv(I) == True{} : Bool}, hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}, hno: {IM.fl.ok(ns, d) == True{} : Bool}, hns: {IM.ix.flsep(I, s, d, ns) == True{} : Bool},
  hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}, m: LAT.Mirror(U32, w)) -> {KMd.chain(IM.mb.cons(IM.ix.par(I, x, k), ns), AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{w}, a}, s, x))), d, KMd.word(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{w}, a}, s, x))), d, P.at_fh())) == True{} : Bool}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e)
  %e : {KMd.chain(IM.mb.cons(IM.ix.par(I, x, k), ns), AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{_}, a}, s, x))), d, KMd.word(AD.view(U32, KMd.words(X.ix.remove(P.H{KM.MG{_}, a}, s, x))), d, P.at_fh())) == True{} : Bool}
  rf.k(I, t0, a, d, s, x, k, ns, hft, hd32, LAB.subst(Array<U32>, q => {IM.ix.real(AD.view(U32, q), d, s, I) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hr), hi, hl, hx, hno, hns,
    LAB.subst(Array<U32>, q => {KMd.chain(ns, AD.view(U32, q), d, KMd.word(AD.view(U32, q), d, P.at_fh())) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hc))

def Laws.remove_free(w, a, d, s, I, x, k, ns, hf, hd32, hr, hi, hl, hx, hno, hns, hc):
  rf.m(w, a, d, s, I, x, k, ns, hf, hd32, hr, hi, hl, hx, hno, hns, hc, LAT.mirror(U32, w))

# An insert's free list
def fi.has(+T: IM.Tr, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +b: U32, +ns: List<&2, U32>,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, IM.Has{T}) == True{} : Bool}, +hi: {IM.tr.ok(T, 0n) == True{} : Bool},
  +hoks: {IM.nd.ok(s, d) == True{} : Bool}, +hoffT: {IM.tr.offn(T, d, s) == True{} : Bool}, +hlayT: {IM.tr.lay(T, d) == True{} : Bool},
  +hfr: {IM.nd.ok(x, d) && (IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && IM.tr.offn(T, d, b)))))) == True{} : Bool},
  +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32}, +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool},
  +ha: {IM.tr.look(T, k) == None{} : Maybe<&2, U32>}, +hno: {IM.fl.ok(ns, d) == True{} : Bool}, +hnsS: {IM.fl.sep(ns, d, s) == True{} : Bool}, +hnsT: {IM.fl.offt(ns, T, d) == True{} : Bool},
  +hnx: {IM.fl.sep(ns, d, x) == True{} : Bool}, +hnsb: {IM.fl.sep(ns, d, b) == True{} : Bool}, +hc: {KMd.chain(Con{b, ns}, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}) -> {KMd.chain(ns, AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, KMd.word(AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, P.at_fh())) == True{} : Bool}:
  +hokx = and_l(IM.nd.ok(x, d), IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && IM.tr.offn(T, d, b))))), hfr)
  +hokb = and_l(IM.nd.ok(b, d), IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && IM.tr.offn(T, d, b)))), and_r(IM.nd.ok(x, d), IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && IM.tr.offn(T, d, b))))), hfr))
  %Equal.sym(P.H, X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a}, ins.heap.has(T, t0, a, d, s, x, k, b, hft, hd32, hre, hi, hoks, hoffT, hlayT, hfr, and_intro(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), Bool.and(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b), True{}), and_l(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b) && KMd.chain(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32))), hc), and_intro(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b), True{}, and_l(U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b), KMd.chain(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32))), and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), 0)), U32.is_eq(KMd.at_idx(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())), b) && KMd.chain(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (b + 1 : U32))), hc)), {==})), hk, hnb, ha)) : {KMd.chain(ns, AD.view(U32, KMd.words(_)), d, KMd.word(AD.view(U32, KMd.words(_)), d, P.at_fh())) == True{} : Bool}
  fl_take(t0, d, b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x, s, ns, hft, hd32, hc,
    neq_comm(AD.slot(P.at_fh(), d), AD.slot(b, d), off0(b, d, P.at_fh(), and_r(IM.ws.apart(KMd.nw(b), d), KMd.off.words(KMd.nw(b), d, P.at_fh()), and_r(U32.is_eq(P.base(b), b), IM.ws.apart(KMd.nw(b), d) && KMd.off.words(KMd.nw(b), d, P.at_fh()), hokb)))), neq_comm(AD.slot(P.at_fh(), d), AD.slot((b + 3 : U32), d), off3(b, d, P.at_fh(), and_r(IM.ws.apart(KMd.nw(b), d), KMd.off.words(KMd.nw(b), d, P.at_fh()), and_r(U32.is_eq(P.base(b), b), IM.ws.apart(KMd.nw(b), d) && KMd.off.words(KMd.nw(b), d, P.at_fh()), hokb)))), neq_comm(AD.slot(P.at_fh(), d), AD.slot((b + 1 : U32), d), off1(b, d, P.at_fh(), and_r(IM.ws.apart(KMd.nw(b), d), KMd.off.words(KMd.nw(b), d, P.at_fh()), and_r(U32.is_eq(P.base(b), b), IM.ws.apart(KMd.nw(b), d) && KMd.off.words(KMd.nw(b), d, P.at_fh()), hokb)))), neq_comm(AD.slot(P.at_fh(), d), AD.slot((b + 2 : U32), d), off2(b, d, P.at_fh(), and_r(IM.ws.apart(KMd.nw(b), d), KMd.off.words(KMd.nw(b), d, P.at_fh()), and_r(U32.is_eq(P.base(b), b), IM.ws.apart(KMd.nw(b), d) && KMd.off.words(KMd.nw(b), d, P.at_fh()), hokb)))),
    neq_comm(AD.slot(P.at_fh(), d), AD.slot(plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), d), plc2b(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32), d, P.at_fh(), lay_offb_fh(T, d, hlayT), off3(s, d, P.at_fh(), and_r(IM.ws.apart(KMd.nw(s), d), KMd.off.words(KMd.nw(s), d, P.at_fh()), and_r(U32.is_eq(P.base(s), s), IM.ws.apart(KMd.nw(s), d) && KMd.off.words(KMd.nw(s), d, P.at_fh()), hoks))))),
    neq_comm(AD.slot(P.at_fh(), d), AD.slot((x + 3 : U32), d), off3(x, d, P.at_fh(), and_r(IM.ws.apart(KMd.nw(x), d), KMd.off.words(KMd.nw(x), d, P.at_fh()), and_r(U32.is_eq(P.base(x), x), IM.ws.apart(KMd.nw(x), d) && KMd.off.words(KMd.nw(x), d, P.at_fh()), hokx)))),
    offw_fh(ns, d, hno), offw_sep0(ns, d, b, hnsb), offw_sep3(ns, d, b, hnsb), offw_sep1(ns, d, b, hnsb), offw_sep2(ns, d, b, hnsb),
    offw_plo(ns, T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, s, d, hnsS, hnsT), offw_sep3(ns, d, x, hnx))

def fi.ept(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +ns: List<&2, U32>,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s) == True{} : Bool}, +hokx: {IM.nd.ok(x, d) == True{} : Bool}, +hsxs: {IM.nd.sep(d, x, s) == True{} : Bool},
  +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32}, +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool},
  +hoks: {IM.nd.ok(s, d) == True{} : Bool}, +hnsS: {IM.fl.sep(ns, d, s) == True{} : Bool}, +hnx: {IM.fl.sep(ns, d, x) == True{} : Bool}, +hc: {KMd.chain(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}) -> {KMd.chain(ns, AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, KMd.word(AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, P.at_fh())) == True{} : Bool}:
  %Equal.sym(P.H, X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), P.H{KM.MG{Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s)}, a}, ins.heap.ept(t0, a, d, s, x, k, hft, hd32, hre, hokx, hsxs, hk, hnb)) : {KMd.chain(ns, AD.view(U32, KMd.words(_)), d, KMd.word(AD.view(U32, KMd.words(_)), d, P.at_fh())) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s)), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x)), AD.slot((x + 3 : U32), d), s), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), d, (x + 3 : U32), s, LA.set_full(U32, LAT.fromT(U32, t0), d, (s + 3 : U32), x, hft), hd32)) : {KMd.chain(ns, _, d, KMd.word(_, d, P.at_fh())) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), LA.set_view(U32, LAT.fromT(U32, t0), d, (s + 3 : U32), x, hft, hd32)) : {KMd.chain(ns, List.set(&2, U32, _, AD.slot((x + 3 : U32), d), s), d, KMd.word(List.set(&2, U32, _, AD.slot((x + 3 : U32), d), s), d, P.at_fh())) == True{} : Bool}
  fl_keepv(ns, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((s + 3 : U32), d), x), d, (x + 3 : U32), s, neq_comm(AD.slot(P.at_fh(), d), AD.slot((x + 3 : U32), d), off3(x, d, P.at_fh(), and_r(IM.ws.apart(KMd.nw(x), d), KMd.off.words(KMd.nw(x), d, P.at_fh()), and_r(U32.is_eq(P.base(x), x), IM.ws.apart(KMd.nw(x), d) && KMd.off.words(KMd.nw(x), d, P.at_fh()), hokx)))), offw_sep3(ns, d, x, hnx),
    fl_keepv(ns, AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32), x, neq_comm(AD.slot(P.at_fh(), d), AD.slot((s + 3 : U32), d), off3(s, d, P.at_fh(), and_r(IM.ws.apart(KMd.nw(s), d), KMd.off.words(KMd.nw(s), d, P.at_fh()), and_r(U32.is_eq(P.base(s), s), IM.ws.apart(KMd.nw(s), d) && KMd.off.words(KMd.nw(s), d, P.at_fh()), hoks)))), offw_sep3(ns, d, s, hnsS), hc))

def fi.k(I: IM.Ix, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +b: U32, +ns: List<&2, U32>,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, I) == True{} : Bool}, +hi: {IM.ix.inv(I) == True{} : Bool}, +hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  +hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool},
  +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32}, +hb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool},
  +ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}, +hno: {IM.fl.ok(ns, d) == True{} : Bool}, +hns: {IM.ix.flsep(I, s, d, ns) == True{} : Bool},
  +hnx: {IM.fl.sep(ns, d, x) == True{} : Bool}, +hnsb: {IM.fl.sep(ns, d, b) == True{} : Bool}, +hc: {KMd.chain(IM.ix.take(I, b, ns), AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}) -> {KMd.chain(ns, AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, KMd.word(AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x))), d, P.at_fh())) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      fi.ept(t0, a, d, s, x, k, ns, hft, hd32, hre, and_l(IM.nd.ok(x, d), IM.nd.sep(d, x, s), hfr), and_r(IM.nd.ok(x, d), IM.nd.sep(d, x, s), hfr), hk, hb, hl, hns, hnx, hc)
    case IM.Has{+t}:
      fi.has(t, t0, a, d, s, x, k, b, ns, hft, hd32, hre, hi,
        and_l(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl), and_l(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl)),
        and_r(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl)), hfr, hk, hb, ha, hno,
        and_l(IM.fl.sep(ns, d, s), IM.fl.offt(ns, t, d), hns), and_r(IM.fl.sep(ns, d, s), IM.fl.offt(ns, t, d), hns), hnx, hnsb, hc)

def fi.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +x: U32, +k: U32, +b: U32, +ns: List<&2, U32>,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}, hi: {IM.ix.inv(I) == True{} : Bool}, hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}, hk: {KMd.word(AD.view(U32, w), d, (x + 2 : U32)) == k : U32}, hb: {X.ix.branch(KMd.word(AD.view(U32, w), d, x)) == False{} : Bool},
  ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}, hno: {IM.fl.ok(ns, d) == True{} : Bool}, hns: {IM.ix.flsep(I, s, d, ns) == True{} : Bool}, hnx: {IM.fl.sep(ns, d, x) == True{} : Bool}, hnsb: {IM.fl.sep(ns, d, b) == True{} : Bool},
  hc: {KMd.chain(IM.ix.take(I, b, ns), AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}, m: LAT.Mirror(U32, w)) -> {KMd.chain(ns, AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{w}, a}, s, x))), d, KMd.word(AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{w}, a}, s, x))), d, P.at_fh())) == True{} : Bool}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e)
  %e : {KMd.chain(ns, AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{_}, a}, s, x))), d, KMd.word(AD.view(U32, KMd.words(X.ix.insert(P.H{KM.MG{_}, a}, s, x))), d, P.at_fh())) == True{} : Bool}
  fi.k(I, t0, a, d, s, x, k, b, ns, hft, hd32, LAB.subst(Array<U32>, q => {IM.ix.real(AD.view(U32, q), d, s, I) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hr), hi, hl, hfr,
    LAB.subst(Array<U32>, q => {KMd.word(AD.view(U32, q), d, (x + 2 : U32)) == k : U32}, w, LAT.fromT(U32, t0), ew, hk),
    LAB.subst(Array<U32>, q => {X.ix.branch(KMd.word(AD.view(U32, q), d, x)) == False{} : Bool}, w, LAT.fromT(U32, t0), ew, hb), ha, hno, hns, hnx, hnsb,
    LAB.subst(Array<U32>, q => {KMd.chain(IM.ix.take(I, b, ns), AD.view(U32, q), d, KMd.word(AD.view(U32, q), d, P.at_fh())) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hc))

def Laws.insert_free(w, a, d, s, I, x, k, b, ns, hf, hd32, hr, hi, hl, hfr, hk, hb, ha, hno, hns, hnx, hnsb, hc):
  fi.m(w, a, d, s, I, x, k, b, ns, hf, hd32, hr, hi, hl, hfr, hk, hb, ha, hno, hns, hnx, hnsb, hc, LAT.mirror(U32, w))

# A member found
# ==============

def ort_l(+e: Bool, +h: {Bool.or(e, False{}) == True{} : Bool}) -> {e == True{} : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      h

def ort_r(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +h: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  ME.subst(Bool, z => {Bool.or(z, b) == True{} : Bool}, a, False{}, ha, h)

# a member of a tree all of whose keys sit on side sd of bit i: its key there
def all_side.k(+hl: Bool, +l: IM.Tr, +r: IM.Tr, +v: List<&2, U32>, +d: Nat, +y: U32, +i: Nat, +sd: Bool, +hhl: {RG.has(IM.tr.leaves(l), y) == hl : Bool},
  +hy: {Bool.or(RG.has(IM.tr.leaves(l), y), RG.has(IM.tr.leaves(r), y)) == True{} : Bool},
  ihl: {RG.has(IM.tr.leaves(l), y) == True{} : Bool} -> {X.ix.same(X.ix.side(KMd.word(v, d, (y + 2 : U32)), i), sd) == True{} : Bool}, ihr: {RG.has(IM.tr.leaves(r), y) == True{} : Bool} -> {X.ix.same(X.ix.side(KMd.word(v, d, (y + 2 : U32)), i), sd) == True{} : Bool}) -> {X.ix.same(X.ix.side(KMd.word(v, d, (y + 2 : U32)), i), sd) == True{} : Bool}:
  match hl:
    case True{}:
      ihl(hhl)
    case False{}:
      ihr(ort_r(RG.has(IM.tr.leaves(l), y), RG.has(IM.tr.leaves(r), y), hhl, hy))

def all_side(t: IM.Tr, +p: U32, +i: Nat, +sd: Bool, +v: List<&2, U32>, +d: Nat, +q: U32, +s: U32, +y: U32,
  +hall: {IM.tr.all(t, p, i, sd) == True{} : Bool}, +hre: {IM.tr.real(v, d, t, q, s) == True{} : Bool}, +hy: {RG.has(IM.tr.leaves(t), y) == True{} : Bool}) -> {X.ix.same(X.ix.side(KMd.word(v, d, (y + 2 : U32)), i), sd) == True{} : Bool}:
  match t:
    case IM.Lf{+x, +k}:
      +hxy = MS.u32_eq_of_is_eq(x, y, ort_l(U32.is_eq(x, y), hy))
      +hk = MS.u32_eq_of_is_eq(KMd.word(v, d, (x + 2 : U32)), k, and_l(U32.is_eq(KMd.word(v, d, (x + 2 : U32)), k), U32.is_eq(KMd.word(v, d, (x + 3 : U32)), s), and_r(Bool.not(X.ix.branch(KMd.word(v, d, x))), U32.is_eq(KMd.word(v, d, (x + 2 : U32)), k) && U32.is_eq(KMd.word(v, d, (x + 3 : U32)), s), and_r(U32.is_eq(q, x), Bool.not(X.ix.branch(KMd.word(v, d, x))) && (U32.is_eq(KMd.word(v, d, (x + 2 : U32)), k) && U32.is_eq(KMd.word(v, d, (x + 3 : U32)), s)), hre))))
      %hxy : {X.ix.same(X.ix.side(KMd.word(v, d, (_ + 2 : U32)), i), sd) == True{} : Bool}
      %Equal.sym(U32, KMd.word(v, d, (x + 2 : U32)), k, hk) : {X.ix.same(X.ix.side(_, i), sd) == True{} : Bool}
      and_r(IM.tr.agree(k, p, i), X.ix.same(X.ix.side(k, i), sd), hall)
    case IM.Br{+b, +j, +l, +r}:
      all_side.k(RG.has(IM.tr.leaves(l), y), l, r, v, d, y, i, sd, {==}, Equal.trans(Bool, Bool.or(RG.has(IM.tr.leaves(l), y), RG.has(IM.tr.leaves(r), y)), RG.has(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), y), True{}, Equal.sym(Bool, RG.has(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), y), Bool.or(RG.has(IM.tr.leaves(l), y), RG.has(IM.tr.leaves(r), y)), has_app(IM.tr.leaves(l), IM.tr.leaves(r), y)), hy),
        hyl => all_side(l, p, i, sd, v, d, KMd.word(v, d, (b + 2 : U32)), s, y, and_l(IM.tr.all(l, p, i, sd), IM.tr.all(r, p, i, sd), hall), and_l(IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s), IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), and_r(Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), j), IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), and_r(X.ix.branch(KMd.word(v, d, b)), Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), j) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s)), and_r(U32.is_eq(q, b), X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), j) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s))), hre)))), hyl),
        hyr => all_side(r, p, i, sd, v, d, KMd.word(v, d, (b + 3 : U32)), s, y, and_r(IM.tr.all(l, p, i, sd), IM.tr.all(r, p, i, sd), hall), and_r(IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s), IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), and_r(Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), j), IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), and_r(X.ix.branch(KMd.word(v, d, b)), Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), j) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s)), and_r(U32.is_eq(q, b), X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), j) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s))), hre)))), hyr))

# a member of a tree on its invariant found at its key
def look_mem.k(+hl: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +v: List<&2, U32>, +d: Nat, +y: U32, +hhl: {RG.has(IM.tr.leaves(l), y) == hl : Bool},
  +hy: {Bool.or(RG.has(IM.tr.leaves(l), y), RG.has(IM.tr.leaves(r), y)) == True{} : Bool},
  hsl: {RG.has(IM.tr.leaves(l), y) == True{} : Bool} -> {X.ix.side(KMd.word(v, d, (y + 2 : U32)), i) == False{} : Bool}, hsr: {RG.has(IM.tr.leaves(r), y) == True{} : Bool} -> {X.ix.side(KMd.word(v, d, (y + 2 : U32)), i) == True{} : Bool},
  ihl: {RG.has(IM.tr.leaves(l), y) == True{} : Bool} -> {IM.tr.look(l, KMd.word(v, d, (y + 2 : U32))) == Some{y} : Maybe<&2, U32>}, ihr: {RG.has(IM.tr.leaves(r), y) == True{} : Bool} -> {IM.tr.look(r, KMd.word(v, d, (y + 2 : U32))) == Some{y} : Maybe<&2, U32>}) -> {IM.tr.look(IM.Br{b, i, l, r}, KMd.word(v, d, (y + 2 : U32))) == Some{y} : Maybe<&2, U32>}:
  match hl:
    case True{}:
      %Equal.sym(Bool, X.ix.side(KMd.word(v, d, (y + 2 : U32)), i), False{}, hsl(hhl)) : {IM.mb.pick(_, IM.tr.look(r, KMd.word(v, d, (y + 2 : U32))), IM.tr.look(l, KMd.word(v, d, (y + 2 : U32)))) == Some{y} : Maybe<&2, U32>}
      ihl(hhl)
    case False{}:
      +hyr = ort_r(RG.has(IM.tr.leaves(l), y), RG.has(IM.tr.leaves(r), y), hhl, hy)
      %Equal.sym(Bool, X.ix.side(KMd.word(v, d, (y + 2 : U32)), i), True{}, hsr(hyr)) : {IM.mb.pick(_, IM.tr.look(r, KMd.word(v, d, (y + 2 : U32))), IM.tr.look(l, KMd.word(v, d, (y + 2 : U32)))) == Some{y} : Maybe<&2, U32>}
      ihr(hyr)

def look_mem(t: IM.Tr, +v: List<&2, U32>, +d: Nat, +q: U32, +s: U32, +lo: Nat, +y: U32,
  +hok: {IM.tr.ok(t, lo) == True{} : Bool}, +hre: {IM.tr.real(v, d, t, q, s) == True{} : Bool}, +hy: {RG.has(IM.tr.leaves(t), y) == True{} : Bool}) -> {IM.tr.look(t, KMd.word(v, d, (y + 2 : U32))) == Some{y} : Maybe<&2, U32>}:
  match t:
    case IM.Lf{+x, +kk}:
      +hxy = MS.u32_eq_of_is_eq(x, y, ort_l(U32.is_eq(x, y), hy))
      +hk = MS.u32_eq_of_is_eq(KMd.word(v, d, (x + 2 : U32)), kk, and_l(U32.is_eq(KMd.word(v, d, (x + 2 : U32)), kk), U32.is_eq(KMd.word(v, d, (x + 3 : U32)), s), and_r(Bool.not(X.ix.branch(KMd.word(v, d, x))), U32.is_eq(KMd.word(v, d, (x + 2 : U32)), kk) && U32.is_eq(KMd.word(v, d, (x + 3 : U32)), s), and_r(U32.is_eq(q, x), Bool.not(X.ix.branch(KMd.word(v, d, x))) && (U32.is_eq(KMd.word(v, d, (x + 2 : U32)), kk) && U32.is_eq(KMd.word(v, d, (x + 3 : U32)), s)), hre))))
      %hxy : {IM.mb.hit(U32.is_eq(kk, KMd.word(v, d, (_ + 2 : U32))), x) == Some{_} : Maybe<&2, U32>}
      %Equal.sym(U32, KMd.word(v, d, (x + 2 : U32)), kk, hk) : {IM.mb.hit(U32.is_eq(kk, _), x) == Some{x} : Maybe<&2, U32>}
      %Equal.sym(Bool, U32.is_eq(kk, kk), True{}, is_eq_self(kk)) : {IM.mb.hit(_, x) == Some{x} : Maybe<&2, U32>}
      {==}
    case IM.Br{+b, +i, +l, +r}:
      +hyo = Equal.trans(Bool, Bool.or(RG.has(IM.tr.leaves(l), y), RG.has(IM.tr.leaves(r), y)), RG.has(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), y), True{}, Equal.sym(Bool, RG.has(List.append(&2, U32, IM.tr.leaves(l), IM.tr.leaves(r)), y), Bool.or(RG.has(IM.tr.leaves(l), y), RG.has(IM.tr.leaves(r), y)), has_app(IM.tr.leaves(l), IM.tr.leaves(r), y)), hy)
      look_mem.k(RG.has(IM.tr.leaves(l), y), b, i, l, r, v, d, y, {==}, hyo,
        hyl => same_eq(X.ix.side(KMd.word(v, d, (y + 2 : U32)), i), False{}, all_side(l, IM.tr.first(l), i, False{}, v, d, KMd.word(v, d, (b + 2 : U32)), s, y, and_l(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))), and_l(IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s), IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), and_r(Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i), IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), and_r(X.ix.branch(KMd.word(v, d, b)), Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s)), and_r(U32.is_eq(q, b), X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s))), hre)))), hyl)),
        hyr => same_eq(X.ix.side(KMd.word(v, d, (y + 2 : U32)), i), True{}, all_side(r, IM.tr.first(l), i, True{}, v, d, KMd.word(v, d, (b + 3 : U32)), s, y, and_l(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok)))), and_r(IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s), IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), and_r(Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i), IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), and_r(X.ix.branch(KMd.word(v, d, b)), Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s)), and_r(U32.is_eq(q, b), X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s))), hre)))), hyr)),
        hyl => look_mem(l, v, d, KMd.word(v, d, (b + 2 : U32)), s, 1n+i, y, and_l(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))), and_l(IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s), IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), and_r(Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i), IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), and_r(X.ix.branch(KMd.word(v, d, b)), Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s)), and_r(U32.is_eq(q, b), X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s))), hre)))), hyl),
        hyr => look_mem(r, v, d, KMd.word(v, d, (b + 3 : U32)), s, 1n+i, y, and_r(IM.tr.ok(l, 1n+i), IM.tr.ok(r, 1n+i), and_r(IM.tr.all(r, IM.tr.first(l), i, True{}), IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)), and_r(IM.tr.all(l, IM.tr.first(l), i, False{}), IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))), and_r(Nat.is_lt(i, 32n), IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i)))), and_r(Nat.is_le(lo, i), Nat.is_lt(i, 32n) && (IM.tr.all(l, IM.tr.first(l), i, False{}) && (IM.tr.all(r, IM.tr.first(l), i, True{}) && (IM.tr.ok(l, 1n+i) && (IM.tr.ok(r, 1n+i))))), hok))))), and_r(IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s), IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), and_r(Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i), IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s), and_r(X.ix.branch(KMd.word(v, d, b)), Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s)), and_r(U32.is_eq(q, b), X.ix.branch(KMd.word(v, d, b)) && (Nat.is_eq(X.ix.bitof(KMd.word(v, d, b)), i) && (IM.tr.real(v, d, l, KMd.word(v, d, (b + 2 : U32)), s) && IM.tr.real(v, d, r, KMd.word(v, d, (b + 3 : U32)), s))), hre)))), hyr))

def look_member.k(I: IM.Ix, +v: List<&2, U32>, +d: Nat, +s: U32, +y: U32, +hr: {IM.ix.real(v, d, s, I) == True{} : Bool}, +hi: {IM.ix.inv(I) == True{} : Bool},
  +hy: {RG.has(IM.ix.leaves(I), y) == True{} : Bool}) -> {IM.ix.look(I, KMd.word(v, d, (y + 2 : U32))) == Some{y} : Maybe<&2, U32>}:
  match I:
    case IM.Ept{}:
      Empty.absurd({IM.ix.look(IM.Ept{}, KMd.word(v, d, (y + 2 : U32))) == Some{y} : Maybe<&2, U32>}, MB.false_ne_true()(hy))
    case IM.Has{+t}:
      look_mem(t, v, d, KMd.word(v, d, (s + 3 : U32)), s, 0n, y, hi, and_r(Bool.not(U32.is_eq(KMd.word(v, d, (s + 3 : U32)), s)), IM.tr.real(v, d, t, KMd.word(v, d, (s + 3 : U32)), s), hr), hy)

def Laws.look_member(w, d, s, I, y, hr, hi, hy):
  look_member.k(I, AD.view(U32, w), d, s, y, hr, hi, hy)

# The serve's side
# ================

# node a's words off b's, read the other way
def disj_flip(+d: Nat, +a: U32, +b: U32, +h: {IM.nd.disj(d, a, b) == True{} : Bool}) -> {IM.nd.disj(d, b, a) == True{} : Bool}:
  and_intro(KMd.off.words(KMd.nw(a), d, b), KMd.off.words(KMd.nw(a), d, (b + 1 : U32)) && (KMd.off.words(KMd.nw(a), d, (b + 2 : U32)) && KMd.off.words(KMd.nw(a), d, (b + 3 : U32))), and_intro(Bool.not(Nat.is_eq(AD.slot(a, d), AD.slot(b, d))), Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot(b, d))) && (Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot(b, d))) && (Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot(b, d))) && True{})), nf(Nat.is_eq(AD.slot(a, d), AD.slot(b, d)), neq_comm(AD.slot(b, d), AD.slot(a, d), not_true(Nat.is_eq(AD.slot(b, d), AD.slot(a, d)), and_l(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot(a, d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(a, d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(a, d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(a, d))) && True{})), and_l(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h))))), and_intro(Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot(b, d))), Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot(b, d))) && (Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot(b, d))) && True{}), nf(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot(b, d)), neq_comm(AD.slot(b, d), AD.slot((a + 1 : U32), d), not_true(Nat.is_eq(AD.slot(b, d), AD.slot((a + 1 : U32), d)), and_l(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 1 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d))) && True{})), and_l(KMd.off.words(KMd.nw(b), d, (a + 1 : U32)), KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h)))))), and_intro(Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot(b, d))), Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot(b, d))) && True{}, nf(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot(b, d)), neq_comm(AD.slot(b, d), AD.slot((a + 2 : U32), d), not_true(Nat.is_eq(AD.slot(b, d), AD.slot((a + 2 : U32), d)), and_l(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 2 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 2 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d))) && True{})), and_l(KMd.off.words(KMd.nw(b), d, (a + 2 : U32)), KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (a + 1 : U32)), KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h))))))), and_intro(Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot(b, d))), True{}, nf(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot(b, d)), neq_comm(AD.slot(b, d), AD.slot((a + 3 : U32), d), not_true(Nat.is_eq(AD.slot(b, d), AD.slot((a + 3 : U32), d)), and_l(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 3 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d))) && True{})), and_r(KMd.off.words(KMd.nw(b), d, (a + 2 : U32)), KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (a + 1 : U32)), KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h))))))), {==})))), and_intro(KMd.off.words(KMd.nw(a), d, (b + 1 : U32)), KMd.off.words(KMd.nw(a), d, (b + 2 : U32)) && KMd.off.words(KMd.nw(a), d, (b + 3 : U32)), and_intro(Bool.not(Nat.is_eq(AD.slot(a, d), AD.slot((b + 1 : U32), d))), Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 1 : U32), d))) && True{})), nf(Nat.is_eq(AD.slot(a, d), AD.slot((b + 1 : U32), d)), neq_comm(AD.slot((b + 1 : U32), d), AD.slot(a, d), not_true(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(a, d)), and_l(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(a, d))), Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(a, d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(a, d))) && True{}), and_r(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot(a, d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(a, d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(a, d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(a, d))) && True{})), and_l(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h)))))), and_intro(Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 1 : U32), d))), Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 1 : U32), d))) && True{}), nf(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 1 : U32), d)), neq_comm(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d), not_true(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d)), and_l(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d))) && True{}), and_r(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 1 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d))) && True{})), and_l(KMd.off.words(KMd.nw(b), d, (a + 1 : U32)), KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h))))))), and_intro(Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 1 : U32), d))), Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 1 : U32), d))) && True{}, nf(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 1 : U32), d)), neq_comm(AD.slot((b + 1 : U32), d), AD.slot((a + 2 : U32), d), not_true(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 2 : U32), d)), and_l(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 2 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d))) && True{}), and_r(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 2 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 2 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d))) && True{})), and_l(KMd.off.words(KMd.nw(b), d, (a + 2 : U32)), KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (a + 1 : U32)), KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h)))))))), and_intro(Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 1 : U32), d))), True{}, nf(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 1 : U32), d)), neq_comm(AD.slot((b + 1 : U32), d), AD.slot((a + 3 : U32), d), not_true(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 3 : U32), d)), and_l(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d))) && True{}), and_r(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 3 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d))) && True{})), and_r(KMd.off.words(KMd.nw(b), d, (a + 2 : U32)), KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (a + 1 : U32)), KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h)))))))), {==})))), and_intro(KMd.off.words(KMd.nw(a), d, (b + 2 : U32)), KMd.off.words(KMd.nw(a), d, (b + 3 : U32)), and_intro(Bool.not(Nat.is_eq(AD.slot(a, d), AD.slot((b + 2 : U32), d))), Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 2 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 2 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 2 : U32), d))) && True{})), nf(Nat.is_eq(AD.slot(a, d), AD.slot((b + 2 : U32), d)), neq_comm(AD.slot((b + 2 : U32), d), AD.slot(a, d), not_true(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(a, d)), and_l(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(a, d))), Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(a, d))) && True{}, and_r(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(a, d))), Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(a, d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(a, d))) && True{}), and_r(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot(a, d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(a, d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(a, d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(a, d))) && True{})), and_l(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h))))))), and_intro(Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 2 : U32), d))), Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 2 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 2 : U32), d))) && True{}), nf(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 2 : U32), d)), neq_comm(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d), not_true(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d)), and_l(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d))) && True{}, and_r(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d))) && True{}), and_r(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 1 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d))) && True{})), and_l(KMd.off.words(KMd.nw(b), d, (a + 1 : U32)), KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h)))))))), and_intro(Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 2 : U32), d))), Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 2 : U32), d))) && True{}, nf(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 2 : U32), d)), neq_comm(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d), not_true(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d)), and_l(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d))) && True{}, and_r(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 2 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d))) && True{}), and_r(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 2 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 2 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d))) && True{})), and_l(KMd.off.words(KMd.nw(b), d, (a + 2 : U32)), KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (a + 1 : U32)), KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h))))))))), and_intro(Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 2 : U32), d))), True{}, nf(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 2 : U32), d)), neq_comm(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d), not_true(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d)), and_l(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d))) && True{}, and_r(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d))) && True{}), and_r(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 3 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d))) && True{})), and_r(KMd.off.words(KMd.nw(b), d, (a + 2 : U32)), KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (a + 1 : U32)), KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h))))))))), {==})))), and_intro(Bool.not(Nat.is_eq(AD.slot(a, d), AD.slot((b + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 3 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 3 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 3 : U32), d))) && True{})), nf(Nat.is_eq(AD.slot(a, d), AD.slot((b + 3 : U32), d)), neq_comm(AD.slot((b + 3 : U32), d), AD.slot(a, d), not_true(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(a, d)), and_l(Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(a, d))), True{}, and_r(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(a, d))), Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(a, d))) && True{}, and_r(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(a, d))), Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(a, d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(a, d))) && True{}), and_r(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot(a, d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot(a, d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot(a, d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot(a, d))) && True{})), and_l(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h)))))))), and_intro(Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 3 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 3 : U32), d))) && True{}), nf(Nat.is_eq(AD.slot((a + 1 : U32), d), AD.slot((b + 3 : U32), d)), neq_comm(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d), not_true(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d)), and_l(Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d))), True{}, and_r(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d))) && True{}, and_r(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d))) && True{}), and_r(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 1 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d))) && True{})), and_l(KMd.off.words(KMd.nw(b), d, (a + 1 : U32)), KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h))))))))), and_intro(Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 3 : U32), d))) && True{}, nf(Nat.is_eq(AD.slot((a + 2 : U32), d), AD.slot((b + 3 : U32), d)), neq_comm(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d), not_true(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d)), and_l(Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d))), True{}, and_r(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d))) && True{}, and_r(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 2 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d))) && True{}), and_r(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 2 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 2 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 2 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 2 : U32), d))) && True{})), and_l(KMd.off.words(KMd.nw(b), d, (a + 2 : U32)), KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (a + 1 : U32)), KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h)))))))))), and_intro(Bool.not(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 3 : U32), d))), True{}, nf(Nat.is_eq(AD.slot((a + 3 : U32), d), AD.slot((b + 3 : U32), d)), neq_comm(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d), not_true(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d)), and_l(Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d))), True{}, and_r(Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d))) && True{}, and_r(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d))) && True{}), and_r(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 3 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 3 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 3 : U32), d))) && True{})), and_r(KMd.off.words(KMd.nw(b), d, (a + 2 : U32)), KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, (a + 1 : U32)), KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), h)))))))))), {==})))))))

def lay_ok.k(+e: Bool, +m: U32, +t: List<&2, U32>, +d: Nat, +a: U32, +he: {U32.is_eq(m, a) == e : Bool},
  +hl: {RG.layout(Con{m, t}, d) == True{} : Bool}, +hb: {RG.bases(Con{m, t}) == True{} : Bool}, +ha: {Bool.or(U32.is_eq(m, a), RG.has(t, a)) == True{} : Bool},
  ih: {RG.has(t, a) == True{} : Bool} -> {IM.nd.ok(a, d) == True{} : Bool}) -> {IM.nd.ok(a, d) == True{} : Bool}:
  match e:
    case True{}:
      %MS.u32_eq_of_is_eq(m, a, he) : {IM.nd.ok(_, d) == True{} : Bool}
      and_intro(U32.is_eq(P.base(m), m), IM.ws.apart(KMd.nw(m), d) && KMd.off.words(KMd.nw(m), d, P.at_fh()), and_l(U32.is_eq(P.base(m), m), RG.bases(t), hb),
        and_intro(IM.ws.apart(KMd.nw(m), d), KMd.off.words(KMd.nw(m), d, P.at_fh()), and_l(RG.apartw(RG.nw(m), d), RG.off(RG.nw(m), d, P.at_fh()) && (RG.cross(t, d, m) && RG.layout(t, d)), hl),
          and_l(RG.off(RG.nw(m), d, P.at_fh()), RG.cross(t, d, m) && RG.layout(t, d), and_r(RG.apartw(RG.nw(m), d), RG.off(RG.nw(m), d, P.at_fh()) && (RG.cross(t, d, m) && RG.layout(t, d)), hl))))
    case False{}:
      ih(ort_r(U32.is_eq(m, a), RG.has(t, a), he, ha))

def lay_ok(N: List<&2, U32>, +d: Nat, +a: U32, +hl: {RG.layout(N, d) == True{} : Bool}, +hb: {RG.bases(N) == True{} : Bool}, +ha: {RG.has(N, a) == True{} : Bool}) -> {IM.nd.ok(a, d) == True{} : Bool}:
  match N:
    case Nil{}:
      Empty.absurd({IM.nd.ok(a, d) == True{} : Bool}, MB.false_ne_true()(ha))
    case Con{+m, +t}:
      lay_ok.k(U32.is_eq(m, a), m, t, d, a, {==}, hl, hb, ha, hta => lay_ok(t, d, a, and_r(RG.cross(t, d, m), RG.layout(t, d), and_r(RG.off(RG.nw(m), d, P.at_fh()), RG.cross(t, d, m) && RG.layout(t, d), and_r(RG.apartw(RG.nw(m), d), RG.off(RG.nw(m), d, P.at_fh()) && (RG.cross(t, d, m) && RG.layout(t, d)), hl))), and_r(U32.is_eq(P.base(m), m), RG.bases(t), hb), hta))

def Laws.layout_ok(N, d, a, hl, hb, ha):
  lay_ok(N, d, a, hl, hb, ha)

# a node of ys, a apart from every node of ys: a apart from it
def cross_has.k(+e: Bool, +y: U32, +r: List<&2, U32>, +d: Nat, +m: U32, +b: U32, +he: {U32.is_eq(y, b) == e : Bool},
  +hc: {RG.cross(Con{y, r}, d, m) == True{} : Bool}, +hb: {Bool.or(U32.is_eq(y, b), RG.has(r, b)) == True{} : Bool}, ih: {RG.has(r, b) == True{} : Bool} -> {RG.disj4(d, m, b) == True{} : Bool}) -> {RG.disj4(d, m, b) == True{} : Bool}:
  match e:
    case True{}:
      %MS.u32_eq_of_is_eq(y, b, he) : {RG.disj4(d, m, _) == True{} : Bool}
      and_l(RG.disj4(d, m, y), RG.cross(r, d, m), hc)
    case False{}:
      ih(ort_r(U32.is_eq(y, b), RG.has(r, b), he, hb))

def cross_has(ys: List<&2, U32>, +d: Nat, +m: U32, +b: U32, +hc: {RG.cross(ys, d, m) == True{} : Bool}, +hb: {RG.has(ys, b) == True{} : Bool}) -> {RG.disj4(d, m, b) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({RG.disj4(d, m, b) == True{} : Bool}, MB.false_ne_true()(hb))
    case Con{+y, +r}:
      cross_has.k(U32.is_eq(y, b), y, r, d, m, b, {==}, hc, hb, hrb => cross_has(r, d, m, b, and_r(RG.disj4(d, m, y), RG.cross(r, d, m), hc), hrb))

def ne_absurd(-A: Type, +m: U32, +a: U32, +b: U32, +ha: {m == a : U32}, +hb: {m == b : U32}, +hab: {U32.is_eq(a, b) == False{} : Bool}) -> A:
  Empty.absurd(A, MB.false_ne_true()(Equal.trans(Bool, False{}, U32.is_eq(a, b), True{}, Equal.sym(Bool, U32.is_eq(a, b), False{}, hab),
    ME.subst(U32, z => {U32.is_eq(z, b) == True{} : Bool}, m, a, ha, ME.subst(U32, z => {U32.is_eq(m, z) == True{} : Bool}, m, b, hb, is_eq_self(m))))))

def lay_sep.b(+eb: Bool, +m: U32, +t: List<&2, U32>, +d: Nat, +a: U32, +b: U32, +ham: {m == a : U32}, +heb: {U32.is_eq(m, b) == eb : Bool},
  +hc: {RG.cross(t, d, m) == True{} : Bool}, +hb: {Bool.or(U32.is_eq(m, b), RG.has(t, b)) == True{} : Bool}, +hab: {U32.is_eq(a, b) == False{} : Bool}) -> {IM.nd.sep(d, a, b) == True{} : Bool}:
  match eb:
    case True{}:
      ne_absurd({IM.nd.sep(d, a, b) == True{} : Bool}, m, a, b, ham, MS.u32_eq_of_is_eq(m, b, heb), hab)
    case False{}:
      +D = cross_has(t, d, m, b, hc, ort_r(U32.is_eq(m, b), RG.has(t, b), heb, hb))
      %ham : {IM.nd.sep(d, _, b) == True{} : Bool}
      and_intro(IM.nd.disj(d, m, b), IM.nd.disj(d, b, m), D, disj_flip(d, m, b, D))

def lay_sep.a(+eb: Bool, +m: U32, +t: List<&2, U32>, +d: Nat, +a: U32, +b: U32, +hea: {U32.is_eq(m, a) == False{} : Bool}, +heb: {U32.is_eq(m, b) == eb : Bool},
  +hc: {RG.cross(t, d, m) == True{} : Bool}, +ha: {Bool.or(U32.is_eq(m, a), RG.has(t, a)) == True{} : Bool}, +hb: {Bool.or(U32.is_eq(m, b), RG.has(t, b)) == True{} : Bool},
  ih: {RG.has(t, a) == True{} : Bool} -> {RG.has(t, b) == True{} : Bool} -> {IM.nd.sep(d, a, b) == True{} : Bool}) -> {IM.nd.sep(d, a, b) == True{} : Bool}:
  match eb:
    case True{}:
      +D = cross_has(t, d, m, a, hc, ort_r(U32.is_eq(m, a), RG.has(t, a), hea, ha))
      %MS.u32_eq_of_is_eq(m, b, heb) : {IM.nd.sep(d, a, _) == True{} : Bool}
      and_intro(IM.nd.disj(d, a, m), IM.nd.disj(d, m, a), disj_flip(d, m, a, D), D)
    case False{}:
      ih(ort_r(U32.is_eq(m, a), RG.has(t, a), hea, ha))(ort_r(U32.is_eq(m, b), RG.has(t, b), heb, hb))

def lay_sep.k(+ea: Bool, +m: U32, +t: List<&2, U32>, +d: Nat, +a: U32, +b: U32, +hea: {U32.is_eq(m, a) == ea : Bool},
  +hl: {RG.layout(Con{m, t}, d) == True{} : Bool}, +ha: {Bool.or(U32.is_eq(m, a), RG.has(t, a)) == True{} : Bool}, +hb: {Bool.or(U32.is_eq(m, b), RG.has(t, b)) == True{} : Bool}, +hab: {U32.is_eq(a, b) == False{} : Bool},
  ih: {RG.has(t, a) == True{} : Bool} -> {RG.has(t, b) == True{} : Bool} -> {IM.nd.sep(d, a, b) == True{} : Bool}) -> {IM.nd.sep(d, a, b) == True{} : Bool}:
  match ea:
    case True{}:
      lay_sep.b(U32.is_eq(m, b), m, t, d, a, b, MS.u32_eq_of_is_eq(m, a, hea), {==}, and_l(RG.cross(t, d, m), RG.layout(t, d), and_r(RG.off(RG.nw(m), d, P.at_fh()), RG.cross(t, d, m) && RG.layout(t, d), and_r(RG.apartw(RG.nw(m), d), RG.off(RG.nw(m), d, P.at_fh()) && (RG.cross(t, d, m) && RG.layout(t, d)), hl))), hb, hab)
    case False{}:
      lay_sep.a(U32.is_eq(m, b), m, t, d, a, b, hea, {==}, and_l(RG.cross(t, d, m), RG.layout(t, d), and_r(RG.off(RG.nw(m), d, P.at_fh()), RG.cross(t, d, m) && RG.layout(t, d), and_r(RG.apartw(RG.nw(m), d), RG.off(RG.nw(m), d, P.at_fh()) && (RG.cross(t, d, m) && RG.layout(t, d)), hl))), ha, hb, ih)

def lay_sep(N: List<&2, U32>, +d: Nat, +a: U32, +b: U32, +hl: {RG.layout(N, d) == True{} : Bool}, +ha: {RG.has(N, a) == True{} : Bool}, +hb: {RG.has(N, b) == True{} : Bool},
  +hab: {U32.is_eq(a, b) == False{} : Bool}) -> {IM.nd.sep(d, a, b) == True{} : Bool}:
  match N:
    case Nil{}:
      Empty.absurd({IM.nd.sep(d, a, b) == True{} : Bool}, MB.false_ne_true()(ha))
    case Con{+m, +t}:
      lay_sep.k(U32.is_eq(m, a), m, t, d, a, b, {==}, hl, ha, hb, hab, hta => htb => lay_sep(t, d, a, b, and_r(RG.cross(t, d, m), RG.layout(t, d), and_r(RG.off(RG.nw(m), d, P.at_fh()), RG.cross(t, d, m) && RG.layout(t, d), and_r(RG.apartw(RG.nw(m), d), RG.off(RG.nw(m), d, P.at_fh()) && (RG.cross(t, d, m) && RG.layout(t, d)), hl))), hta, htb, hab))

def Laws.layout_sep(N, d, a, b, hl, ha, hb, hab):
  lay_sep(N, d, a, b, hl, ha, hb, hab)

# each of ns apart from a leaf, as from its cursor
def offt_lf(ns: List<&2, U32>, +x: U32, +k: U32, +d: Nat, +h: {IM.fl.sep(ns, d, x) == True{} : Bool}) -> {IM.fl.offt(ns, IM.Lf{x, k}, d) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      and_intro(IM.nd.sep(d, x, n), IM.fl.offt(r, IM.Lf{x, k}, d), and_l(IM.nd.sep(d, x, n), IM.fl.sep(r, d, x), h), offt_lf(r, x, k, d, and_r(IM.nd.sep(d, x, n), IM.fl.sep(r, d, x), h)))

def offt_place(ns: List<&2, U32>, +t: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +d: Nat, +ht: {IM.fl.offt(ns, t, d) == True{} : Bool}, +hx: {IM.fl.sep(ns, d, x) == True{} : Bool}, +hb: {IM.fl.sep(ns, d, b) == True{} : Bool}) -> {IM.fl.offt(ns, IM.tr.place(t, x, k, b, c), d) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      and_intro(IM.tr.offn(IM.tr.place(t, x, k, b, c), d, n), IM.fl.offt(r, IM.tr.place(t, x, k, b, c), d),
        place_offn(t, x, k, b, c, d, n, and_l(IM.tr.offn(t, d, n), IM.fl.offt(r, t, d), ht), and_l(IM.nd.sep(d, x, n), IM.fl.sep(r, d, x), hx), and_l(IM.nd.sep(d, b, n), IM.fl.sep(r, d, b), hb)),
        offt_place(r, t, x, k, b, c, d, and_r(IM.tr.offn(t, d, n), IM.fl.offt(r, t, d), ht), and_r(IM.nd.sep(d, x, n), IM.fl.sep(r, d, x), hx), and_r(IM.nd.sep(d, b, n), IM.fl.sep(r, d, b), hb)))

def put_flsep.k(I: IM.Ix, +s: U32, +d: Nat, +x: U32, +k: U32, +b: U32, +ns: List<&2, U32>, +h: {IM.ix.flsep(I, s, d, ns) == True{} : Bool}, +hx: {IM.fl.sep(ns, d, x) == True{} : Bool}, +hb: {IM.fl.sep(ns, d, b) == True{} : Bool}) ->
  {IM.ix.flsep(IM.ix.put(I, x, k, b), s, d, ns) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      and_intro(IM.fl.sep(ns, d, s), IM.fl.offt(ns, IM.Lf{x, k}, d), h, offt_lf(ns, x, k, d, hx))
    case IM.Has{+t}:
      and_intro(IM.fl.sep(ns, d, s), IM.fl.offt(ns, IM.tr.place(t, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k)))), d), and_l(IM.fl.sep(ns, d, s), IM.fl.offt(ns, t, d), h),
        offt_place(ns, t, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k))), d, and_r(IM.fl.sep(ns, d, s), IM.fl.offt(ns, t, d), h), hx, hb))

def Laws.put_flsep(I, s, d, x, k, b, ns, h, hx, hb):
  put_flsep.k(I, s, d, x, k, b, ns, h, hx, hb)

def offt_cut(ns: List<&2, U32>, +t: IM.Tr, +x: U32, +k: U32, +d: Nat, +ht: {IM.fl.offt(ns, t, d) == True{} : Bool}) -> {IM.fl.offt(ns, IM.tr.cut(t, x, k), d) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      and_intro(IM.tr.offn(IM.tr.cut(t, x, k), d, n), IM.fl.offt(r, IM.tr.cut(t, x, k), d), cut_offn(t, x, k, d, n, and_l(IM.tr.offn(t, d, n), IM.fl.offt(r, t, d), ht)),
        offt_cut(r, t, x, k, d, and_r(IM.tr.offn(t, d, n), IM.fl.offt(r, t, d), ht)))

def del_flsep.h(+only: Bool, +t: IM.Tr, +s: U32, +d: Nat, +x: U32, +k: U32, +ns: List<&2, U32>, +h: {IM.ix.flsep(IM.Has{t}, s, d, ns) == True{} : Bool}) ->
  {IM.ix.flsep(IM.ix.del.k(only, t, x, k), s, d, ns) == True{} : Bool}:
  match only:
    case True{}:
      and_l(IM.fl.sep(ns, d, s), IM.fl.offt(ns, t, d), h)
    case False{}:
      and_intro(IM.fl.sep(ns, d, s), IM.fl.offt(ns, IM.tr.cut(t, x, k), d), and_l(IM.fl.sep(ns, d, s), IM.fl.offt(ns, t, d), h), offt_cut(ns, t, x, k, d, and_r(IM.fl.sep(ns, d, s), IM.fl.offt(ns, t, d), h)))

def del_flsep.k(I: IM.Ix, +s: U32, +d: Nat, +x: U32, +k: U32, +ns: List<&2, U32>, +h: {IM.ix.flsep(I, s, d, ns) == True{} : Bool}) -> {IM.ix.flsep(IM.ix.del(I, x, k), s, d, ns) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      h
    case IM.Has{+t}:
      del_flsep.h(U32.is_eq(IM.tr.addr(t), x), t, s, d, x, k, ns, h)

def Laws.del_flsep(I, s, d, x, k, ns, h):
  del_flsep.k(I, s, d, x, k, ns, h)

def sub_app(xs: List<&2, U32>, +ys: List<&2, U32>, +N: List<&2, U32>, +hx: {RG.sub(xs, N) == True{} : Bool}, +hy: {RG.sub(ys, N) == True{} : Bool}) -> {RG.sub(List.append(&2, U32, xs, ys), N) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+z, +r}:
      and_intro(RG.has(N, z), RG.sub(List.append(&2, U32, r, ys), N), and_l(RG.has(N, z), RG.sub(r, N), hx), sub_app(r, ys, N, and_r(RG.has(N, z), RG.sub(r, N), hx), hy))

def sub_app_l(xs: List<&2, U32>, +ys: List<&2, U32>, +N: List<&2, U32>, +h: {RG.sub(List.append(&2, U32, xs, ys), N) == True{} : Bool}) -> {RG.sub(xs, N) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      and_intro(RG.has(N, z), RG.sub(r, N), and_l(RG.has(N, z), RG.sub(List.append(&2, U32, r, ys), N), h), sub_app_l(r, ys, N, and_r(RG.has(N, z), RG.sub(List.append(&2, U32, r, ys), N), h)))

def sub_app_r(xs: List<&2, U32>, +ys: List<&2, U32>, +N: List<&2, U32>, +h: {RG.sub(List.append(&2, U32, xs, ys), N) == True{} : Bool}) -> {RG.sub(ys, N) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+z, +r}:
      sub_app_r(r, ys, N, and_r(RG.has(N, z), RG.sub(List.append(&2, U32, r, ys), N), h))

def join_sub(+sd: Bool, +U: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +N: List<&2, U32>, +hU: {RG.sub(IM.tr.nodes(U), N) == True{} : Bool}, +hx: {RG.has(N, x) == True{} : Bool}, +hb: {RG.has(N, b) == True{} : Bool}) ->
  {RG.sub(IM.tr.nodes(IM.tr.join(sd, U, x, k, b, c)), N) == True{} : Bool}:
  match sd:
    case True{}:
      and_intro(RG.has(N, b), RG.sub(List.append(&2, U32, IM.tr.nodes(U), [x]), N), hb, sub_app(IM.tr.nodes(U), [x], N, hU, and_intro(RG.has(N, x), True{}, hx, {==})))
    case False{}:
      and_intro(RG.has(N, b), RG.sub(List.append(&2, U32, [x], IM.tr.nodes(U)), N), hb, sub_app([x], IM.tr.nodes(U), N, and_intro(RG.has(N, x), True{}, hx, {==}), hU))

def ps.k(+lt: Bool, +sd: Bool, +b2: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +N: List<&2, U32>,
  +h: {RG.sub(IM.tr.nodes(IM.Br{b2, i, l, r}), N) == True{} : Bool}, +hx: {RG.has(N, x) == True{} : Bool}, +hb: {RG.has(N, b) == True{} : Bool},
  +ihl: {RG.sub(IM.tr.nodes(IM.tr.place(l, x, k, b, c)), N) == True{} : Bool}, +ihr: {RG.sub(IM.tr.nodes(IM.tr.place(r, x, k, b, c)), N) == True{} : Bool}) ->
  {RG.sub(IM.tr.nodes(IM.tr.place.k(lt, sd, b2, i, l, r, IM.tr.place(l, x, k, b, c), IM.tr.place(r, x, k, b, c), x, k, b, c)), N) == True{} : Bool}:
  match lt:
    case False{}:
      join_sub(X.ix.side(k, c), IM.Br{b2, i, l, r}, x, k, b, c, N, h, hx, hb)
    case True{}:
      match sd:
        case True{}:
          +hb2 = and_l(RG.has(N, b2), RG.sub(List.append(&2, U32, IM.tr.nodes(l), IM.tr.nodes(r)), N), h)
          +hlr = and_r(RG.has(N, b2), RG.sub(List.append(&2, U32, IM.tr.nodes(l), IM.tr.nodes(r)), N), h)
          and_intro(RG.has(N, b2), RG.sub(List.append(&2, U32, IM.tr.nodes(l), IM.tr.nodes(IM.tr.place(r, x, k, b, c))), N), hb2, sub_app(IM.tr.nodes(l), IM.tr.nodes(IM.tr.place(r, x, k, b, c)), N, sub_app_l(IM.tr.nodes(l), IM.tr.nodes(r), N, hlr), ihr))
        case False{}:
          +hb2 = and_l(RG.has(N, b2), RG.sub(List.append(&2, U32, IM.tr.nodes(l), IM.tr.nodes(r)), N), h)
          +hlr = and_r(RG.has(N, b2), RG.sub(List.append(&2, U32, IM.tr.nodes(l), IM.tr.nodes(r)), N), h)
          and_intro(RG.has(N, b2), RG.sub(List.append(&2, U32, IM.tr.nodes(IM.tr.place(l, x, k, b, c)), IM.tr.nodes(r)), N), hb2, sub_app(IM.tr.nodes(IM.tr.place(l, x, k, b, c)), IM.tr.nodes(r), N, ihl, sub_app_r(IM.tr.nodes(l), IM.tr.nodes(r), N, hlr)))

def place_sub(t: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +N: List<&2, U32>, +h: {RG.sub(IM.tr.nodes(t), N) == True{} : Bool}, +hx: {RG.has(N, x) == True{} : Bool}, +hb: {RG.has(N, b) == True{} : Bool}) -> {RG.sub(IM.tr.nodes(IM.tr.place(t, x, k, b, c)), N) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      join_sub(X.ix.side(k, c), IM.Lf{y, ky}, x, k, b, c, N, h, hx, hb)
    case IM.Br{+b2, +i, +l, +r}:
      +hlr = and_r(RG.has(N, b2), RG.sub(List.append(&2, U32, IM.tr.nodes(l), IM.tr.nodes(r)), N), h)
      ps.k(Nat.is_lt(i, c), X.ix.side(k, i), b2, i, l, r, x, k, b, c, N, h, hx, hb,
        place_sub(l, x, k, b, c, N, sub_app_l(IM.tr.nodes(l), IM.tr.nodes(r), N, hlr), hx, hb), place_sub(r, x, k, b, c, N, sub_app_r(IM.tr.nodes(l), IM.tr.nodes(r), N, hlr), hx, hb))

def put_sub.k(I: IM.Ix, +x: U32, +k: U32, +b: U32, +N: List<&2, U32>, +h: {RG.sub(IM.ix.nodes(I), N) == True{} : Bool}, +hx: {RG.has(N, x) == True{} : Bool}, +hb: {RG.has(N, b) == True{} : Bool}) ->
  {RG.sub(IM.ix.nodes(IM.ix.put(I, x, k, b)), N) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      and_intro(RG.has(N, x), True{}, hx, {==})
    case IM.Has{+t}:
      place_sub(t, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k))), N, h, hx, hb)

def Laws.put_sub(I, x, k, b, N, h, hx, hb):
  put_sub.k(I, x, k, b, N, h, hx, hb)

def cs.r(+hit: Bool, +b: U32, +i: Nat, +l: IM.Tr, +cr: IM.Tr, +N: List<&2, U32>, +hb: {RG.has(N, b) == True{} : Bool}, +hl: {RG.sub(IM.tr.nodes(l), N) == True{} : Bool}, +hcr: {RG.sub(IM.tr.nodes(cr), N) == True{} : Bool}) ->
  {RG.sub(IM.tr.nodes(IM.tr.cut.r(hit, b, i, l, cr)), N) == True{} : Bool}:
  match hit:
    case True{}:
      hl
    case False{}:
      and_intro(RG.has(N, b), RG.sub(List.append(&2, U32, IM.tr.nodes(l), IM.tr.nodes(cr)), N), hb, sub_app(IM.tr.nodes(l), IM.tr.nodes(cr), N, hl, hcr))

def cs.l(+hit: Bool, +b: U32, +i: Nat, +r: IM.Tr, +cl: IM.Tr, +N: List<&2, U32>, +hb: {RG.has(N, b) == True{} : Bool}, +hr: {RG.sub(IM.tr.nodes(r), N) == True{} : Bool}, +hcl: {RG.sub(IM.tr.nodes(cl), N) == True{} : Bool}) ->
  {RG.sub(IM.tr.nodes(IM.tr.cut.l(hit, b, i, r, cl)), N) == True{} : Bool}:
  match hit:
    case True{}:
      hr
    case False{}:
      and_intro(RG.has(N, b), RG.sub(List.append(&2, U32, IM.tr.nodes(cl), IM.tr.nodes(r)), N), hb, sub_app(IM.tr.nodes(cl), IM.tr.nodes(r), N, hcl, hr))

def cs.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +cl: IM.Tr, +cr: IM.Tr, +N: List<&2, U32>, +hb: {RG.has(N, b) == True{} : Bool},
  +hl: {RG.sub(IM.tr.nodes(l), N) == True{} : Bool}, +hr: {RG.sub(IM.tr.nodes(r), N) == True{} : Bool}, +hcl: {RG.sub(IM.tr.nodes(cl), N) == True{} : Bool}, +hcr: {RG.sub(IM.tr.nodes(cr), N) == True{} : Bool}) ->
  {RG.sub(IM.tr.nodes(IM.tr.cut.k(sd, b, i, l, r, x, cl, cr)), N) == True{} : Bool}:
  match sd:
    case True{}:
      cs.r(U32.is_eq(IM.tr.addr(r), x), b, i, l, cr, N, hb, hl, hcr)
    case False{}:
      cs.l(U32.is_eq(IM.tr.addr(l), x), b, i, r, cl, N, hb, hr, hcl)

def cut_sub(t: IM.Tr, +x: U32, +k: U32, +N: List<&2, U32>, +h: {RG.sub(IM.tr.nodes(t), N) == True{} : Bool}) -> {RG.sub(IM.tr.nodes(IM.tr.cut(t, x, k)), N) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      h
    case IM.Br{+b, +i, +l, +r}:
      +hlr = and_r(RG.has(N, b), RG.sub(List.append(&2, U32, IM.tr.nodes(l), IM.tr.nodes(r)), N), h)
      +hl = sub_app_l(IM.tr.nodes(l), IM.tr.nodes(r), N, hlr)
      +hr = sub_app_r(IM.tr.nodes(l), IM.tr.nodes(r), N, hlr)
      cs.k(X.ix.side(k, i), b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k), N, and_l(RG.has(N, b), RG.sub(List.append(&2, U32, IM.tr.nodes(l), IM.tr.nodes(r)), N), h), hl, hr,
        cut_sub(l, x, k, N, hl), cut_sub(r, x, k, N, hr))

def del_sub.h(+only: Bool, +t: IM.Tr, +x: U32, +k: U32, +N: List<&2, U32>, +h: {RG.sub(IM.tr.nodes(t), N) == True{} : Bool}) -> {RG.sub(IM.ix.nodes(IM.ix.del.k(only, t, x, k)), N) == True{} : Bool}:
  match only:
    case True{}:
      {==}
    case False{}:
      cut_sub(t, x, k, N, h)

def del_sub.k(I: IM.Ix, +x: U32, +k: U32, +N: List<&2, U32>, +h: {RG.sub(IM.ix.nodes(I), N) == True{} : Bool}) -> {RG.sub(IM.ix.nodes(IM.ix.del(I, x, k)), N) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      {==}
    case IM.Has{+t}:
      del_sub.h(U32.is_eq(IM.tr.addr(t), x), t, x, k, N, h)

def Laws.del_sub(I, x, k, N, h):
  del_sub.k(I, x, k, N, h)

# A removal's dropped nodes
# =========================

def cx.r(+hit: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +d: Nat, +hhit: {U32.is_eq(IM.tr.addr(r), x) == hit : Bool},
  +hl: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool}, +hxr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>}, ih: {hit == False{} : Bool} -> {IM.tr.offn(IM.tr.cut(r, x, k), d, x) == True{} : Bool}) ->
  {IM.tr.offn(IM.tr.cut.r(hit, b, i, l, IM.tr.cut(r, x, k)), d, x) == True{} : Bool}:
  match hit:
    case True{}:
      apart_look(l, r, d, k, x, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl)))), hxr)
    case False{}:
      and_intro(IM.nd.sep(d, b, x), IM.tr.offn(l, d, x) && IM.tr.offn(IM.tr.cut(r, x, k), d, x), sep_sym(d, x, b, look_sep(r, b, d, k, x, and_l(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl))), hxr)),
        and_intro(IM.tr.offn(l, d, x), IM.tr.offn(IM.tr.cut(r, x, k), d, x), apart_look(l, r, d, k, x, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl)))), hxr), ih({==})))

def cx.l(+hit: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +d: Nat, +hhit: {U32.is_eq(IM.tr.addr(l), x) == hit : Bool},
  +hl: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool}, +hxl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>}, ih: {hit == False{} : Bool} -> {IM.tr.offn(IM.tr.cut(l, x, k), d, x) == True{} : Bool}) ->
  {IM.tr.offn(IM.tr.cut.l(hit, b, i, r, IM.tr.cut(l, x, k)), d, x) == True{} : Bool}:
  match hit:
    case True{}:
      apart_look(r, l, d, k, x, apart_sym(r, l, d, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl))))), hxl)
    case False{}:
      and_intro(IM.nd.sep(d, b, x), IM.tr.offn(IM.tr.cut(l, x, k), d, x) && IM.tr.offn(r, d, x), sep_sym(d, x, b, look_sep(l, b, d, k, x, and_l(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl)), hxl)),
        and_intro(IM.tr.offn(IM.tr.cut(l, x, k), d, x), IM.tr.offn(r, d, x), ih({==}), apart_look(r, l, d, k, x, apart_sym(r, l, d, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl))))), hxl)))

def cx.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +d: Nat, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hl: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool}, +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(l), x) == False{} : Bool} -> {IM.tr.offn(IM.tr.cut(l, x, k), d, x) == True{} : Bool}, ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(r), x) == False{} : Bool} -> {IM.tr.offn(IM.tr.cut(r, x, k), d, x) == True{} : Bool}) ->
  {IM.tr.offn(IM.tr.cut.k(X.ix.side(k, i), b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k)), d, x) == True{} : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {IM.tr.offn(IM.tr.cut.k(_, b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k)), d, x) == True{} : Bool}
      cx.r(U32.is_eq(IM.tr.addr(r), x), b, i, l, r, x, k, d, {==}, hl, hx_side(True{}, k, i, l, r, x, hsd, hx), hn => ihr(hx_side(True{}, k, i, l, r, x, hsd, hx))(hn))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {IM.tr.offn(IM.tr.cut.k(_, b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k)), d, x) == True{} : Bool}
      cx.l(U32.is_eq(IM.tr.addr(l), x), b, i, l, r, x, k, d, {==}, hl, hx_side(False{}, k, i, l, r, x, hsd, hx), hn => ihl(hx_side(False{}, k, i, l, r, x, hsd, hx))(hn))

# the cursor a removal drops apart from the tree that remains
def cut_offx(t: IM.Tr, +x: U32, +k: U32, +d: Nat, +hl: {IM.tr.lay(t, d) == True{} : Bool}, +hx: {IM.tr.look(t, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(t), x) == False{} : Bool}) -> {IM.tr.offn(IM.tr.cut(t, x, k), d, x) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      lf_absurd({IM.tr.offn(IM.tr.cut(IM.Lf{y, ky}, x, k), d, x) == True{} : Bool}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      cx.k(X.ix.side(k, i), b, i, l, r, x, k, d, {==}, hl, hx,
        hxl => hnl => cut_offx(l, x, k, d, and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl))))), hxl, hnl),
        hxr => hnr => cut_offx(r, x, k, d, and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl))))), hxr, hnr))

# a branch of t apart from o where t is: the parent a removal frees

def cut_pa_ap.h(+hit: Bool, +b: U32, +sib: U32, +loc: U32, cd: IM.Cut, +d: Nat, +o: IM.Tr, +hb: {IM.tr.offn(o, d, b) == True{} : Bool},
  ih: {hit == False{} : Bool} -> {IM.tr.offn(o, d, cut.pa(cd)) == True{} : Bool}) -> {IM.tr.offn(o, d, cut.pa(IM.cut.k.of(hit, b, sib, loc, cd))) == True{} : Bool}:
  match hit:
    case True{}:
      hb
    case False{}:
      ih({==})

def cut_pa_ap.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +o: IM.Tr, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hb: {IM.tr.offn(o, d, b) == True{} : Bool},
  +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(l), x) == False{} : Bool} -> {IM.tr.offn(o, d, cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32)))) == True{} : Bool},
  ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(r), x) == False{} : Bool} -> {IM.tr.offn(o, d, cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32)))) == True{} : Bool}) ->
  {IM.tr.offn(o, d, cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) == True{} : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {IM.tr.offn(o, d, cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) == True{} : Bool}
      cut_pa_ap.h(U32.is_eq(IM.tr.addr(r), x), b, IM.tr.addr(l), loc, IM.tr.cutat(r, x, k, (b + 3 : U32)), d, o, hb, hn => ihr(hx_side(True{}, k, i, l, r, x, hsd, hx))(hn))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {IM.tr.offn(o, d, cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) == True{} : Bool}
      cut_pa_ap.h(U32.is_eq(IM.tr.addr(l), x), b, IM.tr.addr(r), loc, IM.tr.cutat(l, x, k, (b + 2 : U32)), d, o, hb, hn => ihl(hx_side(False{}, k, i, l, r, x, hsd, hx))(hn))

def cut_pa_ap(t: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +o: IM.Tr, +ho: {IM.tr.apart(t, o, d) == True{} : Bool},
  +hx: {IM.tr.look(t, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(t), x) == False{} : Bool}) -> {IM.tr.offn(o, d, cut.pa(IM.tr.cutat(t, x, k, loc))) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      lf_absurd({IM.tr.offn(o, d, cut.pa(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc))) == True{} : Bool}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      cut_pa_ap.k(X.ix.side(k, i), b, i, l, r, x, k, loc, d, o, {==}, and_l(IM.tr.offn(o, d, b), IM.tr.apart(l, o, d) && IM.tr.apart(r, o, d), ho), hx,
        hxl => hnl => cut_pa_ap(l, x, k, (b + 2 : U32), d, o, and_l(IM.tr.apart(l, o, d), IM.tr.apart(r, o, d), and_r(IM.tr.offn(o, d, b), IM.tr.apart(l, o, d) && IM.tr.apart(r, o, d), ho)), hxl, hnl),
        hxr => hnr => cut_pa_ap(r, x, k, (b + 3 : U32), d, o, and_r(IM.tr.apart(l, o, d), IM.tr.apart(r, o, d), and_r(IM.tr.offn(o, d, b), IM.tr.apart(l, o, d) && IM.tr.apart(r, o, d), ho)), hxr, hnr))

def cp.r(+hit: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +hhit: {U32.is_eq(IM.tr.addr(r), x) == hit : Bool},
  +hl: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool}, +hxr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>}, ih: {hit == False{} : Bool} -> {IM.tr.offn(IM.tr.cut(r, x, k), d, cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32)))) == True{} : Bool}) ->
  {IM.tr.offn(IM.tr.cut.r(hit, b, i, l, IM.tr.cut(r, x, k)), d, cut.pa(IM.cut.k.of(hit, b, IM.tr.addr(l), loc, IM.tr.cutat(r, x, k, (b + 3 : U32))))) == True{} : Bool}:
  match hit:
    case True{}:
      and_l(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl))
    case False{}:
      and_intro(IM.nd.sep(d, b, cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32)))), IM.tr.offn(l, d, cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32)))) && IM.tr.offn(IM.tr.cut(r, x, k), d, cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32)))),
        sep_sym(d, cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32))), b, cut_pa_sep(r, x, k, (b + 3 : U32), d, b, and_l(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl))), hxr, hhit)),
        and_intro(IM.tr.offn(l, d, cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32)))), IM.tr.offn(IM.tr.cut(r, x, k), d, cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32)))), cut_pa_ap(r, x, k, (b + 3 : U32), d, l, apart_sym(r, l, d, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl))))), hxr, hhit), ih({==})))

def cp.l(+hit: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +hhit: {U32.is_eq(IM.tr.addr(l), x) == hit : Bool},
  +hl: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool}, +hxl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>}, ih: {hit == False{} : Bool} -> {IM.tr.offn(IM.tr.cut(l, x, k), d, cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32)))) == True{} : Bool}) ->
  {IM.tr.offn(IM.tr.cut.l(hit, b, i, r, IM.tr.cut(l, x, k)), d, cut.pa(IM.cut.k.of(hit, b, IM.tr.addr(r), loc, IM.tr.cutat(l, x, k, (b + 2 : U32))))) == True{} : Bool}:
  match hit:
    case True{}:
      and_l(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl)))
    case False{}:
      and_intro(IM.nd.sep(d, b, cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32)))), IM.tr.offn(IM.tr.cut(l, x, k), d, cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32)))) && IM.tr.offn(r, d, cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32)))),
        sep_sym(d, cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32))), b, cut_pa_sep(l, x, k, (b + 2 : U32), d, b, and_l(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl)), hxl, hhit)),
        and_intro(IM.tr.offn(IM.tr.cut(l, x, k), d, cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32)))), IM.tr.offn(r, d, cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32)))), ih({==}), cut_pa_ap(l, x, k, (b + 2 : U32), d, r, and_l(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl)))), hxl, hhit)))

def cp.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +hsd: {X.ix.side(k, i) == sd : Bool},
  +hl: {IM.tr.lay(IM.Br{b, i, l, r}, d) == True{} : Bool}, +hx: {IM.mb.pick(X.ix.side(k, i), IM.tr.look(r, k), IM.tr.look(l, k)) == Some{x} : Maybe<&2, U32>},
  ihl: {IM.tr.look(l, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(l), x) == False{} : Bool} -> {IM.tr.offn(IM.tr.cut(l, x, k), d, cut.pa(IM.tr.cutat(l, x, k, (b + 2 : U32)))) == True{} : Bool}, ihr: {IM.tr.look(r, k) == Some{x} : Maybe<&2, U32>} -> {U32.is_eq(IM.tr.addr(r), x) == False{} : Bool} -> {IM.tr.offn(IM.tr.cut(r, x, k), d, cut.pa(IM.tr.cutat(r, x, k, (b + 3 : U32)))) == True{} : Bool}) ->
  {IM.tr.offn(IM.tr.cut.k(X.ix.side(k, i), b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k)), d, cut.pa(IM.cut.at.k(X.ix.side(k, i), b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) == True{} : Bool}:
  match sd:
    case True{}:
      %Equal.sym(Bool, X.ix.side(k, i), True{}, hsd) : {IM.tr.offn(IM.tr.cut.k(_, b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k)), d, cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) == True{} : Bool}
      cp.r(U32.is_eq(IM.tr.addr(r), x), b, i, l, r, x, k, loc, d, {==}, hl, hx_side(True{}, k, i, l, r, x, hsd, hx), hn => ihr(hx_side(True{}, k, i, l, r, x, hsd, hx))(hn))
    case False{}:
      %Equal.sym(Bool, X.ix.side(k, i), False{}, hsd) : {IM.tr.offn(IM.tr.cut.k(_, b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k)), d, cut.pa(IM.cut.at.k(_, b, l, r, x, loc, IM.tr.cutat(l, x, k, X.ix.kid(False{}, b)), IM.tr.cutat(r, x, k, X.ix.kid(True{}, b))))) == True{} : Bool}
      cp.l(U32.is_eq(IM.tr.addr(l), x), b, i, l, r, x, k, loc, d, {==}, hl, hx_side(False{}, k, i, l, r, x, hsd, hx), hn => ihl(hx_side(False{}, k, i, l, r, x, hsd, hx))(hn))

# the parent a removal frees apart from the tree that remains
def cut_offpa(t: IM.Tr, +x: U32, +k: U32, +loc: U32, +d: Nat, +hl: {IM.tr.lay(t, d) == True{} : Bool}, +hx: {IM.tr.look(t, k) == Some{x} : Maybe<&2, U32>}, +hne: {U32.is_eq(IM.tr.addr(t), x) == False{} : Bool}) -> {IM.tr.offn(IM.tr.cut(t, x, k), d, cut.pa(IM.tr.cutat(t, x, k, loc))) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      lf_absurd({IM.tr.offn(IM.tr.cut(IM.Lf{y, ky}, x, k), d, cut.pa(IM.tr.cutat(IM.Lf{y, ky}, x, k, loc))) == True{} : Bool}, y, ky, x, k, hx, hne)
    case IM.Br{+b, +i, +l, +r}:
      cp.k(X.ix.side(k, i), b, i, l, r, x, k, loc, d, {==}, hl, hx,
        hxl => hnl => cut_offpa(l, x, k, (b + 2 : U32), d, and_l(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl))))), hxl, hnl),
        hxr => hnr => cut_offpa(r, x, k, (b + 3 : U32), d, and_r(IM.tr.lay(l, d), IM.tr.lay(r, d), and_r(IM.tr.apart(l, r, d), IM.tr.lay(l, d) && IM.tr.lay(r, d), and_r(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hl))))), hxr, hnr))

def dd.br(+b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +s: U32, +d: Nat, +x: U32, +k: U32, +hl: {IM.ix.lay(IM.Has{IM.Br{b, i, l, r}}, s, d) == True{} : Bool}, +hx: {IM.tr.look(IM.Br{b, i, l, r}, k) == Some{x} : Maybe<&2, U32>}) ->
  {IM.ix.flsep(IM.ix.del(IM.Has{IM.Br{b, i, l, r}}, x, k), s, d, IM.mb.cons(IM.ix.par(IM.Has{IM.Br{b, i, l, r}}, x, k), [x])) == True{} : Bool}:
  +hlayT = and_r(IM.tr.offn(IM.Br{b, i, l, r}, d, s), IM.tr.lay(IM.Br{b, i, l, r}, d), and_r(IM.nd.ok(s, d), IM.tr.offn(IM.Br{b, i, l, r}, d, s) && IM.tr.lay(IM.Br{b, i, l, r}, d), hl))
  +hoffs = and_l(IM.tr.offn(IM.Br{b, i, l, r}, d, s), IM.tr.lay(IM.Br{b, i, l, r}, d), and_r(IM.nd.ok(s, d), IM.tr.offn(IM.Br{b, i, l, r}, d, s) && IM.tr.lay(IM.Br{b, i, l, r}, d), hl))
  +hneT = sep_ne(d, x, b, ls.k(X.ix.side(k, i), d, i, l, r, k, x, b, {==}, hx, hxl => look_sep(l, b, d, k, x, and_l(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hlayT)), hxl), hxr => look_sep(r, b, d, k, x, and_l(IM.tr.offn(r, d, b), IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)), and_r(IM.tr.offn(l, d, b), IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d))), and_r(IM.nd.ok(b, d), IM.tr.offn(l, d, b) && (IM.tr.offn(r, d, b) && (IM.tr.apart(l, r, d) && (IM.tr.lay(l, d) && IM.tr.lay(r, d)))), hlayT))), hxr)))
  %Equal.sym(Bool, U32.is_eq(b, x), False{}, hneT) : {IM.ix.flsep(IM.ix.del.k(_, IM.Br{b, i, l, r}, x, k), s, d, IM.mb.cons(IM.ix.par(IM.Has{IM.Br{b, i, l, r}}, x, k), [x])) == True{} : Bool}
  %Equal.sym(Maybe<&2, U32>, IM.tr.par(IM.Br{b, i, l, r}, x, k), Some{cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))}, par_cut(IM.Br{b, i, l, r}, x, k, (s + 3 : U32), hx, hneT)) : {IM.ix.flsep(IM.Has{IM.tr.cut(IM.Br{b, i, l, r}, x, k)}, s, d, IM.mb.cons(_, [x])) == True{} : Bool}
  and_intro(IM.fl.sep([cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), x], d, s), IM.fl.offt([cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), x], IM.tr.cut(IM.Br{b, i, l, r}, x, k), d),
    and_intro(IM.nd.sep(d, s, cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), IM.fl.sep([x], d, s), sep_sym(d, cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), s, cut_pa_sep(IM.Br{b, i, l, r}, x, k, (s + 3 : U32), d, s, hoffs, hx, hneT)),
      and_intro(IM.nd.sep(d, s, x), True{}, sep_sym(d, x, s, look_sep(IM.Br{b, i, l, r}, s, d, k, x, hoffs, hx)), {==})),
    and_intro(IM.tr.offn(IM.tr.cut(IM.Br{b, i, l, r}, x, k), d, cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), IM.fl.offt([x], IM.tr.cut(IM.Br{b, i, l, r}, x, k), d), cut_offpa(IM.Br{b, i, l, r}, x, k, (s + 3 : U32), d, hlayT, hx, hneT),
      and_intro(IM.tr.offn(IM.tr.cut(IM.Br{b, i, l, r}, x, k), d, x), True{}, cut_offx(IM.Br{b, i, l, r}, x, k, d, hlayT, hx, hneT), {==})))

def dd.lf(+y: U32, +ky: U32, +s: U32, +d: Nat, +x: U32, +k: U32, +hl: {IM.ix.lay(IM.Has{IM.Lf{y, ky}}, s, d) == True{} : Bool}, +hx: {IM.tr.look(IM.Lf{y, ky}, k) == Some{x} : Maybe<&2, U32>}) ->
  {IM.ix.flsep(IM.ix.del(IM.Has{IM.Lf{y, ky}}, x, k), s, d, IM.mb.cons(IM.ix.par(IM.Has{IM.Lf{y, ky}}, x, k), [x])) == True{} : Bool}:
  %hit_some(U32.is_eq(ky, k), y, x, hx) : {IM.ix.flsep(IM.ix.del.k(U32.is_eq(y, _), IM.Lf{y, ky}, _, k), s, d, [_]) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(y, y), True{}, is_eq_self(y)) : {IM.ix.flsep(IM.ix.del.k(_, IM.Lf{y, ky}, y, k), s, d, [y]) == True{} : Bool}
  and_intro(IM.nd.sep(d, s, y), True{}, sep_sym(d, y, s, and_l(IM.tr.offn(IM.Lf{y, ky}, d, s), IM.tr.lay(IM.Lf{y, ky}, d), and_r(IM.nd.ok(s, d), IM.tr.offn(IM.Lf{y, ky}, d, s) && IM.tr.lay(IM.Lf{y, ky}, d), hl))), {==})

def dd.k(I: IM.Ix, +s: U32, +d: Nat, +x: U32, +k: U32, +hl: {IM.ix.lay(I, s, d) == True{} : Bool}, +hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}) ->
  {IM.ix.flsep(IM.ix.del(I, x, k), s, d, IM.mb.cons(IM.ix.par(I, x, k), [x])) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      Empty.absurd({IM.ix.flsep(IM.ix.del(IM.Ept{}, x, k), s, d, IM.mb.cons(IM.ix.par(IM.Ept{}, x, k), [x])) == True{} : Bool}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, m => is_some(m), None{}, Some{x}, hx)))
    case IM.Has{+t}:
      match t:
        case IM.Lf{+y, +ky}:
          dd.lf(y, ky, s, d, x, k, hl, hx)
        case IM.Br{+b, +i, +l, +r}:
          dd.br(b, i, l, r, s, d, x, k, hl, hx)

def Laws.del_drop(I, s, d, x, k, hl, hx):
  dd.k(I, s, d, x, k, hl, hx)

# The heap's side
# ===============

# word j off every word of ns: off their words 1
def offw_nodes(ns: List<&2, U32>, +d: Nat, +j: U32, +h: {KMd.nodes.off(ns, d, j) == True{} : Bool}) -> {offw(ns, d, j) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      and_intro(Bool.not(Nat.is_eq(AD.slot(j, d), AD.slot((n + 1 : U32), d))), offw(r, d, j),
        nf(Nat.is_eq(AD.slot(j, d), AD.slot((n + 1 : U32), d)), off1(n, d, j, and_l(KMd.off.words(KMd.nw(n), d, j), KMd.nodes.off(r, d, j), h))),
        offw_nodes(r, d, j, and_r(KMd.off.words(KMd.nw(n), d, j), KMd.nodes.off(r, d, j), h)))

def ck.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +j: U32, +val: U32, +ns: List<&2, U32>, hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hjh: {Nat.is_eq(AD.slot(j, d), AD.slot(P.at_fh(), d)) == False{} : Bool}, +hn: {KMd.nodes.off(ns, d, j) == True{} : Bool}, hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}, m: LAT.Mirror(U32, w)) -> {KMd.chain(ns, AD.view(U32, KMd.words(P.wr(P.H{KM.MG{w}, a}, j, val))), d, KMd.word(AD.view(U32, KMd.words(P.wr(P.H{KM.MG{w}, a}, j, val))), d, P.at_fh())) == True{} : Bool}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e)
  %e : {KMd.chain(ns, AD.view(U32, KMd.words(P.wr(P.H{KM.MG{_}, a}, j, val))), d, KMd.word(AD.view(U32, KMd.words(P.wr(P.H{KM.MG{_}, a}, j, val))), d, P.at_fh())) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), j, val)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(j, d), val), LA.set_view(U32, LAT.fromT(U32, t0), d, j, val, hft, hd32)) : {KMd.chain(ns, _, d, KMd.word(_, d, P.at_fh())) == True{} : Bool}
  fl_keepv(ns, AD.view(U32, LAT.fromT(U32, t0)), d, j, val, hjh, offw_nodes(ns, d, j, hn), LAB.subst(Array<U32>, q => {KMd.chain(ns, AD.view(U32, q), d, KMd.word(AD.view(U32, q), d, P.at_fh())) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hc))

def Laws.chain_kept(w, a, d, j, val, ns, hf, hd32, hjh, hn, hc):
  ck.m(w, a, d, j, val, ns, hf, hd32, hjh, hn, hc, LAT.mirror(U32, w))

# the heap a free leaves
def fh1(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +Pn: U32) -> {P.free(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, Pn) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.base(Pn), 0), (P.base(Pn) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))}, a} : P.H}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()), (LAT.fromT(U32, t0), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), LA.get_pair(U32, LAT.fromT(U32, t0), P.at_fh())) : {P.free.fh(KM.m_get.fin(_), a, Pn) == P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.base(Pn), 0), (P.base(Pn) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))}, a} : P.H}
  {==}

# a node Pn freed, the nodes ns the free list's first before: Pn, then ns
def fl_push(+t0: LAT.Tree<U32>, +d: Nat, +Pn: U32, +ns: List<&2, U32>, +hf: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hb: {P.base(Pn) == Pn : U32}, +hPh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((Pn + 1 : U32), d)) == False{} : Bool},
  +hoP: {offw(ns, d, Pn) == True{} : Bool}, +hoP1: {offw(ns, d, (Pn + 1 : U32)) == True{} : Bool}, +hoH: {offw(ns, d, P.at_fh()) == True{} : Bool},
  +hc: {KMd.chain(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}) -> {KMd.chain(Con{Pn, ns}, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, P.at_fh())) == True{} : Bool}:
  %Equal.sym(U32, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, P.at_fh()), ((Pn >> 2n : U32) + 1 : U32), Equal.trans(U32, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32)), P.at_fh())), ((Pn >> 2n : U32) + 1 : U32), wg(Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32)), d, P.at_fh(), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), d, P.at_fh(), ((Pn >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), d, (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t0), d, Pn, 0, hf))), hd32), LA.get_set_same(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32)))) : {KMd.chain(Con{Pn, ns}, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, _) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(((Pn >> 2n : U32) + 1 : U32), 0), False{}, fl_nz(Pn)) : {(Bool.not(_) && (U32.is_eq(KMd.at_idx(((Pn >> 2n : U32) + 1 : U32)), Pn) && KMd.chain(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, (Pn + 1 : U32))))) == True{} : Bool}
  %Equal.sym(U32, KMd.at_idx(((Pn >> 2n : U32) + 1 : U32)), P.base(Pn), fl_idx(Pn)) : {(Bool.not(False{}) && (U32.is_eq(_, Pn) && KMd.chain(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, (Pn + 1 : U32))))) == True{} : Bool}
  %Equal.sym(U32, P.base(Pn), Pn, hb) : {(Bool.not(False{}) && (U32.is_eq(_, Pn) && KMd.chain(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, (Pn + 1 : U32))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(Pn, Pn), True{}, is_eq_self(Pn)) : {(Bool.not(False{}) && (_ && KMd.chain(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, (Pn + 1 : U32))))) == True{} : Bool}
  %Equal.sym(U32, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, (Pn + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Equal.trans(U32, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, (Pn + 1 : U32)), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32)), (Pn + 1 : U32))), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), wg(Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32)), d, (Pn + 1 : U32), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), d, P.at_fh(), ((Pn >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), d, (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t0), d, Pn, 0, hf))), hd32), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32)), (Pn + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), (Pn + 1 : U32))), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), LA.get_set_other(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), d, P.at_fh(), (Pn + 1 : U32), ((Pn >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), d, (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t0), d, Pn, 0, hf)), hd32, hPh), Equal.trans(U32, Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), (Pn + 1 : U32))), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), LA.get_set_same(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), wg(LAT.fromT(U32, t0), d, P.at_fh(), hf, hd32)))))) : {KMd.chain(ns, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), d, _) == True{} : Bool}
  ME.subst(List<&2, U32>, z => {KMd.chain(ns, z, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())))), AD.slot(P.at_fh(), d), ((Pn >> 2n : U32) + 1 : U32)), AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32))), List.set(&2, U32, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())))), AD.slot(P.at_fh(), d), ((Pn >> 2n : U32) + 1 : U32)), LA.set_view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), d, P.at_fh(), ((Pn >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), d, (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t0), d, Pn, 0, hf)), hd32)), chain_set(ns, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())))), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), P.at_fh(), ((Pn >> 2n : U32) + 1 : U32), hoH, ME.subst(List<&2, U32>, z => {KMd.chain(ns, z, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}, List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0)), AD.slot((Pn + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())))), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())))), List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0)), AD.slot((Pn + 1 : U32), d), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), LA.set_view(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0), d, (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t0), d, Pn, 0, hf), hd32)), chain_set(ns, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), (Pn + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), hoP1, ME.subst(List<&2, U32>, z => {KMd.chain(ns, z, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh())) == True{} : Bool}, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(Pn, d), 0), AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0)), Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), Pn, 0)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(Pn, d), 0), LA.set_view(U32, LAT.fromT(U32, t0), d, Pn, 0, hf, hd32)), chain_set(ns, AD.view(U32, LAT.fromT(U32, t0)), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_fh()), Pn, 0, hoP, hc))))))

def fp.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +r: U32, +ns: List<&2, U32>, hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hok: {IM.nd.ok(r, d) == True{} : Bool}, +hno: {IM.fl.ok(ns, d) == True{} : Bool}, +hsep: {IM.fl.sep(ns, d, r) == True{} : Bool}, hc: {KMd.chain(ns, AD.view(U32, w), d, KMd.word(AD.view(U32, w), d, P.at_fh())) == True{} : Bool}, m: LAT.Mirror(U32, w)) -> {KMd.chain(Con{r, ns}, AD.view(U32, KMd.words(P.free(P.H{KM.MG{w}, a}, r))), d, KMd.word(AD.view(U32, KMd.words(P.free(P.H{KM.MG{w}, a}, r))), d, P.at_fh())) == True{} : Bool}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e)
  +hbase = MS.u32_eq_of_is_eq(P.base(r), r, and_l(U32.is_eq(P.base(r), r), IM.ws.apart(KMd.nw(r), d) && KMd.off.words(KMd.nw(r), d, P.at_fh()), hok))
  %e : {KMd.chain(Con{r, ns}, AD.view(U32, KMd.words(P.free(P.H{KM.MG{_}, a}, r))), d, KMd.word(AD.view(U32, KMd.words(P.free(P.H{KM.MG{_}, a}, r))), d, P.at_fh())) == True{} : Bool}
  %Equal.sym(P.H, P.free(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, r), P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((r >> 2n : U32) + 1 : U32))}, a}, fh1(t0, a, r)) : {KMd.chain(Con{r, ns}, AD.view(U32, KMd.words(_)), d, KMd.word(AD.view(U32, KMd.words(_)), d, P.at_fh())) == True{} : Bool}
  %Equal.sym(U32, P.base(r), r, hbase) : {KMd.chain(Con{r, ns}, AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), _, 0), (_ + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((r >> 2n : U32) + 1 : U32))), d, KMd.word(AD.view(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), _, 0), (_ + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((r >> 2n : U32) + 1 : U32))), d, P.at_fh())) == True{} : Bool}
  fl_push(t0, d, r, ns, hft, hd32, hbase, off1(r, d, P.at_fh(), and_r(IM.ws.apart(KMd.nw(r), d), KMd.off.words(KMd.nw(r), d, P.at_fh()), and_r(U32.is_eq(P.base(r), r), IM.ws.apart(KMd.nw(r), d) && KMd.off.words(KMd.nw(r), d, P.at_fh()), hok))), offw_sep0(ns, d, r, hsep), offw_sep1(ns, d, r, hsep), offw_fh(ns, d, hno),
    LAB.subst(Array<U32>, q => {KMd.chain(ns, AD.view(U32, q), d, KMd.word(AD.view(U32, q), d, P.at_fh())) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hc))

def Laws.free_push(w, a, d, r, ns, hf, hd32, hok, hno, hsep, hc):
  fp.m(w, a, d, r, ns, hf, hd32, hok, hno, hsep, hc, LAT.mirror(U32, w))

def ff.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +r: U32, hf: {AD.full(U32, w, d) == True{} : Bool}, m: LAT.Mirror(U32, w)) -> {AD.full(U32, KMd.words(P.free(P.H{KM.MG{w}, a}, r)), d) == True{} : Bool}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  %e : {AD.full(U32, KMd.words(P.free(P.H{KM.MG{_}, a}, r)), d) == True{} : Bool}
  %Equal.sym(P.H, P.free(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, r), P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), P.at_fh(), ((r >> 2n : U32) + 1 : U32))}, a}, fh1(t0, a, r)) : {AD.full(U32, KMd.words(_), d) == True{} : Bool}
  LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.base(r), 0), (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh()))), d, P.at_fh(), ((r >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.base(r), 0), d, (P.base(r) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), P.at_fh())), LA.set_full(U32, LAT.fromT(U32, t0), d, P.base(r), 0, hft)))

def Laws.free_full(w, a, d, r, hf):
  ff.m(w, a, d, r, hf, LAT.mirror(U32, w))

def ifl.has(+T: IM.Tr, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +b: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, IM.Has{T}) == True{} : Bool}, +hi: {IM.tr.ok(T, 0n) == True{} : Bool},
  +hoks: {IM.nd.ok(s, d) == True{} : Bool}, +hoffT: {IM.tr.offn(T, d, s) == True{} : Bool}, +hlayT: {IM.tr.lay(T, d) == True{} : Bool},
  +hfr: {IM.nd.ok(x, d) && (IM.nd.ok(b, d) && (IM.nd.sep(d, x, b) && (IM.nd.sep(d, x, s) && (IM.nd.sep(d, b, s) && (IM.tr.offn(T, d, x) && IM.tr.offn(T, d, b)))))) == True{} : Bool}, +hm: {IM.ix.room(IM.Has{T}, AD.view(U32, LAT.fromT(U32, t0)), d, b) == True{} : Bool},
  +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32}, +hnb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool},
  +ha: {IM.tr.look(T, k) == None{} : Maybe<&2, U32>}) -> {AD.full(U32, KMd.words(X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x)), d) == True{} : Bool}:
  %Equal.sym(P.H, X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), (x + 3 : U32), s)}, a}, ins.heap.has(T, t0, a, d, s, x, k, b, hft, hd32, hre, hi, hoks, hoffT, hlayT, hfr, hm, hk, hnb, ha)) : {AD.full(U32, KMd.words(_), d) == True{} : Bool}
  LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b), d, (x + 3 : U32), s, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x)), d, plc.lo(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), b, LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), (b + 1 : U32), P.era()), d, (b + 2 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))), x), LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32))))), d, (b + 1 : U32), P.era(), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))))), d, (b + 3 : U32), X.ix.pick(X.ix.side(k, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), x, plc.cu(IM.tr.plc(T, IM.cr.i(X.ix.diff(k, IM.tr.near(T, k))), k, (s + 3 : U32)))), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32)))), d, b, X.ix.hd(IM.cr.i(X.ix.diff(k, IM.tr.near(T, k)))), LA.set_full(U32, LAT.fromT(U32, t0), d, P.at_fh(), Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (b + 1 : U32))), hft)))))))

def ifl.k(I: IM.Ix, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32, +b: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, I) == True{} : Bool}, +hi: {IM.ix.inv(I) == True{} : Bool}, +hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  +hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}, +hm: {IM.ix.room(I, AD.view(U32, LAT.fromT(U32, t0)), d, b) == True{} : Bool},
  +hk: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 2 : U32)) == k : U32}, +hb: {X.ix.branch(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, x)) == False{} : Bool},
  +ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}) -> {AD.full(U32, KMd.words(X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x)), d) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      %Equal.sym(P.H, X.ix.insert(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), P.H{KM.MG{Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), (x + 3 : U32), s)}, a}, ins.heap.ept(t0, a, d, s, x, k, hft, hd32, hre, and_l(IM.nd.ok(x, d), IM.nd.sep(d, x, s), hfr), and_r(IM.nd.ok(x, d), IM.nd.sep(d, x, s), hfr), hk, hb)) : {AD.full(U32, KMd.words(_), d) == True{} : Bool}
      LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), x), d, (x + 3 : U32), s, LA.set_full(U32, LAT.fromT(U32, t0), d, (s + 3 : U32), x, hft))
    case IM.Has{+t}:
      ifl.has(t, t0, a, d, s, x, k, b, hft, hd32, hre, hi,
        and_l(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl), and_l(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl)),
        and_r(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl)), hfr, hm, hk, hb, ha)

def ifl.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +x: U32, +k: U32, +b: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}, hi: {IM.ix.inv(I) == True{} : Bool}, hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  hfr: {IM.ix.fresh(I, s, x, b, d) == True{} : Bool}, hm: {IM.ix.room(I, AD.view(U32, w), d, b) == True{} : Bool},
  hk: {KMd.word(AD.view(U32, w), d, (x + 2 : U32)) == k : U32}, hb: {X.ix.branch(KMd.word(AD.view(U32, w), d, x)) == False{} : Bool},
  ha: {IM.ix.look(I, k) == None{} : Maybe<&2, U32>}, m: LAT.Mirror(U32, w)) -> {AD.full(U32, KMd.words(X.ix.insert(P.H{KM.MG{w}, a}, s, x)), d) == True{} : Bool}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e)
  %e : {AD.full(U32, KMd.words(X.ix.insert(P.H{KM.MG{_}, a}, s, x)), d) == True{} : Bool}
  ifl.k(I, t0, a, d, s, x, k, b, hft, hd32, LAB.subst(Array<U32>, q => {IM.ix.real(AD.view(U32, q), d, s, I) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hr), hi, hl, hfr,
    LAB.subst(Array<U32>, q => {IM.ix.room(I, AD.view(U32, q), d, b) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hm),
    LAB.subst(Array<U32>, q => {KMd.word(AD.view(U32, q), d, (x + 2 : U32)) == k : U32}, w, LAT.fromT(U32, t0), ew, hk),
    LAB.subst(Array<U32>, q => {X.ix.branch(KMd.word(AD.view(U32, q), d, x)) == False{} : Bool}, w, LAT.fromT(U32, t0), ew, hb), ha)

def Laws.insert_full(w, a, d, s, I, x, k, b, hf, hd32, hr, hi, hl, hfr, hm, hk, hb, ha):
  ifl.m(w, a, d, s, I, x, k, b, hf, hd32, hr, hi, hl, hfr, hm, hk, hb, ha, LAT.mirror(U32, w))

def rfl.k(I: IM.Ix, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +x: U32, +k: U32,
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hre: {IM.ix.real(AD.view(U32, LAT.fromT(U32, t0)), d, s, I) == True{} : Bool}, +hi: {IM.ix.inv(I) == True{} : Bool}, +hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  +hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}) -> {AD.full(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x)), d) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      Empty.absurd({AD.full(U32, KMd.words(X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x)), d) == True{} : Bool}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, m => is_some(m), None{}, Some{x}, hx)))
    case IM.Has{+t}:
      match t:
        case IM.Lf{+y, +ky}:
          %Equal.sym(P.H, X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), (s + 3 : U32), s)}, a}, rm.heap.lf(t0, a, d, s, x, k, y, ky, hft, hd32, and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Lf{y, ky}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre), hx)) : {AD.full(U32, KMd.words(_), d) == True{} : Bool}
          LA.set_full(U32, LAT.fromT(U32, t0), d, (s + 3 : U32), s, hft)
        case IM.Br{+b, +i, +l, +r}:
          %Equal.sym(P.H, X.ix.remove(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, s, x), P.H{KM.MG{Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32))}, a}, rm.heap.br(t0, a, d, s, x, k, b, i, l, r, hft, hd32, and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, LAT.fromT(U32, t0)), d, IM.Br{b, i, l, r}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (s + 3 : U32)), s), hre), hi,
            and_l(IM.nd.ok(s, d), IM.tr.offn(IM.Br{b, i, l, r}, d, s) && IM.tr.lay(IM.Br{b, i, l, r}, d), hl), and_l(IM.tr.offn(IM.Br{b, i, l, r}, d, s), IM.tr.lay(IM.Br{b, i, l, r}, d), and_r(IM.nd.ok(s, d), IM.tr.offn(IM.Br{b, i, l, r}, d, s) && IM.tr.lay(IM.Br{b, i, l, r}, d), hl)),
            and_r(IM.tr.offn(IM.Br{b, i, l, r}, d, s), IM.tr.lay(IM.Br{b, i, l, r}, d), and_r(IM.nd.ok(s, d), IM.tr.offn(IM.Br{b, i, l, r}, d, s) && IM.tr.lay(IM.Br{b, i, l, r}, d), hl)), hx)) : {AD.full(U32, KMd.words(_), d) == True{} : Bool}
          LA.set_full(U32, Array.set(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh()))), d, P.at_fh(), ((cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) >> 2n : U32) + 1 : U32), LA.set_full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0), d, (cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))) + 1 : U32), Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), P.at_fh())), LA.set_full(U32, Array.set(U32, LAT.fromT(U32, t0), cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32)))), d, cut.pa(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), 0, LA.set_full(U32, LAT.fromT(U32, t0), d, cut.lo(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), cut.si(IM.tr.cutat(IM.Br{b, i, l, r}, x, k, (s + 3 : U32))), hft))))

def rfl.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +x: U32, +k: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}, hi: {IM.ix.inv(I) == True{} : Bool}, hl: {IM.ix.lay(I, s, d) == True{} : Bool},
  hx: {IM.ix.look(I, k) == Some{x} : Maybe<&2, U32>}, m: LAT.Mirror(U32, w)) -> {AD.full(U32, KMd.words(X.ix.remove(P.H{KM.MG{w}, a}, s, x)), d) == True{} : Bool}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e)
  %e : {AD.full(U32, KMd.words(X.ix.remove(P.H{KM.MG{_}, a}, s, x)), d) == True{} : Bool}
  rfl.k(I, t0, a, d, s, x, k, hft, hd32, LAB.subst(Array<U32>, q => {IM.ix.real(AD.view(U32, q), d, s, I) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hr), hi, hl, hx)

def Laws.remove_full(w, a, d, s, I, x, k, hf, hd32, hr, hi, hl, hx):
  rfl.m(w, a, d, s, I, x, k, hf, hd32, hr, hi, hl, hx, LAT.mirror(U32, w))

# A realization kept by a write off it
# ====================================

def rk2.k(I: IM.Ix, +v: List<&2, U32>, +d: Nat, +s: U32, +j: U32, +val: U32, +hj: {IM.ix.offall(I, s, d, j) == True{} : Bool}, +hr: {IM.ix.real(v, d, s, I) == True{} : Bool}) ->
  {IM.ix.real(List.set(&2, U32, v, AD.slot(j, d), val), d, s, I) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      %wl_ne(v, d, j, (s + 3 : U32), val, neq_comm(AD.slot((s + 3 : U32), d), AD.slot(j, d), not_true(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d)), hj))) : {U32.is_eq(_, s) == True{} : Bool}
      hr
    case IM.Has{+t}:
      +h3 = neq_comm(AD.slot((s + 3 : U32), d), AD.slot(j, d), not_true(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d)), and_l(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d))), IM.tr.off(t, d, j), hj)))
      %wl_ne(v, d, j, (s + 3 : U32), val, h3) : {Bool.not(U32.is_eq(_, s)) && IM.tr.real(List.set(&2, U32, v, AD.slot(j, d), val), d, t, _, s) == True{} : Bool}
      %real_set(t, v, d, j, val, KMd.word(v, d, (s + 3 : U32)), s, and_r(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(j, d))), IM.tr.off(t, d, j), hj)) :
        {Bool.not(U32.is_eq(KMd.word(v, d, (s + 3 : U32)), s)) && _ == True{} : Bool}
      hr

def rk2.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +j: U32, +val: U32, hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hj: {IM.ix.offall(I, s, d, j) == True{} : Bool}, hr: {IM.ix.real(AD.view(U32, w), d, s, I) == True{} : Bool}, m: LAT.Mirror(U32, w)) ->
  {IM.ix.real(AD.view(U32, KMd.words(P.wr(P.H{KM.MG{w}, a}, j, val))), d, s, I) == True{} : Bool}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e)
  %e : {IM.ix.real(AD.view(U32, KMd.words(P.wr(P.H{KM.MG{_}, a}, j, val))), d, s, I) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t0), j, val)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot(j, d), val), LA.set_view(U32, LAT.fromT(U32, t0), d, j, val, hft, hd32)) : {IM.ix.real(_, d, s, I) == True{} : Bool}
  rk2.k(I, AD.view(U32, LAT.fromT(U32, t0)), d, s, j, val, hj, LAB.subst(Array<U32>, q => {IM.ix.real(AD.view(U32, q), d, s, I) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hr))

def Laws.real_kept(w, a, d, s, I, j, val, hf, hd32, hj, hr):
  rk2.m(w, a, d, s, I, j, val, hf, hd32, hj, hr, LAT.mirror(U32, w))

# The branches in a list after a put and a removal
# ================================================

def join_bsub(+sd: Bool, +U: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +N: List<&2, U32>, +hU: {RG.sub(IM.tr.branches(U), N) == True{} : Bool}, +hb: {RG.has(N, b) == True{} : Bool}) ->
  {RG.sub(IM.tr.branches(IM.tr.join(sd, U, x, k, b, c)), N) == True{} : Bool}:
  match sd:
    case True{}:
      and_intro(RG.has(N, b), RG.sub(List.append(&2, U32, IM.tr.branches(U), []), N), hb, sub_app(IM.tr.branches(U), [], N, hU, {==}))
    case False{}:
      and_intro(RG.has(N, b), RG.sub(List.append(&2, U32, [], IM.tr.branches(U)), N), hb, hU)

def pbs.k(+lt: Bool, +sd: Bool, +b2: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +N: List<&2, U32>,
  +h: {RG.sub(IM.tr.branches(IM.Br{b2, i, l, r}), N) == True{} : Bool}, +hb: {RG.has(N, b) == True{} : Bool},
  +ihl: {RG.sub(IM.tr.branches(IM.tr.place(l, x, k, b, c)), N) == True{} : Bool}, +ihr: {RG.sub(IM.tr.branches(IM.tr.place(r, x, k, b, c)), N) == True{} : Bool}) ->
  {RG.sub(IM.tr.branches(IM.tr.place.k(lt, sd, b2, i, l, r, IM.tr.place(l, x, k, b, c), IM.tr.place(r, x, k, b, c), x, k, b, c)), N) == True{} : Bool}:
  match lt:
    case False{}:
      join_bsub(X.ix.side(k, c), IM.Br{b2, i, l, r}, x, k, b, c, N, h, hb)
    case True{}:
      match sd:
        case True{}:
          +hb2 = and_l(RG.has(N, b2), RG.sub(List.append(&2, U32, IM.tr.branches(l), IM.tr.branches(r)), N), h)
          +hlr = and_r(RG.has(N, b2), RG.sub(List.append(&2, U32, IM.tr.branches(l), IM.tr.branches(r)), N), h)
          and_intro(RG.has(N, b2), RG.sub(List.append(&2, U32, IM.tr.branches(l), IM.tr.branches(IM.tr.place(r, x, k, b, c))), N), hb2, sub_app(IM.tr.branches(l), IM.tr.branches(IM.tr.place(r, x, k, b, c)), N, sub_app_l(IM.tr.branches(l), IM.tr.branches(r), N, hlr), ihr))
        case False{}:
          +hb2 = and_l(RG.has(N, b2), RG.sub(List.append(&2, U32, IM.tr.branches(l), IM.tr.branches(r)), N), h)
          +hlr = and_r(RG.has(N, b2), RG.sub(List.append(&2, U32, IM.tr.branches(l), IM.tr.branches(r)), N), h)
          and_intro(RG.has(N, b2), RG.sub(List.append(&2, U32, IM.tr.branches(IM.tr.place(l, x, k, b, c)), IM.tr.branches(r)), N), hb2, sub_app(IM.tr.branches(IM.tr.place(l, x, k, b, c)), IM.tr.branches(r), N, ihl, sub_app_r(IM.tr.branches(l), IM.tr.branches(r), N, hlr)))

def place_bsub(t: IM.Tr, +x: U32, +k: U32, +b: U32, +c: Nat, +N: List<&2, U32>, +h: {RG.sub(IM.tr.branches(t), N) == True{} : Bool}, +hb: {RG.has(N, b) == True{} : Bool}) -> {RG.sub(IM.tr.branches(IM.tr.place(t, x, k, b, c)), N) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      join_bsub(X.ix.side(k, c), IM.Lf{y, ky}, x, k, b, c, N, h, hb)
    case IM.Br{+b2, +i, +l, +r}:
      +hlr = and_r(RG.has(N, b2), RG.sub(List.append(&2, U32, IM.tr.branches(l), IM.tr.branches(r)), N), h)
      pbs.k(Nat.is_lt(i, c), X.ix.side(k, i), b2, i, l, r, x, k, b, c, N, h, hb,
        place_bsub(l, x, k, b, c, N, sub_app_l(IM.tr.branches(l), IM.tr.branches(r), N, hlr), hb), place_bsub(r, x, k, b, c, N, sub_app_r(IM.tr.branches(l), IM.tr.branches(r), N, hlr), hb))

def put_bsub.k(I: IM.Ix, +x: U32, +k: U32, +b: U32, +N: List<&2, U32>, +h: {RG.sub(IM.ix.branches(I), N) == True{} : Bool}, +hb: {RG.has(N, b) == True{} : Bool}) ->
  {RG.sub(IM.ix.branches(IM.ix.put(I, x, k, b)), N) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      {==}
    case IM.Has{+t}:
      place_bsub(t, x, k, b, IM.cr.i(X.ix.diff(k, IM.tr.near(t, k))), N, h, hb)

def cbs.r(+hit: Bool, +b: U32, +i: Nat, +l: IM.Tr, +cr: IM.Tr, +N: List<&2, U32>, +hb: {RG.has(N, b) == True{} : Bool}, +hl: {RG.sub(IM.tr.branches(l), N) == True{} : Bool}, +hcr: {RG.sub(IM.tr.branches(cr), N) == True{} : Bool}) ->
  {RG.sub(IM.tr.branches(IM.tr.cut.r(hit, b, i, l, cr)), N) == True{} : Bool}:
  match hit:
    case True{}:
      hl
    case False{}:
      and_intro(RG.has(N, b), RG.sub(List.append(&2, U32, IM.tr.branches(l), IM.tr.branches(cr)), N), hb, sub_app(IM.tr.branches(l), IM.tr.branches(cr), N, hl, hcr))

def cbs.l(+hit: Bool, +b: U32, +i: Nat, +r: IM.Tr, +cl: IM.Tr, +N: List<&2, U32>, +hb: {RG.has(N, b) == True{} : Bool}, +hr: {RG.sub(IM.tr.branches(r), N) == True{} : Bool}, +hcl: {RG.sub(IM.tr.branches(cl), N) == True{} : Bool}) ->
  {RG.sub(IM.tr.branches(IM.tr.cut.l(hit, b, i, r, cl)), N) == True{} : Bool}:
  match hit:
    case True{}:
      hr
    case False{}:
      and_intro(RG.has(N, b), RG.sub(List.append(&2, U32, IM.tr.branches(cl), IM.tr.branches(r)), N), hb, sub_app(IM.tr.branches(cl), IM.tr.branches(r), N, hcl, hr))

def cbs.k(+sd: Bool, +b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr, +x: U32, +cl: IM.Tr, +cr: IM.Tr, +N: List<&2, U32>, +hb: {RG.has(N, b) == True{} : Bool},
  +hl: {RG.sub(IM.tr.branches(l), N) == True{} : Bool}, +hr: {RG.sub(IM.tr.branches(r), N) == True{} : Bool}, +hcl: {RG.sub(IM.tr.branches(cl), N) == True{} : Bool}, +hcr: {RG.sub(IM.tr.branches(cr), N) == True{} : Bool}) ->
  {RG.sub(IM.tr.branches(IM.tr.cut.k(sd, b, i, l, r, x, cl, cr)), N) == True{} : Bool}:
  match sd:
    case True{}:
      cbs.r(U32.is_eq(IM.tr.addr(r), x), b, i, l, cr, N, hb, hl, hcr)
    case False{}:
      cbs.l(U32.is_eq(IM.tr.addr(l), x), b, i, r, cl, N, hb, hr, hcl)

def cut_bsub(t: IM.Tr, +x: U32, +k: U32, +N: List<&2, U32>, +h: {RG.sub(IM.tr.branches(t), N) == True{} : Bool}) -> {RG.sub(IM.tr.branches(IM.tr.cut(t, x, k)), N) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      h
    case IM.Br{+b, +i, +l, +r}:
      +hlr = and_r(RG.has(N, b), RG.sub(List.append(&2, U32, IM.tr.branches(l), IM.tr.branches(r)), N), h)
      +hl = sub_app_l(IM.tr.branches(l), IM.tr.branches(r), N, hlr)
      +hr = sub_app_r(IM.tr.branches(l), IM.tr.branches(r), N, hlr)
      cbs.k(X.ix.side(k, i), b, i, l, r, x, IM.tr.cut(l, x, k), IM.tr.cut(r, x, k), N, and_l(RG.has(N, b), RG.sub(List.append(&2, U32, IM.tr.branches(l), IM.tr.branches(r)), N), h), hl, hr,
        cut_bsub(l, x, k, N, hl), cut_bsub(r, x, k, N, hr))

def del_bsub.h(+only: Bool, +t: IM.Tr, +x: U32, +k: U32, +N: List<&2, U32>, +h: {RG.sub(IM.tr.branches(t), N) == True{} : Bool}) -> {RG.sub(IM.ix.branches(IM.ix.del.k(only, t, x, k)), N) == True{} : Bool}:
  match only:
    case True{}:
      {==}
    case False{}:
      cut_bsub(t, x, k, N, h)

def del_bsub.k(I: IM.Ix, +x: U32, +k: U32, +N: List<&2, U32>, +h: {RG.sub(IM.ix.branches(I), N) == True{} : Bool}) -> {RG.sub(IM.ix.branches(IM.ix.del(I, x, k)), N) == True{} : Bool}:
  match I:
    case IM.Ept{}:
      {==}
    case IM.Has{+t}:
      del_bsub.h(U32.is_eq(IM.tr.addr(t), x), t, x, k, N, h)

def Laws.put_bsub(I, x, k, b, N, h, hb):
  put_bsub.k(I, x, k, b, N, h, hb)

def Laws.del_bsub(I, x, k, N, h):
  del_bsub.k(I, x, k, N, h)
