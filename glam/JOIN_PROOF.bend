# The proof of a join's link over the facing (glam/JOIN_LAWS.bend;
# cells-freeze.sharing.cursors.index.ring.inv). A live node z's word 1
# after the link: the port x faced where y faced z, else the port y faced
# where x faced z, else as before (word_lk); each clause after then
# follows, case by case, from the two-way and none-itself facts before
# and from no port's link word lying in two tracked nodes' words 1 (no2),
# by four propositional lemmas whose case trees an authoring aid writes.
# Generated: glam/proofgen/regen.sh writes this file, link_live's proof
# by gen_link.py and gen_link2.py, link_leave's by gen_lvlink.py
# (generated-outputs-checked-in; glam/proofgen/README.md).

import Base
import ./JOIN_LAWS.bend as Laws
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ./ring_model.bend as RG
import ../spike/kmodel.bend as KMd
import ./INDEX_LAWS.bend as XL
import ./INDEX_PROOF.bend as XP
import ./index_model.bend as IMd
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import ../vendor/bend-mathlib/u32_eq.bend as MS
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MN
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/LAWS.bend as LA
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/PROOF.bend as LAP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_base.bend as LAB
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD

def and_intro(+p: Bool, +q: Bool, +hp: {p == True{} : Bool}, +hq: {q == True{} : Bool}) -> {Bool.and(p, q) == True{} : Bool}:
  XP.and_intro(p, q, hp, hq)

def and_l(+a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  XP.and_l(a, b, h)

def and_r(+a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  XP.and_r(a, b, h)

def not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  XP.not_true(b, h)

def ort_r(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +h: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  XP.ort_r(a, b, ha, h)

def ueq_ne(+a: U32, +b: U32, +h: {U32.is_eq(a, b) == False{} : Bool}) -> {U32.is_eq(b, a) == False{} : Bool}:
  XP.ueq_comm_f(a, b, h)

def sel(+c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

def sel3(+B: Bool, +A: Bool, +pf: Bool, +pw: Bool, +pu: Bool) -> Bool:
  match B:
    case False{}:
      pu
    case True{}:
      match A:
        case False{}:
          pw
        case True{}:
          pf

# a write of a port's link word, none for a static
def lk(+st: Bool, A: Array<U32>, +r: U32, +val: U32) -> Array<U32>:
  match st:
    case True{}:
      A
    case False{}:
      Array.set(U32, A, (r + 1 : U32), val)

def lt_eq(+st: Bool, -A: Array<U32>, -a: Array<V.Val>, +r: U32, +val: U32) -> {P.link.to(st, P.H{KM.MG{A}, a}, r, val) == P.H{KM.MG{lk(st, A, r, val)}, a} : P.H}:
  match st:
    case True{}:
      {==}
    case False{}:
      {==}

def lk_full(+st: Bool, A: Array<U32>, +d: Nat, +r: U32, +val: U32, hf: {AD.full(U32, A, d) == True{} : Bool}) -> {AD.full(U32, lk(st, A, r, val), d) == True{} : Bool}:
  match st:
    case True{}:
      hf
    case False{}:
      LA.set_full(U32, A, d, (r + 1 : U32), val, hf)

def nhas.k(+e: Bool, +L: List<&2, U32>, +z: U32, +x: U32, +he: {U32.is_eq(z, x) == e : Bool}, +hz: {RG.has(L, z) == True{} : Bool}, +hx: {RG.has(L, x) == False{} : Bool}) ->
  {U32.is_eq(z, x) == False{} : Bool}:
  match e:
    case True{}:
      Empty.absurd({U32.is_eq(z, x) == False{} : Bool}, MB.true_ne_false()(Equal.trans(Bool, True{}, RG.has(L, x), False{},
        Equal.sym(Bool, RG.has(L, x), True{}, ME.subst(U32, q => {RG.has(L, q) == True{} : Bool}, z, x, MS.u32_eq_of_is_eq(z, x, he), hz)), hx)))
    case False{}:
      he

def nhas(+L: List<&2, U32>, +z: U32, +x: U32, +hz: {RG.has(L, z) == True{} : Bool}, +hx: {RG.has(L, x) == False{} : Bool}) -> {U32.is_eq(z, x) == False{} : Bool}:
  nhas.k(U32.is_eq(z, x), L, z, x, {==}, hz, hx)

def wlk.e(+e: Bool, +v: List<&2, U32>, +d: Nat, +r: U32, +val: U32, +i: U32, +he: {Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(i, d)) == e : Bool},
  +hs: {XP.is_some(List.get(&2, U32, v, AD.slot((r + 1 : U32), d))) == True{} : Bool}) ->
  {KMd.word(List.set(&2, U32, v, AD.slot((r + 1 : U32), d), val), d, i) == sel(Bool.not(e), KMd.word(v, d, i), val) : U32}:
  match e:
    case True{}:
      %MN.eq_of_is_eq(AD.slot((r + 1 : U32), d), AD.slot(i, d), he) : {KMd.word.m(List.get(&2, U32, List.set(&2, U32, v, AD.slot((r + 1 : U32), d), val), _)) == val : U32}
      XP.wl_eq2(v, d, (r + 1 : U32), val, hs)
    case False{}:
      Equal.sym(U32, KMd.word(v, d, i), KMd.word(List.set(&2, U32, v, AD.slot((r + 1 : U32), d), val), d, i), XP.wl_ne(v, d, (r + 1 : U32), i, val, he))

# a word after a link's write: the value where the port's link word is it
def word_lk(+st: Bool, +t: LAT.Tree<U32>, +d: Nat, +r: U32, +val: U32, +i: U32, +hst: {P.is_static(r) == st : Bool},
  +hf: {AD.full(U32, LAT.fromT(U32, t), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
  {KMd.word(AD.view(U32, lk(st, LAT.fromT(U32, t), r, val)), d, i) == sel(KMd.off.port(d, r, i), KMd.word(AD.view(U32, LAT.fromT(U32, t)), d, i), val) : U32}:
  match st:
    case True{}:
      %Equal.sym(Bool, P.is_static(r), True{}, hst) : {KMd.word(AD.view(U32, lk(True{}, LAT.fromT(U32, t), r, val)), d, i) == sel(KMd.off.lw(KMd.lw.k(_, r), d, i), KMd.word(AD.view(U32, LAT.fromT(U32, t)), d, i), val) : U32}
      {==}
    case False{}:
      %Equal.sym(Bool, P.is_static(r), False{}, hst) : {KMd.word(AD.view(U32, lk(False{}, LAT.fromT(U32, t), r, val)), d, i) == sel(KMd.off.lw(KMd.lw.k(_, r), d, i), KMd.word(AD.view(U32, LAT.fromT(U32, t)), d, i), val) : U32}
      %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (r + 1 : U32), val)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((r + 1 : U32), d), val),
        LA.set_view(U32, LAT.fromT(U32, t), d, (r + 1 : U32), val, hf, hd32)) : {KMd.word(_, d, i) == sel(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(i, d))), KMd.word(AD.view(U32, LAT.fromT(U32, t)), d, i), val) : U32}
      wlk.e(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(i, d)), AD.view(U32, LAT.fromT(U32, t)), d, r, val, i, {==},
        ME.subst(Maybe<&2, U32>, m => {XP.is_some(m) == True{} : Bool}, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (r + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot((r + 1 : U32), d)),
          LA.get_view(U32, LAT.fromT(U32, t), d, (r + 1 : U32), hf, hd32), {==}))

def op_sel(+B: Bool, +A: Bool, +f: U32, +w: U32, +u: U32, +d: Nat, +j: U32) -> {KMd.off.port(d, sel(B, sel(A, f, w), u), j) == sel3(B, A, KMd.off.port(d, f, j), KMd.off.port(d, w, j), KMd.off.port(d, u, j)) : Bool}:
  match B:
    case True{}:
      match A:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

# no port's link word in two tracked nodes' words 1
def no2.e(+e1: Bool, +e2: Bool, +a: U32, +b: U32, +r: U32, +d: Nat, +he1: {Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((a + 1 : U32), d)) == e1 : Bool},
  +he2: {Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((b + 1 : U32), d)) == e2 : Bool}, +hab: {Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d)) == False{} : Bool}) ->
  {Bool.or(Bool.not(e1), Bool.not(e2)) == True{} : Bool}:
  match e1:
    case False{}:
      {==}
    case True{}:
      match e2:
        case False{}:
          {==}
        case True{}:
          Empty.absurd({Bool.or(Bool.not(True{}), Bool.not(True{})) == True{} : Bool}, MB.false_ne_true()(Equal.trans(Bool, False{}, Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d)), True{},
            Equal.sym(Bool, Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d)), False{}, hab),
            ME.subst(Nat, q => {Nat.is_eq(q, AD.slot((a + 1 : U32), d)) == True{} : Bool}, AD.slot((a + 1 : U32), d), AD.slot((b + 1 : U32), d),
              Equal.trans(Nat, AD.slot((a + 1 : U32), d), AD.slot((r + 1 : U32), d), AD.slot((b + 1 : U32), d),
                Equal.sym(Nat, AD.slot((r + 1 : U32), d), AD.slot((a + 1 : U32), d), MN.eq_of_is_eq(AD.slot((r + 1 : U32), d), AD.slot((a + 1 : U32), d), he1)),
                MN.eq_of_is_eq(AD.slot((r + 1 : U32), d), AD.slot((b + 1 : U32), d), he2)),
              MN.is_eq_refl(AD.slot((a + 1 : U32), d))))))

def no2.k(+st: Bool, +r: U32, +a: U32, +b: U32, +d: Nat, +hst: {P.is_static(r) == st : Bool}, +hab: {Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d)) == False{} : Bool}) ->
  {Bool.or(KMd.off.port(d, r, (a + 1 : U32)), KMd.off.port(d, r, (b + 1 : U32))) == True{} : Bool}:
  match st:
    case True{}:
      %Equal.sym(Bool, P.is_static(r), True{}, hst) : {Bool.or(KMd.off.lw(KMd.lw.k(_, r), d, (a + 1 : U32)), KMd.off.lw(KMd.lw.k(_, r), d, (b + 1 : U32))) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, P.is_static(r), False{}, hst) : {Bool.or(KMd.off.lw(KMd.lw.k(_, r), d, (a + 1 : U32)), KMd.off.lw(KMd.lw.k(_, r), d, (b + 1 : U32))) == True{} : Bool}
      no2.e(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((a + 1 : U32), d)), Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((b + 1 : U32), d)), a, b, r, d, {==}, {==}, hab)

def no2(+r: U32, +a: U32, +b: U32, +d: Nat, +N: List<&2, U32>, +hN: {RG.layout(N, d) == True{} : Bool}, +ha: {RG.has(N, a) == True{} : Bool}, +hb: {RG.has(N, b) == True{} : Bool}, +hne: {U32.is_eq(a, b) == False{} : Bool}) ->
  {Bool.or(KMd.off.port(d, r, (a + 1 : U32)), KMd.off.port(d, r, (b + 1 : U32))) == True{} : Bool}:
  no2.k(P.is_static(r), r, a, b, d, {==}, not_true(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d)),
    and_l(Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d))) && True{}), and_r(Bool.not(Nat.is_eq(AD.slot(b, d), AD.slot((a + 1 : U32), d))), Bool.not(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 2 : U32), d), AD.slot((a + 1 : U32), d))) && (Bool.not(Nat.is_eq(AD.slot((b + 3 : U32), d), AD.slot((a + 1 : U32), d))) && True{})), and_l(KMd.off.words(KMd.nw(b), d, (a + 1 : U32)), KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32)), and_r(KMd.off.words(KMd.nw(b), d, a), KMd.off.words(KMd.nw(b), d, (a + 1 : U32)) && (KMd.off.words(KMd.nw(b), d, (a + 2 : U32)) && KMd.off.words(KMd.nw(b), d, (a + 3 : U32))), and_l(IMd.nd.disj(d, a, b), IMd.nd.disj(d, b, a), XL.layout_sep(N, d, a, b, hN, ha, hb, hne))))))))

# what a member of L had before the link
def fm_word(m: Maybe<&2, U32>, +d: Nat, +M: List<&2, U32>, +h: {RG.faces.m(m, d, M) == True{} : Bool}) -> {RG.port.ok(M, d, KMd.word.m(m)) == True{} : Bool}:
  match m:
    case Some{+r}:
      h
    case None{}:
      Empty.absurd({RG.port.ok(M, d, KMd.word.m(None{})) == True{} : Bool}, MB.false_ne_true()(h))

def fm_of_word(m: Maybe<&2, U32>, +d: Nat, +M: List<&2, U32>, +hs: {XP.is_some(m) == True{} : Bool}, +h: {RG.port.ok(M, d, KMd.word.m(m)) == True{} : Bool}) -> {RG.faces.m(m, d, M) == True{} : Bool}:
  match m:
    case Some{+r}:
      h
    case None{}:
      Empty.absurd({RG.faces.m(None{}, d, M) == True{} : Bool}, MB.false_ne_true()(hs))

def fm_of.k(+e: Bool, +y: U32, +t: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +M: List<&2, U32>, +z: U32, +he: {U32.is_eq(y, z) == e : Bool}, +h: {RG.faces(Con{y, t}, v, d, M) == True{} : Bool},
  +hz: {Bool.or(U32.is_eq(y, z), RG.has(t, z)) == True{} : Bool}, ih: {RG.has(t, z) == True{} : Bool} -> {RG.faces.m(List.get(&2, U32, v, AD.slot((z + 1 : U32), d)), d, M) == True{} : Bool}) -> {RG.faces.m(List.get(&2, U32, v, AD.slot((z + 1 : U32), d)), d, M) == True{} : Bool}:
  match e:
    case True{}:
      %MS.u32_eq_of_is_eq(y, z, he) : {RG.faces.m(List.get(&2, U32, v, AD.slot((_ + 1 : U32), d)), d, M) == True{} : Bool}
      and_l(RG.faces.m(List.get(&2, U32, v, AD.slot((y + 1 : U32), d)), d, M), RG.faces(t, v, d, M), h)
    case False{}:
      ih(ort_r(U32.is_eq(y, z), RG.has(t, z), he, hz))

def fm_of(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +M: List<&2, U32>, +z: U32, +h: {RG.faces(ys, v, d, M) == True{} : Bool}, +hz: {RG.has(ys, z) == True{} : Bool}) -> {RG.faces.m(List.get(&2, U32, v, AD.slot((z + 1 : U32), d)), d, M) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({RG.faces.m(List.get(&2, U32, v, AD.slot((z + 1 : U32), d)), d, M) == True{} : Bool}, MB.false_ne_true()(hz))
    case Con{+y, +t}:
      fm_of.k(U32.is_eq(y, z), y, t, v, d, M, z, {==}, h, hz, hzt => fm_of(t, v, d, M, z, and_r(RG.faces.m(List.get(&2, U32, v, AD.slot((y + 1 : U32), d)), d, M), RG.faces(t, v, d, M), h), hzt))

def po_of.k(+e: Bool, +y: U32, +t: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +L: List<&2, U32>, +N: List<&2, U32>, +z: U32, +he: {U32.is_eq(y, z) == e : Bool}, +h: {RG.px.off(Con{y, t}, v, d, L, N) == True{} : Bool},
  +hz: {Bool.or(U32.is_eq(y, z), RG.has(t, z)) == True{} : Bool}, ih: {RG.has(t, z) == True{} : Bool} -> {RG.po.all(KMd.word(v, d, (z + 1 : U32)), L, d, N) == True{} : Bool}) -> {RG.po.all(KMd.word(v, d, (z + 1 : U32)), L, d, N) == True{} : Bool}:
  match e:
    case True{}:
      %MS.u32_eq_of_is_eq(y, z, he) : {RG.po.all(KMd.word(v, d, (_ + 1 : U32)), L, d, N) == True{} : Bool}
      and_l(RG.po.all(KMd.word(v, d, (y + 1 : U32)), L, d, N), RG.px.off(t, v, d, L, N), h)
    case False{}:
      ih(ort_r(U32.is_eq(y, z), RG.has(t, z), he, hz))

def po_of(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +L: List<&2, U32>, +N: List<&2, U32>, +z: U32, +h: {RG.px.off(ys, v, d, L, N) == True{} : Bool}, +hz: {RG.has(ys, z) == True{} : Bool}) -> {RG.po.all(KMd.word(v, d, (z + 1 : U32)), L, d, N) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({RG.po.all(KMd.word(v, d, (z + 1 : U32)), L, d, N) == True{} : Bool}, MB.false_ne_true()(hz))
    case Con{+y, +t}:
      po_of.k(U32.is_eq(y, z), y, t, v, d, L, N, z, {==}, h, hz, hzt => po_of(t, v, d, L, N, z, and_r(RG.po.all(KMd.word(v, d, (y + 1 : U32)), L, d, N), RG.px.off(t, v, d, L, N), h), hzt))

def ns_of.k(+e: Bool, +y: U32, +t: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +L: List<&2, U32>, +z: U32, +he: {U32.is_eq(y, z) == e : Bool}, +h: {RG.px.tw(Con{y, t}, v, d, L) == True{} : Bool},
  +hz: {Bool.or(U32.is_eq(y, z), RG.has(t, z)) == True{} : Bool}, ih: {RG.has(t, z) == True{} : Bool} -> {KMd.off.port(d, KMd.word(v, d, (z + 1 : U32)), (z + 1 : U32)) && RG.tw.q(L, KMd.word(v, d, (z + 1 : U32)), z, v, d) == True{} : Bool}) -> {KMd.off.port(d, KMd.word(v, d, (z + 1 : U32)), (z + 1 : U32)) && RG.tw.q(L, KMd.word(v, d, (z + 1 : U32)), z, v, d) == True{} : Bool}:
  match e:
    case True{}:
      %MS.u32_eq_of_is_eq(y, z, he) : {KMd.off.port(d, KMd.word(v, d, (_ + 1 : U32)), (_ + 1 : U32)) && RG.tw.q(L, KMd.word(v, d, (_ + 1 : U32)), _, v, d) == True{} : Bool}
      and_intro(KMd.off.port(d, KMd.word(v, d, (y + 1 : U32)), (y + 1 : U32)), RG.tw.q(L, KMd.word(v, d, (y + 1 : U32)), y, v, d), and_l(KMd.off.port(d, KMd.word(v, d, (y + 1 : U32)), (y + 1 : U32)), RG.tw.q(L, KMd.word(v, d, (y + 1 : U32)), y, v, d) && RG.px.tw(t, v, d, L), h), and_l(RG.tw.q(L, KMd.word(v, d, (y + 1 : U32)), y, v, d), RG.px.tw(t, v, d, L), and_r(KMd.off.port(d, KMd.word(v, d, (y + 1 : U32)), (y + 1 : U32)), RG.tw.q(L, KMd.word(v, d, (y + 1 : U32)), y, v, d) && RG.px.tw(t, v, d, L), h)))
    case False{}:
      ih(ort_r(U32.is_eq(y, z), RG.has(t, z), he, hz))

def ns_of(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +L: List<&2, U32>, +z: U32, +h: {RG.px.tw(ys, v, d, L) == True{} : Bool}, +hz: {RG.has(ys, z) == True{} : Bool}) -> {KMd.off.port(d, KMd.word(v, d, (z + 1 : U32)), (z + 1 : U32)) && RG.tw.q(L, KMd.word(v, d, (z + 1 : U32)), z, v, d) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({KMd.off.port(d, KMd.word(v, d, (z + 1 : U32)), (z + 1 : U32)) && RG.tw.q(L, KMd.word(v, d, (z + 1 : U32)), z, v, d) == True{} : Bool}, MB.false_ne_true()(hz))
    case Con{+y, +t}:
      ns_of.k(U32.is_eq(y, z), y, t, v, d, L, z, {==}, h, hz, hzt => ns_of(t, v, d, L, z, and_r(RG.tw.q(L, KMd.word(v, d, (y + 1 : U32)), y, v, d), RG.px.tw(t, v, d, L), and_r(KMd.off.port(d, KMd.word(v, d, (y + 1 : U32)), (y + 1 : U32)), RG.tw.q(L, KMd.word(v, d, (y + 1 : U32)), y, v, d) && RG.px.tw(t, v, d, L), h)), hzt))

def tw_at.k(+e: Bool, +y: U32, +t: List<&2, U32>, +r: U32, +x: U32, +v: List<&2, U32>, +d: Nat, +z: U32, +he: {U32.is_eq(y, z) == e : Bool}, +h: {RG.tw.q(Con{y, t}, r, x, v, d) == True{} : Bool},
  +hz: {Bool.or(U32.is_eq(y, z), RG.has(t, z)) == True{} : Bool}, ih: {RG.has(t, z) == True{} : Bool} -> {Bool.or(KMd.off.port(d, r, (z + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, (z + 1 : U32)), (x + 1 : U32)))) == True{} : Bool}) -> {Bool.or(KMd.off.port(d, r, (z + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, (z + 1 : U32)), (x + 1 : U32)))) == True{} : Bool}:
  match e:
    case True{}:
      %MS.u32_eq_of_is_eq(y, z, he) : {Bool.or(KMd.off.port(d, r, (_ + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, (_ + 1 : U32)), (x + 1 : U32)))) == True{} : Bool}
      and_l(Bool.or(KMd.off.port(d, r, (y + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, (y + 1 : U32)), (x + 1 : U32)))), RG.tw.q(t, r, x, v, d), h)
    case False{}:
      ih(ort_r(U32.is_eq(y, z), RG.has(t, z), he, hz))

def tw_at(ys: List<&2, U32>, +r: U32, +x: U32, +v: List<&2, U32>, +d: Nat, +z: U32, +h: {RG.tw.q(ys, r, x, v, d) == True{} : Bool}, +hz: {RG.has(ys, z) == True{} : Bool}) -> {Bool.or(KMd.off.port(d, r, (z + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, (z + 1 : U32)), (x + 1 : U32)))) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({Bool.or(KMd.off.port(d, r, (z + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, (z + 1 : U32)), (x + 1 : U32)))) == True{} : Bool}, MB.false_ne_true()(hz))
    case Con{+y, +t}:
      tw_at.k(U32.is_eq(y, z), y, t, r, x, v, d, z, {==}, h, hz, hzt => tw_at(t, r, x, v, d, z, and_r(Bool.or(KMd.off.port(d, r, (y + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, (y + 1 : U32)), (x + 1 : U32)))), RG.tw.q(t, r, x, v, d), h), hzt))

def ol_at.k(+e: Bool, +y: U32, +t: List<&2, U32>, +d: Nat, +i: U32, +z: U32, +he: {U32.is_eq(y, z) == e : Bool}, +h: {RG.off.links(Con{y, t}, d, i) == True{} : Bool},
  +hz: {Bool.or(U32.is_eq(y, z), RG.has(t, z)) == True{} : Bool}, ih: {RG.has(t, z) == True{} : Bool} -> {Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((z + 3 : U32), d))) == True{} : Bool}) -> {Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((z + 3 : U32), d))) == True{} : Bool}:
  match e:
    case True{}:
      %MS.u32_eq_of_is_eq(y, z, he) : {Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((_ + 3 : U32), d))) == True{} : Bool}
      and_l(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((y + 3 : U32), d))), RG.off.links(t, d, i), h)
    case False{}:
      ih(ort_r(U32.is_eq(y, z), RG.has(t, z), he, hz))

def ol_at(ys: List<&2, U32>, +d: Nat, +i: U32, +z: U32, +h: {RG.off.links(ys, d, i) == True{} : Bool}, +hz: {RG.has(ys, z) == True{} : Bool}) -> {Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((z + 3 : U32), d))) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((z + 3 : U32), d))) == True{} : Bool}, MB.false_ne_true()(hz))
    case Con{+y, +t}:
      ol_at.k(U32.is_eq(y, z), y, t, d, i, z, {==}, h, hz, hzt => ol_at(t, d, i, z, and_r(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((y + 3 : U32), d))), RG.off.links(t, d, i), h), hzt))

def opos_at.k(+e: Bool, +y: U32, +t: List<&2, U32>, +d: Nat, +i: U32, +z: U32, +he: {U32.is_eq(y, z) == e : Bool}, +h: {RG.off.pos(Con{y, t}, d, i) == True{} : Bool},
  +hz: {Bool.or(U32.is_eq(y, z), RG.has(t, z)) == True{} : Bool}, ih: {RG.has(t, z) == True{} : Bool} -> {Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((z + 2 : U32), d))) == True{} : Bool}) -> {Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((z + 2 : U32), d))) == True{} : Bool}:
  match e:
    case True{}:
      %MS.u32_eq_of_is_eq(y, z, he) : {Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((_ + 2 : U32), d))) == True{} : Bool}
      and_l(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((y + 2 : U32), d))), RG.off.pos(t, d, i), h)
    case False{}:
      ih(ort_r(U32.is_eq(y, z), RG.has(t, z), he, hz))

def opos_at(ys: List<&2, U32>, +d: Nat, +i: U32, +z: U32, +h: {RG.off.pos(ys, d, i) == True{} : Bool}, +hz: {RG.has(ys, z) == True{} : Bool}) -> {Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((z + 2 : U32), d))) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((z + 2 : U32), d))) == True{} : Bool}, MB.false_ne_true()(hz))
    case Con{+y, +t}:
      opos_at.k(U32.is_eq(y, z), y, t, d, i, z, {==}, h, hz, hzt => opos_at(t, d, i, z, and_r(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((y + 2 : U32), d))), RG.off.pos(t, d, i), h), hzt))

def ol_sub(M2: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +i: U32, +hs: {RG.sub(M2, M) == True{} : Bool}, +h: {RG.off.links(M, d, i) == True{} : Bool}) -> {RG.off.links(M2, d, i) == True{} : Bool}:
  match M2:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      and_intro(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 3 : U32), d))), RG.off.links(t, d, i), ol_at(M, d, i, m, h, and_l(RG.has(M, m), RG.sub(t, M), hs)),
        ol_sub(t, M, d, i, and_r(RG.has(M, m), RG.sub(t, M), hs), h))

def opos_sub(M2: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +i: U32, +hs: {RG.sub(M2, M) == True{} : Bool}, +h: {RG.off.pos(M, d, i) == True{} : Bool}) -> {RG.off.pos(M2, d, i) == True{} : Bool}:
  match M2:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      and_intro(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 2 : U32), d))), RG.off.pos(t, d, i), opos_at(M, d, i, m, h, and_l(RG.has(M, m), RG.sub(t, M), hs)),
        opos_sub(t, M, d, i, and_r(RG.has(M, m), RG.sub(t, M), hs), h))

def pk_sub(+M2: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +r: U32, +hs: {RG.sub(M2, M) == True{} : Bool}, +h: {RG.port.ok(M, d, r) == True{} : Bool}) -> {RG.port.ok(M2, d, r) == True{} : Bool}:
  and_intro(RG.off.links(M2, d, (r + 1 : U32)), RG.off.pos(M2, d, (r + 1 : U32)), ol_sub(M2, M, d, (r + 1 : U32), hs, and_l(RG.off.links(M, d, (r + 1 : U32)), RG.off.pos(M, d, (r + 1 : U32)), h)),
    opos_sub(M2, M, d, (r + 1 : U32), hs, and_r(RG.off.links(M, d, (r + 1 : U32)), RG.off.pos(M, d, (r + 1 : U32)), h)))

def pk_sel(+B: Bool, +A: Bool, +f: U32, +w: U32, +u: U32, +d: Nat, +M: List<&2, U32>, +hf: {RG.port.ok(M, d, f) == True{} : Bool}, +hw: {RG.port.ok(M, d, w) == True{} : Bool}, +hu: {RG.port.ok(M, d, u) == True{} : Bool}) ->
  {RG.port.ok(M, d, sel(B, sel(A, f, w), u)) == True{} : Bool}:
  match B:
    case True{}:
      match A:
        case True{}:
          hf
        case False{}:
          hw
    case False{}:
      hu

def po_sel(+B: Bool, +A: Bool, +f: U32, +w: U32, +u: U32, +d: Nat, +L: List<&2, U32>, +N: List<&2, U32>, +hf: {RG.po.all(f, L, d, N) == True{} : Bool}, +hw: {RG.po.all(w, L, d, N) == True{} : Bool}, +hu: {RG.po.all(u, L, d, N) == True{} : Bool}) ->
  {RG.po.all(sel(B, sel(A, f, w), u), L, d, N) == True{} : Bool}:
  match B:
    case True{}:
      match A:
        case True{}:
          hf
        case False{}:
          hw
    case False{}:
      hu

def pk2.k(+st: Bool, +M: List<&2, U32>, +d: Nat, +r: U32, +m: U32, +hst: {P.is_static(r) == st : Bool}, +h: {RG.port.ok(M, d, r) == True{} : Bool}, +hm: {RG.has(M, m) == True{} : Bool}) -> {KMd.off.port(d, r, (m + 2 : U32)) == True{} : Bool}:
  match st:
    case True{}:
      %Equal.sym(Bool, P.is_static(r), True{}, hst) : {KMd.off.lw(KMd.lw.k(_, r), d, (m + 2 : U32)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, P.is_static(r), False{}, hst) : {KMd.off.lw(KMd.lw.k(_, r), d, (m + 2 : U32)) == True{} : Bool}
      opos_at(M, d, (r + 1 : U32), m, and_r(RG.off.links(M, d, (r + 1 : U32)), RG.off.pos(M, d, (r + 1 : U32)), h), hm)

def pk2(+M: List<&2, U32>, +d: Nat, +r: U32, +m: U32, +h: {RG.port.ok(M, d, r) == True{} : Bool}, +hm: {RG.has(M, m) == True{} : Bool}) -> {KMd.off.port(d, r, (m + 2 : U32)) == True{} : Bool}:
  pk2.k(P.is_static(r), M, d, r, m, {==}, h, hm)

def pk3.k(+st: Bool, +M: List<&2, U32>, +d: Nat, +r: U32, +m: U32, +hst: {P.is_static(r) == st : Bool}, +h: {RG.port.ok(M, d, r) == True{} : Bool}, +hm: {RG.has(M, m) == True{} : Bool}) -> {KMd.off.port(d, r, (m + 3 : U32)) == True{} : Bool}:
  match st:
    case True{}:
      %Equal.sym(Bool, P.is_static(r), True{}, hst) : {KMd.off.lw(KMd.lw.k(_, r), d, (m + 3 : U32)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, P.is_static(r), False{}, hst) : {KMd.off.lw(KMd.lw.k(_, r), d, (m + 3 : U32)) == True{} : Bool}
      ol_at(M, d, (r + 1 : U32), m, and_l(RG.off.links(M, d, (r + 1 : U32)), RG.off.pos(M, d, (r + 1 : U32)), h), hm)

def pk3(+M: List<&2, U32>, +d: Nat, +r: U32, +m: U32, +h: {RG.port.ok(M, d, r) == True{} : Bool}, +hm: {RG.has(M, m) == True{} : Bool}) -> {KMd.off.port(d, r, (m + 3 : U32)) == True{} : Bool}:
  pk3.k(P.is_static(r), M, d, r, m, {==}, h, hm)

def sh.k(+e: Bool, +m: U32, +t: List<&2, U32>, +C: List<&2, U32>, +a: U32, +he: {U32.is_eq(m, a) == e : Bool}, +hbc: {RG.sub(Con{m, t}, C) == True{} : Bool}, +hb: {Bool.or(U32.is_eq(m, a), RG.has(t, a)) == True{} : Bool},
  ih: {RG.has(t, a) == True{} : Bool} -> {RG.has(C, a) == True{} : Bool}) -> {RG.has(C, a) == True{} : Bool}:
  match e:
    case True{}:
      %MS.u32_eq_of_is_eq(m, a, he) : {RG.has(C, _) == True{} : Bool}
      and_l(RG.has(C, m), RG.sub(t, C), hbc)
    case False{}:
      ih(ort_r(U32.is_eq(m, a), RG.has(t, a), he, hb))

def sub_has2(B: List<&2, U32>, +C: List<&2, U32>, +a: U32, +hbc: {RG.sub(B, C) == True{} : Bool}, +hb: {RG.has(B, a) == True{} : Bool}) -> {RG.has(C, a) == True{} : Bool}:
  match B:
    case Nil{}:
      Empty.absurd({RG.has(C, a) == True{} : Bool}, MB.false_ne_true()(hb))
    case Con{+m, +t}:
      sh.k(U32.is_eq(m, a), m, t, C, a, {==}, hbc, hb, hta => sub_has2(t, C, a, and_r(RG.has(C, m), RG.sub(t, C), hbc), hta))

def or3_drop(+a: Bool, +b: Bool, +c: Bool, +hc: {c == False{} : Bool}, +h: {Bool.or(a, Bool.or(b, c)) == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          ME.subst(Bool, q => {q == True{} : Bool}, c, False{}, hc, h)

# r's link word off x's and y's words 1 to 3: po over L2 from po over L
def pn.x(+ex: Bool, +x: U32, +y: U32, +n: U32, +r: U32, +d: Nat, +hex: {U32.is_eq(x, n) == ex : Bool}, +hor: {Bool.or(U32.is_eq(x, n), U32.is_eq(y, n)) == True{} : Bool},
  +hwx: {KMd.off.port(d, r, (x + 1 : U32)) && (KMd.off.port(d, r, (x + 2 : U32)) && KMd.off.port(d, r, (x + 3 : U32))) == True{} : Bool}, +hwy: {KMd.off.port(d, r, (y + 1 : U32)) && (KMd.off.port(d, r, (y + 2 : U32)) && KMd.off.port(d, r, (y + 3 : U32))) == True{} : Bool}) -> {KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32))) == True{} : Bool}:
  match ex:
    case True{}:
      %MS.u32_eq_of_is_eq(x, n, hex) : {KMd.off.port(d, r, (_ + 1 : U32)) && (KMd.off.port(d, r, (_ + 2 : U32)) && KMd.off.port(d, r, (_ + 3 : U32))) == True{} : Bool}
      hwx
    case False{}:
      %MS.u32_eq_of_is_eq(y, n, ort_r(U32.is_eq(x, n), U32.is_eq(y, n), hex, hor)) : {KMd.off.port(d, r, (_ + 1 : U32)) && (KMd.off.port(d, r, (_ + 2 : U32)) && KMd.off.port(d, r, (_ + 3 : U32))) == True{} : Bool}
      hwy

def pn.k(+e2: Bool, +e1: Bool, +L: List<&2, U32>, +L2: List<&2, U32>, +x: U32, +y: U32, +n: U32, +r: U32, +d: Nat, +he2: {RG.has(L2, n) == e2 : Bool}, +he1: {RG.has(L, n) == e1 : Bool},
  +h: {Bool.or(RG.has(L, n), KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32)))) == True{} : Bool}, +hs2: {RG.sub(L, Con{x, Con{y, L2}}) == True{} : Bool}, +hwx: {KMd.off.port(d, r, (x + 1 : U32)) && (KMd.off.port(d, r, (x + 2 : U32)) && KMd.off.port(d, r, (x + 3 : U32))) == True{} : Bool}, +hwy: {KMd.off.port(d, r, (y + 1 : U32)) && (KMd.off.port(d, r, (y + 2 : U32)) && KMd.off.port(d, r, (y + 3 : U32))) == True{} : Bool}) -> {Bool.or(RG.has(L2, n), KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32)))) == True{} : Bool}:
  match e2:
    case True{}:
      %Equal.sym(Bool, RG.has(L2, n), True{}, he2) : {Bool.or(_, KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32)))) == True{} : Bool}
      {==}
    case False{}:
      match e1:
        case False{}:
          %Equal.sym(Bool, RG.has(L2, n), False{}, he2) : {Bool.or(_, KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32)))) == True{} : Bool}
          ME.subst(Bool, q => {Bool.or(q, KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32)))) == True{} : Bool}, RG.has(L, n), False{}, he1, h)
        case True{}:
          +hn = sub_has2(L, Con{x, Con{y, L2}}, n, hs2, he1)
          %Equal.sym(Bool, RG.has(L2, n), False{}, he2) : {Bool.or(_, KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32)))) == True{} : Bool}
          pn.x(U32.is_eq(x, n), x, y, n, r, d, {==}, or3_drop(U32.is_eq(x, n), U32.is_eq(y, n), RG.has(L2, n), he2, hn), hwx, hwy)

def po_shrink(N: List<&2, U32>, +r: U32, +L: List<&2, U32>, +L2: List<&2, U32>, +x: U32, +y: U32, +d: Nat, +h: {RG.po.all(r, L, d, N) == True{} : Bool}, +hs2: {RG.sub(L, Con{x, Con{y, L2}}) == True{} : Bool},
  +hwx: {KMd.off.port(d, r, (x + 1 : U32)) && (KMd.off.port(d, r, (x + 2 : U32)) && KMd.off.port(d, r, (x + 3 : U32))) == True{} : Bool}, +hwy: {KMd.off.port(d, r, (y + 1 : U32)) && (KMd.off.port(d, r, (y + 2 : U32)) && KMd.off.port(d, r, (y + 3 : U32))) == True{} : Bool}) -> {RG.po.all(r, L2, d, N) == True{} : Bool}:
  match N:
    case Nil{}:
      h
    case Con{+n, +t}:
      and_intro(RG.po.n(r, L2, d, n), RG.po.all(r, L2, d, t),
        and_intro(KMd.off.port(d, r, n), Bool.or(RG.has(L2, n), KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32)))), and_l(KMd.off.port(d, r, n), Bool.or(RG.has(L, n), KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32)))), and_l(RG.po.n(r, L, d, n), RG.po.all(r, L, d, t), h)),
          pn.k(RG.has(L2, n), RG.has(L, n), L, L2, x, y, n, r, d, {==}, {==}, and_r(KMd.off.port(d, r, n), Bool.or(RG.has(L, n), KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32)))), and_l(RG.po.n(r, L, d, n), RG.po.all(r, L, d, t), h)), hs2, hwx, hwy)),
        po_shrink(t, r, L, L2, x, y, d, and_r(RG.po.n(r, L, d, n), RG.po.all(r, L, d, t), h), hs2, hwx, hwy))

def g2x(+bz: Bool, +az: Bool, +pfx: Bool, +pfy: Bool, +pwx: Bool, +puy: Bool, +pux: Bool, +pwy: Bool, +pfz: Bool, +nsx: {pux == True{} : Bool}, +nsy: {pwy == True{} : Bool}, +nsz: {pfz == True{} : Bool}, +tzx: {Bool.or(pfx, Bool.not(az)) == True{} : Bool}, +tzy: {Bool.or(pfy, Bool.not(bz)) == True{} : Bool}, +txz: {Bool.or(az, Bool.not(pfx)) == True{} : Bool}, +tyz: {Bool.or(bz, Bool.not(pfy)) == True{} : Bool}, +txy: {Bool.or(puy, Bool.not(pwx)) == True{} : Bool}, +tyx: {Bool.or(pwx, Bool.not(puy)) == True{} : Bool}, +o_uyz: {Bool.or(puy, az) == True{} : Bool}, +o_wxz: {Bool.or(pwx, bz) == True{} : Bool}, +o_fxy: {Bool.or(pfx, pfy) == True{} : Bool}) -> {sel3(bz, az, pfx, pwx, pux) == True{} : Bool}:
  match bz:
    case True{}:
      match az:
        case True{}:
          match pfx:
            case True{}:
              {==}
            case False{}:
              Empty.absurd({sel3(True{}, True{}, False{}, pwx, pux) == True{} : Bool}, MB.false_ne_true()(tzx))
        case False{}:
          match pfx:
            case True{}:
              Empty.absurd({sel3(True{}, False{}, True{}, pwx, pux) == True{} : Bool}, MB.false_ne_true()(txz))
            case False{}:
              match pfy:
                case True{}:
                  match pwx:
                    case True{}:
                      {==}
                    case False{}:
                      match puy:
                        case True{}:
                          Empty.absurd({sel3(True{}, False{}, False{}, False{}, pux) == True{} : Bool}, MB.false_ne_true()(tyx))
                        case False{}:
                          Empty.absurd({sel3(True{}, False{}, False{}, False{}, pux) == True{} : Bool}, MB.false_ne_true()(o_uyz))
                case False{}:
                  Empty.absurd({sel3(True{}, False{}, False{}, pwx, pux) == True{} : Bool}, MB.false_ne_true()(tzy))
    case False{}:
      match az:
        case True{}:
          match pfx:
            case True{}:
              match pfy:
                case True{}:
                  Empty.absurd({sel3(False{}, True{}, True{}, pwx, pux) == True{} : Bool}, MB.false_ne_true()(tyz))
                case False{}:
                  match pwx:
                    case True{}:
                      match puy:
                        case True{}:
                          match pux:
                            case True{}:
                              {==}
                            case False{}:
                              Empty.absurd({sel3(False{}, True{}, True{}, True{}, False{}) == True{} : Bool}, MB.false_ne_true()(nsx))
                        case False{}:
                          Empty.absurd({sel3(False{}, True{}, True{}, True{}, pux) == True{} : Bool}, MB.false_ne_true()(txy))
                    case False{}:
                      Empty.absurd({sel3(False{}, True{}, True{}, False{}, pux) == True{} : Bool}, MB.false_ne_true()(o_wxz))
            case False{}:
              Empty.absurd({sel3(False{}, True{}, False{}, pwx, pux) == True{} : Bool}, MB.false_ne_true()(tzx))
        case False{}:
          match pfx:
            case True{}:
              Empty.absurd({sel3(False{}, False{}, True{}, pwx, pux) == True{} : Bool}, MB.false_ne_true()(txz))
            case False{}:
              match pfy:
                case True{}:
                  Empty.absurd({sel3(False{}, False{}, False{}, pwx, pux) == True{} : Bool}, MB.false_ne_true()(tyz))
                case False{}:
                  Empty.absurd({sel3(False{}, False{}, False{}, pwx, pux) == True{} : Bool}, MB.false_ne_true()(o_fxy))

def g2y(+bz: Bool, +az: Bool, +pfx: Bool, +pfy: Bool, +pwx: Bool, +puy: Bool, +pux: Bool, +pwy: Bool, +pfz: Bool, +nsx: {pux == True{} : Bool}, +nsy: {pwy == True{} : Bool}, +nsz: {pfz == True{} : Bool}, +tzx: {Bool.or(pfx, Bool.not(az)) == True{} : Bool}, +tzy: {Bool.or(pfy, Bool.not(bz)) == True{} : Bool}, +txz: {Bool.or(az, Bool.not(pfx)) == True{} : Bool}, +tyz: {Bool.or(bz, Bool.not(pfy)) == True{} : Bool}, +txy: {Bool.or(puy, Bool.not(pwx)) == True{} : Bool}, +tyx: {Bool.or(pwx, Bool.not(puy)) == True{} : Bool}, +o_uyz: {Bool.or(puy, az) == True{} : Bool}, +o_wxz: {Bool.or(pwx, bz) == True{} : Bool}, +o_fxy: {Bool.or(pfx, pfy) == True{} : Bool}) -> {sel3(bz, az, pfy, pwy, puy) == True{} : Bool}:
  match bz:
    case True{}:
      match az:
        case True{}:
          match pfx:
            case True{}:
              match pfy:
                case True{}:
                  {==}
                case False{}:
                  Empty.absurd({sel3(True{}, True{}, False{}, pwy, puy) == True{} : Bool}, MB.false_ne_true()(tzy))
            case False{}:
              Empty.absurd({sel3(True{}, True{}, pfy, pwy, puy) == True{} : Bool}, MB.false_ne_true()(tzx))
        case False{}:
          match pfx:
            case True{}:
              Empty.absurd({sel3(True{}, False{}, pfy, pwy, puy) == True{} : Bool}, MB.false_ne_true()(txz))
            case False{}:
              match pfy:
                case True{}:
                  match pwx:
                    case True{}:
                      match puy:
                        case True{}:
                          match pux:
                            case True{}:
                              match pwy:
                                case True{}:
                                  {==}
                                case False{}:
                                  Empty.absurd({sel3(True{}, False{}, True{}, False{}, True{}) == True{} : Bool}, MB.false_ne_true()(nsy))
                            case False{}:
                              Empty.absurd({sel3(True{}, False{}, True{}, pwy, True{}) == True{} : Bool}, MB.false_ne_true()(nsx))
                        case False{}:
                          Empty.absurd({sel3(True{}, False{}, True{}, pwy, False{}) == True{} : Bool}, MB.false_ne_true()(txy))
                    case False{}:
                      match puy:
                        case True{}:
                          Empty.absurd({sel3(True{}, False{}, True{}, pwy, True{}) == True{} : Bool}, MB.false_ne_true()(tyx))
                        case False{}:
                          Empty.absurd({sel3(True{}, False{}, True{}, pwy, False{}) == True{} : Bool}, MB.false_ne_true()(o_uyz))
                case False{}:
                  Empty.absurd({sel3(True{}, False{}, False{}, pwy, puy) == True{} : Bool}, MB.false_ne_true()(tzy))
    case False{}:
      match az:
        case True{}:
          match pfx:
            case True{}:
              match pfy:
                case True{}:
                  Empty.absurd({sel3(False{}, True{}, True{}, pwy, puy) == True{} : Bool}, MB.false_ne_true()(tyz))
                case False{}:
                  match pwx:
                    case True{}:
                      match puy:
                        case True{}:
                          {==}
                        case False{}:
                          Empty.absurd({sel3(False{}, True{}, False{}, pwy, False{}) == True{} : Bool}, MB.false_ne_true()(txy))
                    case False{}:
                      Empty.absurd({sel3(False{}, True{}, False{}, pwy, puy) == True{} : Bool}, MB.false_ne_true()(o_wxz))
            case False{}:
              Empty.absurd({sel3(False{}, True{}, pfy, pwy, puy) == True{} : Bool}, MB.false_ne_true()(tzx))
        case False{}:
          match pfx:
            case True{}:
              Empty.absurd({sel3(False{}, False{}, pfy, pwy, puy) == True{} : Bool}, MB.false_ne_true()(txz))
            case False{}:
              match pfy:
                case True{}:
                  Empty.absurd({sel3(False{}, False{}, True{}, pwy, puy) == True{} : Bool}, MB.false_ne_true()(tyz))
                case False{}:
                  Empty.absurd({sel3(False{}, False{}, False{}, pwy, puy) == True{} : Bool}, MB.false_ne_true()(o_fxy))

def g3(+bz: Bool, +az: Bool, +pfx: Bool, +pfy: Bool, +pwx: Bool, +puy: Bool, +pux: Bool, +pwy: Bool, +pfz: Bool, +nsx: {pux == True{} : Bool}, +nsy: {pwy == True{} : Bool}, +nsz: {pfz == True{} : Bool}, +tzx: {Bool.or(pfx, Bool.not(az)) == True{} : Bool}, +tzy: {Bool.or(pfy, Bool.not(bz)) == True{} : Bool}, +txz: {Bool.or(az, Bool.not(pfx)) == True{} : Bool}, +tyz: {Bool.or(bz, Bool.not(pfy)) == True{} : Bool}, +txy: {Bool.or(puy, Bool.not(pwx)) == True{} : Bool}, +tyx: {Bool.or(pwx, Bool.not(puy)) == True{} : Bool}, +o_uyz: {Bool.or(puy, az) == True{} : Bool}, +o_wxz: {Bool.or(pwx, bz) == True{} : Bool}, +o_fxy: {Bool.or(pfx, pfy) == True{} : Bool}) -> {sel3(bz, az, pfz, bz, az) == True{} : Bool}:
  match bz:
    case True{}:
      match az:
        case True{}:
          match pfx:
            case True{}:
              match pfy:
                case True{}:
                  match pwx:
                    case True{}:
                      match puy:
                        case True{}:
                          match pux:
                            case True{}:
                              match pwy:
                                case True{}:
                                  match pfz:
                                    case True{}:
                                      {==}
                                    case False{}:
                                      Empty.absurd({sel3(True{}, True{}, False{}, True{}, True{}) == True{} : Bool}, MB.false_ne_true()(nsz))
                                case False{}:
                                  Empty.absurd({sel3(True{}, True{}, pfz, True{}, True{}) == True{} : Bool}, MB.false_ne_true()(nsy))
                            case False{}:
                              Empty.absurd({sel3(True{}, True{}, pfz, True{}, True{}) == True{} : Bool}, MB.false_ne_true()(nsx))
                        case False{}:
                          Empty.absurd({sel3(True{}, True{}, pfz, True{}, True{}) == True{} : Bool}, MB.false_ne_true()(txy))
                    case False{}:
                      match puy:
                        case True{}:
                          Empty.absurd({sel3(True{}, True{}, pfz, True{}, True{}) == True{} : Bool}, MB.false_ne_true()(tyx))
                        case False{}:
                          match pux:
                            case True{}:
                              match pwy:
                                case True{}:
                                  match pfz:
                                    case True{}:
                                      {==}
                                    case False{}:
                                      Empty.absurd({sel3(True{}, True{}, False{}, True{}, True{}) == True{} : Bool}, MB.false_ne_true()(nsz))
                                case False{}:
                                  Empty.absurd({sel3(True{}, True{}, pfz, True{}, True{}) == True{} : Bool}, MB.false_ne_true()(nsy))
                            case False{}:
                              Empty.absurd({sel3(True{}, True{}, pfz, True{}, True{}) == True{} : Bool}, MB.false_ne_true()(nsx))
                case False{}:
                  Empty.absurd({sel3(True{}, True{}, pfz, True{}, True{}) == True{} : Bool}, MB.false_ne_true()(tzy))
            case False{}:
              Empty.absurd({sel3(True{}, True{}, pfz, True{}, True{}) == True{} : Bool}, MB.false_ne_true()(tzx))
        case False{}:
          {==}
    case False{}:
      match az:
        case True{}:
          {==}
        case False{}:
          match pfx:
            case True{}:
              Empty.absurd({sel3(False{}, False{}, pfz, False{}, False{}) == True{} : Bool}, MB.false_ne_true()(txz))
            case False{}:
              match pfy:
                case True{}:
                  Empty.absurd({sel3(False{}, False{}, pfz, False{}, False{}) == True{} : Bool}, MB.false_ne_true()(tyz))
                case False{}:
                  Empty.absurd({sel3(False{}, False{}, pfz, False{}, False{}) == True{} : Bool}, MB.false_ne_true()(o_fxy))

def g4(+bz: Bool, +az: Bool, +bq: Bool, +aq: Bool, +pzq: Bool, +pqz: Bool, +pzx: Bool, +pzy: Bool, +pqx: Bool, +pqy: Bool, +tzq: {Bool.or(pzq, Bool.not(pqz)) == True{} : Bool}, +tqz: {Bool.or(pqz, Bool.not(pzq)) == True{} : Bool}, +txz: {Bool.or(az, Bool.not(pzx)) == True{} : Bool}, +txq: {Bool.or(aq, Bool.not(pqx)) == True{} : Bool}, +tyz: {Bool.or(bz, Bool.not(pzy)) == True{} : Bool}, +tyq: {Bool.or(bq, Bool.not(pqy)) == True{} : Bool}, +tzx: {Bool.or(pzx, Bool.not(az)) == True{} : Bool}, +tqx: {Bool.or(pqx, Bool.not(aq)) == True{} : Bool}, +tzy: {Bool.or(pzy, Bool.not(bz)) == True{} : Bool}, +tqy: {Bool.or(pqy, Bool.not(bq)) == True{} : Bool}, +o_qzy: {Bool.or(pqz, pqy) == True{} : Bool}, +o_qzx: {Bool.or(pqz, pqx) == True{} : Bool}, +o_qxy: {Bool.or(pqx, pqy) == True{} : Bool}, +o_zxy: {Bool.or(pzx, pzy) == True{} : Bool}, +o_zqy: {Bool.or(pzq, pzy) == True{} : Bool}, +o_zqx: {Bool.or(pzq, pzx) == True{} : Bool}) -> {Bool.or(sel3(bz, az, pzq, bq, aq), Bool.not(sel3(bq, aq, pqz, bz, az))) == True{} : Bool}:
  match bz:
    case True{}:
      match az:
        case True{}:
          match bq:
            case True{}:
              match aq:
                case True{}:
                  match pzq:
                    case True{}:
                      {==}
                    case False{}:
                      match pqz:
                        case True{}:
                          Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, True{}, True{}), Bool.not(sel3(True{}, True{}, True{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tzq))
                        case False{}:
                          {==}
                case False{}:
                  match pzq:
                    case True{}:
                      {==}
                    case False{}:
                      match pqz:
                        case True{}:
                          Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, True{}, False{}), Bool.not(sel3(True{}, False{}, True{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tzq))
                        case False{}:
                          match pzx:
                            case True{}:
                              match pzy:
                                case True{}:
                                  match pqx:
                                    case True{}:
                                      Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, True{}, False{}), Bool.not(sel3(True{}, False{}, False{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(txq))
                                    case False{}:
                                      Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, True{}, False{}), Bool.not(sel3(True{}, False{}, False{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(o_qzx))
                                case False{}:
                                  Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, True{}, False{}), Bool.not(sel3(True{}, False{}, False{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tzy))
                            case False{}:
                              Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, True{}, False{}), Bool.not(sel3(True{}, False{}, False{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tzx))
            case False{}:
              match aq:
                case True{}:
                  match pzq:
                    case True{}:
                      {==}
                    case False{}:
                      match pqz:
                        case True{}:
                          Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, False{}, True{}), Bool.not(sel3(False{}, True{}, True{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tzq))
                        case False{}:
                          match pzx:
                            case True{}:
                              match pzy:
                                case True{}:
                                  match pqx:
                                    case True{}:
                                      match pqy:
                                        case True{}:
                                          Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, False{}, True{}), Bool.not(sel3(False{}, True{}, False{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tyq))
                                        case False{}:
                                          Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, False{}, True{}), Bool.not(sel3(False{}, True{}, False{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(o_qzy))
                                    case False{}:
                                      Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, False{}, True{}), Bool.not(sel3(False{}, True{}, False{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tqx))
                                case False{}:
                                  Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, False{}, True{}), Bool.not(sel3(False{}, True{}, False{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tzy))
                            case False{}:
                              Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, False{}, True{}), Bool.not(sel3(False{}, True{}, False{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tzx))
                case False{}:
                  match pzq:
                    case True{}:
                      {==}
                    case False{}:
                      match pqz:
                        case True{}:
                          Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, False{}, False{}), Bool.not(sel3(False{}, False{}, True{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tzq))
                        case False{}:
                          match pzx:
                            case True{}:
                              match pzy:
                                case True{}:
                                  match pqx:
                                    case True{}:
                                      Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, False{}, False{}), Bool.not(sel3(False{}, False{}, False{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(txq))
                                    case False{}:
                                      Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, False{}, False{}), Bool.not(sel3(False{}, False{}, False{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(o_qzx))
                                case False{}:
                                  Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, False{}, False{}), Bool.not(sel3(False{}, False{}, False{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tzy))
                            case False{}:
                              Empty.absurd({Bool.or(sel3(True{}, True{}, False{}, False{}, False{}), Bool.not(sel3(False{}, False{}, False{}, True{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tzx))
        case False{}:
          match bq:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match az:
        case True{}:
          match bq:
            case True{}:
              match aq:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match aq:
                case True{}:
                  {==}
                case False{}:
                  match pzq:
                    case True{}:
                      match pqz:
                        case True{}:
                          match pzx:
                            case True{}:
                              match pzy:
                                case True{}:
                                  Empty.absurd({Bool.or(sel3(False{}, True{}, True{}, False{}, False{}), Bool.not(sel3(False{}, False{}, True{}, False{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tyz))
                                case False{}:
                                  match pqx:
                                    case True{}:
                                      Empty.absurd({Bool.or(sel3(False{}, True{}, True{}, False{}, False{}), Bool.not(sel3(False{}, False{}, True{}, False{}, True{}))) == True{} : Bool}, MB.false_ne_true()(txq))
                                    case False{}:
                                      match pqy:
                                        case True{}:
                                          Empty.absurd({Bool.or(sel3(False{}, True{}, True{}, False{}, False{}), Bool.not(sel3(False{}, False{}, True{}, False{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tyq))
                                        case False{}:
                                          Empty.absurd({Bool.or(sel3(False{}, True{}, True{}, False{}, False{}), Bool.not(sel3(False{}, False{}, True{}, False{}, True{}))) == True{} : Bool}, MB.false_ne_true()(o_qxy))
                            case False{}:
                              Empty.absurd({Bool.or(sel3(False{}, True{}, True{}, False{}, False{}), Bool.not(sel3(False{}, False{}, True{}, False{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tzx))
                        case False{}:
                          Empty.absurd({Bool.or(sel3(False{}, True{}, True{}, False{}, False{}), Bool.not(sel3(False{}, False{}, False{}, False{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tqz))
                    case False{}:
                      match pqz:
                        case True{}:
                          Empty.absurd({Bool.or(sel3(False{}, True{}, False{}, False{}, False{}), Bool.not(sel3(False{}, False{}, True{}, False{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tzq))
                        case False{}:
                          match pzx:
                            case True{}:
                              match pzy:
                                case True{}:
                                  Empty.absurd({Bool.or(sel3(False{}, True{}, False{}, False{}, False{}), Bool.not(sel3(False{}, False{}, False{}, False{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tyz))
                                case False{}:
                                  Empty.absurd({Bool.or(sel3(False{}, True{}, False{}, False{}, False{}), Bool.not(sel3(False{}, False{}, False{}, False{}, True{}))) == True{} : Bool}, MB.false_ne_true()(o_zqy))
                            case False{}:
                              Empty.absurd({Bool.or(sel3(False{}, True{}, False{}, False{}, False{}), Bool.not(sel3(False{}, False{}, False{}, False{}, True{}))) == True{} : Bool}, MB.false_ne_true()(tzx))
        case False{}:
          match bq:
            case True{}:
              match aq:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match aq:
                case True{}:
                  {==}
                case False{}:
                  {==}


def tw.or(pp: Bool & Bool) -> Bool:
  (+a, +b) = pp
  Bool.or(a, Bool.not(b))

def pair_eq(+e1: Bool, +e2: Bool, +f1: Bool, +f2: Bool, +h1: {e1 == f1 : Bool}, +h2: {e2 == f2 : Bool}) -> {(e1, e2) == (f1, f2) : Bool & Bool}:
  %h1 : {(e1, e2) == (_, f2) : Bool & Bool}
  %h2 : {(e1, e2) == (e1, _) : Bool & Bool}
  {==}

def sub_cons2(ys: List<&2, U32>, +z: U32, +M: List<&2, U32>, +h: {RG.sub(ys, M) == True{} : Bool}) -> {RG.sub(ys, Con{z, M}) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      and_intro(RG.has(Con{z, M}, m), RG.sub(t, Con{z, M}), XP.or_t_r(U32.is_eq(z, m), RG.has(M, m), and_l(RG.has(M, m), RG.sub(t, M), h)), sub_cons2(t, z, M, and_r(RG.has(M, m), RG.sub(t, M), h)))

def sub_refl2(ys: List<&2, U32>) -> {RG.sub(ys, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      and_intro(RG.has(Con{m, t}, m), RG.sub(t, Con{m, t}), XP.or_t_l(U32.is_eq(m, m), RG.has(t, m), XP.is_eq_self(m)), sub_cons2(t, m, t, sub_refl2(t)))

# the facts of a live node z of L2 before the link, x and y facing u and w
def zf(+t0: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +z: U32, +u: U32, +w: U32,
  +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hx: {RG.has(L, x) == True{} : Bool}, +hy: {RG.has(L, y) == True{} : Bool}, +hzL: {RG.has(L, z) == True{} : Bool},
  +hxy: {U32.is_eq(x, y) == False{} : Bool}, +hzx: {U32.is_eq(z, x) == False{} : Bool}, +hzy: {U32.is_eq(z, y) == False{} : Bool}, +hu: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)) == u : U32}, +hw: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)) == w : U32}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}) ->
  {sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (x + 1 : U32)), KMd.off.port(d, w, (x + 1 : U32)), KMd.off.port(d, u, (x + 1 : U32))) && (sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), KMd.off.port(d, w, (y + 1 : U32)), KMd.off.port(d, u, (y + 1 : U32))) && sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)))) == True{} : Bool}:
  +hxN = sub_has2(L, N, x, hLN, hx)
  +hyN = sub_has2(L, N, y, hLN, hy)
  +hzN = sub_has2(L, N, z, hLN, hzL)
  +nsx = ME.subst(U32, q => {KMd.off.port(d, q, (x + 1 : U32)) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, and_l(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), (x + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), x, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, x, hT, hx)))
  +nsy = ME.subst(U32, q => {KMd.off.port(d, q, (y + 1 : U32)) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, and_l(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), (y + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), y, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, y, hT, hy)))
  +nsz = and_l(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hT, hzL))
  +tzx = ME.subst(U32, q => {Bool.or(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (x + 1 : U32)), Bool.not(KMd.off.port(d, q, (z + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d, x, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hT, hzL)), hx))
  +tzy = ME.subst(U32, q => {Bool.or(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), Bool.not(KMd.off.port(d, q, (z + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d, y, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hT, hzL)), hy))
  +txz = ME.subst(U32, q => {Bool.or(KMd.off.port(d, q, (z + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (x + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), x, AD.view(U32, LAT.fromT(U32, t0)), d, z, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), (x + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), x, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, x, hT, hx)), hzL))
  +tyz = ME.subst(U32, q => {Bool.or(KMd.off.port(d, q, (z + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), y, AD.view(U32, LAT.fromT(U32, t0)), d, z, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), (y + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), y, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, y, hT, hy)), hzL))
  +txy = ME.subst(U32, q => {Bool.or(KMd.off.port(d, u, (y + 1 : U32)), Bool.not(KMd.off.port(d, q, (x + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, ME.subst(U32, q => {Bool.or(KMd.off.port(d, q, (y + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), (x + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), x, AD.view(U32, LAT.fromT(U32, t0)), d, y, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), (x + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), x, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, x, hT, hx)), hy)))
  +tyx = ME.subst(U32, q => {Bool.or(KMd.off.port(d, w, (x + 1 : U32)), Bool.not(KMd.off.port(d, q, (y + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, ME.subst(U32, q => {Bool.or(KMd.off.port(d, q, (x + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), (y + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), y, AD.view(U32, LAT.fromT(U32, t0)), d, x, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), (y + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), y, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, y, hT, hy)), hx)))
  +o_uyz = no2(u, y, z, d, N, hN, hyN, hzN, ueq_ne(z, y, hzy))
  +o_wxz = no2(w, x, z, d, N, hN, hxN, hzN, ueq_ne(z, x, hzx))
  +o_fxy = no2(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), x, y, d, N, hN, hxN, hyN, hxy)
  and_intro(sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (x + 1 : U32)), KMd.off.port(d, w, (x + 1 : U32)), KMd.off.port(d, u, (x + 1 : U32))), sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), KMd.off.port(d, w, (y + 1 : U32)), KMd.off.port(d, u, (y + 1 : U32))) && sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32))),
    g2x(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (x + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), KMd.off.port(d, w, (x + 1 : U32)), KMd.off.port(d, u, (y + 1 : U32)), KMd.off.port(d, u, (x + 1 : U32)), KMd.off.port(d, w, (y + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), nsx, nsy, nsz, tzx, tzy, txz, tyz, txy, tyx, o_uyz, o_wxz, o_fxy),
    and_intro(sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), KMd.off.port(d, w, (y + 1 : U32)), KMd.off.port(d, u, (y + 1 : U32))), sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32))),
      g2y(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (x + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), KMd.off.port(d, w, (x + 1 : U32)), KMd.off.port(d, u, (y + 1 : U32)), KMd.off.port(d, u, (x + 1 : U32)), KMd.off.port(d, w, (y + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), nsx, nsy, nsz, tzx, tzy, txz, tyz, txy, tyx, o_uyz, o_wxz, o_fxy),
      g3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (x + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), KMd.off.port(d, w, (x + 1 : U32)), KMd.off.port(d, u, (y + 1 : U32)), KMd.off.port(d, u, (x + 1 : U32)), KMd.off.port(d, w, (y + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), nsx, nsy, nsz, tzx, tzy, txz, tyz, txy, tyx, o_uyz, o_wxz, o_fxy)))

def zqf(+t0: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +z: U32, +q: U32, +u: U32, +w: U32,
  +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hx: {RG.has(L, x) == True{} : Bool}, +hy: {RG.has(L, y) == True{} : Bool}, +hzL: {RG.has(L, z) == True{} : Bool}, +hqL: {RG.has(L, q) == True{} : Bool},
  +hxy: {U32.is_eq(x, y) == False{} : Bool}, +hzx: {U32.is_eq(z, x) == False{} : Bool}, +hzy: {U32.is_eq(z, y) == False{} : Bool}, +hqx: {U32.is_eq(q, x) == False{} : Bool}, +hqy: {U32.is_eq(q, y) == False{} : Bool}, +hu: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)) == u : U32}, +hw: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)) == w : U32}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}) ->
  {Bool.or(sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (q + 1 : U32)), KMd.off.port(d, w, (q + 1 : U32)), KMd.off.port(d, u, (q + 1 : U32))), Bool.not(sel3(KMd.off.port(d, w, (q + 1 : U32)), KMd.off.port(d, u, (q + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (z + 1 : U32)), KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32))))) == True{} : Bool}:
  +hxN = sub_has2(L, N, x, hLN, hx)
  +hyN = sub_has2(L, N, y, hLN, hy)
  +hzN = sub_has2(L, N, z, hLN, hzL)
  +hqN = sub_has2(L, N, q, hLN, hqL)
  g4(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, w, (q + 1 : U32)), KMd.off.port(d, u, (q + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (q + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (x + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (x + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (y + 1 : U32)),
    tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d, q, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hT, hzL)), hqL), tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), q, AD.view(U32, LAT.fromT(U32, t0)), d, z, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (q + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), q, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, q, hT, hqL)), hzL),
    ME.subst(U32, q => {Bool.or(KMd.off.port(d, q, (z + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (x + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), x, AD.view(U32, LAT.fromT(U32, t0)), d, z, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), (x + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), x, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, x, hT, hx)), hzL)),
    ME.subst(U32, qq => {Bool.or(KMd.off.port(d, qq, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (x + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), x, AD.view(U32, LAT.fromT(U32, t0)), d, q, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), (x + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), x, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, x, hT, hx)), hqL)),
    ME.subst(U32, q => {Bool.or(KMd.off.port(d, q, (z + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), y, AD.view(U32, LAT.fromT(U32, t0)), d, z, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), (y + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), y, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, y, hT, hy)), hzL)),
    ME.subst(U32, qq => {Bool.or(KMd.off.port(d, qq, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (y + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), y, AD.view(U32, LAT.fromT(U32, t0)), d, q, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), (y + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), y, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, y, hT, hy)), hqL)),
    ME.subst(U32, q => {Bool.or(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (x + 1 : U32)), Bool.not(KMd.off.port(d, q, (z + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d, x, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hT, hzL)), hx)),
    ME.subst(U32, qq => {Bool.or(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (x + 1 : U32)), Bool.not(KMd.off.port(d, qq, (q + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), q, AD.view(U32, LAT.fromT(U32, t0)), d, x, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (q + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), q, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, q, hT, hqL)), hx)),
    ME.subst(U32, q => {Bool.or(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), Bool.not(KMd.off.port(d, q, (z + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d, y, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hT, hzL)), hy)),
    ME.subst(U32, qq => {Bool.or(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (y + 1 : U32)), Bool.not(KMd.off.port(d, qq, (q + 1 : U32)))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), q, AD.view(U32, LAT.fromT(U32, t0)), d, y, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (q + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), q, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, q, hT, hqL)), hy)),
    no2(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), z, y, d, N, hN, hzN, hyN, hzy), no2(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), z, x, d, N, hN, hzN, hxN, hzx), no2(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), x, y, d, N, hN, hxN, hyN, hxy),
    no2(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), x, y, d, N, hN, hxN, hyN, hxy), no2(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), q, y, d, N, hN, hqN, hyN, hqy), no2(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), q, x, d, N, hN, hqN, hxN, hqx))

# the faces after: each a port faceable by L, so by L2
def ind_f(ys: List<&2, U32>, +t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +u: U32, +w: U32, +su: Bool, +sw: Bool,
  +e1: {LAT.fromT(U32, t1) == lk(su, LAT.fromT(U32, t0), u, w) : Array<U32>}, +hsu: {P.is_static(u) == su : Bool}, +hsw: {P.is_static(w) == sw : Bool}, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hft1: {AD.full(U32, LAT.fromT(U32, t1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hx: {RG.has(L, x) == True{} : Bool}, +hy: {RG.has(L, y) == True{} : Bool}, +hxy: {U32.is_eq(x, y) == False{} : Bool}, +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{x, Con{y, L2}}) == True{} : Bool},
  +hx2: {RG.has(L2, x) == False{} : Bool}, +hy2: {RG.has(L2, y) == False{} : Bool}, +hu: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)) == u : U32}, +hw: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)) == w : U32},
  +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hys: {RG.sub(ys, L2) == True{} : Bool}) -> {RG.faces(ys, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, L2) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      +hz2 = and_l(RG.has(L2, z), RG.sub(r, L2), hys)
  +hzL = sub_has2(L2, L, z, hs1, hz2)
  +hzx = nhas(L2, z, x, hz2, hx2)
  +hzy = nhas(L2, z, y, hz2, hy2)
      and_intro(RG.faces.m(List.get(&2, U32, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), AD.slot((z + 1 : U32), d)), d, L2), RG.faces(r, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, L2),
        fm_of_word(List.get(&2, U32, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), AD.slot((z + 1 : U32), d)), d, L2,
          ME.subst(Maybe<&2, U32>, m => {XP.is_some(m) == True{} : Bool}, Some{Pair.snd(Array<U32>, U32, Array.get(U32, lk(sw, LAT.fromT(U32, t1), w, u), (z + 1 : U32)))}, List.get(&2, U32, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), AD.slot((z + 1 : U32), d)), LA.get_view(U32, lk(sw, LAT.fromT(U32, t1), w, u), d, (z + 1 : U32), lk_full(sw, LAT.fromT(U32, t1), d, w, u, hft1), hd32), {==}),
          ME.subst(U32, qq => {RG.port.ok(L2, d, qq) == True{} : Bool}, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), Equal.trans(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), sel(KMd.off.port(d, w, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), u), sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), word_lk(sw, t1, d, w, u, (z + 1 : U32), hsw, hft1, hd32), Equal.cong(U32, U32, qq => sel(KMd.off.port(d, w, (z + 1 : U32)), qq, u), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), Equal.trans(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), KMd.word(AD.view(U32, lk(su, LAT.fromT(U32, t0), u, w)), d, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), Equal.cong(Array<U32>, U32, AA => KMd.word(AD.view(U32, AA), d, (z + 1 : U32)), LAT.fromT(U32, t1), lk(su, LAT.fromT(U32, t0), u, w), e1), word_lk(su, t0, d, u, w, (z + 1 : U32), hsu, hft, hd32))))),
            pk_sub(L2, L, d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), hs1, pk_sel(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w, u, d, L, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((z + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hF, hzL)), ME.subst(U32, q => {RG.port.ok(L, d, q) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((y + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, y, hF, hy))), ME.subst(U32, q => {RG.port.ok(L, d, q) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((x + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, x, hF, hx))))))),
        ind_f(r, t0, t1, d, L, L2, N, x, y, u, w, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, hu, hw, hF, hO, hT, and_r(RG.has(L2, z), RG.sub(r, L2), hys)))

# what each of L2 faces after: off every tracked node's words as asked
def ind_o(ys: List<&2, U32>, +t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +u: U32, +w: U32, +su: Bool, +sw: Bool,
  +e1: {LAT.fromT(U32, t1) == lk(su, LAT.fromT(U32, t0), u, w) : Array<U32>}, +hsu: {P.is_static(u) == su : Bool}, +hsw: {P.is_static(w) == sw : Bool}, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hft1: {AD.full(U32, LAT.fromT(U32, t1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hx: {RG.has(L, x) == True{} : Bool}, +hy: {RG.has(L, y) == True{} : Bool}, +hxy: {U32.is_eq(x, y) == False{} : Bool}, +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{x, Con{y, L2}}) == True{} : Bool},
  +hx2: {RG.has(L2, x) == False{} : Bool}, +hy2: {RG.has(L2, y) == False{} : Bool}, +hu: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)) == u : U32}, +hw: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)) == w : U32},
  +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hys: {RG.sub(ys, L2) == True{} : Bool}) -> {RG.px.off(ys, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, L2, N) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      +hz2 = and_l(RG.has(L2, z), RG.sub(r, L2), hys)
  +hzL = sub_has2(L2, L, z, hs1, hz2)
  +hzx = nhas(L2, z, x, hz2, hx2)
  +hzy = nhas(L2, z, y, hz2, hy2)
      and_intro(RG.po.all(KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), L2, d, N), RG.px.off(r, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, L2, N),
        ME.subst(U32, qq => {RG.po.all(qq, L2, d, N) == True{} : Bool}, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), Equal.trans(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), sel(KMd.off.port(d, w, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), u), sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), word_lk(sw, t1, d, w, u, (z + 1 : U32), hsw, hft1, hd32), Equal.cong(U32, U32, qq => sel(KMd.off.port(d, w, (z + 1 : U32)), qq, u), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), Equal.trans(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), KMd.word(AD.view(U32, lk(su, LAT.fromT(U32, t0), u, w)), d, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), Equal.cong(Array<U32>, U32, AA => KMd.word(AD.view(U32, AA), d, (z + 1 : U32)), LAT.fromT(U32, t1), lk(su, LAT.fromT(U32, t0), u, w), e1), word_lk(su, t0, d, u, w, (z + 1 : U32), hsu, hft, hd32))))),
          po_shrink(N, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), L, L2, x, y, d, po_sel(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w, u, d, L, N, po_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N, z, hO, hzL), ME.subst(U32, q => {RG.po.all(q, L, d, N) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, po_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N, y, hO, hy)), ME.subst(U32, q => {RG.po.all(q, L, d, N) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, po_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N, x, hO, hx))), hs2,
            and_intro(KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (x + 1 : U32)), KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (x + 2 : U32)) && KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (x + 3 : U32)), Equal.trans(Bool, KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (x + 1 : U32)), sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (x + 1 : U32)), KMd.off.port(d, w, (x + 1 : U32)), KMd.off.port(d, u, (x + 1 : U32))), True{}, op_sel(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w, u, d, (x + 1 : U32)), and_l(sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (x + 1 : U32)), KMd.off.port(d, w, (x + 1 : U32)), KMd.off.port(d, u, (x + 1 : U32))), sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), KMd.off.port(d, w, (y + 1 : U32)), KMd.off.port(d, u, (y + 1 : U32))) && sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32))), zf(t0, d, L, N, x, y, z, u, w, hN, hLN, hx, hy, hzL, hxy, hzx, hzy, hu, hw, hT))), and_intro(KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (x + 2 : U32)), KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (x + 3 : U32)), pk2(L, d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), x, pk_sel(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w, u, d, L, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((z + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hF, hzL)), ME.subst(U32, q => {RG.port.ok(L, d, q) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((y + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, y, hF, hy))), ME.subst(U32, q => {RG.port.ok(L, d, q) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((x + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, x, hF, hx)))), hx), pk3(L, d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), x, pk_sel(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w, u, d, L, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((z + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hF, hzL)), ME.subst(U32, q => {RG.port.ok(L, d, q) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((y + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, y, hF, hy))), ME.subst(U32, q => {RG.port.ok(L, d, q) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((x + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, x, hF, hx)))), hx))), and_intro(KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (y + 1 : U32)), KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (y + 2 : U32)) && KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (y + 3 : U32)), Equal.trans(Bool, KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (y + 1 : U32)), sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), KMd.off.port(d, w, (y + 1 : U32)), KMd.off.port(d, u, (y + 1 : U32))), True{}, op_sel(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w, u, d, (y + 1 : U32)), and_l(sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), KMd.off.port(d, w, (y + 1 : U32)), KMd.off.port(d, u, (y + 1 : U32))), sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32))), and_r(sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (x + 1 : U32)), KMd.off.port(d, w, (x + 1 : U32)), KMd.off.port(d, u, (x + 1 : U32))), sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), KMd.off.port(d, w, (y + 1 : U32)), KMd.off.port(d, u, (y + 1 : U32))) && sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32))), zf(t0, d, L, N, x, y, z, u, w, hN, hLN, hx, hy, hzL, hxy, hzx, hzy, hu, hw, hT)))), and_intro(KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (y + 2 : U32)), KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (y + 3 : U32)), pk2(L, d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), y, pk_sel(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w, u, d, L, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((z + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hF, hzL)), ME.subst(U32, q => {RG.port.ok(L, d, q) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((y + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, y, hF, hy))), ME.subst(U32, q => {RG.port.ok(L, d, q) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((x + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, x, hF, hx)))), hy), pk3(L, d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), y, pk_sel(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w, u, d, L, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((z + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hF, hzL)), ME.subst(U32, q => {RG.port.ok(L, d, q) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), w, hw, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((y + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, y, hF, hy))), ME.subst(U32, q => {RG.port.ok(L, d, q) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), u, hu, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((x + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, x, hF, hx)))), hy))))),
        ind_o(r, t0, t1, d, L, L2, N, x, y, u, w, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, hu, hw, hF, hO, hT, and_r(RG.has(L2, z), RG.sub(r, L2), hys)))

# z facing back what faces it after, over qs of L2
def ind_q(qs: List<&2, U32>, +t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +u: U32, +w: U32, +su: Bool, +sw: Bool,
  +e1: {LAT.fromT(U32, t1) == lk(su, LAT.fromT(U32, t0), u, w) : Array<U32>}, +hsu: {P.is_static(u) == su : Bool}, +hsw: {P.is_static(w) == sw : Bool}, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hft1: {AD.full(U32, LAT.fromT(U32, t1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hx: {RG.has(L, x) == True{} : Bool}, +hy: {RG.has(L, y) == True{} : Bool}, +hxy: {U32.is_eq(x, y) == False{} : Bool}, +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{x, Con{y, L2}}) == True{} : Bool},
  +hx2: {RG.has(L2, x) == False{} : Bool}, +hy2: {RG.has(L2, y) == False{} : Bool}, +hu: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)) == u : U32}, +hw: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)) == w : U32},
  +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +z: U32, +hz2: {RG.has(L2, z) == True{} : Bool}, +hqs: {RG.sub(qs, L2) == True{} : Bool}) -> {RG.tw.q(qs, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d) == True{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{+q, +r}:
      +hq2 = and_l(RG.has(L2, q), RG.sub(r, L2), hqs)
  +hzL = sub_has2(L2, L, z, hs1, hz2)
  +hzx = nhas(L2, z, x, hz2, hx2)
  +hzy = nhas(L2, z, y, hz2, hy2)
  +hqL = sub_has2(L2, L, q, hs1, hq2)
  +hqx = nhas(L2, q, x, hq2, hx2)
  +hqy = nhas(L2, q, y, hq2, hy2)
      +hzq = Equal.trans(Bool, Bool.or(KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (q + 1 : U32)), Bool.not(KMd.off.port(d, sel(KMd.off.port(d, w, (q + 1 : U32)), sel(KMd.off.port(d, u, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), w), u), (z + 1 : U32)))), sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (q + 1 : U32)), KMd.off.port(d, w, (q + 1 : U32)), KMd.off.port(d, u, (q + 1 : U32))) || Bool.not(sel3(KMd.off.port(d, w, (q + 1 : U32)), KMd.off.port(d, u, (q + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (z + 1 : U32)), KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)))), True{},
        Equal.cong(Bool & Bool, Bool, pp => tw.or(pp), (KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (q + 1 : U32)), KMd.off.port(d, sel(KMd.off.port(d, w, (q + 1 : U32)), sel(KMd.off.port(d, u, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), w), u), (z + 1 : U32))), (sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (q + 1 : U32)), KMd.off.port(d, w, (q + 1 : U32)), KMd.off.port(d, u, (q + 1 : U32))), sel3(KMd.off.port(d, w, (q + 1 : U32)), KMd.off.port(d, u, (q + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (z + 1 : U32)), KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)))),
          pair_eq(KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (q + 1 : U32)), KMd.off.port(d, sel(KMd.off.port(d, w, (q + 1 : U32)), sel(KMd.off.port(d, u, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), w), u), (z + 1 : U32)), sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (q + 1 : U32)), KMd.off.port(d, w, (q + 1 : U32)), KMd.off.port(d, u, (q + 1 : U32))), sel3(KMd.off.port(d, w, (q + 1 : U32)), KMd.off.port(d, u, (q + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (z + 1 : U32)), KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32))), op_sel(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w, u, d, (q + 1 : U32)), op_sel(KMd.off.port(d, w, (q + 1 : U32)), KMd.off.port(d, u, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), w, u, d, (z + 1 : U32)))), zqf(t0, d, L, N, x, y, z, q, u, w, hN, hLN, hx, hy, hzL, hqL, hxy, hzx, hzy, hqx, hqy, hu, hw, hT))
      and_intro(Bool.or(KMd.off.port(d, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (q + 1 : U32)), (z + 1 : U32)))), RG.tw.q(r, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d),
        ME.subst(U32, q2 => {Bool.or(KMd.off.port(d, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), (q + 1 : U32)), Bool.not(KMd.off.port(d, q2, (z + 1 : U32)))) == True{} : Bool}, sel(KMd.off.port(d, w, (q + 1 : U32)), sel(KMd.off.port(d, u, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), w), u), KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (q + 1 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (q + 1 : U32)), sel(KMd.off.port(d, w, (q + 1 : U32)), sel(KMd.off.port(d, u, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), w), u), Equal.trans(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (q + 1 : U32)), sel(KMd.off.port(d, w, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (q + 1 : U32)), u), sel(KMd.off.port(d, w, (q + 1 : U32)), sel(KMd.off.port(d, u, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), w), u), word_lk(sw, t1, d, w, u, (q + 1 : U32), hsw, hft1, hd32), Equal.cong(U32, U32, qq => sel(KMd.off.port(d, w, (q + 1 : U32)), qq, u), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (q + 1 : U32)), sel(KMd.off.port(d, u, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), w), Equal.trans(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (q + 1 : U32)), KMd.word(AD.view(U32, lk(su, LAT.fromT(U32, t0), u, w)), d, (q + 1 : U32)), sel(KMd.off.port(d, u, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), w), Equal.cong(Array<U32>, U32, AA => KMd.word(AD.view(U32, AA), d, (q + 1 : U32)), LAT.fromT(U32, t1), lk(su, LAT.fromT(U32, t0), u, w), e1), word_lk(su, t0, d, u, w, (q + 1 : U32), hsu, hft, hd32))))),
          ME.subst(U32, q1 => {Bool.or(KMd.off.port(d, q1, (q + 1 : U32)), Bool.not(KMd.off.port(d, sel(KMd.off.port(d, w, (q + 1 : U32)), sel(KMd.off.port(d, u, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), w), u), (z + 1 : U32)))) == True{} : Bool}, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), Equal.trans(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), sel(KMd.off.port(d, w, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), u), sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), word_lk(sw, t1, d, w, u, (z + 1 : U32), hsw, hft1, hd32), Equal.cong(U32, U32, qq => sel(KMd.off.port(d, w, (z + 1 : U32)), qq, u), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), Equal.trans(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), KMd.word(AD.view(U32, lk(su, LAT.fromT(U32, t0), u, w)), d, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), Equal.cong(Array<U32>, U32, AA => KMd.word(AD.view(U32, AA), d, (z + 1 : U32)), LAT.fromT(U32, t1), lk(su, LAT.fromT(U32, t0), u, w), e1), word_lk(su, t0, d, u, w, (z + 1 : U32), hsu, hft, hd32))))), hzq)),
        ind_q(r, t0, t1, d, L, L2, N, x, y, u, w, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, hu, hw, hF, hO, hT, z, hz2, and_r(RG.has(L2, q), RG.sub(r, L2), hqs)))

# each of L2 not facing itself after, and facing back what faces it
def ind_t(ys: List<&2, U32>, +t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +u: U32, +w: U32, +su: Bool, +sw: Bool,
  +e1: {LAT.fromT(U32, t1) == lk(su, LAT.fromT(U32, t0), u, w) : Array<U32>}, +hsu: {P.is_static(u) == su : Bool}, +hsw: {P.is_static(w) == sw : Bool}, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hft1: {AD.full(U32, LAT.fromT(U32, t1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hx: {RG.has(L, x) == True{} : Bool}, +hy: {RG.has(L, y) == True{} : Bool}, +hxy: {U32.is_eq(x, y) == False{} : Bool}, +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{x, Con{y, L2}}) == True{} : Bool},
  +hx2: {RG.has(L2, x) == False{} : Bool}, +hy2: {RG.has(L2, y) == False{} : Bool}, +hu: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)) == u : U32}, +hw: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)) == w : U32},
  +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hys: {RG.sub(ys, L2) == True{} : Bool}) -> {RG.px.tw(ys, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, L2) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      +hz2 = and_l(RG.has(L2, z), RG.sub(r, L2), hys)
  +hzL = sub_has2(L2, L, z, hs1, hz2)
  +hzx = nhas(L2, z, x, hz2, hx2)
  +hzy = nhas(L2, z, y, hz2, hy2)
      and_intro(KMd.off.port(d, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L2, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d) && RG.px.tw(r, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, L2),
        ME.subst(U32, qq => {KMd.off.port(d, qq, (z + 1 : U32)) == True{} : Bool}, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), Equal.trans(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), sel(KMd.off.port(d, w, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), u), sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), word_lk(sw, t1, d, w, u, (z + 1 : U32), hsw, hft1, hd32), Equal.cong(U32, U32, qq => sel(KMd.off.port(d, w, (z + 1 : U32)), qq, u), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), Equal.trans(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), KMd.word(AD.view(U32, lk(su, LAT.fromT(U32, t0), u, w)), d, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), Equal.cong(Array<U32>, U32, AA => KMd.word(AD.view(U32, AA), d, (z + 1 : U32)), LAT.fromT(U32, t1), lk(su, LAT.fromT(U32, t0), u, w), e1), word_lk(su, t0, d, u, w, (z + 1 : U32), hsu, hft, hd32))))),
          Equal.trans(Bool, KMd.off.port(d, sel(KMd.off.port(d, w, (z + 1 : U32)), sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), (z + 1 : U32)), sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32))), True{}, op_sel(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w, u, d, (z + 1 : U32)), and_r(sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), KMd.off.port(d, w, (y + 1 : U32)), KMd.off.port(d, u, (y + 1 : U32))), sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32))), and_r(sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (x + 1 : U32)), KMd.off.port(d, w, (x + 1 : U32)), KMd.off.port(d, u, (x + 1 : U32))), sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (y + 1 : U32)), KMd.off.port(d, w, (y + 1 : U32)), KMd.off.port(d, u, (y + 1 : U32))) && sel3(KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), KMd.off.port(d, w, (z + 1 : U32)), KMd.off.port(d, u, (z + 1 : U32))), zf(t0, d, L, N, x, y, z, u, w, hN, hLN, hx, hy, hzL, hxy, hzx, hzy, hu, hw, hT))))),
        and_intro(RG.tw.q(L2, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d), RG.px.tw(r, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, L2), ind_q(L2, t0, t1, d, L, L2, N, x, y, u, w, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, hu, hw, hF, hO, hT, z, hz2, sub_refl2(L2)),
          ind_t(r, t0, t1, d, L, L2, N, x, y, u, w, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, hu, hw, hF, hO, hT, and_r(RG.has(L2, z), RG.sub(r, L2), hys))))

def ll.k1(+t0: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +u: U32, +w: U32, +su: Bool, +sw: Bool,
  +hsu: {P.is_static(u) == su : Bool}, +hsw: {P.is_static(w) == sw : Bool}, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hx: {RG.has(L, x) == True{} : Bool}, +hy: {RG.has(L, y) == True{} : Bool}, +hxy: {U32.is_eq(x, y) == False{} : Bool}, +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{x, Con{y, L2}}) == True{} : Bool},
  +hx2: {RG.has(L2, x) == False{} : Bool}, +hy2: {RG.has(L2, y) == False{} : Bool}, +hu: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)) == u : U32}, +hw: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)) == w : U32},
  +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool},
  -w1: Array<U32>, +hw1: {w1 == lk(su, LAT.fromT(U32, t0), u, w) : Array<U32>}, hf1: {AD.full(U32, w1, d) == True{} : Bool}, m1: LAT.Mirror(U32, w1)) -> {RG.faces(L2, AD.view(U32, lk(sw, w1, w, u)), d, L2) && (RG.px.off(L2, AD.view(U32, lk(sw, w1, w, u)), d, L2, N) && RG.px.tw(L2, AD.view(U32, lk(sw, w1, w, u)), d, L2)) == True{} : Bool}:
  (+t1, +e0) = m1
  +hft1 = LAP.full_t(U32, w1, t1, d, e0, hf1)
  +e1 = Equal.trans(Array<U32>, LAT.fromT(U32, t1), w1, lk(su, LAT.fromT(U32, t0), u, w), e0, hw1)
  %e0 : {RG.faces(L2, AD.view(U32, lk(sw, _, w, u)), d, L2) && (RG.px.off(L2, AD.view(U32, lk(sw, _, w, u)), d, L2, N) && RG.px.tw(L2, AD.view(U32, lk(sw, _, w, u)), d, L2)) == True{} : Bool}
  and_intro(RG.faces(L2, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, L2), RG.px.off(L2, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, L2, N) && RG.px.tw(L2, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, L2), ind_f(L2, t0, t1, d, L, L2, N, x, y, u, w, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, hu, hw, hF, hO, hT, sub_refl2(L2)),
    and_intro(RG.px.off(L2, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, L2, N), RG.px.tw(L2, AD.view(U32, lk(sw, LAT.fromT(U32, t1), w, u)), d, L2), ind_o(L2, t0, t1, d, L, L2, N, x, y, u, w, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, hu, hw, hF, hO, hT, sub_refl2(L2)), ind_t(L2, t0, t1, d, L, L2, N, x, y, u, w, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, hu, hw, hF, hO, hT, sub_refl2(L2))))

def ll.k0(+t0: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +u: U32, +w: U32, 
  +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hx: {RG.has(L, x) == True{} : Bool}, +hy: {RG.has(L, y) == True{} : Bool}, +hxy: {U32.is_eq(x, y) == False{} : Bool}, +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{x, Con{y, L2}}) == True{} : Bool},
  +hx2: {RG.has(L2, x) == False{} : Bool}, +hy2: {RG.has(L2, y) == False{} : Bool}, +hu: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)) == u : U32}, +hw: {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)) == w : U32},
  +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, -a: Array<V.Val>) -> {RG.faces(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, u, w))), d, L2) && (RG.px.off(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, u, w))), d, L2, N) && RG.px.tw(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, u, w))), d, L2)) == True{} : Bool}:
  %Equal.sym(P.H, P.link.to(P.is_static(u), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, u, w), P.H{KM.MG{lk(P.is_static(u), LAT.fromT(U32, t0), u, w)}, a}, lt_eq(P.is_static(u), LAT.fromT(U32, t0), a, u, w)) :
    {RG.faces(L2, AD.view(U32, KMd.words(P.link.to(P.is_static(w), _, w, u))), d, L2) && (RG.px.off(L2, AD.view(U32, KMd.words(P.link.to(P.is_static(w), _, w, u))), d, L2, N) && RG.px.tw(L2, AD.view(U32, KMd.words(P.link.to(P.is_static(w), _, w, u))), d, L2)) == True{} : Bool}
  %Equal.sym(P.H, P.link.to(P.is_static(w), P.H{KM.MG{lk(P.is_static(u), LAT.fromT(U32, t0), u, w)}, a}, w, u), P.H{KM.MG{lk(P.is_static(w), lk(P.is_static(u), LAT.fromT(U32, t0), u, w), w, u)}, a}, lt_eq(P.is_static(w), lk(P.is_static(u), LAT.fromT(U32, t0), u, w), a, w, u)) :
    {RG.faces(L2, AD.view(U32, KMd.words(_)), d, L2) && (RG.px.off(L2, AD.view(U32, KMd.words(_)), d, L2, N) && RG.px.tw(L2, AD.view(U32, KMd.words(_)), d, L2)) == True{} : Bool}
  ll.k1(t0, d, L, L2, N, x, y, u, w, P.is_static(u), P.is_static(w), {==}, {==}, hft, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, hu, hw, hF, hO, hT, lk(P.is_static(u), LAT.fromT(U32, t0), u, w), {==}, lk_full(P.is_static(u), LAT.fromT(U32, t0), d, u, w, hft), LAT.mirror(U32, lk(P.is_static(u), LAT.fromT(U32, t0), u, w)))

def ll.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32,
  hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hx: {RG.has(L, x) == True{} : Bool}, +hy: {RG.has(L, y) == True{} : Bool},
  +hxy: {U32.is_eq(x, y) == False{} : Bool}, +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{x, Con{y, L2}}) == True{} : Bool}, +hx2: {RG.has(L2, x) == False{} : Bool}, +hy2: {RG.has(L2, y) == False{} : Bool},
  hF: {RG.faces(L, AD.view(U32, w), d, L) == True{} : Bool}, hO: {RG.px.off(L, AD.view(U32, w), d, L, N) == True{} : Bool}, hT: {RG.px.tw(L, AD.view(U32, w), d, L) == True{} : Bool}, m: LAT.Mirror(U32, w)) -> {RG.faces(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{w}, a}, KMd.word(AD.view(U32, w), d, (x + 1 : U32)), KMd.word(AD.view(U32, w), d, (y + 1 : U32))))), d, L2) && (RG.px.off(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{w}, a}, KMd.word(AD.view(U32, w), d, (x + 1 : U32)), KMd.word(AD.view(U32, w), d, (y + 1 : U32))))), d, L2, N) && RG.px.tw(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{w}, a}, KMd.word(AD.view(U32, w), d, (x + 1 : U32)), KMd.word(AD.view(U32, w), d, (y + 1 : U32))))), d, L2)) == True{} : Bool}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e)
  %e : {RG.faces(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{_}, a}, KMd.word(AD.view(U32, _), d, (x + 1 : U32)), KMd.word(AD.view(U32, _), d, (y + 1 : U32))))), d, L2) && (RG.px.off(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{_}, a}, KMd.word(AD.view(U32, _), d, (x + 1 : U32)), KMd.word(AD.view(U32, _), d, (y + 1 : U32))))), d, L2, N) && RG.px.tw(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{_}, a}, KMd.word(AD.view(U32, _), d, (x + 1 : U32)), KMd.word(AD.view(U32, _), d, (y + 1 : U32))))), d, L2)) == True{} : Bool}
  ll.k0(t0, d, L, L2, N, x, y, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), hft, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, {==}, {==},
    LAB.subst(Array<U32>, q => {RG.faces(L, AD.view(U32, q), d, L) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hF), LAB.subst(Array<U32>, q => {RG.px.off(L, AD.view(U32, q), d, L, N) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hO), LAB.subst(Array<U32>, q => {RG.px.tw(L, AD.view(U32, q), d, L) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hT), a)

def Laws.link_live(w, a, d, L, L2, N, x, y, hf, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, hF, hO, hT):
  ll.m(w, a, d, L, L2, N, x, y, hf, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, hF, hO, hT, LAT.mirror(U32, w))

def main() -> U32:
  0

# A leave's link (link_leave): a port p, its link word off every tracked
# node's words and the free list's head (RG.po.all over no live node),
# linked to the port a live node c faced. The word a live node of L2
# holds after: what it faced, or p where it faced c (sel)

def or_cases2(+a: Bool, +b: Bool, +c: Bool, h: {Bool.or(a, b) == True{} : Bool}, fa: {a == True{} : Bool} -> {c == True{} : Bool}, fb: {b == True{} : Bool} -> {c == True{} : Bool}) -> {c == True{} : Bool}:
  match a:
    case True{}:
      fa({==})
    case False{}:
      fb(h)



def or_r2(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb


def orfl(+a: Bool, +h: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, MB.false_ne_true()(h))


def or_l2(+a: Bool, b: Bool, +ha: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  ME.subst(Bool, zz => {Bool.or(zz, b) == True{} : Bool}, True{}, a, Equal.sym(Bool, a, True{}, ha), {==})

# p's facts over any live nodes

# p's link word off a tracked node's word 1
def pp1(N: List<&2, U32>, +p: U32, +d: Nat, +z: U32, +h: {RG.po.all(p, [], d, N) == True{} : Bool}, hz: {RG.has(N, z) == True{} : Bool}) -> {KMd.off.port(d, p, (z + 1 : U32)) == True{} : Bool}:
  match N:
    case Nil{}:
      Empty.absurd({KMd.off.port(d, p, (z + 1 : U32)) == True{} : Bool}, MB.false_ne_true()(hz))
    case Con{+n, +r}:
      or_cases2(U32.is_eq(n, z), RG.has(r, z), KMd.off.port(d, p, (z + 1 : U32)), hz,
        e => ME.subst(U32, zz => {KMd.off.port(d, p, (zz + 1 : U32)) == True{} : Bool}, n, z, MS.u32_eq_of_is_eq(n, z, e), and_l(KMd.off.port(d, p, (n + 1 : U32)), KMd.off.port(d, p, (n + 2 : U32)) && KMd.off.port(d, p, (n + 3 : U32)), and_r(KMd.off.port(d, p, n), KMd.off.port(d, p, (n + 1 : U32)) && (KMd.off.port(d, p, (n + 2 : U32)) && KMd.off.port(d, p, (n + 3 : U32))), and_l(RG.po.n(p, [], d, n), RG.po.all(p, [], d, r), h)))),
        e => pp1(r, p, d, z, and_r(RG.po.n(p, [], d, n), RG.po.all(p, [], d, r), h), e))

def pmono.n(+r: U32, +L: List<&2, U32>, +d: Nat, +n: U32, +h: {RG.po.n(r, [], d, n) == True{} : Bool}) -> {RG.po.n(r, L, d, n) == True{} : Bool}:
  and_intro(KMd.off.port(d, r, n), Bool.or(RG.has(L, n), KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32)))), and_l(KMd.off.port(d, r, n), KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32))), h), or_r2(RG.has(L, n), KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32))), and_r(KMd.off.port(d, r, n), KMd.off.port(d, r, (n + 1 : U32)) && (KMd.off.port(d, r, (n + 2 : U32)) && KMd.off.port(d, r, (n + 3 : U32))), h)))

def pmono(N: List<&2, U32>, +r: U32, +L: List<&2, U32>, +d: Nat, +h: {RG.po.all(r, [], d, N) == True{} : Bool}) -> {RG.po.all(r, L, d, N) == True{} : Bool}:
  match N:
    case Nil{}:
      h
    case Con{+n, +k}:
      and_intro(RG.po.n(r, L, d, n), RG.po.all(r, L, d, k), pmono.n(r, L, d, n, and_l(RG.po.n(r, [], d, n), RG.po.all(r, [], d, k), h)), pmono(k, r, L, d, and_r(RG.po.n(r, [], d, n), RG.po.all(r, [], d, k), h)))

def pk_sel2(+b: Bool, +f: U32, +q: U32, +d: Nat, +M: List<&2, U32>, +hf: {RG.port.ok(M, d, f) == True{} : Bool}, +hq: {RG.port.ok(M, d, q) == True{} : Bool}) -> {RG.port.ok(M, d, sel(b, f, q)) == True{} : Bool}:
  match b:
    case True{}:
      hf
    case False{}:
      hq

def lvf(ys: List<&2, U32>, +t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +c: U32, +p: U32, +su: Bool, +sw: Bool,
  +e1: {LAT.fromT(U32, t1) == lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) : Array<U32>}, +hsu: {P.is_static(p) == su : Bool}, +hsw: {P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) == sw : Bool}, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool},
  +hft1: {AD.full(U32, LAT.fromT(U32, t1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hc: {RG.has(L, c) == True{} : Bool},
  +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{c, L2}) == True{} : Bool}, +hc2: {RG.has(L2, c) == False{} : Bool}, +hpo: {RG.po.all(p, [], d, N) == True{} : Bool}, +hpk: {RG.port.ok(L, d, p) == True{} : Bool},
  +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hys: {RG.sub(ys, L2) == True{} : Bool}) -> {RG.faces(ys, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      +hz2 = and_l(RG.has(L2, z), RG.sub(r, L2), hys)
      +hzL = sub_has2(L2, L, z, hs1, hz2)
      +hzN = sub_has2(L, N, z, hLN, hzL)
      +hp1z = pp1(N, p, d, z, hpo, hzN)
      and_intro(RG.faces.m(List.get(&2, U32, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), AD.slot((z + 1 : U32), d)), d, L2), RG.faces(r, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2),
        fm_of_word(List.get(&2, U32, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), AD.slot((z + 1 : U32), d)), d, L2, ME.subst(Maybe<&2, U32>, m => {XP.is_some(m) == True{} : Bool}, Some{Pair.snd(Array<U32>, U32, Array.get(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p), (z + 1 : U32)))}, List.get(&2, U32, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), AD.slot((z + 1 : U32), d)), LA.get_view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p), d, (z + 1 : U32), lk_full(sw, LAT.fromT(U32, t1), d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p, hft1), hd32), {==}),
          ME.subst(U32, xx => {RG.port.ok(L2, d, xx) == True{} : Bool}, sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), Equal.trans(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), p), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), word_lk(sw, t1, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p, (z + 1 : U32), hsw, hft1, hd32), Equal.trans(U32, sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), p), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), sel(KMd.off.port(d, p, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), p), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), Equal.cong(U32, U32, qq => sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), qq, p), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), sel(KMd.off.port(d, p, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), Equal.trans(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), KMd.word(AD.view(U32, lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)))), d, (z + 1 : U32)), sel(KMd.off.port(d, p, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), Equal.cong(Array<U32>, U32, AA => KMd.word(AD.view(U32, AA), d, (z + 1 : U32)), LAT.fromT(U32, t1), lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), e1), word_lk(su, t0, d, p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32), hsu, hft, hd32))), Equal.cong(U32, U32, qq => sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), qq, p), sel(KMd.off.port(d, p, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), Equal.cong(Bool, U32, bb => sel(bb, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), KMd.off.port(d, p, (z + 1 : U32)), True{}, hp1z))))), pk_sel2(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p, d, L2, pk_sub(L2, L, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), hs1, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((z + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hF, hzL))), pk_sub(L2, L, d, p, hs1, hpk)))),
        lvf(r, t0, t1, d, L, L2, N, c, p, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, and_r(RG.has(L2, z), RG.sub(r, L2), hys)))

def lvo.k(+b: Bool, +z: U32, +t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +c: U32, +p: U32, +su: Bool, +sw: Bool,
  +e1: {LAT.fromT(U32, t1) == lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) : Array<U32>}, +hsu: {P.is_static(p) == su : Bool}, +hsw: {P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) == sw : Bool}, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool},
  +hft1: {AD.full(U32, LAT.fromT(U32, t1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hc: {RG.has(L, c) == True{} : Bool},
  +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{c, L2}) == True{} : Bool}, +hc2: {RG.has(L2, c) == False{} : Bool}, +hpo: {RG.po.all(p, [], d, N) == True{} : Bool}, +hpk: {RG.port.ok(L, d, p) == True{} : Bool},
  +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +he: {KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)) == b : Bool}, +hzL: {RG.has(L, z) == True{} : Bool}) -> {RG.po.all(sel(b, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), L2, d, N) == True{} : Bool}:
  match b:
    case True{}:
      po_shrink(N, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), L, L2, c, c, d, po_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N, z, hO, hzL), sub_cons2(L, c, Con{c, L2}, hs2), and_intro(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (c + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (c + 2 : U32)) && KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (c + 3 : U32)), orfl(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (c + 1 : U32)), ME.subst(Bool, bb => {Bool.or(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (c + 1 : U32)), Bool.not(bb)) == True{} : Bool}, KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), True{}, he, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d, c, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hT, hzL)), hc))), and_intro(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (c + 2 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (c + 3 : U32)), pk2(L, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), c, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((z + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hF, hzL)), hc), pk3(L, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), c, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((z + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hF, hzL)), hc))), and_intro(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (c + 1 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (c + 2 : U32)) && KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (c + 3 : U32)), orfl(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (c + 1 : U32)), ME.subst(Bool, bb => {Bool.or(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (c + 1 : U32)), Bool.not(bb)) == True{} : Bool}, KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), True{}, he, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d, c, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hT, hzL)), hc))), and_intro(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (c + 2 : U32)), KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (c + 3 : U32)), pk2(L, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), c, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((z + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hF, hzL)), hc), pk3(L, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), c, fm_word(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((z + 1 : U32), d)), d, L, fm_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hF, hzL)), hc))))
    case False{}:
      pmono(N, p, L2, d, hpo)

def lvo(ys: List<&2, U32>, +t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +c: U32, +p: U32, +su: Bool, +sw: Bool,
  +e1: {LAT.fromT(U32, t1) == lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) : Array<U32>}, +hsu: {P.is_static(p) == su : Bool}, +hsw: {P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) == sw : Bool}, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool},
  +hft1: {AD.full(U32, LAT.fromT(U32, t1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hc: {RG.has(L, c) == True{} : Bool},
  +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{c, L2}) == True{} : Bool}, +hc2: {RG.has(L2, c) == False{} : Bool}, +hpo: {RG.po.all(p, [], d, N) == True{} : Bool}, +hpk: {RG.port.ok(L, d, p) == True{} : Bool},
  +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hys: {RG.sub(ys, L2) == True{} : Bool}) -> {RG.px.off(ys, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2, N) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      +hz2 = and_l(RG.has(L2, z), RG.sub(r, L2), hys)
      +hzL = sub_has2(L2, L, z, hs1, hz2)
      +hzN = sub_has2(L, N, z, hLN, hzL)
      +hp1z = pp1(N, p, d, z, hpo, hzN)
      and_intro(RG.po.all(KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), L2, d, N), RG.px.off(r, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2, N),
        ME.subst(U32, xx => {RG.po.all(xx, L2, d, N) == True{} : Bool}, sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), Equal.trans(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), p), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), word_lk(sw, t1, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p, (z + 1 : U32), hsw, hft1, hd32), Equal.trans(U32, sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), p), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), sel(KMd.off.port(d, p, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), p), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), Equal.cong(U32, U32, qq => sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), qq, p), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), sel(KMd.off.port(d, p, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), Equal.trans(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), KMd.word(AD.view(U32, lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)))), d, (z + 1 : U32)), sel(KMd.off.port(d, p, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), Equal.cong(Array<U32>, U32, AA => KMd.word(AD.view(U32, AA), d, (z + 1 : U32)), LAT.fromT(U32, t1), lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), e1), word_lk(su, t0, d, p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32), hsu, hft, hd32))), Equal.cong(U32, U32, qq => sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), qq, p), sel(KMd.off.port(d, p, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), Equal.cong(Bool, U32, bb => sel(bb, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), KMd.off.port(d, p, (z + 1 : U32)), True{}, hp1z))))), lvo.k(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), z, t0, t1, d, L, L2, N, c, p, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, {==}, hzL)),
        lvo(r, t0, t1, d, L, L2, N, c, p, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, and_r(RG.has(L2, z), RG.sub(r, L2), hys)))

def lvt.e(+b: Bool, +z: U32, +q: U32, +t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +c: U32, +p: U32, +su: Bool, +sw: Bool,
  +e1: {LAT.fromT(U32, t1) == lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) : Array<U32>}, +hsu: {P.is_static(p) == su : Bool}, +hsw: {P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) == sw : Bool}, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool},
  +hft1: {AD.full(U32, LAT.fromT(U32, t1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hc: {RG.has(L, c) == True{} : Bool},
  +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{c, L2}) == True{} : Bool}, +hc2: {RG.has(L2, c) == False{} : Bool}, +hpo: {RG.po.all(p, [], d, N) == True{} : Bool}, +hpk: {RG.port.ok(L, d, p) == True{} : Bool},
  +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +he: {KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (q + 1 : U32)) == b : Bool}, +hzL: {RG.has(L, z) == True{} : Bool}, +hqL: {RG.has(L, q) == True{} : Bool}, +hz2: {RG.has(L2, z) == True{} : Bool}, +hcN: {RG.has(N, c) == True{} : Bool}, +hzN: {RG.has(N, z) == True{} : Bool}) ->
  {Bool.or(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (q + 1 : U32)), Bool.not(KMd.off.port(d, sel(b, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), p), (z + 1 : U32)))) == True{} : Bool}:
  match b:
    case True{}:
      tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d, q, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hT, hzL)), hqL)
    case False{}:
      or_l2(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (q + 1 : U32)), Bool.not(KMd.off.port(d, p, (z + 1 : U32))), orfl(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (q + 1 : U32)), ME.subst(Bool, bb => {Bool.or(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (q + 1 : U32)), Bool.not(bb)) == True{} : Bool}, KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (z + 1 : U32)), True{}, ME.subst(Bool, bb => {Bool.or(bb, KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (z + 1 : U32))) == True{} : Bool}, KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (c + 1 : U32)), False{}, MB.eq_false_of_not_eq_true(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (c + 1 : U32)), ME.subst(Bool, bb => {Bool.or(bb, Bool.not(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), (c + 1 : U32)))) == True{} : Bool}, KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (q + 1 : U32)), False{}, he, tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), c, AD.view(U32, LAT.fromT(U32, t0)), d, q, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (c + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), c, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, c, hT, hc)), hqL))), no2(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), c, z, d, N, hN, hcN, hzN, ueq_ne(z, c, nhas(L2, z, c, hz2, hc2)))), tw_at(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d, q, and_r(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hT, hzL)), hqL))))

def lvt.q(Q: List<&2, U32>, +z: U32, +t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +c: U32, +p: U32, +su: Bool, +sw: Bool,
  +e1: {LAT.fromT(U32, t1) == lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) : Array<U32>}, +hsu: {P.is_static(p) == su : Bool}, +hsw: {P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) == sw : Bool}, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool},
  +hft1: {AD.full(U32, LAT.fromT(U32, t1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hc: {RG.has(L, c) == True{} : Bool},
  +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{c, L2}) == True{} : Bool}, +hc2: {RG.has(L2, c) == False{} : Bool}, +hpo: {RG.po.all(p, [], d, N) == True{} : Bool}, +hpk: {RG.port.ok(L, d, p) == True{} : Bool},
  +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hzL: {RG.has(L, z) == True{} : Bool}, +hz2: {RG.has(L2, z) == True{} : Bool}, +hcN: {RG.has(N, c) == True{} : Bool}, +hzN: {RG.has(N, z) == True{} : Bool}, +hQ: {RG.sub(Q, L2) == True{} : Bool}) ->
  {RG.tw.q(Q, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d) == True{} : Bool}:
  match Q:
    case Nil{}:
      {==}
    case Con{+q, +k}:
      +hq2 = and_l(RG.has(L2, q), RG.sub(k, L2), hQ)
      +hqL = sub_has2(L2, L, q, hs1, hq2)
      +hqN = sub_has2(L, N, q, hLN, hqL)
      +hp1q = pp1(N, p, d, q, hpo, hqN)
      and_intro(Bool.or(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (q + 1 : U32)), (z + 1 : U32)))), RG.tw.q(k, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d),
        ME.subst(U32, xx => {Bool.or(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (q + 1 : U32)), Bool.not(KMd.off.port(d, xx, (z + 1 : U32)))) == True{} : Bool}, sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), p), KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (q + 1 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (q + 1 : U32)), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), p), Equal.trans(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (q + 1 : U32)), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (q + 1 : U32)), p), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), p), word_lk(sw, t1, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p, (q + 1 : U32), hsw, hft1, hd32), Equal.trans(U32, sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (q + 1 : U32)), p), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (q + 1 : U32)), sel(KMd.off.port(d, p, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), p), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), p), Equal.cong(U32, U32, qq => sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (q + 1 : U32)), qq, p), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (q + 1 : U32)), sel(KMd.off.port(d, p, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), Equal.trans(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (q + 1 : U32)), KMd.word(AD.view(U32, lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)))), d, (q + 1 : U32)), sel(KMd.off.port(d, p, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), Equal.cong(Array<U32>, U32, AA => KMd.word(AD.view(U32, AA), d, (q + 1 : U32)), LAT.fromT(U32, t1), lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), e1), word_lk(su, t0, d, p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (q + 1 : U32), hsu, hft, hd32))), Equal.cong(U32, U32, qq => sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (q + 1 : U32)), qq, p), sel(KMd.off.port(d, p, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), Equal.cong(Bool, U32, bb => sel(bb, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (q + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), KMd.off.port(d, p, (q + 1 : U32)), True{}, hp1q))))), lvt.e(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (q + 1 : U32)), z, q, t0, t1, d, L, L2, N, c, p, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, {==}, hzL, hqL, hz2, hcN, hzN)),
        lvt.q(k, z, t0, t1, d, L, L2, N, c, p, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, hzL, hz2, hcN, hzN, and_r(RG.has(L2, q), RG.sub(k, L2), hQ)))

def lvt.p(Q: List<&2, U32>, +z: U32, +t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +c: U32, +p: U32, +su: Bool, +sw: Bool,
  +e1: {LAT.fromT(U32, t1) == lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) : Array<U32>}, +hsu: {P.is_static(p) == su : Bool}, +hsw: {P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) == sw : Bool}, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool},
  +hft1: {AD.full(U32, LAT.fromT(U32, t1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hc: {RG.has(L, c) == True{} : Bool},
  +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{c, L2}) == True{} : Bool}, +hc2: {RG.has(L2, c) == False{} : Bool}, +hpo: {RG.po.all(p, [], d, N) == True{} : Bool}, +hpk: {RG.port.ok(L, d, p) == True{} : Bool},
  +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hQ: {RG.sub(Q, L2) == True{} : Bool}) -> {RG.tw.q(Q, p, z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d) == True{} : Bool}:
  match Q:
    case Nil{}:
      {==}
    case Con{+q, +k}:
      and_intro(Bool.or(KMd.off.port(d, p, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (q + 1 : U32)), (z + 1 : U32)))), RG.tw.q(k, p, z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d),
        or_l2(KMd.off.port(d, p, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (q + 1 : U32)), (z + 1 : U32))), pp1(N, p, d, q, hpo, sub_has2(L, N, q, hLN, sub_has2(L2, L, q, hs1, and_l(RG.has(L2, q), RG.sub(k, L2), hQ))))),
        lvt.p(k, z, t0, t1, d, L, L2, N, c, p, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, and_r(RG.has(L2, q), RG.sub(k, L2), hQ)))

def lvt.k(+b: Bool, +z: U32, +t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +c: U32, +p: U32, +su: Bool, +sw: Bool,
  +e1: {LAT.fromT(U32, t1) == lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) : Array<U32>}, +hsu: {P.is_static(p) == su : Bool}, +hsw: {P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) == sw : Bool}, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool},
  +hft1: {AD.full(U32, LAT.fromT(U32, t1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hc: {RG.has(L, c) == True{} : Bool},
  +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{c, L2}) == True{} : Bool}, +hc2: {RG.has(L2, c) == False{} : Bool}, +hpo: {RG.po.all(p, [], d, N) == True{} : Bool}, +hpk: {RG.port.ok(L, d, p) == True{} : Bool},
  +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +he: {KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)) == b : Bool}, +hzL: {RG.has(L, z) == True{} : Bool}, +hz2: {RG.has(L2, z) == True{} : Bool}, +hcN: {RG.has(N, c) == True{} : Bool}, +hzN: {RG.has(N, z) == True{} : Bool}, +hp1z: {KMd.off.port(d, p, (z + 1 : U32)) == True{} : Bool}) ->
  {KMd.off.port(d, sel(b, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), (z + 1 : U32)) && RG.tw.q(L2, sel(b, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d) == True{} : Bool}:
  match b:
    case True{}:
      and_intro(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L2, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d), and_l(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), z, AD.view(U32, LAT.fromT(U32, t0)), d), ns_of(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, z, hT, hzL)), lvt.q(L2, z, t0, t1, d, L, L2, N, c, p, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, hzL, hz2, hcN, hzN, sub_refl2(L2)))
    case False{}:
      and_intro(KMd.off.port(d, p, (z + 1 : U32)), RG.tw.q(L2, p, z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d), hp1z, lvt.p(L2, z, t0, t1, d, L, L2, N, c, p, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, sub_refl2(L2)))

def lvt(ys: List<&2, U32>, +t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +c: U32, +p: U32, +su: Bool, +sw: Bool,
  +e1: {LAT.fromT(U32, t1) == lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) : Array<U32>}, +hsu: {P.is_static(p) == su : Bool}, +hsw: {P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) == sw : Bool}, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool},
  +hft1: {AD.full(U32, LAT.fromT(U32, t1), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hc: {RG.has(L, c) == True{} : Bool},
  +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{c, L2}) == True{} : Bool}, +hc2: {RG.has(L2, c) == False{} : Bool}, +hpo: {RG.po.all(p, [], d, N) == True{} : Bool}, +hpk: {RG.port.ok(L, d, p) == True{} : Bool},
  +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hys: {RG.sub(ys, L2) == True{} : Bool}) -> {RG.px.tw(ys, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      +hz2 = and_l(RG.has(L2, z), RG.sub(r, L2), hys)
      +hzL = sub_has2(L2, L, z, hs1, hz2)
      +hzN = sub_has2(L, N, z, hLN, hzL)
      +hp1z = pp1(N, p, d, z, hpo, hzN)
      +hcN = sub_has2(L, N, c, hLN, hc)
      +hk = ME.subst(U32, xx => {KMd.off.port(d, xx, (z + 1 : U32)) && RG.tw.q(L2, xx, z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d) == True{} : Bool}, sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), Equal.trans(U32, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), p), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), word_lk(sw, t1, d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p, (z + 1 : U32), hsw, hft1, hd32), Equal.trans(U32, sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), p), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), sel(KMd.off.port(d, p, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), p), sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), p), Equal.cong(U32, U32, qq => sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), qq, p), KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), sel(KMd.off.port(d, p, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), Equal.trans(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t1)), d, (z + 1 : U32)), KMd.word(AD.view(U32, lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)))), d, (z + 1 : U32)), sel(KMd.off.port(d, p, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), Equal.cong(Array<U32>, U32, AA => KMd.word(AD.view(U32, AA), d, (z + 1 : U32)), LAT.fromT(U32, t1), lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), e1), word_lk(su, t0, d, p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32), hsu, hft, hd32))), Equal.cong(U32, U32, qq => sel(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), qq, p), sel(KMd.off.port(d, p, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), Equal.cong(Bool, U32, bb => sel(bb, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), KMd.off.port(d, p, (z + 1 : U32)), True{}, hp1z))))), lvt.k(KMd.off.port(d, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), (z + 1 : U32)), z, t0, t1, d, L, L2, N, c, p, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, {==}, hzL, hz2, hcN, hzN, hp1z))
      and_intro(KMd.off.port(d, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L2, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d) && RG.px.tw(r, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2), and_l(KMd.off.port(d, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L2, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d), hk),
        and_intro(RG.tw.q(L2, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d), RG.px.tw(r, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2), and_r(KMd.off.port(d, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), (z + 1 : U32)), RG.tw.q(L2, KMd.word(AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, (z + 1 : U32)), z, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d), hk), lvt(r, t0, t1, d, L, L2, N, c, p, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, and_r(RG.has(L2, z), RG.sub(r, L2), hys))))

def lv.k1(+t0: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +c: U32, +p: U32, +su: Bool, +sw: Bool, +hsu: {P.is_static(p) == su : Bool}, +hsw: {P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) == sw : Bool}, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool},
  +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hc: {RG.has(L, c) == True{} : Bool}, +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{c, L2}) == True{} : Bool},
  +hc2: {RG.has(L2, c) == False{} : Bool}, +hpo: {RG.po.all(p, [], d, N) == True{} : Bool}, +hpk: {RG.port.ok(L, d, p) == True{} : Bool}, +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool},
  -w1: Array<U32>, +hw1: {w1 == lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))) : Array<U32>}, hf1: {AD.full(U32, w1, d) == True{} : Bool}, m1: LAT.Mirror(U32, w1)) -> {RG.faces(L2, AD.view(U32, lk(sw, w1, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2) && (RG.px.off(L2, AD.view(U32, lk(sw, w1, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2, N) && RG.px.tw(L2, AD.view(U32, lk(sw, w1, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2)) == True{} : Bool}:
  (+t1, +e0) = m1
  +hft1 = LAP.full_t(U32, w1, t1, d, e0, hf1)
  +e1 = Equal.trans(Array<U32>, LAT.fromT(U32, t1), w1, lk(su, LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), e0, hw1)
  %e0 : {RG.faces(L2, AD.view(U32, lk(sw, _, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2) && (RG.px.off(L2, AD.view(U32, lk(sw, _, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2, N) && RG.px.tw(L2, AD.view(U32, lk(sw, _, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2)) == True{} : Bool}
  and_intro(RG.faces(L2, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2), RG.px.off(L2, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2, N) && RG.px.tw(L2, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2), lvf(L2, t0, t1, d, L, L2, N, c, p, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, sub_refl2(L2)),
    and_intro(RG.px.off(L2, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2, N), RG.px.tw(L2, AD.view(U32, lk(sw, LAT.fromT(U32, t1), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)), d, L2), lvo(L2, t0, t1, d, L, L2, N, c, p, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, sub_refl2(L2)), lvt(L2, t0, t1, d, L, L2, N, c, p, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, sub_refl2(L2))))

def lv.k0(+t0: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +c: U32, +p: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hc: {RG.has(L, c) == True{} : Bool}, +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{c, L2}) == True{} : Bool},
  +hc2: {RG.has(L2, c) == False{} : Bool}, +hpo: {RG.po.all(p, [], d, N) == True{} : Bool}, +hpk: {RG.port.ok(L, d, p) == True{} : Bool}, +hF: {RG.faces(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, +hO: {RG.px.off(L, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hT: {RG.px.tw(L, AD.view(U32, LAT.fromT(U32, t0)), d, L) == True{} : Bool}, -a: Array<V.Val>) ->
  {RG.faces(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))))), d, L2) && (RG.px.off(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))))), d, L2, N) && RG.px.tw(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))))), d, L2)) == True{} : Bool}:
  %Equal.sym(P.H, P.link.to(P.is_static(p), P.H{KM.MG{LAT.fromT(U32, t0)}, a}, p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), P.H{KM.MG{lk(P.is_static(p), LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)))}, a}, lt_eq(P.is_static(p), LAT.fromT(U32, t0), a, p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)))) :
    {RG.faces(L2, AD.view(U32, KMd.words(P.link.to(P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), _, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p))), d, L2) && (RG.px.off(L2, AD.view(U32, KMd.words(P.link.to(P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), _, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p))), d, L2, N) && RG.px.tw(L2, AD.view(U32, KMd.words(P.link.to(P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), _, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p))), d, L2)) == True{} : Bool}
  %Equal.sym(P.H, P.link.to(P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), P.H{KM.MG{lk(P.is_static(p), LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)))}, a}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p), P.H{KM.MG{lk(P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), lk(P.is_static(p), LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)}, a}, lt_eq(P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), lk(P.is_static(p), LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), a, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), p)) :
    {RG.faces(L2, AD.view(U32, KMd.words(_)), d, L2) && (RG.px.off(L2, AD.view(U32, KMd.words(_)), d, L2, N) && RG.px.tw(L2, AD.view(U32, KMd.words(_)), d, L2)) == True{} : Bool}
  lv.k1(t0, d, L, L2, N, c, p, P.is_static(p), P.is_static(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), {==}, {==}, hft, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, lk(P.is_static(p), LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32))), {==}, lk_full(P.is_static(p), LAT.fromT(U32, t0), d, p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)), hft), LAT.mirror(U32, lk(P.is_static(p), LAT.fromT(U32, t0), p, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (c + 1 : U32)))))

def lv.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +c: U32, +p: U32, hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool}, +hLN: {RG.sub(L, N) == True{} : Bool}, +hc: {RG.has(L, c) == True{} : Bool}, +hs1: {RG.sub(L2, L) == True{} : Bool}, +hs2: {RG.sub(L, Con{c, L2}) == True{} : Bool},
  +hc2: {RG.has(L2, c) == False{} : Bool}, +hpo: {RG.po.all(p, [], d, N) == True{} : Bool}, +hpk: {RG.port.ok(L, d, p) == True{} : Bool}, hF: {RG.faces(L, AD.view(U32, w), d, L) == True{} : Bool}, hO: {RG.px.off(L, AD.view(U32, w), d, L, N) == True{} : Bool}, hT: {RG.px.tw(L, AD.view(U32, w), d, L) == True{} : Bool},
  m: LAT.Mirror(U32, w)) -> {RG.faces(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{w}, a}, p, KMd.word(AD.view(U32, w), d, (c + 1 : U32))))), d, L2) && (RG.px.off(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{w}, a}, p, KMd.word(AD.view(U32, w), d, (c + 1 : U32))))), d, L2, N) && RG.px.tw(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{w}, a}, p, KMd.word(AD.view(U32, w), d, (c + 1 : U32))))), d, L2)) == True{} : Bool}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e)
  %e : {RG.faces(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{_}, a}, p, KMd.word(AD.view(U32, _), d, (c + 1 : U32))))), d, L2) && (RG.px.off(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{_}, a}, p, KMd.word(AD.view(U32, _), d, (c + 1 : U32))))), d, L2, N) && RG.px.tw(L2, AD.view(U32, KMd.words(P.link_xx(P.H{KM.MG{_}, a}, p, KMd.word(AD.view(U32, _), d, (c + 1 : U32))))), d, L2)) == True{} : Bool}
  lv.k0(t0, d, L, L2, N, c, p, hft, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk,
    LAB.subst(Array<U32>, q => {RG.faces(L, AD.view(U32, q), d, L) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hF), LAB.subst(Array<U32>, q => {RG.px.off(L, AD.view(U32, q), d, L, N) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hO), LAB.subst(Array<U32>, q => {RG.px.tw(L, AD.view(U32, q), d, L) == True{} : Bool}, w, LAT.fromT(U32, t0), ew, hT), a)

def Laws.link_leave(w, a, d, L, L2, N, c, p, hf, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT):
  lv.m(w, a, d, L, L2, N, c, p, hf, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, LAT.mirror(U32, w))
