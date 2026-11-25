# glam/proofgen's alignment lemmas (cells-freeze.sharing.cursors.index
# .ring.premises.implied): a static port's link word and a base's words 2
# and 3 in different slots, at a depth of 2 or more. Kept by hand, checked
# as itself by the gate, and imported by glam/PROOF.bend as AL
# (gen_align.py; cursor-laws.proofs.shared.align).
import Base
import ../../../spike/kprim.bend as P
import ../../../spike/kmodel.bend as KMd
import ../../../glam/ring_model.bend as RG
import ../../../glam/serve_model.bend as SV
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import ../../../vendor/bend-mathlib/u32_eq.bend as MS
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MN
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/PROOF.bend as LAP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/LAWS.bend as LA
import 0x96ab58f86121cb4f3fb48b3c8a045989/LAWS.bend as WL
import 0x96ab58f86121cb4f3fb48b3c8a045989/PROOF.bend as WP
import 0x96ab58f86121cb4f3fb48b3c8a045989/defs.bend as WD

# a static's word modulo 4 is 3
def st_mod4(+r: U32, +h: {P.is_static(r) == True{} : Bool}) -> {Nat.mod(U32.to_nat(r), 4n) == 3n : Nat}:
  Equal.trans(Nat, Nat.mod(U32.to_nat(r), 4n), U32.to_nat(U32.and(r, 3)), 3n,
    Equal.sym(Nat, U32.to_nat(U32.and(r, 3)), Nat.mod(U32.to_nat(r), 4n), WL.to_nat_and_mask(r, 3, 2n, {==})),
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.and(r, 3), 3, MS.u32_eq_of_is_eq(U32.and(r, 3), 3, h)))

def and_not_and(+p: Bool, +q: Bool, +b: Bool) -> {((p && (q && Bool.not(b))) && b) == False{} : Bool}:
  match p:
    case True{}:
      match q:
        case True{}:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          {==}
    case False{}:
      {==}

def bit_zero(+k: Nat) -> {WD.bit(0, k) == False{} : Bool}:
  %Equal.sym(Nat, Nat.div(0n, Nat.pow(2n, k)), 0n, WL.nat_div_small(0n, Nat.pow(2n, k), MN.pow_pos(k, 1n))) : {Nat.is_eq(Nat.mod(_, 2n), 1n) == False{} : Bool}
  {==}

# a base's low two bits clear: (y & ~3) & 3 is 0, bit by bit (the mask
# written U32.not(3): a bit of the literal expands it in unary)
def base_and3.b(+y: U32, +k: Nat) -> {WD.bit(U32.and(U32.and(y, U32.not(3)), 3), k) == WD.bit(0, k) : Bool}:
  +e1 = WL.bit_and(U32.and(y, U32.not(3)), 3, k)
  +e2 = Equal.cong(Bool, Bool, z => (z && WD.bit(3, k)), WD.bit(U32.and(y, U32.not(3)), k), (WD.bit(y, k) && WD.bit(U32.not(3), k)), WL.bit_and(y, U32.not(3), k))
  +e3 = Equal.cong(Bool, Bool, z => ((WD.bit(y, k) && z) && WD.bit(3, k)), WD.bit(U32.not(3), k), (Nat.is_lt(k, 32n) && Bool.not(WD.bit(3, k))), WL.bit_not(3, k))
  +e4 = and_not_and(WD.bit(y, k), Nat.is_lt(k, 32n), WD.bit(3, k))
  Equal.trans(Bool, WD.bit(U32.and(U32.and(y, U32.not(3)), 3), k), (WD.bit(U32.and(y, U32.not(3)), k) && WD.bit(3, k)), WD.bit(0, k), e1,
    Equal.trans(Bool, (WD.bit(U32.and(y, U32.not(3)), k) && WD.bit(3, k)), ((WD.bit(y, k) && WD.bit(U32.not(3), k)) && WD.bit(3, k)), WD.bit(0, k), e2,
      Equal.trans(Bool, ((WD.bit(y, k) && WD.bit(U32.not(3), k)) && WD.bit(3, k)), ((WD.bit(y, k) && (Nat.is_lt(k, 32n) && Bool.not(WD.bit(3, k)))) && WD.bit(3, k)), WD.bit(0, k), e3,
        Equal.trans(Bool, ((WD.bit(y, k) && (Nat.is_lt(k, 32n) && Bool.not(WD.bit(3, k)))) && WD.bit(3, k)), False{}, WD.bit(0, k), e4, Equal.sym(Bool, WD.bit(0, k), False{}, bit_zero(k))))))

def base_and3(+y: U32) -> {U32.and(U32.and(y, U32.not(3)), 3) == 0 : U32}:
  WL.bit_ext(U32.and(U32.and(y, U32.not(3)), 3), 0, k => base_and3.b(y, k))

# a base's word and 3 is 0
def base_lo(+y: U32, +h: {U32.is_eq(P.base(y), y) == True{} : Bool}) -> {U32.and(y, 3) == 0 : U32}:
  Equal.trans(U32, U32.and(y, 3), U32.and(P.base(y), 3), 0,
    Equal.cong(U32, U32, z => U32.and(z, 3), y, P.base(y), Equal.sym(U32, P.base(y), y, MS.u32_eq_of_is_eq(P.base(y), y, h))), base_and3(y))

# a base is no static
def dyn_one(+y: U32, +h: {U32.is_eq(P.base(y), y) == True{} : Bool}) -> {P.is_static(y) == False{} : Bool}:
  Equal.cong(U32, Bool, z => U32.is_eq(z, 3), U32.and(y, 3), 0, base_lo(y, h))

# a base's word modulo 4 is 0
def base_mod4(+y: U32, +h: {U32.is_eq(P.base(y), y) == True{} : Bool}) -> {Nat.mod(U32.to_nat(y), 4n) == 0n : Nat}:
  Equal.trans(Nat, Nat.mod(U32.to_nat(y), 4n), U32.to_nat(U32.and(y, 3)), 0n,
    Equal.sym(Nat, U32.to_nat(U32.and(y, 3)), Nat.mod(U32.to_nat(y), 4n), WL.to_nat_and_mask(y, 3, 2n, {==})),
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.and(y, 3), 0, base_lo(y, h)))

# a slot at a depth of 2 or more keeps a word modulo 4
def slot_mod4(+i: U32, +d: Nat, +h2: {Nat.is_le(2n, d) == True{} : Bool}) -> {Nat.mod(AD.slot(i, d), 4n) == Nat.mod(U32.to_nat(i), 4n) : Nat}:
  WL.nat_mod_mod_pow(U32.to_nat(i), 2n, d, h2)

# a sum of words modulo 4 (2^32 abstracted as m, as lawful-words does:
# the checker would expand it in unary; each motive in its law's syntax)
def add_mod4.k(-m: Nat, +e: {Nat.pow(2n, 32n) == m : Nat}, +r: U32, +j: U32) -> {Nat.mod(U32.to_nat(U32.add(r, j)), Nat.pow(2n, 2n)) == Nat.mod(Nat.add(U32.to_nat(r), U32.to_nat(j)), Nat.pow(2n, 2n)) : Nat}:
  +e1 = ME.subst(Nat, w => {U32.to_nat(U32.add(r, j)) == Nat.mod(Nat.add(U32.to_nat(r), U32.to_nat(j)), w) : Nat}, Nat.pow(2n, 32n), m, e, WL.to_nat_add(r, j))
  +e2 = ME.subst(Nat, w => {Nat.mod(Nat.mod(Nat.add(U32.to_nat(r), U32.to_nat(j)), w), Nat.pow(2n, 2n)) == Nat.mod(Nat.add(U32.to_nat(r), U32.to_nat(j)), Nat.pow(2n, 2n)) : Nat}, Nat.pow(2n, 32n), m, e, WL.nat_mod_mod_pow(Nat.add(U32.to_nat(r), U32.to_nat(j)), 2n, 32n, {==}))
  Equal.trans(Nat, Nat.mod(U32.to_nat(U32.add(r, j)), Nat.pow(2n, 2n)), Nat.mod(Nat.mod(Nat.add(U32.to_nat(r), U32.to_nat(j)), m), Nat.pow(2n, 2n)), Nat.mod(Nat.add(U32.to_nat(r), U32.to_nat(j)), Nat.pow(2n, 2n)),
    Equal.cong(Nat, Nat, z => Nat.mod(z, Nat.pow(2n, 2n)), U32.to_nat(U32.add(r, j)), Nat.mod(Nat.add(U32.to_nat(r), U32.to_nat(j)), m), e1), e2)

def add_mod4(+r: U32, +j: U32) -> {Nat.mod(U32.to_nat((r + j : U32)), 4n) == Nat.mod(Nat.add(U32.to_nat(r), U32.to_nat(j)), 4n) : Nat}:
  add_mod4.k(Nat.pow(2n, 32n), {==}, r, j)

# a of residue m modulo 4, j added: a's quotient's multiple, m + j added
def mod4_shift(+a: Nat, +m: Nat, +j: Nat, +hm: {Nat.mod(a, 4n) == m : Nat}) ->
  {Nat.mod(Nat.add(a, j), 4n) == Nat.mod(Nat.add(Nat.mul(Nat.div(a, 4n), 4n), Nat.add(m, j)), 4n) : Nat}:
  +q = Nat.mul(Nat.div(a, 4n), 4n)
  +ea = Equal.trans(Nat, Nat.add(q, m), Nat.add(q, Nat.mod(a, 4n)), a, Equal.cong(Nat, Nat, z => Nat.add(q, z), m, Nat.mod(a, 4n), Equal.sym(Nat, Nat.mod(a, 4n), m, hm)), WL.nat_div_mod(a, 4n))
  Equal.trans(Nat, Nat.mod(Nat.add(a, j), 4n), Nat.mod(Nat.add(Nat.add(q, m), j), 4n), Nat.mod(Nat.add(q, Nat.add(m, j)), 4n),
    Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(z, j), 4n), a, Nat.add(q, m), Equal.sym(Nat, Nat.add(q, m), a, ea)),
    Equal.cong(Nat, Nat, z => Nat.mod(z, 4n), Nat.add(Nat.add(q, m), j), Nat.add(q, Nat.add(m, j)), WL.nat_add_assoc(q, m, j)))

# a static's link word's slot modulo 4 is 0
def slot_st1(+r: U32, +d: Nat, +h2: {Nat.is_le(2n, d) == True{} : Bool}, +hs: {P.is_static(r) == True{} : Bool}) -> {Nat.mod(AD.slot((r + 1 : U32), d), 4n) == 0n : Nat}:
  +a = U32.to_nat(r)
  +q = Nat.mul(Nat.div(a, 4n), 4n)
  Equal.trans(Nat, Nat.mod(AD.slot((r + 1 : U32), d), 4n), Nat.mod(U32.to_nat((r + 1 : U32)), 4n), 0n, slot_mod4((r + 1 : U32), d, h2),
    Equal.trans(Nat, Nat.mod(U32.to_nat((r + 1 : U32)), 4n), Nat.mod(Nat.add(a, 1n), 4n), 0n, add_mod4(r, 1),
      Equal.trans(Nat, Nat.mod(Nat.add(a, 1n), 4n), Nat.mod(Nat.add(q, 4n), 4n), 0n, mod4_shift(a, 3n, 1n, st_mod4(r, hs)),
        Equal.trans(Nat, Nat.mod(Nat.add(q, 4n), 4n), Nat.mod(Nat.add(4n, q), 4n), 0n, Equal.cong(Nat, Nat, z => Nat.mod(z, 4n), Nat.add(q, 4n), Nat.add(4n, q), WL.nat_add_comm(q, 4n)),
          WL.nat_mul_mod(1n+Nat.div(a, 4n), 4n)))))

# a base's word j's slot modulo 4 is j, for j below 4
def slot_base(+y: U32, +d: Nat, +j: U32, +h2: {Nat.is_le(2n, d) == True{} : Bool}, +hb: {U32.is_eq(P.base(y), y) == True{} : Bool}, +hj: {Nat.is_lt(U32.to_nat(j), 4n) == True{} : Bool}) ->
  {Nat.mod(AD.slot((y + j : U32), d), 4n) == U32.to_nat(j) : Nat}:
  +a = U32.to_nat(y)
  Equal.trans(Nat, Nat.mod(AD.slot((y + j : U32), d), 4n), Nat.mod(U32.to_nat((y + j : U32)), 4n), U32.to_nat(j), slot_mod4((y + j : U32), d, h2),
    Equal.trans(Nat, Nat.mod(U32.to_nat((y + j : U32)), 4n), Nat.mod(Nat.add(a, U32.to_nat(j)), 4n), U32.to_nat(j), add_mod4(y, j),
      Equal.trans(Nat, Nat.mod(Nat.add(a, U32.to_nat(j)), 4n), Nat.mod(Nat.add(Nat.mul(Nat.div(a, 4n), 4n), U32.to_nat(j)), 4n), U32.to_nat(j), mod4_shift(a, 0n, U32.to_nat(j), base_mod4(y, hb)),
        WL.nat_mod_mul_add(Nat.div(a, 4n), 4n, U32.to_nat(j), hj))))

# two numbers of residues apart are apart
def ne_mod4.k(+e: Bool, +x: Nat, +z: Nat, +mx: Nat, +mz: Nat, +he: {Nat.is_eq(x, z) == e : Bool}, +hx: {Nat.mod(x, 4n) == mx : Nat}, +hz: {Nat.mod(z, 4n) == mz : Nat},
  +hne: {Nat.is_eq(mx, mz) == False{} : Bool}) -> {Bool.not(e) == True{} : Bool}:
  match e:
    case True{}:
      +emm = Equal.trans(Nat, mx, Nat.mod(x, 4n), mz, Equal.sym(Nat, Nat.mod(x, 4n), mx, hx),
        Equal.trans(Nat, Nat.mod(x, 4n), Nat.mod(z, 4n), mz, Equal.cong(Nat, Nat, w => Nat.mod(w, 4n), x, z, MN.eq_of_is_eq(x, z, he)), hz))
      +ht = ME.subst(Nat, w => {Nat.is_eq(mx, w) == True{} : Bool}, mx, mz, emm, MN.is_eq_refl(mx))
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, MB.false_ne_true()(Equal.trans(Bool, False{}, Nat.is_eq(mx, mz), True{}, Equal.sym(Bool, Nat.is_eq(mx, mz), False{}, hne), ht)))
    case False{}:
      {==}

def ne_mod4(+x: Nat, +z: Nat, +mx: Nat, +mz: Nat, +hx: {Nat.mod(x, 4n) == mx : Nat}, +hz: {Nat.mod(z, 4n) == mz : Nat}, +hne: {Nat.is_eq(mx, mz) == False{} : Bool}) ->
  {Bool.not(Nat.is_eq(x, z)) == True{} : Bool}:
  ne_mod4.k(Nat.is_eq(x, z), x, z, mx, mz, {==}, hx, hz, hne)

# a static port's link word off a base's word j (2 or 3)
def st_off(+r: U32, +y: U32, +d: Nat, +j: U32, +h2: {Nat.is_le(2n, d) == True{} : Bool}, +hs: {P.is_static(r) == True{} : Bool}, +hb: {U32.is_eq(P.base(y), y) == True{} : Bool},
  +hj: {Nat.is_lt(U32.to_nat(j), 4n) == True{} : Bool}, +hj0: {Nat.is_eq(0n, U32.to_nat(j)) == False{} : Bool}) -> {Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + j : U32), d))) == True{} : Bool}:
  ne_mod4(AD.slot((r + 1 : U32), d), AD.slot((y + j : U32), d), 0n, U32.to_nat(j), slot_st1(r, d, h2, hs), slot_base(y, d, j, h2, hb, hj), hj0)

def mod1_zero.k(x: Nat, +h: {Nat.is_lt(x, 1n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          Empty.absurd({1n == 0n : Nat}, MB.false_ne_true()(h))
        case 1n+q:
          Empty.absurd({2n+q == 0n : Nat}, MB.false_ne_true()(h))

def mod1_zero(+n: Nat) -> {Nat.mod(n, 1n) == 0n : Nat}:
  mod1_zero.k(Nat.mod(n, 1n), WL.nat_mod_lt(n, 1n, {==}))

# three numbers below 2 are not pairwise apart
def pig(x: Nat, y: Nat, z: Nat, +hx: {Nat.is_lt(x, 2n) == True{} : Bool}, +hy: {Nat.is_lt(y, 2n) == True{} : Bool}, +hz: {Nat.is_lt(z, 2n) == True{} : Bool},
  +h10: {Bool.not(Nat.is_eq(y, x)) == True{} : Bool}, +h20: {Bool.not(Nat.is_eq(z, x)) == True{} : Bool}, +h21: {Bool.not(Nat.is_eq(z, y)) == True{} : Bool}) -> Empty:
  match x:
    case 0n:
      match y:
        case 0n:
          match z:
            case 0n:
              MB.false_ne_true()(h10)
            case 1n+pz:
              match pz:
                case 0n:
                  MB.false_ne_true()(h10)
                case 1n+qz:
                  match qz:
                    case 0n:
                      MB.false_ne_true()(hz)
                    case 1n+rz:
                      MB.false_ne_true()(hz)
        case 1n+py:
          match py:
            case 0n:
              match z:
                case 0n:
                  MB.false_ne_true()(h20)
                case 1n+pz:
                  match pz:
                    case 0n:
                      MB.false_ne_true()(h21)
                    case 1n+qz:
                      match qz:
                        case 0n:
                          MB.false_ne_true()(hz)
                        case 1n+rz:
                          MB.false_ne_true()(hz)
            case 1n+qy:
              match qy:
                case 0n:
                  MB.false_ne_true()(hy)
                case 1n+ry:
                  MB.false_ne_true()(hy)
    case 1n+px:
      match px:
        case 0n:
          match y:
            case 0n:
              match z:
                case 0n:
                  MB.false_ne_true()(h21)
                case 1n+pz:
                  match pz:
                    case 0n:
                      MB.false_ne_true()(h20)
                    case 1n+qz:
                      match qz:
                        case 0n:
                          MB.false_ne_true()(hz)
                        case 1n+rz:
                          MB.false_ne_true()(hz)
            case 1n+py:
              match py:
                case 0n:
                  match z:
                    case 0n:
                      MB.false_ne_true()(h10)
                    case 1n+pz:
                      match pz:
                        case 0n:
                          MB.false_ne_true()(h10)
                        case 1n+qz:
                          match qz:
                            case 0n:
                              MB.false_ne_true()(hz)
                            case 1n+rz:
                              MB.false_ne_true()(hz)
                case 1n+qy:
                  match qy:
                    case 0n:
                      MB.false_ne_true()(hy)
                    case 1n+ry:
                      MB.false_ne_true()(hy)
        case 1n+qx:
          match qx:
            case 0n:
              MB.false_ne_true()(hx)
            case 1n+rx:
              MB.false_ne_true()(hx)

# a node's words apart: the depth 2 or more
def d2(d: Nat, +a: U32, +h: {RG.apartw(RG.nw(a), d) == True{} : Bool}) -> {Nat.is_le(2n, d) == True{} : Bool}:
  match d:
    case 0n:
      +h10 = MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), 0n), AD.slot(a, 0n))), RG.off([(a + 2 : U32), (a + 3 : U32)], 0n, a), MB.eq_true_of_and_left(RG.off([(a + 1 : U32), (a + 2 : U32), (a + 3 : U32)], 0n, a), RG.apartw([(a + 1 : U32), (a + 2 : U32), (a + 3 : U32)], 0n), h))
      +g1 = ME.subst(Nat, w => {Bool.not(Nat.is_eq(w, AD.slot(a, 0n))) == True{} : Bool}, AD.slot((a + 1 : U32), 0n), 0n, mod1_zero(U32.to_nat((a + 1 : U32))), h10)
      +g2 = ME.subst(Nat, w => {Bool.not(Nat.is_eq(0n, w)) == True{} : Bool}, AD.slot(a, 0n), 0n, mod1_zero(U32.to_nat(a)), g1)
      Empty.absurd({Nat.is_le(2n, 0n) == True{} : Bool}, MB.false_ne_true()(g2))
    case 1n+p:
      match p:
        case 0n:
          Empty.absurd({Nat.is_le(2n, 1n) == True{} : Bool}, pig(AD.slot(a, 1n), AD.slot((a + 1 : U32), 1n), AD.slot((a + 2 : U32), 1n), WL.nat_mod_lt(U32.to_nat(a), 2n, {==}), WL.nat_mod_lt(U32.to_nat((a + 1 : U32)), 2n, {==}), WL.nat_mod_lt(U32.to_nat((a + 2 : U32)), 2n, {==}), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), 1n), AD.slot(a, 1n))), RG.off([(a + 2 : U32), (a + 3 : U32)], 1n, a), MB.eq_true_of_and_left(RG.off([(a + 1 : U32), (a + 2 : U32), (a + 3 : U32)], 1n, a), RG.apartw([(a + 1 : U32), (a + 2 : U32), (a + 3 : U32)], 1n), h)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), 1n), AD.slot(a, 1n))), RG.off([(a + 3 : U32)], 1n, a), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((a + 1 : U32), 1n), AD.slot(a, 1n))), RG.off([(a + 2 : U32), (a + 3 : U32)], 1n, a), MB.eq_true_of_and_left(RG.off([(a + 1 : U32), (a + 2 : U32), (a + 3 : U32)], 1n, a), RG.apartw([(a + 1 : U32), (a + 2 : U32), (a + 3 : U32)], 1n), h))), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((a + 2 : U32), 1n), AD.slot((a + 1 : U32), 1n))), RG.off([(a + 3 : U32)], 1n, (a + 1 : U32)), MB.eq_true_of_and_left(RG.off([(a + 2 : U32), (a + 3 : U32)], 1n, (a + 1 : U32)), RG.apartw([(a + 2 : U32), (a + 3 : U32)], 1n), MB.eq_true_of_and_right(RG.off([(a + 1 : U32), (a + 2 : U32), (a + 3 : U32)], 1n, a), RG.apartw([(a + 1 : U32), (a + 2 : U32), (a + 3 : U32)], 1n), h)))))
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+r:
              {==}

def ort_r(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +h: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  ME.subst(Bool, z => {Bool.or(z, b) == True{} : Bool}, a, False{}, ha, h)

# a member's words apart, its own base
def lay_at.k(+e: Bool, +m: U32, +t: List<&2, U32>, +d: Nat, +n: U32, +he: {U32.is_eq(m, n) == e : Bool}, +h: {RG.layout(Con{m, t}, d) == True{} : Bool},
  +hn: {Bool.or(U32.is_eq(m, n), RG.has(t, n)) == True{} : Bool}, ih: {RG.has(t, n) == True{} : Bool} -> {RG.apartw(RG.nw(n), d) == True{} : Bool}) -> {RG.apartw(RG.nw(n), d) == True{} : Bool}:
  match e:
    case True{}:
      %MS.u32_eq_of_is_eq(m, n, he) : {RG.apartw(RG.nw(_), d) == True{} : Bool}
      MB.eq_true_of_and_left(RG.apartw(RG.nw(m), d), RG.off(RG.nw(m), d, P.at_fh()) && (RG.cross(t, d, m) && RG.layout(t, d)), h)
    case False{}:
      ih(ort_r(U32.is_eq(m, n), RG.has(t, n), he, hn))

def lay_at(N: List<&2, U32>, +d: Nat, +n: U32, +h: {RG.layout(N, d) == True{} : Bool}, +hn: {RG.has(N, n) == True{} : Bool}) -> {RG.apartw(RG.nw(n), d) == True{} : Bool}:
  match N:
    case Nil{}:
      Empty.absurd({RG.apartw(RG.nw(n), d) == True{} : Bool}, MB.false_ne_true()(hn))
    case Con{+m, +t}:
      lay_at.k(U32.is_eq(m, n), m, t, d, n, {==}, h, hn, hnt => lay_at(t, d, n, MB.eq_true_of_and_right(RG.cross(t, d, m), RG.layout(t, d), MB.eq_true_of_and_right(RG.off(RG.nw(m), d, P.at_fh()), RG.cross(t, d, m) && RG.layout(t, d), MB.eq_true_of_and_right(RG.apartw(RG.nw(m), d), RG.off(RG.nw(m), d, P.at_fh()) && (RG.cross(t, d, m) && RG.layout(t, d)), h))), hnt))

def bases_at.k(+e: Bool, +m: U32, +t: List<&2, U32>, +n: U32, +he: {U32.is_eq(m, n) == e : Bool}, +h: {RG.bases(Con{m, t}) == True{} : Bool},
  +hn: {Bool.or(U32.is_eq(m, n), RG.has(t, n)) == True{} : Bool}, ih: {RG.has(t, n) == True{} : Bool} -> {U32.is_eq(P.base(n), n) == True{} : Bool}) -> {U32.is_eq(P.base(n), n) == True{} : Bool}:
  match e:
    case True{}:
      %MS.u32_eq_of_is_eq(m, n, he) : {U32.is_eq(P.base(_), _) == True{} : Bool}
      MB.eq_true_of_and_left(U32.is_eq(P.base(m), m), RG.bases(t), h)
    case False{}:
      ih(ort_r(U32.is_eq(m, n), RG.has(t, n), he, hn))

def bases_at(N: List<&2, U32>, +n: U32, +h: {RG.bases(N) == True{} : Bool}, +hn: {RG.has(N, n) == True{} : Bool}) -> {U32.is_eq(P.base(n), n) == True{} : Bool}:
  match N:
    case Nil{}:
      Empty.absurd({U32.is_eq(P.base(n), n) == True{} : Bool}, MB.false_ne_true()(hn))
    case Con{+m, +t}:
      bases_at.k(U32.is_eq(m, n), m, t, n, {==}, h, hn, hnt => bases_at(t, n, MB.eq_true_of_and_right(U32.is_eq(P.base(m), m), RG.bases(t), h), hnt))

def po_at.k(+e: Bool, +m: U32, +t: List<&2, U32>, +r: U32, +L: List<&2, U32>, +d: Nat, +n: U32, +he: {U32.is_eq(m, n) == e : Bool},
  +h: {RG.po.all(r, L, d, Con{m, t}) == True{} : Bool}, +hn: {Bool.or(U32.is_eq(m, n), RG.has(t, n)) == True{} : Bool}, ih: {RG.has(t, n) == True{} : Bool} -> {RG.po.n(r, L, d, n) == True{} : Bool}) -> {RG.po.n(r, L, d, n) == True{} : Bool}:
  match e:
    case True{}:
      %MS.u32_eq_of_is_eq(m, n, he) : {RG.po.n(r, L, d, _) == True{} : Bool}
      MB.eq_true_of_and_left(RG.po.n(r, L, d, m), RG.po.all(r, L, d, t), h)
    case False{}:
      ih(ort_r(U32.is_eq(m, n), RG.has(t, n), he, hn))

def po_at(N: List<&2, U32>, +r: U32, +L: List<&2, U32>, +d: Nat, +n: U32, +h: {RG.po.all(r, L, d, N) == True{} : Bool}, +hn: {RG.has(N, n) == True{} : Bool}) -> {RG.po.n(r, L, d, n) == True{} : Bool}:
  match N:
    case Nil{}:
      Empty.absurd({RG.po.n(r, L, d, n) == True{} : Bool}, MB.false_ne_true()(hn))
    case Con{+m, +t}:
      po_at.k(U32.is_eq(m, n), m, t, r, L, d, n, {==}, h, hn, hnt => po_at(t, r, L, d, n, MB.eq_true_of_and_right(RG.po.n(r, L, d, m), RG.po.all(r, L, d, t), h), hnt))

# port r's link word off word j, r no static
def offp_ns(+r: U32, +d: Nat, +j: U32, +hst: {P.is_static(r) == False{} : Bool}, +h: {KMd.off.port(d, r, j) == True{} : Bool}) -> {Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(j, d))) == True{} : Bool}:
  ME.subst(Bool, b => {KMd.off.lw(KMd.lw.k(b, r), d, j) == True{} : Bool}, P.is_static(r), False{}, hst, h)

# port r faceable by one member y of N not live: its link word off y's
# words 3 and 2, a static's by alignment, another's by po.all
def port_one.k(+st: Bool, +y: U32, +r: U32, +L: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +hst: {P.is_static(r) == st : Bool}, +hpo: {RG.po.all(r, L, d, N) == True{} : Bool},
  +hy: {RG.has(N, y) == True{} : Bool}, +hny: {RG.has(L, y) == False{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool}, +hB: {RG.bases(N) == True{} : Bool}) -> {Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + 3 : U32), d))) && Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + 2 : U32), d))) == True{} : Bool}:
  match st:
    case True{}:
      +hb = bases_at(N, y, hB, hy)
      +h2 = d2(d, y, lay_at(N, d, y, hN, hy))
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + 2 : U32), d))), st_off(r, y, d, 3, h2, hst, hb, {==}, {==}), st_off(r, y, d, 2, h2, hst, hb, {==}, {==}))
    case False{}:
      +pn = po_at(N, r, L, d, y, hpo, hy)
      +hor = MB.eq_true_of_and_right(KMd.off.port(d, r, y), Bool.or(RG.has(L, y), KMd.off.port(d, r, (y + 1 : U32)) && (KMd.off.port(d, r, (y + 2 : U32)) && KMd.off.port(d, r, (y + 3 : U32)))), pn)
      +hx = ort_r(RG.has(L, y), KMd.off.port(d, r, (y + 1 : U32)) && (KMd.off.port(d, r, (y + 2 : U32)) && KMd.off.port(d, r, (y + 3 : U32))), hny, hor)
      +h23 = MB.eq_true_of_and_right(KMd.off.port(d, r, (y + 1 : U32)), KMd.off.port(d, r, (y + 2 : U32)) && KMd.off.port(d, r, (y + 3 : U32)), hx)
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + 2 : U32), d))), offp_ns(r, d, (y + 3 : U32), hst, MB.eq_true_of_and_right(KMd.off.port(d, r, (y + 2 : U32)), KMd.off.port(d, r, (y + 3 : U32)), h23)), offp_ns(r, d, (y + 2 : U32), hst, MB.eq_true_of_and_left(KMd.off.port(d, r, (y + 2 : U32)), KMd.off.port(d, r, (y + 3 : U32)), h23)))

# port r faceable by members xs of N none live (RG.port.ok): its link
# word off every tracked node's words where not live (RG.po.all), the
# nodes laid out apart and their own bases (IndexPremises P3)
def port_of_po(xs: List<&2, U32>, +r: U32, +L: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +hpo: {RG.po.all(r, L, d, N) == True{} : Bool}, +hs: {RG.sub(xs, N) == True{} : Bool},
  +hn: {RG.none.in(xs, L) == True{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool}, +hB: {RG.bases(N) == True{} : Bool}) -> {RG.port.ok(xs, d, r) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +hy = MB.eq_true_of_and_left(RG.has(N, y), RG.sub(t, N), hs)
      +hst = MB.eq_true_of_and_right(RG.has(N, y), RG.sub(t, N), hs)
      +hny = MB.eq_false_of_not_eq_true(RG.has(L, y), MB.eq_true_of_and_left(Bool.not(RG.has(L, y)), RG.none.in(t, L), hn))
      +hnt = MB.eq_true_of_and_right(Bool.not(RG.has(L, y)), RG.none.in(t, L), hn)
      +pe = port_one.k(P.is_static(r), y, r, L, d, N, {==}, hpo, hy, hny, hN, hB)
      +ih = port_of_po(t, r, L, d, N, hpo, hst, hnt, hN, hB)
      MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + 3 : U32), d))) && RG.off.links(t, d, (r + 1 : U32)), Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + 2 : U32), d))) && RG.off.pos(t, d, (r + 1 : U32)), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + 3 : U32), d))), RG.off.links(t, d, (r + 1 : U32)), MB.eq_true_of_and_left(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + 2 : U32), d))), pe), MB.eq_true_of_and_left(RG.off.links(t, d, (r + 1 : U32)), RG.off.pos(t, d, (r + 1 : U32)), ih)), MB.and_eq_true(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + 2 : U32), d))), RG.off.pos(t, d, (r + 1 : U32)), MB.eq_true_of_and_right(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + 3 : U32), d))), Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((y + 2 : U32), d))), pe), MB.eq_true_of_and_right(RG.off.links(t, d, (r + 1 : U32)), RG.off.pos(t, d, (r + 1 : U32)), ih)))

def none_nil(xs: List<&2, U32>) -> {RG.none.in(xs, Nil{}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, t}:
      none_nil(t)

def or_true(+b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the eraser's link word off everything: a static has none
def po_static(+L: List<&2, U32>, +d: Nat, N: List<&2, U32>) -> {RG.po.all(P.era(), L, d, N) == True{} : Bool}:
  match N:
    case Nil{}:
      {==}
    case Con{+n, t}:
      MB.and_eq_true(RG.po.n(P.era(), L, d, n), RG.po.all(P.era(), L, d, t), or_true(RG.has(L, n)), po_static(L, d, t))

# the fresh nodes no statics: each its own base
def dyn_of_bases(ns: List<&2, U32>, +hB: {RG.bases(ns) == True{} : Bool}) -> {SV.dyn(ns) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, r}:
      +hb = MB.eq_true_of_and_left(U32.is_eq(P.base(n), n), RG.bases(r), hB)
      MB.and_eq_true(Bool.not(P.is_static(n)), SV.dyn(r), ME.subst(Bool, b => {Bool.not(b) == True{} : Bool}, False{}, P.is_static(n), Equal.sym(Bool, P.is_static(n), False{}, dyn_one(n, hb)), {==}), dyn_of_bases(r, MB.eq_true_of_and_right(U32.is_eq(P.base(n), n), RG.bases(r), hB)))

# the live nodes ys face ports faceable by the fresh nodes xs
# (RG.faces), from the invariant's link words off them (RG.px.off): xs
# tracked and none live, laid out apart, their own bases (IndexPremises
# P3)
def faces_fresh(ys: List<&2, U32>, +t0: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +N: List<&2, U32>, +xs: List<&2, U32>, +hf: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool},
  +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +hpx: {RG.px.off(ys, AD.view(U32, LAT.fromT(U32, t0)), d, L, N) == True{} : Bool}, +hs: {RG.sub(xs, N) == True{} : Bool}, +hn: {RG.none.in(xs, L) == True{} : Bool}, +hN: {RG.layout(N, d) == True{} : Bool},
  +hB: {RG.bases(N) == True{} : Bool}) -> {RG.faces(ys, AD.view(U32, LAT.fromT(U32, t0)), d, xs) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+m, t}:
      +g = LA.get_view(U32, LAT.fromT(U32, t0), d, (m + 1 : U32), hf, hd32)
      +hpo = MB.eq_true_of_and_left(RG.po.all(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (m + 1 : U32)), L, d, N), RG.px.off(t, AD.view(U32, LAT.fromT(U32, t0)), d, L, N), hpx)
      +hpo2 = ME.subst(Maybe<&2, U32>, q => {RG.po.all(KMd.word.m(q), L, d, N) == True{} : Bool}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((m + 1 : U32), d)), Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (m + 1 : U32)))}, Equal.sym(Maybe<&2, U32>, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (m + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((m + 1 : U32), d)), g), hpo)
      +fm = ME.subst(Maybe<&2, U32>, q => {RG.faces.m(q, d, xs) == True{} : Bool}, Some{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (m + 1 : U32)))}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((m + 1 : U32), d)), g, port_of_po(xs, Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), (m + 1 : U32))), L, d, N, hpo2, hs, hn, hN, hB))
      MB.and_eq_true(RG.faces.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t0)), AD.slot((m + 1 : U32), d)), d, xs), RG.faces(t, AD.view(U32, LAT.fromT(U32, t0)), d, xs), fm, faces_fresh(t, t0, d, L, N, xs, hf, hd32, MB.eq_true_of_and_right(RG.po.all(KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (m + 1 : U32)), L, d, N), RG.px.off(t, AD.view(U32, LAT.fromT(U32, t0)), d, L, N), hpx), hs, hn, hN, hB))

def main() -> U32:
  0
