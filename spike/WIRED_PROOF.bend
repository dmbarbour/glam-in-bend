# Proofs of spike/WIRED_LAWS.bend: the wiring's audit (KN.wired_ok) read
# as per-port facts (cursor-laws.noself.model,
# net-obvious-errors).
#
# Lessons (docs/Proving.md has them too):
# - The audit only reads, so it bridges as freeze's write phase does:
#   on a mirrored heap each read hands the heap back, and the audit is a
#   model over the words' tree that accumulates its verdict as the code
#   does, left to right, so that no reassociation is needed (b.go).
# - A false verdict stays false (go_false, ports_false), so a true one
#   had each step true (go_acc, ports_acc).
# - The walk to node j and port p counts on words: (a + 1 : U32) is
#   U32.inc(a), 2^32 abstracted, and to_nat_inc_lt then needs no power in
#   its premise (add1_inc.k, inc_nat); each walk takes its equality test
#   as a parameter, matched after the count, as Bend has no mutual
#   recursion (go_at, port_at).
# - A parameter named as a def shadows it: a premise hw hid the word
#   function hw (wp.k's hwd, hpa).
# - A mutant of the audit cannot be refuted by a witness: a witness must
#   pass the original audit, and then every port passes. Its mutants are
#   caught by the bridge failing on the mutated code.

import Base
import ./WIRED_LAWS.bend as Laws
import ./kprim.bend as P
import ./kmem_grow.bend as KM
import ./val.bend as V
import ./knet.bend as KN
import ./krules.bend as KR
import ./kmodel.bend as KMd
import ./wired_model.bend as WR
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MN
import 0x8ae61ec3a6615abd35f196c07232ad28/u32.bend as MU
import 0x96ab58f86121cb4f3fb48b3c8a045989/LAWS.bend as WL
import 0x96ab58f86121cb4f3fb48b3c8a045989/PROOF.bend as WP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/LAWS.bend as LA
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/PROOF.bend as LAP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_base.bend as LAB

def hw(+t0: LAT.Tree<U32>, +x: U32) -> U32:
  Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), x))

def hp(+t0: LAT.Tree<U32>, a: Array<V.Val>) -> P.H:
  P.H{KM.MG{LAT.fromT(U32, t0)}, a}

def rd_back(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +i: U32) -> {P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, i) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, hw(t0, i)) : P.H & U32}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), i), (LAT.fromT(U32, t0), hw(t0, i)), LA.get_pair(U32, LAT.fromT(U32, t0), i)) :
    {P.rd.fin(KM.m_get.fin(_), a) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, hw(t0, i)) : P.H & U32}
  {==}

# The audit's model over the words' tree, accumulating as the code does
def wm.live(+live: Bool, +t0: LAT.Tree<U32>, +x: U32, +y: U32, +ok: Bool) -> Bool:
  match live:
    case True{}:
      ok && U32.is_eq(hw(t0, (y + 1 : U32)), x)
    case False{}:
      False{}

def wm.at(+inside: Bool, +t0: LAT.Tree<U32>, +x: U32, +y: U32, +ok: Bool) -> Bool:
  match inside:
    case True{}:
      wm.live(U32.is_ne(hw(t0, P.base(y)), 0) && U32.is_lt(P.port(y), KR.kind_arity(P.rk(hw(t0, P.base(y))))), t0, x, y, ok)
    case False{}:
      False{}

def wm.lk(+st: Bool, +t0: LAT.Tree<U32>, +x: U32, +y: U32, +cap: U32, +ok: Bool) -> Bool:
  match st:
    case True{}:
      ok && U32.is_eq(y, P.era())
    case False{}:
      wm.at(U32.is_ge((y >> 2n : U32), P.first()) && U32.is_lt((y >> 2n : U32), cap) && U32.is_ne(y, x), t0, x, y, ok)

def wm.link(+t0: LAT.Tree<U32>, +x: U32, +cap: U32, +ok: Bool) -> Bool:
  wm.lk(P.is_static(hw(t0, (x + 1 : U32))), t0, x, hw(t0, (x + 1 : U32)), cap, ok)

def wm.ports(k: Nat, +t0: LAT.Tree<U32>, +i4: U32, +p: U32, +cap: U32, +ok: Bool) -> Bool:
  match k:
    case 0n:
      ok
    case 1n+q:
      wm.ports(q, t0, i4, (p + 1 : U32), cap, wm.link(t0, (i4 + p : U32), cap, ok))

def wm.node(+t0: LAT.Tree<U32>, +i4: U32, +cap: U32, +ok: Bool) -> Bool:
  wm.ports(U32.to_nat(KR.kind_arity(P.rk(hw(t0, i4)))), t0, i4, 0, cap, ok)

def wm.go(k: Nat, +t0: LAT.Tree<U32>, +i: U32, +cap: U32, +ok: Bool) -> Bool:
  match k:
    case 0n:
      ok
    case 1n+q:
      wm.go(q, t0, (i + 1 : U32), cap, wm.node(t0, (i << 2n : U32), cap, ok))

# the bridge: the audit on a mirrored heap is the model, the heap handed back
def b.live(+live: Bool, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +x: U32, +y: U32, +ok: Bool) ->
  {KN.wa.live(live, hp(t0, a), x, y, ok) == KN.Wa{hp(t0, a), wm.live(live, t0, x, y, ok)} : KN.Wa}:
  match live:
    case True{}:
      %Equal.sym(P.H & U32, P.rd(hp(t0, a), (y + 1 : U32)), (hp(t0, a), hw(t0, (y + 1 : U32))), rd_back(t0, a, (y + 1 : U32))) :
        {KN.wa.back(_, x, ok) == KN.Wa{hp(t0, a), wm.live(True{}, t0, x, y, ok)} : KN.Wa}
      {==}
    case False{}:
      {==}

def b.at(+inside: Bool, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +x: U32, +y: U32, +ok: Bool) ->
  {KN.wa.at(inside, hp(t0, a), x, y, ok) == KN.Wa{hp(t0, a), wm.at(inside, t0, x, y, ok)} : KN.Wa}:
  match inside:
    case True{}:
      %Equal.sym(P.H & U32, P.rd(hp(t0, a), P.base(y)), (hp(t0, a), hw(t0, P.base(y))), rd_back(t0, a, P.base(y))) :
        {KN.wa.peer(_, x, y, ok) == KN.Wa{hp(t0, a), wm.at(True{}, t0, x, y, ok)} : KN.Wa}
      b.live(U32.is_ne(hw(t0, P.base(y)), 0) && U32.is_lt(P.port(y), KR.kind_arity(P.rk(hw(t0, P.base(y))))), t0, a, x, y, ok)
    case False{}:
      {==}

def b.lk(+st: Bool, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +x: U32, +y: U32, +cap: U32, +ok: Bool) ->
  {KN.wa.lk(st, hp(t0, a), x, y, cap, ok) == KN.Wa{hp(t0, a), wm.lk(st, t0, x, y, cap, ok)} : KN.Wa}:
  match st:
    case True{}:
      {==}
    case False{}:
      b.at(U32.is_ge((y >> 2n : U32), P.first()) && U32.is_lt((y >> 2n : U32), cap) && U32.is_ne(y, x), t0, a, x, y, ok)

def b.ports(k: Nat, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +i4: U32, +p: U32, +cap: U32, +ok: Bool) ->
  {KN.wa.ports(k, i4, p, cap, KN.Wa{hp(t0, a), ok}) == KN.Wa{hp(t0, a), wm.ports(k, t0, i4, p, cap, ok)} : KN.Wa}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(P.H & U32, P.rd(hp(t0, a), ((i4 + p : U32) + 1 : U32)), (hp(t0, a), hw(t0, ((i4 + p : U32) + 1 : U32))), rd_back(t0, a, ((i4 + p : U32) + 1 : U32))) :
        {KN.wa.ports(q, i4, (p + 1 : U32), cap, KN.wa.link(_, (i4 + p : U32), cap, ok)) == KN.Wa{hp(t0, a), wm.ports(1n+q, t0, i4, p, cap, ok)} : KN.Wa}
      %Equal.sym(KN.Wa, KN.wa.lk(P.is_static(hw(t0, ((i4 + p : U32) + 1 : U32))), hp(t0, a), (i4 + p : U32), hw(t0, ((i4 + p : U32) + 1 : U32)), cap, ok),
          KN.Wa{hp(t0, a), wm.link(t0, (i4 + p : U32), cap, ok)},
          b.lk(P.is_static(hw(t0, ((i4 + p : U32) + 1 : U32))), t0, a, (i4 + p : U32), hw(t0, ((i4 + p : U32) + 1 : U32)), cap, ok)) :
        {KN.wa.ports(q, i4, (p + 1 : U32), cap, _) == KN.Wa{hp(t0, a), wm.ports(1n+q, t0, i4, p, cap, ok)} : KN.Wa}
      b.ports(q, t0, a, i4, (p + 1 : U32), cap, wm.link(t0, (i4 + p : U32), cap, ok))

def b.go(k: Nat, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +i: U32, +cap: U32, +ok: Bool) ->
  {KN.wa.go(k, i, cap, KN.Wa{hp(t0, a), ok}) == KN.Wa{hp(t0, a), wm.go(k, t0, i, cap, ok)} : KN.Wa}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(P.H & U32, P.rd(hp(t0, a), (i << 2n : U32)), (hp(t0, a), hw(t0, (i << 2n : U32))), rd_back(t0, a, (i << 2n : U32))) :
        {KN.wa.go(q, (i + 1 : U32), cap, KN.wa.node(_, (i << 2n : U32), cap, ok)) == KN.Wa{hp(t0, a), wm.go(1n+q, t0, i, cap, ok)} : KN.Wa}
      %Equal.sym(KN.Wa, KN.wa.ports(U32.to_nat(KR.kind_arity(P.rk(hw(t0, (i << 2n : U32))))), (i << 2n : U32), 0, cap, KN.Wa{hp(t0, a), ok}),
          KN.Wa{hp(t0, a), wm.node(t0, (i << 2n : U32), cap, ok)},
          b.ports(U32.to_nat(KR.kind_arity(P.rk(hw(t0, (i << 2n : U32))))), t0, a, (i << 2n : U32), 0, cap, ok)) :
        {KN.wa.go(q, (i + 1 : U32), cap, _) == KN.Wa{hp(t0, a), wm.go(1n+q, t0, i, cap, ok)} : KN.Wa}
      b.go(q, t0, a, (i + 1 : U32), cap, wm.node(t0, (i << 2n : U32), cap, ok))

# the heap's stats read off the mirror
def m_get_back(+t0: LAT.Tree<U32>, +i: U32) -> {KM.m_get(KM.MG{LAT.fromT(U32, t0)}, i) == (KM.MG{LAT.fromT(U32, t0)}, hw(t0, i)) : KM.M & U32}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), i), (LAT.fromT(U32, t0), hw(t0, i)), LA.get_pair(U32, LAT.fromT(U32, t0), i)) :
    {KM.m_get.fin(_) == (KM.MG{LAT.fromT(U32, t0)}, hw(t0, i)) : KM.M & U32}
  {==}

def stats_back(+t0: LAT.Tree<U32>, -a: Array<V.Val>) ->
  {P.stats(hp(t0, a)) == (hp(t0, a), P.HS{hw(t0, P.at_itrs()), hw(t0, P.at_errs()), hw(t0, P.at_wcap())}) : P.H & P.HS}:
  %Equal.sym(KM.M & U32, KM.m_get(KM.MG{LAT.fromT(U32, t0)}, P.at_itrs()), (KM.MG{LAT.fromT(U32, t0)}, hw(t0, P.at_itrs())), m_get_back(t0, P.at_itrs())) :
    {P.stats.i(_, a) == (hp(t0, a), P.HS{hw(t0, P.at_itrs()), hw(t0, P.at_errs()), hw(t0, P.at_wcap())}) : P.H & P.HS}
  %Equal.sym(KM.M & U32, KM.m_get(KM.MG{LAT.fromT(U32, t0)}, P.at_errs()), (KM.MG{LAT.fromT(U32, t0)}, hw(t0, P.at_errs())), m_get_back(t0, P.at_errs())) :
    {P.stats.e(_, a, hw(t0, P.at_itrs())) == (hp(t0, a), P.HS{hw(t0, P.at_itrs()), hw(t0, P.at_errs()), hw(t0, P.at_wcap())}) : P.H & P.HS}
  %Equal.sym(KM.M & U32, KM.m_get(KM.MG{LAT.fromT(U32, t0)}, P.at_wcap()), (KM.MG{LAT.fromT(U32, t0)}, hw(t0, P.at_wcap())), m_get_back(t0, P.at_wcap())) :
    {P.stats.c(_, a, hw(t0, P.at_itrs()), hw(t0, P.at_errs())) == (hp(t0, a), P.HS{hw(t0, P.at_itrs()), hw(t0, P.at_errs()), hw(t0, P.at_wcap())}) : P.H & P.HS}
  {==}

def capw(+t0: LAT.Tree<U32>) -> U32:
  hw(t0, P.at_wcap())

# the audit's verdict on a mirrored heap is the model's
def wired_back(+t0: LAT.Tree<U32>, -a: Array<V.Val>) ->
  {Pair.snd(P.H, Bool, KN.wired_ok(hp(t0, a))) == wm.go(U32.to_nat((capw(t0) - P.first() : U32)), t0, P.first(), capw(t0), True{}) : Bool}:
  %Equal.sym(P.H & P.HS, P.stats(hp(t0, a)), (hp(t0, a), P.HS{hw(t0, P.at_itrs()), hw(t0, P.at_errs()), capw(t0)}), stats_back(t0, a)) :
    {Pair.snd(P.H, Bool, KN.wa.st(_)) == wm.go(U32.to_nat((capw(t0) - P.first() : U32)), t0, P.first(), capw(t0), True{}) : Bool}
  %Equal.sym(KN.Wa, KN.wa.go(U32.to_nat((capw(t0) - P.first() : U32)), P.first(), capw(t0), KN.Wa{hp(t0, a), True{}}),
      KN.Wa{hp(t0, a), wm.go(U32.to_nat((capw(t0) - P.first() : U32)), t0, P.first(), capw(t0), True{})},
      b.go(U32.to_nat((capw(t0) - P.first() : U32)), t0, a, P.first(), capw(t0), True{})) :
    {Pair.snd(P.H, Bool, KN.wa.fin(_)) == wm.go(U32.to_nat((capw(t0) - P.first() : U32)), t0, P.first(), capw(t0), True{}) : Bool}
  {==}

# a false verdict stays false
def live_false(+live: Bool, +t0: LAT.Tree<U32>, +x: U32, +y: U32) -> {wm.live(live, t0, x, y, False{}) == False{} : Bool}:
  match live:
    case True{}:
      {==}
    case False{}:
      {==}

def at_false(+inside: Bool, +t0: LAT.Tree<U32>, +x: U32, +y: U32) -> {wm.at(inside, t0, x, y, False{}) == False{} : Bool}:
  match inside:
    case True{}:
      live_false(U32.is_ne(hw(t0, P.base(y)), 0) && U32.is_lt(P.port(y), KR.kind_arity(P.rk(hw(t0, P.base(y))))), t0, x, y)
    case False{}:
      {==}

def lk_false(+st: Bool, +t0: LAT.Tree<U32>, +x: U32, +y: U32, +cap: U32) -> {wm.lk(st, t0, x, y, cap, False{}) == False{} : Bool}:
  match st:
    case True{}:
      {==}
    case False{}:
      at_false(U32.is_ge((y >> 2n : U32), P.first()) && U32.is_lt((y >> 2n : U32), cap) && U32.is_ne(y, x), t0, x, y)

def link_false(+t0: LAT.Tree<U32>, +x: U32, +cap: U32) -> {wm.link(t0, x, cap, False{}) == False{} : Bool}:
  lk_false(P.is_static(hw(t0, (x + 1 : U32))), t0, x, hw(t0, (x + 1 : U32)), cap)


def ports_false(k: Nat, +t0: LAT.Tree<U32>, +i4: U32, +p: U32, +cap: U32) -> {wm.ports(k, t0, i4, p, cap, False{}) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(Bool, wm.link(t0, (i4 + p : U32), cap, False{}), False{}, link_false(t0, (i4 + p : U32), cap)) :
        {wm.ports(q, t0, i4, (p + 1 : U32), cap, _) == False{} : Bool}
      ports_false(q, t0, i4, (p + 1 : U32), cap)

def go_false(k: Nat, +t0: LAT.Tree<U32>, +i: U32, +cap: U32) -> {wm.go(k, t0, i, cap, False{}) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(Bool, wm.node(t0, (i << 2n : U32), cap, False{}), False{}, ports_false(U32.to_nat(KR.kind_arity(P.rk(hw(t0, (i << 2n : U32))))), t0, (i << 2n : U32), 0, cap)) :
        {wm.go(q, t0, (i + 1 : U32), cap, _) == False{} : Bool}
      go_false(q, t0, (i + 1 : U32), cap)

# a true verdict had a true start
def ports_acc(+c: Bool, k: Nat, +t0: LAT.Tree<U32>, +i4: U32, +p: U32, +cap: U32, +h: {wm.ports(k, t0, i4, p, cap, c) == True{} : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, MB.false_ne_true()(Equal.trans(Bool, False{}, wm.ports(k, t0, i4, p, cap, False{}), True{}, Equal.sym(Bool, wm.ports(k, t0, i4, p, cap, False{}), False{}, ports_false(k, t0, i4, p, cap)), h)))

def go_acc(+c: Bool, k: Nat, +t0: LAT.Tree<U32>, +i: U32, +cap: U32, +h: {wm.go(k, t0, i, cap, c) == True{} : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, MB.false_ne_true()(Equal.trans(Bool, False{}, wm.go(k, t0, i, cap, False{}), True{}, Equal.sym(Bool, wm.go(k, t0, i, cap, False{}), False{}, go_false(k, t0, i, cap)), h)))

# a word's increment is U32.inc, 2^32 abstracted
def add1_inc.k(-m: Nat, +e: {Nat.pow(2n, 32n) == m : Nat}, +a: U32) -> {(a + 1 : U32) == U32.inc(a) : U32}:
  +e1 = ME.subst(Nat, w => {U32.to_nat(U32.add(a, 1)) == Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(1)), w) : Nat}, Nat.pow(2n, 32n), m, e, WL.to_nat_add(a, 1))
  +e2 = ME.subst(Nat, w => {U32.to_nat(U32.inc(a)) == Nat.mod(Nat.add(U32.to_nat(a), 1n), w) : Nat}, Nat.pow(2n, 32n), m, e, WL.to_nat_inc(a))
  MU.u32_to_nat_inj((a + 1 : U32), U32.inc(a), Equal.trans(Nat, U32.to_nat((a + 1 : U32)), Nat.mod(Nat.add(U32.to_nat(a), 1n), m), U32.to_nat(U32.inc(a)),
    e1, Equal.sym(Nat, U32.to_nat(U32.inc(a)), Nat.mod(Nat.add(U32.to_nat(a), 1n), m), e2)))

def add_one(+x: Nat) -> {Nat.add(x, 1n) == 1n+x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+y:
      %Equal.sym(Nat, Nat.add(y, 1n), 1n+y, add_one(y)) : {1n+_ == 1n+1n+y : Nat}
      {==}

# the next index, below some j, counts one more
def inc_nat(+a: U32, +j: U32, +h: {U32.is_lt(a, j) == True{} : Bool}) -> {U32.to_nat((a + 1 : U32)) == 1n+U32.to_nat(a) : Nat}:
  %Equal.sym(U32, (a + 1 : U32), U32.inc(a), add1_inc.k(Nat.pow(2n, 32n), {==}, a)) : {U32.to_nat(_) == 1n+U32.to_nat(a) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.inc(a)), Nat.add(U32.to_nat(a), 1n), WL.to_nat_inc_lt(a, j, h)) : {_ == 1n+U32.to_nat(a) : Nat}
  add_one(U32.to_nat(a))

# Nat facts for the walk to an index
def le_succ(+d: Nat, +k: Nat, +hle: {Nat.is_le(d, k) == True{} : Bool}, +hne: {Nat.is_eq(d, k) == False{} : Bool}) -> {Nat.is_le(1n+d, k) == True{} : Bool}:
  match d:
    case 0n:
      match k:
        case 0n:
          Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, MB.true_ne_false()(hne))
        case 1n+c:
          match c:
            case 0n:
              {==}
            case 1n+e:
              {==}
    case 1n+a:
      match k:
        case 0n:
          Empty.absurd({Nat.is_le(1n+1n+a, 0n) == True{} : Bool}, MB.false_ne_true()(hle))
        case 1n+c:
          le_succ(a, c, hle, hne)

def lt_of_le_ne(+a: Nat, +b: Nat, +hle: {Nat.is_le(a, b) == True{} : Bool}, +hne: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, MB.true_ne_false()(hne))
        case 1n+c:
          {==}
    case 1n+x:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+x, 0n) == True{} : Bool}, MB.false_ne_true()(hle))
        case 1n+c:
          lt_of_le_ne(x, c, hle, hne)

def lt_le_no(-A: Type, +a: Nat, +b: Nat, +hlt: {Nat.is_lt(a, b) == True{} : Bool}, +hle: {Nat.is_le(b, a) == True{} : Bool}) -> A:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd(A, MB.false_ne_true()(hlt))
        case 1n+c:
          Empty.absurd(A, MB.false_ne_true()(hle))
    case 1n+x:
      match b:
        case 0n:
          Empty.absurd(A, MB.false_ne_true()(hlt))
        case 1n+c:
          lt_le_no(A, x, c, hlt, hle)

# the walk over node slots reaches node j, between i and i + k
def go_at(k: Nat, +e: Bool, +t0: LAT.Tree<U32>, +i: U32, +cap: U32, +j: U32, +he: {Nat.is_eq(U32.to_nat(j), U32.to_nat(i)) == e : Bool},
  +h: {wm.go(k, t0, i, cap, True{}) == True{} : Bool}, +hlo: {Nat.is_le(U32.to_nat(i), U32.to_nat(j)) == True{} : Bool}, +hhi: {Nat.is_lt(U32.to_nat(j), Nat.add(k, U32.to_nat(i))) == True{} : Bool}) ->
  {wm.node(t0, (j << 2n : U32), cap, True{}) == True{} : Bool}:
  match k:
    case 0n:
      lt_le_no({wm.node(t0, (j << 2n : U32), cap, True{}) == True{} : Bool}, U32.to_nat(j), U32.to_nat(i), hhi, hlo)
    case 1n+(+q):
      match e:
        case True{}:
          +hc = go_acc(wm.node(t0, (i << 2n : U32), cap, True{}), q, t0, (i + 1 : U32), cap, h)
          ME.subst(U32, z => {wm.node(t0, (z << 2n : U32), cap, True{}) == True{} : Bool}, i, j, Equal.sym(U32, j, i, MU.u32_to_nat_inj(j, i, MN.eq_of_is_eq(U32.to_nat(j), U32.to_nat(i), he))), hc)
        case False{}:
          +hc = go_acc(wm.node(t0, (i << 2n : U32), cap, True{}), q, t0, (i + 1 : U32), cap, h)
          +ht = ME.subst(Bool, z => {wm.go(q, t0, (i + 1 : U32), cap, z) == True{} : Bool}, wm.node(t0, (i << 2n : U32), cap, True{}), True{}, hc, h)
          +hne = Equal.trans(Bool, Nat.is_eq(U32.to_nat(i), U32.to_nat(j)), Nat.is_eq(U32.to_nat(j), U32.to_nat(i)), False{}, MN.is_eq_comm(U32.to_nat(i), U32.to_nat(j)), he)
          +hlt = Equal.trans(Bool, U32.is_lt(i, j), Nat.is_lt(U32.to_nat(i), U32.to_nat(j)), True{}, MU.u32_is_lt_to_nat(i, j), lt_of_le_ne(U32.to_nat(i), U32.to_nat(j), hlo, hne))
          +hn1 = inc_nat(i, j, hlt)
          +hlo2 = ME.subst(Nat, z => {Nat.is_le(z, U32.to_nat(j)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), hn1), le_succ(U32.to_nat(i), U32.to_nat(j), hlo, hne))
          +hhi1 = ME.subst(Nat, z => {Nat.is_lt(U32.to_nat(j), z) == True{} : Bool}, 1n+Nat.add(q, U32.to_nat(i)), Nat.add(q, 1n+U32.to_nat(i)), Equal.sym(Nat, Nat.add(q, 1n+U32.to_nat(i)), 1n+Nat.add(q, U32.to_nat(i)), MN.add_succ(q, U32.to_nat(i))), hhi)
          +hhi2 = ME.subst(Nat, z => {Nat.is_lt(U32.to_nat(j), Nat.add(q, z)) == True{} : Bool}, 1n+U32.to_nat(i), U32.to_nat((i + 1 : U32)), Equal.sym(Nat, U32.to_nat((i + 1 : U32)), 1n+U32.to_nat(i), hn1), hhi1)
          go_at(q, Nat.is_eq(U32.to_nat(j), U32.to_nat((i + 1 : U32))), t0, (i + 1 : U32), cap, j, {==}, ht, hlo2, hhi2)

# the walk over a node's ports reaches port p, between p0 and p0 + k
def port_at(k: Nat, +e: Bool, +t0: LAT.Tree<U32>, +i4: U32, +p0: U32, +cap: U32, +p: U32, +he: {Nat.is_eq(U32.to_nat(p), U32.to_nat(p0)) == e : Bool},
  +h: {wm.ports(k, t0, i4, p0, cap, True{}) == True{} : Bool}, +hlo: {Nat.is_le(U32.to_nat(p0), U32.to_nat(p)) == True{} : Bool}, +hhi: {Nat.is_lt(U32.to_nat(p), Nat.add(k, U32.to_nat(p0))) == True{} : Bool}) ->
  {wm.link(t0, (i4 + p : U32), cap, True{}) == True{} : Bool}:
  match k:
    case 0n:
      lt_le_no({wm.link(t0, (i4 + p : U32), cap, True{}) == True{} : Bool}, U32.to_nat(p), U32.to_nat(p0), hhi, hlo)
    case 1n+(+q):
      match e:
        case True{}:
          +hc = ports_acc(wm.link(t0, (i4 + p0 : U32), cap, True{}), q, t0, i4, (p0 + 1 : U32), cap, h)
          ME.subst(U32, z => {wm.link(t0, (i4 + z : U32), cap, True{}) == True{} : Bool}, p0, p, Equal.sym(U32, p, p0, MU.u32_to_nat_inj(p, p0, MN.eq_of_is_eq(U32.to_nat(p), U32.to_nat(p0), he))), hc)
        case False{}:
          +hc = ports_acc(wm.link(t0, (i4 + p0 : U32), cap, True{}), q, t0, i4, (p0 + 1 : U32), cap, h)
          +ht = ME.subst(Bool, z => {wm.ports(q, t0, i4, (p0 + 1 : U32), cap, z) == True{} : Bool}, wm.link(t0, (i4 + p0 : U32), cap, True{}), True{}, hc, h)
          +hne = Equal.trans(Bool, Nat.is_eq(U32.to_nat(p0), U32.to_nat(p)), Nat.is_eq(U32.to_nat(p), U32.to_nat(p0)), False{}, MN.is_eq_comm(U32.to_nat(p0), U32.to_nat(p)), he)
          +hlt = Equal.trans(Bool, U32.is_lt(p0, p), Nat.is_lt(U32.to_nat(p0), U32.to_nat(p)), True{}, MU.u32_is_lt_to_nat(p0, p), lt_of_le_ne(U32.to_nat(p0), U32.to_nat(p), hlo, hne))
          +hn1 = inc_nat(p0, p, hlt)
          +hlo2 = ME.subst(Nat, z => {Nat.is_le(z, U32.to_nat(p)) == True{} : Bool}, 1n+U32.to_nat(p0), U32.to_nat((p0 + 1 : U32)), Equal.sym(Nat, U32.to_nat((p0 + 1 : U32)), 1n+U32.to_nat(p0), hn1), le_succ(U32.to_nat(p0), U32.to_nat(p), hlo, hne))
          +hhi1 = ME.subst(Nat, z => {Nat.is_lt(U32.to_nat(p), z) == True{} : Bool}, 1n+Nat.add(q, U32.to_nat(p0)), Nat.add(q, 1n+U32.to_nat(p0)), Equal.sym(Nat, Nat.add(q, 1n+U32.to_nat(p0)), 1n+Nat.add(q, U32.to_nat(p0)), MN.add_succ(q, U32.to_nat(p0))), hhi)
          +hhi2 = ME.subst(Nat, z => {Nat.is_lt(U32.to_nat(p), Nat.add(q, z)) == True{} : Bool}, 1n+U32.to_nat(p0), U32.to_nat((p0 + 1 : U32)), Equal.sym(Nat, U32.to_nat((p0 + 1 : U32)), 1n+U32.to_nat(p0), hn1), hhi1)
          port_at(q, Nat.is_eq(U32.to_nat(p), U32.to_nat((p0 + 1 : U32))), t0, i4, (p0 + 1 : U32), cap, p, {==}, ht, hlo2, hhi2)

# ---- the model's check is the predicate, words read through the view
def wdv(+t0: LAT.Tree<U32>, +d: Nat, +i: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, i) == hw(t0, i) : U32}:
  %LA.get_view(U32, LAT.fromT(U32, t0), d, i, hft, hd32) : {KMd.word.m(_) == hw(t0, i) : U32}
  {==}

def ok_live(+live: Bool, +t0: LAT.Tree<U32>, +d: Nat, +x: U32, +y: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
  {wm.live(live, t0, x, y, True{}) == WR.live(live, AD.view(U32, LAT.fromT(U32, t0)), d, x, y) : Bool}:
  match live:
    case True{}:
      %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (y + 1 : U32)), hw(t0, (y + 1 : U32)), wdv(t0, d, (y + 1 : U32), hft, hd32)) : {U32.is_eq(hw(t0, (y + 1 : U32)), x) == U32.is_eq(_, x) : Bool}
      {==}
    case False{}:
      {==}

def ok_at(+inside: Bool, +t0: LAT.Tree<U32>, +d: Nat, +x: U32, +y: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
  {wm.at(inside, t0, x, y, True{}) == WR.at(inside, AD.view(U32, LAT.fromT(U32, t0)), d, x, y) : Bool}:
  match inside:
    case True{}:
      %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.base(y)), hw(t0, P.base(y)), wdv(t0, d, P.base(y), hft, hd32)) :
        {wm.at(True{}, t0, x, y, True{}) == WR.live(U32.is_ne(_, 0) && U32.is_lt(P.port(y), KR.kind_arity(P.rk(_))), AD.view(U32, LAT.fromT(U32, t0)), d, x, y) : Bool}
      ok_live(U32.is_ne(hw(t0, P.base(y)), 0) && U32.is_lt(P.port(y), KR.kind_arity(P.rk(hw(t0, P.base(y))))), t0, d, x, y, hft, hd32)
    case False{}:
      {==}

def ok_lk(+st: Bool, +t0: LAT.Tree<U32>, +d: Nat, +x: U32, +y: U32, +cap: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
  {wm.lk(st, t0, x, y, cap, True{}) == WR.lk(st, AD.view(U32, LAT.fromT(U32, t0)), d, x, y, cap) : Bool}:
  match st:
    case True{}:
      {==}
    case False{}:
      ok_at(U32.is_ge((y >> 2n : U32), P.first()) && U32.is_lt((y >> 2n : U32), cap) && U32.is_ne(y, x), t0, d, x, y, hft, hd32)

def ok_link(+t0: LAT.Tree<U32>, +d: Nat, +x: U32, +cap: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
  {wm.link(t0, x, cap, True{}) == WR.port.ok(AD.view(U32, LAT.fromT(U32, t0)), d, x, cap) : Bool}:
  %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (x + 1 : U32)), hw(t0, (x + 1 : U32)), wdv(t0, d, (x + 1 : U32), hft, hd32)) : {wm.link(t0, x, cap, True{}) == WR.lk(P.is_static(_), AD.view(U32, LAT.fromT(U32, t0)), d, x, _, cap) : Bool}
  ok_lk(P.is_static(hw(t0, (x + 1 : U32))), t0, d, x, hw(t0, (x + 1 : U32)), cap, hft, hd32)

def sub_add_b(+m: Nat, +n: Nat, +h: {Nat.is_le(m, n) == True{} : Bool}) -> {Nat.add(Nat.sub(n, m), m) == n : Nat}:
  match m:
    case 0n:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, LAB.sub_zero(n)) : {Nat.add(_, 0n) == n : Nat}
      MN.add_zero(n)
    case 1n+c:
      match n:
        case 0n:
          Empty.absurd({Nat.add(Nat.sub(0n, 1n+c), 1n+c) == 0n : Nat}, MB.false_ne_true()(h))
        case 1n+k:
          %Equal.sym(Nat, Nat.add(Nat.sub(k, c), 1n+c), 1n+Nat.add(Nat.sub(k, c), c), MN.add_succ(Nat.sub(k, c), c)) : {_ == 1n+k : Nat}
          %Equal.sym(Nat, Nat.add(Nat.sub(k, c), c), k, sub_add_b(c, k, h)) : {1n+_ == 1n+k : Nat}
          {==}


def le0(+y: Nat) -> {Nat.is_le(0n, y) == True{} : Bool}:
  match y:
    case 0n:
      {==}
    case 1n+c:
      {==}

def le_of_lt(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a:
    case 0n:
      le0(b)
    case 1n+x:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+x, 0n) == True{} : Bool}, MB.false_ne_true()(h))
        case 1n+c:
          le_of_lt(x, c, h)

# a live node's port, below its kind's arity, passes the audit's check
def wp.k(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +hwd: {Pair.snd(P.H, Bool, KN.wired_ok(hp(t0, a))) == True{} : Bool}, +j: U32, +p: U32,
  +hj: {U32.is_le(P.first(), j) == True{} : Bool}, +hjc: {U32.is_lt(j, capw(t0)) == True{} : Bool}, +hpa: {U32.is_lt(p, KR.kind_arity(P.rk(hw(t0, (j << 2n : U32))))) == True{} : Bool}) ->
  {wm.link(t0, ((j << 2n : U32) + p : U32), capw(t0), True{}) == True{} : Bool}:
  +hv = Equal.trans(Bool, wm.go(U32.to_nat((capw(t0) - P.first() : U32)), t0, P.first(), capw(t0), True{}), Pair.snd(P.H, Bool, KN.wired_ok(hp(t0, a))), True{}, Equal.sym(Bool, Pair.snd(P.H, Bool, KN.wired_ok(hp(t0, a))), wm.go(U32.to_nat((capw(t0) - P.first() : U32)), t0, P.first(), capw(t0), True{}), wired_back(t0, a)), hwd)
  +hlo = Equal.trans(Bool, Nat.is_le(U32.to_nat(P.first()), U32.to_nat(j)), U32.is_le(P.first(), j), True{}, Equal.sym(Bool, U32.is_le(P.first(), j), Nat.is_le(U32.to_nat(P.first()), U32.to_nat(j)), MU.u32_is_le_to_nat(P.first(), j)), hj)
  +hjn = Equal.trans(Bool, Nat.is_lt(U32.to_nat(j), U32.to_nat(capw(t0))), U32.is_lt(j, capw(t0)), True{}, Equal.sym(Bool, U32.is_lt(j, capw(t0)), Nat.is_lt(U32.to_nat(j), U32.to_nat(capw(t0))), MU.u32_is_lt_to_nat(j, capw(t0))), hjc)
  +hfc = WL.nat_le_trans(U32.to_nat(P.first()), U32.to_nat(j), U32.to_nat(capw(t0)), hlo, le_of_lt(U32.to_nat(j), U32.to_nat(capw(t0)), hjn))
  +hfcu = Equal.trans(Bool, U32.is_le(P.first(), capw(t0)), Nat.is_le(U32.to_nat(P.first()), U32.to_nat(capw(t0))), True{}, MU.u32_is_le_to_nat(P.first(), capw(t0)), hfc)
  +hK = Equal.trans(Nat, Nat.add(U32.to_nat((capw(t0) - P.first() : U32)), U32.to_nat(P.first())), Nat.add(Nat.sub(U32.to_nat(capw(t0)), U32.to_nat(P.first())), U32.to_nat(P.first())), U32.to_nat(capw(t0)),
    Equal.cong(Nat, Nat, z => Nat.add(z, U32.to_nat(P.first())), U32.to_nat((capw(t0) - P.first() : U32)), Nat.sub(U32.to_nat(capw(t0)), U32.to_nat(P.first())), WL.to_nat_sub_le(capw(t0), P.first(), hfcu)), sub_add_b(U32.to_nat(P.first()), U32.to_nat(capw(t0)), hfc))
  +hhi = ME.subst(Nat, z => {Nat.is_lt(U32.to_nat(j), z) == True{} : Bool}, U32.to_nat(capw(t0)), Nat.add(U32.to_nat((capw(t0) - P.first() : U32)), U32.to_nat(P.first())), Equal.sym(Nat, Nat.add(U32.to_nat((capw(t0) - P.first() : U32)), U32.to_nat(P.first())), U32.to_nat(capw(t0)), hK), hjn)
  +hnode = go_at(U32.to_nat((capw(t0) - P.first() : U32)), Nat.is_eq(U32.to_nat(j), U32.to_nat(P.first())), t0, P.first(), capw(t0), j, {==}, hv, hlo, hhi)
  +hpn = Equal.trans(Bool, Nat.is_lt(U32.to_nat(p), U32.to_nat(KR.kind_arity(P.rk(hw(t0, (j << 2n : U32)))))), U32.is_lt(p, KR.kind_arity(P.rk(hw(t0, (j << 2n : U32))))), True{}, Equal.sym(Bool, U32.is_lt(p, KR.kind_arity(P.rk(hw(t0, (j << 2n : U32))))), Nat.is_lt(U32.to_nat(p), U32.to_nat(KR.kind_arity(P.rk(hw(t0, (j << 2n : U32)))))), MU.u32_is_lt_to_nat(p, KR.kind_arity(P.rk(hw(t0, (j << 2n : U32)))))), hpa)
  +hpn0 = ME.subst(Nat, z => {Nat.is_lt(U32.to_nat(p), z) == True{} : Bool}, U32.to_nat(KR.kind_arity(P.rk(hw(t0, (j << 2n : U32))))), Nat.add(U32.to_nat(KR.kind_arity(P.rk(hw(t0, (j << 2n : U32))))), 0n), Equal.sym(Nat, Nat.add(U32.to_nat(KR.kind_arity(P.rk(hw(t0, (j << 2n : U32))))), 0n), U32.to_nat(KR.kind_arity(P.rk(hw(t0, (j << 2n : U32))))), MN.add_zero(U32.to_nat(KR.kind_arity(P.rk(hw(t0, (j << 2n : U32))))))), hpn)
  port_at(U32.to_nat(KR.kind_arity(P.rk(hw(t0, (j << 2n : U32))))), Nat.is_eq(U32.to_nat(p), 0n), t0, (j << 2n : U32), 0, capw(t0), p, {==}, hnode, le0(U32.to_nat(p)), hpn0)

def wp.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, hf: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  hwd: {Pair.snd(P.H, Bool, KN.wired_ok(P.H{KM.MG{w}, a})) == True{} : Bool}, +j: U32, +p: U32, +hj: {U32.is_le(P.first(), j) == True{} : Bool},
  hjc: {U32.is_lt(j, KMd.word(AD.view(U32, w), d, P.at_wcap())) == True{} : Bool}, hpa: {U32.is_lt(p, KR.kind_arity(P.rk(KMd.word(AD.view(U32, w), d, (j << 2n : U32))))) == True{} : Bool},
  m0: LAT.Mirror(U32, w)) -> {WR.port.ok(AD.view(U32, w), d, ((j << 2n : U32) + p : U32), KMd.word(AD.view(U32, w), d, P.at_wcap())) == True{} : Bool}:
  (+t0, +e0) = m0
  +hft = LAP.full_t(U32, w, t0, d, e0, hf)
  +hw2 = LAB.subst(Array<U32>, x => {Pair.snd(P.H, Bool, KN.wired_ok(P.H{KM.MG{x}, a})) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e0), hwd)
  +hjc2 = LAB.subst(Array<U32>, x => {U32.is_lt(j, KMd.word(AD.view(U32, x), d, P.at_wcap())) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e0), hjc)
  +hjc3 = ME.subst(U32, z => {U32.is_lt(j, z) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_wcap()), capw(t0), wdv(t0, d, P.at_wcap(), hft, hd32), hjc2)
  +hpa2 = LAB.subst(Array<U32>, x => {U32.is_lt(p, KR.kind_arity(P.rk(KMd.word(AD.view(U32, x), d, (j << 2n : U32))))) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e0), hpa)
  +hpa3 = ME.subst(U32, z => {U32.is_lt(p, KR.kind_arity(P.rk(z))) == True{} : Bool}, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (j << 2n : U32)), hw(t0, (j << 2n : U32)), wdv(t0, d, (j << 2n : U32), hft, hd32), hpa2)
  %e0 : {WR.port.ok(AD.view(U32, _), d, ((j << 2n : U32) + p : U32), KMd.word(AD.view(U32, _), d, P.at_wcap())) == True{} : Bool}
  %Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, P.at_wcap()), capw(t0), wdv(t0, d, P.at_wcap(), hft, hd32)) : {WR.port.ok(AD.view(U32, LAT.fromT(U32, t0)), d, ((j << 2n : U32) + p : U32), _) == True{} : Bool}
  %ok_link(t0, d, ((j << 2n : U32) + p : U32), capw(t0), hft, hd32) : {_ == True{} : Bool}
  wp.k(t0, a, d, hw2, j, p, hj, hjc3, hpa3)

def Laws.wired_port(w, a, d, hf, hd32, hwd, j, p, hj, hjc, hpa):
  wp.m(w, a, d, hf, hd32, hwd, j, p, hj, hjc, hpa, LAT.mirror(U32, w))
