# Proofs of glam/FREEZE_LAWS.bend: the write phase of glam/freeze.bend
# (the CursorLaws plan's cursor-laws.materializer.template.emit).
#
# Lessons (docs/Proving.md has them too):
# - A record holding the heap and the map (F.FzE) is named once in a
#   proof's terms. A step lemma inv(z) -> inv(step(z)) chains only by
#   naming it twice, refused as "consumed more than once"; +z is refused
#   for a type that is not Data, and an erased -z cannot be matched ("a -
#   scrutinee matches only in a dead region"). So each step is an
#   equation over mirrors instead: the heap's words and value table and
#   the map as Data trees (hp(t0, ta), LAT.fromT(U32, tm)), the step's
#   result rewritten into a pure model of the record's six data fields
#   (Fl), in the same form, so that steps chain by rewriting (br2, brs,
#   emsb). The invariants are then proved on the model, all Data.
# - Each read hands its array back: get_pair for a word or a value,
#   size_pair for the probe's size (the map full at its depth), and a
#   model of the probe (pr.*) generic in its state (P3) for the lookup.
#   A free table entry counts an error, word 1 written: set_tree_eq
#   (lawful-arrays' proof_index.bend) keeps the words a tree (chk_eq).
# - A U32 matched by literals is stuck in a proof's default arm: the
#   node's read dispatches on its kind and P.peek tests its form
#   (cursor-laws.materializer.template.emit.shape), so that nb splits
#   the kind's nineteen constructors and pk_eq three Bools.
# - A pair is not Data: a model taking one takes it linearly (pk.c).
# - The law states any heap and map; its def matches the heap down to
#   its arrays and mirrors each, as find_tree.m does (ec.m, ek.m).
# - The links' laws take the counts as premises and reuse their lemmas
#   (pe_inv, em_inv) for the steps between; a branch's test is carried as
#   an equation (pe.s_k's hst) where a later step needs what it decided.
# - A far port q & 3 off a static is below 3 by lawful-words'
#   to_nat_and_mask, then a case split of the residue (port3_of, p3n).
# - The node's index counts down on words: the last node split off, so
#   that i - 1 is taken only with a node after it (ems_k, cd_i, cd_l).
# - Nat.cmp and Nat.sub match both arguments: split the symbolic one, or
#   rewrite Nat.sub(a, 0n) by sub0. A let does not infer a constructor's
#   type: inline it (push_k).

import Base
import ./FREEZE_LAWS.bend as Laws
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/rules.bend as R
import ../spike/tpl.bend as T
import ../spike/net.bend as N
import ./ring.bend as RN
import ./freeze.bend as F
import ./freeze_model.bend as FM
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MN
import 0x8ae61ec3a6615abd35f196c07232ad28/u32.bend as MU
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/LAWS.bend as LA
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/PROOF.bend as LAP
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_tree.bend as LAT
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_index.bend as LAI
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/defs.bend as AD
import 0x96ab58f86121cb4f3fb48b3c8a045989/LAWS.bend as WL
import 0x96ab58f86121cb4f3fb48b3c8a045989/PROOF.bend as WP
import ./splice_model.bend as SM

# --- the probe, modelled on a mirrored map

type P3 is Data:
  P3{+i: U32, +done: Bool, +v: U32}

def mk3(a: Array<U32>, +p: P3) -> F.Hp:
  match p:
    case P3{+i, +done, +v}:
      F.Hp{a, i, done, v}

def p3.v(+p: P3) -> U32:
  match p:
    case P3{+i, +done, +v}:
      v

def wd(+tm: LAT.Tree<U32>, +x: U32) -> U32:
  Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, tm), x))

def pr.c(+hit: Bool, +empty: Bool, +tm: LAT.Tree<U32>, +i: U32, +mask: U32) -> P3:
  match hit:
    case True{}:
      P3{i, True{}, wd(tm, ((i << 1n : U32) + 1 : U32))}
    case False{}:
      match empty:
        case True{}:
          P3{i, True{}, 0}
        case False{}:
          P3{((i + 1 : U32) .&. mask : U32), False{}, 0}

def pr.d(+done: Bool, +tm: LAT.Tree<U32>, +b: U32, +i: U32, +mask: U32, +v: U32) -> P3:
  match done:
    case True{}:
      P3{i, True{}, v}
    case False{}:
      pr.c(U32.is_eq(wd(tm, (i << 1n : U32)), b), U32.is_eq(wd(tm, (i << 1n : U32)), 0), tm, i, mask)

def pr.go(f: Nat, +tm: LAT.Tree<U32>, +b: U32, +mask: U32, +p: P3) -> P3:
  match f:
    case 0n:
      p
    case 1n+g:
      match p:
        case P3{+i, +done, +v}:
          pr.go(g, tm, b, mask, pr.d(done, tm, b, i, mask, v))

def at_c_eq(+hit: Bool, +empty: Bool, +tm: LAT.Tree<U32>, +i: U32, +mask: U32) ->
  {F.hm.at.c(hit, empty, LAT.fromT(U32, tm), i, mask) == mk3(LAT.fromT(U32, tm), pr.c(hit, empty, tm, i, mask)) : F.Hp}:
  match hit:
    case True{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, tm), ((i << 1n : U32) + 1 : U32)), (LAT.fromT(U32, tm), wd(tm, ((i << 1n : U32) + 1 : U32))), LA.get_pair(U32, LAT.fromT(U32, tm), ((i << 1n : U32) + 1 : U32))) :
        {F.hm.at.v(_, i) == mk3(LAT.fromT(U32, tm), pr.c(True{}, empty, tm, i, mask)) : F.Hp}
      {==}
    case False{}:
      match empty:
        case True{}:
          {==}
        case False{}:
          {==}

def at_d_eq(+done: Bool, +tm: LAT.Tree<U32>, +b: U32, +i: U32, +mask: U32, +v: U32) ->
  {F.hm.at.d(done, LAT.fromT(U32, tm), b, i, mask, v) == mk3(LAT.fromT(U32, tm), pr.d(done, tm, b, i, mask, v)) : F.Hp}:
  match done:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, tm), (i << 1n : U32)), (LAT.fromT(U32, tm), wd(tm, (i << 1n : U32))), LA.get_pair(U32, LAT.fromT(U32, tm), (i << 1n : U32))) :
        {F.hm.at.k(_, b, i, mask) == mk3(LAT.fromT(U32, tm), pr.d(False{}, tm, b, i, mask, v)) : F.Hp}
      at_c_eq(U32.is_eq(wd(tm, (i << 1n : U32)), b), U32.is_eq(wd(tm, (i << 1n : U32)), 0), tm, i, mask)

def go_eq(f: Nat, +tm: LAT.Tree<U32>, +b: U32, +mask: U32, +p: P3) ->
  {F.hm.at.go(f, b, mask, mk3(LAT.fromT(U32, tm), p)) == mk3(LAT.fromT(U32, tm), pr.go(f, tm, b, mask, p)) : F.Hp}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      match p:
        case P3{+i, +done, +v}:
          %Equal.sym(F.Hp, F.hm.at.d(done, LAT.fromT(U32, tm), b, i, mask, v), mk3(LAT.fromT(U32, tm), pr.d(done, tm, b, i, mask, v)), at_d_eq(done, tm, b, i, mask, v)) :
            {F.hm.at.go(g, b, mask, _) == mk3(LAT.fromT(U32, tm), pr.go(1n+g, tm, b, mask, P3{i, done, v})) : F.Hp}
          go_eq(g, tm, b, mask, pr.d(done, tm, b, i, mask, v))
def get_p_eq(+tm: LAT.Tree<U32>, +p: P3) -> {F.hm.get.p(mk3(LAT.fromT(U32, tm), p)) == (LAT.fromT(U32, tm), p3.v(p)) : Array<U32> & U32}:
  match p:
    case P3{+i, +done, +v}:
      {==}

# the probe's start and fuel at depth dm
def mask.d(+dm: Nat) -> U32:
  ((U32.shln(1, dm) >> 1n : U32) - 1 : U32)

def mv(+tm: LAT.Tree<U32>, +dm: Nat, +b: U32) -> U32:
  p3.v(pr.go(U32.to_nat((mask.d(dm) + 1 : U32)), tm, b, mask.d(dm), P3{(F.fz.at(b) .&. mask.d(dm) : U32), False{}, 0}))

# a lookup hands its map back
def get_eq(+tm: LAT.Tree<U32>, +dm: Nat, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +b: U32) ->
  {F.hm.get(LAT.fromT(U32, tm), b) == (LAT.fromT(U32, tm), mv(tm, dm, b)) : Array<U32> & U32}:
  %Equal.sym(Array<U32> & U32, Array.size(U32, LAT.fromT(U32, tm)), (LAT.fromT(U32, tm), U32.shln(1, dm)), LA.size_pair(U32, LAT.fromT(U32, tm), dm, hf)) :
    {F.hm.get.p(F.hm.at(F.hm.mask(_), b)) == (LAT.fromT(U32, tm), mv(tm, dm, b)) : Array<U32> & U32}
  %Equal.sym(F.Hp, F.hm.at.go(U32.to_nat((mask.d(dm) + 1 : U32)), b, mask.d(dm), mk3(LAT.fromT(U32, tm), P3{(F.fz.at(b) .&. mask.d(dm) : U32), False{}, 0})),
      mk3(LAT.fromT(U32, tm), pr.go(U32.to_nat((mask.d(dm) + 1 : U32)), tm, b, mask.d(dm), P3{(F.fz.at(b) .&. mask.d(dm) : U32), False{}, 0})),
      go_eq(U32.to_nat((mask.d(dm) + 1 : U32)), tm, b, mask.d(dm), P3{(F.fz.at(b) .&. mask.d(dm) : U32), False{}, 0})) :
    {F.hm.get.p(_) == (LAT.fromT(U32, tm), mv(tm, dm, b)) : Array<U32> & U32}
  get_p_eq(tm, pr.go(U32.to_nat((mask.d(dm) + 1 : U32)), tm, b, mask.d(dm), P3{(F.fz.at(b) .&. mask.d(dm) : U32), False{}, 0}))

# --- the write phase's data fields, and fz.peer modelled on them

type Fl is Data:
  Fl{nodes: List<&2, T.TNode>, eras: List<&2, T.TNode>, +ne: U32, ls: List<&2, T.TLink>, root: T.TEnd, curs: List<&2, RN.FzC>}

def mk(h: P.H, map: Array<U32>, +f: Fl) -> F.FzE:
  match f:
    case Fl{nodes, eras, +ne, ls, root, curs}:
      F.FzE{h, map, nodes, eras, ne, ls, root, curs}

def hw(+t0: LAT.Tree<U32>, +x: U32) -> U32:
  Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t0), x))

def pe.v(+unf: Bool, +f: Fl, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +v: U32) -> Fl:
  match unf:
    case True{}:
      match f:
        case Fl{nodes, eras, +ne, ls, root, curs}:
          Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}
    case False{}:
      match f:
        case Fl{nodes, eras, +ne, ls, root, curs}:
          Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (v - 1 : U32)) || (U32.is_eq(i, (v - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (v - 1 : U32), (q .&. 3 : U32), ls), root, curs}

def pe.k(+st: Bool, +rt: Bool, +f: Fl, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32) -> Fl:
  match st:
    case True{}:
      match f:
        case Fl{nodes, eras, +ne, ls, root, curs}:
          Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}
    case False{}:
      match rt:
        case True{}:
          match f:
            case Fl{nodes, eras, +ne, ls, root, curs}:
              Fl{nodes, eras, ne, ls, T.TE{i, p}, curs}
        case False{}:
          pe.v(U32.is_eq(mv(tm, dm, P.base(q)), 0), f, k, b, i, p, q, mv(tm, dm, P.base(q)))

def pe.s(+st: Bool, +f: Fl, +t0: LAT.Tree<U32>, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32) -> Fl:
  match st:
    case True{}:
      pe.k(True{}, False{}, f, tm, dm, k, b, i, p, q)
    case False{}:
      pe.k(F.fz.is_era(hw(t0, P.base(q))), U32.is_eq(P.base(q), P.iface()), f, tm, dm, k, b, i, p, q)

def pe(+f: Fl, +t0: LAT.Tree<U32>, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32, +p: U32) -> Fl:
  pe.s(P.is_static(hw(t0, (b + 1 + p : U32))), f, t0, tm, dm, k, b, i, p, hw(t0, (b + 1 + p : U32)))

# a read hands the heap back (INDEX_PROOF.bend's rd_eq, at this file's hw)
def rd_back(+t0: LAT.Tree<U32>, -a: Array<V.Val>, +i: U32) -> {P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, i) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, hw(t0, i)) : P.H & U32}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), i), (LAT.fromT(U32, t0), hw(t0, i)), LA.get_pair(U32, LAT.fromT(U32, t0), i)) :
    {P.rd.fin(KM.m_get.fin(_), a) == (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, hw(t0, i)) : P.H & U32}
  {==}

def br.v(+unf: Bool, +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +tm: LAT.Tree<U32>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +v: U32) ->
  {F.fz.peer.v(unf, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs, k, b, i, p, q, v) == mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), pe.v(unf, Fl{nodes, eras, ne, ls, root, curs}, k, b, i, p, q, v)) : F.FzE}:
  match unf:
    case True{}:
      {==}
    case False{}:
      {==}

def br.k(+st: Bool, +rt: Bool, +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32) ->
  {F.fz.peer.k(st, rt, F.FzE{P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs}, k, b, i, p, q) == mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), pe.k(st, rt, Fl{nodes, eras, ne, ls, root, curs}, tm, dm, k, b, i, p, q)) : F.FzE}:
  match st:
    case True{}:
      {==}
    case False{}:
      match rt:
        case True{}:
          {==}
        case False{}:
          %Equal.sym(Array<U32> & U32, F.hm.get(LAT.fromT(U32, tm), P.base(q)), (LAT.fromT(U32, tm), mv(tm, dm, P.base(q))), get_eq(tm, dm, hf, P.base(q))) :
            {F.fz.peer.j(_, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, nodes, eras, ne, ls, root, curs, k, b, i, p, q) == mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), pe.k(False{}, False{}, Fl{nodes, eras, ne, ls, root, curs}, tm, dm, k, b, i, p, q)) : F.FzE}
          br.v(U32.is_eq(mv(tm, dm, P.base(q)), 0), nodes, eras, ne, ls, root, curs, t0, a, tm, k, b, i, p, q, mv(tm, dm, P.base(q)))

def br.s(+st: Bool, +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32) ->
  {F.fz.peer.s(st, P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs, k, b, i, p, q) == mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), pe.s(st, Fl{nodes, eras, ne, ls, root, curs}, t0, tm, dm, k, b, i, p, q)) : F.FzE}:
  match st:
    case True{}:
      br.k(True{}, False{}, nodes, eras, ne, ls, root, curs, t0, a, tm, dm, hf, k, b, i, p, q)
    case False{}:
      %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, P.base(q)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, hw(t0, P.base(q))), rd_back(t0, a, P.base(q))) :
        {F.fz.peer.e(_, LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs, k, b, i, p, q) == mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), pe.s(False{}, Fl{nodes, eras, ne, ls, root, curs}, t0, tm, dm, k, b, i, p, q)) : F.FzE}
      br.k(F.fz.is_era(hw(t0, P.base(q))), U32.is_eq(P.base(q), P.iface()), nodes, eras, ne, ls, root, curs, t0, a, tm, dm, hf, k, b, i, p, q)

# fz.peer on a mirrored heap and map: the model's fields, the heap and map handed back
def br(+f: Fl, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +k: R.NodeKind, +b: U32, +i: U32, +p: U32) ->
  {F.fz.peer(mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), f), k, b, i, p) == mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), pe(f, t0, tm, dm, k, b, i, p)) : F.FzE}:
  match f:
    case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
      %Equal.sym(P.H & U32, P.rd(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, (b + 1 + p : U32)), (P.H{KM.MG{LAT.fromT(U32, t0)}, a}, hw(t0, (b + 1 + p : U32))), rd_back(t0, a, (b + 1 + p : U32))) :
        {F.fz.peer.q(_, LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs, k, b, i, p) == mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), pe(Fl{nodes, eras, ne, ls, root, curs}, t0, tm, dm, k, b, i, p)) : F.FzE}
      br.s(P.is_static(hw(t0, (b + 1 + p : U32))), nodes, eras, ne, ls, root, curs, t0, a, tm, dm, hf, k, b, i, p, hw(t0, (b + 1 + p : U32)))

# two ports chained: the record's form kept from one to the next
def br2(+f: Fl, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +k: R.NodeKind, +b: U32, +i: U32) ->
  {F.fz.peer(F.fz.peer(mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), f), k, b, i, 0), k, b, i, 1) == mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), pe(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1)) : F.FzE}:
  %Equal.sym(F.FzE, F.fz.peer(mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), f), k, b, i, 0), mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), pe(f, t0, tm, dm, k, b, i, 0)), br(f, t0, a, tm, dm, hf, k, b, i, 0)) :
    {F.fz.peer(_, k, b, i, 1) == mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), pe(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1)) : F.FzE}
  br(pe(f, t0, tm, dm, k, b, i, 0), t0, a, tm, dm, hf, k, b, i, 1)

# --- the node's read, on a heap whose words and value table are mirrored

def hp(+t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>) -> P.H:
  P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}

def tv(+ta: LAT.Tree<V.Val>, +w: U32) -> V.Val:
  Pair.snd(Array<V.Val>, V.Val, Array.get(V.Val, LAT.fromT(V.Val, ta), w))

type TV is Data:
  TV{t: LAT.Tree<U32>, v: V.Val}

type NR is Data:
  NR{t: LAT.Tree<U32>, n: T.TNode}

def tvh(+ta: LAT.Tree<V.Val>, +r: TV) -> P.H & V.Val:
  match r:
    case TV{t, v}:
      (hp(t, ta), v)

def nrh(+ta: LAT.Tree<V.Val>, +r: NR) -> P.H & T.TNode:
  match r:
    case NR{t, n}:
      (hp(t, ta), n)

# the words after an error counted, or not
def et(+bad: Bool, +t0: LAT.Tree<U32>) -> LAT.Tree<U32>:
  match bad:
    case True{}:
      LAI.set_tree(U32, t0, P.at_errs(), (hw(t0, P.at_errs()) + 1 : U32))
    case False{}:
      t0

def pk.c(r: V.Val & Bool, +t0: LAT.Tree<U32>) -> TV:
  match r:
    case (v, +bad):
      TV{et(bad, t0), v}

def pk.k(+one: Bool, +two: Bool, +three: Bool, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +f: U32, +w: U32) -> TV:
  match one:
    case True{}:
      TV{t0, V.VNum{w}}
    case False{}:
      match two:
        case True{}:
          TV{t0, V.VFun{P.bop(f), P.bneed(f), Nil{}}}
        case False{}:
          match three:
            case True{}:
              TV{t0, V.VFun{P.bop(f), P.bneed(f), [V.VNum{w}]}}
            case False{}:
              pk.c(V.free_chk(tv(ta, w)), t0)

def nd.w(+r: TV, +k: R.NodeKind) -> NR:
  match r:
    case TV{t, v}:
      NR{t, T.TN{k, V.PVal{v}}}

def nd.pk(+t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +hd: U32, +w: U32) -> TV:
  pk.k(U32.is_eq(P.form(hd), 1), U32.is_eq(P.form(hd), 2), U32.is_eq(P.form(hd), 3), t0, ta, P.fld(hd), w)

def nd.lift(+k: R.NodeKind, +t0: LAT.Tree<U32>, +f: U32, +w: U32) -> NR:
  NR{t0, T.TN{k, V.PLift{f, U32.is_ge(w, 2147483648), (w .&. 2147483647 : U32)}}}

def nd(+k: R.NodeKind, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +hd: U32, +b: U32) -> NR:
  match k:
    case R.KFn{}:
      NR{t0, F.fz.lv(U32.is_eq(P.form(hd), P.unlev()), R.KFn{}, P.fld(hd))}
    case R.KAp{}:
      NR{t0, F.fz.lv(U32.is_eq(P.form(hd), P.unlev()), R.KAp{}, P.fld(hd))}
    case R.KFnD{}:
      NR{t0, F.fz.lv(U32.is_eq(P.form(hd), P.unlev()), R.KFnD{}, P.fld(hd))}
    case R.KData{}:
      nd.w(nd.pk(t0, ta, hd, hw(t0, (b + 2 : U32))), R.KData{})
    case R.KOp{}:
      nd.w(nd.pk(t0, ta, hd, hw(t0, (b + 3 : U32))), R.KOp{})
    case R.KDOp{}:
      nd.w(nd.pk(t0, ta, hd, hw(t0, (b + 3 : U32))), R.KDOp{})
    case R.KLift{}:
      nd.lift(R.KLift{}, t0, P.fld(hd), hw(t0, (b + 3 : U32)))
    case R.KLiftC{}:
      nd.lift(R.KLiftC{}, t0, P.fld(hd), hw(t0, (b + 3 : U32)))
    case R.KCopy{}:
      NR{t0, F.fz.fan(U32.is_eq(P.form(hd), P.unlev()), R.KCopy{}, P.fld(hd))}
    case R.KMerge{}:
      NR{t0, F.fz.fan(U32.is_eq(P.form(hd), P.unlev()), R.KMerge{}, P.fld(hd))}
    case R.KCopyL{}:
      NR{t0, F.fz.fan(U32.is_eq(P.form(hd), P.unlev()), R.KCopyL{}, P.fld(hd))}
    case R.KCopyR{}:
      NR{t0, F.fz.fan(U32.is_eq(P.form(hd), P.unlev()), R.KCopyR{}, P.fld(hd))}
    case R.KMergeL{}:
      NR{t0, F.fz.fan(U32.is_eq(P.form(hd), P.unlev()), R.KMergeL{}, P.fld(hd))}
    case R.KMergeR{}:
      NR{t0, F.fz.fan(U32.is_eq(P.form(hd), P.unlev()), R.KMergeR{}, P.fld(hd))}
    case _:
      NR{t0, T.TN{k, V.PNone{}}}

# a free entry counts an error: word 1 written, the words' tree with it
def chk_eq(r: V.Val & Bool, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>) -> {P.chk.fin(r, hp(t0, ta)) == tvh(ta, pk.c(r, t0)) : P.H & V.Val}:
  match r:
    case (v, +bad):
      match bad:
        case True{}:
          %Equal.sym(Array<U32> & U32, Array.get(U32, LAT.fromT(U32, t0), P.at_errs()), (LAT.fromT(U32, t0), hw(t0, P.at_errs())), LA.get_pair(U32, LAT.fromT(U32, t0), P.at_errs())) :
            {(P.h_err.n(KM.m_get.fin(_), LAT.fromT(V.Val, ta)), v) == (P.H{KM.MG{LAT.fromT(U32, LAI.set_tree(U32, t0, P.at_errs(), (hw(t0, P.at_errs()) + 1 : U32)))}, LAT.fromT(V.Val, ta)}, v) : P.H & V.Val}
          %LAI.set_tree_eq(U32, t0, P.at_errs(), (hw(t0, P.at_errs()) + 1 : U32)) :
            {(P.H{KM.MG{Array.set(U32, LAT.fromT(U32, t0), P.at_errs(), (hw(t0, P.at_errs()) + 1 : U32))}, LAT.fromT(V.Val, ta)}, v) == (P.H{KM.MG{_}, LAT.fromT(V.Val, ta)}, v) : P.H & V.Val}
          {==}
        case False{}:
          {==}

def pk_eq(+one: Bool, +two: Bool, +three: Bool, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +f: U32, +w: U32) ->
  {P.peek.k(one, two, three, hp(t0, ta), f, w) == tvh(ta, pk.k(one, two, three, t0, ta, f, w)) : P.H & V.Val}:
  match one:
    case True{}:
      {==}
    case False{}:
      match two:
        case True{}:
          {==}
        case False{}:
          match three:
            case True{}:
              {==}
            case False{}:
              %Equal.sym(Array<V.Val> & V.Val, Array.get(V.Val, LAT.fromT(V.Val, ta), w), (LAT.fromT(V.Val, ta), tv(ta, w)), LA.get_pair(V.Val, LAT.fromT(V.Val, ta), w)) :
                {P.chk(P.tab_get.fin(_, KM.MG{LAT.fromT(U32, t0)})) == tvh(ta, pk.k(False{}, False{}, False{}, t0, ta, f, w)) : P.H & V.Val}
              chk_eq(V.free_chk(tv(ta, w)), t0, ta)

def val_eq(+ta: LAT.Tree<V.Val>, +r: TV, +k: R.NodeKind) -> {F.fz.val(tvh(ta, r), k) == nrh(ta, nd.w(r, k)) : P.H & T.TNode}:
  match r:
    case TV{t, v}:
      {==}

def nb.w(+t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +hd: U32, +w: U32, +k: R.NodeKind) ->
  {F.fz.val(P.peek(hp(t0, ta), P.form(hd), P.fld(hd), w), k) == nrh(ta, nd.w(nd.pk(t0, ta, hd, w), k)) : P.H & T.TNode}:
  %Equal.sym(P.H & V.Val, P.peek.k(U32.is_eq(P.form(hd), 1), U32.is_eq(P.form(hd), 2), U32.is_eq(P.form(hd), 3), hp(t0, ta), P.fld(hd), w), tvh(ta, nd.pk(t0, ta, hd, w)),
      pk_eq(U32.is_eq(P.form(hd), 1), U32.is_eq(P.form(hd), 2), U32.is_eq(P.form(hd), 3), t0, ta, P.fld(hd), w)) :
    {F.fz.val(_, k) == nrh(ta, nd.w(nd.pk(t0, ta, hd, w), k)) : P.H & T.TNode}
  val_eq(ta, nd.pk(t0, ta, hd, w), k)

# the node's read hands the heap back, an error's word written
def nb(+k: R.NodeKind, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +hd: U32, +b: U32) -> {F.fz.node.k(k, hp(t0, ta), hd, b) == nrh(ta, nd(k, t0, ta, hd, b)) : P.H & T.TNode}:
  match k:
    case R.KFree{}:
      {==}
    case R.KFn{}:
      {==}
    case R.KAp{}:
      {==}
    case R.KCopy{}:
      {==}
    case R.KMerge{}:
      {==}
    case R.KData{}:
      %Equal.sym(P.H & U32, P.rd(hp(t0, ta), (b + 2 : U32)), (hp(t0, ta), hw(t0, (b + 2 : U32))), rd_back(t0, LAT.fromT(V.Val, ta), (b + 2 : U32))) :
        {F.fz.word(_, R.KData{}, hd) == nrh(ta, nd(R.KData{}, t0, ta, hd, b)) : P.H & T.TNode}
      nb.w(t0, ta, hd, hw(t0, (b + 2 : U32)), R.KData{})
    case R.KEraN{}:
      {==}
    case R.KEraP{}:
      {==}
    case R.KRoot{}:
      {==}
    case R.KOp{}:
      %Equal.sym(P.H & U32, P.rd(hp(t0, ta), (b + 3 : U32)), (hp(t0, ta), hw(t0, (b + 3 : U32))), rd_back(t0, LAT.fromT(V.Val, ta), (b + 3 : U32))) :
        {F.fz.word(_, R.KOp{}, hd) == nrh(ta, nd(R.KOp{}, t0, ta, hd, b)) : P.H & T.TNode}
      nb.w(t0, ta, hd, hw(t0, (b + 3 : U32)), R.KOp{})
    case R.KLift{}:
      %Equal.sym(P.H & U32, P.rd(hp(t0, ta), (b + 3 : U32)), (hp(t0, ta), hw(t0, (b + 3 : U32))), rd_back(t0, LAT.fromT(V.Val, ta), (b + 3 : U32))) :
        {F.fz.lift(_, R.KLift{}, P.fld(hd)) == nrh(ta, nd(R.KLift{}, t0, ta, hd, b)) : P.H & T.TNode}
      {==}
    case R.KLiftC{}:
      %Equal.sym(P.H & U32, P.rd(hp(t0, ta), (b + 3 : U32)), (hp(t0, ta), hw(t0, (b + 3 : U32))), rd_back(t0, LAT.fromT(V.Val, ta), (b + 3 : U32))) :
        {F.fz.lift(_, R.KLiftC{}, P.fld(hd)) == nrh(ta, nd(R.KLiftC{}, t0, ta, hd, b)) : P.H & T.TNode}
      {==}
    case R.KCopyL{}:
      {==}
    case R.KCopyR{}:
      {==}
    case R.KMergeL{}:
      {==}
    case R.KMergeR{}:
      {==}
    case R.KDOp{}:
      %Equal.sym(P.H & U32, P.rd(hp(t0, ta), (b + 3 : U32)), (hp(t0, ta), hw(t0, (b + 3 : U32))), rd_back(t0, LAT.fromT(V.Val, ta), (b + 3 : U32))) :
        {F.fz.word(_, R.KDOp{}, hd) == nrh(ta, nd(R.KDOp{}, t0, ta, hd, b)) : P.H & T.TNode}
      nb.w(t0, ta, hd, hw(t0, (b + 3 : U32)), R.KDOp{})
    case R.KFnD{}:
      {==}
    case R.KCur{}:
      {==}

# the ports of a node, at most three
def pes(+f: Fl, +t0: LAT.Tree<U32>, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32, a: Nat) -> Fl:
  match a:
    case 0n:
      f
    case 1n+j:
      match j:
        case 0n:
          pe(f, t0, tm, dm, k, b, i, 0)
        case 1n+x:
          match x:
            case 0n:
              pe(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1)
            case 1n+y:
              pe(pe(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1), t0, tm, dm, k, b, i, 2)

def br3(+f: Fl, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +k: R.NodeKind, +b: U32, +i: U32) ->
  {F.fz.peer(F.fz.peer(F.fz.peer(mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), f), k, b, i, 0), k, b, i, 1), k, b, i, 2) == mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), pe(pe(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1), t0, tm, dm, k, b, i, 2)) : F.FzE}:
  %Equal.sym(F.FzE, F.fz.peer(F.fz.peer(mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), f), k, b, i, 0), k, b, i, 1), mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), pe(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1)), br2(f, t0, a, tm, dm, hf, k, b, i)) :
    {F.fz.peer(_, k, b, i, 2) == mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), pe(pe(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1), t0, tm, dm, k, b, i, 2)) : F.FzE}
  br(pe(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1), t0, a, tm, dm, hf, k, b, i, 2)

def brs(+f: Fl, +t0: LAT.Tree<U32>, -a: Array<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +k: R.NodeKind, +b: U32, +i: U32, n: Nat) ->
  {F.fz.peers(mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), f), k, b, i, n) == mk(P.H{KM.MG{LAT.fromT(U32, t0)}, a}, LAT.fromT(U32, tm), pes(f, t0, tm, dm, k, b, i, n)) : F.FzE}:
  match n:
    case 0n:
      {==}
    case 1n+j:
      match j:
        case 0n:
          br(f, t0, a, tm, dm, hf, k, b, i, 0)
        case 1n+x:
          match x:
            case 0n:
              br2(f, t0, a, tm, dm, hf, k, b, i)
            case 1n+y:
              br3(f, t0, a, tm, dm, hf, k, b, i)

# --- a node and its ports; the nodes in turn

type ST is Data:
  ST{t: LAT.Tree<U32>, f: Fl}

def mkS(+ta: LAT.Tree<V.Val>, map: Array<U32>, +s: ST) -> F.FzE:
  match s:
    case ST{+t, +f}:
      mk(hp(t, ta), map, f)

def em.t(+r: NR, +f: Fl, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32) -> ST:
  match r:
    case NR{+t, +n}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          ST{t, pes(Fl{Con{n, nodes}, eras, ne, ls, root, curs}, t, tm, dm, k, b, i, R.arity(k))}

def em(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32) -> ST:
  match s:
    case ST{+t, +f}:
      em.t(nd(N.kof(P.rk(hw(t, b))), t, ta, hw(t, b), b), f, tm, dm, N.kof(P.rk(hw(t, b))), b, i)

def ems(seen: List<&2, U32>, +s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +i: U32) -> ST:
  match seen:
    case Nil{}:
      s
    case Con{+b, rest}:
      ems(rest, em(s, ta, tm, dm, b, i), ta, tm, dm, (i - 1 : U32))

def emt(+r: NR, +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +k: R.NodeKind, +b: U32, +i: U32) ->
  {F.fz.emit.t(nrh(ta, r), LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs, k, b, i) == mkS(ta, LAT.fromT(U32, tm), em.t(r, Fl{nodes, eras, ne, ls, root, curs}, tm, dm, k, b, i)) : F.FzE}:
  match r:
    case NR{+t, +n}:
      brs(Fl{Con{n, nodes}, eras, ne, ls, root, curs}, t, LAT.fromT(V.Val, ta), tm, dm, hf, k, b, i, R.arity(k))

def emb(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +b: U32, +i: U32) ->
  {F.fz.emit(mkS(ta, LAT.fromT(U32, tm), s), b, i) == mkS(ta, LAT.fromT(U32, tm), em(s, ta, tm, dm, b, i)) : F.FzE}:
  match s:
    case ST{+t, +f}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          %Equal.sym(P.H & U32, P.rd(hp(t, ta), b), (hp(t, ta), hw(t, b)), rd_back(t, LAT.fromT(V.Val, ta), b)) :
            {F.fz.emit.hd(_, LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs, b, i) == mkS(ta, LAT.fromT(U32, tm), em(ST{t, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, b, i)) : F.FzE}
          %Equal.sym(P.H & T.TNode, F.fz.node.k(N.kof(P.rk(hw(t, b))), hp(t, ta), hw(t, b), b), nrh(ta, nd(N.kof(P.rk(hw(t, b))), t, ta, hw(t, b), b)), nb(N.kof(P.rk(hw(t, b))), t, ta, hw(t, b), b)) :
            {F.fz.emit.t(_, LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs, N.kof(P.rk(hw(t, b))), b, i) == mkS(ta, LAT.fromT(U32, tm), em(ST{t, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, b, i)) : F.FzE}
          emt(nd(N.kof(P.rk(hw(t, b))), t, ta, hw(t, b), b), nodes, eras, ne, ls, root, curs, ta, tm, dm, hf, N.kof(P.rk(hw(t, b))), b, i)

# the write phase's nodes, on mirrors: the model's state, the heap's words
# as the reads left them, the value table and the map handed back
def emsb(seen: List<&2, U32>, +s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +i: U32) ->
  {F.fz.emits(seen, mkS(ta, LAT.fromT(U32, tm), s), i) == mkS(ta, LAT.fromT(U32, tm), ems(seen, s, ta, tm, dm, i)) : F.FzE}:
  match seen:
    case Nil{}:
      {==}
    case Con{+b, rest}:
      %Equal.sym(F.FzE, F.fz.emit(mkS(ta, LAT.fromT(U32, tm), s), b, i), mkS(ta, LAT.fromT(U32, tm), em(s, ta, tm, dm, b, i)), emb(s, ta, tm, dm, hf, b, i)) :
        {F.fz.emits(rest, _, (i - 1 : U32)) == mkS(ta, LAT.fromT(U32, tm), ems(Con{b, rest}, s, ta, tm, dm, i)) : F.FzE}
      emsb(rest, em(s, ta, tm, dm, b, i), ta, tm, dm, hf, (i - 1 : U32))

# --- the count, on the model

def u32_refl(+x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  Equal.trans(Bool, U32.is_eq(x, x), Nat.is_eq(U32.to_nat(x), U32.to_nat(x)), True{}, MU.u32_is_eq_to_nat(x, x), MN.is_eq_refl(U32.to_nat(x)))

def u32_eq(+a: U32, +b: U32, +h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  MU.u32_to_nat_inj(a, b, MN.eq_of_is_eq(U32.to_nat(a), U32.to_nat(b),
    Equal.trans(Bool, Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), U32.is_eq(a, b), True{}, Equal.sym(Bool, U32.is_eq(a, b), Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), MU.u32_is_eq_to_nat(a, b)), h)))

def inv.fl(+f: Fl, +n0: U32) -> Bool:
  match f:
    case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
      FM.inv.f(eras, ne, curs, n0)

def inv.s(+s: ST, +n0: U32) -> Bool:
  match s:
    case ST{+t, +f}:
      inv.fl(f, n0)

# a static's eraser pushed: the next index one more, the holes as they were
def era_inv(+pol: R.Pol, +eras: List<&2, T.TNode>, +ne: U32, +curs: List<&2, RN.FzC>, +n0: U32, +h: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}) ->
  {FM.inv.f(Con{F.fz.era(pol), eras}, (ne + 1 : U32), curs, n0) == True{} : Bool}:
  match pol:
    case R.Neg{}:
      +e = u32_eq(ne, FM.er.top(eras, n0), MB.eq_true_of_and_left(U32.is_eq(ne, FM.er.top(eras, n0)), FM.lsteq(FM.ats(curs), FM.er.holes(eras, n0)), h))
      %Equal.sym(U32, ne, FM.er.top(eras, n0), e) : {FM.inv.f(Con{F.fz.era(R.Neg{}), eras}, (_ + 1 : U32), curs, n0) == True{} : Bool}
      MB.and_eq_true(U32.is_eq((FM.er.top(eras, n0) + 1 : U32), (FM.er.top(eras, n0) + 1 : U32)), FM.lsteq(FM.ats(curs), FM.er.holes(eras, n0)), u32_refl((FM.er.top(eras, n0) + 1 : U32)),
        MB.eq_true_of_and_right(U32.is_eq(ne, FM.er.top(eras, n0)), FM.lsteq(FM.ats(curs), FM.er.holes(eras, n0)), h))
    case R.Pos{}:
      +e = u32_eq(ne, FM.er.top(eras, n0), MB.eq_true_of_and_left(U32.is_eq(ne, FM.er.top(eras, n0)), FM.lsteq(FM.ats(curs), FM.er.holes(eras, n0)), h))
      %Equal.sym(U32, ne, FM.er.top(eras, n0), e) : {FM.inv.f(Con{F.fz.era(R.Pos{}), eras}, (_ + 1 : U32), curs, n0) == True{} : Bool}
      MB.and_eq_true(U32.is_eq((FM.er.top(eras, n0) + 1 : U32), (FM.er.top(eras, n0) + 1 : U32)), FM.lsteq(FM.ats(curs), FM.er.holes(eras, n0)), u32_refl((FM.er.top(eras, n0) + 1 : U32)),
        MB.eq_true_of_and_right(U32.is_eq(ne, FM.er.top(eras, n0)), FM.lsteq(FM.ats(curs), FM.er.holes(eras, n0)), h))

# a cursor's placeholder pushed, its crossing at its index
def hole_inv(+pol: R.Pol, +eras: List<&2, T.TNode>, +ne: U32, +curs: List<&2, RN.FzC>, +n0: U32, +src: U32, +neg: Bool, +far: U32, +h: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}) ->
  {FM.inv.f(Con{F.fz.hole(pol), eras}, (ne + 1 : U32), Con{RN.FzC{ne, src, neg, far}, curs}, n0) == True{} : Bool}:
  +e = u32_eq(ne, FM.er.top(eras, n0), MB.eq_true_of_and_left(U32.is_eq(ne, FM.er.top(eras, n0)), FM.lsteq(FM.ats(curs), FM.er.holes(eras, n0)), h))
  %Equal.sym(U32, ne, FM.er.top(eras, n0), e) : {FM.inv.f(Con{F.fz.hole(pol), eras}, (_ + 1 : U32), Con{RN.FzC{_, src, neg, far}, curs}, n0) == True{} : Bool}
  MB.and_eq_true(U32.is_eq((FM.er.top(eras, n0) + 1 : U32), (FM.er.top(eras, n0) + 1 : U32)), U32.is_eq(FM.er.top(eras, n0), FM.er.top(eras, n0)) && FM.lsteq(FM.ats(curs), FM.er.holes(eras, n0)), u32_refl((FM.er.top(eras, n0) + 1 : U32)),
    MB.and_eq_true(U32.is_eq(FM.er.top(eras, n0), FM.er.top(eras, n0)), FM.lsteq(FM.ats(curs), FM.er.holes(eras, n0)), u32_refl(FM.er.top(eras, n0)),
      MB.eq_true_of_and_right(U32.is_eq(ne, FM.er.top(eras, n0)), FM.lsteq(FM.ats(curs), FM.er.holes(eras, n0)), h)))

def pe.v_inv(+unf: Bool, +f: Fl, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +v: U32, +n0: U32, +h: {inv.fl(f, n0) == True{} : Bool}) ->
  {inv.fl(pe.v(unf, f, k, b, i, p, q, v), n0) == True{} : Bool}:
  match unf:
    case True{}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          hole_inv(R.port_pol(k, U32.to_nat(p)), eras, ne, curs, n0, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q, h)
    case False{}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          h

def pe.k_inv(+st: Bool, +rt: Bool, +f: Fl, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: U32, +h: {inv.fl(f, n0) == True{} : Bool}) ->
  {inv.fl(pe.k(st, rt, f, tm, dm, k, b, i, p, q), n0) == True{} : Bool}:
  match st:
    case True{}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          era_inv(R.port_pol(k, U32.to_nat(p)), eras, ne, curs, n0, h)
    case False{}:
      match rt:
        case True{}:
          match f:
            case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
              h
        case False{}:
          pe.v_inv(U32.is_eq(mv(tm, dm, P.base(q)), 0), f, k, b, i, p, q, mv(tm, dm, P.base(q)), n0, h)

def pe.s_inv(+st: Bool, +f: Fl, +t0: LAT.Tree<U32>, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: U32, +h: {inv.fl(f, n0) == True{} : Bool}) ->
  {inv.fl(pe.s(st, f, t0, tm, dm, k, b, i, p, q), n0) == True{} : Bool}:
  match st:
    case True{}:
      pe.k_inv(True{}, False{}, f, tm, dm, k, b, i, p, q, n0, h)
    case False{}:
      pe.k_inv(F.fz.is_era(hw(t0, P.base(q))), U32.is_eq(P.base(q), P.iface()), f, tm, dm, k, b, i, p, q, n0, h)

def pe_inv(+f: Fl, +t0: LAT.Tree<U32>, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: U32, +h: {inv.fl(f, n0) == True{} : Bool}) ->
  {inv.fl(pe(f, t0, tm, dm, k, b, i, p), n0) == True{} : Bool}:
  pe.s_inv(P.is_static(hw(t0, (b + 1 + p : U32))), f, t0, tm, dm, k, b, i, p, hw(t0, (b + 1 + p : U32)), n0, h)

def pes_inv(+f: Fl, +t0: LAT.Tree<U32>, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32, a: Nat, +n0: U32, +h: {inv.fl(f, n0) == True{} : Bool}) ->
  {inv.fl(pes(f, t0, tm, dm, k, b, i, a), n0) == True{} : Bool}:
  match a:
    case 0n:
      h
    case 1n+j:
      match j:
        case 0n:
          pe_inv(f, t0, tm, dm, k, b, i, 0, n0, h)
        case 1n+x:
          match x:
            case 0n:
              pe_inv(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1, n0, pe_inv(f, t0, tm, dm, k, b, i, 0, n0, h))
            case 1n+y:
              pe_inv(pe(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1), t0, tm, dm, k, b, i, 2, n0,
                pe_inv(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1, n0, pe_inv(f, t0, tm, dm, k, b, i, 0, n0, h)))

def em.t_inv(+r: NR, +f: Fl, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32, +n0: U32, +h: {inv.fl(f, n0) == True{} : Bool}) ->
  {inv.s(em.t(r, f, tm, dm, k, b, i), n0) == True{} : Bool}:
  match r:
    case NR{+t, +n}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          pes_inv(Fl{Con{n, nodes}, eras, ne, ls, root, curs}, t, tm, dm, k, b, i, R.arity(k), n0, h)

def em_inv(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +n0: U32, +h: {inv.s(s, n0) == True{} : Bool}) ->
  {inv.s(em(s, ta, tm, dm, b, i), n0) == True{} : Bool}:
  match s:
    case ST{+t, +f}:
      em.t_inv(nd(N.kof(P.rk(hw(t, b))), t, ta, hw(t, b), b), f, tm, dm, N.kof(P.rk(hw(t, b))), b, i, n0, h)

def ems_inv(seen: List<&2, U32>, +s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +i: U32, +n0: U32, +h: {inv.s(s, n0) == True{} : Bool}) ->
  {inv.s(ems(seen, s, ta, tm, dm, i), n0) == True{} : Bool}:
  match seen:
    case Nil{}:
      h
    case Con{+b, rest}:
      ems_inv(rest, em(s, ta, tm, dm, b, i), ta, tm, dm, (i - 1 : U32), n0, em_inv(s, ta, tm, dm, b, i, n0, h))

def inv_mkS(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +n0: U32) -> {FM.inv(mkS(ta, LAT.fromT(U32, tm), s), n0) == inv.s(s, n0) : Bool}:
  match s:
    case ST{+t, +f}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          {==}

# --- the law, on mirrors, then on any heap and map

def ec.k(+seen: List<&2, U32>, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +n0: U32, +i: U32,
  +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +hz: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}) ->
  {FM.inv(F.fz.emits(seen, F.FzE{hp(t0, ta), LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}:
  %Equal.sym(F.FzE, F.fz.emits(seen, mkS(ta, LAT.fromT(U32, tm), ST{t0, Fl{nodes, eras, ne, ls, root, curs}}), i), mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), emsb(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, hf, i)) :
    {FM.inv(_, n0) == True{} : Bool}
  %Equal.sym(Bool, FM.inv(mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), n0), inv.s(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i), n0), inv_mkS(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i), ta, tm, n0)) :
    {_ == True{} : Bool}
  ems_inv(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i, n0, hz)

def ec.m(+seen: List<&2, U32>, -A: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +dm: Nat, hf: {AD.full(U32, map, dm) == True{} : Bool}, +n0: U32, +i: U32,
  +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +hz: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool},
  m0: LAT.Mirror(U32, A), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {FM.inv(F.fz.emits(seen, F.FzE{P.H{KM.MG{A}, a}, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}:
  (+t0, +e0) = m0
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, map, tm, dm, em, hf)
  %e0 : {FM.inv(F.fz.emits(seen, F.FzE{P.H{KM.MG{_}, a}, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}
  %ea : {FM.inv(F.fz.emits(seen, F.FzE{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}
  %em : {FM.inv(F.fz.emits(seen, F.FzE{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, _, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}
  ec.k(seen, t0, ta, tm, dm, hft, n0, i, nodes, eras, ne, ls, root, curs, hz)

def Laws.emits_counts(seen, h, map, dm, hf, n0, i, nodes, eras, ne, ls, root, curs, hz):
  match h:
    case P.H{w, a}:
      match w:
        case KM.MG{A}:
          ec.m(seen, A, a, map, dm, hf, n0, i, nodes, eras, ne, ls, root, curs, hz, LAT.mirror(U32, A), LAT.mirror(V.Val, a), LAT.mirror(U32, map))

# --- the links, on the model (emits_links)

def or_l(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}) -> {(a || b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({(False{} || b) == True{} : Bool}, MB.false_ne_true()(ha))

def or_r(+a: Bool, +b: Bool, +hb: {b == True{} : Bool}) -> {(a || b) == True{} : Bool}:
  %Equal.sym(Bool, b, True{}, hb) : {(a || _) == True{} : Bool}
  MB.or_true(a)

def inv.kl(+f: Fl, +n0: U32) -> Bool:
  match f:
    case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
      FM.inv.k(ls, eras, n0)

def inv.ks(+s: ST, +n0: U32) -> Bool:
  match s:
    case ST{+t, +f}:
      inv.kl(f, n0)

# a link from a node read back to port 0 of the next index reaches it
def lk_new(+i: U32, +p: U32, +ne: U32, +top: U32, +n0: U32, +hi: {U32.is_lt(i, n0) == True{} : Bool}, +he: {U32.is_eq(ne, top) == True{} : Bool}) ->
  {FM.lk.to(T.TL{T.TE{i, p}, T.TE{ne, 0}}, n0, top) == True{} : Bool}:
  MB.and_eq_true(U32.is_lt(i, n0), U32.is_eq(ne, top) && U32.is_eq(0, 0), hi, MB.and_eq_true(U32.is_eq(ne, top), U32.is_eq(0, 0), he, {==}))

def to_cons(+l: T.TLink, +ls: List<&2, T.TLink>, +n0: U32, +e: U32, +h: {FM.lks.to(ls, n0, e) == True{} : Bool}) -> {FM.lks.to(Con{l, ls}, n0, e) == True{} : Bool}:
  or_r(FM.lk.to(l, n0, e), FM.lks.to(ls, n0, e), h)

# a link added, each index still linked
def all_cons(es: List<&2, U32>, +l: T.TLink, +ls: List<&2, T.TLink>, +n0: U32, +h: {FM.all.to(es, ls, n0) == True{} : Bool}) -> {FM.all.to(es, Con{l, ls}, n0) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, r}:
      MB.and_eq_true(FM.lks.to(Con{l, ls}, n0, e), FM.all.to(r, Con{l, ls}, n0),
        to_cons(l, ls, n0, e, MB.eq_true_of_and_left(FM.lks.to(ls, n0, e), FM.all.to(r, ls, n0), h)),
        all_cons(r, l, ls, n0, MB.eq_true_of_and_right(FM.lks.to(ls, n0, e), FM.all.to(r, ls, n0), h)))

def add_k(+l: T.TLink, +ls: List<&2, T.TLink>, +eras: List<&2, T.TNode>, +n0: U32, +hl: {FM.lk.ok(l, n0) == True{} : Bool}, +h: {FM.inv.k(ls, eras, n0) == True{} : Bool}) -> {FM.inv.k(Con{l, ls}, eras, n0) == True{} : Bool}:
  MB.and_eq_true(FM.lks.ok(Con{l, ls}, n0), FM.all.to(FM.er.idx(eras, n0), Con{l, ls}, n0),
    MB.and_eq_true(FM.lk.ok(l, n0), FM.lks.ok(ls, n0), hl, MB.eq_true_of_and_left(FM.lks.ok(ls, n0), FM.all.to(FM.er.idx(eras, n0), ls, n0), h)),
    all_cons(FM.er.idx(eras, n0), l, ls, n0, MB.eq_true_of_and_right(FM.lks.ok(ls, n0), FM.all.to(FM.er.idx(eras, n0), ls, n0), h)))

# an eraser or a placeholder pushed with its link: its index linked at its port 0
def push_k(+t: T.TNode, +eras: List<&2, T.TNode>, +ne: U32, +curs: List<&2, RN.FzC>, +ls: List<&2, T.TLink>, +n0: U32, +i: U32, +p: U32,
  +hc: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}, +hk: {FM.inv.k(ls, eras, n0) == True{} : Bool}, +hi: {U32.is_lt(i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) ->
  {FM.inv.k(Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, Con{t, eras}, n0) == True{} : Bool}:
  +top = FM.er.top(eras, n0)
  +he = MB.eq_true_of_and_left(U32.is_eq(ne, top), FM.lsteq(FM.ats(curs), FM.er.holes(eras, n0)), hc)
  MB.and_eq_true(FM.lks.ok(Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, n0), FM.all.to(Con{top, FM.er.idx(eras, n0)}, Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, n0),
    MB.and_eq_true(FM.lk.ok(T.TL{T.TE{i, p}, T.TE{ne, 0}}, n0), FM.lks.ok(ls, n0), MB.and_eq_true(U32.is_lt(i, n0), SM.port3(p) && SM.port3(0), hi, MB.and_eq_true(SM.port3(p), SM.port3(0), hp, {==})),
      MB.eq_true_of_and_left(FM.lks.ok(ls, n0), FM.all.to(FM.er.idx(eras, n0), ls, n0), hk)),
    MB.and_eq_true(FM.lks.to(Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, n0, top), FM.all.to(FM.er.idx(eras, n0), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, n0),
      or_l(FM.lk.to(T.TL{T.TE{i, p}, T.TE{ne, 0}}, n0, top), FM.lks.to(ls, n0, top), lk_new(i, p, ne, top, n0, hi, he)),
      all_cons(FM.er.idx(eras, n0), T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls, n0, MB.eq_true_of_and_right(FM.lks.ok(ls, n0), FM.all.to(FM.er.idx(eras, n0), ls, n0), hk))))

# a word below 4, not 3, is a port below 3
def p3n(+m: Nat, +hlt: {Nat.is_lt(m, 4n) == True{} : Bool}, +hne: {Nat.is_eq(m, 3n) == False{} : Bool}) -> {(Nat.is_eq(m, 0n) || (Nat.is_eq(m, 1n) || Nat.is_eq(m, 2n))) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  Empty.absurd({(Nat.is_eq(3n, 0n) || (Nat.is_eq(3n, 1n) || Nat.is_eq(3n, 2n))) == True{} : Bool}, MB.true_ne_false()(hne))
                case 1n+d:
                  match d:
                    case 0n:
                      Empty.absurd({(Nat.is_eq(1n+1n+1n+1n+0n, 0n) || (Nat.is_eq(1n+1n+1n+1n+0n, 1n) || Nat.is_eq(1n+1n+1n+1n+0n, 2n))) == True{} : Bool}, MB.false_ne_true()(hlt))
                    case 1n+e:
                      Empty.absurd({(Nat.is_eq(1n+1n+1n+1n+1n+e, 0n) || (Nat.is_eq(1n+1n+1n+1n+1n+e, 1n) || Nat.is_eq(1n+1n+1n+1n+1n+e, 2n))) == True{} : Bool}, MB.false_ne_true()(hlt))

# the port of a word not a static's is below 3
def port3_of(+q: U32, +h: {P.is_static(q) == False{} : Bool}) -> {SM.port3((q .&. 3 : U32)) == True{} : Bool}:
  +x = (q .&. 3 : U32)
  +m = Nat.mod(U32.to_nat(q), 4n)
  +em = WL.to_nat_and_mask(q, 3, 2n, {==})
  +hne = Equal.trans(Bool, Nat.is_eq(m, 3n), U32.is_eq(x, 3), False{},
    Equal.trans(Bool, Nat.is_eq(m, 3n), Nat.is_eq(U32.to_nat(x), 3n), U32.is_eq(x, 3), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 3n), m, U32.to_nat(x), Equal.sym(Nat, U32.to_nat(x), m, em)),
      Equal.sym(Bool, U32.is_eq(x, 3), Nat.is_eq(U32.to_nat(x), 3n), MU.u32_is_eq_to_nat(x, 3))), h)
  %Equal.sym(Bool, U32.is_eq(x, 0), Nat.is_eq(U32.to_nat(x), 0n), MU.u32_is_eq_to_nat(x, 0)) : {(_ || (U32.is_eq(x, 1) || U32.is_eq(x, 2))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(x, 1), Nat.is_eq(U32.to_nat(x), 1n), MU.u32_is_eq_to_nat(x, 1)) : {(Nat.is_eq(U32.to_nat(x), 0n) || (_ || U32.is_eq(x, 2))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(x, 2), Nat.is_eq(U32.to_nat(x), 2n), MU.u32_is_eq_to_nat(x, 2)) : {(Nat.is_eq(U32.to_nat(x), 0n) || (Nat.is_eq(U32.to_nat(x), 1n) || _)) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(x), m, em) : {(Nat.is_eq(_, 0n) || (Nat.is_eq(_, 1n) || Nat.is_eq(_, 2n))) == True{} : Bool}
  p3n(m, WL.nat_mod_lt(U32.to_nat(q), 4n, {==}), hne)

def lkk_k(+first: Bool, +i: U32, +p: U32, +j: U32, +r: U32, +ls: List<&2, T.TLink>, +eras: List<&2, T.TNode>, +n0: U32,
  +hi: {U32.is_lt(i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}, +hr: {SM.port3(r) == True{} : Bool}, +hk: {FM.inv.k(ls, eras, n0) == True{} : Bool}) ->
  {FM.inv.k(F.fz.link.k(first, i, p, j, r, ls), eras, n0) == True{} : Bool}:
  match first:
    case True{}:
      add_k(T.TL{T.TE{i, p}, T.TE{j, r}}, ls, eras, n0, MB.and_eq_true(U32.is_lt(i, n0), SM.port3(p) && SM.port3(r), hi, MB.and_eq_true(SM.port3(p), SM.port3(r), hp, hr)), hk)
    case False{}:
      hk

def pe.v_k(+unf: Bool, +f: Fl, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +v: U32, +n0: U32,
  +hc: {inv.fl(f, n0) == True{} : Bool}, +hk: {inv.kl(f, n0) == True{} : Bool}, +hi: {U32.is_lt(i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}, +hq: {SM.port3((q .&. 3 : U32)) == True{} : Bool}) ->
  {inv.kl(pe.v(unf, f, k, b, i, p, q, v), n0) == True{} : Bool}:
  match unf:
    case True{}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          push_k(F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras, ne, curs, ls, n0, i, p, hc, hk, hi, hp)
    case False{}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          lkk_k(U32.is_lt(i, (v - 1 : U32)) || (U32.is_eq(i, (v - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (v - 1 : U32), (q .&. 3 : U32), ls, eras, n0, hi, hp, hq, hk)

def pe.k_k(+st: Bool, +rt: Bool, +f: Fl, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: U32,
  +hc: {inv.fl(f, n0) == True{} : Bool}, +hk: {inv.kl(f, n0) == True{} : Bool}, +hi: {U32.is_lt(i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}, +hq: {(st || SM.port3((q .&. 3 : U32))) == True{} : Bool}) ->
  {inv.kl(pe.k(st, rt, f, tm, dm, k, b, i, p, q), n0) == True{} : Bool}:
  match st:
    case True{}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          push_k(F.fz.era(R.port_pol(k, U32.to_nat(p))), eras, ne, curs, ls, n0, i, p, hc, hk, hi, hp)
    case False{}:
      match rt:
        case True{}:
          match f:
            case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
              hk
        case False{}:
          pe.v_k(U32.is_eq(mv(tm, dm, P.base(q)), 0), f, k, b, i, p, q, mv(tm, dm, P.base(q)), n0, hc, hk, hi, hp, hq)

def pe.s_k(+st: Bool, +f: Fl, +t0: LAT.Tree<U32>, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: U32,
  +hst: {P.is_static(q) == st : Bool}, +hc: {inv.fl(f, n0) == True{} : Bool}, +hk: {inv.kl(f, n0) == True{} : Bool}, +hi: {U32.is_lt(i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) ->
  {inv.kl(pe.s(st, f, t0, tm, dm, k, b, i, p, q), n0) == True{} : Bool}:
  match st:
    case True{}:
      pe.k_k(True{}, False{}, f, tm, dm, k, b, i, p, q, n0, hc, hk, hi, hp, {==})
    case False{}:
      pe.k_k(F.fz.is_era(hw(t0, P.base(q))), U32.is_eq(P.base(q), P.iface()), f, tm, dm, k, b, i, p, q, n0, hc, hk, hi, hp,
        or_r(F.fz.is_era(hw(t0, P.base(q))), SM.port3((q .&. 3 : U32)), port3_of(q, hst)))

def pe_k(+f: Fl, +t0: LAT.Tree<U32>, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: U32,
  +hc: {inv.fl(f, n0) == True{} : Bool}, +hk: {inv.kl(f, n0) == True{} : Bool}, +hi: {U32.is_lt(i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) ->
  {inv.kl(pe(f, t0, tm, dm, k, b, i, p), n0) == True{} : Bool}:
  pe.s_k(P.is_static(hw(t0, (b + 1 + p : U32))), f, t0, tm, dm, k, b, i, p, hw(t0, (b + 1 + p : U32)), n0, {==}, hc, hk, hi, hp)

def pes_k(+f: Fl, +t0: LAT.Tree<U32>, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32, a: Nat, +n0: U32,
  +hc: {inv.fl(f, n0) == True{} : Bool}, +hk: {inv.kl(f, n0) == True{} : Bool}, +hi: {U32.is_lt(i, n0) == True{} : Bool}) ->
  {inv.kl(pes(f, t0, tm, dm, k, b, i, a), n0) == True{} : Bool}:
  match a:
    case 0n:
      hk
    case 1n+j:
      match j:
        case 0n:
          pe_k(f, t0, tm, dm, k, b, i, 0, n0, hc, hk, hi, {==})
        case 1n+x:
          match x:
            case 0n:
              pe_k(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1, n0, pe_inv(f, t0, tm, dm, k, b, i, 0, n0, hc), pe_k(f, t0, tm, dm, k, b, i, 0, n0, hc, hk, hi, {==}), hi, {==})
            case 1n+y:
              pe_k(pe(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1), t0, tm, dm, k, b, i, 2, n0, pe_inv(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1, n0, pe_inv(f, t0, tm, dm, k, b, i, 0, n0, hc)), pe_k(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1, n0, pe_inv(f, t0, tm, dm, k, b, i, 0, n0, hc), pe_k(f, t0, tm, dm, k, b, i, 0, n0, hc, hk, hi, {==}), hi, {==}), hi, {==})

def em.t_k(+r: NR, +f: Fl, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32, +n0: U32,
  +hc: {inv.fl(f, n0) == True{} : Bool}, +hk: {inv.kl(f, n0) == True{} : Bool}, +hi: {U32.is_lt(i, n0) == True{} : Bool}) ->
  {inv.ks(em.t(r, f, tm, dm, k, b, i), n0) == True{} : Bool}:
  match r:
    case NR{+t, +n}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          pes_k(Fl{Con{n, nodes}, eras, ne, ls, root, curs}, t, tm, dm, k, b, i, R.arity(k), n0, hc, hk, hi)

def em_k(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +n0: U32,
  +hc: {inv.s(s, n0) == True{} : Bool}, +hk: {inv.ks(s, n0) == True{} : Bool}, +hi: {U32.is_lt(i, n0) == True{} : Bool}) ->
  {inv.ks(em(s, ta, tm, dm, b, i), n0) == True{} : Bool}:
  match s:
    case ST{+t, +f}:
      em.t_k(nd(N.kof(P.rk(hw(t, b))), t, ta, hw(t, b), b), f, tm, dm, N.kof(P.rk(hw(t, b))), b, i, n0, hc, hk, hi)

# the countdown: a node after the first, at the index one less, still below n0
def lt_succ_r(+y: Nat, +z: Nat, +h: {Nat.is_lt(y, z) == True{} : Bool}) -> {Nat.is_lt(y, 1n+z) == True{} : Bool}:
  match y:
    case 0n:
      {==}
    case 1n+a:
      match z:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+a, 1n+0n) == True{} : Bool}, MB.false_ne_true()(h))
        case 1n+c:
          lt_succ_r(a, c, h)

def sub0(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+c:
      {==}

def lt_pred(+y: Nat, +z: Nat, +h: {Nat.is_lt(y, z) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(y, 1n), z) == True{} : Bool}:
  match y:
    case 0n:
      h
    case 1n+a:
      match z:
        case 0n:
          Empty.absurd({Nat.is_lt(Nat.sub(1n+a, 1n), 0n) == True{} : Bool}, MB.false_ne_true()(h))
        case 1n+c:
          %Equal.sym(Nat, Nat.sub(a, 0n), a, sub0(a)) : {Nat.is_lt(_, 1n+c) == True{} : Bool}
          lt_succ_r(a, c, h)

def le_one(+L: Nat, +y: Nat, +h: {Nat.is_le(1n+L, y) == True{} : Bool}) -> {Nat.is_le(1n, y) == True{} : Bool}:
  match y:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, MB.false_ne_true()(h))
    case 1n+c:
      match c:
        case 0n:
          {==}
        case 1n+e:
          {==}

def le_pred(+L: Nat, +y: Nat, +h: {Nat.is_le(1n+L, y) == True{} : Bool}) -> {Nat.is_le(1n+L, 1n+Nat.sub(y, 1n)) == True{} : Bool}:
  match y:
    case 0n:
      Empty.absurd({Nat.is_le(1n+L, 1n+Nat.sub(0n, 1n)) == True{} : Bool}, MB.false_ne_true()(h))
    case 1n+c:
      %Equal.sym(Nat, Nat.sub(c, 0n), c, sub0(c)) : {Nat.is_le(1n+L, 1n+_) == True{} : Bool}
      h

def cd_one(+i: U32, +L: Nat, +hl: {Nat.is_le(1n+L, U32.to_nat(i)) == True{} : Bool}) -> {U32.is_le(1, i) == True{} : Bool}:
  Equal.trans(Bool, U32.is_le(1, i), Nat.is_le(1n, U32.to_nat(i)), True{}, MU.u32_is_le_to_nat(1, i), le_one(L, U32.to_nat(i), hl))

def cd_l(+i: U32, +L: Nat, +hl: {Nat.is_le(1n+L, U32.to_nat(i)) == True{} : Bool}) -> {Nat.is_le(1n+L, 1n+U32.to_nat((i - 1 : U32))) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat((i - 1 : U32)), Nat.sub(U32.to_nat(i), 1n), WL.to_nat_sub_le(i, 1, cd_one(i, L, hl))) : {Nat.is_le(1n+L, 1n+_) == True{} : Bool}
  le_pred(L, U32.to_nat(i), hl)

def cd_i(+i: U32, +n0: U32, +L: Nat, +hl: {Nat.is_le(1n+L, U32.to_nat(i)) == True{} : Bool}, +hi: {U32.is_lt(i, n0) == True{} : Bool}) -> {U32.is_lt((i - 1 : U32), n0) == True{} : Bool}:
  +hn = Equal.trans(Bool, Nat.is_lt(U32.to_nat(i), U32.to_nat(n0)), U32.is_lt(i, n0), True{}, Equal.sym(Bool, U32.is_lt(i, n0), Nat.is_lt(U32.to_nat(i), U32.to_nat(n0)), MU.u32_is_lt_to_nat(i, n0)), hi)
  %Equal.sym(Bool, U32.is_lt((i - 1 : U32), n0), Nat.is_lt(U32.to_nat((i - 1 : U32)), U32.to_nat(n0)), MU.u32_is_lt_to_nat((i - 1 : U32), n0)) : {_ == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat((i - 1 : U32)), Nat.sub(U32.to_nat(i), 1n), WL.to_nat_sub_le(i, 1, cd_one(i, L, hl))) : {Nat.is_lt(_, U32.to_nat(n0)) == True{} : Bool}
  lt_pred(U32.to_nat(i), U32.to_nat(n0), hn)

def ems_k(seen: List<&2, U32>, +s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +i: U32, +n0: U32,
  +hc: {inv.s(s, n0) == True{} : Bool}, +hk: {inv.ks(s, n0) == True{} : Bool}, +hi: {U32.is_lt(i, n0) == True{} : Bool}, +hl: {Nat.is_le(List.length(&2, U32, seen), 1n+U32.to_nat(i)) == True{} : Bool}) ->
  {inv.ks(ems(seen, s, ta, tm, dm, i), n0) == True{} : Bool}:
  match seen:
    case Nil{}:
      hk
    case Con{+b, rest}:
      match rest:
        case Nil{}:
          em_k(s, ta, tm, dm, b, i, n0, hc, hk, hi)
        case Con{+b2, +r2}:
          ems_k(Con{b2, r2}, em(s, ta, tm, dm, b, i), ta, tm, dm, (i - 1 : U32), n0, em_inv(s, ta, tm, dm, b, i, n0, hc), em_k(s, ta, tm, dm, b, i, n0, hc, hk, hi),
            cd_i(i, n0, List.length(&2, U32, r2), hl, hi), cd_l(i, List.length(&2, U32, r2), hl))

def inv_l_mkS(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +n0: U32) -> {FM.inv.l(mkS(ta, LAT.fromT(U32, tm), s), n0) == inv.ks(s, n0) : Bool}:
  match s:
    case ST{+t, +f}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          {==}

def ek.k(+seen: List<&2, U32>, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +n0: U32, +i: U32,
  +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +hz: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}, +hk: {FM.inv.k(ls, eras, n0) == True{} : Bool},
  +hi: {U32.is_lt(i, n0) == True{} : Bool}, +hl: {Nat.is_le(List.length(&2, U32, seen), 1n+U32.to_nat(i)) == True{} : Bool}) ->
  {FM.inv.l(F.fz.emits(seen, F.FzE{hp(t0, ta), LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}:
  %Equal.sym(F.FzE, F.fz.emits(seen, mkS(ta, LAT.fromT(U32, tm), ST{t0, Fl{nodes, eras, ne, ls, root, curs}}), i), mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), emsb(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, hf, i)) :
    {FM.inv.l(_, n0) == True{} : Bool}
  %Equal.sym(Bool, FM.inv.l(mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), n0), inv.ks(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i), n0), inv_l_mkS(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i), ta, tm, n0)) :
    {_ == True{} : Bool}
  ems_k(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i, n0, hz, hk, hi, hl)

def ek.m(+seen: List<&2, U32>, -A: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +dm: Nat, hf: {AD.full(U32, map, dm) == True{} : Bool}, +n0: U32, +i: U32,
  +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +hz: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}, +hk: {FM.inv.k(ls, eras, n0) == True{} : Bool},
  +hi: {U32.is_lt(i, n0) == True{} : Bool}, +hl: {Nat.is_le(List.length(&2, U32, seen), 1n+U32.to_nat(i)) == True{} : Bool},
  m0: LAT.Mirror(U32, A), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {FM.inv.l(F.fz.emits(seen, F.FzE{P.H{KM.MG{A}, a}, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}:
  (+t0, +e0) = m0
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, map, tm, dm, em, hf)
  %e0 : {FM.inv.l(F.fz.emits(seen, F.FzE{P.H{KM.MG{_}, a}, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}
  %ea : {FM.inv.l(F.fz.emits(seen, F.FzE{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}
  %em : {FM.inv.l(F.fz.emits(seen, F.FzE{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, _, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}
  ek.k(seen, t0, ta, tm, dm, hft, n0, i, nodes, eras, ne, ls, root, curs, hz, hk, hi, hl)

def Laws.emits_links(seen, h, map, dm, hf, n0, i, nodes, eras, ne, ls, root, curs, hz, hk, hi, hl):
  match h:
    case P.H{w, a}:
      match w:
        case KM.MG{A}:
          ek.m(seen, A, a, map, dm, hf, n0, i, nodes, eras, ne, ls, root, curs, hz, hk, hi, hl, LAT.mirror(U32, A), LAT.mirror(V.Val, a), LAT.mirror(U32, map))
