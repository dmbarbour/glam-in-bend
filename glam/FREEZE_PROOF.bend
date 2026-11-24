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
# - The map's values at most n0 (emits_far): a value sits at an odd word,
#   (i << 1) + 1, whose head bit is True after one match on the word
#   (hd_val), so its slot is odd (odd_hd, odd_slot) and its read through
#   get_view a value of the view's odd positions (get_odd). A def is
#   opaque before its definition: inv.jl comes before its lemmas.
# - The model's step ladder (pe.v to em) is written once, a template
#   (em_T) over the invariant, the per-node context and five leaves;
#   each law's instance is its leaves and its own list (ems_c, ems_l,
#   ems_f), its invariant the conjunction of what it rests on (ik, ij).
#   Arrows over + parameters are @+x:A; a leaf is ~l_root, not ~root,
#   which a pattern variable would shadow.
# - The read nodes' kinds (emits_nodes) keep their frame on the current
#   tree: the list's invariant is the words full and each base left with
#   a good header in the current view, kept by an error's write at word
#   1 (et_keeps; an aligned base's slot is 0 mod 4, slot 1 is 1). A
#   hypothesis crosses an equation by ME.subst where lets forbid a
#   rewrite (ems_n). Eraser is tested by S.sp.is_era itself (nd_era).
# - The template's invariant takes its argument at a type parameter (~X);
#   the nodes' count (emits_len) is the template at ~Nat, entered at
#   emt_T with the count one more, since the node's step changes it.

import Base
import ./FREEZE_LAWS.bend as Laws
import ../spike/kprim.bend as P
import ../spike/kmem_grow.bend as KM
import ../spike/val.bend as V
import ../spike/kmodel.bend as KMd
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
import 0x2c172a8ac85e328d5e6af8aa51cec1f8/proof_base.bend as LAB
import 0x96ab58f86121cb4f3fb48b3c8a045989/LAWS.bend as WL
import 0x96ab58f86121cb4f3fb48b3c8a045989/PROOF.bend as WP
import ./splice_model.bend as SM
import ./splice_copy.bend as S

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

# --- the law, on mirrors, then on any heap and map

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

# --- a link's far end, on the model (emits_far)

def mb.le(m: Maybe<&2, U32>, +n0: U32) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+v}:
      U32.is_le(v, n0)

def odd(+s: Nat) -> Bool:
  Nat.is_eq(Nat.mod(s, 2n), 1n)

# a read at an odd position is a value
def get_odd(xs: List<&2, U32>, +s: Nat, +n0: U32, +h: {FM.vals.le(xs, n0) == True{} : Bool}, +hs: {odd(s) == True{} : Bool}) ->
  {mb.le(List.get(&2, U32, xs, s), n0) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{k, r}:
      match r:
        case Nil{}:
          match s:
            case 0n:
              Empty.absurd({mb.le(List.get(&2, U32, [k], 0n), n0) == True{} : Bool}, MB.false_ne_true()(hs))
            case 1n+t:
              {==}
        case Con{+v, rest}:
          match s:
            case 0n:
              Empty.absurd({mb.le(List.get(&2, U32, Con{k, Con{v, rest}}, 0n), n0) == True{} : Bool}, MB.false_ne_true()(hs))
            case 1n+t:
              match t:
                case 0n:
                  MB.eq_true_of_and_left(U32.is_le(v, n0), FM.vals.le(rest, n0), h)
                case 1n+u:
                  get_odd(rest, u, n0, MB.eq_true_of_and_right(U32.is_le(v, n0), FM.vals.le(rest, n0), h),
                    Equal.trans(Bool, odd(u), odd(1n+1n+u), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n), Nat.mod(u, 2n), Nat.mod(1n+1n+u, 2n), Equal.sym(Nat, Nat.mod(1n+1n+u, 2n), Nat.mod(u, 2n), MN.add_mod_left(u, 2n))), hs))

# an odd word's slot at a depth of one or more is odd
def odd_y(+y: Nat) -> {odd(1n+Nat.double(y)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.double(y), Nat.mul(2n, y), MN.double_eq_two_mul(y)) : {Nat.is_eq(Nat.mod(1n+_, 2n), 1n) == True{} : Bool}
  %Equal.sym(Nat, Nat.mod(Nat.add(1n, Nat.mul(2n, y)), 2n), Nat.mod(1n, 2n), MN.add_mul_mod_self_left(1n, 2n, y)) : {Nat.is_eq(_, 1n) == True{} : Bool}
  {==}

# a word's low bit
def hd(+x: U32) -> Bool:
  match x:
    case U32{w}:
      match w:
        case WCon{+b, t}:
          b

def odd_hd(+x: U32, +h: {hd(x) == True{} : Bool}) -> {odd(U32.to_nat(x)) == True{} : Bool}:
  match x:
    case U32{w}:
      match w:
        case WCon{+b, +t}:
          match b:
            case True{}:
              odd_y(Word.to_nat(31n, t))
            case False{}:
              Empty.absurd({odd(U32.to_nat(U32{WCon{False{}, t}})) == True{} : Bool}, MB.false_ne_true()(h))

def hd_val(+i: U32) -> {hd(((i << 1n : U32) + 1 : U32)) == True{} : Bool}:
  match i:
    case U32{w}:
      match w:
        case WCon{+b, +t}:
          {==}

def hd_key(+i: U32) -> {hd((i << 1n : U32)) == False{} : Bool}:
  match i:
    case U32{w}:
      match w:
        case WCon{+b, +t}:
          {==}

def le0(+y: Nat) -> {Nat.is_le(0n, y) == True{} : Bool}:
  match y:
    case 0n:
      {==}
    case 1n+c:
      {==}

def u32_le0(+n0: U32) -> {U32.is_le(0, n0) == True{} : Bool}:
  Equal.trans(Bool, U32.is_le(0, n0), Nat.is_le(0n, U32.to_nat(n0)), True{}, MU.u32_is_le_to_nat(0, n0), le0(U32.to_nat(n0)))

def odd_slot(+x: U32, +dm: Nat, +h1: {Nat.is_le(1n, dm) == True{} : Bool}) -> {odd(AD.slot(x, dm)) == odd(U32.to_nat(x)) : Bool}:
  %Equal.sym(Nat, Nat.mod(Nat.mod(U32.to_nat(x), Nat.pow(2n, dm)), Nat.pow(2n, 1n)), Nat.mod(U32.to_nat(x), Nat.pow(2n, 1n)), WL.nat_mod_mod_pow(U32.to_nat(x), 1n, dm, h1)) : {Nat.is_eq(_, 1n) == odd(U32.to_nat(x)) : Bool}
  {==}

# a value read off the map's odd word is at most n0
def val_le(+tm: LAT.Tree<U32>, +dm: Nat, +h1: {Nat.is_le(1n, dm) == True{} : Bool}, +n0: U32, +x: U32, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +hd32: {Nat.is_lt(dm, 32n) == True{} : Bool},
  +hv: {FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0) == True{} : Bool}, +hx: {hd(x) == True{} : Bool}) -> {U32.is_le(wd(tm, x), n0) == True{} : Bool}:
  +ho = Equal.trans(Bool, odd(AD.slot(x, dm)), odd(U32.to_nat(x)), True{}, odd_slot(x, dm, h1), odd_hd(x, hx))
  %Equal.sym(Maybe<&2, U32>, Some{wd(tm, x)}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot(x, dm)), LA.get_view(U32, LAT.fromT(U32, tm), dm, x, hf, hd32)) : {mb.le(_, n0) == True{} : Bool}
  get_odd(AD.view(U32, LAT.fromT(U32, tm)), AD.slot(x, dm), n0, hv, ho)

# the probe's value at most n0
def c_le(+hit: Bool, +empty: Bool, +tm: LAT.Tree<U32>, +i: U32, +mask: U32, +dm: Nat, +h1: {Nat.is_le(1n, dm) == True{} : Bool}, +n0: U32, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +hd32: {Nat.is_lt(dm, 32n) == True{} : Bool},
  +hv: {FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0) == True{} : Bool}) -> {U32.is_le(p3.v(pr.c(hit, empty, tm, i, mask)), n0) == True{} : Bool}:
  match hit:
    case True{}:
      val_le(tm, dm, h1, n0, ((i << 1n : U32) + 1 : U32), hf, hd32, hv, hd_val(i))
    case False{}:
      match empty:
        case True{}:
          u32_le0(n0)
        case False{}:
          u32_le0(n0)

def d_le(+done: Bool, +tm: LAT.Tree<U32>, +b: U32, +i: U32, +mask: U32, +v: U32, +dm: Nat, +h1: {Nat.is_le(1n, dm) == True{} : Bool}, +n0: U32, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +hd32: {Nat.is_lt(dm, 32n) == True{} : Bool},
  +hv: {FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0) == True{} : Bool}, +hp: {U32.is_le(v, n0) == True{} : Bool}) -> {U32.is_le(p3.v(pr.d(done, tm, b, i, mask, v)), n0) == True{} : Bool}:
  match done:
    case True{}:
      hp
    case False{}:
      c_le(U32.is_eq(wd(tm, (i << 1n : U32)), b), U32.is_eq(wd(tm, (i << 1n : U32)), 0), tm, i, mask, dm, h1, n0, hf, hd32, hv)

def go_le(f: Nat, +tm: LAT.Tree<U32>, +b: U32, +mask: U32, +p: P3, +dm: Nat, +h1: {Nat.is_le(1n, dm) == True{} : Bool}, +n0: U32, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +hd32: {Nat.is_lt(dm, 32n) == True{} : Bool},
  +hv: {FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0) == True{} : Bool}, +hp: {U32.is_le(p3.v(p), n0) == True{} : Bool}) -> {U32.is_le(p3.v(pr.go(f, tm, b, mask, p)), n0) == True{} : Bool}:
  match f:
    case 0n:
      hp
    case 1n+g:
      match p:
        case P3{+i, +done, +v}:
          go_le(g, tm, b, mask, pr.d(done, tm, b, i, mask, v), dm, h1, n0, hf, hd32, hv, d_le(done, tm, b, i, mask, v, dm, h1, n0, hf, hd32, hv, hp))

def mv_le(+tm: LAT.Tree<U32>, +dm: Nat, +h1: {Nat.is_le(1n, dm) == True{} : Bool}, +b: U32, +n0: U32, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +hd32: {Nat.is_lt(dm, 32n) == True{} : Bool},
  +hv: {FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0) == True{} : Bool}) -> {U32.is_le(mv(tm, dm, b), n0) == True{} : Bool}:
  go_le(U32.to_nat((mask.d(dm) + 1 : U32)), tm, b, mask.d(dm), P3{(F.fz.at(b) .&. mask.d(dm) : U32), False{}, 0}, dm, h1, n0, hf, hd32, hv, u32_le0(n0))

# the put side: a key at an even position, a value at most n0 at an odd one
def set_even(xs: List<&2, U32>, +s: Nat, +w: U32, +n0: U32, +h: {FM.vals.le(xs, n0) == True{} : Bool}, +hs: {odd(s) == False{} : Bool}) ->
  {FM.vals.le(List.set(&2, U32, xs, s, w), n0) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{k, r}:
      match r:
        case Nil{}:
          match s:
            case 0n:
              {==}
            case 1n+t:
              {==}
        case Con{+v, rest}:
          match s:
            case 0n:
              h
            case 1n+t:
              match t:
                case 0n:
                  Empty.absurd({FM.vals.le(List.set(&2, U32, Con{k, Con{v, rest}}, 1n, w), n0) == True{} : Bool}, MB.true_ne_false()(hs))
                case 1n+u:
                  MB.and_eq_true(U32.is_le(v, n0), FM.vals.le(List.set(&2, U32, rest, u, w), n0), MB.eq_true_of_and_left(U32.is_le(v, n0), FM.vals.le(rest, n0), h),
                    set_even(rest, u, w, n0, MB.eq_true_of_and_right(U32.is_le(v, n0), FM.vals.le(rest, n0), h),
                      Equal.trans(Bool, odd(u), odd(1n+1n+u), False{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n), Nat.mod(u, 2n), Nat.mod(1n+1n+u, 2n), Equal.sym(Nat, Nat.mod(1n+1n+u, 2n), Nat.mod(u, 2n), MN.add_mod_left(u, 2n))), hs)))

def set_val(xs: List<&2, U32>, +s: Nat, +w: U32, +n0: U32, +h: {FM.vals.le(xs, n0) == True{} : Bool}, +hw: {U32.is_le(w, n0) == True{} : Bool}) ->
  {FM.vals.le(List.set(&2, U32, xs, s, w), n0) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{k, r}:
      match r:
        case Nil{}:
          match s:
            case 0n:
              {==}
            case 1n+t:
              {==}
        case Con{+v, rest}:
          match s:
            case 0n:
              h
            case 1n+t:
              match t:
                case 0n:
                  MB.and_eq_true(U32.is_le(w, n0), FM.vals.le(rest, n0), hw, MB.eq_true_of_and_right(U32.is_le(v, n0), FM.vals.le(rest, n0), h))
                case 1n+u:
                  MB.and_eq_true(U32.is_le(v, n0), FM.vals.le(List.set(&2, U32, rest, u, w), n0), MB.eq_true_of_and_left(U32.is_le(v, n0), FM.vals.le(rest, n0), h),
                    set_val(rest, u, w, n0, MB.eq_true_of_and_right(U32.is_le(v, n0), FM.vals.le(rest, n0), h), hw))

def orand(+a: Bool, +b: Bool, +c: Bool, +d: Bool, +h: {(a || (b && c)) == True{} : Bool}) -> {(a || (b && (d || c))) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          or_r(d, c, h)
        case False{}:
          Empty.absurd({(False{} || (False{} && (d || c))) == True{} : Bool}, MB.false_ne_true()(h))

def far_mono1(+l: T.TLink, +t: T.TNode, +eras: List<&2, T.TNode>, +n0: U32, +h: {FM.lk.far(l, eras, n0) == True{} : Bool}) -> {FM.lk.far(l, Con{t, eras}, n0) == True{} : Bool}:
  match l:
    case T.TL{a, b}:
      match a:
        case T.TE{+i, +p}:
          match b:
            case T.TE{+j, +r}:
              orand(U32.is_lt(j, n0), U32.is_eq(r, 0), FM.lsin(j, FM.er.idx(eras, n0)), U32.is_eq(j, FM.er.top(eras, n0)), h)

# an eraser or placeholder pushed: every far end still where it was
def far_mono(ls: List<&2, T.TLink>, +t: T.TNode, +eras: List<&2, T.TNode>, +n0: U32, +h: {FM.lks.far(ls, eras, n0) == True{} : Bool}) -> {FM.lks.far(ls, Con{t, eras}, n0) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, r}:
      MB.and_eq_true(FM.lk.far(l, Con{t, eras}, n0), FM.lks.far(r, Con{t, eras}, n0),
        far_mono1(l, t, eras, n0, MB.eq_true_of_and_left(FM.lk.far(l, eras, n0), FM.lks.far(r, eras, n0), h)),
        far_mono(r, t, eras, n0, MB.eq_true_of_and_right(FM.lk.far(l, eras, n0), FM.lks.far(r, eras, n0), h)))

def push_j(+t: T.TNode, +eras: List<&2, T.TNode>, +ne: U32, +curs: List<&2, RN.FzC>, +ls: List<&2, T.TLink>, +n0: U32, +i: U32, +p: U32,
  +hc: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}, +hj: {FM.lks.far(ls, eras, n0) == True{} : Bool}) ->
  {FM.lks.far(Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, Con{t, eras}, n0) == True{} : Bool}:
  +top = FM.er.top(eras, n0)
  +he = MB.eq_true_of_and_left(U32.is_eq(ne, top), FM.lsteq(FM.ats(curs), FM.er.holes(eras, n0)), hc)
  MB.and_eq_true(FM.lk.far(T.TL{T.TE{i, p}, T.TE{ne, 0}}, Con{t, eras}, n0), FM.lks.far(ls, Con{t, eras}, n0),
    or_r(U32.is_lt(ne, n0), U32.is_eq(0, 0) && FM.lsin(ne, Con{top, FM.er.idx(eras, n0)}),
      MB.and_eq_true(U32.is_eq(0, 0), FM.lsin(ne, Con{top, FM.er.idx(eras, n0)}), {==}, or_l(U32.is_eq(ne, top), FM.lsin(ne, FM.er.idx(eras, n0)), he))),
    far_mono(ls, t, eras, n0, hj))

def lkk_j(+first: Bool, +i: U32, +p: U32, +j: U32, +r: U32, +ls: List<&2, T.TLink>, +eras: List<&2, T.TNode>, +n0: U32, +hjn: {U32.is_lt(j, n0) == True{} : Bool}, +hj: {FM.lks.far(ls, eras, n0) == True{} : Bool}) ->
  {FM.lks.far(F.fz.link.k(first, i, p, j, r, ls), eras, n0) == True{} : Bool}:
  match first:
    case True{}:
      MB.and_eq_true(FM.lk.far(T.TL{T.TE{i, p}, T.TE{j, r}}, eras, n0), FM.lks.far(ls, eras, n0),
        or_l(U32.is_lt(j, n0), U32.is_eq(r, 0) && FM.lsin(j, FM.er.idx(eras, n0)), hjn), hj)
    case False{}:
      hj

# a value not 0 and at most n0, less one, is below n0
def pred_lt(+y: Nat, +z: Nat, +hne: {Nat.is_eq(y, 0n) == False{} : Bool}, +hle: {Nat.is_le(y, z) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(y, 1n), z) == True{} : Bool}:
  match y:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n), z) == True{} : Bool}, MB.true_ne_false()(hne))
    case 1n+c:
      match z:
        case 0n:
          Empty.absurd({Nat.is_lt(Nat.sub(1n+c, 1n), 0n) == True{} : Bool}, MB.false_ne_true()(hle))
        case 1n+w:
          %Equal.sym(Nat, Nat.sub(c, 0n), c, sub0(c)) : {Nat.is_lt(_, 1n+w) == True{} : Bool}
          Equal.trans(Bool, Nat.is_lt(c, 1n+w), Nat.is_le(c, w), True{}, MN.lt_succ_iff(c, w), hle)

def one_le(+y: Nat, +hne: {Nat.is_eq(y, 0n) == False{} : Bool}) -> {Nat.is_le(1n, y) == True{} : Bool}:
  match y:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, MB.true_ne_false()(hne))
    case 1n+c:
      le_one(0n, 1n+c, le0(c))

def vm1.k(+z: Bool, +v: U32, +n0: U32, +hz: {U32.is_eq(v, 0) == z : Bool}, +h: {U32.is_le(v, n0) == True{} : Bool}) -> {(z || U32.is_lt((v - 1 : U32), n0)) == True{} : Bool}:
  match z:
    case True{}:
      {==}
    case False{}:
      +hne = Equal.trans(Bool, Nat.is_eq(U32.to_nat(v), 0n), U32.is_eq(v, 0), False{}, Equal.sym(Bool, U32.is_eq(v, 0), Nat.is_eq(U32.to_nat(v), 0n), MU.u32_is_eq_to_nat(v, 0)), hz)
      +hle = Equal.trans(Bool, Nat.is_le(U32.to_nat(v), U32.to_nat(n0)), U32.is_le(v, n0), True{}, Equal.sym(Bool, U32.is_le(v, n0), Nat.is_le(U32.to_nat(v), U32.to_nat(n0)), MU.u32_is_le_to_nat(v, n0)), h)
      +h1 = Equal.trans(Bool, U32.is_le(1, v), Nat.is_le(1n, U32.to_nat(v)), True{}, MU.u32_is_le_to_nat(1, v), one_le(U32.to_nat(v), hne))
      %Equal.sym(Bool, U32.is_lt((v - 1 : U32), n0), Nat.is_lt(U32.to_nat((v - 1 : U32)), U32.to_nat(n0)), MU.u32_is_lt_to_nat((v - 1 : U32), n0)) : {(False{} || _) == True{} : Bool}
      %Equal.sym(Nat, U32.to_nat((v - 1 : U32)), Nat.sub(U32.to_nat(v), 1n), WL.to_nat_sub_le(v, 1, h1)) : {(False{} || Nat.is_lt(_, U32.to_nat(n0))) == True{} : Bool}
      pred_lt(U32.to_nat(v), U32.to_nat(n0), hne, hle)

def inv.jl(+f: Fl, +n0: U32) -> Bool:
  match f:
    case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
      FM.lks.far(ls, eras, n0)

# --- the table's put (put_keeps, cursor-laws.materializer.template.walk.vals)

def p3.i(+p: P3) -> U32:
  match p:
    case P3{+i, +done, +v}:
      i

def even_hd(+x: U32, +h: {hd(x) == False{} : Bool}) -> {odd(U32.to_nat(x)) == False{} : Bool}:
  match x:
    case U32{w}:
      match w:
        case WCon{+b, +t}:
          match b:
            case True{}:
              Empty.absurd({odd(U32.to_nat(U32{WCon{True{}, t}})) == False{} : Bool}, MB.true_ne_false()(h))
            case False{}:
              %Equal.sym(Nat, Nat.double(Word.to_nat(31n, t)), Nat.mul(2n, Word.to_nat(31n, t)), MN.double_eq_two_mul(Word.to_nat(31n, t))) : {Nat.is_eq(Nat.mod(_, 2n), 1n) == False{} : Bool}
              %Equal.sym(Nat, Nat.mod(Nat.add(0n, Nat.mul(2n, Word.to_nat(31n, t))), 2n), Nat.mod(0n, 2n), MN.add_mul_mod_self_left(0n, 2n, Word.to_nat(31n, t))) : {Nat.is_eq(_, 1n) == False{} : Bool}
              {==}

def put_p_eq(+tm: LAT.Tree<U32>, +p: P3, +b: U32, +v: U32) ->
  {F.hm.put.p(mk3(LAT.fromT(U32, tm), p), b, v) == Array.set(U32, Array.set(U32, LAT.fromT(U32, tm), (p3.i(p) << 1n : U32), b), ((p3.i(p) << 1n : U32) + 1 : U32), v) : Array<U32>}:
  match p:
    case P3{+i, +done, +w}:
      {==}

# the put on a mirrored map: its two words written where the probe stops
def put_eq(+tm: LAT.Tree<U32>, +e: Nat, +hf: {AD.full(U32, LAT.fromT(U32, tm), 1n+e) == True{} : Bool}, +b: U32, +v: U32) ->
  {F.hm.put(LAT.fromT(U32, tm), b, v) == Array.set(U32, Array.set(U32, LAT.fromT(U32, tm), (p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32), b), ((p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32) + 1 : U32), v) : Array<U32>}:
  %Equal.sym(Array<U32> & U32, Array.size(U32, LAT.fromT(U32, tm)), (LAT.fromT(U32, tm), U32.shln(1, 1n+e)), LA.size_pair(U32, LAT.fromT(U32, tm), 1n+e, hf)) :
    {F.hm.put.p(F.hm.at(F.hm.mask(_), b), b, v) == Array.set(U32, Array.set(U32, LAT.fromT(U32, tm), (p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32), b), ((p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32) + 1 : U32), v) : Array<U32>}
  %Equal.sym(F.Hp, F.hm.at.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), b, mask.d(1n+e), mk3(LAT.fromT(U32, tm), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})),
      mk3(LAT.fromT(U32, tm), pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})), go_eq(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) :
    {F.hm.put.p(_, b, v) == Array.set(U32, Array.set(U32, LAT.fromT(U32, tm), (p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32), b), ((p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32) + 1 : U32), v) : Array<U32>}
  put_p_eq(tm, pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0}), b, v)

def put_vals.k(+tm: LAT.Tree<U32>, +e: Nat, +n0: U32, +b: U32, +v: U32, +i: U32, +hf: {AD.full(U32, LAT.fromT(U32, tm), 1n+e) == True{} : Bool}, +hd32: {Nat.is_lt(1n+e, 32n) == True{} : Bool},
  +hv: {FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0) == True{} : Bool}, +hvn: {U32.is_le(v, n0) == True{} : Bool}) ->
  {FM.vals.le(AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, tm), (i << 1n : U32), b), ((i << 1n : U32) + 1 : U32), v)), n0) == True{} : Bool}:
  +hf1 = LA.set_full(U32, LAT.fromT(U32, tm), 1n+e, (i << 1n : U32), b, hf)
  +hev = Equal.trans(Bool, odd(AD.slot((i << 1n : U32), 1n+e)), odd(U32.to_nat((i << 1n : U32))), False{}, odd_slot((i << 1n : U32), 1n+e, le0(e)), even_hd((i << 1n : U32), hd_key(i)))
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, tm), (i << 1n : U32), b), ((i << 1n : U32) + 1 : U32), v)),
      List.set(&2, U32, AD.view(U32, Array.set(U32, LAT.fromT(U32, tm), (i << 1n : U32), b)), AD.slot(((i << 1n : U32) + 1 : U32), 1n+e), v),
      LA.set_view(U32, Array.set(U32, LAT.fromT(U32, tm), (i << 1n : U32), b), 1n+e, ((i << 1n : U32) + 1 : U32), v, hf1, hd32)) :
    {FM.vals.le(_, n0) == True{} : Bool}
  %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, tm), (i << 1n : U32), b)), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot((i << 1n : U32), 1n+e), b),
      LA.set_view(U32, LAT.fromT(U32, tm), 1n+e, (i << 1n : U32), b, hf, hd32)) :
    {FM.vals.le(List.set(&2, U32, _, AD.slot(((i << 1n : U32) + 1 : U32), 1n+e), v), n0) == True{} : Bool}
  set_val(List.set(&2, U32, AD.view(U32, LAT.fromT(U32, tm)), AD.slot((i << 1n : U32), 1n+e), b), AD.slot(((i << 1n : U32) + 1 : U32), 1n+e), v, n0,
    set_even(AD.view(U32, LAT.fromT(U32, tm)), AD.slot((i << 1n : U32), 1n+e), b, n0, hv, hev), hvn)

def put.k(+tm: LAT.Tree<U32>, +b: U32, +v: U32, +e: Nat, +n0: U32, +hf: {AD.full(U32, LAT.fromT(U32, tm), 1n+e) == True{} : Bool}, +hd32: {Nat.is_lt(1n+e, 32n) == True{} : Bool},
  +hv: {FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0) == True{} : Bool}, +hvn: {U32.is_le(v, n0) == True{} : Bool}) ->
  {(AD.full(U32, F.hm.put(LAT.fromT(U32, tm), b, v), 1n+e) && FM.vals.le(AD.view(U32, F.hm.put(LAT.fromT(U32, tm), b, v)), n0)) == True{} : Bool}:
  %Equal.sym(Array<U32>, F.hm.put(LAT.fromT(U32, tm), b, v), Array.set(U32, Array.set(U32, LAT.fromT(U32, tm), (p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32), b), ((p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32) + 1 : U32), v), put_eq(tm, e, hf, b, v)) :
    {(AD.full(U32, _, 1n+e) && FM.vals.le(AD.view(U32, _), n0)) == True{} : Bool}
  MB.and_eq_true(AD.full(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, tm), (p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32), b), ((p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32) + 1 : U32), v), 1n+e), FM.vals.le(AD.view(U32, Array.set(U32, Array.set(U32, LAT.fromT(U32, tm), (p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32), b), ((p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32) + 1 : U32), v)), n0),
    LA.set_full(U32, Array.set(U32, LAT.fromT(U32, tm), (p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32), b), 1n+e, ((p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32) + 1 : U32), v, LA.set_full(U32, LAT.fromT(U32, tm), 1n+e, (p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})) << 1n : U32), b, hf)),
    put_vals.k(tm, e, n0, b, v, p3.i(pr.go(U32.to_nat((mask.d(1n+e) + 1 : U32)), tm, b, mask.d(1n+e), P3{(F.fz.at(b) .&. mask.d(1n+e) : U32), False{}, 0})), hf, hd32, hv, hvn))

def put.m(-a: Array<U32>, +b: U32, +v: U32, +e: Nat, +n0: U32, hf: {AD.full(U32, a, 1n+e) == True{} : Bool}, +hd32: {Nat.is_lt(1n+e, 32n) == True{} : Bool},
  hv: {FM.vals.le(AD.view(U32, a), n0) == True{} : Bool}, +hvn: {U32.is_le(v, n0) == True{} : Bool}, m: LAT.Mirror(U32, a)) ->
  {(AD.full(U32, F.hm.put(a, b, v), 1n+e) && FM.vals.le(AD.view(U32, F.hm.put(a, b, v)), n0)) == True{} : Bool}:
  (+tm, +em) = m
  +hft = LAP.full_t(U32, a, tm, 1n+e, em, hf)
  +hvt = LAB.subst(Array<U32>, x => {FM.vals.le(AD.view(U32, x), n0) == True{} : Bool}, a, LAT.fromT(U32, tm), Equal.sym(Array<U32>, LAT.fromT(U32, tm), a, em), hv)
  %em : {(AD.full(U32, F.hm.put(_, b, v), 1n+e) && FM.vals.le(AD.view(U32, F.hm.put(_, b, v)), n0)) == True{} : Bool}
  put.k(tm, b, v, e, n0, hft, hd32, hvt, hvn)

def Laws.put_keeps(a, b, v, e, n0, hf, hd32, hv, hvn):
  put.m(a, b, v, e, n0, hf, hd32, hv, hvn, LAT.mirror(U32, a))

# --- the write phase's ladder, written once
#
# A template over the invariant I (on the record's data fields) and C,
# what is fixed for one node (tc the node's tree, ta, tm, dm, its base b
# and index i, n0), with five leaves: a static's eraser pushed (era), the
# root set (root), a cursor's placeholder pushed (hole), a link between
# nodes read back (link), a node added (node). Each leaf gets the raw
# facts of its branch; each law's I is the conjunction of what it rests
# on, its leaves calling those of its parts. I's argument is of the type
# X, moved from port p to p + 1 by nx (the identity, for an invariant
# that no port moves). The node's list (ems) is each law's own, as the
# links' count down.

def not_of(+b: Bool, +h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

def nt_of(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MB.false_ne_true()(h))
    case False{}:
      {==}

# the record a node read adds to
def na(+r: NR, +f: Fl) -> Fl:
  match r:
    case NR{+t, +n}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          Fl{Con{n, nodes}, eras, ne, ls, root, curs}

def st.f(+s: ST) -> Fl:
  match s:
    case ST{+t, +f}:
      f

def st.t(+s: ST) -> LAT.Tree<U32>:
  match s:
    case ST{+t, +f}:
      t

# the ports a node's step has done, matched as pes matches its arity
def pd(a: Nat) -> U32:
  match a:
    case 0n:
      0
    case 1n+j:
      match j:
        case 0n:
          1
        case 1n+x:
          match x:
            case 0n:
              2
            case 1n+y:
              3

# the identities, for an invariant no port moves
def id32(+x: U32, +p: U32) -> U32:
  x

def idnat(+x: Nat, +p: U32) -> Nat:
  x

def pv_T(~X: Data,
  ~nx: @+x:X -> @+p:U32 -> X,
  ~I: @+f:Fl -> @+n0:X -> Bool,
  ~C: @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+b:U32 -> @+i:U32 -> @+n0:X -> Bool,
  ~l_hole: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+q:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_link: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+q:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> @+hst:{P.is_static(q) == False{} : Bool} -> @+hu:{U32.is_eq(mv(tm, dm, P.base(q)), 0) == False{} : Bool} -> {I(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  +unf: Bool, +f: Fl, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: X, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +hu: {U32.is_eq(mv(tm, dm, P.base(q)), 0) == unf : Bool}, +hst: {P.is_static(q) == False{} : Bool}, +h: {I(f, nx(n0, p)) == True{} : Bool}, +hC: {C(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) ->
  {I(pe.v(unf, f, k, b, i, p, q, mv(tm, dm, P.base(q))), nx(n0, (p + 1 : U32))) == True{} : Bool}:
  match unf:
    case True{}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          l_hole(nodes, eras, ne, ls, root, curs, k, b, i, p, q, n0, tc, ta, tm, dm, h, hC, hp)
    case False{}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          l_link(nodes, eras, ne, ls, root, curs, k, b, i, p, q, n0, tc, ta, tm, dm, h, hC, hp, hst, hu)

def pk_T(~X: Data,
  ~nx: @+x:X -> @+p:U32 -> X,
  ~I: @+f:Fl -> @+n0:X -> Bool,
  ~C: @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+b:U32 -> @+i:U32 -> @+n0:X -> Bool,
  ~l_era: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_root: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, eras, ne, ls, T.TE{i, p}, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_hole: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+q:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_link: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+q:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> @+hst:{P.is_static(q) == False{} : Bool} -> @+hu:{U32.is_eq(mv(tm, dm, P.base(q)), 0) == False{} : Bool} -> {I(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  +st: Bool, +rt: Bool, +f: Fl, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: X, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +hns: {(st || Bool.not(P.is_static(q))) == True{} : Bool}, +h: {I(f, nx(n0, p)) == True{} : Bool}, +hC: {C(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) ->
  {I(pe.k(st, rt, f, tm, dm, k, b, i, p, q), nx(n0, (p + 1 : U32))) == True{} : Bool}:
  match st:
    case True{}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          l_era(nodes, eras, ne, ls, root, curs, k, b, i, p, n0, tc, ta, tm, dm, h, hC, hp)
    case False{}:
      match rt:
        case True{}:
          match f:
            case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
              l_root(nodes, eras, ne, ls, root, curs, k, b, i, p, n0, tc, ta, tm, dm, h, hC, hp)
        case False{}:
          pv_T(~X, ~nx, ~I, ~C, ~l_hole, ~l_link, U32.is_eq(mv(tm, dm, P.base(q)), 0), f, k, b, i, p, q, n0, tc, ta, tm, dm, {==}, nt_of(P.is_static(q), hns), h, hC, hp)

def ps_T(~X: Data,
  ~nx: @+x:X -> @+p:U32 -> X,
  ~I: @+f:Fl -> @+n0:X -> Bool,
  ~C: @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+b:U32 -> @+i:U32 -> @+n0:X -> Bool,
  ~l_era: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_root: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, eras, ne, ls, T.TE{i, p}, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_hole: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+q:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_link: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+q:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> @+hst:{P.is_static(q) == False{} : Bool} -> @+hu:{U32.is_eq(mv(tm, dm, P.base(q)), 0) == False{} : Bool} -> {I(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  +st: Bool, +f: Fl, +t0: LAT.Tree<U32>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: X, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +hst: {P.is_static(q) == st : Bool}, +h: {I(f, nx(n0, p)) == True{} : Bool}, +hC: {C(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) ->
  {I(pe.s(st, f, t0, tm, dm, k, b, i, p, q), nx(n0, (p + 1 : U32))) == True{} : Bool}:
  match st:
    case True{}:
      pk_T(~X, ~nx, ~I, ~C, ~l_era, ~l_root, ~l_hole, ~l_link, True{}, False{}, f, k, b, i, p, q, n0, tc, ta, tm, dm, {==}, h, hC, hp)
    case False{}:
      pk_T(~X, ~nx, ~I, ~C, ~l_era, ~l_root, ~l_hole, ~l_link, F.fz.is_era(hw(t0, P.base(q))), U32.is_eq(P.base(q), P.iface()), f, k, b, i, p, q, n0, tc, ta, tm, dm,
        or_r(F.fz.is_era(hw(t0, P.base(q))), Bool.not(P.is_static(q)), not_of(P.is_static(q), hst)), h, hC, hp)

def pe_T(~X: Data,
  ~nx: @+x:X -> @+p:U32 -> X,
  ~I: @+f:Fl -> @+n0:X -> Bool,
  ~C: @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+b:U32 -> @+i:U32 -> @+n0:X -> Bool,
  ~l_era: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_root: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, eras, ne, ls, T.TE{i, p}, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_hole: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+q:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_link: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+q:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> @+hst:{P.is_static(q) == False{} : Bool} -> @+hu:{U32.is_eq(mv(tm, dm, P.base(q)), 0) == False{} : Bool} -> {I(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  +f: Fl, +t0: LAT.Tree<U32>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: X, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {I(f, nx(n0, p)) == True{} : Bool}, +hC: {C(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) ->
  {I(pe(f, t0, tm, dm, k, b, i, p), nx(n0, (p + 1 : U32))) == True{} : Bool}:
  ps_T(~X, ~nx, ~I, ~C, ~l_era, ~l_root, ~l_hole, ~l_link, P.is_static(hw(t0, (b + 1 + p : U32))), f, t0, k, b, i, p, hw(t0, (b + 1 + p : U32)), n0, tc, ta, tm, dm, {==}, h, hC, hp)

def pes_T(~X: Data,
  ~nx: @+x:X -> @+p:U32 -> X,
  ~I: @+f:Fl -> @+n0:X -> Bool,
  ~C: @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+b:U32 -> @+i:U32 -> @+n0:X -> Bool,
  ~l_era: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_root: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, eras, ne, ls, T.TE{i, p}, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_hole: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+q:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_link: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+q:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> @+hst:{P.is_static(q) == False{} : Bool} -> @+hu:{U32.is_eq(mv(tm, dm, P.base(q)), 0) == False{} : Bool} -> {I(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  +f: Fl, +t0: LAT.Tree<U32>, +k: R.NodeKind, +b: U32, +i: U32, a: Nat, +n0: X, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {I(f, nx(n0, 0)) == True{} : Bool}, +hC: {C(tc, ta, tm, dm, b, i, n0) == True{} : Bool}) ->
  {I(pes(f, t0, tm, dm, k, b, i, a), nx(n0, pd(a))) == True{} : Bool}:
  match a:
    case 0n:
      h
    case 1n+j:
      match j:
        case 0n:
          pe_T(~X, ~nx, ~I, ~C, ~l_era, ~l_root, ~l_hole, ~l_link, f, t0, k, b, i, 0, n0, tc, ta, tm, dm, h, hC, {==})
        case 1n+x:
          match x:
            case 0n:
              pe_T(~X, ~nx, ~I, ~C, ~l_era, ~l_root, ~l_hole, ~l_link, pe(f, t0, tm, dm, k, b, i, 0), t0, k, b, i, 1, n0, tc, ta, tm, dm, pe_T(~X, ~nx, ~I, ~C, ~l_era, ~l_root, ~l_hole, ~l_link, f, t0, k, b, i, 0, n0, tc, ta, tm, dm, h, hC, {==}), hC, {==})
            case 1n+y:
              pe_T(~X, ~nx, ~I, ~C, ~l_era, ~l_root, ~l_hole, ~l_link, pe(pe(f, t0, tm, dm, k, b, i, 0), t0, tm, dm, k, b, i, 1), t0, k, b, i, 2, n0, tc, ta, tm, dm, pe_T(~X, ~nx, ~I, ~C, ~l_era, ~l_root, ~l_hole, ~l_link, pe(f, t0, tm, dm, k, b, i, 0), t0, k, b, i, 1, n0, tc, ta, tm, dm, pe_T(~X, ~nx, ~I, ~C, ~l_era, ~l_root, ~l_hole, ~l_link, f, t0, k, b, i, 0, n0, tc, ta, tm, dm, h, hC, {==}), hC, {==}), hC, {==})

def emt_T(~X: Data,
  ~nx: @+x:X -> @+p:U32 -> X,
  ~I: @+f:Fl -> @+n0:X -> Bool,
  ~C: @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+b:U32 -> @+i:U32 -> @+n0:X -> Bool,
  ~l_era: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_root: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, eras, ne, ls, T.TE{i, p}, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_hole: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+q:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_link: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+q:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> @+hst:{P.is_static(q) == False{} : Bool} -> @+hu:{U32.is_eq(mv(tm, dm, P.base(q)), 0) == False{} : Bool} -> {I(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  +r: NR, +f: Fl, +k: R.NodeKind, +b: U32, +i: U32, +n0: X, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +hN: {I(na(r, f), nx(n0, 0)) == True{} : Bool}, +hC: {C(tc, ta, tm, dm, b, i, n0) == True{} : Bool}) ->
  {I(st.f(em.t(r, f, tm, dm, k, b, i)), nx(n0, pd(R.arity(k)))) == True{} : Bool}:
  match r:
    case NR{+t, +n}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          pes_T(~X, ~nx, ~I, ~C, ~l_era, ~l_root, ~l_hole, ~l_link, Fl{Con{n, nodes}, eras, ne, ls, root, curs}, t, k, b, i, R.arity(k), n0, tc, ta, tm, dm, hN, hC)

# a node and its ports, any invariant its five leaves keep
def em_T(~X: Data,
  ~nx: @+x:X -> @+p:U32 -> X,
  ~I: @+f:Fl -> @+n0:X -> Bool,
  ~C: @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+b:U32 -> @+i:U32 -> @+n0:X -> Bool,
  ~l_era: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_root: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, eras, ne, ls, T.TE{i, p}, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_hole: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+q:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> {I(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_link: @+nodes:List<&2, T.TNode> -> @+eras:List<&2, T.TNode> -> @+ne:U32 -> @+ls:List<&2, T.TLink> -> @+root:T.TEnd -> @+curs:List<&2, RN.FzC> -> @+k:R.NodeKind -> @+b:U32 -> @+i:U32 -> @+p:U32 -> @+q:U32 -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+h:{I(Fl{nodes, eras, ne, ls, root, curs}, nx(n0, p)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> @+hp:{SM.port3(p) == True{} : Bool} -> @+hst:{P.is_static(q) == False{} : Bool} -> @+hu:{U32.is_eq(mv(tm, dm, P.base(q)), 0) == False{} : Bool} -> {I(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, nx(n0, (p + 1 : U32))) == True{} : Bool},
  ~l_node: @+f:Fl -> @+n0:X -> @+tc:LAT.Tree<U32> -> @+ta:LAT.Tree<V.Val> -> @+tm:LAT.Tree<U32> -> @+dm:Nat -> @+b:U32 -> @+i:U32 -> @+h:{I(f, nx(n0, 0)) == True{} : Bool} -> @+hC:{C(tc, ta, tm, dm, b, i, n0) == True{} : Bool} -> {I(na(nd(N.kof(P.rk(hw(tc, b))), tc, ta, hw(tc, b), b), f), nx(n0, 0)) == True{} : Bool},
  +s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +n0: X,
  +h: {I(st.f(s), nx(n0, 0)) == True{} : Bool}, +hC: {C(st.t(s), ta, tm, dm, b, i, n0) == True{} : Bool}) ->
  {I(st.f(em(s, ta, tm, dm, b, i)), nx(n0, pd(R.arity(N.kof(P.rk(hw(st.t(s), b))))))) == True{} : Bool}:
  match s:
    case ST{+t, +f}:
      emt_T(~X, ~nx, ~I, ~C, ~l_era, ~l_root, ~l_hole, ~l_link, nd(N.kof(P.rk(hw(t, b))), t, ta, hw(t, b), b), f, N.kof(P.rk(hw(t, b))), b, i, n0, t, ta, tm, dm,
        l_node(f, n0, t, ta, tm, dm, b, i, h, hC), hC)

# --- the counts' instance

def cnt_na(+r: NR, +f: Fl, +n0: U32, +h: {inv.fl(f, n0) == True{} : Bool}) -> {inv.fl(na(r, f), n0) == True{} : Bool}:
  match r:
    case NR{+t, +n}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          h

def c.true(+tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +n0: U32) -> Bool:
  True{}

def c_era(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.true(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {inv.fl(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, n0) == True{} : Bool}:
  era_inv(R.port_pol(k, U32.to_nat(p)), eras, ne, curs, n0, h)

def c_root(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.true(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {inv.fl(Fl{nodes, eras, ne, ls, T.TE{i, p}, curs}, n0) == True{} : Bool}:
  h

def c_hole(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.true(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {inv.fl(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, n0) == True{} : Bool}:
  hole_inv(R.port_pol(k, U32.to_nat(p)), eras, ne, curs, n0, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q, h)

def c_link(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.true(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool},
  +hst: {P.is_static(q) == False{} : Bool}, +hu: {U32.is_eq(mv(tm, dm, P.base(q)), 0) == False{} : Bool}) -> {inv.fl(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, n0) == True{} : Bool}:
  h

def c_node(+f: Fl, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +h: {inv.fl(f, n0) == True{} : Bool}, +hC: {c.true(tc, ta, tm, dm, b, i, n0) == True{} : Bool}) ->
  {inv.fl(na(nd(N.kof(P.rk(hw(tc, b))), tc, ta, hw(tc, b), b), f), n0) == True{} : Bool}:
  cnt_na(nd(N.kof(P.rk(hw(tc, b))), tc, ta, hw(tc, b), b), f, n0, h)

def em_c(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +n0: U32, +h: {inv.fl(st.f(s), n0) == True{} : Bool}) ->
  {inv.fl(st.f(em(s, ta, tm, dm, b, i)), n0) == True{} : Bool}:
  em_T(~U32, ~id32, ~inv.fl, ~c.true, ~c_era, ~c_root, ~c_hole, ~c_link, ~c_node, s, ta, tm, dm, b, i, n0, h, {==})

def ems_c(seen: List<&2, U32>, +s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +i: U32, +n0: U32, +h: {inv.fl(st.f(s), n0) == True{} : Bool}) ->
  {inv.fl(st.f(ems(seen, s, ta, tm, dm, i)), n0) == True{} : Bool}:
  match seen:
    case Nil{}:
      h
    case Con{+b, rest}:
      ems_c(rest, em(s, ta, tm, dm, b, i), ta, tm, dm, (i - 1 : U32), n0, em_c(s, ta, tm, dm, b, i, n0, h))

def inv_mkS_f(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +n0: U32) -> {FM.inv(mkS(ta, LAT.fromT(U32, tm), s), n0) == inv.fl(st.f(s), n0) : Bool}:
  match s:
    case ST{+t, +f}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          {==}

def ec.k(+seen: List<&2, U32>, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +n0: U32, +i: U32,
  +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +hz: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}) ->
  {FM.inv(F.fz.emits(seen, F.FzE{hp(t0, ta), LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}:
  %Equal.sym(F.FzE, F.fz.emits(seen, mkS(ta, LAT.fromT(U32, tm), ST{t0, Fl{nodes, eras, ne, ls, root, curs}}), i), mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), emsb(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, hf, i)) :
    {FM.inv(_, n0) == True{} : Bool}
  %Equal.sym(Bool, FM.inv(mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), n0), inv.fl(st.f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), n0), inv_mkS_f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i), ta, tm, n0)) :
    {_ == True{} : Bool}
  ems_c(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i, n0, hz)

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

# --- the links' instance: the counts and the links together

def ik(+f: Fl, +n0: U32) -> Bool:
  inv.fl(f, n0) && inv.kl(f, n0)

def c.lt(+tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +n0: U32) -> Bool:
  U32.is_lt(i, n0)

def k_era(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {ik(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.lt(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {ik(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, n0) == True{} : Bool}:
  MB.and_eq_true(inv.fl(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, n0), inv.kl(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, n0), era_inv(R.port_pol(k, U32.to_nat(p)), eras, ne, curs, n0, MB.eq_true_of_and_left(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.kl(Fl{nodes, eras, ne, ls, root, curs}, n0), h)),
    push_k(F.fz.era(R.port_pol(k, U32.to_nat(p))), eras, ne, curs, ls, n0, i, p, MB.eq_true_of_and_left(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.kl(Fl{nodes, eras, ne, ls, root, curs}, n0), h), MB.eq_true_of_and_right(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.kl(Fl{nodes, eras, ne, ls, root, curs}, n0), h), hC, hp))

def k_root(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {ik(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.lt(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {ik(Fl{nodes, eras, ne, ls, T.TE{i, p}, curs}, n0) == True{} : Bool}:
  h

def k_hole(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {ik(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.lt(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {ik(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, n0) == True{} : Bool}:
  MB.and_eq_true(inv.fl(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, n0), inv.kl(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, n0), hole_inv(R.port_pol(k, U32.to_nat(p)), eras, ne, curs, n0, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q, MB.eq_true_of_and_left(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.kl(Fl{nodes, eras, ne, ls, root, curs}, n0), h)),
    push_k(F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras, ne, curs, ls, n0, i, p, MB.eq_true_of_and_left(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.kl(Fl{nodes, eras, ne, ls, root, curs}, n0), h), MB.eq_true_of_and_right(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.kl(Fl{nodes, eras, ne, ls, root, curs}, n0), h), hC, hp))

def k_link(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {ik(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.lt(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool},
  +hst: {P.is_static(q) == False{} : Bool}, +hu: {U32.is_eq(mv(tm, dm, P.base(q)), 0) == False{} : Bool}) -> {ik(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, n0) == True{} : Bool}:
  MB.and_eq_true(inv.fl(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, n0), inv.kl(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, n0), MB.eq_true_of_and_left(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.kl(Fl{nodes, eras, ne, ls, root, curs}, n0), h),
    lkk_k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls, eras, n0, hC, hp, port3_of(q, hst), MB.eq_true_of_and_right(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.kl(Fl{nodes, eras, ne, ls, root, curs}, n0), h)))

def k_na(+r: NR, +f: Fl, +n0: U32, +h: {ik(f, n0) == True{} : Bool}) -> {ik(na(r, f), n0) == True{} : Bool}:
  match r:
    case NR{+t, +n}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          h

def k_node(+f: Fl, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +h: {ik(f, n0) == True{} : Bool}, +hC: {c.lt(tc, ta, tm, dm, b, i, n0) == True{} : Bool}) ->
  {ik(na(nd(N.kof(P.rk(hw(tc, b))), tc, ta, hw(tc, b), b), f), n0) == True{} : Bool}:
  k_na(nd(N.kof(P.rk(hw(tc, b))), tc, ta, hw(tc, b), b), f, n0, h)

def em_l(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +n0: U32, +h: {ik(st.f(s), n0) == True{} : Bool}, +hi: {U32.is_lt(i, n0) == True{} : Bool}) ->
  {ik(st.f(em(s, ta, tm, dm, b, i)), n0) == True{} : Bool}:
  em_T(~U32, ~id32, ~ik, ~c.lt, ~k_era, ~k_root, ~k_hole, ~k_link, ~k_node, s, ta, tm, dm, b, i, n0, h, hi)

def ems_l(seen: List<&2, U32>, +s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +i: U32, +n0: U32,
  +h: {ik(st.f(s), n0) == True{} : Bool}, +hi: {U32.is_lt(i, n0) == True{} : Bool}, +hl: {Nat.is_le(List.length(&2, U32, seen), 1n+U32.to_nat(i)) == True{} : Bool}) ->
  {ik(st.f(ems(seen, s, ta, tm, dm, i)), n0) == True{} : Bool}:
  match seen:
    case Nil{}:
      h
    case Con{+b, rest}:
      match rest:
        case Nil{}:
          em_l(s, ta, tm, dm, b, i, n0, h, hi)
        case Con{+b2, +r2}:
          ems_l(Con{b2, r2}, em(s, ta, tm, dm, b, i), ta, tm, dm, (i - 1 : U32), n0, em_l(s, ta, tm, dm, b, i, n0, h, hi),
            cd_i(i, n0, List.length(&2, U32, r2), hl, hi), cd_l(i, List.length(&2, U32, r2), hl))

def inv_l_f(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +n0: U32) -> {FM.inv.l(mkS(ta, LAT.fromT(U32, tm), s), n0) == inv.kl(st.f(s), n0) : Bool}:
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
  %Equal.sym(Bool, FM.inv.l(mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), n0), inv.kl(st.f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), n0), inv_l_f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i), ta, tm, n0)) :
    {_ == True{} : Bool}
  MB.eq_true_of_and_right(inv.fl(st.f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), n0), inv.kl(st.f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), n0),
    ems_l(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i, n0, MB.and_eq_true(FM.inv.f(eras, ne, curs, n0), FM.inv.k(ls, eras, n0), hz, hk), hi, hl))

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

# --- the far ends' instance: the counts and the far ends together

def ij(+f: Fl, +n0: U32) -> Bool:
  inv.fl(f, n0) && inv.jl(f, n0)

# the map's facts, the same for every node
def c.map(+tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +n0: U32) -> Bool:
  AD.full(U32, LAT.fromT(U32, tm), dm) && (Nat.is_lt(dm, 32n) && (Nat.is_le(1n, dm) && FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0)))

def j_era(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {ij(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.map(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {ij(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, n0) == True{} : Bool}:
  MB.and_eq_true(inv.fl(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, n0), inv.jl(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, n0), era_inv(R.port_pol(k, U32.to_nat(p)), eras, ne, curs, n0, MB.eq_true_of_and_left(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.jl(Fl{nodes, eras, ne, ls, root, curs}, n0), h)),
    push_j(F.fz.era(R.port_pol(k, U32.to_nat(p))), eras, ne, curs, ls, n0, i, p, MB.eq_true_of_and_left(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.jl(Fl{nodes, eras, ne, ls, root, curs}, n0), h), MB.eq_true_of_and_right(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.jl(Fl{nodes, eras, ne, ls, root, curs}, n0), h)))

def j_root(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {ij(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.map(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {ij(Fl{nodes, eras, ne, ls, T.TE{i, p}, curs}, n0) == True{} : Bool}:
  h

def j_hole(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {ij(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.map(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {ij(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, n0) == True{} : Bool}:
  MB.and_eq_true(inv.fl(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, n0), inv.jl(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, n0), hole_inv(R.port_pol(k, U32.to_nat(p)), eras, ne, curs, n0, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q, MB.eq_true_of_and_left(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.jl(Fl{nodes, eras, ne, ls, root, curs}, n0), h)),
    push_j(F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras, ne, curs, ls, n0, i, p, MB.eq_true_of_and_left(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.jl(Fl{nodes, eras, ne, ls, root, curs}, n0), h), MB.eq_true_of_and_right(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.jl(Fl{nodes, eras, ne, ls, root, curs}, n0), h)))

def j_link(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {ij(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.map(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool},
  +hst: {P.is_static(q) == False{} : Bool}, +hu: {U32.is_eq(mv(tm, dm, P.base(q)), 0) == False{} : Bool}) -> {ij(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, n0) == True{} : Bool}:
  MB.and_eq_true(inv.fl(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, n0), inv.jl(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, n0), MB.eq_true_of_and_left(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.jl(Fl{nodes, eras, ne, ls, root, curs}, n0), h),
    lkk_j(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls, eras, n0,
      vm1.k(False{}, mv(tm, dm, P.base(q)), n0, hu, mv_le(tm, dm, MB.eq_true_of_and_left(Nat.is_le(1n, dm), FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0), MB.eq_true_of_and_right(Nat.is_lt(dm, 32n), Nat.is_le(1n, dm) && FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0), MB.eq_true_of_and_right(AD.full(U32, LAT.fromT(U32, tm), dm), Nat.is_lt(dm, 32n) && (Nat.is_le(1n, dm) && FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0)), hC))), P.base(q), n0, MB.eq_true_of_and_left(AD.full(U32, LAT.fromT(U32, tm), dm), Nat.is_lt(dm, 32n) && (Nat.is_le(1n, dm) && FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0)), hC), MB.eq_true_of_and_left(Nat.is_lt(dm, 32n), Nat.is_le(1n, dm) && FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0), MB.eq_true_of_and_right(AD.full(U32, LAT.fromT(U32, tm), dm), Nat.is_lt(dm, 32n) && (Nat.is_le(1n, dm) && FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0)), hC)), MB.eq_true_of_and_right(Nat.is_le(1n, dm), FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0), MB.eq_true_of_and_right(Nat.is_lt(dm, 32n), Nat.is_le(1n, dm) && FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0), MB.eq_true_of_and_right(AD.full(U32, LAT.fromT(U32, tm), dm), Nat.is_lt(dm, 32n) && (Nat.is_le(1n, dm) && FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0)), hC))))), MB.eq_true_of_and_right(inv.fl(Fl{nodes, eras, ne, ls, root, curs}, n0), inv.jl(Fl{nodes, eras, ne, ls, root, curs}, n0), h)))

def j_na(+r: NR, +f: Fl, +n0: U32, +h: {ij(f, n0) == True{} : Bool}) -> {ij(na(r, f), n0) == True{} : Bool}:
  match r:
    case NR{+t, +n}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          h

def j_node(+f: Fl, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +h: {ij(f, n0) == True{} : Bool}, +hC: {c.map(tc, ta, tm, dm, b, i, n0) == True{} : Bool}) ->
  {ij(na(nd(N.kof(P.rk(hw(tc, b))), tc, ta, hw(tc, b), b), f), n0) == True{} : Bool}:
  j_na(nd(N.kof(P.rk(hw(tc, b))), tc, ta, hw(tc, b), b), f, n0, h)

def em_f(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +n0: U32, +h: {ij(st.f(s), n0) == True{} : Bool}, +hm: {AD.full(U32, LAT.fromT(U32, tm), dm) && (Nat.is_lt(dm, 32n) && (Nat.is_le(1n, dm) && FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0))) == True{} : Bool}) ->
  {ij(st.f(em(s, ta, tm, dm, b, i)), n0) == True{} : Bool}:
  em_T(~U32, ~id32, ~ij, ~c.map, ~j_era, ~j_root, ~j_hole, ~j_link, ~j_node, s, ta, tm, dm, b, i, n0, h, hm)

def ems_f(seen: List<&2, U32>, +s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +i: U32, +n0: U32, +h: {ij(st.f(s), n0) == True{} : Bool}, +hm: {AD.full(U32, LAT.fromT(U32, tm), dm) && (Nat.is_lt(dm, 32n) && (Nat.is_le(1n, dm) && FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0))) == True{} : Bool}) ->
  {ij(st.f(ems(seen, s, ta, tm, dm, i)), n0) == True{} : Bool}:
  match seen:
    case Nil{}:
      h
    case Con{+b, rest}:
      ems_f(rest, em(s, ta, tm, dm, b, i), ta, tm, dm, (i - 1 : U32), n0, em_f(s, ta, tm, dm, b, i, n0, h, hm), hm)

def inv_j_f(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +n0: U32) -> {FM.inv.j(mkS(ta, LAT.fromT(U32, tm), s), n0) == inv.jl(st.f(s), n0) : Bool}:
  match s:
    case ST{+t, +f}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          {==}

def ej.k(+seen: List<&2, U32>, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +e: Nat, +n0: U32, +i: U32,
  +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +hz: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}, +hj: {FM.lks.far(ls, eras, n0) == True{} : Bool}, +hf: {AD.full(U32, LAT.fromT(U32, tm), 1n+e) == True{} : Bool}, +hd32: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hv: {FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0) == True{} : Bool}) ->
  {FM.inv.j(F.fz.emits(seen, F.FzE{hp(t0, ta), LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}:
  %Equal.sym(F.FzE, F.fz.emits(seen, mkS(ta, LAT.fromT(U32, tm), ST{t0, Fl{nodes, eras, ne, ls, root, curs}}), i), mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, 1n+e, i)), emsb(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, 1n+e, hf, i)) :
    {FM.inv.j(_, n0) == True{} : Bool}
  %Equal.sym(Bool, FM.inv.j(mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, 1n+e, i)), n0), inv.jl(st.f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, 1n+e, i)), n0), inv_j_f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, 1n+e, i), ta, tm, n0)) :
    {_ == True{} : Bool}
  MB.eq_true_of_and_right(inv.fl(st.f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, 1n+e, i)), n0), inv.jl(st.f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, 1n+e, i)), n0),
    ems_f(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, 1n+e, i, n0, MB.and_eq_true(FM.inv.f(eras, ne, curs, n0), FM.lks.far(ls, eras, n0), hz, hj),
      MB.and_eq_true(AD.full(U32, LAT.fromT(U32, tm), 1n+e), Nat.is_lt(1n+e, 32n) && (Nat.is_le(1n, 1n+e) && FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0)), hf,
        MB.and_eq_true(Nat.is_lt(1n+e, 32n), Nat.is_le(1n, 1n+e) && FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0), hd32,
          MB.and_eq_true(Nat.is_le(1n, 1n+e), FM.vals.le(AD.view(U32, LAT.fromT(U32, tm)), n0), le0(e), hv)))))

def ej.m(+seen: List<&2, U32>, -A: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +e: Nat, hf: {AD.full(U32, map, 1n+e) == True{} : Bool}, +hd32: {Nat.is_lt(1n+e, 32n) == True{} : Bool},
  +n0: U32, hv: {FM.vals.le(AD.view(U32, map), n0) == True{} : Bool}, +i: U32,
  +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +hz: {FM.inv.f(eras, ne, curs, n0) == True{} : Bool}, +hj: {FM.lks.far(ls, eras, n0) == True{} : Bool},
  m0: LAT.Mirror(U32, A), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {FM.inv.j(F.fz.emits(seen, F.FzE{P.H{KM.MG{A}, a}, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}:
  (+t0, +e0) = m0
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, map, tm, 1n+e, em, hf)
  +hvt = LAB.subst(Array<U32>, x => {FM.vals.le(AD.view(U32, x), n0) == True{} : Bool}, map, LAT.fromT(U32, tm), Equal.sym(Array<U32>, LAT.fromT(U32, tm), map, em), hv)
  %e0 : {FM.inv.j(F.fz.emits(seen, F.FzE{P.H{KM.MG{_}, a}, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}
  %ea : {FM.inv.j(F.fz.emits(seen, F.FzE{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}
  %em : {FM.inv.j(F.fz.emits(seen, F.FzE{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, _, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}
  ej.k(seen, t0, ta, tm, e, n0, i, nodes, eras, ne, ls, root, curs, hz, hj, hft, hd32, hvt)

def Laws.emits_far(seen, h, map, e, hf, hd32, n0, hv, i, nodes, eras, ne, ls, root, curs, hz, hj):
  match h:
    case P.H{w, a}:
      match w:
        case KM.MG{A}:
          ej.m(seen, A, a, map, e, hf, hd32, n0, hv, i, nodes, eras, ne, ls, root, curs, hz, hj, LAT.mirror(U32, A), LAT.mirror(V.Val, a), LAT.mirror(U32, map))

# --- the root's and the eras' instance (emits_root)

def ir(+f: Fl, +n0: U32) -> Bool:
  match f:
    case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
      FM.rt.ok(root, n0) && FM.eras.ok(eras)

# a static's eraser is an eraser, no placeholder
def era_ok(+pol: R.Pol, +eras: List<&2, T.TNode>, +h: {FM.eras.ok(eras) == True{} : Bool}) -> {FM.eras.ok(Con{F.fz.era(pol), eras}) == True{} : Bool}:
  match pol:
    case R.Neg{}:
      h
    case R.Pos{}:
      h

def r_era(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {ir(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.lt(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {ir(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, n0) == True{} : Bool}:
  MB.and_eq_true(FM.rt.ok(root, n0), FM.eras.ok(Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}), MB.eq_true_of_and_left(FM.rt.ok(root, n0), FM.eras.ok(eras), h), era_ok(R.port_pol(k, U32.to_nat(p)), eras, MB.eq_true_of_and_right(FM.rt.ok(root, n0), FM.eras.ok(eras), h)))

def r_root(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {ir(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.lt(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {ir(Fl{nodes, eras, ne, ls, T.TE{i, p}, curs}, n0) == True{} : Bool}:
  MB.and_eq_true(FM.rt.ok(T.TE{i, p}, n0), FM.eras.ok(eras), MB.and_eq_true(U32.is_lt(i, n0), SM.port3(p), hC, hp), MB.eq_true_of_and_right(FM.rt.ok(root, n0), FM.eras.ok(eras), h))

def r_hole(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {ir(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.lt(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {ir(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, n0) == True{} : Bool}:
  h

def r_link(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {ir(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.lt(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool},
  +hst: {P.is_static(q) == False{} : Bool}, +hu: {U32.is_eq(mv(tm, dm, P.base(q)), 0) == False{} : Bool}) -> {ir(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, n0) == True{} : Bool}:
  h

def r_na(+r: NR, +f: Fl, +n0: U32, +h: {ir(f, n0) == True{} : Bool}) -> {ir(na(r, f), n0) == True{} : Bool}:
  match r:
    case NR{+t, +n}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          h

def r_node(+f: Fl, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +h: {ir(f, n0) == True{} : Bool}, +hC: {c.lt(tc, ta, tm, dm, b, i, n0) == True{} : Bool}) ->
  {ir(na(nd(N.kof(P.rk(hw(tc, b))), tc, ta, hw(tc, b), b), f), n0) == True{} : Bool}:
  r_na(nd(N.kof(P.rk(hw(tc, b))), tc, ta, hw(tc, b), b), f, n0, h)

def em_r(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +n0: U32, +h: {ir(st.f(s), n0) == True{} : Bool}, +hi: {U32.is_lt(i, n0) == True{} : Bool}) ->
  {ir(st.f(em(s, ta, tm, dm, b, i)), n0) == True{} : Bool}:
  em_T(~U32, ~id32, ~ir, ~c.lt, ~r_era, ~r_root, ~r_hole, ~r_link, ~r_node, s, ta, tm, dm, b, i, n0, h, hi)

def ems_r(seen: List<&2, U32>, +s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +i: U32, +n0: U32,
  +h: {ir(st.f(s), n0) == True{} : Bool}, +hi: {U32.is_lt(i, n0) == True{} : Bool}, +hl: {Nat.is_le(List.length(&2, U32, seen), 1n+U32.to_nat(i)) == True{} : Bool}) ->
  {ir(st.f(ems(seen, s, ta, tm, dm, i)), n0) == True{} : Bool}:
  match seen:
    case Nil{}:
      h
    case Con{+b, rest}:
      match rest:
        case Nil{}:
          em_r(s, ta, tm, dm, b, i, n0, h, hi)
        case Con{+b2, +r2}:
          ems_r(Con{b2, r2}, em(s, ta, tm, dm, b, i), ta, tm, dm, (i - 1 : U32), n0, em_r(s, ta, tm, dm, b, i, n0, h, hi),
            cd_i(i, n0, List.length(&2, U32, r2), hl, hi), cd_l(i, List.length(&2, U32, r2), hl))

def inv_r_f(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +n0: U32) -> {FM.inv.r(mkS(ta, LAT.fromT(U32, tm), s), n0) == ir(st.f(s), n0) : Bool}:
  match s:
    case ST{+t, +f}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          {==}

def er.k(+seen: List<&2, U32>, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +n0: U32, +i: U32,
  +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +hr: {FM.rt.ok(root, n0) == True{} : Bool}, +he: {FM.eras.ok(eras) == True{} : Bool},
  +hi: {U32.is_lt(i, n0) == True{} : Bool}, +hl: {Nat.is_le(List.length(&2, U32, seen), 1n+U32.to_nat(i)) == True{} : Bool}) ->
  {FM.inv.r(F.fz.emits(seen, F.FzE{hp(t0, ta), LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}:
  %Equal.sym(F.FzE, F.fz.emits(seen, mkS(ta, LAT.fromT(U32, tm), ST{t0, Fl{nodes, eras, ne, ls, root, curs}}), i), mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), emsb(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, hf, i)) :
    {FM.inv.r(_, n0) == True{} : Bool}
  %Equal.sym(Bool, FM.inv.r(mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), n0), ir(st.f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), n0), inv_r_f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i), ta, tm, n0)) :
    {_ == True{} : Bool}
  ems_r(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i, n0, MB.and_eq_true(FM.rt.ok(root, n0), FM.eras.ok(eras), hr, he), hi, hl)

def er.m(+seen: List<&2, U32>, -A: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +dm: Nat, hf: {AD.full(U32, map, dm) == True{} : Bool}, +n0: U32, +i: U32,
  +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +hr: {FM.rt.ok(root, n0) == True{} : Bool}, +he: {FM.eras.ok(eras) == True{} : Bool},
  +hi: {U32.is_lt(i, n0) == True{} : Bool}, +hl: {Nat.is_le(List.length(&2, U32, seen), 1n+U32.to_nat(i)) == True{} : Bool},
  m0: LAT.Mirror(U32, A), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {FM.inv.r(F.fz.emits(seen, F.FzE{P.H{KM.MG{A}, a}, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}:
  (+t0, +e0) = m0
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, map, tm, dm, em, hf)
  %e0 : {FM.inv.r(F.fz.emits(seen, F.FzE{P.H{KM.MG{_}, a}, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}
  %ea : {FM.inv.r(F.fz.emits(seen, F.FzE{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}
  %em : {FM.inv.r(F.fz.emits(seen, F.FzE{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, _, nodes, eras, ne, ls, root, curs}, i), n0) == True{} : Bool}
  er.k(seen, t0, ta, tm, dm, hft, n0, i, nodes, eras, ne, ls, root, curs, hr, he, hi, hl)

def Laws.emits_root(seen, h, map, dm, hf, n0, i, nodes, eras, ne, ls, root, curs, hr, he, hi, hl):
  match h:
    case P.H{w, a}:
      match w:
        case KM.MG{A}:
          er.m(seen, A, a, map, dm, hf, n0, i, nodes, eras, ne, ls, root, curs, hr, he, hi, hl, LAT.mirror(U32, A), LAT.mirror(V.Val, a), LAT.mirror(U32, map))

# --- the read nodes' kinds (emits_nodes)

def nr.n(+r: NR) -> T.TNode:
  match r:
    case NR{+t, +n}:
      n

def nr.t(+r: NR) -> LAT.Tree<U32>:
  match r:
    case NR{+t, +n}:
      t

# a read node an eraser exactly when its kind is an eraser's
def lv_era(+un: Bool, +k: R.NodeKind, +f: U32) -> {S.sp.is_era(F.fz.lv(un, k, f)) == S.sp.is_era(T.TN{k, V.PNone{}}) : Bool}:
  match un:
    case True{}:
      {==}
    case False{}:
      {==}

def fan_era(+un: Bool, +k: R.NodeKind, +f: U32) -> {S.sp.is_era(F.fz.fan(un, k, f)) == False{} : Bool}:
  match un:
    case True{}:
      {==}
    case False{}:
      {==}

def ndw_era(+r: TV, +k: R.NodeKind) -> {S.sp.is_era(nr.n(nd.w(r, k))) == S.sp.is_era(T.TN{k, V.PNone{}}) : Bool}:
  match r:
    case TV{+t, +v}:
      {==}

def nd_era(+k: R.NodeKind, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +hd: U32, +b: U32) -> {S.sp.is_era(nr.n(nd(k, t0, ta, hd, b))) == S.sp.is_era(T.TN{k, V.PNone{}}) : Bool}:
  match k:
    case R.KFree{}:
      {==}
    case R.KFn{}:
      lv_era(U32.is_eq(P.form(hd), P.unlev()), R.KFn{}, P.fld(hd))
    case R.KAp{}:
      lv_era(U32.is_eq(P.form(hd), P.unlev()), R.KAp{}, P.fld(hd))
    case R.KCopy{}:
      fan_era(U32.is_eq(P.form(hd), P.unlev()), R.KCopy{}, P.fld(hd))
    case R.KMerge{}:
      fan_era(U32.is_eq(P.form(hd), P.unlev()), R.KMerge{}, P.fld(hd))
    case R.KData{}:
      ndw_era(nd.pk(t0, ta, hd, hw(t0, (b + 2 : U32))), R.KData{})
    case R.KEraN{}:
      {==}
    case R.KEraP{}:
      {==}
    case R.KRoot{}:
      {==}
    case R.KOp{}:
      ndw_era(nd.pk(t0, ta, hd, hw(t0, (b + 3 : U32))), R.KOp{})
    case R.KLift{}:
      {==}
    case R.KLiftC{}:
      {==}
    case R.KCopyL{}:
      fan_era(U32.is_eq(P.form(hd), P.unlev()), R.KCopyL{}, P.fld(hd))
    case R.KCopyR{}:
      fan_era(U32.is_eq(P.form(hd), P.unlev()), R.KCopyR{}, P.fld(hd))
    case R.KMergeL{}:
      fan_era(U32.is_eq(P.form(hd), P.unlev()), R.KMergeL{}, P.fld(hd))
    case R.KMergeR{}:
      fan_era(U32.is_eq(P.form(hd), P.unlev()), R.KMergeR{}, P.fld(hd))
    case R.KDOp{}:
      ndw_era(nd.pk(t0, ta, hd, hw(t0, (b + 3 : U32))), R.KDOp{})
    case R.KFnD{}:
      lv_era(U32.is_eq(P.form(hd), P.unlev()), R.KFnD{}, P.fld(hd))
    case R.KCur{}:
      {==}

def in_(+f: Fl, +n0: U32) -> Bool:
  match f:
    case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
      FM.no_era(nodes)

def c.k(+tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +n0: U32) -> Bool:
  FM.k.ok(N.kof(P.rk(hw(tc, b))))

def n_era(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {in_(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.k(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {in_(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, n0) == True{} : Bool}:
  h

def n_root(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {in_(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.k(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {in_(Fl{nodes, eras, ne, ls, T.TE{i, p}, curs}, n0) == True{} : Bool}:
  h

def n_hole(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {in_(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.k(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {in_(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, n0) == True{} : Bool}:
  h

def n_link(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {in_(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.k(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool},
  +hst: {P.is_static(q) == False{} : Bool}, +hu: {U32.is_eq(mv(tm, dm, P.base(q)), 0) == False{} : Bool}) -> {in_(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, n0) == True{} : Bool}:
  h

def n_na(+r: NR, +f: Fl, +n0: U32, +hr: {Bool.not(S.sp.is_era(nr.n(r))) == True{} : Bool}, +h: {in_(f, n0) == True{} : Bool}) -> {in_(na(r, f), n0) == True{} : Bool}:
  match r:
    case NR{+t, +n}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          MB.and_eq_true(Bool.not(S.sp.is_era(n)), FM.no_era(nodes), hr, h)

def n_node(+f: Fl, +n0: U32, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +h: {in_(f, n0) == True{} : Bool}, +hC: {c.k(tc, ta, tm, dm, b, i, n0) == True{} : Bool}) ->
  {in_(na(nd(N.kof(P.rk(hw(tc, b))), tc, ta, hw(tc, b), b), f), n0) == True{} : Bool}:
  +K = N.kof(P.rk(hw(tc, b)))
  n_na(nd(N.kof(P.rk(hw(tc, b))), tc, ta, hw(tc, b), b), f, n0,
    Equal.trans(Bool, Bool.not(S.sp.is_era(nr.n(nd(N.kof(P.rk(hw(tc, b))), tc, ta, hw(tc, b), b)))), Bool.not(S.sp.is_era(T.TN{K, V.PNone{}})), True{},
      Equal.cong(Bool, Bool, z => Bool.not(z), S.sp.is_era(nr.n(nd(N.kof(P.rk(hw(tc, b))), tc, ta, hw(tc, b), b))), S.sp.is_era(T.TN{K, V.PNone{}}), nd_era(K, tc, ta, hw(tc, b), b)), hC), h)

def em_n(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +n0: U32, +h: {in_(st.f(s), n0) == True{} : Bool}, +hC: {c.k(st.t(s), ta, tm, dm, b, i, n0) == True{} : Bool}) ->
  {in_(st.f(em(s, ta, tm, dm, b, i)), n0) == True{} : Bool}:
  em_T(~U32, ~id32, ~in_, ~c.k, ~n_era, ~n_root, ~n_hole, ~n_link, ~n_node, s, ta, tm, dm, b, i, n0, h, hC)

# copied for the frame (INDEX_PROOF.bend's wl_ne and wd, proofgen/align's
# slot_mod4 and ne_mod4; to be shared under cursor-laws.proofs)
def wl_ne(+v: List<&2, U32>, +d: Nat, +j: U32, +i: U32, +val: U32, +h: {Nat.is_eq(AD.slot(j, d), AD.slot(i, d)) == False{} : Bool}) ->
  {KMd.word(v, d, i) == KMd.word(List.set(&2, U32, v, AD.slot(j, d), val), d, i) : U32}:
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, v, AD.slot(j, d), val), AD.slot(i, d)), List.get(&2, U32, v, AD.slot(i, d)), LAB.get_set_ne(U32, v, AD.slot(j, d), AD.slot(i, d), val, h)) :
    {KMd.word(v, d, i) == KMd.word.m(_) : U32}
  {==}

def slot_mod4(+i: U32, +d: Nat, +h2: {Nat.is_le(2n, d) == True{} : Bool}) -> {Nat.mod(AD.slot(i, d), 4n) == Nat.mod(U32.to_nat(i), 4n) : Nat}:
  WL.nat_mod_mod_pow(U32.to_nat(i), 2n, d, h2)

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

def wdv(+t0: LAT.Tree<U32>, +d: Nat, +i: U32, +hft: {AD.full(U32, LAT.fromT(U32, t0), d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}) ->
  {KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, i) == hw(t0, i) : U32}:
  %LA.get_view(U32, LAT.fromT(U32, t0), d, i, hft, hd32) : {KMd.word.m(_) == hw(t0, i) : U32}
  {==}

# the words' frame: an error's write at word 1 keeps each aligned base's
# header, the words full
def hdrs_set(bs: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +x: U32, +h2: {Nat.is_le(2n, d) == True{} : Bool}, +h: {FM.hdrs.ok(bs, v, d) == True{} : Bool}) ->
  {FM.hdrs.ok(bs, List.set(&2, U32, v, AD.slot(1, d), x), d) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, r}:
      +hb = MB.eq_true_of_and_left(Nat.is_eq(Nat.mod(U32.to_nat(b), 4n), 0n), FM.k.ok(N.kof(P.rk(KMd.word(v, d, b)))) && FM.hdrs.ok(r, v, d), h)
      +hrest = MB.eq_true_of_and_right(Nat.is_eq(Nat.mod(U32.to_nat(b), 4n), 0n), FM.k.ok(N.kof(P.rk(KMd.word(v, d, b)))) && FM.hdrs.ok(r, v, d), h)
      +hk = MB.eq_true_of_and_left(FM.k.ok(N.kof(P.rk(KMd.word(v, d, b)))), FM.hdrs.ok(r, v, d), hrest)
      +hr = MB.eq_true_of_and_right(FM.k.ok(N.kof(P.rk(KMd.word(v, d, b)))), FM.hdrs.ok(r, v, d), hrest)
      +hz = Equal.trans(Nat, Nat.mod(AD.slot(b, d), 4n), Nat.mod(U32.to_nat(b), 4n), 0n, slot_mod4(b, d, h2), MN.eq_of_is_eq(Nat.mod(U32.to_nat(b), 4n), 0n, hb))
      +hne = nt_of(Nat.is_eq(AD.slot(1, d), AD.slot(b, d)), ne_mod4(AD.slot(1, d), AD.slot(b, d), 1n, 0n, slot_mod4(1, d, h2), hz, {==}))
      %wl_ne(v, d, 1, b, x, hne) : {(Nat.is_eq(Nat.mod(U32.to_nat(b), 4n), 0n) && (FM.k.ok(N.kof(P.rk(_))) && FM.hdrs.ok(r, List.set(&2, U32, v, AD.slot(1, d), x), d))) == True{} : Bool}
      MB.and_eq_true(Nat.is_eq(Nat.mod(U32.to_nat(b), 4n), 0n), FM.k.ok(N.kof(P.rk(KMd.word(v, d, b)))) && FM.hdrs.ok(r, List.set(&2, U32, v, AD.slot(1, d), x), d), hb,
        MB.and_eq_true(FM.k.ok(N.kof(P.rk(KMd.word(v, d, b)))), FM.hdrs.ok(r, List.set(&2, U32, v, AD.slot(1, d), x), d), hk, hdrs_set(r, v, d, x, h2, hr)))

def et_keeps(+bad: Bool, +bs: List<&2, U32>, +tc: LAT.Tree<U32>, +d: Nat, +h2: {Nat.is_le(2n, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +h: {(AD.full(U32, LAT.fromT(U32, tc), d) && FM.hdrs.ok(bs, AD.view(U32, LAT.fromT(U32, tc)), d)) == True{} : Bool}) -> {(AD.full(U32, LAT.fromT(U32, et(bad, tc)), d) && FM.hdrs.ok(bs, AD.view(U32, LAT.fromT(U32, et(bad, tc))), d)) == True{} : Bool}:
  match bad:
    case False{}:
      h
    case True{}:
      +hf = MB.eq_true_of_and_left(AD.full(U32, LAT.fromT(U32, tc), d), FM.hdrs.ok(bs, AD.view(U32, LAT.fromT(U32, tc)), d), h)
      +hh = MB.eq_true_of_and_right(AD.full(U32, LAT.fromT(U32, tc), d), FM.hdrs.ok(bs, AD.view(U32, LAT.fromT(U32, tc)), d), h)
      %LAI.set_tree_eq(U32, tc, P.at_errs(), (hw(tc, P.at_errs()) + 1 : U32)) : {(AD.full(U32, _, d) && FM.hdrs.ok(bs, AD.view(U32, _), d)) == True{} : Bool}
      %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, tc), P.at_errs(), (hw(tc, P.at_errs()) + 1 : U32))), List.set(&2, U32, AD.view(U32, LAT.fromT(U32, tc)), AD.slot(P.at_errs(), d), (hw(tc, P.at_errs()) + 1 : U32)),
          LA.set_view(U32, LAT.fromT(U32, tc), d, P.at_errs(), (hw(tc, P.at_errs()) + 1 : U32), hf, hd32)) :
        {(AD.full(U32, Array.set(U32, LAT.fromT(U32, tc), P.at_errs(), (hw(tc, P.at_errs()) + 1 : U32)), d) && FM.hdrs.ok(bs, _, d)) == True{} : Bool}
      MB.and_eq_true(AD.full(U32, Array.set(U32, LAT.fromT(U32, tc), P.at_errs(), (hw(tc, P.at_errs()) + 1 : U32)), d), FM.hdrs.ok(bs, List.set(&2, U32, AD.view(U32, LAT.fromT(U32, tc)), AD.slot(P.at_errs(), d), (hw(tc, P.at_errs()) + 1 : U32)), d),
        LA.set_full(U32, LAT.fromT(U32, tc), d, P.at_errs(), (hw(tc, P.at_errs()) + 1 : U32), hf), hdrs_set(bs, AD.view(U32, LAT.fromT(U32, tc)), d, (hw(tc, P.at_errs()) + 1 : U32), h2, hh))

def tv.t(+r: TV) -> LAT.Tree<U32>:
  match r:
    case TV{+t, +v}:
      t

def pc_keeps(r: V.Val & Bool, +bs: List<&2, U32>, +tc: LAT.Tree<U32>, +d: Nat, +h2: {Nat.is_le(2n, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +h: {(AD.full(U32, LAT.fromT(U32, tc), d) && FM.hdrs.ok(bs, AD.view(U32, LAT.fromT(U32, tc)), d)) == True{} : Bool}) -> {(AD.full(U32, LAT.fromT(U32, tv.t(pk.c(r, tc))), d) && FM.hdrs.ok(bs, AD.view(U32, LAT.fromT(U32, tv.t(pk.c(r, tc)))), d)) == True{} : Bool}:
  match r:
    case (v, +bad):
      et_keeps(bad, bs, tc, d, h2, hd32, h)

def pk_keeps(+one: Bool, +two: Bool, +three: Bool, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +f: U32, +w: U32, +bs: List<&2, U32>, +d: Nat, +h2: {Nat.is_le(2n, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +h: {(AD.full(U32, LAT.fromT(U32, tc), d) && FM.hdrs.ok(bs, AD.view(U32, LAT.fromT(U32, tc)), d)) == True{} : Bool}) ->
  {(AD.full(U32, LAT.fromT(U32, tv.t(pk.k(one, two, three, tc, ta, f, w))), d) && FM.hdrs.ok(bs, AD.view(U32, LAT.fromT(U32, tv.t(pk.k(one, two, three, tc, ta, f, w)))), d)) == True{} : Bool}:
  match one:
    case True{}:
      h
    case False{}:
      match two:
        case True{}:
          h
        case False{}:
          match three:
            case True{}:
              h
            case False{}:
              pc_keeps(V.free_chk(tv(ta, w)), bs, tc, d, h2, hd32, h)

def ndw_t(+r: TV, +k: R.NodeKind) -> {nr.t(nd.w(r, k)) == tv.t(r) : LAT.Tree<U32>}:
  match r:
    case TV{+t, +v}:
      {==}

# the node read's tree keeps the frame
def nd_keeps(+k: R.NodeKind, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +hd: U32, +b: U32, +bs: List<&2, U32>, +d: Nat, +h2: {Nat.is_le(2n, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +h: {(AD.full(U32, LAT.fromT(U32, tc), d) && FM.hdrs.ok(bs, AD.view(U32, LAT.fromT(U32, tc)), d)) == True{} : Bool}) ->
  {(AD.full(U32, LAT.fromT(U32, nr.t(nd(k, tc, ta, hd, b))), d) && FM.hdrs.ok(bs, AD.view(U32, LAT.fromT(U32, nr.t(nd(k, tc, ta, hd, b)))), d)) == True{} : Bool}:
  match k:
    case R.KFree{}:
      h
    case R.KFn{}:
      h
    case R.KAp{}:
      h
    case R.KCopy{}:
      h
    case R.KMerge{}:
      h
    case R.KData{}:
      %Equal.sym(LAT.Tree<U32>, nr.t(nd.w(nd.pk(tc, ta, hd, hw(tc, (b + 2 : U32))), R.KData{})), tv.t(nd.pk(tc, ta, hd, hw(tc, (b + 2 : U32)))), ndw_t(nd.pk(tc, ta, hd, hw(tc, (b + 2 : U32))), R.KData{})) : {(AD.full(U32, LAT.fromT(U32, _), d) && FM.hdrs.ok(bs, AD.view(U32, LAT.fromT(U32, _)), d)) == True{} : Bool}
      pk_keeps(U32.is_eq(P.form(hd), 1), U32.is_eq(P.form(hd), 2), U32.is_eq(P.form(hd), 3), tc, ta, P.fld(hd), hw(tc, (b + 2 : U32)), bs, d, h2, hd32, h)
    case R.KEraN{}:
      h
    case R.KEraP{}:
      h
    case R.KRoot{}:
      h
    case R.KOp{}:
      %Equal.sym(LAT.Tree<U32>, nr.t(nd.w(nd.pk(tc, ta, hd, hw(tc, (b + 3 : U32))), R.KOp{})), tv.t(nd.pk(tc, ta, hd, hw(tc, (b + 3 : U32)))), ndw_t(nd.pk(tc, ta, hd, hw(tc, (b + 3 : U32))), R.KOp{})) : {(AD.full(U32, LAT.fromT(U32, _), d) && FM.hdrs.ok(bs, AD.view(U32, LAT.fromT(U32, _)), d)) == True{} : Bool}
      pk_keeps(U32.is_eq(P.form(hd), 1), U32.is_eq(P.form(hd), 2), U32.is_eq(P.form(hd), 3), tc, ta, P.fld(hd), hw(tc, (b + 3 : U32)), bs, d, h2, hd32, h)
    case R.KLift{}:
      h
    case R.KLiftC{}:
      h
    case R.KCopyL{}:
      h
    case R.KCopyR{}:
      h
    case R.KMergeL{}:
      h
    case R.KMergeR{}:
      h
    case R.KDOp{}:
      %Equal.sym(LAT.Tree<U32>, nr.t(nd.w(nd.pk(tc, ta, hd, hw(tc, (b + 3 : U32))), R.KDOp{})), tv.t(nd.pk(tc, ta, hd, hw(tc, (b + 3 : U32)))), ndw_t(nd.pk(tc, ta, hd, hw(tc, (b + 3 : U32))), R.KDOp{})) : {(AD.full(U32, LAT.fromT(U32, _), d) && FM.hdrs.ok(bs, AD.view(U32, LAT.fromT(U32, _)), d)) == True{} : Bool}
      pk_keeps(U32.is_eq(P.form(hd), 1), U32.is_eq(P.form(hd), 2), U32.is_eq(P.form(hd), 3), tc, ta, P.fld(hd), hw(tc, (b + 3 : U32)), bs, d, h2, hd32, h)
    case R.KFnD{}:
      h
    case R.KCur{}:
      h

def emt_t(+r: NR, +f: Fl, +tm: LAT.Tree<U32>, +dm: Nat, +k: R.NodeKind, +b: U32, +i: U32) -> {st.t(em.t(r, f, tm, dm, k, b, i)) == nr.t(r) : LAT.Tree<U32>}:
  match r:
    case NR{+t, +n}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          {==}

def em_t(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32) ->
  {st.t(em(s, ta, tm, dm, b, i)) == nr.t(nd(N.kof(P.rk(hw(st.t(s), b))), st.t(s), ta, hw(st.t(s), b), b)) : LAT.Tree<U32>}:
  match s:
    case ST{+t, +f}:
      emt_t(nd(N.kof(P.rk(hw(t, b))), t, ta, hw(t, b), b), f, tm, dm, N.kof(P.rk(hw(t, b))), b, i)

def ems_n(seen: List<&2, U32>, +s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +i: U32, +n0: U32, +d: Nat, +h2: {Nat.is_le(2n, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +h: {in_(st.f(s), n0) == True{} : Bool}, +hk: {(AD.full(U32, LAT.fromT(U32, st.t(s)), d) && FM.hdrs.ok(seen, AD.view(U32, LAT.fromT(U32, st.t(s))), d)) == True{} : Bool}) ->
  {in_(st.f(ems(seen, s, ta, tm, dm, i)), n0) == True{} : Bool}:
  match seen:
    case Nil{}:
      h
    case Con{+b, +rest}:
      +V0 = AD.view(U32, LAT.fromT(U32, st.t(s)))
      +hfull = MB.eq_true_of_and_left(AD.full(U32, LAT.fromT(U32, st.t(s)), d), FM.hdrs.ok(Con{b, rest}, V0, d), hk)
      +hh = MB.eq_true_of_and_right(AD.full(U32, LAT.fromT(U32, st.t(s)), d), FM.hdrs.ok(Con{b, rest}, V0, d), hk)
      +h3 = MB.eq_true_of_and_right(Nat.is_eq(Nat.mod(U32.to_nat(b), 4n), 0n), FM.k.ok(N.kof(P.rk(KMd.word(V0, d, b)))) && FM.hdrs.ok(rest, V0, d), hh)
      +hmid = MB.eq_true_of_and_left(FM.k.ok(N.kof(P.rk(KMd.word(V0, d, b)))), FM.hdrs.ok(rest, V0, d), h3)
      +htl = MB.eq_true_of_and_right(FM.k.ok(N.kof(P.rk(KMd.word(V0, d, b)))), FM.hdrs.ok(rest, V0, d), h3)
      +hC = ME.subst(U32, z => {FM.k.ok(N.kof(P.rk(z))) == True{} : Bool}, KMd.word(V0, d, b), hw(st.t(s), b), wdv(st.t(s), d, b, hfull, hd32), hmid)
      +hk2 = ME.subst(LAT.Tree<U32>, z => {(AD.full(U32, LAT.fromT(U32, z), d) && FM.hdrs.ok(rest, AD.view(U32, LAT.fromT(U32, z)), d)) == True{} : Bool}, nr.t(nd(N.kof(P.rk(hw(st.t(s), b))), st.t(s), ta, hw(st.t(s), b), b)), st.t(em(s, ta, tm, dm, b, i)),
        Equal.sym(LAT.Tree<U32>, st.t(em(s, ta, tm, dm, b, i)), nr.t(nd(N.kof(P.rk(hw(st.t(s), b))), st.t(s), ta, hw(st.t(s), b), b)), em_t(s, ta, tm, dm, b, i)),
        nd_keeps(N.kof(P.rk(hw(st.t(s), b))), st.t(s), ta, hw(st.t(s), b), b, rest, d, h2, hd32, MB.and_eq_true(AD.full(U32, LAT.fromT(U32, st.t(s)), d), FM.hdrs.ok(rest, V0, d), hfull, htl)))
      ems_n(rest, em(s, ta, tm, dm, b, i), ta, tm, dm, (i - 1 : U32), n0, d, h2, hd32, em_n(s, ta, tm, dm, b, i, n0, h, hC), hk2)

def inv_n_f(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +n0: U32) -> {FM.inv.n(mkS(ta, LAT.fromT(U32, tm), s)) == in_(st.f(s), n0) : Bool}:
  match s:
    case ST{+t, +f}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          {==}

def en.k(+seen: List<&2, U32>, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +d: Nat, +h2: {Nat.is_le(2n, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hk: {(AD.full(U32, LAT.fromT(U32, t0), d) && FM.hdrs.ok(seen, AD.view(U32, LAT.fromT(U32, t0)), d)) == True{} : Bool}, +n0: U32, +i: U32, +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +hn: {FM.no_era(nodes) == True{} : Bool}) ->
  {FM.inv.n(F.fz.emits(seen, F.FzE{hp(t0, ta), LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs}, i)) == True{} : Bool}:
  %Equal.sym(F.FzE, F.fz.emits(seen, mkS(ta, LAT.fromT(U32, tm), ST{t0, Fl{nodes, eras, ne, ls, root, curs}}), i), mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), emsb(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, hf, i)) :
    {FM.inv.n(_) == True{} : Bool}
  %Equal.sym(Bool, FM.inv.n(mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i))), in_(st.f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), n0), inv_n_f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i), ta, tm, n0)) :
    {_ == True{} : Bool}
  ems_n(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i, n0, d, h2, hd32, hn, hk)

def en.m(+seen: List<&2, U32>, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +dm: Nat, hf: {AD.full(U32, map, dm) == True{} : Bool},
  +d: Nat, hfw: {AD.full(U32, w, d) == True{} : Bool}, +hd32: {Nat.is_lt(d, 32n) == True{} : Bool}, +h2: {Nat.is_le(2n, d) == True{} : Bool}, hh: {FM.hdrs.ok(seen, AD.view(U32, w), d) == True{} : Bool},
  +n0: U32, +i: U32, +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +hn: {FM.no_era(nodes) == True{} : Bool},
  m0: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {FM.inv.n(F.fz.emits(seen, F.FzE{P.H{KM.MG{w}, a}, map, nodes, eras, ne, ls, root, curs}, i)) == True{} : Bool}:
  (+t0, +e0) = m0
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, map, tm, dm, em, hf)
  +hfwt = LAP.full_t(U32, w, t0, d, e0, hfw)
  +hht = LAB.subst(Array<U32>, x => {FM.hdrs.ok(seen, AD.view(U32, x), d) == True{} : Bool}, w, LAT.fromT(U32, t0), Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e0), hh)
  %e0 : {FM.inv.n(F.fz.emits(seen, F.FzE{P.H{KM.MG{_}, a}, map, nodes, eras, ne, ls, root, curs}, i)) == True{} : Bool}
  %ea : {FM.inv.n(F.fz.emits(seen, F.FzE{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map, nodes, eras, ne, ls, root, curs}, i)) == True{} : Bool}
  %em : {FM.inv.n(F.fz.emits(seen, F.FzE{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, _, nodes, eras, ne, ls, root, curs}, i)) == True{} : Bool}
  en.k(seen, t0, ta, tm, dm, hft, d, h2, hd32, MB.and_eq_true(AD.full(U32, LAT.fromT(U32, t0), d), FM.hdrs.ok(seen, AD.view(U32, LAT.fromT(U32, t0)), d), hfwt, hht), n0, i, nodes, eras, ne, ls, root, curs, hn)

def Laws.emits_nodes(seen, w, a, map, dm, hf, d, hfw, hd32, h2, hh, n0, i, nodes, eras, ne, ls, root, curs, hn):
  en.m(seen, w, a, map, dm, hf, d, hfw, hd32, h2, hh, n0, i, nodes, eras, ne, ls, root, curs, hn, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))

# --- the nodes' count (emits_len): the template at ~Nat, entered at the
# node's step (emt_T) with the count one more

def fl.nodes(+f: Fl) -> List<&2, T.TNode>:
  match f:
    case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
      nodes

def il(+f: Fl, +m: Nat) -> Bool:
  Nat.is_eq(List.length(&2, T.TNode, fl.nodes(f)), m)

def c.tn(+tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32, +n0: Nat) -> Bool:
  True{}

def len_era(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: Nat, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {il(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.tn(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {il(Fl{nodes, Con{F.fz.era(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, curs}, n0) == True{} : Bool}:
  h

def len_root(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +n0: Nat, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {il(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.tn(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {il(Fl{nodes, eras, ne, ls, T.TE{i, p}, curs}, n0) == True{} : Bool}:
  h

def len_hole(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: Nat, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {il(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.tn(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool}) -> {il(Fl{nodes, Con{F.fz.hole(R.port_pol(k, U32.to_nat(p))), eras}, (ne + 1 : U32), Con{T.TL{T.TE{i, p}, T.TE{ne, 0}}, ls}, root, Con{RN.FzC{ne, (b + p : U32), F.fz.neg(R.port_pol(k, U32.to_nat(p))), q}, curs}}, n0) == True{} : Bool}:
  h

def len_link(+nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>, +k: R.NodeKind, +b: U32, +i: U32, +p: U32, +q: U32, +n0: Nat, +tc: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat,
  +h: {il(Fl{nodes, eras, ne, ls, root, curs}, n0) == True{} : Bool}, +hC: {c.tn(tc, ta, tm, dm, b, i, n0) == True{} : Bool}, +hp: {SM.port3(p) == True{} : Bool},
  +hst: {P.is_static(q) == False{} : Bool}, +hu: {U32.is_eq(mv(tm, dm, P.base(q)), 0) == False{} : Bool}) -> {il(Fl{nodes, eras, ne, F.fz.link.k(U32.is_lt(i, (mv(tm, dm, P.base(q)) - 1 : U32)) || (U32.is_eq(i, (mv(tm, dm, P.base(q)) - 1 : U32)) && U32.is_lt(p, (q .&. 3 : U32))), i, p, (mv(tm, dm, P.base(q)) - 1 : U32), (q .&. 3 : U32), ls), root, curs}, n0) == True{} : Bool}:
  h

def len_na(+r: NR, +f: Fl) -> {il(na(r, f), 1n+List.length(&2, T.TNode, fl.nodes(f))) == True{} : Bool}:
  match r:
    case NR{+t, +n}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          MN.is_eq_refl(1n+List.length(&2, T.TNode, nodes))

# a node's step adds one node
def em_len(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +b: U32, +i: U32) -> {il(st.f(em(s, ta, tm, dm, b, i)), 1n+List.length(&2, T.TNode, fl.nodes(st.f(s)))) == True{} : Bool}:
  match s:
    case ST{+t, +f}:
      emt_T(~Nat, ~idnat, ~il, ~c.tn, ~len_era, ~len_root, ~len_hole, ~len_link, nd(N.kof(P.rk(hw(t, b))), t, ta, hw(t, b), b), f, N.kof(P.rk(hw(t, b))), b, i,
        1n+List.length(&2, T.TNode, fl.nodes(f)), t, ta, tm, dm, len_na(nd(N.kof(P.rk(hw(t, b))), t, ta, hw(t, b), b), f), {==})

def ems_len(seen: List<&2, U32>, +s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +i: U32) ->
  {List.length(&2, T.TNode, fl.nodes(st.f(ems(seen, s, ta, tm, dm, i)))) == Nat.add(List.length(&2, U32, seen), List.length(&2, T.TNode, fl.nodes(st.f(s)))) : Nat}:
  match seen:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      +L = List.length(&2, T.TNode, fl.nodes(st.f(s)))
      +E = List.length(&2, T.TNode, fl.nodes(st.f(em(s, ta, tm, dm, b, i))))
      +he = MN.eq_of_is_eq(E, 1n+L, em_len(s, ta, tm, dm, b, i))
      Equal.trans(Nat, List.length(&2, T.TNode, fl.nodes(st.f(ems(rest, em(s, ta, tm, dm, b, i), ta, tm, dm, (i - 1 : U32))))), Nat.add(List.length(&2, U32, rest), E), 1n+Nat.add(List.length(&2, U32, rest), L),
        ems_len(rest, em(s, ta, tm, dm, b, i), ta, tm, dm, (i - 1 : U32)),
        Equal.trans(Nat, Nat.add(List.length(&2, U32, rest), E), Nat.add(List.length(&2, U32, rest), 1n+L), 1n+Nat.add(List.length(&2, U32, rest), L),
          Equal.cong(Nat, Nat, z => Nat.add(List.length(&2, U32, rest), z), E, 1n+L, he), MN.add_succ(List.length(&2, U32, rest), L)))

def nodes_mkS(+s: ST, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>) -> {FM.nodes.of(mkS(ta, LAT.fromT(U32, tm), s)) == fl.nodes(st.f(s)) : List<&2, T.TNode>}:
  match s:
    case ST{+t, +f}:
      match f:
        case Fl{+nodes, +eras, +ne, +ls, +root, +curs}:
          {==}

def el.k(+seen: List<&2, U32>, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +dm: Nat, +hf: {AD.full(U32, LAT.fromT(U32, tm), dm) == True{} : Bool}, +i: U32, +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>) ->
  {List.length(&2, T.TNode, FM.nodes.of(F.fz.emits(seen, F.FzE{hp(t0, ta), LAT.fromT(U32, tm), nodes, eras, ne, ls, root, curs}, i))) == Nat.add(List.length(&2, U32, seen), List.length(&2, T.TNode, nodes)) : Nat}:
  %Equal.sym(F.FzE, F.fz.emits(seen, mkS(ta, LAT.fromT(U32, tm), ST{t0, Fl{nodes, eras, ne, ls, root, curs}}), i), mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)), emsb(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, hf, i)) :
    {List.length(&2, T.TNode, FM.nodes.of(_)) == Nat.add(List.length(&2, U32, seen), List.length(&2, T.TNode, nodes)) : Nat}
  %Equal.sym(List<&2, T.TNode>, FM.nodes.of(mkS(ta, LAT.fromT(U32, tm), ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i))), fl.nodes(st.f(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i))), nodes_mkS(ems(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i), ta, tm)) :
    {List.length(&2, T.TNode, _) == Nat.add(List.length(&2, U32, seen), List.length(&2, T.TNode, nodes)) : Nat}
  ems_len(seen, ST{t0, Fl{nodes, eras, ne, ls, root, curs}}, ta, tm, dm, i)

def el.m(+seen: List<&2, U32>, -A: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +dm: Nat, hf: {AD.full(U32, map, dm) == True{} : Bool}, +i: U32, +nodes: List<&2, T.TNode>, +eras: List<&2, T.TNode>, +ne: U32, +ls: List<&2, T.TLink>, +root: T.TEnd, +curs: List<&2, RN.FzC>,
  m0: LAT.Mirror(U32, A), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {List.length(&2, T.TNode, FM.nodes.of(F.fz.emits(seen, F.FzE{P.H{KM.MG{A}, a}, map, nodes, eras, ne, ls, root, curs}, i))) == Nat.add(List.length(&2, U32, seen), List.length(&2, T.TNode, nodes)) : Nat}:
  (+t0, +e0) = m0
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, map, tm, dm, em, hf)
  %e0 : {List.length(&2, T.TNode, FM.nodes.of(F.fz.emits(seen, F.FzE{P.H{KM.MG{_}, a}, map, nodes, eras, ne, ls, root, curs}, i))) == Nat.add(List.length(&2, U32, seen), List.length(&2, T.TNode, nodes)) : Nat}
  %ea : {List.length(&2, T.TNode, FM.nodes.of(F.fz.emits(seen, F.FzE{P.H{KM.MG{LAT.fromT(U32, t0)}, _}, map, nodes, eras, ne, ls, root, curs}, i))) == Nat.add(List.length(&2, U32, seen), List.length(&2, T.TNode, nodes)) : Nat}
  %em : {List.length(&2, T.TNode, FM.nodes.of(F.fz.emits(seen, F.FzE{P.H{KM.MG{LAT.fromT(U32, t0)}, LAT.fromT(V.Val, ta)}, _, nodes, eras, ne, ls, root, curs}, i))) == Nat.add(List.length(&2, U32, seen), List.length(&2, T.TNode, nodes)) : Nat}
  el.k(seen, t0, ta, tm, dm, hft, i, nodes, eras, ne, ls, root, curs)

def Laws.emits_len(seen, h, map, dm, hf, i, nodes, eras, ne, ls, root, curs):
  match h:
    case P.H{w, a}:
      match w:
        case KM.MG{A}:
          el.m(seen, A, a, map, dm, hf, i, nodes, eras, ne, ls, root, curs, LAT.mirror(U32, A), LAT.mirror(V.Val, a), LAT.mirror(U32, map))
