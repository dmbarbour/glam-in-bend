# authoring aid: glam/JOIN_PROOF.bend, the proof of link_live
props=open('glam/proofgen/link_props.bend').read()
T=lambda h: f'{{{h} == True{{}} : Bool}}'
F_=lambda h: f'{{{h} == False{{}} : Bool}}'
def conj(t):
    return t[0] if len(t)==1 else (f'{t[0]} && ({conj(t[1:])})' if len(t)>2 else f'{t[0]} && {t[1]}')
def proj(t, n, h):
    e=h
    for m in range(n): e=f'and_r({t[m]}, {conj(t[m+1:])}, {e})'
    if n<len(t)-1: e=f'and_l({t[n]}, {conj(t[n+1:])}, {e})'
    return e
SL=lambda a: f'AD.slot({a}, d)'
def P1(x,i): return x if i==0 else f'({x} + {i} : U32)'
OP=lambda r,j: f'KMd.off.port(d, {r}, {j})'
A0='LAT.fromT(U32, t0)'; A1='LAT.fromT(U32, t1)'
V0=f'AD.view(U32, {A0})'
LK1=f'lk(su, {A0}, u, w)'
V2=f'AD.view(U32, lk(sw, {A1}, w, u))'
WD=lambda v,i: f'KMd.word({v}, d, {i})'
FZ=WD(V0,'(z + 1 : U32)'); FQ=WD(V0,'(q + 1 : U32)')
TRI=lambda v: [f'RG.faces(L2, {v}, d, L2)', f'RG.px.off(L2, {v}, d, L2, N)', f'RG.px.tw(L2, {v}, d, L2)']
out='''# The proof of a join's link over the facing (glam/JOIN_LAWS.bend;
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
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import 0x8ae61ec3a6615abd35f196c07232ad28/string.bend as MS
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

def nhas(+L: List<&2, U32>, +z: U32, +x: U32, +hz: {RG.has(L, z) == True{} : Bool}, +hx: {RG.has(L, x) == False{} : Bool}) -> {U32.is_eq(z, x) == False{} : Bool}:
  nhas.k(U32.is_eq(z, x), L, z, x, {==}, hz, hx)
'''
out=out.replace('''def nhas(+L''','''def nhas.k(+e: Bool, +L: List<&2, U32>, +z: U32, +x: U32, +he: {U32.is_eq(z, x) == e : Bool}, +hz: {RG.has(L, z) == True{} : Bool}, +hx: {RG.has(L, x) == False{} : Bool}) ->
  {U32.is_eq(z, x) == False{} : Bool}:
  match e:
    case True{}:
      Empty.absurd({U32.is_eq(z, x) == False{} : Bool}, MB.true_ne_false()(Equal.trans(Bool, True{}, RG.has(L, x), False{},
        Equal.sym(Bool, RG.has(L, x), True{}, ME.subst(U32, q => {RG.has(L, q) == True{} : Bool}, z, x, MS.u32_eq_of_is_eq(z, x, he), hz)), hx)))
    case False{}:
      he

def nhas(+L''')
# word_lk
WL=lambda st,A: f'KMd.word(AD.view(U32, lk({st}, {A}, r, val)), d, i)'
SELV=lambda v: f'sel(KMd.off.port(d, r, i), KMd.word({v}, d, i), val)'
VT='AD.view(U32, LAT.fromT(U32, t))'
LSV=f'List.set(&2, U32, v, AD.slot((r + 1 : U32), d), val)'
out+=f'''
def wlk.e(+e: Bool, +v: List<&2, U32>, +d: Nat, +r: U32, +val: U32, +i: U32, +he: {{Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(i, d)) == e : Bool}},
  +hs: {{XP.is_some(List.get(&2, U32, v, AD.slot((r + 1 : U32), d))) == True{{}} : Bool}}) ->
  {{KMd.word({LSV}, d, i) == sel(Bool.not(e), KMd.word(v, d, i), val) : U32}}:
  match e:
    case True{{}}:
      %MN.eq_of_is_eq(AD.slot((r + 1 : U32), d), AD.slot(i, d), he) : {{KMd.word.m(List.get(&2, U32, {LSV}, _)) == val : U32}}
      XP.wl_eq2(v, d, (r + 1 : U32), val, hs)
    case False{{}}:
      Equal.sym(U32, KMd.word(v, d, i), KMd.word({LSV}, d, i), XP.wl_ne(v, d, (r + 1 : U32), i, val, he))

# a word after a link's write: the value where the port's link word is it
def word_lk(+st: Bool, +t: LAT.Tree<U32>, +d: Nat, +r: U32, +val: U32, +i: U32, +hst: {{P.is_static(r) == st : Bool}},
  +hf: {{AD.full(U32, LAT.fromT(U32, t), d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}) ->
  {{{WL('st','LAT.fromT(U32, t)')} == {SELV(VT)} : U32}}:
  match st:
    case True{{}}:
      %Equal.sym(Bool, P.is_static(r), True{{}}, hst) : {{{WL('True{}','LAT.fromT(U32, t)')} == sel(KMd.off.lw(KMd.lw.k(_, r), d, i), KMd.word({VT}, d, i), val) : U32}}
      {{==}}
    case False{{}}:
      %Equal.sym(Bool, P.is_static(r), False{{}}, hst) : {{{WL('False{}','LAT.fromT(U32, t)')} == sel(KMd.off.lw(KMd.lw.k(_, r), d, i), KMd.word({VT}, d, i), val) : U32}}
      %Equal.sym(List<&2, U32>, AD.view(U32, Array.set(U32, LAT.fromT(U32, t), (r + 1 : U32), val)), List.set(&2, U32, {VT}, AD.slot((r + 1 : U32), d), val),
        LA.set_view(U32, LAT.fromT(U32, t), d, (r + 1 : U32), val, hf, hd32)) : {{KMd.word(_, d, i) == sel(Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(i, d))), KMd.word({VT}, d, i), val) : U32}}
      wlk.e(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(i, d)), {VT}, d, r, val, i, {{==}},
        ME.subst(Maybe<&2, U32>, m => {{XP.is_some(m) == True{{}} : Bool}}, Some{{Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), (r + 1 : U32)))}}, List.get(&2, U32, {VT}, AD.slot((r + 1 : U32), d)),
          LA.get_view(U32, LAT.fromT(U32, t), d, (r + 1 : U32), hf, hd32), {{==}}))

def op_sel(+B: Bool, +A: Bool, +f: U32, +w: U32, +u: U32, +d: Nat, +j: U32) -> {{KMd.off.port(d, sel(B, sel(A, f, w), u), j) == sel3(B, A, {OP('f','j')}, {OP('w','j')}, {OP('u','j')}) : Bool}}:
  match B:
    case True{{}}:
      match A:
        case True{{}}:
          {{==}}
        case False{{}}:
          {{==}}
    case False{{}}:
      {{==}}
'''
# no2
out+=f'''
# no port's link word in two tracked nodes' words 1
def no2.e(+e1: Bool, +e2: Bool, +a: U32, +b: U32, +r: U32, +d: Nat, +he1: {{Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((a + 1 : U32), d)) == e1 : Bool}},
  +he2: {{Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((b + 1 : U32), d)) == e2 : Bool}}, +hab: {{Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d)) == False{{}} : Bool}}) ->
  {T('Bool.or(Bool.not(e1), Bool.not(e2))')}:
  match e1:
    case False{{}}:
      {{==}}
    case True{{}}:
      match e2:
        case False{{}}:
          {{==}}
        case True{{}}:
          Empty.absurd({T('Bool.or(Bool.not(True{}), Bool.not(True{}))')}, MB.false_ne_true()(Equal.trans(Bool, False{{}}, Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d)), True{{}},
            Equal.sym(Bool, Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d)), False{{}}, hab),
            ME.subst(Nat, q => {{Nat.is_eq(q, AD.slot((a + 1 : U32), d)) == True{{}} : Bool}}, AD.slot((a + 1 : U32), d), AD.slot((b + 1 : U32), d),
              Equal.trans(Nat, AD.slot((a + 1 : U32), d), AD.slot((r + 1 : U32), d), AD.slot((b + 1 : U32), d),
                Equal.sym(Nat, AD.slot((r + 1 : U32), d), AD.slot((a + 1 : U32), d), MN.eq_of_is_eq(AD.slot((r + 1 : U32), d), AD.slot((a + 1 : U32), d), he1)),
                MN.eq_of_is_eq(AD.slot((r + 1 : U32), d), AD.slot((b + 1 : U32), d), he2)),
              MN.is_eq_refl(AD.slot((a + 1 : U32), d))))))

def no2.k(+st: Bool, +r: U32, +a: U32, +b: U32, +d: Nat, +hst: {{P.is_static(r) == st : Bool}}, +hab: {{Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d)) == False{{}} : Bool}}) ->
  {T(f"Bool.or({OP('r','(a + 1 : U32)')}, {OP('r','(b + 1 : U32)')})")}:
  match st:
    case True{{}}:
      %Equal.sym(Bool, P.is_static(r), True{{}}, hst) : {T('Bool.or(KMd.off.lw(KMd.lw.k(_, r), d, (a + 1 : U32)), KMd.off.lw(KMd.lw.k(_, r), d, (b + 1 : U32)))')}
      {{==}}
    case False{{}}:
      %Equal.sym(Bool, P.is_static(r), False{{}}, hst) : {T('Bool.or(KMd.off.lw(KMd.lw.k(_, r), d, (a + 1 : U32)), KMd.off.lw(KMd.lw.k(_, r), d, (b + 1 : U32)))')}
      no2.e(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((a + 1 : U32), d)), Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot((b + 1 : U32), d)), a, b, r, d, {{==}}, {{==}}, hab)

def no2(+r: U32, +a: U32, +b: U32, +d: Nat, +N: List<&2, U32>, +hN: {T('RG.layout(N, d)')}, +ha: {T('RG.has(N, a)')}, +hb: {T('RG.has(N, b)')}, +hne: {F_('U32.is_eq(a, b)')}) ->
  {T(f"Bool.or({OP('r','(a + 1 : U32)')}, {OP('r','(b + 1 : U32)')})")}:
  no2.k(P.is_static(r), r, a, b, d, {{==}}, not_true(Nat.is_eq(AD.slot((b + 1 : U32), d), AD.slot((a + 1 : U32), d)),
    {proj([f'Bool.not(Nat.is_eq({SL(P1("b",q))}, {SL("(a + 1 : U32)")}))' for q in range(4)]+['True{}'],1,
      proj([f'KMd.off.words(KMd.nw(b), d, {P1("a",i)})' for i in range(4)],1,'and_l(IM.nd.disj(d, a, b), IM.nd.disj(d, b, a), XL.layout_sep(N, d, a, b, hN, ha, hb, hne))'))}))
'''
out=out.replace('IM.nd.disj','IMd.nd.disj')
# member extraction
def extract(name, fold_sig, fold, head, tail_args, extra_sig, extra_args):
    pass
out+=f'''
# what a member of L had before the link
def fm_word(m: Maybe<&2, U32>, +d: Nat, +M: List<&2, U32>, +h: {T('RG.faces.m(m, d, M)')}) -> {T('RG.port.ok(M, d, KMd.word.m(m))')}:
  match m:
    case Some{{+r}}:
      h
    case None{{}}:
      Empty.absurd({T('RG.port.ok(M, d, KMd.word.m(None{}))')}, MB.false_ne_true()(h))

def fm_of_word(m: Maybe<&2, U32>, +d: Nat, +M: List<&2, U32>, +hs: {T('XP.is_some(m)')}, +h: {T('RG.port.ok(M, d, KMd.word.m(m))')}) -> {T('RG.faces.m(m, d, M)')}:
  match m:
    case Some{{+r}}:
      h
    case None{{}}:
      Empty.absurd({T('RG.faces.m(None{}, d, M)')}, MB.false_ne_true()(hs))
'''
GET=lambda z: f'List.get(&2, U32, v, AD.slot(({z} + 1 : U32), d))'
def mem(name, sig, fold_t, head_t, rest_t, hyp_name, hd=None, tl=None):
    # fold_t(ys) over ys, head_t(y) the head conjunct, the member z's
    return f'''
def {name}.k(+e: Bool, +y: U32, +t: List<&2, U32>, {sig}, +z: U32, +he: {{U32.is_eq(y, z) == e : Bool}}, +h: {T(fold_t('Con{y, t}'))},
  +hz: {T('Bool.or(U32.is_eq(y, z), RG.has(t, z))')}, ih: {T('RG.has(t, z)')} -> {T(head_t('z'))}) -> {T(head_t('z'))}:
  match e:
    case True{{}}:
      %MS.u32_eq_of_is_eq(y, z, he) : {T(head_t('_'))}
      {hd('y','t','h') if hd else f"and_l({head_t('y')}, {rest_t('t')}, h)"}
    case False{{}}:
      ih(ort_r(U32.is_eq(y, z), RG.has(t, z), he, hz))

def {name}(ys: List<&2, U32>, {sig}, +z: U32, +h: {T(fold_t('ys'))}, +hz: {T('RG.has(ys, z)')}) -> {T(head_t('z'))}:
  match ys:
    case Nil{{}}:
      Empty.absurd({T(head_t('z'))}, MB.false_ne_true()(hz))
    case Con{{+y, +t}}:
      {name}.k(U32.is_eq(y, z), y, t, {', '.join(a.split(':')[0].strip('+ ') for a in sig.split(', +'))}, z, {{==}}, h, hz, hzt => {name}(t, {', '.join(a.split(':')[0].strip('+ ') for a in sig.split(', +'))}, z, {tl('y','t','h') if tl else f"and_r({head_t('y')}, {rest_t('t')}, h)"}, hzt))
'''
SIGF='+v: List<&2, U32>, +d: Nat, +M: List<&2, U32>'
out+=mem('fm_of', SIGF, lambda ys: f'RG.faces({ys}, v, d, M)', lambda z: f'RG.faces.m({GET(z)}, d, M)', lambda t: f'RG.faces({t}, v, d, M)', 'h')
SIGO='+v: List<&2, U32>, +d: Nat, +L: List<&2, U32>, +N: List<&2, U32>'
out+=mem('po_of', SIGO, lambda ys: f'RG.px.off({ys}, v, d, L, N)', lambda z: f'RG.po.all(KMd.word(v, d, ({z} + 1 : U32)), L, d, N)', lambda t: f'RG.px.off({t}, v, d, L, N)', 'h')
SIGT='+v: List<&2, U32>, +d: Nat, +L: List<&2, U32>'
NSH=lambda z: f'KMd.off.port(d, KMd.word(v, d, ({z} + 1 : U32)), ({z} + 1 : U32))'
TQH=lambda z: f'RG.tw.q(L, KMd.word(v, d, ({z} + 1 : U32)), {z}, v, d)'
PT=lambda t: f'RG.px.tw({t}, v, d, L)'
out+=mem('ns_of', SIGT, lambda ys: f'RG.px.tw({ys}, v, d, L)', lambda z: f'{NSH(z)} && {TQH(z)}', PT, 'h',
  hd=lambda y,t,h: f"and_intro({NSH(y)}, {TQH(y)}, and_l({NSH(y)}, {TQH(y)} && {PT(t)}, {h}), and_l({TQH(y)}, {PT(t)}, and_r({NSH(y)}, {TQH(y)} && {PT(t)}, {h})))",
  tl=lambda y,t,h: f"and_r({TQH(y)}, {PT(t)}, and_r({NSH(y)}, {TQH(y)} && {PT(t)}, {h}))")
SIGQ='+r: U32, +x: U32, +v: List<&2, U32>, +d: Nat'
TWA=lambda q: f'Bool.or(KMd.off.port(d, r, ({q} + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, ({q} + 1 : U32)), (x + 1 : U32))))'
out+=mem('tw_at', SIGQ, lambda ys: f'RG.tw.q({ys}, r, x, v, d)', TWA, lambda t: f'RG.tw.q({t}, r, x, v, d)', 'h')
# port.ok conversions
OL=lambda M,i: f'RG.off.links({M}, d, {i})'; OPS=lambda M,i: f'RG.off.pos({M}, d, {i})'
out+=mem('ol_at', '+d: Nat, +i: U32', lambda ys: OL(ys,'i'), lambda z: f'Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot(({z} + 3 : U32), d)))', lambda t: OL(t,'i'), 'h')
out+=mem('opos_at', '+d: Nat, +i: U32', lambda ys: OPS(ys,'i'), lambda z: f'Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot(({z} + 2 : U32), d)))', lambda t: OPS(t,'i'), 'h')
out+=f'''
def ol_sub(M2: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +i: U32, +hs: {T('RG.sub(M2, M)')}, +h: {T(OL('M','i'))}) -> {T(OL('M2','i'))}:
  match M2:
    case Nil{{}}:
      {{==}}
    case Con{{+m, +t}}:
      and_intro(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 3 : U32), d))), {OL('t','i')}, ol_at(M, d, i, m, h, and_l(RG.has(M, m), RG.sub(t, M), hs)),
        ol_sub(t, M, d, i, and_r(RG.has(M, m), RG.sub(t, M), hs), h))

def opos_sub(M2: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +i: U32, +hs: {T('RG.sub(M2, M)')}, +h: {T(OPS('M','i'))}) -> {T(OPS('M2','i'))}:
  match M2:
    case Nil{{}}:
      {{==}}
    case Con{{+m, +t}}:
      and_intro(Bool.not(Nat.is_eq(AD.slot(i, d), AD.slot((m + 2 : U32), d))), {OPS('t','i')}, opos_at(M, d, i, m, h, and_l(RG.has(M, m), RG.sub(t, M), hs)),
        opos_sub(t, M, d, i, and_r(RG.has(M, m), RG.sub(t, M), hs), h))

def pk_sub(+M2: List<&2, U32>, +M: List<&2, U32>, +d: Nat, +r: U32, +hs: {T('RG.sub(M2, M)')}, +h: {T('RG.port.ok(M, d, r)')}) -> {T('RG.port.ok(M2, d, r)')}:
  and_intro({OL('M2','(r + 1 : U32)')}, {OPS('M2','(r + 1 : U32)')}, ol_sub(M2, M, d, (r + 1 : U32), hs, and_l({OL('M','(r + 1 : U32)')}, {OPS('M','(r + 1 : U32)')}, h)),
    opos_sub(M2, M, d, (r + 1 : U32), hs, and_r({OL('M','(r + 1 : U32)')}, {OPS('M','(r + 1 : U32)')}, h)))

def pk_sel(+B: Bool, +A: Bool, +f: U32, +w: U32, +u: U32, +d: Nat, +M: List<&2, U32>, +hf: {T('RG.port.ok(M, d, f)')}, +hw: {T('RG.port.ok(M, d, w)')}, +hu: {T('RG.port.ok(M, d, u)')}) ->
  {T('RG.port.ok(M, d, sel(B, sel(A, f, w), u))')}:
  match B:
    case True{{}}:
      match A:
        case True{{}}:
          hf
        case False{{}}:
          hw
    case False{{}}:
      hu

def po_sel(+B: Bool, +A: Bool, +f: U32, +w: U32, +u: U32, +d: Nat, +L: List<&2, U32>, +N: List<&2, U32>, +hf: {T('RG.po.all(f, L, d, N)')}, +hw: {T('RG.po.all(w, L, d, N)')}, +hu: {T('RG.po.all(u, L, d, N)')}) ->
  {T('RG.po.all(sel(B, sel(A, f, w), u), L, d, N)')}:
  match B:
    case True{{}}:
      match A:
        case True{{}}:
          hf
        case False{{}}:
          hw
    case False{{}}:
      hu
'''
for jw,(fn,nm) in [(2,('opos_at','pk2')),(3,('ol_at','pk3'))]:
    Fold = OPS if jw==2 else OL
    getter = (lambda h: f"and_r({OL('M','(r + 1 : U32)')}, {OPS('M','(r + 1 : U32)')}, {h})") if jw==2 else (lambda h: f"and_l({OL('M','(r + 1 : U32)')}, {OPS('M','(r + 1 : U32)')}, {h})")
    out+=f'''
def {nm}.k(+st: Bool, +M: List<&2, U32>, +d: Nat, +r: U32, +m: U32, +hst: {{P.is_static(r) == st : Bool}}, +h: {T('RG.port.ok(M, d, r)')}, +hm: {T('RG.has(M, m)')}) -> {T(OP('r',f'(m + {jw} : U32)'))}:
  match st:
    case True{{}}:
      %Equal.sym(Bool, P.is_static(r), True{{}}, hst) : {T(f'KMd.off.lw(KMd.lw.k(_, r), d, (m + {jw} : U32))')}
      {{==}}
    case False{{}}:
      %Equal.sym(Bool, P.is_static(r), False{{}}, hst) : {T(f'KMd.off.lw(KMd.lw.k(_, r), d, (m + {jw} : U32))')}
      {fn}(M, d, (r + 1 : U32), m, {getter('h')}, hm)

def {nm}(+M: List<&2, U32>, +d: Nat, +r: U32, +m: U32, +h: {T('RG.port.ok(M, d, r)')}, +hm: {T('RG.has(M, m)')}) -> {T(OP('r',f'(m + {jw} : U32)'))}:
  {nm}.k(P.is_static(r), M, d, r, m, {{==}}, h, hm)
'''
# po_shrink
W3=lambda r,n: f"{OP(r,f'({n} + 1 : U32)')} && ({OP(r,f'({n} + 2 : U32)')} && {OP(r,f'({n} + 3 : U32)')})"
PN=lambda L,n: f'Bool.or(RG.has({L}, {n}), {W3("r",n)})'
out+=f'''
# r's link word off x's and y's words 1 to 3: po over L2 from po over L
def pn.x(+ex: Bool, +x: U32, +y: U32, +n: U32, +r: U32, +d: Nat, +hex: {{U32.is_eq(x, n) == ex : Bool}}, +hor: {T('Bool.or(U32.is_eq(x, n), U32.is_eq(y, n))')},
  +hwx: {T(W3('r','x'))}, +hwy: {T(W3('r','y'))}) -> {T(W3('r','n'))}:
  match ex:
    case True{{}}:
      %MS.u32_eq_of_is_eq(x, n, hex) : {T(W3('r','_'))}
      hwx
    case False{{}}:
      %MS.u32_eq_of_is_eq(y, n, ort_r(U32.is_eq(x, n), U32.is_eq(y, n), hex, hor)) : {T(W3('r','_'))}
      hwy

def pn.k(+e2: Bool, +e1: Bool, +L: List<&2, U32>, +L2: List<&2, U32>, +x: U32, +y: U32, +n: U32, +r: U32, +d: Nat, +he2: {{RG.has(L2, n) == e2 : Bool}}, +he1: {{RG.has(L, n) == e1 : Bool}},
  +h: {T(PN('L','n'))}, +hs2: {T('RG.sub(L, Con{x, Con{y, L2}})')}, +hwx: {T(W3('r','x'))}, +hwy: {T(W3('r','y'))}) -> {T(PN('L2','n'))}:
  match e2:
    case True{{}}:
      %Equal.sym(Bool, RG.has(L2, n), True{{}}, he2) : {T(f'Bool.or(_, {W3("r","n")})')}
      {{==}}
    case False{{}}:
      match e1:
        case False{{}}:
          %Equal.sym(Bool, RG.has(L2, n), False{{}}, he2) : {T(f'Bool.or(_, {W3("r","n")})')}
          ME.subst(Bool, q => {T(f'Bool.or(q, {W3("r","n")})')}, RG.has(L, n), False{{}}, he1, h)
        case True{{}}:
          +hn = XP.sub_has2(L, Con{{x, Con{{y, L2}}}}, n, hs2, he1)
          %Equal.sym(Bool, RG.has(L2, n), False{{}}, he2) : {T(f'Bool.or(_, {W3("r","n")})')}
          pn.x(U32.is_eq(x, n), x, y, n, r, d, {{==}}, ort_r2(U32.is_eq(x, n), U32.is_eq(y, n), RG.has(L2, n), he2, hn), hwx, hwy)

def po_shrink(N: List<&2, U32>, +r: U32, +L: List<&2, U32>, +L2: List<&2, U32>, +x: U32, +y: U32, +d: Nat, +h: {T('RG.po.all(r, L, d, N)')}, +hs2: {T('RG.sub(L, Con{x, Con{y, L2}})')},
  +hwx: {T(W3('r','x'))}, +hwy: {T(W3('r','y'))}) -> {T('RG.po.all(r, L2, d, N)')}:
  match N:
    case Nil{{}}:
      h
    case Con{{+n, +t}}:
      and_intro(RG.po.n(r, L2, d, n), RG.po.all(r, L2, d, t),
        and_intro(KMd.off.port(d, r, n), {PN('L2','n')}, and_l(KMd.off.port(d, r, n), {PN('L','n')}, and_l(RG.po.n(r, L, d, n), RG.po.all(r, L, d, t), h)),
          pn.k(RG.has(L2, n), RG.has(L, n), L, L2, x, y, n, r, d, {{==}}, {{==}}, and_r(KMd.off.port(d, r, n), {PN('L','n')}, and_l(RG.po.n(r, L, d, n), RG.po.all(r, L, d, t), h)), hs2, hwx, hwy)),
        po_shrink(t, r, L, L2, x, y, d, and_r(RG.po.n(r, L, d, n), RG.po.all(r, L, d, t), h), hs2, hwx, hwy))
'''
out=out.replace("ort_r2(U32.is_eq(x, n), U32.is_eq(y, n), RG.has(L2, n), he2, hn)","or3_drop(U32.is_eq(x, n), U32.is_eq(y, n), RG.has(L2, n), he2, hn)")
out+=f'''
def or3_drop(+a: Bool, +b: Bool, +c: Bool, +hc: {F_('c')}, +h: {T('Bool.or(a, Bool.or(b, c))')}) -> {T('Bool.or(a, b)')}:
  match a:
    case True{{}}:
      {{==}}
    case False{{}}:
      match b:
        case True{{}}:
          {{==}}
        case False{{}}:
          ME.subst(Bool, q => {T('q')}, c, False{{}}, hc, h)
'''
# move or3_drop before pn.k
k1=out.index('# r\'s link word off x\'s and y\'s words 1 to 3'); k2=out.index('\ndef or3_drop(')
out=out[:k1]+out[k2+1:]+'\n'+out[k1:k2]
out=out.replace('XP.sub_has2(','sub_has2(')
out+=f'''
def sub_has2(B: List<&2, U32>, +C: List<&2, U32>, +a: U32, +hbc: {T('RG.sub(B, C)')}, +hb: {{RG.has(B, a) == True{{}} : Bool}}) -> {T('RG.has(C, a)')}:
  match B:
    case Nil{{}}:
      Empty.absurd({T('RG.has(C, a)')}, MB.false_ne_true()(hb))
    case Con{{+m, +t}}:
      sh.k(U32.is_eq(m, a), m, t, C, a, {{==}}, hbc, hb, hta => sub_has2(t, C, a, and_r(RG.has(C, m), RG.sub(t, C), hbc), hta))
'''
out=out.replace(f'''
def sub_has2(''',f'''
def sh.k(+e: Bool, +m: U32, +t: List<&2, U32>, +C: List<&2, U32>, +a: U32, +he: {{U32.is_eq(m, a) == e : Bool}}, +hbc: {T('RG.sub(Con{m, t}, C)')}, +hb: {T('Bool.or(U32.is_eq(m, a), RG.has(t, a))')},
  ih: {T('RG.has(t, a)')} -> {T('RG.has(C, a)')}) -> {T('RG.has(C, a)')}:
  match e:
    case True{{}}:
      %MS.u32_eq_of_is_eq(m, a, he) : {T('RG.has(C, _)')}
      and_l(RG.has(C, m), RG.sub(t, C), hbc)
    case False{{}}:
      ih(ort_r(U32.is_eq(m, a), RG.has(t, a), he, hb))

def sub_has2(''')
# sub_has2 must come before pn.k: move it and sh.k up front of the po section
k1=out.index('\ndef sh.k('); blk=out[k1:]; out=out[:k1]
kk=out.index('\ndef or3_drop(')
out=out[:kk]+blk+out[kk:]
out+='\n'+props
# the per-z and per-(z, q) facts and the inductions
AZ=lambda z: OP('u',f'({z} + 1 : U32)'); BZ=lambda z: OP('w',f'({z} + 1 : U32)')
FW=lambda z: WD(V0,f'({z} + 1 : U32)')
def PF(z,n): return OP(FW(z),f'({n} + 1 : U32)')
def ns(z): return f"and_l({NSH(z).replace('v, d','" + V0 + ", d')}, {TQH(z)}, ns_of(L, {V0}, d, L, {z}, hT, h{z}L))"
NSv=lambda z: f'KMd.off.port(d, {FW(z)}, ({z} + 1 : U32))'
TQv=lambda z: f'RG.tw.q(L, {FW(z)}, {z}, {V0}, d)'
def nsf(z): return f'and_l({NSv(z)}, {TQv(z)}, ns_of(L, {V0}, d, L, {z}, hT, {hz(z)}))'
def twq(z): return f'and_r({NSv(z)}, {TQv(z)}, ns_of(L, {V0}, d, L, {z}, hT, {hz(z)}))'
def hz(z): return {'x':'hx','y':'hy'}.get(z, f'h{z}L')
def tw(z,q):
    # or(off.port(f_z, q+1), not(off.port(f_q, z+1))), from tw.q of z at q
    return f'tw_at(L, {FW(z)}, {z}, {V0}, d, {q}, {twq(z)}, {hz(q)})'
def subu(z, e):
    # rewrite x's and y's faces (words) to u, w in a fact e about them
    return e
def facesub(term, fact, who):
    # a fact stated with x's face word, turned to u (who='x') or w (who='y')
    pass
# a fact about f_x turned into one about u: ME.subst over the word
def to_u(pred_lam, fact):  # pred_lam: q => T(...)
    return f'ME.subst(U32, q => {pred_lam}, {FW("x")}, u, hu, {fact})'
def to_w(pred_lam, fact):
    return f'ME.subst(U32, q => {pred_lam}, {FW("y")}, w, hw, {fact})'
def NE(a,b): return f'{{U32.is_eq({a}, {b}) == False{{}} : Bool}}'
out+=f'''
# the facts of a live node z of L2 before the link, x and y facing u and w
def zf(+t0: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +z: U32, +u: U32, +w: U32,
  +hN: {T('RG.layout(N, d)')}, +hLN: {T('RG.sub(L, N)')}, +hx: {T('RG.has(L, x)')}, +hy: {T('RG.has(L, y)')}, +hzL: {T('RG.has(L, z)')},
  +hxy: {NE('x','y')}, +hzx: {NE('z','x')}, +hzy: {NE('z','y')}, +hu: {{{FW('x')} == u : U32}}, +hw: {{{FW('y')} == w : U32}}, +hT: {T(f'RG.px.tw(L, {V0}, d, L)')}) ->
  {T('sel3(' + BZ('z') + ', ' + AZ('z') + ', ' + PF('z','x') + ', ' + OP('w','(x + 1 : U32)') + ', ' + OP('u','(x + 1 : U32)') + ') && (sel3(' + BZ('z') + ', ' + AZ('z') + ', ' + PF('z','y') + ', ' + OP('w','(y + 1 : U32)') + ', ' + OP('u','(y + 1 : U32)') + ') && sel3(' + BZ('z') + ', ' + AZ('z') + ', ' + PF('z','z') + ', ' + BZ('z') + ', ' + AZ('z') + '))')}:
  +hxN = sub_has2(L, N, x, hLN, hx)
  +hyN = sub_has2(L, N, y, hLN, hy)
  +hzN = sub_has2(L, N, z, hLN, hzL)
  +nsx = {to_u(T(OP('q','(x + 1 : U32)')), nsf('x'))}
  +nsy = {to_w(T(OP('q','(y + 1 : U32)')), nsf('y'))}
  +nsz = {nsf('z')}
  +tzx = {to_u(T(f"Bool.or({PF('z','x')}, Bool.not({OP('q','(z + 1 : U32)')}))"), tw('z','x'))}
  +tzy = {to_w(T(f"Bool.or({PF('z','y')}, Bool.not({OP('q','(z + 1 : U32)')}))"), tw('z','y'))}
  +txz = {to_u(T(f"Bool.or({OP('q','(z + 1 : U32)')}, Bool.not({PF('z','x')}))"), tw('x','z'))}
  +tyz = {to_w(T(f"Bool.or({OP('q','(z + 1 : U32)')}, Bool.not({PF('z','y')}))"), tw('y','z'))}
  +txy = {to_w(T(f"Bool.or({OP('u','(y + 1 : U32)')}, Bool.not({OP('q','(x + 1 : U32)')}))"), to_u(T(f"Bool.or({OP('q','(y + 1 : U32)')}, Bool.not({OP(FW('y'),'(x + 1 : U32)')}))"), tw('x','y')))}
  +tyx = {to_u(T(f"Bool.or({OP('w','(x + 1 : U32)')}, Bool.not({OP('q','(y + 1 : U32)')}))"), to_w(T(f"Bool.or({OP('q','(x + 1 : U32)')}, Bool.not({OP(FW('x'),'(y + 1 : U32)')}))"), tw('y','x')))}
  +o_uyz = no2(u, y, z, d, N, hN, hyN, hzN, ueq_ne(z, y, hzy))
  +o_wxz = no2(w, x, z, d, N, hN, hxN, hzN, ueq_ne(z, x, hzx))
  +o_fxy = no2({FW('z')}, x, y, d, N, hN, hxN, hyN, hxy)
  and_intro(sel3({BZ('z')}, {AZ('z')}, {PF('z','x')}, {OP('w','(x + 1 : U32)')}, {OP('u','(x + 1 : U32)')}), sel3({BZ('z')}, {AZ('z')}, {PF('z','y')}, {OP('w','(y + 1 : U32)')}, {OP('u','(y + 1 : U32)')}) && sel3({BZ('z')}, {AZ('z')}, {PF('z','z')}, {BZ('z')}, {AZ('z')}),
    g2x({BZ('z')}, {AZ('z')}, {PF('z','x')}, {PF('z','y')}, {OP('w','(x + 1 : U32)')}, {OP('u','(y + 1 : U32)')}, {OP('u','(x + 1 : U32)')}, {OP('w','(y + 1 : U32)')}, {PF('z','z')}, nsx, nsy, nsz, tzx, tzy, txz, tyz, txy, tyx, o_uyz, o_wxz, o_fxy),
    and_intro(sel3({BZ('z')}, {AZ('z')}, {PF('z','y')}, {OP('w','(y + 1 : U32)')}, {OP('u','(y + 1 : U32)')}), sel3({BZ('z')}, {AZ('z')}, {PF('z','z')}, {BZ('z')}, {AZ('z')}),
      g2y({BZ('z')}, {AZ('z')}, {PF('z','x')}, {PF('z','y')}, {OP('w','(x + 1 : U32)')}, {OP('u','(y + 1 : U32)')}, {OP('u','(x + 1 : U32)')}, {OP('w','(y + 1 : U32)')}, {PF('z','z')}, nsx, nsy, nsz, tzx, tzy, txz, tyz, txy, tyx, o_uyz, o_wxz, o_fxy),
      g3({BZ('z')}, {AZ('z')}, {PF('z','x')}, {PF('z','y')}, {OP('w','(x + 1 : U32)')}, {OP('u','(y + 1 : U32)')}, {OP('u','(x + 1 : U32)')}, {OP('w','(y + 1 : U32)')}, {PF('z','z')}, nsx, nsy, nsz, tzx, tzy, txz, tyz, txy, tyx, o_uyz, o_wxz, o_fxy)))
'''
# per (z, q)
G4G=f"Bool.or(sel3({BZ('z')}, {AZ('z')}, {PF('z','q')}, {BZ('q')}, {AZ('q')}), Bool.not(sel3({BZ('q')}, {AZ('q')}, {PF('q','z')}, {BZ('z')}, {AZ('z')})))"
out+=f'''
def zqf(+t0: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +z: U32, +q: U32, +u: U32, +w: U32,
  +hN: {T('RG.layout(N, d)')}, +hLN: {T('RG.sub(L, N)')}, +hx: {T('RG.has(L, x)')}, +hy: {T('RG.has(L, y)')}, +hzL: {T('RG.has(L, z)')}, +hqL: {T('RG.has(L, q)')},
  +hxy: {NE('x','y')}, +hzx: {NE('z','x')}, +hzy: {NE('z','y')}, +hqx: {NE('q','x')}, +hqy: {NE('q','y')}, +hu: {{{FW('x')} == u : U32}}, +hw: {{{FW('y')} == w : U32}}, +hT: {T(f'RG.px.tw(L, {V0}, d, L)')}) ->
  {T(G4G)}:
  +hxN = sub_has2(L, N, x, hLN, hx)
  +hyN = sub_has2(L, N, y, hLN, hy)
  +hzN = sub_has2(L, N, z, hLN, hzL)
  +hqN = sub_has2(L, N, q, hLN, hqL)
  g4({BZ('z')}, {AZ('z')}, {BZ('q')}, {AZ('q')}, {PF('z','q')}, {PF('q','z')}, {PF('z','x')}, {PF('z','y')}, {PF('q','x')}, {PF('q','y')},
    {tw('z','q')}, {tw('q','z')},
    {to_u(T(f"Bool.or({OP('q','(z + 1 : U32)')}, Bool.not({PF('z','x')}))".replace("OP_Q","q")), tw('x','z'))},
    {to_u(T(f"Bool.or({OP('qq','(q + 1 : U32)')}, Bool.not({PF('q','x')}))"), tw('x','q')).replace('q => ','qq => ')},
    {to_w(T(f"Bool.or({OP('q','(z + 1 : U32)')}, Bool.not({PF('z','y')}))"), tw('y','z'))},
    {to_w(T(f"Bool.or({OP('qq','(q + 1 : U32)')}, Bool.not({PF('q','y')}))"), tw('y','q')).replace('q => ','qq => ')},
    {to_u(T(f"Bool.or({PF('z','x')}, Bool.not({OP('q','(z + 1 : U32)')}))"), tw('z','x'))},
    {to_u(T(f"Bool.or({PF('q','x')}, Bool.not({OP('qq','(q + 1 : U32)')}))"), tw('q','x')).replace('q => ','qq => ')},
    {to_w(T(f"Bool.or({PF('z','y')}, Bool.not({OP('q','(z + 1 : U32)')}))"), tw('z','y'))},
    {to_w(T(f"Bool.or({PF('q','y')}, Bool.not({OP('qq','(q + 1 : U32)')}))"), tw('q','y')).replace('q => ','qq => ')},
    no2({FW('q')}, z, y, d, N, hN, hzN, hyN, hzy), no2({FW('q')}, z, x, d, N, hN, hzN, hxN, hzx), no2({FW('q')}, x, y, d, N, hN, hxN, hyN, hxy),
    no2({FW('z')}, x, y, d, N, hN, hxN, hyN, hxy), no2({FW('z')}, q, y, d, N, hN, hqN, hyN, hqy), no2({FW('z')}, q, x, d, N, hN, hqN, hxN, hqx))
'''
# hface: the word after the link
SV2=lambda z: f"sel({BZ(z)}, sel({AZ(z)}, {FW(z)}, w), u)"
def hface(z):
    return (f"Equal.trans(U32, {WD(V2,f'({z} + 1 : U32)')}, sel({BZ(z)}, {WD('AD.view(U32, ' + A1 + ')',f'({z} + 1 : U32)')}, u), {SV2(z)}, "
            f"word_lk(sw, t1, d, w, u, ({z} + 1 : U32), hsw, hft1, hd32), "
            f"Equal.cong(U32, U32, qq => sel({BZ(z)}, qq, u), {WD('AD.view(U32, ' + A1 + ')',f'({z} + 1 : U32)')}, sel({AZ(z)}, {FW(z)}, w), "
            f"Equal.trans(U32, {WD('AD.view(U32, ' + A1 + ')',f'({z} + 1 : U32)')}, {WD('AD.view(U32, ' + LK1 + ')',f'({z} + 1 : U32)')}, sel({AZ(z)}, {FW(z)}, w), "
            f"Equal.cong(Array<U32>, U32, AA => KMd.word(AD.view(U32, AA), d, ({z} + 1 : U32)), {A1}, {LK1}, e1), word_lk(su, t0, d, u, w, ({z} + 1 : U32), hsu, hft, hd32))))")
COMMON_SIG=f'''+t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +u: U32, +w: U32, +su: Bool, +sw: Bool,
  +e1: {{{A1} == {LK1} : Array<U32>}}, +hsu: {{P.is_static(u) == su : Bool}}, +hsw: {{P.is_static(w) == sw : Bool}}, +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, +hft1: {{AD.full(U32, {A1}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}},
  +hN: {T('RG.layout(N, d)')}, +hLN: {T('RG.sub(L, N)')}, +hx: {T('RG.has(L, x)')}, +hy: {T('RG.has(L, y)')}, +hxy: {NE('x','y')}, +hs1: {T('RG.sub(L2, L)')}, +hs2: {T('RG.sub(L, Con{x, Con{y, L2}})')},
  +hx2: {F_('RG.has(L2, x)')}, +hy2: {F_('RG.has(L2, y)')}, +hu: {{{FW('x')} == u : U32}}, +hw: {{{FW('y')} == w : U32}},
  +hF: {T(f'RG.faces(L, {V0}, d, L)')}, +hO: {T(f'RG.px.off(L, {V0}, d, L, N)')}, +hT: {T(f'RG.px.tw(L, {V0}, d, L)')}'''
COMMON_ARGS='t0, t1, d, L, L2, N, x, y, u, w, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, hu, hw, hF, hO, hT'
FULL2=f'lk_full(sw, {A1}, d, w, u, hft1)'
LK2=f'lk(sw, {A1}, w, u)'
def zpre(z):
    return f'''  +h{z}L = sub_has2(L2, L, {z}, hs1, h{z}2)
  +h{z}x = nhas(L2, {z}, x, h{z}2, hx2)
  +h{z}y = nhas(L2, {z}, y, h{z}2, hy2)
'''
PKW=lambda z: f"sub_has2(L, N, {z}, hLN, h{z}L)"
def pkz(z):  # port.ok(L, d, f_z)
    return f"fm_word(List.get(&2, U32, {V0}, AD.slot(({z} + 1 : U32), d)), d, L, fm_of(L, {V0}, d, L, {z}, hF, {hz(z)}))"
PKu=to_u(T('RG.port.ok(L, d, q)'), pkz('x')); PKw=to_w(T('RG.port.ok(L, d, q)'), pkz('y'))
POu=to_u(T('RG.po.all(q, L, d, N)'), f'po_of(L, {V0}, d, L, N, x, hO, hx)'); POw=to_w(T('RG.po.all(q, L, d, N)'), f'po_of(L, {V0}, d, L, N, y, hO, hy)')
ZF=lambda z: f'zf(t0, d, L, N, x, y, {z}, u, w, hN, hLN, hx, hy, h{z}L, hxy, h{z}x, h{z}y, hu, hw, hT)'
S3x=lambda z: f"sel3({BZ(z)}, {AZ(z)}, {PF(z,'x')}, {OP('w','(x + 1 : U32)')}, {OP('u','(x + 1 : U32)')})"
S3y=lambda z: f"sel3({BZ(z)}, {AZ(z)}, {PF(z,'y')}, {OP('w','(y + 1 : U32)')}, {OP('u','(y + 1 : U32)')})"
S3z=lambda z: f"sel3({BZ(z)}, {AZ(z)}, {PF(z,'z')}, {BZ(z)}, {AZ(z)})"
def zfx(z): return f"and_l({S3x(z)}, {S3y(z)} && {S3z(z)}, {ZF(z)})"
def zfy(z): return f"and_l({S3y(z)}, {S3z(z)}, and_r({S3x(z)}, {S3y(z)} && {S3z(z)}, {ZF(z)}))"
def zfz(z): return f"and_r({S3y(z)}, {S3z(z)}, and_r({S3x(z)}, {S3y(z)} && {S3z(z)}, {ZF(z)}))"
def opsel(z, j):  # off.port(d, sel(...), j) == sel3(...)
    return f"op_sel({BZ(z)}, {AZ(z)}, {FW(z)}, w, u, d, {j})"
def via_sel(z, j, fact):
    # off.port(d, S(z), j) == True from the sel3 fact
    return f"Equal.trans(Bool, KMd.off.port(d, {SV2(z)}, {j}), sel3({BZ(z)}, {AZ(z)}, {OP(FW(z),j)}, {OP('w',j)}, {OP('u',j)}), True{{}}, {opsel(z,j)}, {fact})"
PKS=lambda z: f"pk_sel({BZ(z)}, {AZ(z)}, {FW(z)}, w, u, d, L, {pkz(z)}, {PKw}, {PKu})"
out+=f'''
# the faces after: each a port faceable by L, so by L2
def ind_f(ys: List<&2, U32>, {COMMON_SIG}, +hys: {T('RG.sub(ys, L2)')}) -> {T(f'RG.faces(ys, {V2}, d, L2)')}:
  match ys:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      +hz2 = and_l(RG.has(L2, z), RG.sub(r, L2), hys)
{zpre('z')}      and_intro(RG.faces.m(List.get(&2, U32, {V2}, AD.slot((z + 1 : U32), d)), d, L2), RG.faces(r, {V2}, d, L2),
        fm_of_word(List.get(&2, U32, {V2}, AD.slot((z + 1 : U32), d)), d, L2,
          ME.subst(Maybe<&2, U32>, m => {T('XP.is_some(m)')}, Some{{Pair.snd(Array<U32>, U32, Array.get(U32, {LK2}, (z + 1 : U32)))}}, List.get(&2, U32, {V2}, AD.slot((z + 1 : U32), d)), LA.get_view(U32, {LK2}, d, (z + 1 : U32), {FULL2}, hd32), {{==}}),
          ME.subst(U32, qq => {T('RG.port.ok(L2, d, qq)')}, {SV2('z')}, {WD(V2,'(z + 1 : U32)')}, Equal.sym(U32, {WD(V2,'(z + 1 : U32)')}, {SV2('z')}, {hface('z')}),
            pk_sub(L2, L, d, {SV2('z')}, hs1, {PKS('z')}))),
        ind_f(r, {COMMON_ARGS}, and_r(RG.has(L2, z), RG.sub(r, L2), hys)))
'''
W3S=lambda z,n: W3(SV2(z),n)
def w3(z,n):
    one = via_sel(z, f'({n} + 1 : U32)', zfx(z) if n=='x' else zfy(z))
    return f"and_intro({OP(SV2(z),f'({n} + 1 : U32)')}, {OP(SV2(z),f'({n} + 2 : U32)')} && {OP(SV2(z),f'({n} + 3 : U32)')}, {one}, and_intro({OP(SV2(z),f'({n} + 2 : U32)')}, {OP(SV2(z),f'({n} + 3 : U32)')}, pk2(L, d, {SV2(z)}, {n}, {PKS(z)}, h{n}), pk3(L, d, {SV2(z)}, {n}, {PKS(z)}, h{n})))"
out+=f'''
# what each of L2 faces after: off every tracked node's words as asked
def ind_o(ys: List<&2, U32>, {COMMON_SIG}, +hys: {T('RG.sub(ys, L2)')}) -> {T(f'RG.px.off(ys, {V2}, d, L2, N)')}:
  match ys:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      +hz2 = and_l(RG.has(L2, z), RG.sub(r, L2), hys)
{zpre('z')}      and_intro(RG.po.all({WD(V2,'(z + 1 : U32)')}, L2, d, N), RG.px.off(r, {V2}, d, L2, N),
        ME.subst(U32, qq => {T('RG.po.all(qq, L2, d, N)')}, {SV2('z')}, {WD(V2,'(z + 1 : U32)')}, Equal.sym(U32, {WD(V2,'(z + 1 : U32)')}, {SV2('z')}, {hface('z')}),
          po_shrink(N, {SV2('z')}, L, L2, x, y, d, po_sel({BZ('z')}, {AZ('z')}, {FW('z')}, w, u, d, L, N, po_of(L, {V0}, d, L, N, z, hO, hzL), {POw}, {POu}), hs2,
            {w3('z','x')}, {w3('z','y')})),
        ind_o(r, {COMMON_ARGS}, and_r(RG.has(L2, z), RG.sub(r, L2), hys)))
'''
G4F=lambda z,q: f'zqf(t0, d, L, N, x, y, {z}, {q}, u, w, hN, hLN, hx, hy, h{z}L, h{q}L, hxy, h{z}x, h{z}y, h{q}x, h{q}y, hu, hw, hT)'
TWG=f"Bool.or(KMd.off.port(d, {SV2('z')}, (q + 1 : U32)), Bool.not(KMd.off.port(d, {SV2('q')}, (z + 1 : U32))))"
out+=f'''
# z facing back what faces it after, over qs of L2
def ind_q(qs: List<&2, U32>, {COMMON_SIG}, +z: U32, +hz2: {T('RG.has(L2, z)')}, +hqs: {T('RG.sub(qs, L2)')}) -> {T(f"RG.tw.q(qs, {WD(V2,'(z + 1 : U32)')}, z, {V2}, d)")}:
  match qs:
    case Nil{{}}:
      {{==}}
    case Con{{+q, +r}}:
      +hq2 = and_l(RG.has(L2, q), RG.sub(r, L2), hqs)
{zpre('z')}{zpre('q')}      +hzq = Equal.trans(Bool, {TWG}, sel3({BZ('z')}, {AZ('z')}, {PF('z','q')}, {BZ('q')}, {AZ('q')}) || Bool.not(sel3({BZ('q')}, {AZ('q')}, {PF('q','z')}, {BZ('z')}, {AZ('z')})), True{{}},
        Equal.cong(Bool & Bool, Bool, pp => tw.or(pp), (KMd.off.port(d, {SV2('z')}, (q + 1 : U32)), KMd.off.port(d, {SV2('q')}, (z + 1 : U32))), (sel3({BZ('z')}, {AZ('z')}, {PF('z','q')}, {BZ('q')}, {AZ('q')}), sel3({BZ('q')}, {AZ('q')}, {PF('q','z')}, {BZ('z')}, {AZ('z')})),
          pair_eq({opsel('z','(q + 1 : U32)')}, {opsel('q','(z + 1 : U32)')})), {G4F('z','q')})
      and_intro(Bool.or(KMd.off.port(d, {WD(V2,'(z + 1 : U32)')}, (q + 1 : U32)), Bool.not(KMd.off.port(d, {WD(V2,'(q + 1 : U32)')}, (z + 1 : U32)))), RG.tw.q(r, {WD(V2,'(z + 1 : U32)')}, z, {V2}, d),
        ME.subst(U32, q2 => {T(f"Bool.or(KMd.off.port(d, {WD(V2,'(z + 1 : U32)')}, (q + 1 : U32)), Bool.not(KMd.off.port(d, q2, (z + 1 : U32))))")}, {SV2('q')}, {WD(V2,'(q + 1 : U32)')}, Equal.sym(U32, {WD(V2,'(q + 1 : U32)')}, {SV2('q')}, {hface('q')}),
          ME.subst(U32, q1 => {T(f"Bool.or(KMd.off.port(d, q1, (q + 1 : U32)), Bool.not(KMd.off.port(d, {SV2('q')}, (z + 1 : U32))))")}, {SV2('z')}, {WD(V2,'(z + 1 : U32)')}, Equal.sym(U32, {WD(V2,'(z + 1 : U32)')}, {SV2('z')}, {hface('z')}), hzq)),
        ind_q(r, {COMMON_ARGS}, z, hz2, and_r(RG.has(L2, q), RG.sub(r, L2), hqs)))

# each of L2 not facing itself after, and facing back what faces it
def ind_t(ys: List<&2, U32>, {COMMON_SIG}, +hys: {T('RG.sub(ys, L2)')}) -> {T(f'RG.px.tw(ys, {V2}, d, L2)')}:
  match ys:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      +hz2 = and_l(RG.has(L2, z), RG.sub(r, L2), hys)
{zpre('z')}      and_intro(KMd.off.port(d, {WD(V2,'(z + 1 : U32)')}, (z + 1 : U32)), RG.tw.q(L2, {WD(V2,'(z + 1 : U32)')}, z, {V2}, d) && RG.px.tw(r, {V2}, d, L2),
        ME.subst(U32, qq => {T('KMd.off.port(d, qq, (z + 1 : U32))')}, {SV2('z')}, {WD(V2,'(z + 1 : U32)')}, Equal.sym(U32, {WD(V2,'(z + 1 : U32)')}, {SV2('z')}, {hface('z')}),
          {via_sel('z','(z + 1 : U32)',zfz('z'))}),
        and_intro(RG.tw.q(L2, {WD(V2,'(z + 1 : U32)')}, z, {V2}, d), RG.px.tw(r, {V2}, d, L2), ind_q(L2, {COMMON_ARGS}, z, hz2, XP.sub_refl2(L2)),
          ind_t(r, {COMMON_ARGS}, and_r(RG.has(L2, z), RG.sub(r, L2), hys))))
'''
out=out.replace('XP.sub_refl2(L2)','sub_refl2(L2)')
pre=f'''
def tw.or(pp: Bool & Bool) -> Bool:
  (+a, +b) = pp
  Bool.or(a, Bool.not(b))

def pair_eq(+e1: Bool, +e2: Bool, +f1: Bool, +f2: Bool, +h1: {{e1 == f1 : Bool}}, +h2: {{e2 == f2 : Bool}}) -> {{(e1, e2) == (f1, f2) : Bool & Bool}}:
  %h1 : {{(e1, e2) == (_, f2) : Bool & Bool}}
  %h2 : {{(e1, e2) == (e1, _) : Bool & Bool}}
  {{==}}

def sub_cons2(ys: List<&2, U32>, +z: U32, +M: List<&2, U32>, +h: {T('RG.sub(ys, M)')}) -> {T('RG.sub(ys, Con{z, M})')}:
  match ys:
    case Nil{{}}:
      {{==}}
    case Con{{+m, +t}}:
      and_intro(RG.has(Con{{z, M}}, m), RG.sub(t, Con{{z, M}}), XP.or_t_r(U32.is_eq(z, m), RG.has(M, m), and_l(RG.has(M, m), RG.sub(t, M), h)), sub_cons2(t, z, M, and_r(RG.has(M, m), RG.sub(t, M), h)))

def sub_refl2(ys: List<&2, U32>) -> {T('RG.sub(ys, ys)')}:
  match ys:
    case Nil{{}}:
      {{==}}
    case Con{{+m, +t}}:
      and_intro(RG.has(Con{{m, t}}, m), RG.sub(t, Con{{m, t}}), XP.or_t_l(U32.is_eq(m, m), RG.has(t, m), XP.is_eq_self(m)), sub_cons2(t, m, t, sub_refl2(t)))
'''
k=out.index('\n# the facts of a live node z of L2 before the link')
out=out[:k]+pre+out[k:]
# pair_eq usage: pass the four Bools then the equations
out=out.replace(f"pair_eq({opsel('z','(q + 1 : U32)')}, {opsel('q','(z + 1 : U32)')})",
  f"pair_eq(KMd.off.port(d, {SV2('z')}, (q + 1 : U32)), KMd.off.port(d, {SV2('q')}, (z + 1 : U32)), sel3({BZ('z')}, {AZ('z')}, {PF('z','q')}, {BZ('q')}, {AZ('q')}), sel3({BZ('q')}, {AZ('q')}, {PF('q','z')}, {BZ('z')}, {AZ('z')}), {opsel('z','(q + 1 : U32)')}, {opsel('q','(z + 1 : U32)')})")
# the assembly
G=lambda v: T(conj(TRI(v)))
LXW=lambda A: f"KMd.words(P.link_xx(P.H{{KM.MG{{{A}}}, a}}, u, w))"
out+=f'''
def ll.k1({COMMON_SIG.replace('+t1: LAT.Tree<U32>, ','').replace(f'+e1: {{{A1} == {LK1} : Array<U32>}}, ','').replace(f'+hft1: {{AD.full(U32, {A1}, d) == True{{}} : Bool}}, ','')},
  -w1: Array<U32>, +hw1: {{w1 == {LK1} : Array<U32>}}, hf1: {{AD.full(U32, w1, d) == True{{}} : Bool}}, m1: LAT.Mirror(U32, w1)) -> {G('AD.view(U32, lk(sw, w1, w, u))')}:
  (+t1, +e0) = m1
  +hft1 = LAP.full_t(U32, w1, t1, d, e0, hf1)
  +e1 = Equal.trans(Array<U32>, {A1}, w1, {LK1}, e0, hw1)
  %e0 : {G('AD.view(U32, lk(sw, _, w, u))')}
  and_intro({TRI(V2)[0]}, {conj(TRI(V2)[1:])}, ind_f(L2, {COMMON_ARGS}, sub_refl2(L2)),
    and_intro({TRI(V2)[1]}, {TRI(V2)[2]}, ind_o(L2, {COMMON_ARGS}, sub_refl2(L2)), ind_t(L2, {COMMON_ARGS}, sub_refl2(L2))))
'''
SIG0=COMMON_SIG.replace('+t1: LAT.Tree<U32>, ','').replace(f'+e1: {{{A1} == {LK1} : Array<U32>}}, ','').replace(f'+hft1: {{AD.full(U32, {A1}, d) == True{{}} : Bool}}, ','').replace('+su: Bool, +sw: Bool,\n  ','\n  ').replace('+hsu: {P.is_static(u) == su : Bool}, +hsw: {P.is_static(w) == sw : Bool}, ','')
ARG1=', '.join(a for a in COMMON_ARGS.split(', ') if a not in ('t1','e1','hft1'))
LKU=f'lk(P.is_static(u), {A0}, u, w)'
out+=f'''
def ll.k0({SIG0}, -a: Array<V.Val>) -> {G(f'AD.view(U32, {LXW(A0)})')}:
  %Equal.sym(P.H, P.link.to(P.is_static(u), P.H{{KM.MG{{{A0}}}, a}}, u, w), P.H{{KM.MG{{{LKU}}}, a}}, lt_eq(P.is_static(u), {A0}, a, u, w)) :
    {G('AD.view(U32, KMd.words(P.link.to(P.is_static(w), _, w, u)))')}
  %Equal.sym(P.H, P.link.to(P.is_static(w), P.H{{KM.MG{{{LKU}}}, a}}, w, u), P.H{{KM.MG{{lk(P.is_static(w), {LKU}, w, u)}}, a}}, lt_eq(P.is_static(w), {LKU}, a, w, u)) :
    {G('AD.view(U32, KMd.words(_))')}
  ll.k1({ARG1.replace('su, sw, ','P.is_static(u), P.is_static(w), ').replace('hsu, hsw, ','{==}, {==}, ')}, {LKU}, {{==}}, lk_full(P.is_static(u), {A0}, d, u, w, hft), LAT.mirror(U32, {LKU}))
'''
LW=lambda w_: f"KMd.words(P.link_xx(P.H{{KM.MG{{{w_}}}, a}}, KMd.word(AD.view(U32, {w_}), d, (x + 1 : U32)), KMd.word(AD.view(U32, {w_}), d, (y + 1 : U32))))"
GW=lambda w_: G(f'AD.view(U32, {LW(w_)})')
PRE_W=lambda q: [f'RG.faces(L, AD.view(U32, {q}), d, L)', f'RG.px.off(L, AD.view(U32, {q}), d, L, N)', f'RG.px.tw(L, AD.view(U32, {q}), d, L)']
out+=f'''
def ll.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hLN: {T('RG.sub(L, N)')}, +hx: {T('RG.has(L, x)')}, +hy: {T('RG.has(L, y)')},
  +hxy: {NE('x','y')}, +hs1: {T('RG.sub(L2, L)')}, +hs2: {T('RG.sub(L, Con{x, Con{y, L2}})')}, +hx2: {F_('RG.has(L2, x)')}, +hy2: {F_('RG.has(L2, y)')},
  hF: {T(PRE_W('w')[0])}, hO: {T(PRE_W('w')[1])}, hT: {T(PRE_W('w')[2])}, m: LAT.Mirror(U32, w)) -> {GW('w')}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, {A0}, w, e)
  %e : {GW('_')}
  ll.k0(t0, d, L, L2, N, x, y, {FW('x')}, {FW('y')}, hft, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, {{==}}, {{==}},
    LAB.subst(Array<U32>, q => {T(PRE_W('q')[0])}, w, {A0}, ew, hF), LAB.subst(Array<U32>, q => {T(PRE_W('q')[1])}, w, {A0}, ew, hO), LAB.subst(Array<U32>, q => {T(PRE_W('q')[2])}, w, {A0}, ew, hT), a)

def Laws.link_live(w, a, d, L, L2, N, x, y, hf, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, hF, hO, hT):
  ll.m(w, a, d, L, L2, N, x, y, hf, hd32, hN, hLN, hx, hy, hxy, hs1, hs2, hx2, hy2, hF, hO, hT, LAT.mirror(U32, w))

def main() -> U32:
  0
'''
out=out.replace('import ./INDEX_PROOF.bend as XP\n','import ./INDEX_PROOF.bend as XP\nimport ./index_model.bend as IMd\n')
open('glam/JOIN_PROOF.bend','w').write(out)
print('written', len(out.splitlines()))
