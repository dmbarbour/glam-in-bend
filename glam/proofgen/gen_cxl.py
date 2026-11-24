# authoring aid: the served cursor's lookup kept through a copy's
# crossings (cxl.k, cxl.go, cxl.m; glam/PROOF.bend), crf.go's fold with a
# lookup for its goal, each step by look_del_other or look_put_other;
# and the model's RG.far.off (glam/ring_model.bend). Run by regen.sh
# after gen_jnk.py (cells-freeze.sharing.cursors.index.ring.premises.lookups)
import os
exec(open('glam/proofgen/gen_fold.py').read().split("out=f'''")[0])
nsJ={}
exec(open('glam/proofgen/gen_j1.py').read().split("open('glam/proofgen/j1_part1.txt','w')")[0], nsJ)
PXOK=nsJ['PXOK']; proj=nsJ['proj']
MB_='Maybe<&2, U32>'
GX=lambda S: f'{{IM.ix.look(RG.cxs.I({S}), k) == Some{{nc}} : {MB_}}}'
C3=PXOK(f'AD.view(U32, {TW})', 'I', f'Con{{{X}, {PSR}}}', 'L', F0E, 'N')
out=f'''
# The served cursor's lookup kept through a copy's crossings
# (cells-freeze.sharing.cursors.index.ring.premises.lookups): a join
# removes the cursor at another key, an insert puts at a key absent, so
# that neither moves a cursor found at a key no crossing looks for
def isnone_none(+m: {MB_}, +h: {{RG.isnone(m) == True{{}} : Bool}}) -> {{m == None{{}} : {MB_}}}:
  match m:
    case Some{{+y}}:
      Empty.absurd({{Some{{y}} == None{{}} : {MB_}}}, MB.false_ne_true()(h))
    case None{{}}:
      {{==}}

def src_ne.k(+e: Bool, +I: IM.Ix, +src: U32, +k: U32, +nc: U32, +he: {{U32.is_eq(src, k) == e : Bool}}, +ha: {{IM.ix.look(I, src) == None{{}} : {MB_}}},
  +hk: {{IM.ix.look(I, k) == Some{{nc}} : {MB_}}}) -> {{e == False{{}} : Bool}}:
  match e:
    case True{{}}:
      Empty.absurd({{True{{}} == False{{}} : Bool}}, MB.false_ne_true()(Equal.cong({MB_}, Bool, m => XP.is_some(m), None{{}}, Some{{nc}},
        Equal.trans({MB_}, None{{}}, IM.ix.look(I, k), Some{{nc}}, Equal.sym({MB_}, IM.ix.look(I, k), None{{}}, ME.subst(U32, z => {{IM.ix.look(I, z) == None{{}} : {MB_}}}, src, k, MS.u32_eq_of_is_eq(src, k, he), ha)), hk))))
    case False{{}}:
      {{==}}

def src_ne(+I: IM.Ix, +src: U32, +k: U32, +nc: U32, +ha: {{IM.ix.look(I, src) == None{{}} : {MB_}}}, +hk: {{IM.ix.look(I, k) == Some{{nc}} : {MB_}}}) ->
  {{U32.is_eq(src, k) == False{{}} : Bool}}:
  src_ne.k(U32.is_eq(src, k), I, src, k, nc, {{==}}, ha, hk)

# one crossing: the cursor found at k found there after
def cxl.k(+m: {MB_}, +I: IM.Ix, +s: U32, +d: Nat, +x: U32, +src: U32, +b: U32, +far: U32, +k: U32, +nc: U32, +he: {{IM.ix.look(I, far) == m : {MB_}}},
  +hi: {{IM.ix.inv(I) == True{{}} : Bool}}, +hl: {{IM.ix.lay(I, s, d) == True{{}} : Bool}}, +hab: {{RG.cx.ab(m, I, src) == True{{}} : Bool}},
  +hk: {{IM.ix.look(I, k) == Some{{nc}} : {MB_}}}, +hfk: {{U32.is_eq(far, k) == False{{}} : Bool}}) -> {{IM.ix.look(RG.cx.I(m, I, x, src, b, far), k) == Some{{nc}} : {MB_}}}:
  match m:
    case Some{{+y}}:
      Equal.trans({MB_}, IM.ix.look(IM.ix.del(I, y, far), k), IM.ix.look(I, k), Some{{nc}}, XL.look_del_other(I, s, y, far, k, d, hi, hl, he, hfk), hk)
    case None{{}}:
      +ha = isnone_none(IM.ix.look(I, src), hab)
      Equal.trans({MB_}, IM.ix.look(IM.ix.put(I, x, src, b), k), IM.ix.look(I, k), Some{{nc}}, XL.look_put_other(I, x, src, b, k, hi, ha, src_ne(I, src, k, nc, ha, hk)), hk)

# the crossings in turn: the cursor found at k, a key no crossing's far
# end is, found there after them (crf.go's fold, each step's invariant
# giving the index's own)
def cxl.go(cl: List<&2, R.FzC>, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +s: U32, +I: IM.Ix, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, hfm: {{AD.full(U32, map, dm) == True{{}} : Bool}}, +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}},
  +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, hp: {HPX('AD.view(U32, w)', 'RG.pls(cl, AD.view(U32, map), dm)')}, hok: {T('RG.cxs.ok(cl, AD.view(U32, map), dm, I, F)')},
  +k: U32, +nc: U32, +hk: {{IM.ix.look(I, k) == Some{{nc}} : {MB_}}}, +hu: {T('RG.far.off(cl, k)')},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) -> {GX(S0('cl','AD.view(U32, map)'))}:
  match cl:
    case Nil{{}}:
      hk
    case Con{{c, +rest}}:
      match c:
        case R.FzC{{+at, +src, +neg, +far}}:
          (+tw, +ew) = mw
          (+ta, +ea) = ma
          (+tm, +em) = mm
          +hft = LAP.full_t(U32, w, tw, d, ew, hf)
          +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
          +ePL = ME.subst({MB_}, q => {{RG.pl.of(q) == {X} : U32}}, Some{{{X}}}, List.get(&2, U32, AD.view(U32, {TM}), AD.slot(at, dm)), LA.get_view(U32, {TM}, dm, at, hfmt, hdm), {{==}})
          +hpa = LAB.subst(Array<U32>, qq => {HPX('AD.view(U32, qq)', 'Con{'+XMq('map')+', RG.pls(rest, AD.view(U32, map), dm)}')}, w, {TW}, Equal.sym(Array<U32>, {TW}, w, ew), hp)
          +hpb = LAB.subst(Array<U32>, qq => {HPX(f'AD.view(U32, {TW})', 'Con{'+XMq('qq')+', RG.pls(rest, AD.view(U32, qq), dm)}')}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hpa)
          +hp3 = ME.subst(U32, q => {HPX(f'AD.view(U32, {TW})', 'Con{q, '+PSR+'}')}, {XM}, {X}, ePL, hpb)
          +hoa = LAB.subst(Array<U32>, qq => {T(f'({AB} && {RM}) && '+OKR('AD.view(U32, qq)', XMq('qq')))}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hok)
          +hob = ME.subst(U32, q => {T(f'({AB} && {RM}) && '+OKR(f'AD.view(U32, {TM})', 'q'))}, {XM}, {X}, ePL, hoa)
          +hab = and_l({AB}, {RM}, and_l({AB} && {RM}, {OKR(f'AD.view(U32, {TM})', X)}, hob))
          +hrm = and_r({AB}, {RM}, and_l({AB} && {RM}, {OKR(f'AD.view(U32, {TM})', X)}, hob))
          +hokr = and_r({AB} && {RM}, {OKR(f'AD.view(U32, {TM})', X)}, hob)
          +hpF = ME.subst(List<&2, U32>, q => {T(f'RG.px.ok(AD.view(U32, {TW}), d, s, I, Con{{{X}, {PSR}}}, L, q, N)')}, F, {F0E}, Equal.sym(List<&2, U32>, {F0E}, F, cx_f0({M}, I, F, hrm)), hp3)
          +hC = cxp.t(tw, ta, d, s, I, {PSR}, L, {TL}, N, {X}, src, neg, far, {HD}, hft, hd32, hN, hB, hpF, hab)
          +hfk = MB.eq_false_of_not_eq_true(U32.is_eq(far, k), and_l(Bool.not(U32.is_eq(far, k)), RG.far.off(rest, k), hu))
          +hur = and_r(Bool.not(U32.is_eq(far, k)), RG.far.off(rest, k), hu)
          +hk1 = cxl.k({M}, I, s, d, {X}, src, {HD}, far, k, nc, {{==}}, {proj(C3,1,'hpF')}, {proj(C3,2,'hpF')}, hab, hk, hfk)
          %em : {GX(S0(CL,'AD.view(U32, _)'))}
          %Equal.sym(U32, {XM}, {X}, ePL) : {GX(SR('_'))}
          cxl.go(rest, RG.words({H1}), KMd.vals({H1}), {TM}, d, dm, s, {I1(X)}, {L1(X)}, {F1(X)}, N, and_r({PX1}, {FU1}, hC), hd32, hfmt, hdm, hN, hB, and_l({PX1}, {FU1}, hC), hokr,
            k, nc, hk1, hur, LAT.mirror(U32, RG.words({H1})), LAT.mirror(V.Val, KMd.vals({H1})), LAT.mirror(U32, {TM}))

def cxl.m(-w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +s: U32, +I: IM.Ix, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +cs: List<&2, R.FzC>,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, hfm: {{AD.full(U32, map, dm) == True{{}} : Bool}}, +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}},
  +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, hp: {HPX('AD.view(U32, w)', 'RG.pls(cs, AD.view(U32, map), dm)')}, hok: {T('RG.cxs.ok(cs, AD.view(U32, map), dm, I, F)')},
  +k: U32, +nc: U32, +hk: {{IM.ix.look(I, k) == Some{{nc}} : {MB_}}}, +hu: {T('RG.far.off(cs, k)')},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) -> {GX(S0('cs','AD.view(U32, map)'))}:
  (+tw, +ew) = mw
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, w, tw, d, ew, hf)
  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
  +hpa = LAB.subst(Array<U32>, qq => {HPX('AD.view(U32, qq)', 'RG.pls(cs, AD.view(U32, map), dm)')}, w, {TW}, Equal.sym(Array<U32>, {TW}, w, ew), hp)
  +hpb = LAB.subst(Array<U32>, qq => {HPX(f'AD.view(U32, {TW})', 'RG.pls(cs, AD.view(U32, qq), dm)')}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hpa)
  +hoT = LAB.subst(Array<U32>, qq => {T('RG.cxs.ok(cs, AD.view(U32, qq), dm, I, F)')}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hok)
  %em : {GX(S0('cs','AD.view(U32, _)'))}
  cxl.go(cs, {TW}, {TA}, {TM}, d, dm, s, I, L, F, N, hft, hd32, hfmt, hdm, hN, hB, hpb, hoT, k, nc, hk, hu, LAT.mirror(U32, {TW}), LAT.mirror(V.Val, {TA}), LAT.mirror(U32, {TM}))

def Laws.crossings_look(w, a, map, d, dm, s, I, L, F, N, cs, k, nc, hf, hd32, hfm, hdm, hN, hB, hp, hok, hk, hu):
  cxl.m(w, a, map, d, dm, s, I, L, F, N, cs, hf, hd32, hfm, hdm, hN, hB, hp, hok, k, nc, hk, hu, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))
'''
FAR='''
# no crossing of cs looks for key k at its far end: the served cursor's
# key, which no crossing then joins (serve_ring_exact)
def far.off(cs: List<&2, R.FzC>, +k: U32) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{f, r}:
      match f:
        case R.FzC{+at, +src, neg, +far}:
          Bool.not(U32.is_eq(far, k)) && far.off(r, k)
'''
if os.environ.get('CXL_ONLY'):
    open('glam/proofgen/kp/sec.txt','w').write(out)
    print('cxl', len(out.splitlines()))
else:
    rp='glam/ring_model.bend'; r=open(rp).read()
    if 'def far.off(' not in r:
        i=r.index("# A copy's crossings over the index (R.crossings; crossings_pend): each\n")
        r=r[:i]+FAR.lstrip('\n')+'\n'+r[i:]
        open(rp,'w').write(r)
    p='glam/PROOF.bend'; s=open(p).read()
    assert 'def cxl.go(' not in s
    s=s.rstrip('\n')+'\n'+out
    open(p,'w').write(s)
    print('cxl', len(out.splitlines()))
