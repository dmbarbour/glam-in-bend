# authoring aid: leave_pend over the index (glam/PROOF.bend), from the
# join's generators (gen_j1*.py): the live list without the cursor y alone,
# a port p linked in its place, one free
import re, os
exec(open('glam/proofgen/gen_j1.py').read().split("open('glam/proofgen/j1_part1.txt','w')")[0])
L2='RG.without(L, y)'      # TRI and frstep read it
xp=open('glam/INDEX_PROOF.bend').read()
A0='LAT.fromT(U32, t0)'; AA='LAT.fromT(V.Val, ta)'; V0=f'AD.view(U32, {A0})'
I0='IM.Has{t}'; Id='IM.ix.del(IM.Has{t}, y, k)'; Pa='IM.ix.par(IM.Has{t}, y, k)'
FP=lambda Pl: f'Con{{y, {Pl}}}'
H0=f'P.H{{KM.MG{{{A0}}}, {AA}}}'
WW=WD(V0,'(y + 1 : U32)')
LK1=f'JP.lk(P.is_static(p), {A0}, p, {WW})'; LK2=f'JP.lk(P.is_static({WW}), {LK1}, {WW}, p)'
NOD=lambda I: f'IM.ix.nodes({I})'; BR=lambda I: f'IM.ix.branches({I})'; LV=lambda I: f'IM.ix.leaves({I})'
MBt=lambda J: [f'IM.ix.inv({J})', f'IM.ix.lay({J}, s, d)', f'RG.sub(Con{{s, {LV(J)}}}, {L2})', f'RG.sub(ps, {L2})', f'RG.none.in(ps, Con{{s, {NOD(J)}}})', 'RG.distinct(ps)',
  f'RG.none.in({L2}, {BR(J)})', f'RG.sub({L2}, N)', f'RG.sub({NOD(J)}, N)']
PLFt=lambda J,Pl: [f'RG.distinct({FP(Pl)})', f'RG.none.in({FP(Pl)}, Con{{s, {NOD(J)}}})', f'RG.none.in({FP(Pl)}, {L2})', f'RG.sub({FP(Pl)}, N)',
  f'IM.fl.ok({Pl}, d)', f'IM.fl.sep({Pl}, d, y)']
OFX=lambda J,j: f'IM.ix.offr({J}, s, d, {j})'
ONS=lambda j: f'ones({L2}, d, {j})'
QFt=lambda J: ['IM.nd.ok(y, d)', OFX(J,'y'), OFX(J,'(y + 1 : U32)'), OFX(J,'P.at_fh()'), ONS('y'), ONS('(y + 1 : U32)'), ONS('P.at_fh()')]
out=f'''
# The pending placeholders over the index: a leave
# ================================================
#
# cells-freeze.sharing.cursors.index.ring.leave: leave_pend as join1_pend,
# its port p linked in the cursor y's place (JL.link_leave), y removed
# from the index and freed alone.

def sub_w1(K: List<&2, U32>, +L: List<&2, U32>, +y: U32, +hs: {T('RG.sub(K, L)')}, +hy: {F_('RG.has(K, y)')}) -> {T('RG.sub(K, RG.without(L, y))')}:
  match K:
    case Nil{{}}:
      {{==}}
    case Con{{+m, +r}}:
      MB.and_eq_true(RG.has(RG.without(L, y), m), RG.sub(r, RG.without(L, y)), has_without(L, y, m, ueq_ne(m, y, or_false_l(U32.is_eq(m, y), RG.has(r, y), hy)), MB.eq_true_of_and_left(RG.has(L, m), RG.sub(r, L), hs)),
        sub_w1(r, L, y, MB.eq_true_of_and_right(RG.has(L, m), RG.sub(r, L), hs), or_false_r(U32.is_eq(m, y), RG.has(r, y), hy)))

def sub_back1.k(+ey: Bool, +z: U32, +L: List<&2, U32>, +y: U32, +hey: {{U32.is_eq(y, z) == ey : Bool}}, +hz: {T('RG.has(L, z)')}) -> {T('RG.has(Con{y, RG.without(L, y)}, z)')}:
  match ey:
    case True{{}}:
      %Equal.sym(Bool, U32.is_eq(y, z), True{{}}, hey) : {T('Bool.or(_, RG.has(RG.without(L, y), z))')}
      {{==}}
    case False{{}}:
      has_cons(y, RG.without(L, y), z, has_without(L, y, z, hey, hz))

def sub_back1(K: List<&2, U32>, +L: List<&2, U32>, +y: U32, +hK: {T('RG.sub(K, L)')}) -> {T('RG.sub(K, Con{y, RG.without(L, y)})')}:
  match K:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      and_intro(RG.has(Con{{y, RG.without(L, y)}}, z), RG.sub(r, Con{{y, RG.without(L, y)}}), sub_back1.k(U32.is_eq(y, z), z, L, y, {{==}}, and_l(RG.has(L, z), RG.sub(r, L), hK)),
        sub_back1(r, L, y, and_r(RG.has(L, z), RG.sub(r, L), hK)))
'''
# ---- the free list's first nodes after a leave: the removal's parent, if any ----
def lpl_body(pp):
    if pp:
        Pl=f'Con{{{pp}, F}}'
        lets=f'''      +hpb = XL.par_branch({I0}, y, k, {pp}, he)
      +hpn = sub_has(IM.tr.branches(t), IM.tr.nodes(t), {pp}, br_sub(t), hpb)
      +hpN = sub_has(IM.tr.nodes(t), N, {pp}, hIN, hpn)
      +hpL = none_notin(L, IM.tr.branches(t), {pp}, hbr, hpb)
      +hpF = none_notin(F, Con{{s, IM.tr.nodes(t)}}, {pp}, hfn, has_cons(s, IM.tr.nodes(t), {pp}, hpn))
      +hpy = nhas(IM.tr.branches(t), {pp}, y, hpb, hyB)
      +hps = nhas(IM.tr.nodes(t), {pp}, s, hpn, hst)
      +hDA = ME.subst(Maybe<&2, U32>, mm => {T(f"RG.none.in(IM.mb.cons(mm, [y]), {NOD(Id)})")}, {Pa}, Some{{{pp}}}, he, XL.del_absent({I0}, s, d, y, k, hlay, hy))
      +hpD = MB.eq_false_of_not_eq_true(RG.has({NOD(Id)}, {pp}), and_l(Bool.not(RG.has({NOD(Id)}, {pp})), RG.none.in([y], {NOD(Id)}), hDA))
'''
    else:
        Pl='F'
        lets=f'''      +hDA = ME.subst(Maybe<&2, U32>, mm => {T(f"RG.none.in(IM.mb.cons(mm, [y]), {NOD(Id)})")}, {Pa}, None{{}}, he, XL.del_absent({I0}, s, d, y, k, hlay, hy))
'''
    lets+=f'''      +hyD = none_last({'Some{'+pp+'}' if pp else 'None{}'}, y, {NOD(Id)}, hDA)
      +hSD = and_intro(RG.has(Con{{s, IM.tr.nodes(t)}}, s), RG.sub({NOD(Id)}, Con{{s, IM.tr.nodes(t)}}), has_head(s, IM.tr.nodes(t)), sub_cons_r({NOD(Id)}, s, IM.tr.nodes(t), XL.del_sub({I0}, y, k, IM.tr.nodes(t), sub_refl(IM.tr.nodes(t)))))
'''
    M=f'Con{{s, {NOD(Id)}}}'
    def nin(a, hs_a, hd_a): return f'not_t(RG.has({M}, {a}), or_ff(U32.is_eq(s, {a}), RG.has({NOD(Id)}, {a}), {hs_a}, {hd_a}))'
    def ninL(a, h): return f'not_t(RG.has({L2}, {a}), {h})'
    ys=['y']+([pp] if pp else [])
    def none_chain(elems, Mexp, nots, tail):
        if not elems: return tail
        a=elems[0]; rest=elems[1:]
        restlist = ('Con{'+', Con{'.join(rest)+', F'+'}'*len(rest)) if rest else 'F'
        return f'and_intro(Bool.not(RG.has({Mexp}, {a})), RG.none.in({restlist}, {Mexp}), {nots[0]}, {none_chain(rest, Mexp, nots[1:], tail)})'
    nM=none_chain(ys, M, [nin('y','ueq_ne(y, s, hys)','hyD')]+([nin(pp,f'ueq_ne({pp}, s, hps)','hpD')] if pp else []), f'none_sub(F, Con{{s, IM.tr.nodes(t)}}, {M}, hfn, hSD)')
    nL=none_chain(ys, L2, [ninL('y','hy2')]+([ninL(pp, f'notin_sub({L2}, L, {pp}, hs1, hpL)')] if pp else []), f'none_sub(F, L, {L2}, hFL, hs1)')
    def sub_chain(elems, hasp, tail):
        if not elems: return tail
        a=elems[0]; rest=elems[1:]
        restlist = ('Con{'+', Con{'.join(rest)+', F'+'}'*len(rest)) if rest else 'F'
        return f'and_intro(RG.has(N, {a}), RG.sub({restlist}, N), {hasp[0]}, {sub_chain(rest, hasp[1:], tail)})'
    sN=sub_chain(ys, ['hyN']+(['hpN'] if pp else []), 'hFN')
    sNp=sub_chain(ys[1:], (['hpN'] if pp else []), 'hFN')
    if pp:
        hyP=f'or_ff(U32.is_eq({pp}, y), RG.has(F, y), hpy, hyF)'
        dist=f'and_intro(Bool.not(RG.has({Pl}, y)), RG.distinct({Pl}), not_t(RG.has({Pl}, y), {hyP}), and_intro(Bool.not(RG.has(F, {pp})), RG.distinct(F), not_t(RG.has(F, {pp}), hpF), hFd))'
    else:
        hyP='hyF'
        dist=f'and_intro(Bool.not(RG.has(F, y)), RG.distinct(F), not_t(RG.has(F, y), hyF), hFd)'
    PL=PLFt(Id,Pl)
    prfs=[dist, nM, nL, sN, f'flok_of({Pl}, N, d, hN, hB, {sNp})', f'flsep_of({Pl}, N, d, y, hN, {sNp}, hyN, {hyP})']
    return lets+f'      {intro(PL,prfs)}\n'
LPLS=f'''+t: IM.Tr, +d: Nat, +s: U32, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +y: U32, +k: U32,
  +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, +hbr: {T('RG.none.in(L, IM.tr.branches(t))')}, +hfn: {T('RG.none.in(F, Con{s, IM.tr.nodes(t)})')}, +hFL: {T('RG.none.in(F, L)')},
  +hFN: {T('RG.sub(F, N)')}, +hFd: {T('RG.distinct(F)')}, +hyF: {F_('RG.has(F, y)')}, +hyN: {T('RG.has(N, y)')},
  +hs1: {T(f'RG.sub({L2}, L)')}, +hy2: {F_(f'RG.has({L2}, y)')}, +hst: {F_('RG.has(IM.tr.nodes(t), s)')},
  +hyB: {F_('RG.has(IM.tr.branches(t), y)')}, +hIN: {T('RG.sub(IM.tr.nodes(t), N)')}, +hys: {NE('y','s')}, +hlay: {T(f'IM.ix.lay({I0}, s, d)')}, +hy: {{IM.ix.look({I0}, k) == Some{{y}} : Maybe<&2, U32>}}'''
out+=f'''
# what the free list's first nodes after a leave hold, the removal's parent m if any
def lpl(+m: Maybe<&2, U32>, {LPLS}, +he: {{{Pa} == m : Maybe<&2, U32>}}) -> {T(conj(PLFt(Id,'IM.mb.cons(m, F)')))}:
  match m:
    case Some{{+pp}}:
{lpl_body('pp')}    case None{{}}:
{lpl_body(None)}'''
# ---- the free, y's ----
GOAL=lambda v,J,Pl: T('(' + conj(PXOK(v,J,'ps',L2,FP(Pl),'N')) + ') && AD.full(U32, ' + v[len('AD.view(U32, '):-1] + ', d)')
FREEV=lambda w,r: f'AD.view(U32, KMd.words(P.free(P.H{{KM.MG{{{w}}}, {AA}}}, {r})))'
COMMON=f'''+J: IM.Ix, +Pl: List<&2, U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +N: List<&2, U32>, +y: U32,
  +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hM: {T(conj(MBt('J')))}, +hQ: {T(conj(QFt('J')))}, +hPL: {T(conj(PLFt('J','Pl')))}'''
CARGS='J, Pl, ta, d, s, ps, L, N, y, hd32, hN, hM, hQ, hPL'
QF=QFt('J'); MBL=MBt('J'); PLL=PLFt('J','Pl')
q=lambda i: proj(QF,i,'hQ'); mb=lambda i: proj(MBL,i,'hM'); pl=lambda i: proj(PLL,i,'hPL')
def base_eq(r, okp): return f"MS.u32_eq_of_is_eq(P.base({r}), {r}, and_l(U32.is_eq(P.base({r}), {r}), IM.ws.apart(KMd.nw({r}), d) && {OW(r,FH)}, {okp}))"
def to_base(pred, r, fact, hb): return f'ME.subst(U32, qq => {pred}, {r}, P.base({r}), Equal.sym(U32, P.base({r}), {r}, {hb}), {fact})'
A3='LAT.fromT(U32, t3)'
G2=GET(A3,FH); Hh='((y >> 2n : U32) + 1 : U32)'
B1=AS(A3,'P.base(y)','0'); B2=AS(B1,'(P.base(y) + 1 : U32)',G2); B3=AS(B2,FH,Hh)
f1=sfull(A3,'P.base(y)','0','hft3'); f2=sfull(B1,'(P.base(y) + 1 : U32)',G2,f1)
tri=frstep(A3,'P.base(y)','0','hft3','htr3T',to_base(T(f'ones({L2}, d, qq)'),'y',q(4),'hby'))
tri=frstep(B1,'(P.base(y) + 1 : U32)',G2,f1,tri,to_base(T(f'ones({L2}, d, (qq + 1 : U32))'),'y',q(5),'hby'))
tri=frstep(B2,FH,Hh,f2,tri,q(6))
V4=FREEV(A3,'y')
TRIy=f"ME.subst(P.H, hh => {T(conj(TRI('AD.view(U32, KMd.words(hh))')))}, P.H{{KM.MG{{{B3}}}, {AA}}}, P.free(P.H{{KM.MG{{{A3}}}, {AA}}}, y), Equal.sym(P.H, P.free(P.H{{KM.MG{{{A3}}}, {AA}}}, y), P.H{{KM.MG{{{B3}}}, {AA}}}, heqy), htry)"
FIN=PXOK(V4,'J','ps',L2,FP('Pl'),'N')
fin_prfs=['hfry', mb(0), mb(1), mb(2), mb(3), mb(4), mb(5), mb(6), 'hfcy', pl(0), pl(1), pl(2), mb(7), pl(3), mb(8),
  proj(TRI(V4),0,'htrF'), proj(TRI(V4),1,'htrF'), proj(TRI(V4),2,'htrF')]
SUBT=lambda pred,w,t_,e: f'LAB.subst(Array<U32>, qq => {pred}, {w}, LAT.fromT(U32, {t_}), {e}, '
out+=f'''
# the free, y's, and the invariant after
def lfr({COMMON}, -w3: Array<U32>, hf3: {{AD.full(U32, w3, d) == True{{}} : Bool}}, hr3: {T('IM.ix.real(AD.view(U32, w3), d, s, J)')},
  hc3: {T('KMd.chain(Pl, AD.view(U32, w3), d, KMd.word(AD.view(U32, w3), d, P.at_fh()))')}, htr3: {T(conj(TRI('AD.view(U32, w3)')))}, m3: LAT.Mirror(U32, w3)) ->
  {GOAL(f'AD.view(U32, KMd.words(P.free(P.H{{KM.MG{{w3}}, {AA}}}, y)))','J','Pl')}:
  (+t3, +e3) = m3
  +hft3 = LAP.full_t(U32, w3, t3, d, e3, hf3)
  +ew3 = Equal.sym(Array<U32>, {A3}, w3, e3)
  +hr3T = {SUBT(T('IM.ix.real(AD.view(U32, qq), d, s, J)'),'w3','t3','ew3')}hr3)
  +hc3T = {SUBT(T('KMd.chain(Pl, AD.view(U32, qq), d, KMd.word(AD.view(U32, qq), d, P.at_fh()))'),'w3','t3','ew3')}hc3)
  +htr3T = {SUBT(T(conj(TRI('AD.view(U32, qq)'))),'w3','t3','ew3')}htr3)
  +hby = {base_eq('y', q(0))}
  +hfry = XL.free_real({A3}, {AA}, d, s, J, y, hft3, hd32, {to_base(T(OFX('J','qq')),'y',q(1),'hby')}, {to_base(T(OFX('J','(qq + 1 : U32)')),'y',q(2),'hby')}, {q(3)}, hr3T)
  +hfcy = XL.free_push({A3}, {AA}, d, y, Pl, hft3, hd32, {q(0)}, {pl(4)}, {pl(5)}, hc3T)
  +hffy = XL.free_full({A3}, {AA}, d, y, hft3)
  +heqy = XP.fh1(t3, {AA}, y)
  +htry = {tri}
  +htrF = {TRIy}
  %e3 : {GOAL(f'AD.view(U32, KMd.words(P.free(P.H{{KM.MG{{_}}, {AA}}}, y)))','J','Pl')}
  and_intro({conj(FIN)}, AD.full(U32, KMd.words(P.free(P.H{{KM.MG{{{A3}}}, {AA}}}, y)), d), {intro(FIN, fin_prfs)}, hffy)
'''
if os.environ.get('LV_PART')=='1':
    open('glam/proofgen/lv_pend1.txt','w').write(out)
    print('part1', len(out.splitlines()))
# ---- part 2: the removal by shape, the case, the entry ----
A1='LAT.fromT(U32, t1)'
PLX=f'IM.mb.cons({Pa}, F)'
LRM_SIG=f'''+t: IM.Tr, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +y: U32, +k: U32,
  +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hy: {{IM.ix.look({I0}, k) == Some{{y}} : Maybe<&2, U32>}},
  +hinv: {T(f'IM.ix.inv({I0})')}, +hlay: {T(f'IM.ix.lay({I0}, s, d)')}, +hM: {T(conj(MBt(Id)))}, +hQ: {T(conj(QFt(Id)))}, +hPL: {T(conj(PLFt(Id,PLX)))},
  +hL2N: {T(f'RG.sub({L2}, N)')}, +hsN: {T('RG.has(N, s)')}, +hIN: {T(f'RG.sub({NOD(I0)}, N)')}, +hL2b: {T(f'RG.none.in({L2}, {BR(I0)})')},
  +hFok: {T('IM.fl.ok(F, d)')}, +hFs: {T(f'IM.ix.flsep({I0}, s, d, F)')},
  -w1: Array<U32>, hf1: {{AD.full(U32, w1, d) == True{{}} : Bool}}, hr1: {T(f'IM.ix.real(AD.view(U32, w1), d, s, {I0})')},
  hc1: {T('KMd.chain(F, AD.view(U32, w1), d, KMd.word(AD.view(U32, w1), d, P.at_fh()))')}, htr1: {T(conj(TRI('AD.view(U32, w1)')))}, m1: LAT.Mirror(U32, w1)'''
LRM_ARGS='t0, ta, d, s, ps, L, F, N, y, k, hd32, hN, hy, hinv, hlay, hM, hQ, hPL, hL2N, hsN, hIN, hL2b, hFok, hFs'
GOALR=lambda w,I: GOAL(f'AD.view(U32, KMd.words(P.free(X.ix.remove(P.H{{KM.MG{{{w}}}, {AA}}}, s, y), y)))', f'IM.ix.del({I}, y, k)', f'IM.mb.cons(IM.ix.par({I}, y, k), F)')
def rm_case(shape):
    if shape=='lf':
        TT='IM.Lf{y0, ky}'; tparam='+y0: U32, +ky: U32'
    else:
        TT='IM.Br{b, i, l, r}'; tparam='+b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr'
    sig=LRM_SIG.replace('+t: IM.Tr, ',tparam+', ').replace('IM.Has{t}','IM.Has{'+TT+'}').replace('IM.tr.nodes(t)','IM.tr.nodes('+TT+')')
    I=f'IM.Has{{{TT}}}'
    REMW=lambda w: f'X.ix.remove(P.H{{KM.MG{{{w}}}, {AA}}}, s, y)'
    lets=f'''  (+t1, +e1) = m1
  +hft1 = LAP.full_t(U32, w1, t1, d, e1, hf1)
  +ew1 = Equal.sym(Array<U32>, {A1}, w1, e1)
  +hr1T = LAB.subst(Array<U32>, qq => {T(f'IM.ix.real(AD.view(U32, qq), d, s, {I})')}, w1, {A1}, ew1, hr1)
  +hc1T = LAB.subst(Array<U32>, qq => {T('KMd.chain(F, AD.view(U32, qq), d, KMd.word(AD.view(U32, qq), d, P.at_fh()))')}, w1, {A1}, ew1, hc1)
  +htr1T = LAB.subst(Array<U32>, qq => {T(conj(TRI('AD.view(U32, qq)')))}, w1, {A1}, ew1, htr1)
  +hreT1 = and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, {A1}), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, {A1}), d, {TT}, KMd.word(AD.view(U32, {A1}), d, (s + 3 : U32)), s), hr1T)
  +hre2L = XL.remove_tree({A1}, {AA}, d, s, {I}, y, k, hft1, hd32, hr1T, hinv, hlay, hy)
  +hc2L = XL.remove_free({A1}, {AA}, d, s, {I}, y, k, F, hft1, hd32, hr1T, hinv, hlay, hy, hFok, hFs, hc1T)
  +hf2L = XL.remove_full({A1}, {AA}, d, s, {I}, y, k, hft1, hd32, hr1T, hinv, hlay, hy)
'''
    if shape=='lf':
        AR=AS(A1,'(s + 3 : U32)','s')
        eqR=f'XP.rm.heap.lf(t1, {AA}, d, s, y, k, y0, ky, hft1, hd32, hreT1, hy)'
        W_=[('(s + 3 : U32)','s',f'ones_p3({L2}, N, d, s, hL2N, hN, hsN)')]
        hlets=''
    else:
        TB=TT
        CUTB=f'IM.tr.cutat({TB}, y, k, (s + 3 : U32))'
        LOB=f'XP.cut.lo({CUTB})'; SIB=f'XP.cut.si({CUTB})'; PAB=f'XP.cut.pa({CUTB})'
        B1_=AS(A1,LOB,SIB); G=GET(B1_,FH); AR=AS(AS(AS(B1_,PAB,'0'),f'({PAB} + 1 : U32)',G),FH,f'(({PAB} >> 2n : U32) + 1 : U32)')
        L6=['IM.nd.ok(b, d)','IM.tr.offn(l, d, b)','IM.tr.offn(r, d, b)','IM.tr.apart(l, r, d)','IM.tr.lay(l, d)','IM.tr.lay(r, d)']
        hl3=['IM.nd.ok(s, d)', f'IM.tr.offn({TB}, d, s)', f'IM.tr.lay({TB}, d)']
        hlets=f'''  +hoks = {proj(hl3,0,'hlay')}
  +hoffT = {proj(hl3,1,'hlay')}
  +hlayT = {proj(hl3,2,'hlay')}
  +hneT = XP.sep_ne(d, y, b, XP.ls.k(X.ix.side(k, i), d, i, l, r, k, y, b, {{==}}, hy, hyl => XP.look_sep(l, b, d, k, y, {proj(L6,1,'hlayT')}, hyl), hyr => XP.look_sep(r, b, d, k, y, {proj(L6,2,'hlayT')}, hyr)))
  +hpb = XL.par_branch({I}, y, k, {PAB}, XP.par_cut({TB}, y, k, (s + 3 : U32), hy, hneT))
  +hpN = sub_has(IM.tr.nodes({TB}), N, {PAB}, hIN, sub_has(IM.tr.branches({TB}), IM.tr.nodes({TB}), {PAB}, br_sub({TB}), hpb))
  +hpL2 = none_notin({L2}, IM.tr.branches({TB}), {PAB}, hL2b, hpb)
'''
        eqR=f'XP.rm.heap.br(t1, {AA}, d, s, y, k, b, i, l, r, hft1, hd32, hreT1, hinv, hoks, hoffT, hlayT, hy)'
        W_=[(LOB,SIB,f'ones_clo({L2}, N, d, {TB}, y, k, s, hL2N, hN, hsN, hIN, hL2b, hy, hneT)'),(PAB,'0',f'ones_b0({L2}, N, d, {PAB}, hL2N, hN, hpN, hpL2)'),
           (f'({PAB} + 1 : U32)',G,f'ones_b1({L2}, N, d, {PAB}, hL2N, hN, hpN, hpL2)'),(FH,f'(({PAB} >> 2n : U32) + 1 : U32)',f'ones_fh({L2}, N, d, hL2N, hN)')]
    arrs=[A1]; fulls=['hft1']
    for (jj,v,_) in W_:
        arrs.append(AS(arrs[-1],jj,v)); fulls.append(sfull(arrs[-2],jj,v,fulls[-1]))
    assert arrs[-1]==AR
    tri_='htr1T'
    for m_,(jj,v,ho) in enumerate(W_):
        tri_=frstep(arrs[m_],jj,v,fulls[m_],tri_,ho)
    EQS=lambda pred: f"ME.subst(P.H, hh => {pred}, {REMW(A1)}, P.H{{KM.MG{{{AR}}}, {AA}}}, eqR, "
    IdS=f'IM.ix.del({I}, y, k)'; PlS=f'IM.mb.cons(IM.ix.par({I}, y, k), F)'
    return f'''
def lrm.{shape}({sig}) -> {GOALR('w1',I)}:
{lets}{hlets}  +eqR = {eqR}
  +htr2 = {tri_}
  %e1 : {GOALR('_',I)}
  %Equal.sym(P.H, {REMW(A1)}, P.H{{KM.MG{{{AR}}}, {AA}}}, eqR) : {GOAL(f'AD.view(U32, KMd.words(P.free(_, y)))', IdS, PlS)}
  lfr({IdS}, {PlS}, ta, d, s, ps, L, N, y, hd32, hN, hM, hQ, hPL, {AR}, {EQS(T('AD.full(U32, KMd.words(hh), d)'))}hf2L),
    {EQS(T(f'IM.ix.real(AD.view(U32, KMd.words(hh)), d, s, {IdS})'))}hre2L), {EQS(T(f'KMd.chain({PlS}, AD.view(U32, KMd.words(hh)), d, KMd.word(AD.view(U32, KMd.words(hh)), d, P.at_fh()))'))}hc2L),
    htr2, LAT.mirror(U32, {AR}))
'''
out+=rm_case('lf')+rm_case('br')
out+=f'''
def lrm({LRM_SIG}) -> {GOALR('w1',I0)}:
  match t:
    case IM.Lf{{+y0, +ky}}:
      lrm.lf(y0, ky, {LRM_ARGS}, w1, hf1, hr1, hc1, htr1, m1)
    case IM.Br{{+b, +i, +l, +r}}:
      lrm.br(b, i, l, r, {LRM_ARGS}, w1, hf1, hr1, hc1, htr1, m1)
'''
# ---- the case ----
C0=PXOK(V0,I0,'ps','L','F','N')
lets=''.join(f'  +hp{i} = {proj(C0,i,"hp")}\n' for i in range(18))
NDt='IM.tr.nodes(t)'
K3=lambda r: [f"Bool.or(P.is_static({r}), IM.ix.offr({I0}, s, d, ({r} + 1 : U32)))", f"Bool.or(P.is_static({r}), KMd.nodes.off(F, d, ({r} + 1 : U32)))", f"Bool.or(P.is_static({r}), Bool.not(Nat.is_eq(AD.slot(({r} + 1 : U32), d), AD.slot(P.at_fh(), d))))"]
KP=f'lk_off.k(P.is_static(p), p, {I0}, s, L, F, d, N, {{==}}, hpoL, hpk, hsL, hp14, hlL, hp7, hp13, hp11)'
KY=f'lk_off.k(P.is_static({WW}), {WW}, {I0}, s, L, F, d, N, {{==}}, hpoy, hpky, hsL, hp14, hlL, hp7, hp13, hp11)'
FL1=f'JP.lk_full(P.is_static(p), {A0}, d, p, {WW}, hft)'
RDy3=lambda h: f'Pair.snd(P.H, U32, P.rd({h}, (y + 3 : U32)))'
H1p=f'P.H{{KM.MG{{{LK2}}}, {AA}}}'
LXX=f'P.link_xx({H0}, p, {WW})'
EH=(f"Equal.trans(P.H, {LXX}, P.link.to(P.is_static({WW}), P.H{{KM.MG{{{LK1}}}, {AA}}}, {WW}, p), {H1p}, "
    f"Equal.cong(P.H, P.H, hh => P.link.to(P.is_static({WW}), hh, {WW}, p), P.link.to(P.is_static(p), {H0}, p, {WW}), P.H{{KM.MG{{{LK1}}}, {AA}}}, JP.lt_eq(P.is_static(p), {A0}, {AA}, p, {WW})), "
    f"JP.lt_eq(P.is_static({WW}), {LK1}, {AA}, {WW}, p))")
GETy3=GET(LK2,'(y + 3 : U32)')
HG=trans('U32',[GETy3, RDy3(H1p), RDy3(LXX), RDy3(H0), GET(A0,'(y + 3 : U32)'), WD(V0,'(y + 3 : U32)'), 's'],
  [f"Equal.sym(U32, {RDy3(H1p)}, {GETy3}, Equal.cong(P.H & U32, U32, qq => Pair.snd(P.H, U32, qq), P.rd({H1p}, (y + 3 : U32)), ({H1p}, {GETy3}), XP.rd_eqA({LK2}, {AA}, (y + 3 : U32))))",
   f"Equal.cong(P.H, U32, hh => {RDy3('hh')}, {H1p}, {LXX}, Equal.sym(P.H, {LXX}, {H1p}, heH))",
   f"HL.link_keeps({A0}, {AA}, d, p, {WW}, (y + 3 : U32), hft, hd32, JP.pk3(L, d, p, y, hpk, hyL), JP.pk3(L, d, {WW}, y, hpky, hyL))",
   f"Equal.cong(P.H & U32, U32, qq => Pair.snd(P.H, U32, qq), P.rd({H0}, (y + 3 : U32)), ({H0}, {GET(A0,'(y + 3 : U32)')}), XP.rd_eq(t0, {AA}, (y + 3 : U32)))",
   f"Equal.sym(U32, {WD(V0,'(y + 3 : U32)')}, {GET(A0,'(y + 3 : U32)')}, XP.wd(t0, d, (y + 3 : U32), hft, hd32))",
   f"XL.look_home({A0}, d, s, {I0}, k, y, hp0, hy)"])
PLm=f'IM.mb.cons({Pa}, F)'
GJ=lambda v: GOAL(v, Id, PLm)
GY=GET(A0,'(y + 1 : U32)')
HX_=f'P.free(R.rg.unlink({LXX}, y), y)'
lets+=f'''  +hsL = and_l(RG.has(L, s), RG.sub({LV(I0)}, L), hp3)
  +hlL = and_r(RG.has(L, s), RG.sub({LV(I0)}, L), hp3)
  +hyl = XL.look_leaf({I0}, k, y, hy)
  +hyL = sub_has({LV(I0)}, L, y, hlL, hyl)
  +hyt = leaf_node(t, y, hyl)
  +hst = XP.absent_nodes(t, d, s, and_l(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hp2)))
  +hys = nhas({NDt}, y, s, hyt, hst)
  +hyps = none_has(ps, Con{{s, {NDt}}}, y, hp5, has_cons(s, {NDt}, y, hyt))
  +hyF = none_has(F, Con{{s, {NDt}}}, y, hp10, has_cons(s, {NDt}, y, hyt))
  +hsF = none_has(F, Con{{s, {NDt}}}, s, hp10, has_head(s, {NDt}))
  +hsN = sub_has(L, N, s, hp12, hsL)
  +hyN = sub_has(L, N, y, hp12, hyL)
  +hyB = none_mem(L, {BR(I0)}, y, hp7, hyL)
  +hs1 = sub_without(L, y)
  +hs2 = sub_back1(L, L, y, sub_refl(L))
  +hy2 = notin_without(L, y)
  +hL2N = sub_trans({L2}, L, N, hs1, hp12)
  +hsL2 = has_without(L, y, s, ueq_ne(s, y, ueq_ne(y, s, hys)), hsL)
  +hL2b = none_subl({L2}, L, {BR(I0)}, hs1, hp7)
  +hpky = JP.fm_word(List.get(&2, U32, {V0}, AD.slot((y + 1 : U32), d)), d, L, JP.fm_of(L, {V0}, d, L, y, hp15, hyL))
  +hpoy = JP.po_of(L, {V0}, d, L, N, y, hp16, hyL)
  +hpoL = JP.pmono(N, p, L, d, hpo)
  +heH = {EH}
  +hg = {HG}
  +hFs = and_intro(IM.fl.sep(F, d, s), IM.fl.offt(F, t, d), flsep_of(F, N, d, s, hN, hp13, hsN, hsF), offt_of(F, t, N, d, hN, hp13, hp14, none_sub(F, Con{{s, {NDt}}}, {NDt}, hp10, sub_cons_r({NDt}, s, {NDt}, sub_refl({NDt})))))
'''
MBp=[f'XL.del_inv({I0}, y, k, hp1, hy)', f'XL.del_lay({I0}, s, y, k, d, hp2)',
  f"and_intro(RG.has({L2}, s), RG.sub({LV(Id)}, {L2}), hsL2, ME.subst(List<&2, U32>, qq => {T(f'RG.sub(qq, {L2})')}, RG.without({LV(I0)}, y), {LV(Id)}, Equal.sym(List<&2, U32>, {LV(Id)}, RG.without({LV(I0)}, y), XL.del_leaves({I0}, s, y, k, d, hp2, hy)), "
  f"sub_w1(RG.without({LV(I0)}, y), L, y, sub_trans(RG.without({LV(I0)}, y), {LV(I0)}, L, sub_without({LV(I0)}, y), hlL), notin_without({LV(I0)}, y))))",
  'sub_w1(ps, L, y, hp4, hyps)',
  f"none_sub(ps, Con{{s, {NDt}}}, Con{{s, {NOD(Id)}}}, hp5, and_intro(RG.has(Con{{s, {NDt}}}, s), RG.sub({NOD(Id)}, Con{{s, {NDt}}}), has_head(s, {NDt}), sub_cons_r({NOD(Id)}, s, {NDt}, XL.del_sub({I0}, y, k, {NDt}, sub_refl({NDt})))))",
  'hp6', f"none_sub({L2}, {BR(I0)}, {BR(Id)}, hL2b, XL.del_bsub({I0}, y, k, {BR(I0)}, sub_refl({BR(I0)})))", 'hL2N', f'XL.del_sub({I0}, y, k, N, hp14)']
hyD=f"none_last({Pa}, y, {NOD(Id)}, XL.del_absent({I0}, s, d, y, k, hp2, hy))"
QFp=['XL.layout_ok(N, d, y, hN, hB, hyN)',
  f'offr_n0({Id}, s, d, y, N, hN, XL.del_sub({I0}, y, k, N, hp14), hyN, hsN, {hyD}, hys)', f'offr_n1({Id}, s, d, y, N, hN, XL.del_sub({I0}, y, k, N, hp14), hyN, hsN, {hyD}, hys)',
  f'offr_hix({Id}, s, d, XL.del_lay({I0}, s, y, k, d, hp2))',
  f'ones_b0({L2}, N, d, y, hL2N, hN, hyN, hy2)', f'ones_b1({L2}, N, d, y, hL2N, hN, hyN, hy2)', f'ones_fh({L2}, N, d, hL2N, hN)']
hM=intro(MBt(Id),MBp); hQ=intro(QFt(Id),QFp)
hPL=f'lpl({Pa}, t, d, s, L, F, N, y, k, hN, hB, hp7, hp10, hp11, hp13, hp9, hyF, hyN, hs1, hy2, hst, hyB, hp14, hys, hp2, hy, {{==}})'
real1=f"real_lk(P.is_static({WW}), {LK1}, ta, d, s, {I0}, {WW}, p, {{==}}, {proj(K3(WW),0,KY)}, {FL1}, hd32, real_lk(P.is_static(p), {A0}, ta, d, s, {I0}, p, {WW}, {{==}}, {proj(K3('p'),0,KP)}, hft, hd32, hp0))"
chain1=f"chain_lk(P.is_static({WW}), {LK1}, ta, d, {WW}, p, F, {{==}}, {proj(K3(WW),1,KY)}, {proj(K3(WW),2,KY)}, {FL1}, hd32, chain_lk(P.is_static(p), {A0}, ta, d, p, {WW}, F, {{==}}, {proj(K3('p'),1,KP)}, {proj(K3('p'),2,KP)}, hft, hd32, hp8))"
tri1=f"ME.subst(P.H, hh => {T(conj(TRI('AD.view(U32, KMd.words(hh))')))}, {LXX}, {H1p}, heH, JL.link_leave({A0}, {AA}, d, L, {L2}, N, y, p, hft, hd32, hN, hp12, hyL, hs1, hs2, hy2, hpo, hpk, hp15, hp16, hp17))"
full1=f"JP.lk_full(P.is_static({WW}), {LK1}, d, {WW}, p, {FL1})"
LCP=f'''+t: IM.Tr, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +p: U32, +y: U32, +k: U32,
  +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}'''
PREMP=f"+hpo: {T('RG.po.all(p, [], d, N)')}, +hpk: {T('RG.port.ok(L, d, p)')}"
out+=f'''
# a leave, the index a tree: the facts before, the link, then the removal
def lcase({LCP},
  +hp: {T(conj(C0))}, +hy: {{IM.ix.look({I0}, k) == Some{{y}} : Maybe<&2, U32>}}, {PREMP}) -> {GJ(f'AD.view(U32, RG.words(R.leave({H0}, p, y)))')}:
{lets}  %Equal.sym(P.H & U32, P.rd({H0}, (y + 1 : U32)), ({H0}, {GY}), XP.rd_eq(t0, {AA}, (y + 1 : U32))) : {GJ('AD.view(U32, RG.words(R.lv.w(_, p, y)))')}
  %XP.wd(t0, d, (y + 1 : U32), hft, hd32) : {GJ(f'AD.view(U32, RG.words(P.free(R.rg.unlink(P.link_xx({H0}, p, _), y), y)))')}
  %Equal.sym(Array<U32>, RG.words({HX_}), KMd.words({HX_}), rw_kw({HX_})) : {GJ('AD.view(U32, _)')}
  %Equal.sym(P.H, {LXX}, {H1p}, heH) : {GJ('AD.view(U32, KMd.words(P.free(R.rg.unlink(_, y), y)))')}
  %Equal.sym(P.H & U32, P.rd({H1p}, (y + 3 : U32)), ({H1p}, {GETy3}), XP.rd_eqA({LK2}, {AA}, (y + 3 : U32))) : {GJ('AD.view(U32, KMd.words(P.free(R.rg.unlink.s(_, y), y)))')}
  %Equal.sym(U32, {GETy3}, s, hg) : {GJ(f'AD.view(U32, KMd.words(P.free(X.ix.remove({H1p}, _, y), y)))')}
  lrm(t, t0, ta, d, s, ps, L, F, N, y, k, hd32, hN, hy, hp1, hp2, {hM}, {hQ}, {hPL}, hL2N, hsN, hp14, hL2b, flok_of(F, N, d, hN, hB, hp13), hFs,
    {LK2}, {full1}, {real1}, {chain1}, {tri1}, LAT.mirror(U32, {LK2}))
'''
GK0=lambda I,w,a: T(conj(PXOK(f'AD.view(U32, RG.words(R.leave(P.H{{KM.MG{{{w}}}, {a}}}, p, y)))', f'IM.ix.del({I}, y, k)', 'ps', L2, FP(f'IM.mb.cons(IM.ix.par({I}, y, k), F)'), 'N')))
GK=lambda I,w,a: GOAL(f'AD.view(U32, RG.words(R.leave(P.H{{KM.MG{{{w}}}, {a}}}, p, y)))', f'IM.ix.del({I}, y, k)', f'IM.mb.cons(IM.ix.par({I}, y, k), F)')
out+=f'''
def lpx.k(I: IM.Ix, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +p: U32, +y: U32, +k: U32,
  +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  +hp: {T(f'RG.px.ok({V0}, d, s, I, ps, L, F, N)')}, +hy: {{IM.ix.look(I, k) == Some{{y}} : Maybe<&2, U32>}}, {PREMP}) -> {GK('I',A0,AA)}:
  match I:
    case IM.Ept{{}}:
      Empty.absurd({GK('IM.Ept{}',A0,AA)}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, m => XP.is_some(m), None{{}}, Some{{y}}, hy)))
    case IM.Has{{+t}}:
      lcase(t, t0, ta, d, s, ps, L, F, N, p, y, k, hft, hd32, hN, hB, hp, hy, hpo, hpk)

def lpx.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +p: U32, +y: U32, +k: U32,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  hp: {T('RG.px.ok(AD.view(U32, w), d, s, I, ps, L, F, N)')}, +hy: {{IM.ix.look(I, k) == Some{{y}} : Maybe<&2, U32>}}, +hpo: {T('RG.po.all(p, [], d, N)')}, m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) -> {GK0('I','w','a')}:
  (+t0, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, {A0}, w, e)
  +hpT = LAB.subst(Array<U32>, qq => {T('RG.px.ok(AD.view(U32, qq), d, s, I, ps, L, F, N)')}, w, {A0}, ew, hp)
  +hpk = AL.port_of_po(L, p, [], d, N, hpo, {proj(PXOK(f'AD.view(U32, {A0})', 'I', 'ps', 'L', 'F', 'N'),12,'hpT')}, none_nil(L), hN, hB)
  %e : {GK0('I','_','a')}
  %ea : {GK0('I',A0,'_')}
  and_l({conj(PXOK(f'AD.view(U32, RG.words(R.leave({H0}, p, y)))', 'IM.ix.del(I, y, k)', 'ps', L2, FP('IM.mb.cons(IM.ix.par(I, y, k), F)'), 'N'))}, AD.full(U32, RG.words(R.leave({H0}, p, y)), d),
    lpx.k(I, t0, ta, d, s, ps, L, F, N, p, y, k, hft, hd32, hN, hB, hpT, hy, hpo, hpk))

def Laws.leave_pend(w, a, d, s, I, ps, L, F, N, p, c, k, hf, hd32, hN, hB, hp, hc, hpo):
  lpx.m(w, a, d, s, I, ps, L, F, N, p, c, k, hf, hd32, hN, hB, hp, hc, hpo, LAT.mirror(U32, w), LAT.mirror(V.Val, a))
'''
LAW='''
# LAW: a cursor c the index finds at k leaving (R.leave), a port p linked in
# its place (its link word off every tracked node's words and the free
# list's head, RG.po.all over no live node, and faceable by the live
# nodes: the copy's root port, or the eraser), keeps the pending
# placeholders' invariant over the index: c out of the index and of the
# live nodes, the free list's first nodes c and the parent the removal
# frees (cells-freeze.sharing.cursors.index.ring.leave).
# Record: copy-reduced-function-nets
# Record: cursors-indexed
# Record: copy-links-two-way
# Record: serve-premises-over-index
law leave_pend:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +ps: List<&2, U32>
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +p: U32
  for +c: U32
  for +k: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, ps, L, F, N) == True{} : Bool}
  for hc: {IM.ix.look(I, k) == Some{c} : Maybe<&2, U32>}
  for hpo: {RG.po.all(p, Nil{}, d, N) == True{} : Bool}
  {RG.px.ok(AD.view(U32, RG.words(R.leave(P.H{KM.MG{w}, a}, p, c))), d, s, IM.ix.del(I, c, k), ps, RG.without(L, c), Con{c, IM.mb.cons(IM.ix.par(I, c, k), F)}, N) == True{} : Bool}
'''
out=re.sub(r'(?<!case )Nil\{\}', '[]', out)
if os.environ.get('LV_PART')=='2':
    open('glam/proofgen/lv_pend1.txt','w').write(out)
    open('glam/proofgen/lv_pend_law.txt','w').write(LAW)
    print('part2', len(out.splitlines()))
if not os.environ.get('LV_PART'):
    p='glam/PROOF.bend'; s=open(p).read()
    assert 'def Laws.leave_pend(' not in s
    s=s.rstrip('\n')+'\n'+out
    open(p,'w').write(s)
    lp='glam/LAWS.bend'; l=open(lp).read()
    if 'law leave_pend:' not in l:
        anchor='\n# LAW: a serve\'s end, its crossings and then its root\'s leave'
        i=l.index(anchor)
        l=l[:i].rstrip('\n')+'\n'+LAW+l[i:]
        open(lp,'w').write(l)
    print('leave', len(out.splitlines()))
