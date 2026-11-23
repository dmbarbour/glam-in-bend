# authoring aid: join1_pend over the index, part 3, and the file
import re
exec(open('glam/proofgen/gen_j1b.py').read().split("open('glam/proofgen/j1_part2.txt','w')")[0])
out=''
# ---- the removal, by the tree's shape ----
A1='LAT.fromT(U32, t1)'
JFR_SIG_BASE=f'''+t: IM.Tr, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +k: U32,
  +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hy: {{IM.ix.look({I0}, k) == Some{{y}} : Maybe<&2, U32>}},
  +hinv: {T(f'IM.ix.inv({I0})')}, +hlay: {T(f'IM.ix.lay({I0}, s, d)')}, +hM: {T(conj(MBt(Id)))}, +hQ: {T(conj(QFt(Id)))}, +hPL: {T(conj(PLFt(Id,f'IM.mb.cons({Pa}, F)')))},
  +hL2N: {T(f'RG.sub({L2}, N)')}, +hsN: {T('RG.has(N, s)')}, +hIN: {T(f'RG.sub({NOD(I0)}, N)')}, +hL2b: {T(f'RG.none.in({L2}, {BR(I0)})')},
  +hFok: {T('IM.fl.ok(F, d)')}, +hFs: {T(f'IM.ix.flsep({I0}, s, d, F)')},
  -w1: Array<U32>, hf1: {{AD.full(U32, w1, d) == True{{}} : Bool}}, hr1: {T(f'IM.ix.real(AD.view(U32, w1), d, s, {I0})')},
  hc1: {T('KMd.chain(F, AD.view(U32, w1), d, KMd.word(AD.view(U32, w1), d, P.at_fh()))')}, htr1: {T(conj(TRI('AD.view(U32, w1)')))}, m1: LAT.Mirror(U32, w1)'''
JFR_ARGS='t, t0, ta, d, s, ps, L, F, N, x, y, k, hd32, hN, hy, hinv, hlay, hM, hQ, hPL, hL2N, hsN, hIN, hL2b, hFok, hFs'
PLX=f'IM.mb.cons({Pa}, F)'
GOALR=lambda w,I: GOAL(f'AD.view(U32, KMd.words(P.free(P.free(X.ix.remove(P.H{{KM.MG{{{w}}}, {AA}}}, s, y), x), y)))', f'IM.ix.del({I}, y, k)', f'IM.mb.cons(IM.ix.par({I}, y, k), F)')
def rm_case(shape):
    if shape=='lf':
        TT='IM.Lf{y0, ky}'; tparam='+y0: U32, +ky: U32'; targs='y0, ky'
    else:
        TT='IM.Br{b, i, l, r}'; tparam='+b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr'; targs='b, i, l, r'
    sig=JFR_SIG_BASE.replace('+t: IM.Tr, ',tparam+', ').replace('IM.Has{t}','IM.Has{'+TT+'}').replace('IM.tr.nodes(t)','IM.tr.nodes('+TT+')')
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
        W=[('(s + 3 : U32)','s',f'ones_p3({L2}, N, d, s, hL2N, hN, hsN)')]
        hlets=''
    else:
        TB=TT
        CUTB=f'IM.tr.cutat({TB}, y, k, (s + 3 : U32))'
        LOB=f'XP.cut.lo({CUTB})'; SIB=f'XP.cut.si({CUTB})'; PAB=f'XP.cut.pa({CUTB})'
        B1=AS(A1,LOB,SIB); G=GET(B1,FH); AR=AS(AS(AS(B1,PAB,'0'),f'({PAB} + 1 : U32)',G),FH,f'(({PAB} >> 2n : U32) + 1 : U32)')
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
        W=[(LOB,SIB,f'ones_clo({L2}, N, d, {TB}, y, k, s, hL2N, hN, hsN, hIN, hL2b, hy, hneT)'),(PAB,'0',f'ones_b0({L2}, N, d, {PAB}, hL2N, hN, hpN, hpL2)'),
           (f'({PAB} + 1 : U32)',G,f'ones_b1({L2}, N, d, {PAB}, hL2N, hN, hpN, hpL2)'),(FH,f'(({PAB} >> 2n : U32) + 1 : U32)',f'ones_fh({L2}, N, d, hL2N, hN)')]
    arrs=[A1]; fulls=['hft1']
    for (jj,v,_) in W:
        arrs.append(AS(arrs[-1],jj,v)); fulls.append(sfull(arrs[-2],jj,v,fulls[-1]))
    assert arrs[-1]==AR
    tri='htr1T'
    for m,(jj,v,ho) in enumerate(W):
        tri=frstep(arrs[m],jj,v,fulls[m],tri,ho)
    EQS=lambda pred: f"ME.subst(P.H, hh => {pred}, {REMW(A1)}, P.H{{KM.MG{{{AR}}}, {AA}}}, eqR, "
    IdS=f'IM.ix.del({I}, y, k)'; PlS=f'IM.mb.cons(IM.ix.par({I}, y, k), F)'
    return f'''
def jrm.{shape}({sig}) -> {GOALR('w1',I)}:
{lets}{hlets}  +eqR = {eqR}
  +htr2 = {tri}
  %e1 : {GOALR('_',I)}
  %Equal.sym(P.H, {REMW(A1)}, P.H{{KM.MG{{{AR}}}, {AA}}}, eqR) : {GOAL(f'AD.view(U32, KMd.words(P.free(P.free(_, x), y)))', IdS, PlS)}
  jfr({IdS}, {PlS}, ta, d, s, ps, L, N, x, y, hd32, hN, hM, hQ, hPL, {AR}, {EQS(T('AD.full(U32, KMd.words(hh), d)'))}hf2L),
    {EQS(T(f'IM.ix.real(AD.view(U32, KMd.words(hh)), d, s, {IdS})'))}hre2L), {EQS(T(f'KMd.chain({PlS}, AD.view(U32, KMd.words(hh)), d, KMd.word(AD.view(U32, KMd.words(hh)), d, P.at_fh()))'))}hc2L),
    htr2, LAT.mirror(U32, {AR}))
'''
out+=rm_case('lf')+rm_case('br')
out+=f'''
def jrm({JFR_SIG_BASE}) -> {GOALR('w1',I0)}:
  match t:
    case IM.Lf{{+y0, +ky}}:
      jrm.lf(y0, ky, {JFR_ARGS.replace('t, t0','t0')}, w1, hf1, hr1, hc1, htr1, m1)
    case IM.Br{{+b, +i, +l, +r}}:
      jrm.br(b, i, l, r, {JFR_ARGS.replace('t, t0','t0')}, w1, hf1, hr1, hc1, htr1, m1)
'''
# ---- the case: facts, the link, the goal's rewrites ----
C0=PXOK(V0,I0,'Con{x, ps}','L','F','N')
lets=''.join(f'  +hp{i} = {proj(C0,i,"hp")}\n' for i in range(18))
NDt=f'IM.tr.nodes(t)'
K3=lambda r: [f"Bool.or(P.is_static({r}), IM.ix.offr({I0}, s, d, ({r} + 1 : U32)))", f"Bool.or(P.is_static({r}), KMd.nodes.off(F, d, ({r} + 1 : U32)))", f"Bool.or(P.is_static({r}), Bool.not(Nat.is_eq(AD.slot(({r} + 1 : U32), d), AD.slot(P.at_fh(), d))))"]
KX=f'lk_off.k(P.is_static({UU}), {UU}, {I0}, s, L, F, d, N, {{==}}, hpox, hpkx, hsL, hp14, hlL, hp7, hp13, hp11)'
KY=f'lk_off.k(P.is_static({WW}), {WW}, {I0}, s, L, F, d, N, {{==}}, hpoy, hpky, hsL, hp14, hlL, hp7, hp13, hp11)'
FL1=f'JP.lk_full(P.is_static({UU}), {A0}, d, {UU}, {WW}, hft)'
RD=lambda h: f'Pair.snd(P.H, U32, P.rd({h}, (y + 3 : U32)))'
H1p=f'P.H{{KM.MG{{{LK2}}}, {AA}}}'
LXX=f'P.link_xx({H0}, {UU}, {WW})'
EH=(f"Equal.trans(P.H, {LXX}, P.link.to(P.is_static({WW}), P.H{{KM.MG{{{LK1}}}, {AA}}}, {WW}, {UU}), {H1p}, "
    f"Equal.cong(P.H, P.H, hh => P.link.to(P.is_static({WW}), hh, {WW}, {UU}), P.link.to(P.is_static({UU}), {H0}, {UU}, {WW}), P.H{{KM.MG{{{LK1}}}, {AA}}}, JP.lt_eq(P.is_static({UU}), {A0}, {AA}, {UU}, {WW})), "
    f"JP.lt_eq(P.is_static({WW}), {LK1}, {AA}, {WW}, {UU}))")
GETy3=GET(LK2,'(y + 3 : U32)')
HG=trans('U32',[GETy3, RD(H1p), RD(LXX), RD(H0), GET(A0,'(y + 3 : U32)'), WD(V0,'(y + 3 : U32)'), 's'],
  [f"Equal.sym(U32, {RD(H1p)}, {GETy3}, Equal.cong(P.H & U32, U32, qq => Pair.snd(P.H, U32, qq), P.rd({H1p}, (y + 3 : U32)), ({H1p}, {GETy3}), XP.rd_eqA({LK2}, {AA}, (y + 3 : U32))))",
   f"Equal.cong(P.H, U32, hh => {RD('hh')}, {H1p}, {LXX}, Equal.sym(P.H, {LXX}, {H1p}, heH))",
   f"HL.link_keeps({A0}, {AA}, d, {UU}, {WW}, (y + 3 : U32), hft, hd32, JP.pk3(L, d, {UU}, y, hpkx, hyL), JP.pk3(L, d, {WW}, y, hpky, hyL))",
   f"Equal.cong(P.H & U32, U32, qq => Pair.snd(P.H, U32, qq), P.rd({H0}, (y + 3 : U32)), ({H0}, {GET(A0,'(y + 3 : U32)')}), XP.rd_eq(t0, {AA}, (y + 3 : U32)))",
   f"Equal.sym(U32, {WD(V0,'(y + 3 : U32)')}, {GET(A0,'(y + 3 : U32)')}, XP.wd(t0, d, (y + 3 : U32), hft, hd32))",
   f"XL.look_home({A0}, d, s, {I0}, k, y, hp0, hy)"])
PLm=f'IM.mb.cons({Pa}, F)'
GJ=lambda v: GOAL(v, Id, PLm)
GX=GET(A0,'(x + 1 : U32)'); GY=GET(A0,'(y + 1 : U32)')
HX_=f'P.free(P.free(R.rg.unlink(P.link_xx({H0}, {UU}, {WW}), y), x), y)'
lets2=f'''  +hsL = and_l(RG.has(L, s), RG.sub({LV(I0)}, L), hp3)
  +hlL = and_r(RG.has(L, s), RG.sub({LV(I0)}, L), hp3)
  +hxL = and_l(RG.has(L, x), RG.sub(ps, L), hp4)
  +hps = and_r(RG.has(L, x), RG.sub(ps, L), hp4)
  +hxo = MB.eq_false_of_not_eq_true(RG.has(Con{{s, {NDt}}}, x), and_l(Bool.not(RG.has(Con{{s, {NDt}}}, x)), RG.none.in(ps, Con{{s, {NDt}}}), hp5))
  +hpsn = and_r(Bool.not(RG.has(Con{{s, {NDt}}}, x)), RG.none.in(ps, Con{{s, {NDt}}}), hp5)
  +hxs = ueq_ne(s, x, or_false_l(U32.is_eq(s, x), RG.has({NDt}, x), hxo))
  +hxt = or_false_r(U32.is_eq(s, x), RG.has({NDt}, x), hxo)
  +hxps = MB.eq_false_of_not_eq_true(RG.has(ps, x), and_l(Bool.not(RG.has(ps, x)), RG.distinct(ps), hp6))
  +hpsd = and_r(Bool.not(RG.has(ps, x)), RG.distinct(ps), hp6)
  +hyl = XL.look_leaf({I0}, k, y, hy)
  +hyL = sub_has({LV(I0)}, L, y, hlL, hyl)
  +hyt = leaf_node(t, y, hyl)
  +hst = XP.absent_nodes(t, d, s, and_l(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hp2)))
  +hys = nhas({NDt}, y, s, hyt, hst)
  +hxy = ueq_ne(y, x, nhas({NDt}, y, x, hyt, hxt))
  +hyps = none_has(ps, Con{{s, {NDt}}}, y, hpsn, has_cons(s, {NDt}, y, hyt))
  +hyF = none_has(F, Con{{s, {NDt}}}, y, hp10, has_cons(s, {NDt}, y, hyt))
  +hxF = none_has(F, L, x, hp11, hxL)
  +hsF = none_has(F, Con{{s, {NDt}}}, s, hp10, has_head(s, {NDt}))
  +hsN = sub_has(L, N, s, hp12, hsL)
  +hxN = sub_has(L, N, x, hp12, hxL)
  +hyN = sub_has(L, N, y, hp12, hyL)
  +hyB = none_mem(L, {BR(I0)}, y, hp7, hyL)
  +hs1 = sub_trans({L2}, RG.without(L, x), L, sub_without(RG.without(L, x), y), sub_without(L, x))
  +hs2 = sub_back(L, L, x, y, sub_refl(L))
  +hx2 = notin_sub({L2}, RG.without(L, x), x, sub_without(RG.without(L, x), y), notin_without(L, x))
  +hy2 = notin_without(RG.without(L, x), y)
  +hL2N = sub_trans({L2}, L, N, hs1, hp12)
  +hsL2 = has_without(RG.without(L, x), y, s, ueq_ne(s, y, ueq_ne(y, s, hys)), has_without(L, x, s, ueq_ne(s, x, ueq_ne(x, s, hxs)), hsL))
  +hL2b = none_subl({L2}, L, {BR(I0)}, hs1, hp7)
  +hpkx = JP.fm_word(List.get(&2, U32, {V0}, AD.slot((x + 1 : U32), d)), d, L, JP.fm_of(L, {V0}, d, L, x, hp15, hxL))
  +hpky = JP.fm_word(List.get(&2, U32, {V0}, AD.slot((y + 1 : U32), d)), d, L, JP.fm_of(L, {V0}, d, L, y, hp15, hyL))
  +hpox = JP.po_of(L, {V0}, d, L, N, x, hp16, hxL)
  +hpoy = JP.po_of(L, {V0}, d, L, N, y, hp16, hyL)
  +heH = {EH}
  +hg = {HG}
  +hFs = and_intro(IM.fl.sep(F, d, s), IM.fl.offt(F, t, d), flsep_of(F, N, d, s, hN, hp13, hsN, hsF), offt_of(F, t, N, d, hN, hp13, hp14, none_sub(F, Con{{s, {NDt}}}, {NDt}, hp10, sub_cons_r({NDt}, s, {NDt}, sub_refl({NDt})))))
'''
# the model bundle for Id and the free bundle
MBp=[f'XL.del_inv({I0}, y, k, hp1, hy)', f'XL.del_lay({I0}, s, y, k, d, hp2)',
  f"and_intro(RG.has({L2}, s), RG.sub({LV(Id)}, {L2}), hsL2, ME.subst(List<&2, U32>, qq => {T(f'RG.sub(qq, {L2})')}, RG.without({LV(I0)}, y), {LV(Id)}, Equal.sym(List<&2, U32>, {LV(Id)}, RG.without({LV(I0)}, y), XL.del_leaves({I0}, s, y, k, d, hp2, hy)), "
  f"sub_w2(RG.without({LV(I0)}, y), L, x, y, sub_trans(RG.without({LV(I0)}, y), {LV(I0)}, L, sub_without({LV(I0)}, y), hlL), notin_sub(RG.without({LV(I0)}, y), {LV(I0)}, x, sub_without({LV(I0)}, y), notin_sub({LV(I0)}, {NDt}, x, lv_sub(t), hxt)), notin_without({LV(I0)}, y))))",
  'sub_w2(ps, L, x, y, hps, hxps, hyps)',
  f"none_sub(ps, Con{{s, {NDt}}}, Con{{s, {NOD(Id)}}}, hpsn, and_intro(RG.has(Con{{s, {NDt}}}, s), RG.sub({NOD(Id)}, Con{{s, {NDt}}}), has_head(s, {NDt}), sub_cons_r({NOD(Id)}, s, {NDt}, XL.del_sub({I0}, y, k, {NDt}, sub_refl({NDt})))))",
  'hpsd', f"none_sub({L2}, {BR(I0)}, {BR(Id)}, hL2b, XL.del_bsub({I0}, y, k, {BR(I0)}, sub_refl({BR(I0)})))", 'hL2N', f'XL.del_sub({I0}, y, k, N, hp14)']
hyD=f"none_last({Pa}, y, {NOD(Id)}, XL.del_absent({I0}, s, d, y, k, hp2, hy))"
hxD=f"notin_sub({NOD(Id)}, {NDt}, x, XL.del_sub({I0}, y, k, {NDt}, sub_refl({NDt})), hxt)"
QFp=['XL.layout_ok(N, d, x, hN, hB, hxN)', 'XL.layout_ok(N, d, y, hN, hB, hyN)',
  f'offr_n0({Id}, s, d, x, N, hN, XL.del_sub({I0}, y, k, N, hp14), hxN, hsN, {hxD}, hxs)', f'offr_n1({Id}, s, d, x, N, hN, XL.del_sub({I0}, y, k, N, hp14), hxN, hsN, {hxD}, hxs)',
  f'offr_n0({Id}, s, d, y, N, hN, XL.del_sub({I0}, y, k, N, hp14), hyN, hsN, {hyD}, hys)', f'offr_n1({Id}, s, d, y, N, hN, XL.del_sub({I0}, y, k, N, hp14), hyN, hsN, {hyD}, hys)',
  f'offr_hix({Id}, s, d, XL.del_lay({I0}, s, y, k, d, hp2))',
  f'ones_b0({L2}, N, d, x, hL2N, hN, hxN, hx2)', f'ones_b1({L2}, N, d, x, hL2N, hN, hxN, hx2)', f'ones_b0({L2}, N, d, y, hL2N, hN, hyN, hy2)', f'ones_b1({L2}, N, d, y, hL2N, hN, hyN, hy2)',
  f'ones_fh({L2}, N, d, hL2N, hN)']
hM=intro(MBt(Id),MBp); hQ=intro(QFt(Id),QFp)
hPL=f'jpl({Pa}, t, d, s, L, F, N, x, y, k, hN, hB, hp7, hp10, hp11, hp13, hp9, hyF, hxF, hxy, hxN, hyN, hs1, hx2, hy2, hxt, hst, hyB, hp14, hxs, hys, hp2, hy, {{==}})'
real1=f"real_lk(P.is_static({WW}), {LK1}, ta, d, s, {I0}, {WW}, {UU}, {{==}}, {proj(K3(WW),0,KY)}, {FL1}, hd32, real_lk(P.is_static({UU}), {A0}, ta, d, s, {I0}, {UU}, {WW}, {{==}}, {proj(K3(UU),0,KX)}, hft, hd32, hp0))"
chain1=f"chain_lk(P.is_static({WW}), {LK1}, ta, d, {WW}, {UU}, F, {{==}}, {proj(K3(WW),1,KY)}, {proj(K3(WW),2,KY)}, {FL1}, hd32, chain_lk(P.is_static({UU}), {A0}, ta, d, {UU}, {WW}, F, {{==}}, {proj(K3(UU),1,KX)}, {proj(K3(UU),2,KX)}, hft, hd32, hp8))"
tri1=f"ME.subst(P.H, hh => {T(conj(TRI('AD.view(U32, KMd.words(hh))')))}, {LXX}, {H1p}, heH, JL.link_live({A0}, {AA}, d, L, {L2}, N, x, y, hft, hd32, hN, hp12, hxL, hyL, hxy, hs1, hs2, hx2, hy2, hp15, hp16, hp17))"
full1=f"JP.lk_full(P.is_static({WW}), {LK1}, d, {WW}, {UU}, {FL1})"
GXv=lambda v: GJ(v)
out+=f'''
# a join, the index a tree: the facts before, the link, then the removal
def jcase(+t: IM.Tr, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +k: U32,
  +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  +hp: {T(conj(C0))}, +hy: {{IM.ix.look({I0}, k) == Some{{y}} : Maybe<&2, U32>}}) -> {GJ(f'AD.view(U32, RG.words(R.join1({H0}, x, y)))')}:
{lets}{lets2}  %Equal.sym(P.H & U32, P.rd({H0}, (x + 1 : U32)), ({H0}, {GX}), XP.rd_eq(t0, {AA}, (x + 1 : U32))) : {GJ('AD.view(U32, RG.words(R.jn1.u(_, x, y)))')}
  %Equal.sym(P.H & U32, P.rd({H0}, (y + 1 : U32)), ({H0}, {GY}), XP.rd_eq(t0, {AA}, (y + 1 : U32))) : {GJ(f'AD.view(U32, RG.words(R.jn1.w(_, {GX}, x, y)))')}
  %XP.wd(t0, d, (x + 1 : U32), hft, hd32) : {GJ(f'AD.view(U32, RG.words(P.free(P.free(R.rg.unlink(P.link_xx({H0}, _, {GY}), y), x), y)))')}
  %XP.wd(t0, d, (y + 1 : U32), hft, hd32) : {GJ(f'AD.view(U32, RG.words(P.free(P.free(R.rg.unlink(P.link_xx({H0}, {UU}, _), y), x), y)))')}
  %Equal.sym(Array<U32>, RG.words({HX_}), KMd.words({HX_}), rw_kw({HX_})) : {GJ('AD.view(U32, _)')}
  %Equal.sym(P.H, {LXX}, {H1p}, heH) : {GJ('AD.view(U32, KMd.words(P.free(P.free(R.rg.unlink(_, y), x), y)))')}
  %Equal.sym(P.H & U32, P.rd({H1p}, (y + 3 : U32)), ({H1p}, {GETy3}), XP.rd_eqA({LK2}, {AA}, (y + 3 : U32))) : {GJ('AD.view(U32, KMd.words(P.free(P.free(R.rg.unlink.s(_, y), x), y)))')}
  %Equal.sym(U32, {GETy3}, s, hg) : {GJ(f'AD.view(U32, KMd.words(P.free(P.free(X.ix.remove({H1p}, _, y), x), y)))')}
  jrm(t, t0, ta, d, s, ps, L, F, N, x, y, k, hd32, hN, hy, hp1, hp2, {hM}, {hQ}, {hPL}, hL2N, hsN, hp14, hL2b, flok_of(F, N, d, hN, hB, hp13), hFs,
    {LK2}, {full1}, {real1}, {chain1}, {tri1}, LAT.mirror(U32, {LK2}))
'''
# ---- the entry ----
GK0=lambda I,w,a: T(conj(PXOK(f'AD.view(U32, RG.words(R.join1(P.H{{KM.MG{{{w}}}, {a}}}, x, y)))', f'IM.ix.del({I}, y, k)', 'ps', L2, FP(f'IM.mb.cons(IM.ix.par({I}, y, k), F)'), 'N')))
GK=lambda I,w,a: GOAL(f'AD.view(U32, RG.words(R.join1(P.H{{KM.MG{{{w}}}, {a}}}, x, y)))', f'IM.ix.del({I}, y, k)', f'IM.mb.cons(IM.ix.par({I}, y, k), F)')
out+=f'''
def jpx.k(I: IM.Ix, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +k: U32,
  +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  +hp: {T(f'RG.px.ok({V0}, d, s, I, Con{{x, ps}}, L, F, N)')}, +hy: {{IM.ix.look(I, k) == Some{{y}} : Maybe<&2, U32>}}) -> {GK('I',A0,AA)}:
  match I:
    case IM.Ept{{}}:
      Empty.absurd({GK('IM.Ept{}',A0,AA)}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, m => XP.is_some(m), None{{}}, Some{{y}}, hy)))
    case IM.Has{{+t}}:
      jcase(t, t0, ta, d, s, ps, L, F, N, x, y, k, hft, hd32, hN, hB, hp, hy)

def jpx.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +k: U32,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  hp: {T('RG.px.ok(AD.view(U32, w), d, s, I, Con{x, ps}, L, F, N)')}, +hy: {{IM.ix.look(I, k) == Some{{y}} : Maybe<&2, U32>}}, m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) -> {GK0('I','w','a')}:
  (+t0, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, {A0}, w, e)
  %e : {GK0('I','_','a')}
  %ea : {GK0('I',A0,'_')}
  and_l({conj(PXOK(f'AD.view(U32, RG.words(R.join1({H0}, x, y)))', 'IM.ix.del(I, y, k)', 'ps', L2, FP('IM.mb.cons(IM.ix.par(I, y, k), F)'), 'N'))}, AD.full(U32, RG.words(R.join1({H0}, x, y)), d),
    jpx.k(I, t0, ta, d, s, ps, L, F, N, x, y, k, hft, hd32, hN, hB, LAB.subst(Array<U32>, qq => {T('RG.px.ok(AD.view(U32, qq), d, s, I, Con{x, ps}, L, F, N)')}, w, {A0}, ew, hp), hy))

def Laws.join1_pend(w, a, d, s, I, ps, L, F, N, x, y, k, hf, hd32, hN, hB, hp, hy):
  jpx.m(w, a, d, s, I, ps, L, F, N, x, y, k, hf, hd32, hN, hB, hp, hy, LAT.mirror(U32, w), LAT.mirror(V.Val, a))
'''
part1=open('glam/proofgen/j1_part1.txt').read()
part2=open('glam/proofgen/j1_part2.txt').read()
full=part1+part2+out
s=open('glam/proofgen/PROOF.before_j1.bend').read()
i=s.index('def Laws.join1_pend('); j=s.index('\n\n',i)
s=s[:i]+s[j+2:]
for imp in ['import ./JOIN_LAWS.bend as JL','import ./JOIN_PROOF.bend as JP','import ../spike/HEAP_LAWS.bend as HL','import ../spike/HEAP_PROOF.bend as HLP']:
    if imp not in s:
        s=s.replace('import ./witness.bend as WB\n', 'import ./witness.bend as WB\n'+imp+'\n',1)
s=s.rstrip('\n')+'\n'+full
open('glam/PROOF.bend','w').write(s)
print('written', len(full.splitlines()))
