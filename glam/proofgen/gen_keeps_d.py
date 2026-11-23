# authoring aid, part of gen_keeps.py: the faced ports after a cursor made
# and after a join, and after a crossing
def cfi_case(has):
    I0='IM.Has{t}' if has else 'IM.Ept{}'; F0='Con{b, F}' if has else 'F'
    nm='cfi.has' if has else 'cfi.ept'; tparam='+t: IM.Tr, ' if has else ''; targ='t, ' if has else ''
    C=PXOK(V0, I0, 'Con{x, ps}', 'L', F0, 'N')
    W=f'RG.words({CUR})'
    lp, _=pxlets(I0, F0)
    extra=''
    if has:
        extra=(f"      +hzB = none_mem(L, IM.ix.branches({I0}), z, {proj(C,7,'hp')}, hzL)\n"
               f"      +hbN = and_l(RG.has(N, b), RG.sub(F, N), {proj(C,13,'hp')})\n"
               f"      +hbL = MB.eq_false_of_not_eq_true(RG.has(L, b), and_l(Bool.not(RG.has(L, b)), RG.none.in(F, L), {proj(C,11,'hp')}))\n"
               f"      +hzb = nhas(L, z, b, hzL, hbL)\n")
        newb=W1of('z','b','XL.layout_sep(N, d, z, b, hN, hzN, hbN, hzb)')
    else:
        newb='{==}'
    hg=trans('U32',[GETt(W,'(z + 1 : U32)'), RD(f'P.H{{KM.MG{{{W}}}, KMd.vals({CUR})}}','(z + 1 : U32)'), RD(CUR,'(z + 1 : U32)'), RD(H0,'(z + 1 : U32)'), GETt(A0,'(z + 1 : U32)')],
      [f"Equal.sym(U32, {RD(f'P.H{{KM.MG{{{W}}}, KMd.vals({CUR})}}','(z + 1 : U32)')}, {GETt(W,'(z + 1 : U32)')}, rd_get({W}, KMd.vals({CUR}), (z + 1 : U32)))",
       f"Equal.cong(P.H, U32, hh => {RD('hh','(z + 1 : U32)')}, P.H{{KM.MG{{{W}}}, KMd.vals({CUR})}}, {CUR}, heta2({CUR}))", 'hfr', f'rd_get({A0}, {AA}, (z + 1 : U32))'])
    NEx=lambda i: f"MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot({P1('x',i)}, d), AD.slot((z + 1 : U32), d)), {proj(SX,[0,2,3].index(i),'hsx')})"
    G=lambda K: T(f'faced.in({K}, AD.view(U32, {W}), d, Fp)')
    return f"""
# the faced ports after a cursor made {('into a tree' if has else 'into an empty index')}: each live node's word 1 as it was
def {nm}(K: List<&2, U32>, {tparam}{CKPAR},
  +hp: {T(conj(C))}, +ha: {{IM.ix.look({I0}, src) == None{{}} : Maybe<&2, U32>}}, +Fp: List<&2, U32>, +hfi: {T(f'faced.in(L, {V0}, d, Fp)')}, +hfW: {T(f'AD.full(U32, {W}, d)')},
  +hK: {T('RG.sub(K, L)')}) -> {G('K')}:
  match K:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
{lp}      +hzL = and_l(RG.has(L, z), RG.sub(r, L), hK)
      +hzN = sub_has(L, N, z, {proj(C,12,'hp')}, hzL)
{extra}      +hsx = sx.k(U32.is_eq(z, x), z, x, N, d, {{==}}, hN, hzN, hxN)
      +hfr = cfr.{('has' if has else 'ept')}({targ}t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, ha, (z + 1 : U32), {NEx(0)}, {NEx(2)}, {NEx(3)}, {OFFBz(has, proj(C,14,'hp'))}, {newb}, {FHz})
      +hzF = ME.subst(Maybe<&2, U32>, q => {T('fin.m(q, d, Fp)')}, List.get(&2, U32, {V0}, AD.slot((z + 1 : U32), d)), Some{{{GETt(A0,'(z + 1 : U32)')}}},
        Equal.sym(Maybe<&2, U32>, Some{{{GETt(A0,'(z + 1 : U32)')}}}, List.get(&2, U32, {V0}, AD.slot((z + 1 : U32), d)), LA.get_view(U32, {A0}, d, (z + 1 : U32), hft, hd32)), fi_at(L, {V0}, d, Fp, z, hfi, hzL))
      and_intro({FIN(f'AD.view(U32, {W})','z')}, faced.in(r, AD.view(U32, {W}), d, Fp),
        {WORDFIN(W,'(z + 1 : U32)','hfW',f"ME.subst(U32, q => {T('RG.has(Fp, q)')}, {GETt(A0,'(z + 1 : U32)')}, {GETt(W,'(z + 1 : U32)')}, Equal.sym(U32, {GETt(W,'(z + 1 : U32)')}, {GETt(A0,'(z + 1 : U32)')}, {hg}), hzF)")},
        {nm}(r, {targ}t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, ha, Fp, hfi, hfW, and_r(RG.has(L, z), RG.sub(r, L), hK)))
"""
sec+=cfi_case(False)+cfi_case(True)
# the join
WJ=f'RG.words({JOIN})'
L2s='RG.without(RG.without(L, x), y)'
hgj=trans('U32',[GETt(WJ,'(z + 1 : U32)'), RD(f'P.H{{KM.MG{{{WJ}}}, KMd.vals({JOIN})}}','(z + 1 : U32)'), RD(JOIN,'(z + 1 : U32)'), RD(H1p,'(z + 1 : U32)'), GETt(LK2,'(z + 1 : U32)')],
  [f"Equal.sym(U32, {RD(f'P.H{{KM.MG{{{WJ}}}, KMd.vals({JOIN})}}','(z + 1 : U32)')}, {GETt(WJ,'(z + 1 : U32)')}, rd_get({WJ}, KMd.vals({JOIN}), (z + 1 : U32)))",
   f"Equal.cong(P.H, U32, hh => {RD('hh','(z + 1 : U32)')}, P.H{{KM.MG{{{WJ}}}, KMd.vals({JOIN})}}, {JOIN}, heta2({JOIN}))", 'hfr', f'rd_get({LK2}, {AA}, (z + 1 : U32))'])
GJ2=lambda K: T(f'faced.in({K}, AD.view(U32, {WJ}), d, Fp)')
JGO=f"""+hp: {T(conj(Cj))}, +hy: {{IM.ix.look(IM.Has{{t}}, k) == Some{{y}} : Maybe<&2, U32>}}, +Fp: List<&2, U32>, +hfW: {T(f'AD.full(U32, {WJ}, d)')}, +hLK: {T(f'faced.in({L2s}, AD.view(U32, {LK2}), d, Fp)')},
  +hs1: {T(f'RG.sub({L2s}, L)')}, +hx2: {F_(f'RG.has({L2s}, x)')}, +hy2: {F_(f'RG.has({L2s}, y)')}, +hxN: {T('RG.has(N, x)')}, +hyN: {T('RG.has(N, y)')}, +hsN: {T('RG.has(N, s)')}"""
JGA='t, t0, ta, d, s, ps, L, F, N, x, y, k, hft, hd32, hN, hB, hp, hy, Fp, hfW, hLK, hs1, hx2, hy2, hxN, hyN, hsN'
sec+=f"""
# the faced ports after a join: each remaining live node's word 1 as after
# the link alone, there one of the ports faced before
def jfi.go(K: List<&2, U32>, +t: IM.Tr, {JKPAR},
  {JGO}, +hK: {T(f'RG.sub(K, {L2s})')}) -> {GJ2('K')}:
  match K:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      +hz2 = and_l(RG.has({L2s}, z), RG.sub(r, {L2s}), hK)
      +hzL = sub_has({L2s}, L, z, hs1, hz2)
      +hzN = sub_has(L, N, z, {proj(Cj,12,'hp')}, hzL)
      +hzB = none_mem(L, IM.ix.branches(IM.Has{{t}}), z, {proj(Cj,7,'hp')}, hzL)
      +hzx = nhas({L2s}, z, x, hz2, hx2)
      +hzy = nhas({L2s}, z, y, hz2, hy2)
      +hwx = {W1of('z','x','XL.layout_sep(N, d, z, x, hN, hzN, hxN, hzx)')}
      +hwy = {W1of('z','y','XL.layout_sep(N, d, z, y, hN, hzN, hyN, hzy)')}
      +hfr = jfr.k(t, t0, ta, d, s, ps, L, F, N, x, y, k, hft, hd32, hN, hB, hp, hy, (z + 1 : U32), {NEz('x',0,'hwx')}, {NEz('x',1,'hwx')}, {NEz('y',0,'hwy')}, {NEz('y',1,'hwy')}, {FHz}, {OFFBz(True, proj(Cj,14,'hp'))})
      +hzF = ME.subst(Maybe<&2, U32>, q => {T('fin.m(q, d, Fp)')}, List.get(&2, U32, AD.view(U32, {LK2}), AD.slot((z + 1 : U32), d)), Some{{{GETt(LK2,'(z + 1 : U32)')}}},
        Equal.sym(Maybe<&2, U32>, Some{{{GETt(LK2,'(z + 1 : U32)')}}}, List.get(&2, U32, AD.view(U32, {LK2}), AD.slot((z + 1 : U32), d)), LA.get_view(U32, {LK2}, d, (z + 1 : U32), {full1}, hd32)), fi_at({L2s}, AD.view(U32, {LK2}), d, Fp, z, hLK, hz2))
      and_intro({FIN(f'AD.view(U32, {WJ})','z')}, faced.in(r, AD.view(U32, {WJ}), d, Fp),
        {WORDFIN(WJ,'(z + 1 : U32)','hfW',f"ME.subst(U32, q => {T('RG.has(Fp, q)')}, {GETt(LK2,'(z + 1 : U32)')}, {GETt(WJ,'(z + 1 : U32)')}, Equal.sym(U32, {GETt(WJ,'(z + 1 : U32)')}, {GETt(LK2,'(z + 1 : U32)')}, {hgj}), hzF)")},
        jfi.go(r, {JGA}, and_r(RG.has({L2s}, z), RG.sub(r, {L2s}), hK)))
"""
