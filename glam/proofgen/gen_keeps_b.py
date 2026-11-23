# authoring aid, part of gen_keeps.py: membership in the faced ports, the
# frame at j by case and the crossing's
nsX={}
exec(open('glam/proofgen/gen_cx.py').read().split("out=f" + "'" * 3)[0], nsX)
GETt=lambda A,i: f'Pair.snd(Array<U32>, U32, Array.get(U32, {A}, {i}))'
FIN=lambda v,z: f'fin.m(List.get(&2, U32, {v}, AD.slot(({z} + 1 : U32), d)), d, Fp)'
sec+=f"""
# the port a node of K faces among Fp, where each of K faces one
def fi_at(K: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +Fp: List<&2, U32>, +z: U32, +h: {T('faced.in(K, v, d, Fp)')}, hz: {T('RG.has(K, z)')}) -> {T(FIN('v','z'))}:
  match K:
    case Nil{{}}:
      Empty.absurd({T(FIN('v','z'))}, MB.false_ne_true()(hz))
    case Con{{+m, +r}}:
      or_cases(U32.is_eq(m, z), RG.has(r, z), {FIN('v','z')}, hz,
        q => ME.subst(U32, kk => {T(FIN('v','kk'))}, m, z, MS.u32_eq_of_is_eq(m, z, q), and_l({FIN('v','m')}, faced.in(r, v, d, Fp), h)),
        q => fi_at(r, v, d, Fp, z, and_r({FIN('v','m')}, faced.in(r, v, d, Fp), h), q))

# a port of Fp, its link word off j where every one of Fp's is
def ops_at(Fp: List<&2, U32>, +d: Nat, +j: U32, +r: U32, +h: {T('RG.off.ports(Fp, d, j)')}, hr: {T('RG.has(Fp, r)')}) -> {T('KMd.off.port(d, r, j)')}:
  match Fp:
    case Nil{{}}:
      Empty.absurd({T('KMd.off.port(d, r, j)')}, MB.false_ne_true()(hr))
    case Con{{+f, +q}}:
      or_cases(U32.is_eq(f, r), RG.has(q, r), KMd.off.port(d, r, j), hr,
        e => ME.subst(U32, kk => {T('KMd.off.port(d, kk, j)')}, f, r, MS.u32_eq_of_is_eq(f, r, e), and_l(KMd.off.port(d, f, j), RG.off.ports(q, d, j), h)),
        e => ops_at(q, d, j, r, and_r(KMd.off.port(d, f, j), RG.off.ports(q, d, j), h), e))

# the port a node faces, by its word 1, among Fp
def fin_word(+t: LAT.Tree<U32>, +d: Nat, +Fp: List<&2, U32>, +i: U32, +hft: {{AD.full(U32, LAT.fromT(U32, t), d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}},
  +h: {T('fin.m(List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(i, d)), d, Fp)')}) -> {T('RG.has(Fp, KMd.word(AD.view(U32, LAT.fromT(U32, t)), d, i))')}:
  ME.subst(U32, q => {T('RG.has(Fp, q)')}, {GETt('LAT.fromT(U32, t)','i')}, KMd.word(AD.view(U32, LAT.fromT(U32, t)), d, i), Equal.sym(U32, KMd.word(AD.view(U32, LAT.fromT(U32, t)), d, i), {GETt('LAT.fromT(U32, t)','i')}, XP.wg(LAT.fromT(U32, t), d, i, hft, hd32)),
    ME.subst(Maybe<&2, U32>, q => {T('fin.m(q, d, Fp)')}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(i, d)), Some{{{GETt('LAT.fromT(U32, t)','i')}}},
      Equal.sym(Maybe<&2, U32>, Some{{{GETt('LAT.fromT(U32, t)','i')}}}, List.get(&2, U32, AD.view(U32, LAT.fromT(U32, t)), AD.slot(i, d)), LA.get_view(U32, LAT.fromT(U32, t), d, i, hft, hd32)), h))
"""
def NEof(m, i, hn):
    return f"MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot({P1(m,i)}, d), AD.slot(j, d)), {proj(OWN(m,'j'),i,hn)})"
def pxlets(I0s, F0s, ind='      '):
    C=PXOK(V0, I0s, 'Con{x, ps}', 'L', F0s, 'N')
    LVs=f'IM.ix.leaves({I0s})'
    return (f"{ind}+hxL = and_l(RG.has(L, x), RG.sub(ps, L), {proj(C,4,'hp')})\n"
            f"{ind}+hsL = and_l(RG.has(L, s), RG.sub({LVs}, L), {proj(C,3,'hp')})\n"
            f"{ind}+hxN = sub_has(L, N, x, {proj(C,12,'hp')}, hxL)\n"
            f"{ind}+hsN = sub_has(L, N, s, {proj(C,12,'hp')}, hsL)\n"), C
CKPAR=f"""+t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +b: U32,
  +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}"""
KGOAL=lambda h: f'{{{RD(h,"j")} == {RD(H0,"j")} : U32}}'
CUR=f'R.cursor({H0}, s, x, src, neg)'
le, Ce = pxlets('IM.Ept{}','F'); lh, Ch = pxlets('IM.Has{t}','Con{b, F}')
sec+=f"""
# a cursor made: every word off the tracked nodes' and the free list's head
# as it was
def ck.k(I: IM.Ix, {CKPAR},
  +hp: {T(f'RG.px.ok({V0}, d, s, I, Con{{x, ps}}, L, IM.ix.take(I, b, F), N)')}, +ha: {{IM.ix.look(I, src) == None{{}} : Maybe<&2, U32>}}, +j: U32, +hj: {T('RG.off.nodes(N, d, j)')}, +hjh: {NE_('P.at_fh()','j')}) -> {KGOAL(CUR)}:
  match I:
    case IM.Ept{{}}:
{le}      +hnx = n_at(N, d, j, x, hj, hxN)
      cfr.ept(t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, ha, j, {NEof('x',0,'hnx')}, {NEof('x',2,'hnx')}, {NEof('x',3,'hnx')},
        ixoffb(IM.Ept{{}}, s, N, d, j, hsN, {{==}}, hj), {{==}}, hjh)
    case IM.Has{{+t}}:
{lh}      +hnx = n_at(N, d, j, x, hj, hxN)
      +hbN = and_l(RG.has(N, b), RG.sub(F, N), {proj(Ch,13,'hp')})
      cfr.has(t, t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, ha, j, {NEof('x',0,'hnx')}, {NEof('x',2,'hnx')}, {NEof('x',3,'hnx')},
        ixoffb(IM.Has{{t}}, s, N, d, j, hsN, {proj(Ch,14,'hp')}, hj), n_at(N, d, j, b, hj, hbN), hjh)
"""
JOIN=f'R.join1({H0}, x, y)'
lj, Cj = pxlets('IM.Has{t}','F', '  ')
JKPAR=CKPAR.replace('+src: U32, +neg: Bool, +b: U32,','+y: U32, +k: U32,')
JPR=f"+Fp: List<&2, U32>, +j: U32, +hj: {T('RG.off.nodes(N, d, j)')}, +hjh: {NE_('P.at_fh()','j')}, +hjf: {T('RG.off.ports(Fp, d, j)')}, +hfi: {T(f'faced.in(L, {V0}, d, Fp)')}"
jchain=trans('U32',[RD(JOIN,'j'), RD(H1p,'j'), RD(LXX,'j'), RD(H0,'j')],
    [f"jfr.k(t, t0, ta, d, s, ps, L, F, N, x, y, k, hft, hd32, hN, hB, hp, hy, j, {NEof('x',0,'hnx')}, {NEof('x',1,'hnx')}, {NEof('y',0,'hny')}, {NEof('y',1,'hny')}, hjh, ixoffb(IM.Has{{t}}, s, N, d, j, hsN, {proj(Cj,14,'hp')}, hj))",
     f"Equal.cong(P.H, U32, hh => {RD('hh','j')}, {H1p}, {LXX}, Equal.sym(P.H, {LXX}, {H1p}, {EH}))",
     f"HL.link_keeps({A0}, {AA}, d, {UU}, {WW}, j, hft, hd32, ops_at(Fp, d, j, {UU}, hjf, hUF), ops_at(Fp, d, j, {WW}, hjf, hWF))"])
sec+=f"""
# a join: every word off the tracked nodes', the free list's head and the
# faced ports' link words as it was
def jk.t(+t: IM.Tr, {JKPAR},
  +hp: {T(conj(Cj))}, +hy: {{IM.ix.look(IM.Has{{t}}, k) == Some{{y}} : Maybe<&2, U32>}}, {JPR}) -> {KGOAL(JOIN)}:
{lj}  +hyL = sub_has(IM.ix.leaves(IM.Has{{t}}), L, y, and_r(RG.has(L, s), RG.sub(IM.ix.leaves(IM.Has{{t}}), L), {proj(Cj,3,'hp')}), XL.look_leaf(IM.Has{{t}}, k, y, hy))
  +hyN = sub_has(L, N, y, {proj(Cj,12,'hp')}, hyL)
  +hnx = n_at(N, d, j, x, hj, hxN)
  +hny = n_at(N, d, j, y, hj, hyN)
  +hUF = fin_word(t0, d, Fp, (x + 1 : U32), hft, hd32, fi_at(L, {V0}, d, Fp, x, hfi, hxL))
  +hWF = fin_word(t0, d, Fp, (y + 1 : U32), hft, hd32, fi_at(L, {V0}, d, Fp, y, hfi, hyL))
  {jchain}

def jk.k(I: IM.Ix, {JKPAR},
  +hp: {T(f'RG.px.ok({V0}, d, s, I, Con{{x, ps}}, L, F, N)')}, +hy: {{IM.ix.look(I, k) == Some{{y}} : Maybe<&2, U32>}}, {JPR}) -> {KGOAL(JOIN)}:
  match I:
    case IM.Ept{{}}:
      Empty.absurd({KGOAL(JOIN)}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, mm => XP.is_some(mm), None{{}}, Some{{y}}, hy)))
    case IM.Has{{+t}}:
      jk.t(t, t0, ta, d, s, ps, L, F, N, x, y, k, hft, hd32, hN, hB, hp, hy, Fp, j, hj, hjh, hjf, hfi)
"""
CROSSK=f'R.cross.k(({H0}, m), s, x, src, neg)'
XPAR=CKPAR.replace('+b: U32,','+far: U32, +b: U32,')
HPm=lambda mm: T(f'RG.px.ok({V0}, d, s, I, Con{{x, ps}}, L, RG.cx.F0({mm}, I, b, F), N)')
sec+=f"""
# a crossing, either way
def cks.k(+m: Maybe<&2, U32>, +I: IM.Ix, {XPAR}, +he: {{IM.ix.look(I, far) == m : Maybe<&2, U32>}}, +hp: {HPm('m')}, +ha: {T('RG.cx.ab(m, I, src)')},
  {JPR}) -> {KGOAL(CROSSK)}:
  match m:
    case Some{{+y}}:
      jk.k(I, t0, ta, d, s, ps, L, F, N, x, y, far, hft, hd32, hN, hB, hp, he, Fp, j, hj, hjh, hjf, hfi)
    case None{{}}:
      ck.k(I, t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, isnone_eq(IM.ix.look(I, src), ha), j, hj, hjh)

def cks.t(+I: IM.Ix, {XPAR}, +hp: {HPm('IM.ix.look(I, far)')}, +ha: {T('RG.cx.ab(IM.ix.look(I, far), I, src)')},
  {JPR}) -> {KGOAL(f'R.cross({H0}, s, x, src, neg, far)')}:
  +hre = and_l(IM.ix.real({V0}, d, s, I), {nsX['REST1']}, hp)
  +hiv = and_l(IM.ix.inv(I), {nsX['REST2']}, and_r(IM.ix.real({V0}, d, s, I), {nsX['REST1']}, hp))
  %Equal.sym(P.H & Maybe<&2, U32>, X.ix.find({H0}, s, far), ({H0}, IM.ix.look(I, far)), XL.find_tree({A0}, {AA}, d, s, I, far, hft, hd32, hre, hiv)) :
    {KGOAL('R.cross.k(_, s, x, src, neg)')}
  cks.k(IM.ix.look(I, far), I, t0, ta, d, s, ps, L, F, N, x, src, neg, far, b, hft, hd32, hN, hB, {{==}}, hp, ha, Fp, j, hj, hjh, hjf, hfi)
"""

def WORDFIN(A, i, hf, h):   # fin.m(List.get(view A, slot(i))) from has(Fp, GET(A, i)), A full
    return f"ME.subst(Maybe<&2, U32>, q => {T('fin.m(q, d, Fp)')}, Some{{{GETt(A,i)}}}, List.get(&2, U32, AD.view(U32, {A}), AD.slot({i}, d)), LA.get_view(U32, {A}, d, {i}, {hf}, hd32), {h})"
sec+=f"""
# a choice of two ports of Fp, one of them
def hs_sel(+c: Bool, +a: U32, +b: U32, +Fp: List<&2, U32>, +ha: {T('RG.has(Fp, a)')}, +hb: {T('RG.has(Fp, b)')}) -> {T('RG.has(Fp, JP.sel(c, a, b))')}:
  match c:
    case True{{}}:
      ha
    case False{{}}:
      hb
"""
exec(open('glam/proofgen/gen_keeps_c.py').read())

exec(open('glam/proofgen/gen_keeps_d.py').read())

exec(open('glam/proofgen/gen_keeps_e.py').read())
