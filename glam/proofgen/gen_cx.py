# authoring aid: cross_pend over the index (glam/PROOF.bend)
p='glam/PROOF.bend'
s=open('glam/proofgen/PROOF.before_cx.bend').read()
T=lambda h: f'{{{h} == True{{}} : Bool}}'
A0='LAT.fromT(U32, t0)'; AA='LAT.fromT(V.Val, ta)'; V0=f'AD.view(U32, {A0})'
H0=f'P.H{{KM.MG{{{A0}}}, {AA}}}'
def PXA(h, m): return f'RG.px.ok(AD.view(U32, RG.words({h})), d, s, RG.cx.I({m}, I, x, src, b, far), ps, RG.cx.L({m}, x, L), RG.cx.F1({m}, I, x, far, F), N)'
def G(h, m): return T(PXA(h, m))
def G2(h, m): return T(PXA(h, m) + f' && AD.full(U32, RG.words({h}), d)')
FS=lambda F: f'RG.cx.F0(IM.ix.look(I, far), I, b, {F})'
CONJ=['IM.ix.real({V}, d, s, I)', 'IM.ix.inv(I)', 'IM.ix.lay(I, s, d)', 'RG.sub(Con{{s, IM.ix.leaves(I)}}, L)', 'RG.sub(Con{{x, ps}}, L)', 'RG.none.in(Con{{x, ps}}, Con{{s, IM.ix.nodes(I)}})', 'RG.distinct(Con{{x, ps}})',
  'RG.none.in(L, IM.ix.branches(I))', 'KMd.chain({F}, {V}, d, KMd.word({V}, d, P.at_fh()))', 'RG.distinct({F})', 'RG.none.in({F}, Con{{s, IM.ix.nodes(I)}})', 'RG.none.in({F}, L)', 'RG.sub(L, N)', 'RG.sub({F}, N)',
  'RG.sub(IM.ix.nodes(I), N)', 'RG.faces(L, {V}, d, L)', 'RG.px.off(L, {V}, d, L, N)', 'RG.px.tw(L, {V}, d, L)']
def cj(ts):
    return ts[0] if len(ts)==1 else f'{ts[0]} && ({cj(ts[1:])})' if len(ts)>2 else f'{ts[0]} && {ts[1]}'
CJ=[c.format(V='AD.view(U32, LAT.fromT(U32, t0))', F=FS('F')) for c in CONJ]
REST1=cj(CJ[1:]); REST2=cj(CJ[2:])
HP=lambda v,m: T(f'RG.px.ok({v}, d, s, I, Con{{x, ps}}, L, RG.cx.F0({m}, I, b, F), N)')
SIG=f'''+t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +far: U32, +b: U32,
  +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}'''
out=f'''
# A crossing over the index
# =========================

def isnone_eq(m: Maybe<&2, U32>, +h: {T('RG.isnone(m)')}) -> {{m == None{{}} : Maybe<&2, U32>}}:
  match m:
    case Some{{+y}}:
      Empty.absurd({{Some{{y}} == None{{}} : Maybe<&2, U32>}}, MB.false_ne_true()(h))
    case None{{}}:
      {{==}}

def cxp.k(+m: Maybe<&2, U32>, {SIG}, +he: {{IM.ix.look(I, far) == m : Maybe<&2, U32>}}, +hp: {HP(V0,'m')}, +ha: {T('RG.cx.ab(m, I, src)')}) ->
  {G2(f'R.cross.k(({H0}, m), s, x, src, neg)', 'm')}:
  match m:
    case Some{{+y}}:
      jpx.k(I, t0, ta, d, s, ps, L, F, N, x, y, far, hft, hd32, hN, hB, hp, he)
    case None{{}}:
      cpx.k(I, t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, isnone_eq(IM.ix.look(I, src), ha))

# a crossing at a heap of trees, the invariant after and its words full
def cxp.t({SIG}, +hp: {HP(V0,'IM.ix.look(I, far)')}, +ha: {T('RG.cx.ab(IM.ix.look(I, far), I, src)')}) ->
  {G2(f'R.cross({H0}, s, x, src, neg, far)', 'IM.ix.look(I, far)')}:
  +hre = and_l(IM.ix.real({V0}, d, s, I), {REST1}, hp)
  +hiv = and_l(IM.ix.inv(I), {REST2}, and_r(IM.ix.real({V0}, d, s, I), {REST1}, hp))
  %Equal.sym(P.H & Maybe<&2, U32>, X.ix.find({H0}, s, far), ({H0}, IM.ix.look(I, far)), XL.find_tree({A0}, {AA}, d, s, I, far, hft, hd32, hre, hiv)) :
    {G2('R.cross.k(_, s, x, src, neg)', 'IM.ix.look(I, far)')}
  cxp.k(IM.ix.look(I, far), t0, ta, d, s, I, ps, L, F, N, x, src, neg, far, b, hft, hd32, hN, hB, {{==}}, hp, ha)

def cxp.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +far: U32, +b: U32,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  hp: {HP('AD.view(U32, w)','IM.ix.look(I, far)')}, +ha: {T('RG.cx.ab(IM.ix.look(I, far), I, src)')}, m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {G('R.cross(P.H{KM.MG{w}, a}, s, x, src, neg, far)', 'IM.ix.look(I, far)')}:
  (+t0, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, {A0}, w, e)
  +hpT = LAB.subst(Array<U32>, qq => {HP('AD.view(U32, qq)','IM.ix.look(I, far)')}, w, {A0}, ew, hp)
  %e : {G('R.cross(P.H{KM.MG{_}, a}, s, x, src, neg, far)', 'IM.ix.look(I, far)')}
  %ea : {G(f'R.cross(P.H{{KM.MG{{{A0}}}, _}}, s, x, src, neg, far)', 'IM.ix.look(I, far)')}
  and_l({PXA(f'R.cross({H0}, s, x, src, neg, far)', 'IM.ix.look(I, far)')}, AD.full(U32, RG.words(R.cross({H0}, s, x, src, neg, far)), d),
    cxp.t(t0, ta, d, s, I, ps, L, F, N, x, src, neg, far, b, hft, hd32, hN, hB, hpT, ha))

def Laws.cross_pend(w, a, d, s, I, ps, L, F, N, x, src, neg, far, b, hf, hd32, hN, hB, hp, ha):
  cxp.m(w, a, d, s, I, ps, L, F, N, x, src, neg, far, b, hf, hd32, hN, hB, hp, ha, LAT.mirror(U32, w), LAT.mirror(V.Val, a))
'''
i=s.index('def Laws.cross_pend('); j=s.index('\n\n',i)
s=s[:i]+s[j+2:]
s=s.rstrip('\n')+'\n'+out
open(p,'w').write(s)
