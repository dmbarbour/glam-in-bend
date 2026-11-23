# authoring aid: cursor_head restated over the index (glam/LAWS.bend,
# glam/PROOF.bend): the cursor's frame (cfr_case, gen_keeps.py) read at the
# cursor's own word 0; run by regen.sh after gen_lvk.py
import os, re
nsC={}
exec(open('glam/proofgen/gen_cpend.py').read().split("# the law's proof replaced")[0], nsC)
T=lambda h: f'{{{h} == True{{}} : Bool}}'
NE_=lambda a,b: f'{{Nat.is_eq(AD.slot({a}, d), AD.slot({b}, d)) == False{{}} : Bool}}'
RD=lambda h,j: f'Pair.snd(P.H, U32, P.rd({h}, {j}))'
GT=lambda A,j: f'Pair.snd(Array<U32>, U32, Array.get(U32, {A}, {j}))'
trans=nsC['trans']; conj=nsC['conj']; proj=nsC['proj']; OWt=nsC['OWt']; DISJ=nsC['DISJ']; NDOK=nsC['NDOK']
A0c, A1c, A2c, HDc = nsC['A0'], nsC['A1'], nsC['A2'], nsC['HD']
out='''
# A cursor's header over the index (cursor_head;
# cells-freeze.sharing.cursors.index.ring.retire): a node apart from n,
# n's word 0 off its words; a tree apart from n, n's word 0 off its
# branches
def sep_w0(+d: Nat, +a: U32, +n: U32, +h: {IM.nd.sep(d, a, n) == True{} : Bool}) -> {KMd.off.words(KMd.nw(a), d, n) == True{} : Bool}:
  and_l(KMd.off.words(KMd.nw(a), d, n), KMd.off.words(KMd.nw(a), d, (n + 1 : U32)) && (KMd.off.words(KMd.nw(a), d, (n + 2 : U32)) && KMd.off.words(KMd.nw(a), d, (n + 3 : U32))), and_r(IM.nd.disj(d, a, n), IM.nd.disj(d, n, a), h))

def offn_offb0(t: IM.Tr, +d: Nat, +n: U32, +h: {IM.tr.offn(t, d, n) == True{} : Bool}) -> {IM.tr.offb(t, d, n) == True{} : Bool}:
  match t:
    case IM.Lf{+y, +ky}:
      {==}
    case IM.Br{+b, +i, +l, +r}:
      +hlr = and_r(IM.nd.sep(d, b, n), IM.tr.offn(l, d, n) && IM.tr.offn(r, d, n), h)
      and_intro(KMd.off.words(KMd.nw(b), d, n), IM.tr.offb(l, d, n) && IM.tr.offb(r, d, n), sep_w0(d, b, n, and_l(IM.nd.sep(d, b, n), IM.tr.offn(l, d, n) && IM.tr.offn(r, d, n), h)),
        and_intro(IM.tr.offb(l, d, n), IM.tr.offb(r, d, n), offn_offb0(l, d, n, and_l(IM.tr.offn(l, d, n), IM.tr.offn(r, d, n), hlr)), offn_offb0(r, d, n, and_r(IM.tr.offn(l, d, n), IM.tr.offn(r, d, n), hlr))))
'''
x2x=(f'not_true(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(x, d)), and_l(Bool.not(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(x, d))), RG.off([(x + 3 : U32)], d, x), {{R3}}))')
apx=proj(NDOK('x'),1,'hokx')
R123=f'and_l(RG.off([(x + 1 : U32), (x + 2 : U32), (x + 3 : U32)], d, x), RG.apartw([(x + 1 : U32), (x + 2 : U32), (x + 3 : U32)], d), {apx})'
R23=f'and_r(Bool.not(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(x, d))), RG.off([(x + 2 : U32), (x + 3 : U32)], d, x), {R123})'
R3=f'and_r(Bool.not(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(x, d))), RG.off([(x + 3 : U32)], d, x), {R23})'
X2X=f'not_true(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(x, d)), and_l(Bool.not(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(x, d))), RG.off([(x + 3 : U32)], d, x), {R23}))'
X3X=f'not_true(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(x, d)), and_l(Bool.not(Nat.is_eq(AD.slot((x + 3 : U32), d), AD.slot(x, d))), RG.off([], d, x), {R3}))'
okx3=proj(NDOK('x'),2,'hokx')
XFH=f"neq_comm2(AD.slot(x, d), AD.slot(P.at_fh(), d), not_true(Nat.is_eq(AD.slot(x, d), AD.slot(P.at_fh(), d)), {proj(OWt('x','P.at_fh()'),0,okx3)}))"
D_xs='and_l(IM.nd.disj(d, x, s), IM.nd.disj(d, s, x), hsxs)'
S3X=proj(OWt('s','x'),3,proj(DISJ('x','s'),0,D_xs))
def ch_case(has):
    lets, Lc = nsC['CASE_LETS'][has]
    I0='IM.Has{t}' if has else 'IM.Ept{}'; F0='Con{b, F}' if has else 'F'; bE='b' if has else 's'
    nm='ch.has' if has else 'ch.ept'; tparam='+t: IM.Tr, ' if has else ''
    C0=nsC['PXOK'](nsC['V0'], I0, 'Con{x, ps}', 'L', F0, 'N')
    WW=nsC['WD'](A2c,'P.at_fh()')
    if has:
        RESTC=f'U32.is_eq(KMd.at_idx({WW}), b) && KMd.chain(F, AD.view(U32, {A2c}), d, KMd.word(AD.view(U32, {A2c}), d, (b + 1 : U32)))'
        room=(f'and_intro(Bool.not(U32.is_eq({WW}, 0)), Bool.and(U32.is_eq(KMd.at_idx({WW}), b), True{{}}), and_l(Bool.not(U32.is_eq({WW}, 0)), {RESTC}, hch2), '
              f'and_intro(U32.is_eq(KMd.at_idx({WW}), b), True{{}}, and_l(U32.is_eq(KMd.at_idx({WW}), b), KMd.chain(F, AD.view(U32, {A2c}), d, KMd.word(AD.view(U32, {A2c}), d, (b + 1 : U32))), and_r(Bool.not(U32.is_eq({WW}, 0)), {RESTC}, hch2)), {{==}}))')
        hjb=f'and_intro(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(x, d))), IM.tr.offb(t, d, x), {S3X}, offn_offb0(t, d, x, hofx))'
        hjn=proj(DISJ('x','b'),0,'and_l(IM.nd.disj(d, x, b), IM.nd.disj(d, b, x), hsxb)')
    else:
        room='{==}'; hjb=S3X; hjn='{==}'
    HA=f'P.H{{KM.MG{{{A0c}}}, a}}'; INS2=f'X.ix.insert(P.H{{KM.MG{{{A2c}}}, a}}, s, x)'
    chain=trans('U32',[RD(INS2,'x'), RD(f'P.H{{KM.MG{{{A2c}}}, a}}','x'), GT(A2c,'x'), GT(A1c,'x'), HDc],
      [f'XL.insert_keeps({A2c}, a, d, s, {I0}, x, src, {bE}, x, {nsC["f2"]}, hd32, hre2, hp1, hp2, hfr, {room}, hk2, hnb2, ha, {hjb}, {hjn}, {XFH}, {X3X})',
       f'rd_get({A2c}, a, x)', f'LA.get_set_other(U32, {A1c}, d, (x + 2 : U32), x, src, {nsC["f1"]}, hd32, {X2X})',
       f'LA.get_set_same(U32, {A0c}, x, {HDc})'])
    txt=f"""
# a cursor made, {('into a tree' if has else 'into an empty index')}: its word 0 its header after the insert
def {nm}({tparam}+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +b: U32,
  +hft: {{AD.full(U32, {A0c}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  +hp: {T(conj(C0))}, +ha: {{IM.ix.look({I0}, src) == None{{}} : Maybe<&2, U32>}}) -> {{{RD(f'R.cursor({HA}, s, x, src, neg)','x')} == {HDc} : U32}}:
{lets}{Lc}  {chain}
"""
    return nsC['ta_of'](txt)
out+=ch_case(False)+ch_case(True)
AA='LAT.fromT(V.Val, ta)'
HAt=f'P.H{{KM.MG{{{A0c}}}, {AA}}}'
GKc=lambda w,a: f"{{{RD(f'R.cursor(P.H{{KM.MG{{{w}}}, {a}}}, s, x, src, neg)','x')} == {HDc} : U32}}"
out+=f'''
def ch.k(I: IM.Ix, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +b: U32,
  +hft: {{AD.full(U32, {A0c}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  +hp: {T(f'RG.px.ok(AD.view(U32, {A0c}), d, s, I, Con{{x, ps}}, L, IM.ix.take(I, b, F), N)')}, +ha: {{IM.ix.look(I, src) == None{{}} : Maybe<&2, U32>}}) -> {GKc(A0c, AA)}:
  match I:
    case IM.Ept{{}}:
      ch.ept(t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, ha)
    case IM.Has{{+t}}:
      ch.has(t, t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, ha)

def ch.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +b: U32,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  hp: {T('RG.px.ok(AD.view(U32, w), d, s, I, Con{x, ps}, L, IM.ix.take(I, b, F), N)')}, +ha: {{IM.ix.look(I, src) == None{{}} : Maybe<&2, U32>}}, m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) -> {GKc('w','a')}:
  (+t0, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  %e : {GKc('_','a')}
  %ea : {GKc(A0c,'_')}
  ch.k(I, t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, LAB.subst(Array<U32>, qq => {T('RG.px.ok(AD.view(U32, qq), d, s, I, Con{x, ps}, L, IM.ix.take(I, b, F), N)')}, w, {A0c}, Equal.sym(Array<U32>, {A0c}, w, e), hp), ha)

def Laws.cursor_head(w, a, d, s, I, ps, L, F, N, x, src, neg, b, hf, hd32, hN, hB, hp, ha):
  ch.m(w, a, d, s, I, ps, L, F, N, x, src, neg, b, hf, hd32, hN, hB, hp, ha, LAT.mirror(U32, w), LAT.mirror(V.Val, a))
'''
out=re.sub(r'(?<!case )Nil\{\}', '[]', out)
LAW='''# LAW: a placeholder x made a cursor (R.cursor), on cursor_pend's
# premises, holds its header, a cursor's kind (18) and form (0 negative,
# 1 positive), at word 0 after the insert into the index
# (cells-freeze.sharing.cursors.index.ring.retire: no other law sees a
# cursor's form).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
# Record: cursors-indexed
law cursor_head:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +s: U32
  for +I: IM.Ix
  for +ps: List<&2, U32>
  for +L: List<&2, U32>
  for +F: List<&2, U32>
  for +N: List<&2, U32>
  for +x: U32
  for +src: U32
  for +neg: Bool
  for +b: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, Con{x, ps}, L, IM.ix.take(I, b, F), N) == True{} : Bool}
  for ha: {IM.ix.look(I, src) == None{} : Maybe<&2, U32>}
  {Pair.snd(P.H, U32, P.rd(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg), x)) == P.hd2(18, R.cur.form(neg), 0) : U32}
'''
if os.environ.get('CH_ONLY'):
    i=out.index('def Laws.cursor_head(')
    open('glam/proofgen/kp/sec.txt','w').write(out[:i])
    print('ch', len(out.splitlines()))
else:
    p='glam/PROOF.bend'; s=open(p).read()
    def drop(s, head):
        i=s.index(head); j=s.index('\n\n',i); return s[:i]+s[j+2:]
    if 'def cursor_head.m(' in s:
        for h in ('def cursor_head.m(','def Laws.cursor_head('):
            s=drop(s,h)
    assert 'def ch.k(' not in s
    s=s.rstrip('\n')+'\n'+out
    open(p,'w').write(s)
    lp='glam/LAWS.bend'; l=open(lp).read()
    if 'law cursor_head:\n  for w: Array<U32>\n  for a: Array<V.Val>\n  for +d: Nat\n  for +s: U32\n  for +t:' in l:
        i=l.index('# LAW: a placeholder x made a cursor, x ready to enter the ring, holds\n# its header')
        j=l.index('\n\n', l.index('law cursor_head:'))
        l=l[:i]+LAW.rstrip('\n')+l[j:]
        open(lp,'w').write(l)
    print('ch', len(out.splitlines()))
