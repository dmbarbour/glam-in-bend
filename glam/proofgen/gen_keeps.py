# authoring aid: crossings_keeps over the index (glam/PROOF.bend), run
# after gen_fold.py by regen.sh; KP_ONLY writes the section alone for the
# scratch harness (kp/harness.py, an authoring aid not kept)
import os, re
src=open('glam/proofgen/gen_j1c.py').read()
exec(src.split("part1=open(")[0])
T=lambda h: f'{{{h} == True{{}} : Bool}}'
F_=lambda h: f'{{{h} == False{{}} : Bool}}'
NE_=lambda a,b: f'{{Nat.is_eq(AD.slot({a}, d), AD.slot({b}, d)) == False{{}} : Bool}}'
SL=lambda a,b: f'Bool.not(Nat.is_eq(AD.slot({a}, d), AD.slot({b}, d)))'
P1=lambda a,i: a if i==0 else f'({a} + {i} : U32)'
RGN=lambda m,j: [SL(P1(m,i),j) for i in range(4)]
OWN=lambda m,j: [SL(P1(m,i),j) for i in range(4)]+['True{}']
RD=lambda h,j: f'Pair.snd(P.H, U32, P.rd({h}, {j}))'
sec=f'''
# A copy's crossings over the index: the words they keep
# ======================================================
#
# cells-freeze.sharing.cursors.index.ring.fold: crossings_keeps by the
# crossings in turn, each keeping word j by the index's own frame laws
# (remove_keeps, insert_keeps) at the heap after its link or its header's
# writes, a free's and a link's frame; the ports the live nodes face kept
# among the first ones (faced.in), a join moving a faced port from one
# node to another.

# word j off a node's words, ring_model's form to kmodel's
def on_ow(+d: Nat, +m: U32, +j: U32, +h: {T(conj(RGN('m','j')))}) -> {T('KMd.off.words(KMd.nw(m), d, j)')}:
  {intro(OWN('m','j'), [proj(RGN('m','j'),i,'h') for i in range(4)]+['{==}'])}

# word j off every node of N, so off each one's
def n_at(N: List<&2, U32>, +d: Nat, +j: U32, +m: U32, +h: {T('RG.off.nodes(N, d, j)')}, hm: {T('RG.has(N, m)')}) -> {T('KMd.off.words(KMd.nw(m), d, j)')}:
  on_ow(d, m, j, nodes_at(N, d, j, m, h, hm))
'''
APP=lambda a,b: f'List.append(&2, U32, {a}, {b})'
NL='IM.tr.nodes(l)'; NR='IM.tr.nodes(r)'
sec+=f'''
# word j off every branch of a tree whose nodes N holds
def offb_from(t: IM.Tr, +N: List<&2, U32>, +d: Nat, +j: U32, +hs: {T('RG.sub(IM.tr.nodes(t), N)')}, +hj: {T('RG.off.nodes(N, d, j)')}) -> {T('IM.tr.offb(t, d, j)')}:
  match t:
    case IM.Lf{{+y, +k}}:
      {{==}}
    case IM.Br{{+b, +i, +l, +r}}:
      XP.and_intro(KMd.off.words(KMd.nw(b), d, j), IM.tr.offb(l, d, j) && IM.tr.offb(r, d, j), n_at(N, d, j, b, hj, XP.and_l(RG.has(N, b), RG.sub({APP(NL,NR)}, N), hs)),
        XP.and_intro(IM.tr.offb(l, d, j), IM.tr.offb(r, d, j),
          offb_from(l, N, d, j, sub_trans({NL}, {APP(NL,NR)}, N, sub_appl({NL}, {NR}), XP.and_r(RG.has(N, b), RG.sub({APP(NL,NR)}, N), hs)), hj),
          offb_from(r, N, d, j, sub_trans({NR}, {APP(NL,NR)}, N, sub_appr({NL}, {NR}), XP.and_r(RG.has(N, b), RG.sub({APP(NL,NR)}, N), hs)), hj)))

# and off the situating node's word 3: the index's frame premise
def ixoffb(I: IM.Ix, +s: U32, +N: List<&2, U32>, +d: Nat, +j: U32, +hsN: {T('RG.has(N, s)')}, +hIN: {T('RG.sub(IM.ix.nodes(I), N)')}, +hj: {T('RG.off.nodes(N, d, j)')}) -> {T('IM.ix.offb(I, s, d, j)')}:
  match I:
    case IM.Ept{{}}:
      {proj(OWN('s','j'),3,'n_at(N, d, j, s, hj, hsN)')}
    case IM.Has{{+t}}:
      XP.and_intro({SL('(s + 3 : U32)','j')}, IM.tr.offb(t, d, j), {proj(OWN('s','j'),3,'n_at(N, d, j, s, hj, hsN)')}, offb_from(t, N, d, j, hIN, hj))

# any heap in its parts (kmodel's)
def heta3(h: P.H) -> {{P.H{{KM.MG{{KMd.words(h)}}, KMd.vals(h)}} == h : P.H}}:
  match h:
    case P.H{{w, a}}:
      match w:
        case KM.MG{{x}}:
          {{==}}

# a free, every word off the node and the head as it was
def fk.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +r: U32, +j: U32, hf: {T('AD.full(U32, w, d)')}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}},
  +h0: {NE_('P.base(r)','j')}, +h1: {NE_('(P.base(r) + 1 : U32)','j')}, +hh: {NE_('P.at_fh()','j')}, m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {{{RD('P.free(P.H{KM.MG{w}, a}, r)','j')} == {RD('P.H{KM.MG{w}, a}','j')} : U32}}:
  (+t, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t, d, e, hf)
  %e : {{{RD('P.free(P.H{KM.MG{_}, a}, r)','j')} == {RD('P.H{KM.MG{_}, a}','j')} : U32}}
  %ea : {{{RD('P.free(P.H{KM.MG{LAT.fromT(U32, t)}, _}, r)','j')} == {RD('P.H{KM.MG{LAT.fromT(U32, t)}, _}','j')} : U32}}
  {trans('U32',[RD('P.free(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, r)','j'), RD('P.H{KM.MG{RG.words(P.free(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, r))}, LAT.fromT(V.Val, ta)}','j'),
    'Pair.snd(Array<U32>, U32, Array.get(U32, RG.words(P.free(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, r)), j))', 'Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j))', RD('P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}','j')],
   ['Equal.cong(P.H, U32, hh => '+RD('hh','j')+', P.free(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, r), P.H{KM.MG{RG.words(P.free(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, r))}, LAT.fromT(V.Val, ta)}, Equal.sym(P.H, P.H{KM.MG{RG.words(P.free(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, r))}, LAT.fromT(V.Val, ta)}, P.free(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, r), fr_parts(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), r, LAT.mirror(U32, LAT.fromT(U32, t)))))',
    'rd_get(RG.words(P.free(P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}, r)), LAT.fromT(V.Val, ta), j)',
    'fr_keeps(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), d, r, j, hft, hd32, h0, h1, hh, LAT.mirror(U32, LAT.fromT(U32, t)))',
    'Equal.sym(U32, '+RD('P.H{KM.MG{LAT.fromT(U32, t)}, LAT.fromT(V.Val, ta)}','j')+', Pair.snd(Array<U32>, U32, Array.get(U32, LAT.fromT(U32, t), j)), rd_get(LAT.fromT(U32, t), LAT.fromT(V.Val, ta), j))'])}

'''

# the cursor's lets, from its generator (its output unchanged)
nsC={}
exec(open('glam/proofgen/gen_cpend.py').read().split("# the law's proof replaced")[0], nsC)
def cfr_case(has):
    lets, Lc = nsC['CASE_LETS'][has]
    I0='IM.Has{t}' if has else 'IM.Ept{}'; F0='Con{b, F}' if has else 'F'; bE='b' if has else 's'
    nm='cfr.has' if has else 'cfr.ept'; tparam='+t: IM.Tr, ' if has else ''
    A0c, A1c, A2c, HDc = nsC['A0'], nsC['A1'], nsC['A2'], nsC['HD']
    C0=nsC['PXOK'](nsC['V0'], I0, 'Con{x, ps}', 'L', F0, 'N')
    WW=nsC['WD'](A2c,'P.at_fh()')
    if has:
        RESTC=f'U32.is_eq(KMd.at_idx({WW}), b) && KMd.chain(F, AD.view(U32, {A2c}), d, KMd.word(AD.view(U32, {A2c}), d, (b + 1 : U32)))'
        room=(f'and_intro(Bool.not(U32.is_eq({WW}, 0)), Bool.and(U32.is_eq(KMd.at_idx({WW}), b), True{{}}), and_l(Bool.not(U32.is_eq({WW}, 0)), {RESTC}, hch2), '
              f'and_intro(U32.is_eq(KMd.at_idx({WW}), b), True{{}}, and_l(U32.is_eq(KMd.at_idx({WW}), b), KMd.chain(F, AD.view(U32, {A2c}), d, KMd.word(AD.view(U32, {A2c}), d, (b + 1 : U32))), and_r(Bool.not(U32.is_eq({WW}, 0)), {RESTC}, hch2)), {{==}}))')
    else:
        room='{==}'
    HA=f'P.H{{KM.MG{{{A0c}}}, a}}'; INS2=f'X.ix.insert(P.H{{KM.MG{{{A2c}}}, a}}, s, x)'
    GT=lambda A: f'Pair.snd(Array<U32>, U32, Array.get(U32, {A}, j))'
    chain=trans('U32',[RD(INS2,'j'), RD(f'P.H{{KM.MG{{{A2c}}}, a}}','j'), GT(A2c), GT(A1c), GT(A0c), RD(HA,'j')],
      [f'XL.insert_keeps({A2c}, a, d, s, {I0}, x, src, {bE}, j, {nsC["f2"]}, hd32, hre2, hp1, hp2, hfr, {room}, hk2, hnb2, ha, hjb, hjn, hjh, hjx3)',
       f'rd_get({A2c}, a, j)', f'LA.get_set_other(U32, {A1c}, d, (x + 2 : U32), j, src, {nsC["f1"]}, hd32, hjx2)',
       f'LA.get_set_other(U32, {A0c}, d, x, j, {HDc}, hft, hd32, hjx0)', f'Equal.sym(U32, {RD(HA,"j")}, {GT(A0c)}, rd_get({A0c}, a, j))'])
    txt=f"""
# a cursor made, {('into a tree' if has else 'into an empty index')}: a word off its written words, the index's
# branches{(', the node it takes' if has else '')} and the free list's head as it was
def {nm}({tparam}+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +b: U32,
  +hft: {{AD.full(U32, {A0c}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  +hp: {T(conj(C0))}, +ha: {{IM.ix.look({I0}, src) == None{{}} : Maybe<&2, U32>}}, +j: U32, +hjx0: {NE_('x','j')}, +hjx2: {NE_('(x + 2 : U32)','j')}, +hjx3: {NE_('(x + 3 : U32)','j')},
  +hjb: {T(f'IM.ix.offb({I0}, s, d, j)')}, +hjn: {T(f'IM.ix.newb({I0}, {bE}, d, j)')}, +hjh: {NE_('P.at_fh()','j')}) -> {{{RD(f'R.cursor({HA}, s, x, src, neg)','j')} == {RD(HA,'j')} : U32}}:
{lets}{Lc}  {chain}
"""
    return nsC['ta_of'](txt)
sec+=cfr_case(False)+cfr_case(True)

# a free of any heap R (a term, P.H not Data): its words full, a word
# off the node and the head as it was
HP_=lambda R: f'P.H{{KM.MG{{KMd.words({R})}}, KMd.vals({R})}}'
def FFULL(R, r, hf):
    return f"ME.subst(P.H, hh => {T(f'AD.full(U32, KMd.words(P.free(hh, {r})), d)')}, {HP_(R)}, {R}, heta3({R}), XL.free_full(KMd.words({R}), KMd.vals({R}), d, {r}, {hf}))"
def FKEEP(R, r, j, hf, h0, h1, hh):
    return (f"ME.subst(P.H, hh => {{{RD(f'P.free(hh, {r})',j)} == {RD('hh',j)} : U32}}, {HP_(R)}, {R}, heta3({R}), "
            f"fk.m(KMd.words({R}), KMd.vals({R}), d, {r}, {j}, {hf}, hd32, {h0}, {h1}, {hh}, LAT.mirror(U32, KMd.words({R})), LAT.mirror(V.Val, KMd.vals({R}))))")

# the join's frame below its link: the join rewritten as jcase does, then
# the removal's frame law and the two frees'
def jfr_k():
    KG=lambda h: f'{{{RD(h,"j")} == {RD(H1p,"j")} : U32}}'
    R2=f'X.ix.remove({H1p}, s, y)'
    hfR2=f'XL.remove_full({LK2}, {AA}, d, s, {I0}, y, k, {full1}, hd32, {real1}, hp1, hp2, hy)'
    def b0(r,h): return f"ME.subst(U32, q => {NE_('q','j')}, {r}, P.base({r}), Equal.sym(U32, P.base({r}), {r}, hb{r}), {h})"
    def b1(r,h): return f"ME.subst(U32, q => {NE_('(q + 1 : U32)','j')}, {r}, P.base({r}), Equal.sym(U32, P.base({r}), {r}, hb{r}), {h})"
    chain=trans('U32',[RD(f'P.free(P.free({R2}, x), y)','j'), RD(f'P.free({R2}, x)','j'), RD(R2,'j'), RD(H1p,'j')],
      [FKEEP(f'P.free({R2}, x)','y','j',FFULL(R2,'x',hfR2),b0('y','hjy0'),b1('y','hjy1'),'hjh'),
       FKEEP(R2,'x','j',hfR2,b0('x','hjx0'),b1('x','hjx1'),'hjh'),
       f'XL.remove_keeps({LK2}, {AA}, d, s, {I0}, y, k, j, {full1}, hd32, {real1}, hp1, hp2, hy, hjb, hjh)'])
    NDB=lambda r: f"MS.u32_eq_of_is_eq(P.base({r}), {r}, and_l(U32.is_eq(P.base({r}), {r}), IM.ws.apart(KMd.nw({r}), d) && KMd.off.words(KMd.nw({r}), d, P.at_fh()), XL.layout_ok(N, d, {r}, hN, hB, h{r}N)))"
    return f"""
# a join below its link: a word off the freed nodes' words 0 and 1, the
# free list's head and the index's branches reads after the join as after
# the link alone
def jfr.k(+t: IM.Tr, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +k: U32,
  +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  +hp: {T(conj(C0))}, +hy: {{IM.ix.look({I0}, k) == Some{{y}} : Maybe<&2, U32>}}, +j: U32, +hjx0: {NE_('x','j')}, +hjx1: {NE_('(x + 1 : U32)','j')},
  +hjy0: {NE_('y','j')}, +hjy1: {NE_('(y + 1 : U32)','j')}, +hjh: {NE_('P.at_fh()','j')}, +hjb: {T(f'IM.ix.offb({I0}, s, d, j)')}) -> {KG(f'R.join1({H0}, x, y)')}:
{lets}{lets2}  +hbx = {NDB('x')}
  +hby = {NDB('y')}
  %Equal.sym(P.H & U32, P.rd({H0}, (x + 1 : U32)), ({H0}, {GX}), XP.rd_eq(t0, {AA}, (x + 1 : U32))) : {KG('R.jn1.u(_, x, y)')}
  %Equal.sym(P.H & U32, P.rd({H0}, (y + 1 : U32)), ({H0}, {GY}), XP.rd_eq(t0, {AA}, (y + 1 : U32))) : {KG(f'R.jn1.w(_, {GX}, x, y)')}
  %XP.wd(t0, d, (x + 1 : U32), hft, hd32) : {KG(f'P.free(P.free(R.rg.unlink(P.link_xx({H0}, _, {GY}), y), x), y)')}
  %XP.wd(t0, d, (y + 1 : U32), hft, hd32) : {KG(f'P.free(P.free(R.rg.unlink(P.link_xx({H0}, {UU}, _), y), x), y)')}
  %Equal.sym(P.H, {LXX}, {H1p}, heH) : {KG('P.free(P.free(R.rg.unlink(_, y), x), y)')}
  %Equal.sym(P.H & U32, P.rd({H1p}, (y + 3 : U32)), ({H1p}, {GETy3}), XP.rd_eqA({LK2}, {AA}, (y + 3 : U32))) : {KG('P.free(P.free(R.rg.unlink.s(_, y), x), y)')}
  %Equal.sym(U32, {GETy3}, s, hg) : {KG(f'P.free(P.free(X.ix.remove({H1p}, _, y), x), y)')}
  {chain}
"""
sec+=jfr_k()

exec(open('glam/proofgen/gen_keeps_b.py').read())
if os.environ.get('KP_ONLY'):
    open('glam/proofgen/kp/sec.txt','w').write(sec)
    print('section', len(sec.splitlines()))
else:
    p='glam/PROOF.bend'; s=open(p).read()
    def drop(s, head):
        i=s.index(head); j=s.index('\n\n',i); return s[:i]+s[j+2:]
    # the ring's frame proof, superseded
    for h in ('def crk_step(','def crf_step(','def crk.m(','def crk.go(','def crossings_keeps.m(','def Laws.crossings_keeps('):
        s=drop(s,h)
    s=s.rstrip('\n')+'\n'+sec
    open(p,'w').write(s)
    print('keeps', len(sec.splitlines()))
