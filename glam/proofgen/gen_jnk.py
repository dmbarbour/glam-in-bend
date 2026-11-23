# authoring aid: join_keeps restated over the index (glam/LAWS.bend,
# glam/PROOF.bend): R.join's frame, as leave_keeps' with x's removal
# first, y's home read past it; run by regen.sh after gen_ch.py
import os
os.environ['JN_PART']='x'
exec(open('glam/proofgen/gen_jn.py').read())
# jnk.below takes y's lookup in the index without x, as jncase did before
lets=lets.replace('  +hy = '+HYDEL+'\n','')
NE_=lambda a,b: f'{{Nat.is_eq(AD.slot({a}, d), AD.slot({b}, d)) == False{{}} : Bool}}'
SL=lambda a,b: f'Bool.not(Nat.is_eq(AD.slot({a}, d), AD.slot({b}, d)))'
P1=lambda a,i: a if i==0 else f'({a} + {i} : U32)'
OWN=lambda m,j: [SL(P1(m,i),j) for i in range(4)]+['True{}']
RD=lambda h,j: f'Pair.snd(P.H, U32, P.rd({h}, {j}))'
HP_=lambda R: f'P.H{{KM.MG{{KMd.words({R})}}, KMd.vals({R})}}'
def FFULL(R, r, hf):
    return f"ME.subst(P.H, hh => {T(f'AD.full(U32, KMd.words(P.free(hh, {r})), d)')}, {HP_(R)}, {R}, heta3({R}), XL.free_full(KMd.words({R}), KMd.vals({R}), d, {r}, {hf}))"
def FKEEP(R, r, j, hf, h0, h1, hh):
    return (f"ME.subst(P.H, hh => {{{RD(f'P.free(hh, {r})',j)} == {RD('hh',j)} : U32}}, {HP_(R)}, {R}, heta3({R}), "
            f"fk.m(KMd.words({R}), KMd.vals({R}), d, {r}, {j}, {hf}, hd32, {h0}, {h1}, {hh}, LAT.mirror(U32, KMd.words({R})), LAT.mirror(V.Val, KMd.vals({R}))))")
def NEof(m, i, hn):
    return f"MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot({P1(m,i)}, d), AD.slot(j, d)), {proj(OWN(m,'j'),i,hn)})"
NDB=lambda r: f"MS.u32_eq_of_is_eq(P.base({r}), {r}, and_l(U32.is_eq(P.base({r}), {r}), IM.ws.apart(KMd.nw({r}), d) && KMd.off.words(KMd.nw({r}), d, P.at_fh()), XL.layout_ok(N, d, {r}, hN, hB, h{r}N)))"
def b(r,i,h): return f"ME.subst(U32, q => {NE_(P1('q',i),'j')}, {r}, P.base({r}), Equal.sym(U32, P.base({r}), {r}, hb{r}), {h})"
# ---- below x's removal: y's removal and the frees, over any heap's words, mirrored ----
A2='LAT.fromT(U32, t2)'; A2v='LAT.fromT(V.Val, ta2)'
H2w=lambda w,a: f'P.H{{KM.MG{{{w}}}, {a}}}'
G2=lambda w,a, inner=None: f"{{{RD(f'P.free(P.free({inner if inner else f"R.rg.unlink({H2w(w,a)}, y)"}, x), y)','j')} == {RD(H2w(w,a),'j')} : U32}}"
H2=H2w(A2,A2v)
R3=f'X.ix.remove({H2}, s, y)'
GETy3=GET(A2,'(y + 3 : U32)')
hfR3=f'XL.remove_full({A2}, {A2v}, d, s, J, y, ky, hft2, hd32, hr2T, hinv, hlay, hy)'
HG2=trans('U32',[GETy3, WD(f'AD.view(U32, {A2})','(y + 3 : U32)'), 's'],
  [f"Equal.sym(U32, {WD(f'AD.view(U32, {A2})','(y + 3 : U32)')}, {GETy3}, XP.wd(t2, d, (y + 3 : U32), hft2, hd32))", f"XL.look_home({A2}, d, s, J, ky, y, hr2T, hy)"])
chain2=trans('U32',[RD(f'P.free(P.free({R3}, x), y)','j'), RD(f'P.free({R3}, x)','j'), RD(R3,'j'), RD(H2,'j')],
  [FKEEP(f'P.free({R3}, x)','y','j',FFULL(R3,'x',hfR3),b('y',0,NEof('y',0,'hny')),b('y',1,NEof('y',1,'hny')),'hjh'),
   FKEEP(R3,'x','j',hfR3,b('x',0,NEof('x',0,'hnx')),b('x',1,NEof('x',1,'hnx')),'hjh'),
   f'XL.remove_keeps({A2}, {A2v}, d, s, J, y, ky, j, hft2, hd32, hr2T, hinv, hlay, hy, ixoffb(J, s, N, d, j, hsN, hJN, hj), hjh)'])
out=f'''
# R.join's frame over the index (join_keeps;
# cells-freeze.sharing.cursors.index.ring.retire)

# below x's removal: y's removal and both frees keep a word off the
# tracked nodes and the head, over the index J without x
def jnk2(+J: IM.Ix, -w2: Array<U32>, -a2: Array<V.Val>, +d: Nat, +s: U32, +N: List<&2, U32>, +x: U32, +y: U32, +ky: U32,
  +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, +hinv: {T('IM.ix.inv(J)')}, +hlay: {T('IM.ix.lay(J, s, d)')},
  +hy: {{IM.ix.look(J, ky) == Some{{y}} : Maybe<&2, U32>}}, +hsN: {T('RG.has(N, s)')}, +hJN: {T('RG.sub(IM.ix.nodes(J), N)')}, +hxN: {T('RG.has(N, x)')}, +hyN: {T('RG.has(N, y)')},
  +j: U32, +hj: {T('RG.off.nodes(N, d, j)')}, +hjh: {NE_('P.at_fh()','j')},
  hf2: {{AD.full(U32, w2, d) == True{{}} : Bool}}, hr2: {T('IM.ix.real(AD.view(U32, w2), d, s, J)')}, m2: LAT.Mirror(U32, w2), ma2: LAT.Mirror(V.Val, a2)) -> {G2('w2','a2')}:
  (+t2, +e2) = m2
  (+ta2, +ea2) = ma2
  +hft2 = LAP.full_t(U32, w2, t2, d, e2, hf2)
  +hr2T = LAB.subst(Array<U32>, qq => {T('IM.ix.real(AD.view(U32, qq), d, s, J)')}, w2, {A2}, Equal.sym(Array<U32>, {A2}, w2, e2), hr2)
  +hg2 = {HG2}
  +hbx = {NDB('x')}
  +hby = {NDB('y')}
  +hnx = n_at(N, d, j, x, hj, hxN)
  +hny = n_at(N, d, j, y, hj, hyN)
  %e2 : {G2('_','a2')}
  %ea2 : {G2(A2,'_')}
  %Equal.sym(P.H & U32, P.rd({H2}, (y + 3 : U32)), ({H2}, {GETy3}), XP.rd_eq(t2, {A2v}, (y + 3 : U32))) : {G2(A2,A2v,'R.rg.unlink.s(_, y)')}
  %Equal.sym(U32, {GETy3}, s, hg2) : {G2(A2,A2v,f'X.ix.remove({H2}, _, y)')}
  {chain2}
'''
# ---- below the link: the join rewritten, x's removal, then jnk2 ----
KG=lambda h: f'{{{RD(h,"j")} == {RD(H1p,"j")} : U32}}'
R2=f'X.ix.remove({H1p}, s, x)'
R2E=HP_(R2)
JN2=f'IM.ix.del({I0}, x, kx)'
hfR2=f'XL.remove_full({LK2}, {AA}, d, s, {I0}, x, kx, {full1}, hd32, {real1}, hp1, hp2, hx)'
hrR2=f'XL.remove_tree({LK2}, {AA}, d, s, {I0}, x, kx, {full1}, hd32, {real1}, hp1, hp2, hx)'
J2call=(f"jnk2({JN2}, KMd.words({R2}), KMd.vals({R2}), d, s, N, x, y, ky, hd32, hN, hB, XL.del_inv({I0}, x, kx, hp1, hx), XL.del_lay({I0}, s, x, kx, d, hp2), hy, hsN, XL.del_sub({I0}, x, kx, N, hp14), hxN, hyN, "
        f"j, hj, hjh, {hfR2}, {hrR2}, LAT.mirror(U32, KMd.words({R2})), LAT.mirror(V.Val, KMd.vals({R2})))")
belowchain=trans('U32',[RD(f'P.free(P.free(R.rg.unlink({R2}, y), x), y)','j'), RD(R2,'j'), RD(H1p,'j')],
  [f"ME.subst(P.H, hh => {{{RD('P.free(P.free(R.rg.unlink(hh, y), x), y)','j')} == {RD('hh','j')} : U32}}, {R2E}, {R2}, heta3({R2}), {J2call})",
   f"XL.remove_keeps({LK2}, {AA}, d, s, {I0}, x, kx, j, {full1}, hd32, {real1}, hp1, hp2, hx, ixoffb({I0}, s, N, d, j, hsN, hp14, hj), hjh)"])
JPR=f"+j: U32, +hj: {T('RG.off.nodes(N, d, j)')}, +hjh: {NE_('P.at_fh()','j')}"
out+=f'''
# a join below its link: x's removal, y's, the frees
def jnk.below({CS},
  +hp: {T(conj(C0))}, +hx: {{IM.ix.look({I0}, kx) == Some{{x}} : Maybe<&2, U32>}}, +hy: {{IM.ix.look({J0}, ky) == Some{{y}} : Maybe<&2, U32>}}, {JPR}) -> {KG(f'R.join({H0}, x, y)')}:
{lets}  %Equal.sym(P.H & U32, P.rd({H0}, (x + 1 : U32)), ({H0}, {GX}), XP.rd_eq(t0, {AA}, (x + 1 : U32))) : {KG('R.jn.u(_, x, y)')}
  %Equal.sym(P.H & U32, P.rd({H0}, (y + 1 : U32)), ({H0}, {GY}), XP.rd_eq(t0, {AA}, (y + 1 : U32))) : {KG(f'R.jn.w(_, {GX}, x, y)')}
  %XP.wd(t0, d, (x + 1 : U32), hft, hd32) : {KG(f'P.free(P.free(R.rg.unlink(R.rg.unlink(P.link_xx({H0}, _, {GY}), x), y), x), y)')}
  %XP.wd(t0, d, (y + 1 : U32), hft, hd32) : {KG(f'P.free(P.free(R.rg.unlink(R.rg.unlink(P.link_xx({H0}, {UU}, _), x), y), x), y)')}
  %Equal.sym(P.H, {LXX}, {H1p}, heH) : {KG('P.free(P.free(R.rg.unlink(R.rg.unlink(_, x), y), x), y)')}
  %Equal.sym(P.H & U32, P.rd({H1p}, (x + 3 : U32)), ({H1p}, {GETx3}), XP.rd_eqA({LK2}, {AA}, (x + 3 : U32))) : {KG('P.free(P.free(R.rg.unlink(R.rg.unlink.s(_, x), y), x), y)')}
  %Equal.sym(U32, {GETx3}, s, hgx) : {KG(f'P.free(P.free(R.rg.unlink(X.ix.remove({H1p}, _, x), y), x), y)')}
  {belowchain}
'''
KGOAL=lambda h: f'{{{RD(h,"j")} == {RD(H0,"j")} : U32}}'
JOIN=f'R.join({H0}, x, y)'
JPR2=JPR+f", +hju: {T(f'KMd.off.port(d, {UU}, j)')}, +hjw: {T(f'KMd.off.port(d, {WW}, j)')}"
out+=f'''
# a join: every word off the tracked nodes', the free list's head and the
# two faced ports' link words as it was
def jnk.t({CS},
  +hp: {T(conj(C0))}, +hx: {{IM.ix.look({I0}, kx) == Some{{x}} : Maybe<&2, U32>}}, +hy0: {{IM.ix.look({I0}, ky) == Some{{y}} : Maybe<&2, U32>}}, +hxy0: {{U32.is_eq(x, y) == False{{}} : Bool}}, {JPR2}) -> {KGOAL(JOIN)}:
  {trans('U32',[RD(JOIN,'j'), RD(H1p,'j'), RD(LXX,'j'), RD(H0,'j')],
    [f"jnk.below(t, t0, ta, d, s, ps, L, F, N, x, y, kx, ky, hft, hd32, hN, hB, hp, hx, Equal.trans(Maybe<&2, U32>, IM.ix.look({J0}, ky), IM.ix.look({I0}, ky), Some{{y}}, XL.look_del_other({I0}, s, x, kx, ky, d, {proj(C0,1,'hp')}, {proj(C0,2,'hp')}, hx, keys_ne({I0}, kx, ky, x, y, hx, hy0, hxy0)), hy0), j, hj, hjh)",
     f"Equal.cong(P.H, U32, hh => {RD('hh','j')}, {H1p}, {LXX}, Equal.sym(P.H, {LXX}, {H1p}, {EH}))",
     f"HL.link_keeps({A0}, {AA}, d, {UU}, {WW}, j, hft, hd32, hju, hjw)"])}

def jnk.k(I: IM.Ix, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +kx: U32, +ky: U32,
  +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  +hp: {T(f'RG.px.ok({V0}, d, s, I, ps, L, F, N)')}, +hx: {{IM.ix.look(I, kx) == Some{{x}} : Maybe<&2, U32>}}, +hy: {{IM.ix.look(I, ky) == Some{{y}} : Maybe<&2, U32>}}, +hxy: {{U32.is_eq(x, y) == False{{}} : Bool}}, {JPR2}) -> {KGOAL(JOIN)}:
  match I:
    case IM.Ept{{}}:
      Empty.absurd({KGOAL(JOIN)}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, mm => XP.is_some(mm), None{{}}, Some{{x}}, hx)))
    case IM.Has{{+t}}:
      jnk.t(t, t0, ta, d, s, ps, L, F, N, x, y, kx, ky, hft, hd32, hN, hB, hp, hx, hy, hxy, j, hj, hjh, hju, hjw)
'''
HWA=lambda w,a: f'P.H{{KM.MG{{{w}}}, {a}}}'
KGm=lambda w,a: f'{{{RD(f"R.join({HWA(w,a)}, x, y)","j")} == {RD(HWA(w,a),"j")} : U32}}'
WDw=lambda w,i: f'KMd.word(AD.view(U32, {w}), d, {i})'
out+=f'''
def jnk.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +kx: U32, +ky: U32, +j: U32,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  hp: {T('RG.px.ok(AD.view(U32, w), d, s, I, ps, L, F, N)')}, +hx: {{IM.ix.look(I, kx) == Some{{x}} : Maybe<&2, U32>}}, +hy: {{IM.ix.look(I, ky) == Some{{y}} : Maybe<&2, U32>}}, +hxy: {{U32.is_eq(x, y) == False{{}} : Bool}},
  +hj: {T('RG.off.nodes(N, d, j)')}, +hjh: {NE_('P.at_fh()','j')}, hju: {T(f"KMd.off.port(d, {WDw('w','(x + 1 : U32)')}, j)")}, hjw: {T(f"KMd.off.port(d, {WDw('w','(y + 1 : U32)')}, j)")},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) -> {KGm('w','a')}:
  (+t0, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, {A0}, w, e)
  %e : {KGm('_','a')}
  %ea : {KGm(A0,'_')}
  jnk.k(I, t0, ta, d, s, ps, L, F, N, x, y, kx, ky, hft, hd32, hN, hB, LAB.subst(Array<U32>, qq => {T('RG.px.ok(AD.view(U32, qq), d, s, I, ps, L, F, N)')}, w, {A0}, ew, hp), hx, hy, hxy, j, hj, hjh,
    LAB.subst(Array<U32>, qq => {T(f"KMd.off.port(d, {WDw('qq','(x + 1 : U32)')}, j)")}, w, {A0}, ew, hju), LAB.subst(Array<U32>, qq => {T(f"KMd.off.port(d, {WDw('qq','(y + 1 : U32)')}, j)")}, w, {A0}, ew, hjw))

def Laws.join_keeps(w, a, d, s, I, ps, L, F, N, x, y, kx, ky, j, hf, hd32, hN, hB, hp, hx, hy, hxy, hj, hjh, hju, hjw):
  jnk.m(w, a, d, s, I, ps, L, F, N, x, y, kx, ky, j, hf, hd32, hN, hB, hp, hx, hy, hxy, hj, hjh, hju, hjw, LAT.mirror(U32, w), LAT.mirror(V.Val, a))
'''
LAWK='''# LAW: two cursors x and y of the index joined (R.join), on join_pend's
# premises, leave every word as it was but the tracked nodes' (N: the
# live nodes, the index's, the free list's), the free list's head, and
# the link words of the two ports x and y faced, a static having none:
# the join's frame, for the materializer's frontier, which joins two
# cursors directly (cells-freeze.sharing.cursors.index.ring.retire).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
# Record: cursors-indexed
law join_keeps:
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
  for +y: U32
  for +kx: U32
  for +ky: U32
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, ps, L, F, N) == True{} : Bool}
  for hx: {IM.ix.look(I, kx) == Some{x} : Maybe<&2, U32>}
  for hy: {IM.ix.look(I, ky) == Some{y} : Maybe<&2, U32>}
  for hxy: {U32.is_eq(x, y) == False{} : Bool}
  for hj: {RG.off.nodes(N, d, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  for hju: {KMd.off.port(d, KMd.word(AD.view(U32, w), d, (x + 1 : U32)), j) == True{} : Bool}
  for hjw: {KMd.off.port(d, KMd.word(AD.view(U32, w), d, (y + 1 : U32)), j) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(R.join(P.H{KM.MG{w}, a}, x, y), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}
'''
if os.environ.get('JNK_ONLY'):
    i=out.index('def Laws.join_keeps(')
    open('glam/proofgen/kp/sec.txt','w').write(out[:i])
    print('jnk', len(out.splitlines()))
else:
    p='glam/PROOF.bend'; s=open(p).read()
    def drop(s, head):
        i=s.index(head); j=s.index('\n\n',i); return s[:i]+s[j+2:]
    if 'def Laws.join_keeps(w, a, d, s, t,' in s:
        s=drop(s,'def Laws.join_keeps(')
    assert 'def jnk.t(' not in s
    s=s.rstrip('\n')+'\n'+out
    open(p,'w').write(s)
    lp='glam/LAWS.bend'; l=open(lp).read()
    if 'law join_keeps:\n  for w: Array<U32>\n  for a: Array<V.Val>\n  for +d: Nat\n  for +s: U32\n  for +t:' in l:
        j0=l.index('law join_keeps:')
        i=l.rfind('\n\n', 0, j0)+2
        j=l.index('\n\n', j0)
        l=l[:i]+LAWK.rstrip('\n')+l[j:]
        open(lp,'w').write(l)
    print('jnk', len(out.splitlines()))
