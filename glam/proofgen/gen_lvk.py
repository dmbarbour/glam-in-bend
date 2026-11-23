# authoring aid: leave_keeps restated over the index (glam/LAWS.bend,
# glam/PROOF.bend): the leave's frame, as the join's in a crossing (jfr.k,
# jk.t), on leave_pend's premises; run by regen.sh after gen_cfi.py
import os
os.environ['LV_PART']='x'
exec(open('glam/proofgen/gen_lv.py').read())
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
LEAVE=f'R.leave({H0}, p, y)'
KG=lambda h: f'{{{RD(h,"j")} == {RD(H1p,"j")} : U32}}'
R2=f'X.ix.remove({H1p}, s, y)'
hfR2=f'XL.remove_full({LK2}, {AA}, d, s, {I0}, y, k, {full1}, hd32, {real1}, hp1, hp2, hy)'
def b(r,i,h): return f"ME.subst(U32, q => {NE_(P1('q',i),'j')}, {r}, P.base({r}), Equal.sym(U32, P.base({r}), {r}, hb{r}), {h})"
chain=trans('U32',[RD(f'P.free({R2}, y)','j'), RD(R2,'j'), RD(H1p,'j')],
  [FKEEP(R2,'y','j',hfR2,b('y',0,'hjy0'),b('y',1,'hjy1'),'hjh'),
   f'XL.remove_keeps({LK2}, {AA}, d, s, {I0}, y, k, j, {full1}, hd32, {real1}, hp1, hp2, hy, hjb, hjh)'])
NDB=lambda r: f"MS.u32_eq_of_is_eq(P.base({r}), {r}, and_l(U32.is_eq(P.base({r}), {r}), IM.ws.apart(KMd.nw({r}), d) && KMd.off.words(KMd.nw({r}), d, P.at_fh()), XL.layout_ok(N, d, {r}, hN, hB, h{r}N)))"
out=f'''
# The leave's frame over the index (leave_keeps;
# cells-freeze.sharing.cursors.index.ring.leave)

# a leave below its link: a word off the freed node's words 0 and 1, the
# free list's head and the index's branches reads after the leave as after
# the link alone
def lvfr.k({LCP},
  +hp: {T(conj(C0))}, +hy: {{IM.ix.look({I0}, k) == Some{{y}} : Maybe<&2, U32>}}, {PREMP},
  +j: U32, +hjy0: {NE_('y','j')}, +hjy1: {NE_('(y + 1 : U32)','j')}, +hjh: {NE_('P.at_fh()','j')}, +hjb: {T(f'IM.ix.offb({I0}, s, d, j)')}) -> {KG(LEAVE)}:
{lets}  +hby = {NDB('y')}
  %Equal.sym(P.H & U32, P.rd({H0}, (y + 1 : U32)), ({H0}, {GY}), XP.rd_eq(t0, {AA}, (y + 1 : U32))) : {KG('R.lv.w(_, p, y)')}
  %XP.wd(t0, d, (y + 1 : U32), hft, hd32) : {KG(f'P.free(R.rg.unlink(P.link_xx({H0}, p, _), y), y)')}
  %Equal.sym(P.H, {LXX}, {H1p}, heH) : {KG('P.free(R.rg.unlink(_, y), y)')}
  %Equal.sym(P.H & U32, P.rd({H1p}, (y + 3 : U32)), ({H1p}, {GETy3}), XP.rd_eqA({LK2}, {AA}, (y + 3 : U32))) : {KG('P.free(R.rg.unlink.s(_, y), y)')}
  %Equal.sym(U32, {GETy3}, s, hg) : {KG(f'P.free(X.ix.remove({H1p}, _, y), y)')}
  {chain}
'''
KGOAL=lambda h: f'{{{RD(h,"j")} == {RD(H0,"j")} : U32}}'
JPR=f"+j: U32, +hj: {T('RG.off.nodes(N, d, j)')}, +hjh: {NE_('P.at_fh()','j')}, +hjp: {T('KMd.off.port(d, p, j)')}, +hjw: {T(f'KMd.off.port(d, {WW}, j)')}"
lchain=trans('U32',[RD(LEAVE,'j'), RD(H1p,'j'), RD(LXX,'j'), RD(H0,'j')],
    [f"lvfr.k(t, t0, ta, d, s, ps, L, F, N, p, y, k, hft, hd32, hN, hB, hp, hy, hpo, hpk, j, {NEof('y',0,'hny')}, {NEof('y',1,'hny')}, hjh, ixoffb({I0}, s, N, d, j, hsN, {proj(C0,14,'hp')}, hj))",
     f"Equal.cong(P.H, U32, hh => {RD('hh','j')}, {H1p}, {LXX}, Equal.sym(P.H, {LXX}, {H1p}, {EH}))",
     f"HL.link_keeps({A0}, {AA}, d, p, {WW}, j, hft, hd32, hjp, hjw)"])
out+=f'''
# a leave: every word off the tracked nodes', the free list's head and the
# two ports' link words as it was
def lvk.t({LCP},
  +hp: {T(conj(C0))}, +hy: {{IM.ix.look({I0}, k) == Some{{y}} : Maybe<&2, U32>}}, {PREMP}, {JPR}) -> {KGOAL(LEAVE)}:
  +hsL = and_l(RG.has(L, s), RG.sub({LV(I0)}, L), {proj(C0,3,'hp')})
  +hyL = sub_has({LV(I0)}, L, y, and_r(RG.has(L, s), RG.sub({LV(I0)}, L), {proj(C0,3,'hp')}), XL.look_leaf({I0}, k, y, hy))
  +hsN = sub_has(L, N, s, {proj(C0,12,'hp')}, hsL)
  +hyN = sub_has(L, N, y, {proj(C0,12,'hp')}, hyL)
  +hny = n_at(N, d, j, y, hj, hyN)
  {lchain}

def lvk.k(I: IM.Ix, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +p: U32, +y: U32, +k: U32,
  +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  +hp: {T(f'RG.px.ok({V0}, d, s, I, ps, L, F, N)')}, +hy: {{IM.ix.look(I, k) == Some{{y}} : Maybe<&2, U32>}}, {PREMP}, {JPR}) -> {KGOAL(LEAVE)}:
  match I:
    case IM.Ept{{}}:
      Empty.absurd({KGOAL(LEAVE)}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, mm => XP.is_some(mm), None{{}}, Some{{y}}, hy)))
    case IM.Has{{+t}}:
      lvk.t(t, t0, ta, d, s, ps, L, F, N, p, y, k, hft, hd32, hN, hB, hp, hy, hpo, hpk, j, hj, hjh, hjp, hjw)
'''
HWA=lambda w,a: f'P.H{{KM.MG{{{w}}}, {a}}}'
KGm=lambda w,a: f'{{{RD(f"R.leave({HWA(w,a)}, p, c)","j")} == {RD(HWA(w,a),"j")} : U32}}'
out+=f'''
def lvk.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +p: U32, +c: U32, +k: U32, +j: U32,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  hp: {T('RG.px.ok(AD.view(U32, w), d, s, I, ps, L, F, N)')}, +hc: {{IM.ix.look(I, k) == Some{{c}} : Maybe<&2, U32>}}, +hpo: {T('RG.po.all(p, [], d, N)')},
  +hj: {T('RG.off.nodes(N, d, j)')}, +hjh: {NE_('P.at_fh()','j')}, +hjp: {T('KMd.off.port(d, p, j)')}, hjw: {T('KMd.off.port(d, KMd.word(AD.view(U32, w), d, (c + 1 : U32)), j)')},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) -> {KGm('w','a')}:
  (+t0, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, {A0}, w, e)
  +hpT = LAB.subst(Array<U32>, qq => {T('RG.px.ok(AD.view(U32, qq), d, s, I, ps, L, F, N)')}, w, {A0}, ew, hp)
  +hpk = port_of_po(L, p, [], d, N, hpo, {proj(PXOK(f'AD.view(U32, {A0})', 'I', 'ps', 'L', 'F', 'N'),12,'hpT')}, none_nil(L), hN, hB)
  %e : {KGm('_','a')}
  %ea : {KGm(A0,'_')}
  lvk.k(I, t0, ta, d, s, ps, L, F, N, p, c, k, hft, hd32, hN, hB, hpT, hc, hpo, hpk,
    j, hj, hjh, hjp, LAB.subst(Array<U32>, qq => {T('KMd.off.port(d, KMd.word(AD.view(U32, qq), d, (c + 1 : U32)), j)')}, w, {A0}, ew, hjw))

def Laws.leave_keeps(w, a, d, s, I, ps, L, F, N, p, c, k, j, hf, hd32, hN, hB, hp, hc, hpo, hj, hjh, hjp, hjw):
  lvk.m(w, a, d, s, I, ps, L, F, N, p, c, k, j, hf, hd32, hN, hB, hp, hc, hpo, hj, hjh, hjp, hjw, LAT.mirror(U32, w), LAT.mirror(V.Val, a))
'''
out=out.replace('IM.ix.leaves(IM.Has{t})','IM.ix.leaves(IM.Has{t})')
LAWK='''# LAW: a cursor c the index finds at k leaving (R.leave), a port p linked
# in its place, on leave_pend's premises, leaves every word as it was but
# the tracked nodes' (N: the live nodes, the index's, the free list's),
# the free list's head, and the two ports' link words, p's and the one c
# faced, a static having none: the leave's frame
# (cells-freeze.sharing.cursors.index.ring.leave; the frame law leave
# lacked: .host.witness.audit).
# Record: copy-reduced-function-nets
# Record: hub-laws-reused
# Record: cursors-indexed
law leave_keeps:
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
  for +j: U32
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, ps, L, F, N) == True{} : Bool}
  for hc: {IM.ix.look(I, k) == Some{c} : Maybe<&2, U32>}
  for hpo: {RG.po.all(p, Nil{}, d, N) == True{} : Bool}
  for hj: {RG.off.nodes(N, d, j) == True{} : Bool}
  for hjh: {Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)) == False{} : Bool}
  for hjp: {KMd.off.port(d, p, j) == True{} : Bool}
  for hjw: {KMd.off.port(d, KMd.word(AD.view(U32, w), d, (c + 1 : U32)), j) == True{} : Bool}
  {Pair.snd(P.H, U32, P.rd(R.leave(P.H{KM.MG{w}, a}, p, c), j)) == Pair.snd(P.H, U32, P.rd(P.H{KM.MG{w}, a}, j)) : U32}
'''
if os.environ.get('LVK_ONLY'):
    i=out.index('def Laws.leave_keeps(')
    open('glam/proofgen/kp/sec.txt','w').write(out[:i])
    print('lvk', len(out.splitlines()))
else:
    p='glam/PROOF.bend'; s=open(p).read()
    def drop(s, head):
        i=s.index(head); j=s.index('\n\n',i); return s[:i]+s[j+2:]
    if 'def leave_keeps.x(' in s:
        for h in ('def leave_keeps.x(','def leave_keeps.m(','def Laws.leave_keeps('):
            s=drop(s,h)
    assert 'def lvk.t(' not in s
    s=s.rstrip('\n')+'\n'+out
    open(p,'w').write(s)
    lp='glam/LAWS.bend'; l=open(lp).read()
    if 'law leave_keeps:\n  for w: Array<U32>\n  for a: Array<V.Val>\n  for +d: Nat\n  for +s: U32\n  for +t:' in l:
        i=l.index('# LAW: a cursor c of a ring exact with its nodes leaving it, the port it\n# faced linked to a port p faceable by the ring\'s members, leaves every')
        j=l.index('\n\n', l.index('law leave_keeps:'))
        l=l[:i]+LAWK.rstrip('\n')+l[j:]
        open(lp,'w').write(l)
    print('lvk', len(out.splitlines()))
