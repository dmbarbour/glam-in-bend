# authoring aid: join_pend over the index (glam/PROOF.bend): two cursors
# of the index joined (R.join), from the join1 generators: the link as
# join1's (link_live), x's removal here, then join1's removal and frees
# (jrm) over the index without x
import re, os
exec(open('glam/proofgen/gen_j1c.py').read().split("# ---- the case: facts, the link, the goal's rewrites ----")[0])
out=''
I0='IM.Has{t}'; J0=f'IM.ix.del({I0}, x, kx)'; F1=f'IM.mb.cons(IM.ix.par({I0}, x, kx), F)'
NDt='IM.tr.nodes(t)'
GOALJ=lambda v,J,Fl: GOAL(v, f'IM.ix.del({J}, y, ky)', f'IM.mb.cons(IM.ix.par({J}, y, ky), {Fl})')
# the facts carried past x's removal: over the index J without x and the
# free list Fl with x's removal's parent
JB=lambda J,Fl: [f'IM.ix.inv({J})', f'IM.ix.lay({J}, s, d)', f'RG.sub(IM.ix.leaves({J}), RG.without(L, x))', f'RG.none.in(ps, Con{{s, IM.ix.nodes({J})}})',
  f'RG.none.in(L, IM.ix.branches({J}))', f'RG.sub(IM.ix.nodes({J}), N)', f'Bool.not(RG.has(IM.ix.nodes({J}), x))']
F1B=lambda J,Fl: [f'RG.none.in({Fl}, Con{{s, IM.ix.nodes({J})}})', f'RG.none.in({Fl}, L)', f'RG.sub({Fl}, N)', f'RG.distinct({Fl})', f'Bool.not(RG.has({Fl}, y))', f'Bool.not(RG.has({Fl}, x))']
JBF=lambda J,Fl: JB(J,Fl)+F1B(J,Fl)
OT=['Bool.not(U32.is_eq(x, y))', 'RG.has(N, x)', 'RG.has(N, y)', 'RG.has(N, s)', 'Bool.not(U32.is_eq(x, s))', 'Bool.not(U32.is_eq(y, s))',
  f'RG.sub({L2}, L)', f'Bool.not(RG.has({L2}, x))', f'Bool.not(RG.has({L2}, y))', f'RG.sub({L2}, N)', f'RG.has({L2}, s)', f'RG.sub(ps, {L2})', 'RG.distinct(ps)', 'RG.has(L, y)']
# ---- the free list after x's removal ----
def npl_body(pp):
    M=f'Con{{s, IM.ix.nodes({J0})}}'
    hSD=f"and_intro(RG.has(Con{{s, {NDt}}}, s), RG.sub(IM.ix.nodes({J0}), Con{{s, {NDt}}}), has_head(s, {NDt}), sub_cons_r(IM.ix.nodes({J0}), s, {NDt}, XL.del_sub({I0}, x, kx, {NDt}, sub_refl({NDt}))))"
    if pp:
        Fl=f'Con{{{pp}, F}}'
        lets=f'''      +hpb = XL.par_branch({I0}, x, kx, {pp}, he)
      +hpn = sub_has(IM.tr.branches(t), {NDt}, {pp}, br_sub(t), hpb)
      +hpN = sub_has({NDt}, N, {pp}, hIN, hpn)
      +hpL = none_notin(L, IM.tr.branches(t), {pp}, hbr, hpb)
      +hpF = none_notin(F, Con{{s, {NDt}}}, {pp}, hfn, has_cons(s, {NDt}, {pp}, hpn))
      +hpy = nhas(IM.tr.branches(t), {pp}, y, hpb, hyB)
      +hpx = nhas(IM.tr.branches(t), {pp}, x, hpb, hxB)
      +hps = nhas({NDt}, {pp}, s, hpn, hst)
      +hDA = ME.subst(Maybe<&2, U32>, mm => {T(f"RG.none.in(IM.mb.cons(mm, [x]), IM.ix.nodes({J0}))")}, IM.ix.par({I0}, x, kx), Some{{{pp}}}, he, XL.del_absent({I0}, s, d, x, kx, hlay, hx))
      +hpD = MB.eq_false_of_not_eq_true(RG.has(IM.ix.nodes({J0}), {pp}), and_l(Bool.not(RG.has(IM.ix.nodes({J0}), {pp})), RG.none.in([x], IM.ix.nodes({J0})), hDA))
'''
        prfs=[f"and_intro(Bool.not(RG.has({M}, {pp})), RG.none.in(F, {M}), not_t(RG.has({M}, {pp}), or_ff(U32.is_eq(s, {pp}), RG.has(IM.ix.nodes({J0}), {pp}), ueq_ne({pp}, s, hps), hpD)), none_sub(F, Con{{s, {NDt}}}, {M}, hfn, {hSD}))",
          f"and_intro(Bool.not(RG.has(L, {pp})), RG.none.in(F, L), not_t(RG.has(L, {pp}), hpL), hFL)",
          f"and_intro(RG.has(N, {pp}), RG.sub(F, N), hpN, hFN)",
          f"and_intro(Bool.not(RG.has(F, {pp})), RG.distinct(F), not_t(RG.has(F, {pp}), hpF), hFd)",
          f"not_t(RG.has({Fl}, y), or_ff(U32.is_eq({pp}, y), RG.has(F, y), hpy, hyF))",
          f"not_t(RG.has({Fl}, x), or_ff(U32.is_eq({pp}, x), RG.has(F, x), hpx, hxF))"]
    else:
        Fl='F'; lets=''
        prfs=[f"none_sub(F, Con{{s, {NDt}}}, {M}, hfn, {hSD})", 'hFL', 'hFN', 'hFd', 'not_t(RG.has(F, y), hyF)', 'not_t(RG.has(F, x), hxF)']
    return lets+f'      {intro(F1B(J0,Fl),prfs)}\n'
out+=f'''
# The pending placeholders over the index: a join of two cursors
# ==============================================================
#
# cells-freeze.sharing.cursors.index.ring.leave: join_pend, the link as
# join1_pend's, x's removal, then join1_pend's removal of y and frees
# (jrm) over the index without x, its parent pushed on the free list.

# what the free list after x's removal holds, the removal's parent m if any
def jnpl(+m: Maybe<&2, U32>, +t: IM.Tr, +d: Nat, +s: U32, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +kx: U32,
  +hbr: {T('RG.none.in(L, IM.tr.branches(t))')}, +hfn: {T(f'RG.none.in(F, Con{{s, {NDt}}})')}, +hFL: {T('RG.none.in(F, L)')}, +hFN: {T('RG.sub(F, N)')}, +hFd: {T('RG.distinct(F)')},
  +hyF: {F_('RG.has(F, y)')}, +hxF: {F_('RG.has(F, x)')}, +hIN: {T(f'RG.sub({NDt}, N)')}, +hst: {F_(f'RG.has({NDt}, s)')}, +hyB: {F_('RG.has(IM.tr.branches(t), y)')}, +hxB: {F_('RG.has(IM.tr.branches(t), x)')},
  +hlay: {T(f'IM.ix.lay({I0}, s, d)')}, +hx: {{IM.ix.look({I0}, kx) == Some{{x}} : Maybe<&2, U32>}}, +he: {{IM.ix.par({I0}, x, kx) == m : Maybe<&2, U32>}}) -> {T(conj(F1B(J0,'IM.mb.cons(m, F)')))}:
  match m:
    case Some{{+pp}}:
{npl_body('pp')}    case None{{}}:
{npl_body(None)}'''
# ---- y's removal and the frees, over an index J without x ----
H2=f'P.H{{KM.MG{{LAT.fromT(U32, t2)}}, {AA}}}'; A2='LAT.fromT(U32, t2)'
G3=lambda J,w: GOALJ(f'AD.view(U32, KMd.words(P.free(P.free(R.rg.unlink(P.H{{KM.MG{{{w}}}, {AA}}}, y), x), y)))', J, 'F1')
GETy3=GET(A2,'(y + 3 : U32)')
JN3S=f'''J: IM.Ix, +F1: List<&2, U32>, +t2: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +ky: U32,
  +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, +hJB: {T(conj(JBF('J','F1')))}, +hO: {T(conj(OT))}, +hy: {{IM.ix.look(J, ky) == Some{{y}} : Maybe<&2, U32>}}'''
J1='IM.Has{t1}'; NDt1='IM.tr.nodes(t1)'; Id1=f'IM.ix.del({J1}, y, ky)'; Pa1=f'IM.ix.par({J1}, y, ky)'
jb=lambda i: proj(JBF(J1,'F1'),i,'hJB'); ot=lambda i: proj(OT,i,'hO')
MB1=[f'XL.del_inv({J1}, y, ky, jinv, hy)', f'XL.del_lay({J1}, s, y, ky, d, jlay)',
  f"and_intro(RG.has({L2}, s), RG.sub(IM.ix.leaves({Id1}), {L2}), {ot(10)}, ME.subst(List<&2, U32>, qq => {T(f'RG.sub(qq, {L2})')}, RG.without(IM.ix.leaves({J1}), y), IM.ix.leaves({Id1}), Equal.sym(List<&2, U32>, IM.ix.leaves({Id1}), RG.without(IM.ix.leaves({J1}), y), XL.del_leaves({J1}, s, y, ky, d, jlay, hy)), "
  f"sub_w1(RG.without(IM.ix.leaves({J1}), y), RG.without(L, x), y, sub_trans(RG.without(IM.ix.leaves({J1}), y), IM.ix.leaves({J1}), RG.without(L, x), sub_without(IM.ix.leaves({J1}), y), {jb(2)}), notin_without(IM.ix.leaves({J1}), y))))",
  ot(11),
  f"none_sub(ps, Con{{s, {NDt1}}}, Con{{s, IM.ix.nodes({Id1})}}, {jb(3)}, and_intro(RG.has(Con{{s, {NDt1}}}, s), RG.sub(IM.ix.nodes({Id1}), Con{{s, {NDt1}}}), has_head(s, {NDt1}), sub_cons_r(IM.ix.nodes({Id1}), s, {NDt1}, XL.del_sub({J1}, y, ky, {NDt1}, sub_refl({NDt1})))))",
  ot(12), f"none_sub({L2}, IM.ix.branches({J1}), IM.ix.branches({Id1}), hL2b1, XL.del_bsub({J1}, y, ky, IM.ix.branches({J1}), sub_refl(IM.ix.branches({J1}))))", ot(9), f'XL.del_sub({J1}, y, ky, N, {jb(5)})']
hyD1=f"none_last({Pa1}, y, IM.ix.nodes({Id1}), XL.del_absent({J1}, s, d, y, ky, jlay, hy))"
hxD1=f"notin_sub(IM.ix.nodes({Id1}), {NDt1}, x, XL.del_sub({J1}, y, ky, {NDt1}, sub_refl({NDt1})), hxt1)"
DS=f'XL.del_sub({J1}, y, ky, N, {jb(5)})'
QF1=['XL.layout_ok(N, d, x, hN, hB, hxN)', 'XL.layout_ok(N, d, y, hN, hB, hyN)',
  f'offr_n0({Id1}, s, d, x, N, hN, {DS}, hxN, hsN, {hxD1}, hxs)', f'offr_n1({Id1}, s, d, x, N, hN, {DS}, hxN, hsN, {hxD1}, hxs)',
  f'offr_n0({Id1}, s, d, y, N, hN, {DS}, hyN, hsN, {hyD1}, hys)', f'offr_n1({Id1}, s, d, y, N, hN, {DS}, hyN, hsN, {hyD1}, hys)',
  f'offr_hix({Id1}, s, d, XL.del_lay({J1}, s, y, ky, d, jlay))',
  f'ones_b0({L2}, N, d, x, hL2N, hN, hxN, hx2)', f'ones_b1({L2}, N, d, x, hL2N, hN, hxN, hx2)', f'ones_b0({L2}, N, d, y, hL2N, hN, hyN, hy2)', f'ones_b1({L2}, N, d, y, hL2N, hN, hyN, hy2)',
  f'ones_fh({L2}, N, d, hL2N, hN)']
QFj=['IM.nd.ok(x, d)', 'IM.nd.ok(y, d)', OFX(Id1,'x'), OFX(Id1,'(x + 1 : U32)'), OFX(Id1,'y'), OFX(Id1,'(y + 1 : U32)'), OFX(Id1,'P.at_fh()'),
  ONS('x'), ONS('(x + 1 : U32)'), ONS('y'), ONS('(y + 1 : U32)'), ONS('P.at_fh()')]
assert QFj==QFt(Id1)
nf=lambda i: f'MB.eq_false_of_not_eq_true({OT[i][len("Bool.not("):-1]}, {ot(i)})'
HG2=trans('U32',[GETy3, WD(f'AD.view(U32, {A2})','(y + 3 : U32)'), 's'],
  [f"Equal.sym(U32, {WD(f'AD.view(U32, {A2})','(y + 3 : U32)')}, {GETy3}, XP.wd(t2, d, (y + 3 : U32), hft2, hd32))", f"XL.look_home({A2}, d, s, {J1}, ky, y, hr2, hy)"])
out+=f'''
# y's removal and the frees, the index J without x a tree
def jn3({JN3S},
  +hft2: {{AD.full(U32, {A2}, d) == True{{}} : Bool}}, +hr2: {T(f'IM.ix.real(AD.view(U32, {A2}), d, s, J)')},
  +hc2: {T(f'KMd.chain(F1, AD.view(U32, {A2}), d, KMd.word(AD.view(U32, {A2}), d, P.at_fh()))')}, +htr2: {T(conj(TRI(f'AD.view(U32, {A2})')))}) -> {G3('J',A2)}:
  match J:
    case IM.Ept{{}}:
      Empty.absurd({G3('IM.Ept{}',A2)}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, m => XP.is_some(m), None{{}}, Some{{y}}, hy)))
    case IM.Has{{+t1}}:
      +jinv = {jb(0)}
      +jlay = {jb(1)}
      +hxt1 = MB.eq_false_of_not_eq_true(RG.has({NDt1}, x), {jb(6)})
      +hyF1 = MB.eq_false_of_not_eq_true(RG.has(F1, y), {jb(11)})
      +hxF1 = MB.eq_false_of_not_eq_true(RG.has(F1, x), {jb(12)})
      +hxy = {nf(0)}
      +hxN = {ot(1)}
      +hyN = {ot(2)}
      +hsN = {ot(3)}
      +hxs = {nf(4)}
      +hys = {nf(5)}
      +hs1 = {ot(6)}
      +hx2 = {nf(7)}
      +hy2 = {nf(8)}
      +hL2N = {ot(9)}
      +hst1 = XP.absent_nodes(t1, d, s, and_l(IM.tr.offn(t1, d, s), IM.tr.lay(t1, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t1, d, s) && IM.tr.lay(t1, d), jlay)))
      +hyB1 = none_mem(L, IM.tr.branches(t1), y, {jb(4)}, {ot(13)})
      +hsF1 = none_has(F1, Con{{s, {NDt1}}}, s, {jb(7)}, has_head(s, {NDt1}))
      +hL2b1 = none_subl({L2}, L, IM.tr.branches(t1), hs1, {jb(4)})
      +hg2 = {HG2}
      %Equal.sym(P.H & U32, P.rd({H2}, (y + 3 : U32)), ({H2}, {GETy3}), XP.rd_eq(t2, {AA}, (y + 3 : U32))) : {GOALJ(f'AD.view(U32, KMd.words(P.free(P.free(R.rg.unlink.s(_, y), x), y)))', J1, 'F1')}
      %Equal.sym(U32, {GETy3}, s, hg2) : {GOALJ(f'AD.view(U32, KMd.words(P.free(P.free(X.ix.remove({H2}, _, y), x), y)))', J1, 'F1')}
      jrm(t1, t2, ta, d, s, ps, L, F1, N, x, y, ky, hd32, hN, hy, jinv, jlay, {intro(MBt(Id1),MB1)}, {intro(QFj,QF1)},
        jpl({Pa1}, t1, d, s, L, F1, N, x, y, ky, hN, hB, {jb(4)}, {jb(7)}, {jb(8)}, {jb(9)}, {jb(10)}, hyF1, hxF1, hxy, hxN, hyN, hs1, hx2, hy2, hxt1, hst1, hyB1, {jb(5)}, hxs, hys, jlay, hy, {{==}}),
        hL2N, hsN, {jb(5)}, hL2b1, flok_of(F1, N, d, hN, hB, {jb(9)}),
        and_intro(IM.fl.sep(F1, d, s), IM.fl.offt(F1, t1, d), flsep_of(F1, N, d, s, hN, {jb(9)}, hsN, hsF1), offt_of(F1, t1, N, d, hN, {jb(9)}, {jb(5)}, none_sub(F1, Con{{s, {NDt1}}}, {NDt1}, {jb(7)}, sub_cons_r({NDt1}, s, {NDt1}, sub_refl({NDt1}))))),
        {A2}, hft2, hr2, hc2, htr2, LAT.mirror(U32, {A2}))

# the same over any array, by its mirror
def jn2({JN3S.replace('+t2: LAT.Tree<U32>, ','')},
  -w2: Array<U32>, hf2: {{AD.full(U32, w2, d) == True{{}} : Bool}}, hr2: {T('IM.ix.real(AD.view(U32, w2), d, s, J)')},
  hc2: {T('KMd.chain(F1, AD.view(U32, w2), d, KMd.word(AD.view(U32, w2), d, P.at_fh()))')}, htr2: {T(conj(TRI('AD.view(U32, w2)')))}, m2: LAT.Mirror(U32, w2)) -> {G3('J','w2')}:
  (+t2, +e2) = m2
  +hft2 = LAP.full_t(U32, w2, t2, d, e2, hf2)
  +ew2 = Equal.sym(Array<U32>, {A2}, w2, e2)
  %e2 : {G3('J','_')}
  jn3(J, F1, t2, ta, d, s, ps, L, N, x, y, ky, hd32, hN, hB, hJB, hO, hy, hft2,
    LAB.subst(Array<U32>, qq => {T('IM.ix.real(AD.view(U32, qq), d, s, J)')}, w2, {A2}, ew2, hr2),
    LAB.subst(Array<U32>, qq => {T('KMd.chain(F1, AD.view(U32, qq), d, KMd.word(AD.view(U32, qq), d, P.at_fh()))')}, w2, {A2}, ew2, hc2),
    LAB.subst(Array<U32>, qq => {T(conj(TRI('AD.view(U32, qq)')))}, w2, {A2}, ew2, htr2))
'''
# ---- x's removal, by the tree's shape ----
A1='LAT.fromT(U32, t1)'
NRM_SIG=f'''+t: IM.Tr, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +kx: U32, +ky: U32,
  +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, +hx: {{IM.ix.look({I0}, kx) == Some{{x}} : Maybe<&2, U32>}},
  +hinv: {T(f'IM.ix.inv({I0})')}, +hlay: {T(f'IM.ix.lay({I0}, s, d)')}, +hL2N: {T(f'RG.sub({L2}, N)')}, +hsN: {T('RG.has(N, s)')}, +hIN: {T(f'RG.sub(IM.ix.nodes({I0}), N)')}, +hL2b: {T(f'RG.none.in({L2}, IM.ix.branches({I0}))')},
  +hFok: {T('IM.fl.ok(F, d)')}, +hFs: {T(f'IM.ix.flsep({I0}, s, d, F)')}, +hJB: {T(conj(JBF(J0,F1)))}, +hO: {T(conj(OT))}, +hy: {{IM.ix.look({J0}, ky) == Some{{y}} : Maybe<&2, U32>}},
  -w1: Array<U32>, hf1: {{AD.full(U32, w1, d) == True{{}} : Bool}}, hr1: {T(f'IM.ix.real(AD.view(U32, w1), d, s, {I0})')},
  hc1: {T('KMd.chain(F, AD.view(U32, w1), d, KMd.word(AD.view(U32, w1), d, P.at_fh()))')}, htr1: {T(conj(TRI('AD.view(U32, w1)')))}, m1: LAT.Mirror(U32, w1)'''
NRM_ARGS='ta, d, s, ps, L, F, N, x, y, kx, ky, hd32, hN, hB, hx, hinv, hlay, hL2N, hsN, hIN, hL2b, hFok, hFs, hJB, hO, hy'
GN=lambda w,I: GOALJ(f'AD.view(U32, KMd.words(P.free(P.free(R.rg.unlink(X.ix.remove(P.H{{KM.MG{{{w}}}, {AA}}}, s, x), y), x), y)))', f'IM.ix.del({I}, x, kx)', f'IM.mb.cons(IM.ix.par({I}, x, kx), F)')
def nrm_case(shape):
    if shape=='lf':
        TT='IM.Lf{x0, kx0}'; tparam='+x0: U32, +kx0: U32'
    else:
        TT='IM.Br{b, i, l, r}'; tparam='+b: U32, +i: Nat, +l: IM.Tr, +r: IM.Tr'
    sig=NRM_SIG.replace('+t: IM.Tr, ',tparam+', ').replace('IM.Has{t}','IM.Has{'+TT+'}')
    I=f'IM.Has{{{TT}}}'
    REMW=lambda w: f'X.ix.remove(P.H{{KM.MG{{{w}}}, {AA}}}, s, x)'
    lets=f'''  (+t1, +e1) = m1
  +hft1 = LAP.full_t(U32, w1, t1, d, e1, hf1)
  +ew1 = Equal.sym(Array<U32>, {A1}, w1, e1)
  +hr1T = LAB.subst(Array<U32>, qq => {T(f'IM.ix.real(AD.view(U32, qq), d, s, {I})')}, w1, {A1}, ew1, hr1)
  +hc1T = LAB.subst(Array<U32>, qq => {T('KMd.chain(F, AD.view(U32, qq), d, KMd.word(AD.view(U32, qq), d, P.at_fh()))')}, w1, {A1}, ew1, hc1)
  +htr1T = LAB.subst(Array<U32>, qq => {T(conj(TRI('AD.view(U32, qq)')))}, w1, {A1}, ew1, htr1)
  +hreT1 = and_r(Bool.not(U32.is_eq(KMd.word(AD.view(U32, {A1}), d, (s + 3 : U32)), s)), IM.tr.real(AD.view(U32, {A1}), d, {TT}, KMd.word(AD.view(U32, {A1}), d, (s + 3 : U32)), s), hr1T)
  +hre2L = XL.remove_tree({A1}, {AA}, d, s, {I}, x, kx, hft1, hd32, hr1T, hinv, hlay, hx)
  +hc2L = XL.remove_free({A1}, {AA}, d, s, {I}, x, kx, F, hft1, hd32, hr1T, hinv, hlay, hx, hFok, hFs, hc1T)
  +hf2L = XL.remove_full({A1}, {AA}, d, s, {I}, x, kx, hft1, hd32, hr1T, hinv, hlay, hx)
'''
    if shape=='lf':
        AR=AS(A1,'(s + 3 : U32)','s')
        eqR=f'XP.rm.heap.lf(t1, {AA}, d, s, x, kx, x0, kx0, hft1, hd32, hreT1, hx)'
        W_=[('(s + 3 : U32)','s',f'ones_p3({L2}, N, d, s, hL2N, hN, hsN)')]
        hlets=''
    else:
        TB=TT
        CUTB=f'IM.tr.cutat({TB}, x, kx, (s + 3 : U32))'
        LOB=f'XP.cut.lo({CUTB})'; SIB=f'XP.cut.si({CUTB})'; PAB=f'XP.cut.pa({CUTB})'
        B1_=AS(A1,LOB,SIB); G=GET(B1_,FH); AR=AS(AS(AS(B1_,PAB,'0'),f'({PAB} + 1 : U32)',G),FH,f'(({PAB} >> 2n : U32) + 1 : U32)')
        L6=['IM.nd.ok(b, d)','IM.tr.offn(l, d, b)','IM.tr.offn(r, d, b)','IM.tr.apart(l, r, d)','IM.tr.lay(l, d)','IM.tr.lay(r, d)']
        hl3=['IM.nd.ok(s, d)', f'IM.tr.offn({TB}, d, s)', f'IM.tr.lay({TB}, d)']
        hlets=f'''  +hoks = {proj(hl3,0,'hlay')}
  +hoffT = {proj(hl3,1,'hlay')}
  +hlayT = {proj(hl3,2,'hlay')}
  +hneT = XP.sep_ne(d, x, b, XP.ls.k(X.ix.side(kx, i), d, i, l, r, kx, x, b, {{==}}, hx, hxl => XP.look_sep(l, b, d, kx, x, {proj(L6,1,'hlayT')}, hxl), hxr => XP.look_sep(r, b, d, kx, x, {proj(L6,2,'hlayT')}, hxr)))
  +hpb = XL.par_branch({I}, x, kx, {PAB}, XP.par_cut({TB}, x, kx, (s + 3 : U32), hx, hneT))
  +hpN = sub_has(IM.tr.nodes({TB}), N, {PAB}, hIN, sub_has(IM.tr.branches({TB}), IM.tr.nodes({TB}), {PAB}, br_sub({TB}), hpb))
  +hpL2 = none_notin({L2}, IM.tr.branches({TB}), {PAB}, hL2b, hpb)
'''
        eqR=f'XP.rm.heap.br(t1, {AA}, d, s, x, kx, b, i, l, r, hft1, hd32, hreT1, hinv, hoks, hoffT, hlayT, hx)'
        W_=[(LOB,SIB,f'ones_clo({L2}, N, d, {TB}, x, kx, s, hL2N, hN, hsN, hIN, hL2b, hx, hneT)'),(PAB,'0',f'ones_b0({L2}, N, d, {PAB}, hL2N, hN, hpN, hpL2)'),
           (f'({PAB} + 1 : U32)',G,f'ones_b1({L2}, N, d, {PAB}, hL2N, hN, hpN, hpL2)'),(FH,f'(({PAB} >> 2n : U32) + 1 : U32)',f'ones_fh({L2}, N, d, hL2N, hN)')]
    arrs=[A1]; fulls=['hft1']
    for (jj,v,_) in W_:
        arrs.append(AS(arrs[-1],jj,v)); fulls.append(sfull(arrs[-2],jj,v,fulls[-1]))
    assert arrs[-1]==AR
    tri_='htr1T'
    for m_,(jj,v,ho) in enumerate(W_):
        tri_=frstep(arrs[m_],jj,v,fulls[m_],tri_,ho)
    EQS=lambda pred: f"ME.subst(P.H, hh => {pred}, {REMW(A1)}, P.H{{KM.MG{{{AR}}}, {AA}}}, eqR, "
    JS=f'IM.ix.del({I}, x, kx)'; FS=f'IM.mb.cons(IM.ix.par({I}, x, kx), F)'
    return f'''
def jnrm.{shape}({sig}) -> {GN('w1',I)}:
{lets}{hlets}  +eqR = {eqR}
  +htr2 = {tri_}
  %e1 : {GN('_',I)}
  %Equal.sym(P.H, {REMW(A1)}, P.H{{KM.MG{{{AR}}}, {AA}}}, eqR) : {GOALJ(f'AD.view(U32, KMd.words(P.free(P.free(R.rg.unlink(_, y), x), y)))', JS, FS)}
  jn2({JS}, {FS}, ta, d, s, ps, L, N, x, y, ky, hd32, hN, hB, hJB, hO, hy, {AR}, {EQS(T('AD.full(U32, KMd.words(hh), d)'))}hf2L),
    {EQS(T(f'IM.ix.real(AD.view(U32, KMd.words(hh)), d, s, {JS})'))}hre2L), {EQS(T(f'KMd.chain({FS}, AD.view(U32, KMd.words(hh)), d, KMd.word(AD.view(U32, KMd.words(hh)), d, P.at_fh()))'))}hc2L),
    htr2, LAT.mirror(U32, {AR}))
'''
out+=nrm_case('lf')+nrm_case('br')
out+=f'''
def jnrm({NRM_SIG}) -> {GN('w1',I0)}:
  match t:
    case IM.Lf{{+x0, +kx0}}:
      jnrm.lf(x0, kx0, {NRM_ARGS}, w1, hf1, hr1, hc1, htr1, m1)
    case IM.Br{{+b, +i, +l, +r}}:
      jnrm.br(b, i, l, r, {NRM_ARGS}, w1, hf1, hr1, hc1, htr1, m1)
'''
if os.environ.get('JN_PART')=='1':
    open('glam/proofgen/jn_pend1.txt','w').write(out)
    print('part1', len(out.splitlines()))
# ---- the case: facts, the link, the goal's rewrites ----
HYDEL=(f"Equal.trans(Maybe<&2, U32>, IM.ix.look({J0}, ky), IM.ix.look({I0}, ky), Some{{y}}, "
       f"XL.look_del_other({I0}, s, x, kx, ky, d, hp1, hp2, hx, keys_ne({I0}, kx, ky, x, y, hx, hy0, hxy0)), hy0)")
KEYS_NE=f'''
# two cursors apart found at their keys: the keys apart
def keys_ne.k(+e: Bool, +I: IM.Ix, +kx: U32, +ky: U32, +x: U32, +y: U32, +he: {{U32.is_eq(kx, ky) == e : Bool}},
  +hx: {{IM.ix.look(I, kx) == Some{{x}} : Maybe<&2, U32>}}, +hy: {{IM.ix.look(I, ky) == Some{{y}} : Maybe<&2, U32>}}, +hxy: {{U32.is_eq(x, y) == False{{}} : Bool}}) -> {{e == False{{}} : Bool}}:
  match e:
    case True{{}}:
      +exy = Equal.cong(Maybe<&2, U32>, U32, m => KMd.word.m(m), Some{{x}}, Some{{y}}, Equal.trans(Maybe<&2, U32>, Some{{x}}, IM.ix.look(I, ky), Some{{y}},
        Equal.sym(Maybe<&2, U32>, IM.ix.look(I, ky), Some{{x}}, ME.subst(U32, z => {{IM.ix.look(I, z) == Some{{x}} : Maybe<&2, U32>}}, kx, ky, MS.u32_eq_of_is_eq(kx, ky, he), hx)), hy))
      Empty.absurd({{True{{}} == False{{}} : Bool}}, MB.false_ne_true()(Equal.trans(Bool, False{{}}, U32.is_eq(x, y), True{{}}, Equal.sym(Bool, U32.is_eq(x, y), False{{}}, hxy),
        ME.subst(U32, z => {{U32.is_eq(x, z) == True{{}} : Bool}}, x, y, exy, XP.is_eq_self(x)))))
    case False{{}}:
      {{==}}

def keys_ne(+I: IM.Ix, +kx: U32, +ky: U32, +x: U32, +y: U32, +hx: {{IM.ix.look(I, kx) == Some{{x}} : Maybe<&2, U32>}},
  +hy: {{IM.ix.look(I, ky) == Some{{y}} : Maybe<&2, U32>}}, +hxy: {{U32.is_eq(x, y) == False{{}} : Bool}}) -> {{U32.is_eq(kx, ky) == False{{}} : Bool}}:
  keys_ne.k(U32.is_eq(kx, ky), I, kx, ky, x, y, {{==}}, hx, hy, hxy)
'''
out+=KEYS_NE
C0=PXOK(V0,I0,'ps','L','F','N')
lets=''.join(f'  +hp{i} = {proj(C0,i,"hp")}\n' for i in range(18))
K3=lambda r: [f"Bool.or(P.is_static({r}), IM.ix.offr({I0}, s, d, ({r} + 1 : U32)))", f"Bool.or(P.is_static({r}), KMd.nodes.off(F, d, ({r} + 1 : U32)))", f"Bool.or(P.is_static({r}), Bool.not(Nat.is_eq(AD.slot(({r} + 1 : U32), d), AD.slot(P.at_fh(), d))))"]
KX=f'lk_off.k(P.is_static({UU}), {UU}, {I0}, s, L, F, d, N, {{==}}, hpox, hpkx, hsL, hp14, hlL, hp7, hp13, hp11)'
KY=f'lk_off.k(P.is_static({WW}), {WW}, {I0}, s, L, F, d, N, {{==}}, hpoy, hpky, hsL, hp14, hlL, hp7, hp13, hp11)'
FL1=f'JP.lk_full(P.is_static({UU}), {A0}, d, {UU}, {WW}, hft)'
RDx=lambda h: f'Pair.snd(P.H, U32, P.rd({h}, (x + 3 : U32)))'
H1p=f'P.H{{KM.MG{{{LK2}}}, {AA}}}'
LXX=f'P.link_xx({H0}, {UU}, {WW})'
EH=(f"Equal.trans(P.H, {LXX}, P.link.to(P.is_static({WW}), P.H{{KM.MG{{{LK1}}}, {AA}}}, {WW}, {UU}), {H1p}, "
    f"Equal.cong(P.H, P.H, hh => P.link.to(P.is_static({WW}), hh, {WW}, {UU}), P.link.to(P.is_static({UU}), {H0}, {UU}, {WW}), P.H{{KM.MG{{{LK1}}}, {AA}}}, JP.lt_eq(P.is_static({UU}), {A0}, {AA}, {UU}, {WW})), "
    f"JP.lt_eq(P.is_static({WW}), {LK1}, {AA}, {WW}, {UU}))")
GETx3=GET(LK2,'(x + 3 : U32)')
HGX=trans('U32',[GETx3, RDx(H1p), RDx(LXX), RDx(H0), GET(A0,'(x + 3 : U32)'), WD(V0,'(x + 3 : U32)'), 's'],
  [f"Equal.sym(U32, {RDx(H1p)}, {GETx3}, Equal.cong(P.H & U32, U32, qq => Pair.snd(P.H, U32, qq), P.rd({H1p}, (x + 3 : U32)), ({H1p}, {GETx3}), XP.rd_eqA({LK2}, {AA}, (x + 3 : U32))))",
   f"Equal.cong(P.H, U32, hh => {RDx('hh')}, {H1p}, {LXX}, Equal.sym(P.H, {LXX}, {H1p}, heH))",
   f"HL.link_keeps({A0}, {AA}, d, {UU}, {WW}, (x + 3 : U32), hft, hd32, JP.pk3(L, d, {UU}, x, hpkx, hxL), JP.pk3(L, d, {WW}, x, hpky, hxL))",
   f"Equal.cong(P.H & U32, U32, qq => Pair.snd(P.H, U32, qq), P.rd({H0}, (x + 3 : U32)), ({H0}, {GET(A0,'(x + 3 : U32)')}), XP.rd_eq(t0, {AA}, (x + 3 : U32)))",
   f"Equal.sym(U32, {WD(V0,'(x + 3 : U32)')}, {GET(A0,'(x + 3 : U32)')}, XP.wd(t0, d, (x + 3 : U32), hft, hd32))",
   f"XL.look_home({A0}, d, s, {I0}, kx, x, hp0, hx)"])
GJn=lambda v: GOALJ(v, J0, F1)
GX=GET(A0,'(x + 1 : U32)'); GY=GET(A0,'(y + 1 : U32)')
HX_=f'P.free(P.free(R.rg.unlink(R.rg.unlink(P.link_xx({H0}, {UU}, {WW}), x), y), x), y)'
LVI=f'IM.ix.leaves({I0})'
SD0=f"and_intro(RG.has(Con{{s, {NDt}}}, s), RG.sub(IM.ix.nodes({J0}), Con{{s, {NDt}}}), has_head(s, {NDt}), sub_cons_r(IM.ix.nodes({J0}), s, {NDt}, XL.del_sub({I0}, x, kx, {NDt}, sub_refl({NDt}))))"
lets+=f'''  +hy = {HYDEL}
  +hsL = and_l(RG.has(L, s), RG.sub({LVI}, L), hp3)
  +hlL = and_r(RG.has(L, s), RG.sub({LVI}, L), hp3)
  +hxl = XL.look_leaf({I0}, kx, x, hx)
  +hxL = sub_has({LVI}, L, x, hlL, hxl)
  +hxt = leaf_node(t, x, hxl)
  +hst = XP.absent_nodes(t, d, s, and_l(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hp2)))
  +hxs = nhas({NDt}, x, s, hxt, hst)
  +hlv0 = XL.del_leaves({I0}, s, x, kx, d, hp2, hx)
  +hyW = ME.subst(List<&2, U32>, qq => {T('RG.has(qq, y)')}, IM.ix.leaves({J0}), RG.without({LVI}, x), hlv0, XL.look_leaf({J0}, ky, y, hy))
  +hyl = sub_has(RG.without({LVI}, x), {LVI}, y, sub_without({LVI}, x), hyW)
  +hyL = sub_has({LVI}, L, y, hlL, hyl)
  +hyt = leaf_node(t, y, hyl)
  +hys = nhas({NDt}, y, s, hyt, hst)
  +hxy = ueq_ne(y, x, nhas(RG.without({LVI}, x), y, x, hyW, notin_without({LVI}, x)))
  +hxps = none_has(ps, Con{{s, {NDt}}}, x, hp5, has_cons(s, {NDt}, x, hxt))
  +hyps = none_has(ps, Con{{s, {NDt}}}, y, hp5, has_cons(s, {NDt}, y, hyt))
  +hyF = none_has(F, Con{{s, {NDt}}}, y, hp10, has_cons(s, {NDt}, y, hyt))
  +hxF = none_has(F, Con{{s, {NDt}}}, x, hp10, has_cons(s, {NDt}, x, hxt))
  +hsF = none_has(F, Con{{s, {NDt}}}, s, hp10, has_head(s, {NDt}))
  +hsN = sub_has(L, N, s, hp12, hsL)
  +hxN = sub_has(L, N, x, hp12, hxL)
  +hyN = sub_has(L, N, y, hp12, hyL)
  +hyB = none_mem(L, IM.tr.branches(t), y, hp7, hyL)
  +hxB = none_mem(L, IM.tr.branches(t), x, hp7, hxL)
  +hs1 = sub_trans({L2}, RG.without(L, x), L, sub_without(RG.without(L, x), y), sub_without(L, x))
  +hs2 = sub_back(L, L, x, y, sub_refl(L))
  +hx2 = notin_sub({L2}, RG.without(L, x), x, sub_without(RG.without(L, x), y), notin_without(L, x))
  +hy2 = notin_without(RG.without(L, x), y)
  +hL2N = sub_trans({L2}, L, N, hs1, hp12)
  +hsL2 = has_without(RG.without(L, x), y, s, ueq_ne(s, y, ueq_ne(y, s, hys)), has_without(L, x, s, ueq_ne(s, x, ueq_ne(x, s, hxs)), hsL))
  +hL2b = none_subl({L2}, L, IM.tr.branches(t), hs1, hp7)
  +hpkx = JP.fm_word(List.get(&2, U32, {V0}, AD.slot((x + 1 : U32), d)), d, L, JP.fm_of(L, {V0}, d, L, x, hp15, hxL))
  +hpky = JP.fm_word(List.get(&2, U32, {V0}, AD.slot((y + 1 : U32), d)), d, L, JP.fm_of(L, {V0}, d, L, y, hp15, hyL))
  +hpox = JP.po_of(L, {V0}, d, L, N, x, hp16, hxL)
  +hpoy = JP.po_of(L, {V0}, d, L, N, y, hp16, hyL)
  +heH = {EH}
  +hgx = {HGX}
  +hFs = and_intro(IM.fl.sep(F, d, s), IM.fl.offt(F, t, d), flsep_of(F, N, d, s, hN, hp13, hsN, hsF), offt_of(F, t, N, d, hN, hp13, hp14, none_sub(F, Con{{s, {NDt}}}, {NDt}, hp10, sub_cons_r({NDt}, s, {NDt}, sub_refl({NDt})))))
  +hF1 = jnpl(IM.ix.par({I0}, x, kx), t, d, s, L, F, N, x, y, kx, hp7, hp10, hp11, hp13, hp9, hyF, hxF, hp14, hst, hyB, hxB, hp2, hx, {{==}})
'''
JBp=[f'XL.del_inv({I0}, x, kx, hp1, hx)', f'XL.del_lay({I0}, s, x, kx, d, hp2)',
  f"ME.subst(List<&2, U32>, qq => {T('RG.sub(qq, RG.without(L, x))')}, RG.without({LVI}, x), IM.ix.leaves({J0}), Equal.sym(List<&2, U32>, IM.ix.leaves({J0}), RG.without({LVI}, x), hlv0), "
  f"sub_w1(RG.without({LVI}, x), L, x, sub_trans(RG.without({LVI}, x), {LVI}, L, sub_without({LVI}, x), hlL), notin_without({LVI}, x)))",
  f"none_sub(ps, Con{{s, {NDt}}}, Con{{s, IM.ix.nodes({J0})}}, hp5, {SD0})",
  f"none_sub(L, IM.ix.branches({I0}), IM.ix.branches({J0}), hp7, XL.del_bsub({I0}, x, kx, IM.ix.branches({I0}), sub_refl(IM.ix.branches({I0}))))",
  f"XL.del_sub({I0}, x, kx, N, hp14)",
  f"not_t(RG.has(IM.ix.nodes({J0}), x), none_last(IM.ix.par({I0}, x, kx), x, IM.ix.nodes({J0}), XL.del_absent({I0}, s, d, x, kx, hp2, hx)))"]
JBp+=[proj(F1B(J0,F1),i,'hF1') for i in range(6)]
OTp=['not_t(U32.is_eq(x, y), hxy)', 'hxN', 'hyN', 'hsN', 'not_t(U32.is_eq(x, s), hxs)', 'not_t(U32.is_eq(y, s), hys)',
  'hs1', f'not_t(RG.has({L2}, x), hx2)', f'not_t(RG.has({L2}, y), hy2)', 'hL2N', 'hsL2', 'sub_w2(ps, L, x, y, hp4, hxps, hyps)', 'hp6', 'hyL']
real1=f"real_lk(P.is_static({WW}), {LK1}, ta, d, s, {I0}, {WW}, {UU}, {{==}}, {proj(K3(WW),0,KY)}, {FL1}, hd32, real_lk(P.is_static({UU}), {A0}, ta, d, s, {I0}, {UU}, {WW}, {{==}}, {proj(K3(UU),0,KX)}, hft, hd32, hp0))"
chain1=f"chain_lk(P.is_static({WW}), {LK1}, ta, d, {WW}, {UU}, F, {{==}}, {proj(K3(WW),1,KY)}, {proj(K3(WW),2,KY)}, {FL1}, hd32, chain_lk(P.is_static({UU}), {A0}, ta, d, {UU}, {WW}, F, {{==}}, {proj(K3(UU),1,KX)}, {proj(K3(UU),2,KX)}, hft, hd32, hp8))"
tri1=f"ME.subst(P.H, hh => {T(conj(TRI('AD.view(U32, KMd.words(hh))')))}, {LXX}, {H1p}, heH, JL.link_live({A0}, {AA}, d, L, {L2}, N, x, y, hft, hd32, hN, hp12, hxL, hyL, hxy, hs1, hs2, hx2, hy2, hp15, hp16, hp17))"
full1=f"JP.lk_full(P.is_static({WW}), {LK1}, d, {WW}, {UU}, {FL1})"
CS=f'''+t: IM.Tr, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +kx: U32, +ky: U32,
  +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}'''
out+=f'''
# a join of two cursors, the index a tree: the facts before, the link,
# then x's removal
def jncase({CS},
  +hp: {T(conj(C0))}, +hx: {{IM.ix.look({I0}, kx) == Some{{x}} : Maybe<&2, U32>}}, +hy0: {{IM.ix.look({I0}, ky) == Some{{y}} : Maybe<&2, U32>}}, +hxy0: {{U32.is_eq(x, y) == False{{}} : Bool}}) -> {GJn(f'AD.view(U32, RG.words(R.join({H0}, x, y)))')}:
{lets}  %Equal.sym(P.H & U32, P.rd({H0}, (x + 1 : U32)), ({H0}, {GX}), XP.rd_eq(t0, {AA}, (x + 1 : U32))) : {GJn('AD.view(U32, RG.words(R.jn.u(_, x, y)))')}
  %Equal.sym(P.H & U32, P.rd({H0}, (y + 1 : U32)), ({H0}, {GY}), XP.rd_eq(t0, {AA}, (y + 1 : U32))) : {GJn(f'AD.view(U32, RG.words(R.jn.w(_, {GX}, x, y)))')}
  %XP.wd(t0, d, (x + 1 : U32), hft, hd32) : {GJn(f'AD.view(U32, RG.words(P.free(P.free(R.rg.unlink(R.rg.unlink(P.link_xx({H0}, _, {GY}), x), y), x), y)))')}
  %XP.wd(t0, d, (y + 1 : U32), hft, hd32) : {GJn(f'AD.view(U32, RG.words(P.free(P.free(R.rg.unlink(R.rg.unlink(P.link_xx({H0}, {UU}, _), x), y), x), y)))')}
  %Equal.sym(Array<U32>, RG.words({HX_}), KMd.words({HX_}), rw_kw({HX_})) : {GJn('AD.view(U32, _)')}
  %Equal.sym(P.H, {LXX}, {H1p}, heH) : {GJn('AD.view(U32, KMd.words(P.free(P.free(R.rg.unlink(R.rg.unlink(_, x), y), x), y)))')}
  %Equal.sym(P.H & U32, P.rd({H1p}, (x + 3 : U32)), ({H1p}, {GETx3}), XP.rd_eqA({LK2}, {AA}, (x + 3 : U32))) : {GJn('AD.view(U32, KMd.words(P.free(P.free(R.rg.unlink(R.rg.unlink.s(_, x), y), x), y)))')}
  %Equal.sym(U32, {GETx3}, s, hgx) : {GJn(f'AD.view(U32, KMd.words(P.free(P.free(R.rg.unlink(X.ix.remove({H1p}, _, x), y), x), y)))')}
  jnrm(t, ta, d, s, ps, L, F, N, x, y, kx, ky, hd32, hN, hB, hx, hp1, hp2, hL2N, hsN, hp14, hL2b, flok_of(F, N, d, hN, hB, hp13), hFs,
    {intro(JBF(J0,F1),JBp)}, {intro(OT,OTp)}, hy,
    {LK2}, {full1}, {real1}, {chain1}, {tri1}, LAT.mirror(U32, {LK2}))
'''
# ---- the entry ----
CONC=lambda I,w,a: conj(PXOK(f'AD.view(U32, RG.words(R.join(P.H{{KM.MG{{{w}}}, {a}}}, x, y)))', f'IM.ix.del(IM.ix.del({I}, x, kx), y, ky)', 'ps', L2,
  FP(f'IM.mb.cons(IM.ix.par(IM.ix.del({I}, x, kx), y, ky), IM.mb.cons(IM.ix.par({I}, x, kx), F))'), 'N'))
GK=lambda I,w,a: GOALJ(f'AD.view(U32, RG.words(R.join(P.H{{KM.MG{{{w}}}, {a}}}, x, y)))', f'IM.ix.del({I}, x, kx)', f'IM.mb.cons(IM.ix.par({I}, x, kx), F)')
out+=f'''
def jnpx.k(I: IM.Ix, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +kx: U32, +ky: U32,
  +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  +hp: {T(f'RG.px.ok({V0}, d, s, I, ps, L, F, N)')}, +hx: {{IM.ix.look(I, kx) == Some{{x}} : Maybe<&2, U32>}}, +hy: {{IM.ix.look(I, ky) == Some{{y}} : Maybe<&2, U32>}}, +hxy: {{U32.is_eq(x, y) == False{{}} : Bool}}) -> {GK('I',A0,AA)}:
  match I:
    case IM.Ept{{}}:
      Empty.absurd({GK('IM.Ept{}',A0,AA)}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, m => XP.is_some(m), None{{}}, Some{{x}}, hx)))
    case IM.Has{{+t}}:
      jncase(t, t0, ta, d, s, ps, L, F, N, x, y, kx, ky, hft, hd32, hN, hB, hp, hx, hy, hxy)

def jnpx.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +kx: U32, +ky: U32,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  hp: {T('RG.px.ok(AD.view(U32, w), d, s, I, ps, L, F, N)')}, +hx: {{IM.ix.look(I, kx) == Some{{x}} : Maybe<&2, U32>}}, +hy: {{IM.ix.look(I, ky) == Some{{y}} : Maybe<&2, U32>}}, +hxy: {{U32.is_eq(x, y) == False{{}} : Bool}},
  m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) -> {T(CONC('I','w','a'))}:
  (+t0, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, {A0}, w, e)
  %e : {T(CONC('I','_','a'))}
  %ea : {T(CONC('I',A0,'_'))}
  and_l({CONC('I',A0,AA)}, AD.full(U32, RG.words(R.join({H0}, x, y)), d),
    jnpx.k(I, t0, ta, d, s, ps, L, F, N, x, y, kx, ky, hft, hd32, hN, hB, LAB.subst(Array<U32>, qq => {T('RG.px.ok(AD.view(U32, qq), d, s, I, ps, L, F, N)')}, w, {A0}, ew, hp), hx, hy, hxy))

def Laws.join_pend(w, a, d, s, I, ps, L, F, N, x, y, kx, ky, hf, hd32, hN, hB, hp, hx, hy, hxy):
  jnpx.m(w, a, d, s, I, ps, L, F, N, x, y, kx, ky, hf, hd32, hN, hB, hp, hx, hy, hxy, LAT.mirror(U32, w), LAT.mirror(V.Val, a))
'''
LAW='''
# LAW: two cursors x and y of the index joined (R.join: the ports they
# faced linked, x then y taken out of the index, both freed), two cursors
# apart found at kx and ky, keep the pending placeholders'
# invariant over the index: the index without x and y, the live nodes
# without x and y, the free list's first nodes y, x, the parents the
# removals free if any, then the nodes before
# (cells-freeze.sharing.cursors.index.ring.leave).
# Record: copy-reduced-function-nets
# Record: cursors-indexed
# Record: copy-links-two-way
# Record: serve-premises-over-index
law join_pend:
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
  for hf: {AD.full(U32, w, d) == True{} : Bool}
  for hd32: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hN: {RG.layout(N, d) == True{} : Bool}
  for hB: {RG.bases(N) == True{} : Bool}
  for hp: {RG.px.ok(AD.view(U32, w), d, s, I, ps, L, F, N) == True{} : Bool}
  for hx: {IM.ix.look(I, kx) == Some{x} : Maybe<&2, U32>}
  for hy: {IM.ix.look(I, ky) == Some{y} : Maybe<&2, U32>}
  for hxy: {U32.is_eq(x, y) == False{} : Bool}
  {RG.px.ok(AD.view(U32, RG.words(R.join(P.H{KM.MG{w}, a}, x, y))), d, s, IM.ix.del(IM.ix.del(I, x, kx), y, ky), ps, RG.without(RG.without(L, x), y), Con{y, Con{x, IM.mb.cons(IM.ix.par(IM.ix.del(I, x, kx), y, ky), IM.mb.cons(IM.ix.par(I, x, kx), F))}}, N) == True{} : Bool}
'''
if os.environ.get('JN_PART')=='2':
    i=out.index('def Laws.join_pend(')
    open('glam/proofgen/kp/sec.txt','w').write(out[:i])
    print('part2', len(out.splitlines()))
elif not os.environ.get('JN_PART'):
    p='glam/PROOF.bend'; s=open(p).read()
    assert 'def Laws.join_pend(' not in s
    s=s.rstrip('\n')+'\n'+out
    open(p,'w').write(s)
    lp='glam/LAWS.bend'; l=open(lp).read()
    if 'law join_pend:' not in l:
        anchor='\n# LAW: a serve\'s end, its crossings and then its root\'s leave'
        i=l.index(anchor)
        l=l[:i].rstrip('\n')+'\n'+LAW+l[i:]
        open(lp,'w').write(l)
    print('join', len(out.splitlines()))
