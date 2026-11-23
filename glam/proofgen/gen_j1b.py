# authoring aid: join1_pend over the index, part 2 (glam/PROOF.bend)
import re
exec(open('glam/proofgen/gen_j1.py').read().split("open('glam/proofgen/j1_part1.txt','w')")[0])
xp=open('glam/INDEX_PROOF.bend').read()
A0='LAT.fromT(U32, t0)'; AA='LAT.fromT(V.Val, ta)'; V0=f'AD.view(U32, {A0})'
I0='IM.Has{t}'; Id='IM.ix.del(IM.Has{t}, y, k)'; Pa='IM.ix.par(IM.Has{t}, y, k)'
FP=lambda Pl: f'Con{{y, Con{{x, {Pl}}}}}'
H0=f'P.H{{KM.MG{{{A0}}}, {AA}}}'
UU=WD(V0,'(x + 1 : U32)'); WW=WD(V0,'(y + 1 : U32)')
LK1=f'JP.lk(P.is_static({UU}), {A0}, {UU}, {WW})'; LK2=f'JP.lk(P.is_static({WW}), {LK1}, {WW}, {UU})'
NOD=lambda I: f'IM.ix.nodes({I})'; BR=lambda I: f'IM.ix.branches({I})'; LV=lambda I: f'IM.ix.leaves({I})'
MBt=lambda J: [f'IM.ix.inv({J})', f'IM.ix.lay({J}, s, d)', f'RG.sub(Con{{s, {LV(J)}}}, {L2})', f'RG.sub(ps, {L2})', f'RG.none.in(ps, Con{{s, {NOD(J)}}})', 'RG.distinct(ps)',
  f'RG.none.in({L2}, {BR(J)})', f'RG.sub({L2}, N)', f'RG.sub({NOD(J)}, N)']
PLFt=lambda J,Pl: [f'RG.distinct({FP(Pl)})', f'RG.none.in({FP(Pl)}, Con{{s, {NOD(J)}}})', f'RG.none.in({FP(Pl)}, {L2})', f'RG.sub({FP(Pl)}, N)',
  f'IM.fl.ok({Pl}, d)', f'IM.fl.sep({Pl}, d, x)', f'IM.fl.ok(Con{{x, {Pl}}}, d)', f'IM.fl.sep(Con{{x, {Pl}}}, d, y)']
OFX=lambda J,j: f'IM.ix.offr({J}, s, d, {j})'
ONS=lambda j: f'ones({L2}, d, {j})'
QFt=lambda J: ['IM.nd.ok(x, d)', 'IM.nd.ok(y, d)', OFX(J,'x'), OFX(J,'(x + 1 : U32)'), OFX(J,'y'), OFX(J,'(y + 1 : U32)'), OFX(J,'P.at_fh()'),
  ONS('x'), ONS('(x + 1 : U32)'), ONS('y'), ONS('(y + 1 : U32)'), ONS('P.at_fh()')]
out=''
# ---- generic lemmas for part 2 ----
out+=f'''
# the branches of a tree among its nodes
def br_sub(t: IM.Tr) -> {T('RG.sub(IM.tr.branches(t), IM.tr.nodes(t))')}:
  match t:
    case IM.Lf{{+y, +ky}}:
      {{==}}
    case IM.Br{{+b, +i, +l, +r}}:
      and_intro(RG.has(Con{{b, {AP('IM.tr.nodes(l)','IM.tr.nodes(r)')}}}, b), RG.sub({AP('IM.tr.branches(l)','IM.tr.branches(r)')}, Con{{b, {AP('IM.tr.nodes(l)','IM.tr.nodes(r)')}}}), has_head(b, {AP('IM.tr.nodes(l)','IM.tr.nodes(r)')}),
        sub_cons_r({AP('IM.tr.branches(l)','IM.tr.branches(r)')}, b, {AP('IM.tr.nodes(l)','IM.tr.nodes(r)')},
          XP.sub_app(IM.tr.branches(l), IM.tr.branches(r), {AP('IM.tr.nodes(l)','IM.tr.nodes(r)')}, sub_trans(IM.tr.branches(l), IM.tr.nodes(l), {AP('IM.tr.nodes(l)','IM.tr.nodes(r)')}, br_sub(l), sub_appl(IM.tr.nodes(l), IM.tr.nodes(r))),
            sub_trans(IM.tr.branches(r), IM.tr.nodes(r), {AP('IM.tr.nodes(l)','IM.tr.nodes(r)')}, br_sub(r), sub_appr(IM.tr.nodes(l), IM.tr.nodes(r))))))

def lv_sub(t: IM.Tr) -> {T('RG.sub(IM.tr.leaves(t), IM.tr.nodes(t))')}:
  match t:
    case IM.Lf{{+y, +ky}}:
      and_intro(RG.has([y], y), RG.sub([], [y]), has_head(y, []), {{==}})
    case IM.Br{{+b, +i, +l, +r}}:
      sub_cons_r({AP('IM.tr.leaves(l)','IM.tr.leaves(r)')}, b, {AP('IM.tr.nodes(l)','IM.tr.nodes(r)')},
        XP.sub_app(IM.tr.leaves(l), IM.tr.leaves(r), {AP('IM.tr.nodes(l)','IM.tr.nodes(r)')}, sub_trans(IM.tr.leaves(l), IM.tr.nodes(l), {AP('IM.tr.nodes(l)','IM.tr.nodes(r)')}, lv_sub(l), sub_appl(IM.tr.nodes(l), IM.tr.nodes(r))),
          sub_trans(IM.tr.leaves(r), IM.tr.nodes(r), {AP('IM.tr.nodes(l)','IM.tr.nodes(r)')}, lv_sub(r), sub_appr(IM.tr.nodes(l), IM.tr.nodes(r)))))

# a member of M none of L's
def none_notin(L: List<&2, U32>, +M: List<&2, U32>, +p: U32, +hn: {T('RG.none.in(L, M)')}, +hp: {T('RG.has(M, p)')}) -> {F_('RG.has(L, p)')}:
  match L:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      or_ff(U32.is_eq(z, p), RG.has(r, p), nhas(M, p, z, hp, MB.eq_false_of_not_eq_true(RG.has(M, z), and_l(Bool.not(RG.has(M, z)), RG.none.in(r, M), hn))) |> ueqf(p, z),
        none_notin(r, M, p, and_r(Bool.not(RG.has(M, z)), RG.none.in(r, M), hn), hp))

def ueqf(+a: U32, +b: U32, +h: {NE('a','b')}) -> {NE('b','a')}:
  ueq_ne(a, b, h)

def none_last(+m: Maybe<&2, U32>, +y: U32, +X: List<&2, U32>, +h: {T('RG.none.in(IM.mb.cons(m, [y]), X)')}) -> {F_('RG.has(X, y)')}:
  match m:
    case Some{{+q}}:
      MB.eq_false_of_not_eq_true(RG.has(X, y), and_l(Bool.not(RG.has(X, y)), RG.none.in([], X), and_r(Bool.not(RG.has(X, q)), RG.none.in([y], X), h)))
    case None{{}}:
      MB.eq_false_of_not_eq_true(RG.has(X, y), and_l(Bool.not(RG.has(X, y)), RG.none.in([], X), h))
'''
out=out.replace("nhas(M, p, z, hp, MB.eq_false_of_not_eq_true(RG.has(M, z), and_l(Bool.not(RG.has(M, z)), RG.none.in(r, M), hn))) |> ueqf(p, z)",
  "ueqf(p, z, nhas(M, p, z, hp, MB.eq_false_of_not_eq_true(RG.has(M, z), and_l(Bool.not(RG.has(M, z)), RG.none.in(r, M), hn))))")
out=mv(out,'def ueqf(','def none_notin(')
# offr of a tracked node's words over any index J
for i in (0,1):
    ni=P1('n',i)
    DJ=lambda a,b: [OW(b,P1(a,q)) for q in range(4)]
    OWs=[f'Bool.not(Nat.is_eq(AD.slot({P1("s",q)}, d), AD.slot({ni}, d)))' for q in range(4)]+['True{}']
    S3N=proj(OWs,3,proj(DJ('n','s'),i,'and_l(IM.nd.disj(d, n, s), IM.nd.disj(d, s, n), XL.layout_sep(N, d, n, s, hN, hnN, hsN, hns))'))
    out+=f'''
def offr_n{i}(J: IM.Ix, +s: U32, +d: Nat, +n: U32, +N: List<&2, U32>, +hN: {T('RG.layout(N, d)')}, +hJN: {T(f'RG.sub({NOD("J")}, N)')}, +hnN: {T('RG.has(N, n)')}, +hsN: {T('RG.has(N, s)')},
  +hnJ: {F_(f'RG.has({NOD("J")}, n)')}, +hns: {NE('n','s')}) -> {T(OFX('J',ni))}:
  match J:
    case IM.Ept{{}}:
      {S3N}
    case IM.Has{{+t}}:
      and_intro(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot({ni}, d))), IM.tr.offr(t, d, {ni}), {S3N}, offr_sep{i}(t, d, n, offn_of(t, N, d, n, hN, hJN, hnN, hnJ)))
'''
NDOKs=['U32.is_eq(P.base(s), s)', 'IM.ws.apart(KMd.nw(s), d)', OW('s',FH)]
OWsh=[f'Bool.not(Nat.is_eq(AD.slot({P1("s",q)}, d), AD.slot(P.at_fh(), d)))' for q in range(4)]+['True{}']
out+=f'''
def offr_hix(J: IM.Ix, +s: U32, +d: Nat, +hl: {T('IM.ix.lay(J, s, d)')}) -> {T(OFX('J','P.at_fh()'))}:
  match J:
    case IM.Ept{{}}:
      {proj(OWsh,3,proj(NDOKs,2,'hl'))}
    case IM.Has{{+t}}:
      and_intro(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot(P.at_fh(), d))), IM.tr.offr(t, d, P.at_fh()), {proj(OWsh,3,proj(NDOKs,2,'and_l(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl)'))},
        offr_fh(t, d, and_r(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hl))))
'''
# ones for a removal's write at its cut's word
CL='XP.cut.lo(IM.tr.cutat(t, x, k, (s + 3 : U32)))'
ONE=lambda i: f'Bool.not(Nat.is_eq(AD.slot({i}, d), AD.slot((m + 1 : U32), d)))'
out+=f'''
# the word a removal writes the sibling at off the live nodes' words 1
def ones_clo(L: List<&2, U32>, +N: List<&2, U32>, +d: Nat, +t: IM.Tr, +x: U32, +k: U32, +s: U32, +hs: {T('RG.sub(L, N)')}, +hN: {T('RG.layout(N, d)')}, +hsN: {T('RG.has(N, s)')},
  +htN: {T(f"RG.sub({NODES('t')}, N)")}, +hLb: {T(f"RG.none.in(L, {BRS('t')})")}, +hx: {{IM.tr.look(t, k) == Some{{x}} : Maybe<&2, U32>}}, +hne: {NE('IM.tr.addr(t)','x')}) -> {T(f'ones(L, d, {CL})')}:
  match L:
    case Nil{{}}:
      {{==}}
    case Con{{+m, +r}}:
      +hmN = and_l(RG.has(N, m), RG.sub(r, N), hs)
      and_intro({ONE(CL)}, ones(r, d, {CL}), nf2(Nat.is_eq(AD.slot({CL}, d), AD.slot((m + 1 : U32), d)), neq_comm2(AD.slot((m + 1 : U32), d), AD.slot({CL}, d),
        XP.c2b(t, x, k, (s + 3 : U32), d, (m + 1 : U32), offb_of(t, N, d, m, hN, htN, hmN, MB.eq_false_of_not_eq_true(RG.has({BRS('t')}, m), and_l(Bool.not(RG.has({BRS('t')}, m)), RG.none.in(r, {BRS('t')}), hLb))),
          m13.k(U32.is_eq(m, s), m, s, N, d, {{==}}, hN, hmN, hsN), hx, hne))),
        ones_clo(r, N, d, t, x, k, s, and_r(RG.has(N, m), RG.sub(r, N), hs), hN, hsN, htN, and_r(Bool.not(RG.has({BRS('t')}, m)), RG.none.in(r, {BRS('t')}), hLb), hx, hne))
'''
# ---- the Pl facts ----
def jpl_body(pp):
    if pp:
        Pl=f'Con{{{pp}, F}}'
        lets=f'''      +hpb = XL.par_branch({I0}, y, k, {pp}, he)
      +hpn = sub_has(IM.tr.branches(t), IM.tr.nodes(t), {pp}, br_sub(t), hpb)
      +hpN = sub_has(IM.tr.nodes(t), N, {pp}, hIN, hpn)
      +hpL = none_notin(L, IM.tr.branches(t), {pp}, hbr, hpb)
      +hpF = none_notin(F, Con{{s, IM.tr.nodes(t)}}, {pp}, hfn, has_cons(s, IM.tr.nodes(t), {pp}, hpn))
      +hpy = nhas(IM.tr.branches(t), {pp}, y, hpb, hyB)
      +hpx = nhas(IM.tr.nodes(t), {pp}, x, hpn, hxt)
      +hps = nhas(IM.tr.nodes(t), {pp}, s, hpn, hst)
      +hDA = ME.subst(Maybe<&2, U32>, mm => {T(f"RG.none.in(IM.mb.cons(mm, [y]), {NOD(Id)})")}, {Pa}, Some{{{pp}}}, he, XL.del_absent({I0}, s, d, y, k, hlay, hy))
      +hpD = MB.eq_false_of_not_eq_true(RG.has({NOD(Id)}, {pp}), and_l(Bool.not(RG.has({NOD(Id)}, {pp})), RG.none.in([y], {NOD(Id)}), hDA))
'''
    else:
        Pl='F'
        lets=f'''      +hDA = ME.subst(Maybe<&2, U32>, mm => {T(f"RG.none.in(IM.mb.cons(mm, [y]), {NOD(Id)})")}, {Pa}, None{{}}, he, XL.del_absent({I0}, s, d, y, k, hlay, hy))
'''
    lets+=f'''      +hyD = none_last({'Some{'+pp+'}' if pp else 'None{}'}, y, {NOD(Id)}, hDA)
      +hxD = notin_sub({NOD(Id)}, IM.tr.nodes(t), x, XL.del_sub({I0}, y, k, IM.tr.nodes(t), sub_refl(IM.tr.nodes(t))), hxt)
      +hSD = and_intro(RG.has(Con{{s, IM.tr.nodes(t)}}, s), RG.sub({NOD(Id)}, Con{{s, IM.tr.nodes(t)}}), has_head(s, IM.tr.nodes(t)), sub_cons_r({NOD(Id)}, s, IM.tr.nodes(t), XL.del_sub({I0}, y, k, IM.tr.nodes(t), sub_refl(IM.tr.nodes(t)))))
'''
    M=f'Con{{s, {NOD(Id)}}}'
    def nin(a, hs_a, hd_a): return f'not_t(RG.has({M}, {a}), or_ff(U32.is_eq(s, {a}), RG.has({NOD(Id)}, {a}), {hs_a}, {hd_a}))'
    def ninL(a, h): return f'not_t(RG.has({L2}, {a}), {h})'
    ys=['y','x']+([pp] if pp else [])
    # none.in(Fp, M)
    nM_terms=[]; 
    def none_chain(elems, Mexp, nots, tail):
        if not elems: return tail
        a=elems[0]; rest=elems[1:]
        restlist = ('Con{'+', Con{'.join(rest)+', F'+'}'*len(rest)) if rest else 'F'
        return f'and_intro(Bool.not(RG.has({Mexp}, {a})), RG.none.in({restlist}, {Mexp}), {nots[0]}, {none_chain(rest, Mexp, nots[1:], tail)})'
    nM=none_chain(ys, M, [nin('y','ueq_ne(y, s, hys)','hyD'), nin('x','ueq_ne(x, s, hxs)','hxD')]+([nin(pp,f'ueq_ne({pp}, s, hps)','hpD')] if pp else []),
      f'none_sub(F, Con{{s, IM.tr.nodes(t)}}, {M}, hfn, hSD)')
    nL=none_chain(ys, L2, [ninL('y','hy2'), ninL('x','hx2')]+([ninL(pp, f'notin_sub({L2}, L, {pp}, hs1, hpL)')] if pp else []), f'none_sub(F, L, {L2}, hFL, hs1)')
    def sub_chain(elems, hasp, tail):
        if not elems: return tail
        a=elems[0]; rest=elems[1:]
        restlist = ('Con{'+', Con{'.join(rest)+', F'+'}'*len(rest)) if rest else 'F'
        return f'and_intro(RG.has(N, {a}), RG.sub({restlist}, N), {hasp[0]}, {sub_chain(rest, hasp[1:], tail)})'
    sN=sub_chain(ys, ['hyN','hxN']+(['hpN'] if pp else []), 'hFN')
    sNx=sub_chain(ys[1:], ['hxN']+(['hpN'] if pp else []), 'hFN')
    sNp=sub_chain(ys[2:], (['hpN'] if pp else []), 'hFN')
    # distinct
    if pp:
        hyX=f'or_ff(U32.is_eq(x, y), RG.has(Con{{{pp}, F}}, y), hxy, or_ff(U32.is_eq({pp}, y), RG.has(F, y), hpy, hyF))'
        hxP=f'or_ff(U32.is_eq({pp}, x), RG.has(F, x), hpx, hxF)'
        dist=f'and_intro(Bool.not(RG.has(Con{{x, {Pl}}}, y)), RG.distinct(Con{{x, {Pl}}}), not_t(RG.has(Con{{x, {Pl}}}, y), {hyX}), and_intro(Bool.not(RG.has({Pl}, x)), RG.distinct({Pl}), not_t(RG.has({Pl}, x), {hxP}), and_intro(Bool.not(RG.has(F, {pp})), RG.distinct(F), not_t(RG.has(F, {pp}), hpF), hFd)))'
    else:
        hyX='or_ff(U32.is_eq(x, y), RG.has(F, y), hxy, hyF)'; hxP='hxF'
        dist=f'and_intro(Bool.not(RG.has(Con{{x, F}}, y)), RG.distinct(Con{{x, F}}), not_t(RG.has(Con{{x, F}}, y), {hyX}), and_intro(Bool.not(RG.has(F, x)), RG.distinct(F), not_t(RG.has(F, x), {hxP}), hFd))'
    PL=PLFt(Id,Pl)
    prfs=[dist, nM, nL, sN, f'flok_of({Pl}, N, d, hN, hB, {sNp})', f'flsep_of({Pl}, N, d, x, hN, {sNp}, hxN, {hxP})',
          f'flok_of(Con{{x, {Pl}}}, N, d, hN, hB, {sNx})', f'flsep_of(Con{{x, {Pl}}}, N, d, y, hN, {sNx}, hyN, {hyX})']
    return lets+f'      {intro(PL,prfs)}\n'
JPLS=f'''+t: IM.Tr, +d: Nat, +s: U32, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32, +k: U32,
  +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, +hbr: {T('RG.none.in(L, IM.tr.branches(t))')}, +hfn: {T('RG.none.in(F, Con{s, IM.tr.nodes(t)})')}, +hFL: {T('RG.none.in(F, L)')},
  +hFN: {T('RG.sub(F, N)')}, +hFd: {T('RG.distinct(F)')}, +hyF: {F_('RG.has(F, y)')}, +hxF: {F_('RG.has(F, x)')}, +hxy: {NE('x','y')}, +hxN: {T('RG.has(N, x)')}, +hyN: {T('RG.has(N, y)')},
  +hs1: {T(f'RG.sub({L2}, L)')}, +hx2: {F_(f'RG.has({L2}, x)')}, +hy2: {F_(f'RG.has({L2}, y)')}, +hxt: {F_('RG.has(IM.tr.nodes(t), x)')}, +hst: {F_('RG.has(IM.tr.nodes(t), s)')},
  +hyB: {F_('RG.has(IM.tr.branches(t), y)')}, +hIN: {T('RG.sub(IM.tr.nodes(t), N)')}, +hxs: {NE('x','s')}, +hys: {NE('y','s')}, +hlay: {T(f'IM.ix.lay({I0}, s, d)')}, +hy: {{IM.ix.look({I0}, k) == Some{{y}} : Maybe<&2, U32>}}'''
JPLA='t, d, s, L, F, N, x, y, k, hN, hB, hbr, hfn, hFL, hFN, hFd, hyF, hxF, hxy, hxN, hyN, hs1, hx2, hy2, hxt, hst, hyB, hIN, hxs, hys, hlay, hy'
out+=f'''
# what the free list's first nodes after a join hold, the removal's parent m if any
def jpl(+m: Maybe<&2, U32>, {JPLS}, +he: {{{Pa} == m : Maybe<&2, U32>}}) -> {T(conj(PLFt(Id,'IM.mb.cons(m, F)')))}:
  match m:
    case Some{{+pp}}:
{jpl_body('pp')}    case None{{}}:
{jpl_body(None)}'''
# ---- frees, the second ----
GOAL=lambda v,J,Pl: T('(' + conj(PXOK(v,J,'ps',L2,FP(Pl),'N')) + ') && AD.full(U32, ' + v[len('AD.view(U32, '):-1] + ', d)')
FREEV=lambda w,r: f'AD.view(U32, KMd.words(P.free(P.H{{KM.MG{{{w}}}, {AA}}}, {r})))'
COMMON=f'''+J: IM.Ix, +Pl: List<&2, U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +N: List<&2, U32>, +x: U32, +y: U32,
  +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hM: {T(conj(MBt('J')))}, +hQ: {T(conj(QFt('J')))}, +hPL: {T(conj(PLFt('J','Pl')))}'''
CARGS='J, Pl, ta, d, s, ps, L, N, x, y, hd32, hN, hM, hQ, hPL'
QF=QFt('J'); MBL=MBt('J'); PLL=PLFt('J','Pl')
q=lambda i: proj(QF,i,'hQ'); mb=lambda i: proj(MBL,i,'hM'); pl=lambda i: proj(PLL,i,'hPL')
def base_eq(r, okp): return f"MS.u32_eq_of_is_eq(P.base({r}), {r}, and_l(U32.is_eq(P.base({r}), {r}), IM.ws.apart(KMd.nw({r}), d) && {OW(r,FH)}, {okp}))"
def to_base(pred, r, fact, hb):  # pred over q; fact at r; gives at P.base(r)
    return f'ME.subst(U32, qq => {pred}, {r}, P.base({r}), Equal.sym(U32, P.base({r}), {r}, {hb}), {fact})'
def free_phase(r, Aw, Pl_before, okp, flok, flsep, ofr0, ofr1, ofh, on0, on1, onh, hr, hc, htr, tag):
    # facts after freeing r from the heap H{MG{Aw}, AA}, Aw = LAT.fromT(U32, tX)
    tX={'x':'t2','y':'t3'}[r]
    G2=GET(Aw,FH); Hh=f'(({r} >> 2n : U32) + 1 : U32)'
    B1=AS(Aw,f'P.base({r})','0'); B2=AS(B1,f'(P.base({r}) + 1 : U32)',G2); B3=AS(B2,FH,Hh)
    f1=sfull(Aw,f'P.base({r})','0',f'hft{tag}'); f2=sfull(B1,f'(P.base({r}) + 1 : U32)',G2,f1)
    hb=f'hb{r}'
    tri=frstep(Aw,f'P.base({r})','0',f'hft{tag}',htr,to_base(T(f'ones({L2}, d, qq)'),r,on0,hb))
    tri=frstep(B1,f'(P.base({r}) + 1 : U32)',G2,f1,tri,to_base(T(f'ones({L2}, d, (qq + 1 : U32))'),r,on1,hb))
    tri=frstep(B2,FH,Hh,f2,tri,onh)
    lets=f'''  +{hb} = {base_eq(r, okp)}
  +hfr{r} = XL.free_real({Aw}, {AA}, d, s, J, {r}, hft{tag}, hd32, {to_base(T(OFX('J','qq')),r,ofr0,hb)}, {to_base(T(OFX('J','(qq + 1 : U32)')),r,ofr1,hb)}, {ofh}, {hr})
  +hfc{r} = XL.free_push({Aw}, {AA}, d, {r}, {Pl_before}, hft{tag}, hd32, {okp}, {flok}, {flsep}, {hc})
  +hff{r} = XL.free_full({Aw}, {AA}, d, {r}, hft{tag})
  +heq{r} = XP.fh1({tX}, {AA}, {r})
  +htr{r} = {tri}
'''
    return lets, B3
# jfr2: free y on A3, assemble
A3='LAT.fromT(U32, t3)'
lets_y, AFy = free_phase('y', A3, 'Con{x, Pl}', q(1), pl(6), pl(7), q(4), q(5), q(6), q(9), q(10), q(11), 'hr3T', 'hc3T', 'htr3T', '3')
V4=FREEV(A3,'y')
TRIy=f"ME.subst(P.H, hh => {T(conj(TRI('AD.view(U32, KMd.words(hh))')))}, P.H{{KM.MG{{{AFy}}}, {AA}}}, P.free(P.H{{KM.MG{{{A3}}}, {AA}}}, y), Equal.sym(P.H, P.free(P.H{{KM.MG{{{A3}}}, {AA}}}, y), P.H{{KM.MG{{{AFy}}}, {AA}}}, heqy), htry)"
FIN=PXOK(V4,'J','ps',L2,FP('Pl'),'N')
fin_prfs=['hfry', mb(0), mb(1), mb(2), mb(3), mb(4), mb(5), mb(6), 'hfcy', pl(0), pl(1), pl(2), mb(7), pl(3), mb(8),
  proj(TRI(V4),0,'htrF'), proj(TRI(V4),1,'htrF'), proj(TRI(V4),2,'htrF')]
SUBT=lambda pred,w,t_,e: f'LAB.subst(Array<U32>, qq => {pred}, {w}, LAT.fromT(U32, {t_}), {e}, '
out+=f'''
# the second free, y's, and the invariant after
def jfr2({COMMON}, -w3: Array<U32>, hf3: {{AD.full(U32, w3, d) == True{{}} : Bool}}, hr3: {T('IM.ix.real(AD.view(U32, w3), d, s, J)')},
  hc3: {T('KMd.chain(Con{x, Pl}, AD.view(U32, w3), d, KMd.word(AD.view(U32, w3), d, P.at_fh()))')}, htr3: {T(conj(TRI('AD.view(U32, w3)')))}, m3: LAT.Mirror(U32, w3)) ->
  {GOAL(f'AD.view(U32, KMd.words(P.free(P.H{{KM.MG{{w3}}, {AA}}}, y)))','J','Pl')}:
  (+t3, +e3) = m3
  +hft3 = LAP.full_t(U32, w3, t3, d, e3, hf3)
  +ew3 = Equal.sym(Array<U32>, {A3}, w3, e3)
  +hr3T = {SUBT(T('IM.ix.real(AD.view(U32, qq), d, s, J)'),'w3','t3','ew3')}hr3)
  +hc3T = {SUBT(T('KMd.chain(Con{x, Pl}, AD.view(U32, qq), d, KMd.word(AD.view(U32, qq), d, P.at_fh()))'),'w3','t3','ew3')}hc3)
  +htr3T = {SUBT(T(conj(TRI('AD.view(U32, qq)'))),'w3','t3','ew3')}htr3)
{lets_y}  +htrF = {TRIy}
  %e3 : {GOAL(f'AD.view(U32, KMd.words(P.free(P.H{{KM.MG{{_}}, {AA}}}, y)))','J','Pl')}
  and_intro({conj(FIN)}, AD.full(U32, KMd.words(P.free(P.H{{KM.MG{{{A3}}}, {AA}}}, y)), d), {intro(FIN, fin_prfs)}, hffy)
'''
A2='LAT.fromT(U32, t2)'
lets_x, AFx = free_phase('x', A2, 'Pl', q(0), pl(4), pl(5), q(2), q(3), q(6), q(7), q(8), q(11), 'hr2T', 'hc2T', 'htr2T', '2')
EQ2=lambda pred: f"ME.subst(P.H, hh => {pred}, P.free(P.H{{KM.MG{{{A2}}}, {AA}}}, x), P.H{{KM.MG{{{AFx}}}, {AA}}}, heqx, "
out+=f'''
# the first free, x's
def jfr({COMMON}, -w2: Array<U32>, hf2: {{AD.full(U32, w2, d) == True{{}} : Bool}}, hr2: {T('IM.ix.real(AD.view(U32, w2), d, s, J)')},
  hc2: {T('KMd.chain(Pl, AD.view(U32, w2), d, KMd.word(AD.view(U32, w2), d, P.at_fh()))')}, htr2: {T(conj(TRI('AD.view(U32, w2)')))}, m2: LAT.Mirror(U32, w2)) ->
  {GOAL(f'AD.view(U32, KMd.words(P.free(P.free(P.H{{KM.MG{{w2}}, {AA}}}, x), y)))','J','Pl')}:
  (+t2, +e2) = m2
  +hft2 = LAP.full_t(U32, w2, t2, d, e2, hf2)
  +ew2 = Equal.sym(Array<U32>, {A2}, w2, e2)
  +hr2T = {SUBT(T('IM.ix.real(AD.view(U32, qq), d, s, J)'),'w2','t2','ew2')}hr2)
  +hc2T = {SUBT(T('KMd.chain(Pl, AD.view(U32, qq), d, KMd.word(AD.view(U32, qq), d, P.at_fh()))'),'w2','t2','ew2')}hc2)
  +htr2T = {SUBT(T(conj(TRI('AD.view(U32, qq)'))),'w2','t2','ew2')}htr2)
{lets_x}  %e2 : {GOAL(f'AD.view(U32, KMd.words(P.free(P.free(P.H{{KM.MG{{_}}, {AA}}}, x), y)))','J','Pl')}
  %Equal.sym(P.H, P.free(P.H{{KM.MG{{{A2}}}, {AA}}}, x), P.H{{KM.MG{{{AFx}}}, {AA}}}, heqx) : {GOAL(f'AD.view(U32, KMd.words(P.free(_, y)))','J','Pl')}
  jfr2({CARGS}, {AFx}, {EQ2(T('AD.full(U32, KMd.words(hh), d)'))}hffx), {EQ2(T('IM.ix.real(AD.view(U32, KMd.words(hh)), d, s, J)'))}hfrx),
    {EQ2(T('KMd.chain(Con{x, Pl}, AD.view(U32, KMd.words(hh)), d, KMd.word(AD.view(U32, KMd.words(hh)), d, P.at_fh()))'))}hfcx), htrx, LAT.mirror(U32, {AFx}))
'''
open('glam/proofgen/j1_part2.txt','w').write(out)
print('part 2', len(out.splitlines()))
