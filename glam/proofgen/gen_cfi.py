# authoring aid: the ports the live nodes face after a copy's crossings,
# among those faced at the start (cfi.go, cfi.m; glam/PROOF.bend), crk.go's
# fold with faced.in for its result; run by regen.sh after gen_jn.py
import os
exec(open('glam/proofgen/gen_fold.py').read().split("out=f'''")[0])
GF=lambda code, S: T(f'faced.in(RG.cxs.L({S}), AD.view(U32, RG.words({code})), d, Fp)')
out=f'''
# The ports the live nodes face after a copy's crossings, among those faced
# at the start (cells-freeze.sharing.cursors.index.ring.leave: the frame of
# the leave at the source's root, serve_root_keeps)
def cfi.go(cl: List<&2, R.FzC>, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +s: U32, +I: IM.Ix, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, hfm: {{AD.full(U32, map, dm) == True{{}} : Bool}}, +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}},
  +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, hp: {HPX('AD.view(U32, w)', 'RG.pls(cl, AD.view(U32, map), dm)')}, hok: {T('RG.cxs.ok(cl, AD.view(U32, map), dm, I, F)')},
  +Fp: List<&2, U32>, hfi: {T('faced.in(L, AD.view(U32, w), d, Fp)')}, mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) -> {GF(CODE('cl','map','P.H{KM.MG{w}, a}'), S0('cl','AD.view(U32, map)'))}:
  match cl:
    case Nil{{}}:
      hfi
    case Con{{c, +rest}}:
      match c:
        case R.FzC{{+at, +src, +neg, +far}}:
          (+tw, +ew) = mw
          (+ta, +ea) = ma
          (+tm, +em) = mm
          +hft = LAP.full_t(U32, w, tw, d, ew, hf)
          +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
          +ePL = ME.subst(Maybe<&2, U32>, q => {{RG.pl.of(q) == {X} : U32}}, Some{{{X}}}, List.get(&2, U32, AD.view(U32, {TM}), AD.slot(at, dm)), LA.get_view(U32, {TM}, dm, at, hfmt, hdm), {{==}})
          +hpa = LAB.subst(Array<U32>, qq => {HPX('AD.view(U32, qq)', 'Con{'+XMq('map')+', RG.pls(rest, AD.view(U32, map), dm)}')}, w, {TW}, Equal.sym(Array<U32>, {TW}, w, ew), hp)
          +hpb = LAB.subst(Array<U32>, qq => {HPX(f'AD.view(U32, {TW})', 'Con{'+XMq('qq')+', RG.pls(rest, AD.view(U32, qq), dm)}')}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hpa)
          +hp3 = ME.subst(U32, q => {HPX(f'AD.view(U32, {TW})', 'Con{q, '+PSR+'}')}, {XM}, {X}, ePL, hpb)
          +hoa = LAB.subst(Array<U32>, qq => {T(f'({AB} && {RM}) && '+OKR('AD.view(U32, qq)', XMq('qq')))}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hok)
          +hob = ME.subst(U32, q => {T(f'({AB} && {RM}) && '+OKR(f'AD.view(U32, {TM})', 'q'))}, {XM}, {X}, ePL, hoa)
          +hab = and_l({AB}, {RM}, and_l({AB} && {RM}, {OKR(f'AD.view(U32, {TM})', X)}, hob))
          +hrm = and_r({AB}, {RM}, and_l({AB} && {RM}, {OKR(f'AD.view(U32, {TM})', X)}, hob))
          +hokr = and_r({AB} && {RM}, {OKR(f'AD.view(U32, {TM})', X)}, hob)
          +hpF = ME.subst(List<&2, U32>, q => {T(f'RG.px.ok(AD.view(U32, {TW}), d, s, I, Con{{{X}, {PSR}}}, L, q, N)')}, F, {F0E}, Equal.sym(List<&2, U32>, {F0E}, F, cx_f0({M}, I, F, hrm)), hp3)
          +hfiT = LAB.subst(Array<U32>, qq => {T('faced.in(L, AD.view(U32, qq), d, Fp)')}, w, {TW}, Equal.sym(Array<U32>, {TW}, w, ew), hfi)
          +hC = cxp.t(tw, ta, d, s, I, {PSR}, L, {TL}, N, {X}, src, neg, far, {HD}, hft, hd32, hN, hB, hpF, hab)
          +hfi1 = cfs.t(I, tw, ta, d, s, {PSR}, L, {TL}, N, {X}, src, neg, far, {HD}, hft, hd32, hN, hB, hpF, hab, Fp, hfiT)
          %ew : {GF(CODE(CL,'map','P.H{KM.MG{_}, a}'), S0(CL,'AD.view(U32, map)'))}
          %ea : {GF(CODE(CL,'map',f'P.H{{KM.MG{{{TW}}}, _}}'), S0(CL,'AD.view(U32, map)'))}
          %em : {GF(CODE(CL,'_',H0), S0(CL,'AD.view(U32, _)'))}
          %Equal.sym(Array<U32> & U32, Array.get(U32, {TM}, at), ({TM}, {X}), LA.get_pair(U32, {TM}, at)) :
            {GF(CODEr(f'R.crossing.pl(_, {H0}, s, src, neg, far)'), SR(XM))}
          %Equal.sym(U32, {XM}, {X}, ePL) :
            {GF(CODEr(f'({TM}, {H1})'), SR('_'))}
          %heta2({H1}) :
            {GF(CODEr(f'({TM}, _)'), SR(X))}
          cfi.go(rest, RG.words({H1}), KMd.vals({H1}), {TM}, d, dm, s, {I1(X)}, {L1(X)}, {F1(X)}, N, and_r({PX1}, {FU1}, hC), hd32, hfmt, hdm, hN, hB, and_l({PX1}, {FU1}, hC), hokr,
            Fp, hfi1, LAT.mirror(U32, RG.words({H1})), LAT.mirror(V.Val, KMd.vals({H1})), LAT.mirror(U32, {TM}))
'''
GM=lambda w, a, m: T(f"faced.in(RG.cxs.L(RG.cxs(cs, AD.view(U32, {m}), dm, I, L, F)), AD.view(U32, RG.words({CODE('cs', m, f'P.H{{KM.MG{{{w}}}, {a}}}')})), d, RG.faced(L, AD.view(U32, {w}), d))")
out+=f'''
# from the ports the live nodes face at the start
def cfi.m(-w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +s: U32, +I: IM.Ix, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +cs: List<&2, R.FzC>,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, hfm: {{AD.full(U32, map, dm) == True{{}} : Bool}}, +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}},
  +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, hp: {HPX('AD.view(U32, w)', 'RG.pls(cs, AD.view(U32, map), dm)')}, hok: {T('RG.cxs.ok(cs, AD.view(U32, map), dm, I, F)')},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) -> {GM('w','a','map')}:
  (+tw, +ew) = mw
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, w, tw, d, ew, hf)
  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
  +hpa = LAB.subst(Array<U32>, qq => {HPX('AD.view(U32, qq)', 'RG.pls(cs, AD.view(U32, map), dm)')}, w, {TW}, Equal.sym(Array<U32>, {TW}, w, ew), hp)
  +hpb = LAB.subst(Array<U32>, qq => {HPX(f'AD.view(U32, {TW})', 'RG.pls(cs, AD.view(U32, qq), dm)')}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hpa)
  +hoT = LAB.subst(Array<U32>, qq => {T('RG.cxs.ok(cs, AD.view(U32, qq), dm, I, F)')}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hok)
  %ew : {GM('_','a','map')}
  %ea : {GM(TW,'_','map')}
  %em : {GM(TW,TA,'_')}
  cfi.go(cs, {TW}, {TA}, {TM}, d, dm, s, I, L, F, N, hft, hd32, hfmt, hdm, hN, hB, hpb, hoT,
    RG.faced(L, AD.view(U32, {TW}), d), faced_init(L, L, tw, d, hft, hd32, sub_refl(L)), LAT.mirror(U32, {TW}), LAT.mirror(V.Val, {TA}), LAT.mirror(U32, {TM}))
'''
if os.environ.get('CFI_ONLY'):
    open('glam/proofgen/kp/sec.txt','w').write(out)
    print('cfi', len(out.splitlines()))
else:
    p='glam/PROOF.bend'; s=open(p).read()
    assert 'def cfi.go(' not in s
    s=s.rstrip('\n')+'\n'+out
    open(p,'w').write(s)
    print('cfi', len(out.splitlines()))
