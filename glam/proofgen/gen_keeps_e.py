# authoring aid, part of gen_keeps.py: the faced ports after a crossing,
# the fold over the crossings and crossings_keeps' entry
FC=lambda h: T(f'faced.in(L, AD.view(U32, RG.words({h})), d, Fp)')
C1=lambda I0s: PXOK(f'AD.view(U32, RG.words({CUR}))', f'IM.ix.put({I0s}, x, src, b)', 'ps', 'L', 'F', 'N')
FPR=f"+Fp: List<&2, U32>, +hfi: {T(f'faced.in(L, {V0}, d, Fp)')}"
sec+=f"""
# the faced ports after a cursor made
def cfs.c(I: IM.Ix, {CKPAR},
  +hp: {T(f'RG.px.ok({V0}, d, s, I, Con{{x, ps}}, L, IM.ix.take(I, b, F), N)')}, +ha: {{IM.ix.look(I, src) == None{{}} : Maybe<&2, U32>}}, {FPR}) -> {FC(CUR)}:
  match I:
    case IM.Ept{{}}:
      cfi.ept(L, t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, ha, Fp, hfi,
        and_r({conj(C1('IM.Ept{}'))}, AD.full(U32, RG.words({CUR}), d), cpx.ept(t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, ha)), sub_refl(L))
    case IM.Has{{+t}}:
      cfi.has(L, t, t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, ha, Fp, hfi,
        and_r({conj(C1('IM.Has{t}'))}, AD.full(U32, RG.words({CUR}), d), cpx.has(t, t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, ha)), sub_refl(L))

# the faced ports after a join
def jfi.t(+t: IM.Tr, {JKPAR},
  +hp: {T(conj(Cj))}, +hy: {{IM.ix.look(IM.Has{{t}}, k) == Some{{y}} : Maybe<&2, U32>}}, {FPR}) -> {GJ2(L2s)}:
{lets}{lets2}  +hUF = fin_word(t0, d, Fp, (x + 1 : U32), hft, hd32, fi_at(L, {V0}, d, Fp, x, hfi, hxL))
  +hWF = fin_word(t0, d, Fp, (y + 1 : U32), hft, hd32, fi_at(L, {V0}, d, Fp, y, hfi, hyL))
  +hLK = fi_lk.m(t0, d, L, {L2s}, Fp, x, y, {UU}, {WW}, P.is_static({UU}), P.is_static({WW}), {{==}}, {{==}}, hft, hd32, hs1, hUF, hWF, hfi, {LK1}, {{==}}, JP.lk_full(P.is_static({UU}), {A0}, d, {UU}, {WW}, hft), LAT.mirror(U32, {LK1}))
  +hfW = and_r({conj(PXOK(f'AD.view(U32, {WJ})', 'IM.ix.del(IM.Has{t}, y, k)', 'ps', L2s, FP('IM.mb.cons(IM.ix.par(IM.Has{t}, y, k), F)'), 'N'))}, AD.full(U32, {WJ}, d),
    jpx.k(IM.Has{{t}}, t0, ta, d, s, ps, L, F, N, x, y, k, hft, hd32, hN, hB, hp, hy))
  jfi.go({L2s}, {JGA}, sub_refl({L2s}))

def jfi.k(I: IM.Ix, {JKPAR},
  +hp: {T(f'RG.px.ok({V0}, d, s, I, Con{{x, ps}}, L, F, N)')}, +hy: {{IM.ix.look(I, k) == Some{{y}} : Maybe<&2, U32>}}, {FPR}) -> {GJ2(L2s)}:
  match I:
    case IM.Ept{{}}:
      Empty.absurd({GJ2(L2s)}, MB.false_ne_true()(Equal.cong(Maybe<&2, U32>, Bool, mm => XP.is_some(mm), None{{}}, Some{{y}}, hy)))
    case IM.Has{{+t}}:
      jfi.t(t, t0, ta, d, s, ps, L, F, N, x, y, k, hft, hd32, hN, hB, hp, hy, Fp, hfi)

# the faced ports after a crossing, among the first ones still
def cfs.k(+m: Maybe<&2, U32>, +I: IM.Ix, {XPAR}, +he: {{IM.ix.look(I, far) == m : Maybe<&2, U32>}}, +hp: {HPm('m')}, +ha: {T('RG.cx.ab(m, I, src)')}, {FPR}) ->
  {T(f'faced.in(RG.cx.L(m, x, L), AD.view(U32, RG.words({CROSSK})), d, Fp)')}:
  match m:
    case Some{{+y}}:
      jfi.k(I, t0, ta, d, s, ps, L, F, N, x, y, far, hft, hd32, hN, hB, hp, he, Fp, hfi)
    case None{{}}:
      cfs.c(I, t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, isnone_eq(IM.ix.look(I, src), ha), Fp, hfi)

def cfs.t(+I: IM.Ix, {XPAR}, +hp: {HPm('IM.ix.look(I, far)')}, +ha: {T('RG.cx.ab(IM.ix.look(I, far), I, src)')}, {FPR}) ->
  {T(f'faced.in(RG.cx.L(IM.ix.look(I, far), x, L), AD.view(U32, RG.words(R.cross({H0}, s, x, src, neg, far))), d, Fp)')}:
  +hre = and_l(IM.ix.real({V0}, d, s, I), {nsX['REST1']}, hp)
  +hiv = and_l(IM.ix.inv(I), {nsX['REST2']}, and_r(IM.ix.real({V0}, d, s, I), {nsX['REST1']}, hp))
  %Equal.sym(P.H & Maybe<&2, U32>, X.ix.find({H0}, s, far), ({H0}, IM.ix.look(I, far)), XL.find_tree({A0}, {AA}, d, s, I, far, hft, hd32, hre, hiv)) :
    {T('faced.in(RG.cx.L(IM.ix.look(I, far), x, L), AD.view(U32, RG.words(R.cross.k(_, s, x, src, neg))), d, Fp)')}
  cfs.k(IM.ix.look(I, far), I, t0, ta, d, s, ps, L, F, N, x, src, neg, far, b, hft, hd32, hN, hB, {{==}}, hp, ha, Fp, hfi)
"""
# --- the fold ---
TW='LAT.fromT(U32, tw)'; TA='LAT.fromT(V.Val, ta)'; TM='LAT.fromT(U32, tm)'
HW=f'P.H{{KM.MG{{{TW}}}, {TA}}}'
def CODE(cl, mp, heap): return f'Pair.snd(Array<U32>, P.H, R.crossings({cl}, ({mp}, {heap}), s))'
def CODEr(q): return f'Pair.snd(Array<U32>, P.H, R.crossings(rest, {q}, s))'
KF=lambda code, h0: f'{{{RD(code,"j")} == {RD(h0,"j")} : U32}}'
CLx='Con{R.FzC{at, src, neg, far}, rest}'
Mx='IM.ix.look(I, far)'; HDx='RG.cx.hd(F)'; TLx=f'RG.cx.tl({Mx}, I, F)'
F0x=f'RG.cx.F0({Mx}, I, {HDx}, {TLx})'
XMx=f'RG.pl.of(List.get(&2, U32, AD.view(U32, {TM}), AD.slot(at, dm)))'
Xx=f'Pair.snd(Array<U32>, U32, Array.get(U32, {TM}, at))'
PSRx=f'RG.pls(rest, AD.view(U32, {TM}), dm)'
I1x=f'RG.cx.I({Mx}, I, {Xx}, src, {HDx}, far)'; L1x=f'RG.cx.L({Mx}, {Xx}, L)'; F1x=f'RG.cx.F1({Mx}, I, {Xx}, far, {TLx})'
H1x=f'R.cross({HW}, s, {Xx}, src, neg, far)'
PX1x=f'RG.px.ok(AD.view(U32, RG.words({H1x})), d, s, {I1x}, {PSRx}, {L1x}, {F1x}, N)'; FU1x=f'AD.full(U32, RG.words({H1x}), d)'
ABx=f'RG.cx.ab({Mx}, I, src)'; RMx=f'RG.cx.room({Mx}, I, F)'
OKRx=lambda vm, x: f'RG.cxs.ok(rest, {vm}, dm, RG.cx.I({Mx}, I, {x}, src, {HDx}, far), RG.cx.F1({Mx}, I, {x}, far, {TLx}))'
HPXw=lambda v, ps: T(f'RG.px.ok({v}, d, s, I, {ps}, L, F, N)')
XMqx=lambda q: f'RG.pl.of(List.get(&2, U32, AD.view(U32, {q}), AD.slot(at, dm)))'
JPF=f"+Fp: List<&2, U32>, +j: U32, +hj: {T('RG.off.nodes(N, d, j)')}, +hjh: {NE_('P.at_fh()','j')}, +hjf: {T('RG.off.ports(Fp, d, j)')}"
sec+=f"""
# the crossings in turn: every word off the tracked nodes', the free list's
# head and the faced ports' link words as it was
def crk.go(cl: List<&2, R.FzC>, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +s: U32, +I: IM.Ix, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, hfm: {{AD.full(U32, map, dm) == True{{}} : Bool}}, +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}},
  +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, hp: {HPXw('AD.view(U32, w)', 'RG.pls(cl, AD.view(U32, map), dm)')}, hok: {T('RG.cxs.ok(cl, AD.view(U32, map), dm, I, F)')},
  {JPF}, hfi: {T('faced.in(L, AD.view(U32, w), d, Fp)')}, mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {KF(CODE('cl','map','P.H{KM.MG{w}, a}'),'P.H{KM.MG{w}, a}')}:
  match cl:
    case Nil{{}}:
      {{==}}
    case Con{{c, +rest}}:
      match c:
        case R.FzC{{+at, +src, +neg, +far}}:
          (+tw, +ew) = mw
          (+ta, +ea) = ma
          (+tm, +em) = mm
          +hft = LAP.full_t(U32, w, tw, d, ew, hf)
          +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
          +ePL = ME.subst(Maybe<&2, U32>, q => {{RG.pl.of(q) == {Xx} : U32}}, Some{{{Xx}}}, List.get(&2, U32, AD.view(U32, {TM}), AD.slot(at, dm)), LA.get_view(U32, {TM}, dm, at, hfmt, hdm), {{==}})
          +hpa = LAB.subst(Array<U32>, qq => {HPXw('AD.view(U32, qq)', 'Con{'+XMqx('map')+', RG.pls(rest, AD.view(U32, map), dm)}')}, w, {TW}, Equal.sym(Array<U32>, {TW}, w, ew), hp)
          +hpb = LAB.subst(Array<U32>, qq => {HPXw(f'AD.view(U32, {TW})', 'Con{'+XMqx('qq')+', RG.pls(rest, AD.view(U32, qq), dm)}')}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hpa)
          +hp3 = ME.subst(U32, q => {HPXw(f'AD.view(U32, {TW})', 'Con{q, '+PSRx+'}')}, {XMx}, {Xx}, ePL, hpb)
          +hoa = LAB.subst(Array<U32>, qq => {T(f'({ABx} && {RMx}) && '+OKRx('AD.view(U32, qq)', XMqx('qq')))}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hok)
          +hob = ME.subst(U32, q => {T(f'({ABx} && {RMx}) && '+OKRx(f'AD.view(U32, {TM})', 'q'))}, {XMx}, {Xx}, ePL, hoa)
          +hab = and_l({ABx}, {RMx}, and_l({ABx} && {RMx}, {OKRx(f'AD.view(U32, {TM})', Xx)}, hob))
          +hrm = and_r({ABx}, {RMx}, and_l({ABx} && {RMx}, {OKRx(f'AD.view(U32, {TM})', Xx)}, hob))
          +hokr = and_r({ABx} && {RMx}, {OKRx(f'AD.view(U32, {TM})', Xx)}, hob)
          +hpF = ME.subst(List<&2, U32>, q => {T(f'RG.px.ok(AD.view(U32, {TW}), d, s, I, Con{{{Xx}, {PSRx}}}, L, q, N)')}, F, {F0x}, Equal.sym(List<&2, U32>, {F0x}, F, cx_f0({Mx}, I, F, hrm)), hp3)
          +hfiT = LAB.subst(Array<U32>, qq => {T('faced.in(L, AD.view(U32, qq), d, Fp)')}, w, {TW}, Equal.sym(Array<U32>, {TW}, w, ew), hfi)
          +hC = cxp.t(tw, ta, d, s, I, {PSRx}, L, {TLx}, N, {Xx}, src, neg, far, {HDx}, hft, hd32, hN, hB, hpF, hab)
          +hst = cks.t(I, tw, ta, d, s, {PSRx}, L, {TLx}, N, {Xx}, src, neg, far, {HDx}, hft, hd32, hN, hB, hpF, hab, Fp, j, hj, hjh, hjf, hfiT)
          +hfi1 = cfs.t(I, tw, ta, d, s, {PSRx}, L, {TLx}, N, {Xx}, src, neg, far, {HDx}, hft, hd32, hN, hB, hpF, hab, Fp, hfiT)
          %ew : {KF(CODE(CLx,'map','P.H{KM.MG{_}, a}'),'P.H{KM.MG{_}, a}')}
          %ea : {KF(CODE(CLx,'map',f'P.H{{KM.MG{{{TW}}}, _}}'),f'P.H{{KM.MG{{{TW}}}, _}}')}
          %em : {KF(CODE(CLx,'_',HW),HW)}
          %Equal.sym(Array<U32> & U32, Array.get(U32, {TM}, at), ({TM}, {Xx}), LA.get_pair(U32, {TM}, at)) :
            {KF(CODEr(f'R.crossing.pl(_, {HW}, s, src, neg, far)'),HW)}
          %heta2({H1x}) :
            {KF(CODEr(f'({TM}, _)'),HW)}
          {trans('U32',[RD(CODEr(f'({TM}, P.H{{KM.MG{{RG.words({H1x})}}, KMd.vals({H1x})}})'),'j'), RD(f'P.H{{KM.MG{{RG.words({H1x})}}, KMd.vals({H1x})}}','j'), RD(H1x,'j'), RD(HW,'j')],
            [f"crk.go(rest, RG.words({H1x}), KMd.vals({H1x}), {TM}, d, dm, s, {I1x}, {L1x}, {F1x}, N, and_r({PX1x}, {FU1x}, hC), hd32, hfmt, hdm, hN, hB, and_l({PX1x}, {FU1x}, hC), hokr, Fp, j, hj, hjh, hjf, hfi1, LAT.mirror(U32, RG.words({H1x})), LAT.mirror(V.Val, KMd.vals({H1x})), LAT.mirror(U32, {TM}))",
             f"Equal.cong(P.H, U32, hh => {RD('hh','j')}, P.H{{KM.MG{{RG.words({H1x})}}, KMd.vals({H1x})}}, {H1x}, heta2({H1x}))", 'hst'])}

def crossings_keeps.m(-w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +s: U32, +I: IM.Ix, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +cs: List<&2, R.FzC>, +j: U32,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, hfm: {{AD.full(U32, map, dm) == True{{}} : Bool}}, +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}},
  +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, hp: {HPXw('AD.view(U32, w)', 'RG.pls(cs, AD.view(U32, map), dm)')}, hok: {T('RG.cxs.ok(cs, AD.view(U32, map), dm, I, F)')},
  +hj: {T('RG.off.nodes(N, d, j)')}, +hjh: {NE_('P.at_fh()','j')}, hjf: {T('RG.off.ports(RG.faced(L, AD.view(U32, w), d), d, j)')},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) -> {KF(CODE('cs','map','P.H{KM.MG{w}, a}'),'P.H{KM.MG{w}, a}')}:
  (+tw, +ew) = mw
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, w, tw, d, ew, hf)
  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
  +hpa = LAB.subst(Array<U32>, qq => {HPXw('AD.view(U32, qq)', 'RG.pls(cs, AD.view(U32, map), dm)')}, w, {TW}, Equal.sym(Array<U32>, {TW}, w, ew), hp)
  +hpb = LAB.subst(Array<U32>, qq => {HPXw(f'AD.view(U32, {TW})', 'RG.pls(cs, AD.view(U32, qq), dm)')}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hpa)
  +hoT = LAB.subst(Array<U32>, qq => {T('RG.cxs.ok(cs, AD.view(U32, qq), dm, I, F)')}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hok)
  +hjfT = LAB.subst(Array<U32>, qq => {T('RG.off.ports(RG.faced(L, AD.view(U32, qq), d), d, j)')}, w, {TW}, Equal.sym(Array<U32>, {TW}, w, ew), hjf)
  %ew : {KF(CODE('cs','map','P.H{KM.MG{_}, a}'),'P.H{KM.MG{_}, a}')}
  %ea : {KF(CODE('cs','map',f'P.H{{KM.MG{{{TW}}}, _}}'),f'P.H{{KM.MG{{{TW}}}, _}}')}
  %em : {KF(CODE('cs','_',HW),HW)}
  crk.go(cs, {TW}, {TA}, {TM}, d, dm, s, I, L, F, N, hft, hd32, hfmt, hdm, hN, hB, hpb, hoT,
    RG.faced(L, AD.view(U32, {TW}), d), j, hj, hjh, hjfT, faced_init(L, L, tw, d, hft, hd32, sub_refl(L)), LAT.mirror(U32, {TW}), LAT.mirror(V.Val, {TA}), LAT.mirror(U32, {TM}))

def Laws.crossings_keeps(w, a, map, d, dm, s, I, L, F, N, cs, j, hf, hd32, hfm, hdm, hN, hB, hp, hok, hj, hjh, hjf):
  crossings_keeps.m(w, a, map, d, dm, s, I, L, F, N, cs, j, hf, hd32, hfm, hdm, hN, hB, hp, hok, hj, hjh, hjf, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))
"""
