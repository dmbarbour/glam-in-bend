# authoring aid, part of gen_keeps.py: the faced ports carried through a
# crossing (faced.in after a cursor made and after a join)
import re as _re
WSEL=open('glam/proofgen/wsel.txt').read()
for f in ('word_lk','lk','sel'):
    WSEL=_re.sub(r'(?<![\w.])'+f+r'\(', 'JP.'+f+'(', WSEL)
SLz=lambda a: SL(a,'(z + 1 : U32)')
DISJ=lambda a,b: [f'KMd.off.words(KMd.nw({b}), d, {P1(a,i)})' for i in range(4)]
NDOKz=lambda a: [f'U32.is_eq(P.base({a}), {a})', f'IM.ws.apart(KMd.nw({a}), d)', f'KMd.off.words(KMd.nw({a}), d, P.at_fh())']
def W1of(a, b, hsep):   # off.words(nw(b), d, a+1) from a, b apart
    return proj(DISJ(a,b),1,f'and_l(IM.nd.disj(d, {a}, {b}), IM.nd.disj(d, {b}, {a}), {hsep})')
def NEz(m, i, hw):      # Nat.is_eq(slot(m+i), slot(z+1)) == False from off.words(nw(m), d, z+1)
    return f"MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot({P1(m,i)}, d), AD.slot((z + 1 : U32), d)), {proj(OWN(m,'(z + 1 : U32)'),i,hw)})"
FHz=(f"neq_comm2(AD.slot((z + 1 : U32), d), AD.slot(P.at_fh(), d), not_true(Nat.is_eq(AD.slot((z + 1 : U32), d), AD.slot(P.at_fh(), d)), "
     f"{proj(OWN('z','P.at_fh()'),1,proj(NDOKz('z'),2,'XL.layout_ok(N, d, z, hN, hB, hzN)'))}))")
S3z=f"nf2(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((z + 1 : U32), d)), neq_comm2(AD.slot((z + 1 : U32), d), AD.slot((s + 3 : U32), d), m13.k(U32.is_eq(z, s), z, s, N, d, {{==}}, hN, hzN, hsN)))"
def OFFBz(has, hIN):
    if not has: return S3z
    return f"and_intro({SL('(s + 3 : U32)','(z + 1 : U32)')}, IM.tr.offb(t, d, (z + 1 : U32)), {S3z}, offb_of(t, N, d, z, hN, {hIN}, hzN, hzB))"
# x's words off a live node's word 1, x itself live
SX=[SLz('x'), SLz('(x + 2 : U32)'), SLz('(x + 3 : U32)')]
SXx=lambda: [SL('x','(x + 1 : U32)'), SL('(x + 2 : U32)','(x + 1 : U32)'), SL('(x + 3 : U32)','(x + 1 : U32)')]
AP='lay_self(N, d, x, hN, hxN)'
O0=f'and_l(RG.off([(x + 1 : U32), (x + 2 : U32), (x + 3 : U32)], d, x), RG.apartw([(x + 1 : U32), (x + 2 : U32), (x + 3 : U32)], d), {AP})'
A1=f'and_r(RG.off([(x + 1 : U32), (x + 2 : U32), (x + 3 : U32)], d, x), RG.apartw([(x + 1 : U32), (x + 2 : U32), (x + 3 : U32)], d), {AP})'
O1=f'and_l(RG.off([(x + 2 : U32), (x + 3 : U32)], d, (x + 1 : U32)), RG.apartw([(x + 2 : U32), (x + 3 : U32)], d), {A1})'
c0=(f"nf2(Nat.is_eq(AD.slot(x, d), AD.slot((x + 1 : U32), d)), neq_comm2(AD.slot((x + 1 : U32), d), AD.slot(x, d), not_true(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(x, d)), "
    f"and_l({SL('(x + 1 : U32)','x')}, RG.off([(x + 2 : U32), (x + 3 : U32)], d, x), {O0}))))")
c2=f"and_l({SL('(x + 2 : U32)','(x + 1 : U32)')}, RG.off([(x + 3 : U32)], d, (x + 1 : U32)), {O1})"
c3=f"and_l({SL('(x + 3 : U32)','(x + 1 : U32)')}, True{{}}, and_r({SL('(x + 2 : U32)','(x + 1 : U32)')}, RG.off([(x + 3 : U32)], d, (x + 1 : U32)), {O1}))"
W1x=W1of('z','x','XL.layout_sep(N, d, z, x, hN, hzN, hxN, he)')
sec+=f"""
# the cursor's written words off a live node's word 1, the cursor's own
def sx.k(+e: Bool, +z: U32, +x: U32, +N: List<&2, U32>, +d: Nat, +he: {{U32.is_eq(z, x) == e : Bool}}, +hN: {T('RG.layout(N, d)')}, +hzN: {T('RG.has(N, z)')}, +hxN: {T('RG.has(N, x)')}) ->
  {T(conj(SX))}:
  match e:
    case True{{}}:
      %Equal.sym(U32, z, x, MS.u32_eq_of_is_eq(z, x, he)) : {T(conj([SL('x','(_ + 1 : U32)'), SL('(x + 2 : U32)','(_ + 1 : U32)'), SL('(x + 3 : U32)','(_ + 1 : U32)')]))}
      {intro(SXx(), [c0, c2, c3])}
    case False{{}}:
      {intro(SX, [proj(OWN('x','(z + 1 : U32)'),i,W1x) for i in (0,2,3)])}

# the port each of ys faces among Fp after a link, its word 1 the port it
# faced, or the port either joined node faced (link_live's ind_f)
def fi_lk(ys: List<&2, U32>, +t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +Fp: List<&2, U32>, +x: U32, +y: U32, +u: U32, +w: U32, +su: Bool, +sw: Bool,
  +e1: {{LAT.fromT(U32, t1) == JP.lk(su, LAT.fromT(U32, t0), u, w) : Array<U32>}}, +hsu: {{P.is_static(u) == su : Bool}}, +hsw: {{P.is_static(w) == sw : Bool}}, +hft: {{AD.full(U32, LAT.fromT(U32, t0), d) == True{{}} : Bool}},
  +hft1: {{AD.full(U32, LAT.fromT(U32, t1), d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hs1: {T('RG.sub(L2, L)')}, +hUF: {T('RG.has(Fp, u)')}, +hWF: {T('RG.has(Fp, w)')},
  +hfi: {T('faced.in(L, AD.view(U32, LAT.fromT(U32, t0)), d, Fp)')}, +hys: {T('RG.sub(ys, L2)')}) -> {T('faced.in(ys, AD.view(U32, JP.lk(sw, LAT.fromT(U32, t1), w, u)), d, Fp)')}:
  match ys:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      +hz2 = and_l(RG.has(L2, z), RG.sub(r, L2), hys)
      +hzL = sub_has(L2, L, z, hs1, hz2)
      +hz0 = fin_word(t0, d, Fp, (z + 1 : U32), hft, hd32, fi_at(L, AD.view(U32, LAT.fromT(U32, t0)), d, Fp, z, hfi, hzL))
      +hsel = hs_sel(KMd.off.port(d, w, (z + 1 : U32)), JP.sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u, Fp,
        hs_sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w, Fp, hz0, hWF), hUF)
      +hwz = ME.subst(U32, q => {T('RG.has(Fp, q)')}, JP.sel(KMd.off.port(d, w, (z + 1 : U32)), JP.sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u),
        KMd.word(AD.view(U32, JP.lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), Equal.sym(U32, KMd.word(AD.view(U32, JP.lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)),
          JP.sel(KMd.off.port(d, w, (z + 1 : U32)), JP.sel(KMd.off.port(d, u, (z + 1 : U32)), KMd.word(AD.view(U32, LAT.fromT(U32, t0)), d, (z + 1 : U32)), w), u), {WSEL}), hsel)
      and_intro({FIN('AD.view(U32, JP.lk(sw, LAT.fromT(U32, t1), w, u))','z')}, faced.in(r, AD.view(U32, JP.lk(sw, LAT.fromT(U32, t1), w, u)), d, Fp),
        {WORDFIN('JP.lk(sw, LAT.fromT(U32, t1), w, u)', '(z + 1 : U32)', 'JP.lk_full(sw, LAT.fromT(U32, t1), d, w, u, hft1)', f"ME.subst(U32, q => {T('RG.has(Fp, q)')}, KMd.word(AD.view(U32, JP.lk(sw, LAT.fromT(U32, t1), w, u)), d, (z + 1 : U32)), {GETt('JP.lk(sw, LAT.fromT(U32, t1), w, u)','(z + 1 : U32)')}, XP.wg(JP.lk(sw, LAT.fromT(U32, t1), w, u), d, (z + 1 : U32), JP.lk_full(sw, LAT.fromT(U32, t1), d, w, u, hft1), hd32), hwz)")},
        fi_lk(r, t0, t1, d, L, L2, Fp, x, y, u, w, su, sw, e1, hsu, hsw, hft, hft1, hd32, hs1, hUF, hWF, hfi, and_r(RG.has(L2, z), RG.sub(r, L2), hys)))

def fi_lk.m(+t0: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +Fp: List<&2, U32>, +x: U32, +y: U32, +u: U32, +w: U32, +su: Bool, +sw: Bool,
  +hsu: {{P.is_static(u) == su : Bool}}, +hsw: {{P.is_static(w) == sw : Bool}}, +hft: {{AD.full(U32, LAT.fromT(U32, t0), d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}},
  +hs1: {T('RG.sub(L2, L)')}, +hUF: {T('RG.has(Fp, u)')}, +hWF: {T('RG.has(Fp, w)')}, +hfi: {T('faced.in(L, AD.view(U32, LAT.fromT(U32, t0)), d, Fp)')},
  -w1: Array<U32>, +hw1: {{w1 == JP.lk(su, LAT.fromT(U32, t0), u, w) : Array<U32>}}, hf1: {{AD.full(U32, w1, d) == True{{}} : Bool}}, m1: LAT.Mirror(U32, w1)) -> {T('faced.in(L2, AD.view(U32, JP.lk(sw, w1, w, u)), d, Fp)')}:
  (+t1, +e0) = m1
  +hft1 = LAP.full_t(U32, w1, t1, d, e0, hf1)
  +e1 = Equal.trans(Array<U32>, LAT.fromT(U32, t1), w1, JP.lk(su, LAT.fromT(U32, t0), u, w), e0, hw1)
  %e0 : {T('faced.in(L2, AD.view(U32, JP.lk(sw, _, w, u)), d, Fp)')}
  fi_lk(L2, t0, t1, d, L, L2, Fp, x, y, u, w, su, sw, e1, hsu, hsw, hft, hft1, hd32, hs1, hUF, hWF, hfi, sub_refl(L2))
"""
