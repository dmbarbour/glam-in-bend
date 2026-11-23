# authoring aid: a leave's link over the live nodes' facing (glam/JOIN_LAWS.bend
# link_leave, glam/JOIN_PROOF.bend): a port p, off every tracked node's
# words, linked to the port a live node c faced
import os
T=lambda h: f'{{{h} == True{{}} : Bool}}'
F_=lambda h: f'{{{h} == False{{}} : Bool}}'
def conj(t): return t[0] if len(t)==1 else (f'{t[0]} && ({conj(t[1:])})' if len(t)>2 else f'{t[0]} && {t[1]}')
A0='LAT.fromT(U32, t0)'; A1='LAT.fromT(U32, t1)'
V0=f'AD.view(U32, {A0})'; V1v=f'AD.view(U32, {A1})'
W=f'KMd.word({V0}, d, (c + 1 : U32))'
LKa=f'JP_lk(su, {A0}, p, {W})'
LKb=f'lk(sw, {A1}, {W}, p)'
VB=f'AD.view(U32, {LKb})'
WD=lambda v,i: f'KMd.word({v}, d, {i})'
OP=lambda r,j: f'KMd.off.port(d, {r}, {j})'
Z1='(z + 1 : U32)'; Q1='(q + 1 : U32)'; C1='(c + 1 : U32)'
OFF3=lambda r,n: f'{OP(r,f"({n} + 1 : U32)")} && ({OP(r,f"({n} + 2 : U32)")} && {OP(r,f"({n} + 3 : U32)")})'
fz=WD(V0,Z1); fq=WD(V0,Q1)
LVP=(f"+t0: LAT.Tree<U32>, +t1: LAT.Tree<U32>, +d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +c: U32, +p: U32, +su: Bool, +sw: Bool,\n"
     f"  +e1: {{{A1} == lk(su, {A0}, p, {W}) : Array<U32>}}, +hsu: {{P.is_static(p) == su : Bool}}, +hsw: {{P.is_static({W}) == sw : Bool}}, +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}},\n"
     f"  +hft1: {{AD.full(U32, {A1}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hLN: {T('RG.sub(L, N)')}, +hc: {T('RG.has(L, c)')},\n"
     f"  +hs1: {T('RG.sub(L2, L)')}, +hs2: {T('RG.sub(L, Con{c, L2})')}, +hc2: {F_('RG.has(L2, c)')}, +hpo: {T('RG.po.all(p, [], d, N)')}, +hpk: {T('RG.port.ok(L, d, p)')},\n"
     f"  +hF: {T(f'RG.faces(L, {V0}, d, L)')}, +hO: {T(f'RG.px.off(L, {V0}, d, L, N)')}, +hT: {T(f'RG.px.tw(L, {V0}, d, L)')}")
LVA='t0, t1, d, L, L2, N, c, p, su, sw, e1, hsu, hsw, hft, hft1, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT'
B=lambda z: OP(W, f'({z} + 1 : U32)')
PZ=lambda z: OP('p', f'({z} + 1 : U32)')
def WZ(z, hp1):   # word z+1 after the link: sel(B_z, f_z, p)
    fzz=WD(V0,f'({z} + 1 : U32)'); w1=WD(V1v,f'({z} + 1 : U32)'); wb=WD(VB,f'({z} + 1 : U32)')
    wa=WD(f'AD.view(U32, lk(su, {A0}, p, {W}))', f'({z} + 1 : U32)')
    nodes=[wb, f'sel({B(z)}, {w1}, p)', f'sel({B(z)}, sel({PZ(z)}, {fzz}, {W}), p)', f'sel({B(z)}, {fzz}, p)']
    pr=[f'word_lk(sw, t1, d, {W}, p, ({z} + 1 : U32), hsw, hft1, hd32)',
        f"Equal.cong(U32, U32, qq => sel({B(z)}, qq, p), {w1}, sel({PZ(z)}, {fzz}, {W}), Equal.trans(U32, {w1}, {wa}, sel({PZ(z)}, {fzz}, {W}), Equal.cong(Array<U32>, U32, AA => KMd.word(AD.view(U32, AA), d, ({z} + 1 : U32)), {A1}, lk(su, {A0}, p, {W}), e1), word_lk(su, t0, d, p, {W}, ({z} + 1 : U32), hsu, hft, hd32)))",
        f"Equal.cong(U32, U32, qq => sel({B(z)}, qq, p), sel({PZ(z)}, {fzz}, {W}), {fzz}, Equal.cong(Bool, U32, bb => sel(bb, {fzz}, {W}), {PZ(z)}, True{{}}, {hp1}))"]
    t=pr[-1]
    for k in range(len(pr)-2, -1, -1):
        t=f'Equal.trans(U32, {nodes[k]}, {nodes[k+1]}, {nodes[-1]}, {pr[k]}, {t})'
    return t
SUBW=lambda pred, a, b, e, h: f"ME.subst(U32, xx => {pred('xx')}, {a}, {b}, {e}, {h})"
sec=f'''
# A leave's link (link_leave): a port p, its link word off every tracked
# node's words and the free list's head (RG.po.all over no live node),
# linked to the port a live node c faced. The word a live node of L2
# holds after: what it faced, or p where it faced c (sel)

# p's link word off a tracked node's word 1
def pp1(N: List<&2, U32>, +p: U32, +d: Nat, +z: U32, +h: {T('RG.po.all(p, [], d, N)')}, hz: {T('RG.has(N, z)')}) -> {T(OP('p',Z1))}:
  match N:
    case Nil{{}}:
      Empty.absurd({T(OP('p',Z1))}, MB.false_ne_true()(hz))
    case Con{{+n, +r}}:
      or_cases2(U32.is_eq(n, z), RG.has(r, z), {OP('p',Z1)}, hz,
        e => ME.subst(U32, zz => {T(OP('p','(zz + 1 : U32)'))}, n, z, MS.u32_eq_of_is_eq(n, z, e), and_l({OP('p','(n + 1 : U32)')}, {OP('p','(n + 2 : U32)')} && {OP('p','(n + 3 : U32)')}, and_r({OP('p','n')}, {OFF3('p','n')}, and_l(RG.po.n(p, [], d, n), RG.po.all(p, [], d, r), h)))),
        e => pp1(r, p, d, z, and_r(RG.po.n(p, [], d, n), RG.po.all(p, [], d, r), h), e))

def or_cases2(+a: Bool, +b: Bool, +c: Bool, h: {T('Bool.or(a, b)')}, fa: {T('a')} -> {T('c')}, fb: {T('b')} -> {T('c')}) -> {T('c')}:
  match a:
    case True{{}}:
      fa({{==}})
    case False{{}}:
      fb(h)

# p's facts over any live nodes
def pmono.n(+r: U32, +L: List<&2, U32>, +d: Nat, +n: U32, +h: {T(f'RG.po.n(r, [], d, n)')}) -> {T('RG.po.n(r, L, d, n)')}:
  and_intro({OP('r','n')}, Bool.or(RG.has(L, n), {OFF3('r','n')}), and_l({OP('r','n')}, {OFF3('r','n')}, h), or_r2(RG.has(L, n), {OFF3('r','n')}, and_r({OP('r','n')}, {OFF3('r','n')}, h)))

def or_r2(a: Bool, +b: Bool, hb: {T('b')}) -> {T('Bool.or(a, b)')}:
  match a:
    case True{{}}:
      {{==}}
    case False{{}}:
      hb

def pmono(N: List<&2, U32>, +r: U32, +L: List<&2, U32>, +d: Nat, +h: {T('RG.po.all(r, [], d, N)')}) -> {T('RG.po.all(r, L, d, N)')}:
  match N:
    case Nil{{}}:
      h
    case Con{{+n, +k}}:
      and_intro(RG.po.n(r, L, d, n), RG.po.all(r, L, d, k), pmono.n(r, L, d, n, and_l(RG.po.n(r, [], d, n), RG.po.all(r, [], d, k), h)), pmono(k, r, L, d, and_r(RG.po.n(r, [], d, n), RG.po.all(r, [], d, k), h)))

def pk_sel2(+b: Bool, +f: U32, +q: U32, +d: Nat, +M: List<&2, U32>, +hf: {T('RG.port.ok(M, d, f)')}, +hq: {T('RG.port.ok(M, d, q)')}) -> {T('RG.port.ok(M, d, sel(b, f, q))')}:
  match b:
    case True{{}}:
      hf
    case False{{}}:
      hq
'''
# faces
def zfacts():
    return (f"      +hz2 = and_l(RG.has(L2, z), RG.sub(r, L2), hys)\n"
            f"      +hzL = sub_has2(L2, L, z, hs1, hz2)\n"
            f"      +hzN = sub_has2(L, N, z, hLN, hzL)\n"
            f"      +hp1z = pp1(N, p, d, z, hpo, hzN)\n")
GV=lambda z: f'List.get(&2, U32, {VB}, AD.slot(({z} + 1 : U32), d))'
sec+=f'''
def lvf(ys: List<&2, U32>, {LVP}, +hys: {T('RG.sub(ys, L2)')}) -> {T(f'RG.faces(ys, {VB}, d, L2)')}:
  match ys:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
{zfacts()}      and_intro(RG.faces.m({GV('z')}, d, L2), RG.faces(r, {VB}, d, L2),
        fm_of_word({GV('z')}, d, L2, ME.subst(Maybe<&2, U32>, m => {{XP.is_some(m) == True{{}} : Bool}}, Some{{Pair.snd(Array<U32>, U32, Array.get(U32, {LKb}, {Z1}))}}, {GV('z')}, LA.get_view(U32, {LKb}, d, {Z1}, lk_full(sw, {A1}, d, {W}, p, hft1), hd32), {{==}}),
          {SUBW(lambda x: T(f'RG.port.ok(L2, d, {x})'), f'sel({B("z")}, {fz}, p)', WD(VB,Z1), f'Equal.sym(U32, {WD(VB,Z1)}, sel({B("z")}, {fz}, p), {WZ("z","hp1z")})',
            f"pk_sel2({B('z')}, {fz}, p, d, L2, pk_sub(L2, L, d, {fz}, hs1, fm_word(List.get(&2, U32, {V0}, AD.slot({Z1}, d)), d, L, fm_of(L, {V0}, d, L, z, hF, hzL))), pk_sub(L2, L, d, p, hs1, hpk))")}),
        lvf(r, {LVA}, and_r(RG.has(L2, z), RG.sub(r, L2), hys)))
'''

SMALL=f"""
def orfl(+a: Bool, +h: {T('Bool.or(a, False{})')}) -> {T('a')}:
  match a:
    case True{{}}:
      {{==}}
    case False{{}}:
      Empty.absurd({{False{{}} == True{{}} : Bool}}, MB.false_ne_true()(h))

def or_l2(+a: Bool, b: Bool, +ha: {T('a')}) -> {T('Bool.or(a, b)')}:
  ME.subst(Bool, zz => {T('Bool.or(zz, b)')}, True{{}}, a, Equal.sym(Bool, a, True{{}}, ha), {{==}})
"""
sec=sec.replace("# p's facts over any live nodes", SMALL+"\n# p's facts over any live nodes")
twz=f"and_r({OP(fz,Z1)}, RG.tw.q(L, {fz}, z, {V0}, d), ns_of(L, {V0}, d, L, z, hT, hzL))"
twc=f"and_r({OP(W,C1)}, RG.tw.q(L, {W}, c, {V0}, d), ns_of(L, {V0}, d, L, c, hT, hc))"
PKZ=f"fm_word(List.get(&2, U32, {V0}, AD.slot({Z1}, d)), d, L, fm_of(L, {V0}, d, L, z, hF, hzL))"
hfc=f"orfl({OP(fz,C1)}, ME.subst(Bool, bb => {T(f'Bool.or({OP(fz,C1)}, Bool.not(bb))')}, {B('z')}, True{{}}, he, tw_at(L, {fz}, z, {V0}, d, c, {twz}, hc)))"
OFFC=f"and_intro({OP(fz,C1)}, {OP(fz,'(c + 2 : U32)')} && {OP(fz,'(c + 3 : U32)')}, {hfc}, and_intro({OP(fz,'(c + 2 : U32)')}, {OP(fz,'(c + 3 : U32)')}, pk2(L, d, {fz}, c, {PKZ}, hc), pk3(L, d, {fz}, c, {PKZ}, hc)))"
sec+=f"""
def lvo.k(+b: Bool, +z: U32, {LVP}, +he: {{{B('z')} == b : Bool}}, +hzL: {T('RG.has(L, z)')}) -> {T(f'RG.po.all(sel(b, {fz}, p), L2, d, N)')}:
  match b:
    case True{{{{}}}}:
      po_shrink(N, {fz}, L, L2, c, c, d, po_of(L, {V0}, d, L, N, z, hO, hzL), sub_cons2(L, c, Con{{{{c, L2}}}}, hs2), {OFFC}, {OFFC})
    case False{{{{}}}}:
      pmono(N, p, L2, d, hpo)

def lvo(ys: List<&2, U32>, {LVP}, +hys: {T('RG.sub(ys, L2)')}) -> {T(f'RG.px.off(ys, {VB}, d, L2, N)')}:
  match ys:
    case Nil{{{{}}}}:
      {{{{==}}}}
    case Con{{{{+z, +r}}}}:
{zfacts()}      and_intro(RG.po.all({WD(VB,Z1)}, L2, d, N), RG.px.off(r, {VB}, d, L2, N),
        {SUBW(lambda x: T(f'RG.po.all({x}, L2, d, N)'), f'sel({B("z")}, {fz}, p)', WD(VB,Z1), f'Equal.sym(U32, {WD(VB,Z1)}, sel({B("z")}, {fz}, p), {WZ("z","hp1z")})', f"lvo.k({B('z')}, z, {LVA}, {{{{==}}}}, hzL)")},
        lvo(r, {LVA}, and_r(RG.has(L2, z), RG.sub(r, L2), hys)))
""".replace('{{{{','{{').replace('}}}}','}}').replace('{{','{').replace('}}','}')
# the two-way facing: a node of L2 that faced c faces p, whose link word is
# off every tracked node's word 1; one that did not keeps its facing, a
# node that faced c, its faced port c's word 1, so off its own
EQ=lambda r,q,z: f'Bool.or({OP(r,f"({q} + 1 : U32)")}, Bool.not({OP(WD(VB,f"({q} + 1 : U32)"),f"({z} + 1 : U32)")}))'
ELs=lambda r,s_,z: f'Bool.or({OP(r,Q1)}, Bool.not({OP(s_,f"({z} + 1 : U32)")}))'
twq_z=f"tw_at(L, {fz}, z, {V0}, d, q, {twz}, hqL)"
twc_q=f"tw_at(L, {W}, c, {V0}, d, q, {twc}, hqL)"
hfqc=f"MB.eq_false_of_not_eq_true({OP(fq,C1)}, ME.subst(Bool, bb => {T(f'Bool.or(bb, Bool.not({OP(fq,C1)}))')}, {B('q')}, False{{}}, he, {twc_q}))"
hfqz=f"ME.subst(Bool, bb => {T(f'Bool.or(bb, {OP(fq,Z1)})')}, {OP(fq,C1)}, False{{}}, {hfqc}, no2({fq}, c, z, d, N, hN, hcN, hzN, ueq_ne(z, c, nhas(L2, z, c, hz2, hc2))))"
sec+=f"""
def lvt.e(+b: Bool, +z: U32, +q: U32, {LVP}, +he: {{{B('q')} == b : Bool}}, +hzL: {T('RG.has(L, z)')}, +hqL: {T('RG.has(L, q)')}, +hz2: {T('RG.has(L2, z)')}, +hcN: {T('RG.has(N, c)')}, +hzN: {T('RG.has(N, z)')}) ->
  {T(ELs(fz, f'sel(b, {fq}, p)', 'z'))}:
  match b:
    case True{{}}:
      {twq_z}
    case False{{}}:
      or_l2({OP(fz,Q1)}, Bool.not({OP('p',Z1)}), orfl({OP(fz,Q1)}, ME.subst(Bool, bb => {T(f'Bool.or({OP(fz,Q1)}, Bool.not(bb))')}, {OP(fq,Z1)}, True{{}}, {hfqz}, {twq_z})))

def lvt.q(Q: List<&2, U32>, +z: U32, {LVP}, +hzL: {T('RG.has(L, z)')}, +hz2: {T('RG.has(L2, z)')}, +hcN: {T('RG.has(N, c)')}, +hzN: {T('RG.has(N, z)')}, +hQ: {T('RG.sub(Q, L2)')}) ->
  {T(f'RG.tw.q(Q, {fz}, z, {VB}, d)')}:
  match Q:
    case Nil{{}}:
      {{==}}
    case Con{{+q, +k}}:
      +hq2 = and_l(RG.has(L2, q), RG.sub(k, L2), hQ)
      +hqL = sub_has2(L2, L, q, hs1, hq2)
      +hqN = sub_has2(L, N, q, hLN, hqL)
      +hp1q = pp1(N, p, d, q, hpo, hqN)
      and_intro({EQ(fz,'q','z')}, RG.tw.q(k, {fz}, z, {VB}, d),
        {SUBW(lambda x: T(ELs(fz, x, 'z')), f'sel({B("q")}, {fq}, p)', WD(VB,Q1), f'Equal.sym(U32, {WD(VB,Q1)}, sel({B("q")}, {fq}, p), {WZ("q","hp1q")})', f"lvt.e({B('q')}, z, q, {LVA}, {{==}}, hzL, hqL, hz2, hcN, hzN)")},
        lvt.q(k, z, {LVA}, hzL, hz2, hcN, hzN, and_r(RG.has(L2, q), RG.sub(k, L2), hQ)))

def lvt.p(Q: List<&2, U32>, +z: U32, {LVP}, +hQ: {T('RG.sub(Q, L2)')}) -> {T(f'RG.tw.q(Q, p, z, {VB}, d)')}:
  match Q:
    case Nil{{}}:
      {{==}}
    case Con{{+q, +k}}:
      and_intro({EQ('p','q','z')}, RG.tw.q(k, p, z, {VB}, d),
        or_l2({OP('p',Q1)}, Bool.not({OP(WD(VB,Q1),Z1)}), pp1(N, p, d, q, hpo, sub_has2(L, N, q, hLN, sub_has2(L2, L, q, hs1, and_l(RG.has(L2, q), RG.sub(k, L2), hQ))))),
        lvt.p(k, z, {LVA}, and_r(RG.has(L2, q), RG.sub(k, L2), hQ)))

def lvt.k(+b: Bool, +z: U32, {LVP}, +he: {{{B('z')} == b : Bool}}, +hzL: {T('RG.has(L, z)')}, +hz2: {T('RG.has(L2, z)')}, +hcN: {T('RG.has(N, c)')}, +hzN: {T('RG.has(N, z)')}, +hp1z: {T(OP('p',Z1))}) ->
  {T(f"{OP(f'sel(b, {fz}, p)',Z1)} && RG.tw.q(L2, sel(b, {fz}, p), z, {VB}, d)")}:
  match b:
    case True{{}}:
      and_intro({OP(fz,Z1)}, RG.tw.q(L2, {fz}, z, {VB}, d), and_l({OP(fz,Z1)}, RG.tw.q(L, {fz}, z, {V0}, d), ns_of(L, {V0}, d, L, z, hT, hzL)), lvt.q(L2, z, {LVA}, hzL, hz2, hcN, hzN, sub_refl2(L2)))
    case False{{}}:
      and_intro({OP('p',Z1)}, RG.tw.q(L2, p, z, {VB}, d), hp1z, lvt.p(L2, z, {LVA}, sub_refl2(L2)))
"""
PT=lambda x: f"{OP(x,Z1)} && RG.tw.q(L2, {x}, z, {VB}, d)"
sec+=f"""
def lvt(ys: List<&2, U32>, {LVP}, +hys: {T('RG.sub(ys, L2)')}) -> {T(f'RG.px.tw(ys, {VB}, d, L2)')}:
  match ys:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
{zfacts()}      +hcN = sub_has2(L, N, c, hLN, hc)
      +hk = {SUBW(lambda x: T(PT(x)), f'sel({B("z")}, {fz}, p)', WD(VB,Z1), f'Equal.sym(U32, {WD(VB,Z1)}, sel({B("z")}, {fz}, p), {WZ("z","hp1z")})', f"lvt.k({B('z')}, z, {LVA}, {{==}}, hzL, hz2, hcN, hzN, hp1z)")}
      and_intro({OP(WD(VB,Z1),Z1)}, RG.tw.q(L2, {WD(VB,Z1)}, z, {VB}, d) && RG.px.tw(r, {VB}, d, L2), and_l({OP(WD(VB,Z1),Z1)}, RG.tw.q(L2, {WD(VB,Z1)}, z, {VB}, d), hk),
        and_intro(RG.tw.q(L2, {WD(VB,Z1)}, z, {VB}, d), RG.px.tw(r, {VB}, d, L2), and_r({OP(WD(VB,Z1),Z1)}, RG.tw.q(L2, {WD(VB,Z1)}, z, {VB}, d), hk), lvt(r, {LVA}, and_r(RG.has(L2, z), RG.sub(r, L2), hys))))
"""
import re as _re
def _blk(t, name):
    i=t.index('def '+name+'('); j=t.find('\ndef ', i+1)
    j=len(t) if j<0 else j
    return t[:i]+t[j+1:], t[i:j+1]
heads=''
for nm in ('or_cases2','or_r2','orfl','or_l2'):
    sec, b=_blk(sec, nm); heads+=b+'\n'
k=sec.index('# p\'s link word off a tracked node\'s word 1')
sec=sec[:k]+heads+sec[k:]
open('glam/proofgen/lv_part1.txt','w').write(sec)
print(len(sec.splitlines()))
# ---- the entry and the law ----
C3=lambda v: f'RG.faces(L2, {v}, d, L2) && (RG.px.off(L2, {v}, d, L2, N) && RG.px.tw(L2, {v}, d, L2))'
LVPh=(f"+d: Nat, +L: List<&2, U32>, +L2: List<&2, U32>, +N: List<&2, U32>, +c: U32, +p: U32")
PREM=lambda v: (f"+hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hLN: {T('RG.sub(L, N)')}, +hc: {T('RG.has(L, c)')}, +hs1: {T('RG.sub(L2, L)')}, +hs2: {T('RG.sub(L, Con{c, L2})')},\n"
                f"  +hc2: {F_('RG.has(L2, c)')}, +hpo: {T('RG.po.all(p, [], d, N)')}, +hpk: {T('RG.port.ok(L, d, p)')}")
HFOT=lambda v: f"+hF: {T(f'RG.faces(L, {v}, d, L)')}, +hO: {T(f'RG.px.off(L, {v}, d, L, N)')}, +hT: {T(f'RG.px.tw(L, {v}, d, L)')}"
LKA0=f'lk(P.is_static(p), {A0}, p, {W})'
Wv=lambda w: f'KMd.word(AD.view(U32, {w}), d, (c + 1 : U32))'
GL=lambda w,a: T(C3(f'AD.view(U32, KMd.words(P.link_xx(P.H{{KM.MG{{{w}}}, {a}}}, p, {Wv(w)})))'))
ent=f'''
def lv.k1(+t0: LAT.Tree<U32>, {LVPh}, +su: Bool, +sw: Bool, +hsu: {{P.is_static(p) == su : Bool}}, +hsw: {{P.is_static({W}) == sw : Bool}}, +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}},
  {PREM(V0)}, {HFOT(V0)},
  -w1: Array<U32>, +hw1: {{w1 == lk(su, {A0}, p, {W}) : Array<U32>}}, hf1: {{AD.full(U32, w1, d) == True{{}} : Bool}}, m1: LAT.Mirror(U32, w1)) -> {T(C3(f'AD.view(U32, lk(sw, w1, {W}, p))'))}:
  (+t1, +e0) = m1
  +hft1 = LAP.full_t(U32, w1, t1, d, e0, hf1)
  +e1 = Equal.trans(Array<U32>, {A1}, w1, lk(su, {A0}, p, {W}), e0, hw1)
  %e0 : {T(C3(f'AD.view(U32, lk(sw, _, {W}, p))'))}
  and_intro(RG.faces(L2, {VB}, d, L2), RG.px.off(L2, {VB}, d, L2, N) && RG.px.tw(L2, {VB}, d, L2), lvf(L2, {LVA}, sub_refl2(L2)),
    and_intro(RG.px.off(L2, {VB}, d, L2, N), RG.px.tw(L2, {VB}, d, L2), lvo(L2, {LVA}, sub_refl2(L2)), lvt(L2, {LVA}, sub_refl2(L2))))

def lv.k0(+t0: LAT.Tree<U32>, {LVPh}, +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, {PREM(V0)}, {HFOT(V0)}, -a: Array<V.Val>) ->
  {GL(A0,'a')}:
  %Equal.sym(P.H, P.link.to(P.is_static(p), P.H{{KM.MG{{{A0}}}, a}}, p, {W}), P.H{{KM.MG{{{LKA0}}}, a}}, lt_eq(P.is_static(p), {A0}, a, p, {W})) :
    {T(C3(f'AD.view(U32, KMd.words(P.link.to(P.is_static({W}), _, {W}, p)))'))}
  %Equal.sym(P.H, P.link.to(P.is_static({W}), P.H{{KM.MG{{{LKA0}}}, a}}, {W}, p), P.H{{KM.MG{{lk(P.is_static({W}), {LKA0}, {W}, p)}}, a}}, lt_eq(P.is_static({W}), {LKA0}, a, {W}, p)) :
    {T(C3('AD.view(U32, KMd.words(_))'))}
  lv.k1(t0, d, L, L2, N, c, p, P.is_static(p), P.is_static({W}), {{==}}, {{==}}, hft, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, {LKA0}, {{==}}, lk_full(P.is_static(p), {A0}, d, p, {W}, hft), LAT.mirror(U32, {LKA0}))

def lv.m(-w: Array<U32>, -a: Array<V.Val>, {LVPh}, hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, {PREM('AD.view(U32, w)')}, {HFOT('AD.view(U32, w)').replace('+hF','hF').replace('+hO','hO').replace('+hT','hT')},
  m: LAT.Mirror(U32, w)) -> {GL('w','a')}:
  (+t0, +e) = m
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, {A0}, w, e)
  %e : {GL('_','a')}
  lv.k0(t0, d, L, L2, N, c, p, hft, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk,
    LAB.subst(Array<U32>, q => {T('RG.faces(L, AD.view(U32, q), d, L)')}, w, {A0}, ew, hF), LAB.subst(Array<U32>, q => {T('RG.px.off(L, AD.view(U32, q), d, L, N)')}, w, {A0}, ew, hO), LAB.subst(Array<U32>, q => {T('RG.px.tw(L, AD.view(U32, q), d, L)')}, w, {A0}, ew, hT), a)

def Laws.link_leave(w, a, d, L, L2, N, c, p, hf, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT):
  lv.m(w, a, d, L, L2, N, c, p, hf, hd32, hN, hLN, hc, hs1, hs2, hc2, hpo, hpk, hF, hO, hT, LAT.mirror(U32, w))
'''
open('glam/proofgen/lv_part1.txt','a').write(ent)
LAW=f'''
# LAW: a port p, its link word off every tracked node's words and the
# free list's head (RG.po.all over no live node: a node's port none
# tracked, or a static) and faceable by the live nodes (RG.port.ok),
# linked (P.link_xx) to the port a live node c faced, the live nodes then
# L2 (L's but c): each of L2 faces a port faceable by L2, its link word
# off every tracked node's words but the live ones' words 1 to 3 and off
# the free list's head, and they face one another both ways, none itself,
# as before the link over L. A live node that faced c faces p: a leave's
# link, the copy's root port joined in the served cursor's place, or the
# eraser (cells-freeze.sharing.cursors.index.ring.leave).
# Record: cursors-indexed
# Record: copy-links-two-way
# Record: serve-premises-over-index
law link_leave:
  for w: Array<U32>
  for a: Array<V.Val>
  for +d: Nat
  for +L: List<&2, U32>
  for +L2: List<&2, U32>
  for +N: List<&2, U32>
  for +c: U32
  for +p: U32
  for hf: {{AD.full(U32, w, d) == True{{}} : Bool}}
  for hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}
  for hN: {T('RG.layout(N, d)')}
  for hLN: {T('RG.sub(L, N)')}
  for hc: {T('RG.has(L, c)')}
  for hs1: {T('RG.sub(L2, L)')}
  for hs2: {T('RG.sub(L, Con{c, L2})')}
  for hc2: {F_('RG.has(L2, c)')}
  for hpo: {T('RG.po.all(p, Nil{}, d, N)')}
  for hpk: {T('RG.port.ok(L, d, p)')}
  for hF: {T('RG.faces(L, AD.view(U32, w), d, L)')}
  for hO: {T('RG.px.off(L, AD.view(U32, w), d, L, N)')}
  for hT: {T('RG.px.tw(L, AD.view(U32, w), d, L)')}
  {GL('w','a')}
'''
open('glam/proofgen/lv_law.txt','w').write(LAW)
print('entry')
