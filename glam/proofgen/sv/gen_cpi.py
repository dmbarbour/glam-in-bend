# authoring aid: copy_pend over the index (glam/SERVE_PROOF.bend's cpi
# section), part 1: generic list, layout and px.off lemmas
import os
T=lambda h: f'{{{h} == True{{}} : Bool}}'
F_=lambda h: f'{{{h} == False{{}} : Bool}}'
AP=lambda a,b: f'List.append(&2, U32, {a}, {b})'
P1=lambda a,i: a if i==0 else f'({a} + {i} : U32)'
def lst(xs): return '[' + ', '.join(xs) + ']'
NW=lambda f: [P1(f,i) for i in range(4)]
L=lambda a,b,h: f'MB.eq_true_of_and_left({a}, {b}, {h})'
R=lambda a,b,h: f'MB.eq_true_of_and_right({a}, {b}, {h})'
A=lambda a,b,ha,hb: f'MB.and_eq_true({a}, {b}, {ha}, {hb})'
def OWS(n, x): return f'KMd.off.words(KMd.nw({n}), d, {x})'
sec=f'''
# The copy's hand-off over the index (copy_pend; the Cells plan's
# cells-freeze.sharing.cursors.index.ring.copy)
# =====================================================================

# Lists appended: a sublist's part, membership, none and distinct
def has_app_back(A: List<&2, U32>, +B: List<&2, U32>, +x: U32, +h: {T(f'RG.has({AP("A","B")}, x)')}, +hb: {F_('RG.has(B, x)')}) -> {T('RG.has(A, x)')}:
  match A:
    case Nil{{}}:
      Empty.absurd({T('RG.has([], x)')}, MB.false_ne_true()(Equal.trans(Bool, False{{}}, RG.has(B, x), True{{}}, Equal.sym(Bool, RG.has(B, x), False{{}}, hb), h)))
    case Con{{+y, +r}}:
      GP.or_cases(U32.is_eq(y, x), RG.has({AP("r","B")}, x), RG.has(Con{{y, r}}, x), h, q => SPP.or_l(U32.is_eq(y, x), RG.has(r, x), q),
        q => SPP.or_r(U32.is_eq(y, x), RG.has(r, x), has_app_back(r, B, x, q, hb)))

def sub_left(X: List<&2, U32>, +A: List<&2, U32>, +B: List<&2, U32>, +hs: {T(f'RG.sub(X, {AP("A","B")})')}, +hn: {T('RG.none.in(B, X)')}) -> {T('RG.sub(X, A)')}:
  match X:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +r}}:
      {A('RG.has(A, x)','RG.sub(r, A)', f'has_app_back(A, B, x, {L(f"RG.has({AP("A","B")}, x)", f"RG.sub(r, {AP("A","B")})", "hs")}, GP.none_has(B, Con{{x, r}}, x, hn, GP.has_head(x, r)))',
        f'sub_left(r, A, B, {R(f"RG.has({AP("A","B")}, x)", f"RG.sub(r, {AP("A","B")})", "hs")}, GP.none_sub(B, Con{{x, r}}, r, hn, GP.sub_cons_r(r, x, r, GP.sub_refl(r))))')}

def none_appl(A: List<&2, U32>, +B: List<&2, U32>, +M: List<&2, U32>, +h: {T(f'RG.none.in({AP("A","B")}, M)')}) -> {T('RG.none.in(A, M)')}:
  match A:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +r}}:
      {A('Bool.not(RG.has(M, x))','RG.none.in(r, M)', L('Bool.not(RG.has(M, x))', f'RG.none.in({AP("r","B")}, M)','h'), f'none_appl(r, B, M, {R("Bool.not(RG.has(M, x))", f"RG.none.in({AP("r","B")}, M)","h")})')}

def none_appr(A: List<&2, U32>, +B: List<&2, U32>, +M: List<&2, U32>, +h: {T(f'RG.none.in({AP("A","B")}, M)')}) -> {T('RG.none.in(B, M)')}:
  match A:
    case Nil{{}}:
      h
    case Con{{+x, +r}}:
      none_appr(r, B, M, {R("Bool.not(RG.has(M, x))", f"RG.none.in({AP("r","B")}, M)","h")})

def has_app_lf(A: List<&2, U32>, +B: List<&2, U32>, +x: U32, +h: {F_(f'RG.has({AP("A","B")}, x)')}) -> {F_('RG.has(A, x)')}:
  match A:
    case Nil{{}}:
      {{==}}
    case Con{{+y, +r}}:
      GP.or_ff(U32.is_eq(y, x), RG.has(r, x), GP.or_false_l(U32.is_eq(y, x), RG.has({AP("r","B")}, x), h), has_app_lf(r, B, x, GP.or_false_r(U32.is_eq(y, x), RG.has({AP("r","B")}, x), h)))

def dist_pre(A: List<&2, U32>, +B: List<&2, U32>, +h: {T(f'RG.distinct({AP("A","B")})')}) -> {T('RG.distinct(A)')}:
  match A:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +r}}:
      {A('Bool.not(RG.has(r, x))','RG.distinct(r)', f'GP.nf2(RG.has(r, x), has_app_lf(r, B, x, MB.eq_false_of_not_eq_true(RG.has({AP("r","B")}, x), {L(f"Bool.not(RG.has({AP("r","B")}, x))", f"RG.distinct({AP("r","B")})","h")})))',
        f'dist_pre(r, B, {R(f"Bool.not(RG.has({AP("r","B")}, x))", f"RG.distinct({AP("r","B")})","h")})')}

def dist_suf(A: List<&2, U32>, +B: List<&2, U32>, +h: {T(f'RG.distinct({AP("A","B")})')}) -> {T('RG.distinct(B)')}:
  match A:
    case Nil{{}}:
      h
    case Con{{+x, +r}}:
      dist_suf(r, B, {R(f"Bool.not(RG.has({AP("r","B")}, x))", f"RG.distinct({AP("r","B")})","h")})

# A node past the header's words, of a list past them; a sublist past them
def kpast_at(Y: List<&2, U32>, +d: Nat, +n: U32, +hp: {T('KMd.past(Y, d)')}, hn: {T('RG.has(Y, n)')}) -> {T('KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d)')}:
  match Y:
    case Nil{{}}:
      Empty.absurd({T('KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d)')}, MB.false_ne_true()(hn))
    case Con{{+y, +r}}:
      GP.or_cases(U32.is_eq(y, n), RG.has(r, n), KMd.ws.off(KMd.nw(n), KMd.hdr_all(), d), hn,
        q => ME.subst(U32, z => {T('KMd.ws.off(KMd.nw(z), KMd.hdr_all(), d)')}, y, n, MS.u32_eq_of_is_eq(y, n, q), {L('KMd.ws.off(KMd.nw(y), KMd.hdr_all(), d)','KMd.past(r, d)','hp')}),
        q => kpast_at(r, d, n, {R('KMd.ws.off(KMd.nw(y), KMd.hdr_all(), d)','KMd.past(r, d)','hp')}, q))

def kpast_sub(X: List<&2, U32>, +Y: List<&2, U32>, +d: Nat, +hs: {T('RG.sub(X, Y)')}, +hp: {T('KMd.past(Y, d)')}) -> {T('KMd.past(X, d)')}:
  match X:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +r}}:
      {A('KMd.ws.off(KMd.nw(x), KMd.hdr_all(), d)','KMd.past(r, d)', f"kpast_at(Y, d, x, hp, {L('RG.has(Y, x)','RG.sub(r, Y)','hs')})", f"kpast_sub(r, Y, d, {R('RG.has(Y, x)','RG.sub(r, Y)','hs')}, hp)")}
'''
# word i of a later node f off the fresh nodes ns, ns ++ Fa apart
for i in range(4):
    x=P1('f',i)
    w=f'SPP.an_at(n, {AP("r","Fa")}, d, f, {L(f"KMd.apart.n(n, {AP("r","Fa")}, d)", f"KMd.apart({AP("r","Fa")}, d)", "hap")}, SPP.kapp_r(r, Fa, f, hf))'
    # component i of ws.off(nw(f), nw(n)): drop i heads, then the head
    t=w
    for k in range(i):
        t=R(OWS('n',P1('f',k)), f'KMd.ws.off({lst(NW("f")[k+1:])}, KMd.nw(n), d)', t)
    t=L(OWS('n',x), f'KMd.ws.off({lst(NW("f")[i+1:])}, KMd.nw(n), d)', t)
    sec+=f'''
def nsoff{i}(ns: List<&2, U32>, +Fa: List<&2, U32>, +d: Nat, +f: U32, +hap: {T(f'KMd.apart({AP("ns","Fa")}, d)')}, +hf: {T('KMd.has(Fa, f)')}) -> {T(f'KMd.nodes.off(ns, d, {x})')}:
  match ns:
    case Nil{{}}:
      {{==}}
    case Con{{+n, +r}}:
      {A(OWS('n',x), f'KMd.nodes.off(r, d, {x})', t, f'nsoff{i}(r, Fa, d, f, {R(f"KMd.apart.n(n, {AP("r","Fa")}, d)", f"KMd.apart({AP("r","Fa")}, d)", "hap")}, hf)')}
'''
# a hole's word i off every copy node that is no hole
DISJ=lambda a,b: [f'KMd.off.words(KMd.nw({b}), d, {P1(a,i)})' for i in range(4)]
def conj(t): return t[0] if len(t)==1 else f'{t[0]} && ({conj(t[1:])})' if len(t)>2 else f'{t[0]} && {t[1]}'
def proj(cs, i, h):
    t=h
    for k in range(i):
        t=R(cs[k], conj(cs[k+1:]), t)
    if i<len(cs)-1: t=L(cs[i], conj(cs[i+1:]), t)
    return t
for i in (0,1):
    x=P1('q',i)
    sec+=f'''
def nmk{i}(+e: Bool, +x: U32, +r: List<&2, U32>, +ys: List<&2, U32>, +N: List<&2, U32>, +d: Nat, +q: U32, +he: {{RG.has(ys, x) == e : Bool}}, +hN: {T('RG.layout(N, d)')}, +hxN: {T('RG.has(N, x)')},
  +hqN: {T('RG.has(N, q)')}, +hq: {T('RG.has(ys, q)')}, +hih: {T(f'KMd.nodes.off(RG.minus(r, ys), d, {x})')}) -> {T(f'KMd.nodes.off(RG.minus.k(e, x, RG.minus(r, ys)), d, {x})')}:
  match e:
    case True{{}}:
      hih
    case False{{}}:
      {A(OWS('x',x), f'KMd.nodes.off(RG.minus(r, ys), d, {x})', proj(DISJ('q','x'), i, f"MB.eq_true_of_and_left(IM.nd.disj(d, q, x), IM.nd.disj(d, x, q), XL.layout_sep(N, d, q, x, hN, hqN, hxN, GP.nhas(ys, q, x, hq, he)))"), 'hih')}

def noff_minus{i}(xs: List<&2, U32>, +ys: List<&2, U32>, +N: List<&2, U32>, +d: Nat, +q: U32, +hN: {T('RG.layout(N, d)')}, +hs: {T('RG.sub(xs, N)')}, +hqN: {T('RG.has(N, q)')}, +hq: {T('RG.has(ys, q)')}) ->
  {T(f'KMd.nodes.off(RG.minus(xs, ys), d, {x})')}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +r}}:
      nmk{i}(RG.has(ys, x), x, r, ys, N, d, q, {{==}}, hN, {L('RG.has(N, x)','RG.sub(r, N)','hs')}, hqN, hq, noff_minus{i}(r, ys, N, d, q, hN, {R('RG.has(N, x)','RG.sub(r, N)','hs')}, hqN, hq))
'''
# px.off's ports: over a bigger L and a smaller N, over appended N
PON=lambda r,L_,n: f'RG.po.n({r}, {L_}, d, {n})'
OFF3=lambda r,n: f'KMd.off.port(d, {r}, ({n} + 1 : U32)) && (KMd.off.port(d, {r}, ({n} + 2 : U32)) && KMd.off.port(d, {r}, ({n} + 3 : U32)))'
sec+=f'''
def po_fh(N: List<&2, U32>, +r: U32, +L: List<&2, U32>, +d: Nat, +h: {T('RG.po.all(r, L, d, N)')}) -> {T('KMd.off.port(d, r, P.at_fh())')}:
  match N:
    case Nil{{}}:
      h
    case Con{{+n, +q}}:
      po_fh(q, r, L, d, {R(PON('r','L','n'),'RG.po.all(r, L, d, q)','h')})

def po_at(N: List<&2, U32>, +r: U32, +L: List<&2, U32>, +d: Nat, +n: U32, +h: {T('RG.po.all(r, L, d, N)')}, hn: {T('RG.has(N, n)')}) -> {T(PON('r','L','n'))}:
  match N:
    case Nil{{}}:
      Empty.absurd({T(PON('r','L','n'))}, MB.false_ne_true()(hn))
    case Con{{+m, +q}}:
      GP.or_cases(U32.is_eq(m, n), RG.has(q, n), {PON('r','L','n')}, hn,
        e => ME.subst(U32, z => {T(PON('r','L','z'))}, m, n, MS.u32_eq_of_is_eq(m, n, e), {L(PON('r','L','m'),'RG.po.all(r, L, d, q)','h')}),
        e => po_at(q, r, L, d, n, {R(PON('r','L','m'),'RG.po.all(r, L, d, q)','h')}, e))

def po_mono(+r: U32, +L: List<&2, U32>, +L2: List<&2, U32>, +d: Nat, +n: U32, +hl: {T('RG.sub(L, L2)')}, +h: {T(PON('r','L','n'))}) -> {T(PON('r','L2','n'))}:
  {A('KMd.off.port(d, r, n)', f'Bool.or(RG.has(L2, n), {OFF3("r","n")})', L('KMd.off.port(d, r, n)', f'Bool.or(RG.has(L, n), {OFF3("r","n")})','h'),
    f'GP.or_cases(RG.has(L, n), {OFF3("r","n")}, Bool.or(RG.has(L2, n), {OFF3("r","n")}), {R("KMd.off.port(d, r, n)", f"Bool.or(RG.has(L, n), {OFF3('r','n')})","h")}, e => SPP.or_l(RG.has(L2, n), {OFF3("r","n")}, GP.sub_has(L, L2, n, hl, e)), e => SPP.or_r(RG.has(L2, n), {OFF3("r","n")}, e))')}

def po_sub(N2: List<&2, U32>, +r: U32, +L: List<&2, U32>, +L2: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +hl: {T('RG.sub(L, L2)')}, +hs: {T('RG.sub(N2, N)')}, +h: {T('RG.po.all(r, L, d, N)')}) -> {T('RG.po.all(r, L2, d, N2)')}:
  match N2:
    case Nil{{}}:
      po_fh(N, r, L, d, h)
    case Con{{+n, +q}}:
      {A(PON('r','L2','n'),'RG.po.all(r, L2, d, q)', f"po_mono(r, L, L2, d, n, hl, po_at(N, r, L, d, n, h, {L('RG.has(N, n)','RG.sub(q, N)','hs')}))", f"po_sub(q, r, L, L2, d, N, hl, {R('RG.has(N, n)','RG.sub(q, N)','hs')}, h)")}

def po_app(A: List<&2, U32>, +B: List<&2, U32>, +r: U32, +L: List<&2, U32>, +d: Nat, +ha: {T('RG.po.all(r, L, d, A)')}, +hb: {T('RG.po.all(r, L, d, B)')}) -> {T(f'RG.po.all(r, L, d, {AP("A","B")})')}:
  match A:
    case Nil{{}}:
      hb
    case Con{{+n, +q}}:
      {A(PON('r','L','n'), f'RG.po.all(r, L, d, {AP("q","B")})', L(PON('r','L','n'),'RG.po.all(r, L, d, q)','ha'), f"po_app(q, B, r, L, d, {R(PON('r','L','n'),'RG.po.all(r, L, d, q)','ha')}, hb)")}
'''
if os.environ.get('CPI_PART')=='1':
    open('glam/proofgen/sv/cpi1.txt','w').write(sec)
    print('part1', len(sec.splitlines()))
# ---- part 2: the index realized after the copy ----
CTXP=open('glam/proofgen/sv/ctxp.txt').read()
CTXA='ts, ls, t0, ta, tm, d, dm, by, ns, s, t, hft, hd32, hfmt, hdm, hct, hl, hlay, hbs, hdy, hpa, hhd, hfr, ht'
T0='LAT.fromT(U32, t0)'; TA='LAT.fromT(V.Val, ta)'; TM='LAT.fromT(U32, tm)'
SPN=f'S.sp.nodes(ts, 0, S.Sp{{P.H{{KM.MG{{{T0}}}, {TA}}}, {TM}}}, by)'
SPL=f'S.sp.links(ls, {SPN})'
V0=f'AD.view(U32, {T0})'; V1=f'AD.view(U32, KMd.words(SM.heap({SPL})))'
WD=lambda v,j: f'KMd.word({v}, d, {j})'
MN=AP('M','ns'); NM=AP('ns','M')
XP_=f'''+M: List<&2, U32>, +hapNM: {T(f'KMd.apart({NM}, d)')}, +hpaMN: {T(f'KMd.past({MN}, d)')}'''
XA='M, hapNM, hpaMN'
def KHAS(Lst, n, h): return f"ME.subst(Bool, z => {{z == True{{}} : Bool}}, RG.has({Lst}, {n}), KMd.has({Lst}, {n}), Equal.sym(Bool, KMd.has({Lst}, {n}), RG.has({Lst}, {n}), hasb({Lst}, {n})), {h})"
def HJH(n, k, hM):   # word k of a node of M off the header's words
    t=f"kpast_at({MN}, d, {n}, hpaMN, has_app_l(M, ns, {n}, {hM}))"
    for q in range(k):
        t=R(f'KMd.off.words(KMd.hdr_all(), d, {P1(n,q)})', f'KMd.ws.off({lst(NW(n)[q+1:])}, KMd.hdr_all(), d)', t)
    t=L(f'KMd.off.words(KMd.hdr_all(), d, {P1(n,k)})', f'KMd.ws.off({lst(NW(n)[k+1:])}, KMd.hdr_all(), d)', t)
    return t
def WFR(n, k, hM):   # word k of a node of M reads alike after the copy
    return (f"Equal.cong(Maybe<&2, U32>, U32, mm => KMd.word.m(mm), List.get(&2, U32, {V1}, AD.slot({P1(n,k)}, d)), List.get(&2, U32, {V0}, AD.slot({P1(n,k)}, d)), "
            f"agree_at({CTXA}, {P1(n,k)}, nsoff{k}(ns, M, d, {n}, hapNM, {KHAS('M', n, hM)}), {HJH(n, k, hM)}))")
SUBW=lambda pred, a, b, e, h: f"ME.subst(U32, z => {pred('z')}, {a}, {b}, {e}, {h})"
NLR=AP('IM.tr.nodes(l)','IM.tr.nodes(r)')
def lf_real(v, x, kk): return [f'U32.is_eq(p, {x})', f'Bool.not(X.ix.branch({WD(v,x)}))', f'U32.is_eq({WD(v,P1(x,2))}, {kk})', f'U32.is_eq({WD(v,P1(x,3))}, s)']
# leaf: substitute words x, x+2, x+3 in turn
LP=lambda a,b,c: T(conj(['U32.is_eq(p, x)', f'Bool.not(X.ix.branch({a}))', f'U32.is_eq({b}, k)', f'U32.is_eq({c}, s)']))
w0=lambda j: WD(V0,j); w1=lambda j: WD(V1,j)
sym=lambda a,b,e: f'Equal.sym(U32, {a}, {b}, {e})'
lf=SUBW(lambda z: LP(w1('x'),w1('(x + 2 : U32)'),z), w0('(x + 3 : U32)'), w1('(x + 3 : U32)'), sym(w1('(x + 3 : U32)'), w0('(x + 3 : U32)'), WFR('x',3,'hxM')),
   SUBW(lambda z: LP(w1('x'),z,w0('(x + 3 : U32)')), w0('(x + 2 : U32)'), w1('(x + 2 : U32)'), sym(w1('(x + 2 : U32)'), w0('(x + 2 : U32)'), WFR('x',2,'hxM')),
   SUBW(lambda z: LP(z,w0('(x + 2 : U32)'),w0('(x + 3 : U32)')), w0('x'), w1('x'), sym(w1('x'), w0('x'), WFR('x',0,'hxM')), 'h')))
BRc=lambda v: ['U32.is_eq(p, b)', f'X.ix.branch({WD(v,"b")})', f'Nat.is_eq(X.ix.bitof({WD(v,"b")}), i)', f'IM.tr.real({v}, d, l, {WD(v,"(b + 2 : U32)")}, s)', f'IM.tr.real({v}, d, r, {WD(v,"(b + 3 : U32)")}, s)']
C0b=BRc(V0); C1b=BRc(V1)
hbM=L('RG.has(M, b)', f'RG.sub({NLR}, M)', 'hs')
hlM=f"GP.sub_trans(IM.tr.nodes(l), {NLR}, M, sub_app_l(IM.tr.nodes(l), IM.tr.nodes(r)), {R('RG.has(M, b)', f'RG.sub({NLR}, M)', 'hs')})"
hrM=f"GP.sub_trans(IM.tr.nodes(r), {NLR}, M, sub_app_r(IM.tr.nodes(l), IM.tr.nodes(r)), {R('RG.has(M, b)', f'RG.sub({NLR}, M)', 'hs')})"
eb=WFR('b',0,'hbM')
br=A(C1b[0], conj(C1b[1:]), proj(C0b,0,'h'),
     A(C1b[1], conj(C1b[2:]), SUBW(lambda z: T(f'X.ix.branch({z})'), w0('b'), w1('b'), sym(w1('b'), w0('b'), eb), proj(C0b,1,'h')),
       A(C1b[2], conj(C1b[3:]), SUBW(lambda z: T(f'Nat.is_eq(X.ix.bitof({z}), i)'), w0('b'), w1('b'), sym(w1('b'), w0('b'), eb), proj(C0b,2,'h')),
         A(C1b[3], C1b[4],
           SUBW(lambda z: T(f'IM.tr.real({V1}, d, l, {z}, s)'), w0('(b + 2 : U32)'), w1('(b + 2 : U32)'), sym(w1('(b + 2 : U32)'), w0('(b + 2 : U32)'), WFR('b',2,'hbM')),
             f"rf_tr(l, {CTXA}, {XA}, {w0('(b + 2 : U32)')}, hlM, {proj(C0b,3,'h')})"),
           SUBW(lambda z: T(f'IM.tr.real({V1}, d, r, {z}, s)'), w0('(b + 3 : U32)'), w1('(b + 3 : U32)'), sym(w1('(b + 3 : U32)'), w0('(b + 3 : U32)'), WFR('b',3,'hbM')),
             f"rf_tr(r, {CTXA}, {XA}, {w0('(b + 3 : U32)')}, hrM, {proj(C0b,4,'h')})")))))
sec2=f'''
# the index realized after the copy: every word its realization reads
# off the fresh nodes and the header's, so read alike (agree_at)
def rf_tr(tr: IM.Tr, {CTXP}, {XP_}, +p: U32, +hs: {T('RG.sub(IM.tr.nodes(tr), M)')}, +h: {T(f'IM.tr.real({V0}, d, tr, p, s)')}) -> {T(f'IM.tr.real({V1}, d, tr, p, s)')}:
  match tr:
    case IM.Lf{{+x, +k}}:
      +hxM = {L('RG.has(M, x)','RG.sub([], M)','hs')}
      {lf}
    case IM.Br{{+b, +i, +l, +r}}:
      +hbM = {hbM}
      +hlM = {hlM}
      +hrM = {hrM}
      {br}

def rf_ix(I: IM.Ix, {CTXP}, {XP_}, +hsM: {T('RG.has(M, s)')}, +hs: {T('RG.sub(IM.ix.nodes(I), M)')}, +h: {T(f'IM.ix.real({V0}, d, s, I)')}) -> {T(f'IM.ix.real({V1}, d, s, I)')}:
  match I:
    case IM.Ept{{}}:
      {SUBW(lambda z: T(f'U32.is_eq({z}, s)'), w0('(s + 3 : U32)'), w1('(s + 3 : U32)'), sym(w1('(s + 3 : U32)'), w0('(s + 3 : U32)'), WFR('s',3,'hsM')), 'h')}
    case IM.Has{{+tr}}:
      {A(f'Bool.not(U32.is_eq({w1("(s + 3 : U32)")}, s))', f'IM.tr.real({V1}, d, tr, {w1("(s + 3 : U32)")}, s)',
        SUBW(lambda z: T(f'Bool.not(U32.is_eq({z}, s))'), w0('(s + 3 : U32)'), w1('(s + 3 : U32)'), sym(w1('(s + 3 : U32)'), w0('(s + 3 : U32)'), WFR('s',3,'hsM')), L(f'Bool.not(U32.is_eq({w0("(s + 3 : U32)")}, s))', f'IM.tr.real({V0}, d, tr, {w0("(s + 3 : U32)")}, s)', 'h')),
        SUBW(lambda z: T(f'IM.tr.real({V1}, d, tr, {z}, s)'), w0('(s + 3 : U32)'), w1('(s + 3 : U32)'), sym(w1('(s + 3 : U32)'), w0('(s + 3 : U32)'), WFR('s',3,'hsM')),
          f"rf_tr(tr, {CTXA}, {XA}, {w0('(s + 3 : U32)')}, hs, {R(f'Bool.not(U32.is_eq({w0(chr(40)+"s + 3 : U32)")}, s))', f'IM.tr.real({V0}, d, tr, {w0("(s + 3 : U32)")}, s)', 'h')})"))}
'''
sec2=sec2.replace(f'Bool.not(U32.is_eq({w0(chr(40)+"s + 3 : U32)")}, s))', f'Bool.not(U32.is_eq({w0("(s + 3 : U32)")}, s))')
sec+=sec2
if os.environ.get('CPI_PART')=='2':
    open('glam/proofgen/sv/cpi1.txt','w').write(sec)
    print('part2', len(sec.splitlines()))
# ---- part 3: small list lemmas, the holes' facing ----
SPLv=SPL
MAPV=f'AD.view(U32, SM.map({SPLv}))'
PLS=f'RG.pls(cs, {MAPV}, dm)'
L0='Con{s, t}'; Lp=AP(L0, PLS); Mp=AP('M', PLS); NF=AP('ns','F')
OFF3=lambda r,n: f'KMd.off.port(d, {r}, ({n} + 1 : U32)) && (KMd.off.port(d, {r}, ({n} + 2 : U32)) && KMd.off.port(d, {r}, ({n} + 3 : U32)))'
PONs=lambda r,L_,n: f'RG.po.n({r}, {L_}, d, {n})'
sec3=f'''
# a Maybe's word, two readers
def plw(m: Maybe<&2, U32>) -> {{RG.pl.of(m) == KMd.word.m(m) : U32}}:
  match m:
    case Some{{+q}}:
      {{==}}
    case None{{}}:
      {{==}}

def has_app_rf(A: List<&2, U32>, +B: List<&2, U32>, +x: U32, +h: {F_(f'RG.has({AP("A","B")}, x)')}) -> {F_('RG.has(B, x)')}:
  match A:
    case Nil{{}}:
      h
    case Con{{+y, +r}}:
      has_app_rf(r, B, x, GP.or_false_r(U32.is_eq(y, x), RG.has({AP("r","B")}, x), h))

def none_of_dist(A: List<&2, U32>, +B: List<&2, U32>, +h: {T(f'RG.distinct({AP("A","B")})')}) -> {T('RG.none.in(A, B)')}:
  match A:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +r}}:
      {A('Bool.not(RG.has(B, x))','RG.none.in(r, B)', f'GP.nf2(RG.has(B, x), has_app_rf(r, B, x, MB.eq_false_of_not_eq_true(RG.has({AP("r","B")}, x), {L(f"Bool.not(RG.has({AP("r","B")}, x))", f"RG.distinct({AP("r","B")})","h")})))',
        f'none_of_dist(r, B, {R(f"Bool.not(RG.has({AP("r","B")}, x))", f"RG.distinct({AP("r","B")})","h")})')}

def none_flip(+A: List<&2, U32>, B: List<&2, U32>, +h: {T('RG.none.in(A, B)')}) -> {T('RG.none.in(B, A)')}:
  match B:
    case Nil{{}}:
      {{==}}
    case Con{{+b, +r}}:
      {A('Bool.not(RG.has(A, b))','RG.none.in(r, A)', 'GP.nf2(RG.has(A, b), GP.none_has(A, Con{b, r}, b, h, GP.has_head(b, r)))', 'none_flip(A, r, GP.none_sub(A, Con{b, r}, r, h, GP.sub_cons_r(r, b, r, GP.sub_refl(r))))')}

def none_in_app(ps: List<&2, U32>, +A: List<&2, U32>, +B: List<&2, U32>, +ha: {T('RG.none.in(ps, A)')}, +hb: {T('RG.none.in(ps, B)')}) -> {T(f'RG.none.in(ps, {AP("A","B")})')}:
  match ps:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +r}}:
      {A(f'Bool.not(RG.has({AP("A","B")}, x))', f'RG.none.in(r, {AP("A","B")})',
        f'GP.nf2(RG.has({AP("A","B")}, x), has_app_ff(A, B, x, MB.eq_false_of_not_eq_true(RG.has(A, x), {L("Bool.not(RG.has(A, x))","RG.none.in(r, A)","ha")}), MB.eq_false_of_not_eq_true(RG.has(B, x), {L("Bool.not(RG.has(B, x))","RG.none.in(r, B)","hb")})))',
        f'none_in_app(r, A, B, {R("Bool.not(RG.has(A, x))","RG.none.in(r, A)","ha")}, {R("Bool.not(RG.has(B, x))","RG.none.in(r, B)","hb")})')}

def none_app(A: List<&2, U32>, +B: List<&2, U32>, +X: List<&2, U32>, +ha: {T('RG.none.in(A, X)')}, +hb: {T('RG.none.in(B, X)')}) -> {T(f'RG.none.in({AP("A","B")}, X)')}:
  match A:
    case Nil{{}}:
      hb
    case Con{{+x, +r}}:
      {A('Bool.not(RG.has(X, x))', f'RG.none.in({AP("r","B")}, X)', L('Bool.not(RG.has(X, x))','RG.none.in(r, X)','ha'), f'none_app(r, B, X, {R("Bool.not(RG.has(X, x))","RG.none.in(r, X)","ha")}, hb)')}

def ixbr_sub(I: IM.Ix, +s: U32) -> {T('RG.sub(IM.ix.branches(I), Con{s, IM.ix.nodes(I)})')}:
  match I:
    case IM.Ept{{}}:
      {{==}}
    case IM.Has{{+tr}}:
      GP.sub_cons_r(IM.tr.branches(tr), s, IM.tr.nodes(tr), GP.br_sub(tr))

def px_off_app(A: List<&2, U32>, +B: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +L: List<&2, U32>, +N: List<&2, U32>, +ha: {T('RG.px.off(A, v, d, L, N)')}, +hb: {T('RG.px.off(B, v, d, L, N)')}) -> {T(f'RG.px.off({AP("A","B")}, v, d, L, N)')}:
  match A:
    case Nil{{}}:
      hb
    case Con{{+z, +r}}:
      {A('RG.po.all(KMd.word(v, d, (z + 1 : U32)), L, d, N)', f'RG.px.off({AP("r","B")}, v, d, L, N)', L('RG.po.all(KMd.word(v, d, (z + 1 : U32)), L, d, N)','RG.px.off(r, v, d, L, N)','ha'), f"px_off_app(r, B, v, d, L, N, {R('RG.po.all(KMd.word(v, d, (z + 1 : U32)), L, d, N)','RG.px.off(r, v, d, L, N)','ha')}, hb)")}

def tw_app(A: List<&2, U32>, +B: List<&2, U32>, +r: U32, +z: U32, +v: List<&2, U32>, +d: Nat, +ha: {T('RG.tw.q(A, r, z, v, d)')}, +hb: {T('RG.tw.q(B, r, z, v, d)')}) -> {T(f'RG.tw.q({AP("A","B")}, r, z, v, d)')}:
  match A:
    case Nil{{}}:
      hb
    case Con{{+q, +k}}:
      {A('Bool.or(KMd.off.port(d, r, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, (q + 1 : U32)), (z + 1 : U32))))', f'RG.tw.q({AP("k","B")}, r, z, v, d)',
        L('Bool.or(KMd.off.port(d, r, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, (q + 1 : U32)), (z + 1 : U32))))','RG.tw.q(k, r, z, v, d)','ha'),
        f"tw_app(k, B, r, z, v, d, {R('Bool.or(KMd.off.port(d, r, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, (q + 1 : U32)), (z + 1 : U32))))','RG.tw.q(k, r, z, v, d)','ha')}, hb)")}

def px_tw_app(A: List<&2, U32>, +B: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +L: List<&2, U32>, +ha: {T('RG.px.tw(A, v, d, L)')}, +hb: {T('RG.px.tw(B, v, d, L)')}) -> {T(f'RG.px.tw({AP("A","B")}, v, d, L)')}:
  match A:
    case Nil{{}}:
      hb
    case Con{{+z, +r}}:
      {A('KMd.off.port(d, KMd.word(v, d, (z + 1 : U32)), (z + 1 : U32))', f'RG.tw.q(L, KMd.word(v, d, (z + 1 : U32)), z, v, d) && RG.px.tw({AP("r","B")}, v, d, L)',
        L('KMd.off.port(d, KMd.word(v, d, (z + 1 : U32)), (z + 1 : U32))', 'RG.tw.q(L, KMd.word(v, d, (z + 1 : U32)), z, v, d) && RG.px.tw(r, v, d, L)', 'ha'),
        A('RG.tw.q(L, KMd.word(v, d, (z + 1 : U32)), z, v, d)', f'RG.px.tw({AP("r","B")}, v, d, L)',
          L('RG.tw.q(L, KMd.word(v, d, (z + 1 : U32)), z, v, d)','RG.px.tw(r, v, d, L)', R('KMd.off.port(d, KMd.word(v, d, (z + 1 : U32)), (z + 1 : U32))', 'RG.tw.q(L, KMd.word(v, d, (z + 1 : U32)), z, v, d) && RG.px.tw(r, v, d, L)', 'ha')),
          f"px_tw_app(r, B, v, d, L, {R('RG.tw.q(L, KMd.word(v, d, (z + 1 : U32)), z, v, d)','RG.px.tw(r, v, d, L)', R('KMd.off.port(d, KMd.word(v, d, (z + 1 : U32)), (z + 1 : U32))', 'RG.tw.q(L, KMd.word(v, d, (z + 1 : U32)), z, v, d) && RG.px.tw(r, v, d, L)', 'ha'))}, hb)"))}

# a crossing's hole among the holes, its slot among theirs
def pls_has(cs: List<&2, R.FzC>, +vm: List<&2, U32>, +dm: Nat, +at: U32, hat: {T('RG.has(SV.ats(cs), at)')}) -> {T('RG.has(RG.pls(cs, vm, dm), RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm))))')}:
  match cs:
    case Nil{{}}:
      Empty.absurd({T('RG.has(RG.pls([], vm, dm), RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm))))')}, MB.false_ne_true()(hat))
    case Con{{c, +r}}:
      match c:
        case R.FzC{{+a2, +src, neg, +far}}:
          GP.or_cases(U32.is_eq(a2, at), RG.has(SV.ats(r), at), RG.has(RG.pls(Con{{R.FzC{{a2, src, neg, far}}, r}}, vm, dm), RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm)))), hat,
            e => ME.subst(U32, z => {T('RG.has(Con{RG.pl.of(List.get(&2, U32, vm, AD.slot(z, dm))), RG.pls(r, vm, dm)}, RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm))))')}, at, a2, Equal.sym(U32, a2, at, MS.u32_eq_of_is_eq(a2, at, e)),
              SPP.or_l(U32.is_eq(RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm)))), RG.has(RG.pls(r, vm, dm), RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm)))), SPP.u32_refl(RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm)))))),
            e => SPP.or_r(U32.is_eq(RG.pl.of(List.get(&2, U32, vm, AD.slot(a2, dm))), RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm)))), RG.has(RG.pls(r, vm, dm), RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm)))), pls_has(r, vm, dm, at, e)))
'''
# the holes: each hole's faced port off the tracked nodes, the holes, the live nodes
EXP=(f"+cs: List<&2, R.FzC>, +M: List<&2, U32>, +hapNM: {T(f'KMd.apart({NM}, d)')}, +hpns: {T('KMd.past(ns, d)')}, +hN: {T(f'RG.layout({MN}, d)')}, "
     f"+hPs: {T(f'RG.sub({PLS}, ns)')}, +hh: {T('SV.holes.ok(SV.ats(cs), ls, ts, dm, SV.ats(cs))')}, +hL0M: {T(f'RG.sub({L0}, M)')}")
EXA='cs, M, hapNM, hpns, hN, hPs, hh, hL0M'
HOLEP=(f"+at: U32, +hna: {T('SV.node.at(ts, dm, at)')}, +hat: {T('RG.has(SV.ats(cs), at)')}, +hnm: {T('SV.names(ls, dm, at)')}, +hhl: {T('SV.hole.links(ls, ts, dm, at, SV.ats(cs))')}")
HOLEA='at, hna, hat, hnm, hhl'
Q=f'RG.pl.of(List.get(&2, U32, {MAPV}, AD.slot(at, dm)))'
RQ=f'KMd.word({V1}, d, ({Q} + 1 : U32))'
LG1=f'List.get(&2, U32, {V1}, AD.slot(({Q} + 1 : U32), d))'
def HOFF(j, hj, two=False):
    nm='hole_offp2' if two else 'hole_offp'
    return f"ME.subst(U32, zz => {T(f'KMd.off.port(d, zz, {j})')}, RG.pl.of({LG1}), KMd.word.m({LG1}), plw({LG1}), {nm}(cs, {CTXA}, {j}, {hj}, {HOLEA}, hh, hnm, hhl))"
HOFF=HOFF
def HOFFx(j, hj, two=False):
    nm='hole_offp2' if two else 'hole_offp'
    return f"ME.subst(U32, zz => {T(f'KMd.off.port(d, zz, {j})')}, RG.pl.of({LG1}), KMd.word.m({LG1}), plw({LG1}), {nm}(cs, {CTXA}, {j}, {hj}, at, hna, hat, hh, hnm, hhl))"
NSi=lambda i,n,h: f'nsoff{i}(ns, M, d, {n}, hapNM, {KHAS("M", n, h)})'
HNSMN=f'sub_app_r(M, ns)'
NMi=lambda i,q,hqMN,hqP: f'noff_minus{i}(ns, {PLS}, {MN}, d, {q}, hN, {HNSMN}, {hqMN}, {hqP})'
HPAR=f'{CTXP}, {EXP}, {HOLEP}'
HARG=f'{CTXA}, {EXA}, {HOLEA}'
sec3+=f'''
# A hole's faced port's link word off the tracked nodes but the holes (all
# off the fresh nodes), off the holes' words (off every fresh node that is
# no hole), off the free list's head
def pom(K: List<&2, U32>, {HPAR}, +hK: {T('RG.sub(K, M)')}) -> {T(f'RG.po.all({RQ}, {Lp}, d, K)')}:
  match K:
    case Nil{{}}:
      {HOFFx('P.at_fh()','SPP.npast(ns, d, hpns)')}
    case Con{{+n, +k}}:
      +hnM = {L('RG.has(M, n)','RG.sub(k, M)','hK')}
      {A(PONs(RQ,Lp,'n'), f'RG.po.all({RQ}, {Lp}, d, k)',
        A(f'KMd.off.port(d, {RQ}, n)', f'Bool.or(RG.has({Lp}, n), {OFF3(RQ,"n")})', HOFFx('n', NSi(0,'n','hnM')),
          f"SPP.or_r(RG.has({Lp}, n), {OFF3(RQ,'n')}, {A(f'KMd.off.port(d, {RQ}, (n + 1 : U32))', f'KMd.off.port(d, {RQ}, (n + 2 : U32)) && KMd.off.port(d, {RQ}, (n + 3 : U32))', HOFFx('(n + 1 : U32)', NSi(1,'n','hnM')), A(f'KMd.off.port(d, {RQ}, (n + 2 : U32))', f'KMd.off.port(d, {RQ}, (n + 3 : U32))', HOFFx('(n + 2 : U32)', NSi(2,'n','hnM')), HOFFx('(n + 3 : U32)', NSi(3,'n','hnM'))))})"),
        f"pom(k, {HARG}, {R('RG.has(M, n)','RG.sub(k, M)','hK')})")}

def pop(K: List<&2, U32>, {HPAR}, +hK: {T(f'RG.sub(K, {PLS})')}) -> {T(f'RG.po.all({RQ}, {Lp}, d, K)')}:
  match K:
    case Nil{{}}:
      {HOFFx('P.at_fh()','SPP.npast(ns, d, hpns)')}
    case Con{{+q, +k}}:
      +hqP = {L(f'RG.has({PLS}, q)','RG.sub(k, '+PLS+')','hK')}
      +hqMN = has_app_r(M, ns, q, GP.sub_has({PLS}, ns, q, hPs, hqP))
      {A(PONs(RQ,Lp,'q'), f'RG.po.all({RQ}, {Lp}, d, k)',
        A(f'KMd.off.port(d, {RQ}, q)', f'Bool.or(RG.has({Lp}, q), {OFF3(RQ,"q")})', HOFFx('q', NMi(0,'q','hqMN','hqP'), True),
          f"SPP.or_l(RG.has({Lp}, q), {OFF3(RQ,'q')}, has_app_r({L0}, {PLS}, q, hqP))"),
        f"pop(k, {HARG}, {R(f'RG.has({PLS}, q)','RG.sub(k, '+PLS+')','hK')})")}

def twl(K: List<&2, U32>, {HPAR}, +hK: {T(f'RG.sub(K, {L0})')}) -> {T(f'RG.tw.q(K, {RQ}, {Q}, {V1}, d)')}:
  match K:
    case Nil{{}}:
      {{==}}
    case Con{{+q, +k}}:
      +hqM = GP.sub_has({L0}, M, q, hL0M, {L(f'RG.has({L0}, q)','RG.sub(k, '+L0+')','hK')})
      {A(f'Bool.or(KMd.off.port(d, {RQ}, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word({V1}, d, (q + 1 : U32)), ({Q} + 1 : U32))))', f'RG.tw.q(k, {RQ}, {Q}, {V1}, d)',
        f"SPP.or_l(KMd.off.port(d, {RQ}, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word({V1}, d, (q + 1 : U32)), ({Q} + 1 : U32))), {HOFFx('(q + 1 : U32)', NSi(1,'q','hqM'))})",
        f"twl(k, {HARG}, {R(f'RG.has({L0}, q)','RG.sub(k, '+L0+')','hK')})")}

def twp(K: List<&2, U32>, {HPAR}, +hK: {T(f'RG.sub(K, {PLS})')}) -> {T(f'RG.tw.q(K, {RQ}, {Q}, {V1}, d)')}:
  match K:
    case Nil{{}}:
      {{==}}
    case Con{{+q, +k}}:
      +hqP = {L(f'RG.has({PLS}, q)','RG.sub(k, '+PLS+')','hK')}
      +hqMN = has_app_r(M, ns, q, GP.sub_has({PLS}, ns, q, hPs, hqP))
      {A(f'Bool.or(KMd.off.port(d, {RQ}, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word({V1}, d, (q + 1 : U32)), ({Q} + 1 : U32))))', f'RG.tw.q(k, {RQ}, {Q}, {V1}, d)',
        f"SPP.or_l(KMd.off.port(d, {RQ}, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word({V1}, d, (q + 1 : U32)), ({Q} + 1 : U32))), {HOFFx('(q + 1 : U32)', NMi(1,'q','hqMN','hqP'), True)})",
        f"twp(k, {HARG}, {R(f'RG.has({PLS}, q)','RG.sub(k, '+PLS+')','hK')})")}
'''
# the holes in turn (as holes_offp): px.off and px.tw over them
HO=lambda r: f'SV.holes.ok(SV.ats({r}), ls, ts, dm, SV.ats(cs))'
HE=['SV.node.at(ts, dm, at)','SV.names(ls, dm, at)','SV.hole.links(ls, ts, dm, at, SV.ats(cs))',HO('r')]
PLSr=lambda r: f'RG.pls({r}, {MAPV}, dm)'
hna=proj(HE,0,'hhr'); hnm=proj(HE,1,'hhr'); hhl=proj(HE,2,'hhr'); hhr2=proj(HE,3,'hhr')
hat=L('RG.has(SV.ats(cs), at)','RG.sub(SV.ats(r), SV.ats(cs))','hsub'); hsub2=R('RG.has(SV.ats(cs), at)','RG.sub(SV.ats(r), SV.ats(cs))','hsub')
HSP=f"+hhr: {T(HO('csr'))}, +hsub: {T('RG.sub(SV.ats(csr), SV.ats(cs))')}"
EXTR=f'''          +hna = {hna}
          +hnm = {hnm}
          +hhl = {hhl}
          +hat = {hat}
'''
sec3+=f'''
def hpxo(csr: List<&2, R.FzC>, {CTXP}, {EXP}, {HSP}) -> {T(f'RG.px.off({PLSr("csr")}, {V1}, d, {Lp}, {Mp})')}:
  match csr:
    case Nil{{}}:
      {{==}}
    case Con{{c, +r}}:
      match c:
        case R.FzC{{+at, +src, neg, +far}}:
{EXTR}          {A(f'RG.po.all({RQ}, {Lp}, d, {Mp})', f'RG.px.off({PLSr("r")}, {V1}, d, {Lp}, {Mp})',
            f"po_app(M, {PLS}, {RQ}, {Lp}, d, pom(M, {HARG}, GP.sub_refl(M)), pop({PLS}, {HARG}, GP.sub_refl({PLS})))",
            f"hpxo(r, {CTXA}, {EXA}, {hhr2}, {hsub2})")}

def hptw(csr: List<&2, R.FzC>, {CTXP}, {EXP}, {HSP}) -> {T(f'RG.px.tw({PLSr("csr")}, {V1}, d, {Lp})')}:
  match csr:
    case Nil{{}}:
      {{==}}
    case Con{{c, +r}}:
      match c:
        case R.FzC{{+at, +src, neg, +far}}:
{EXTR}          +hQP = pls_has(cs, {MAPV}, dm, at, hat)
          +hQMN = has_app_r(M, ns, {Q}, GP.sub_has({PLS}, ns, {Q}, hPs, hQP))
          {A(f'KMd.off.port(d, {RQ}, ({Q} + 1 : U32))', f'RG.tw.q({Lp}, {RQ}, {Q}, {V1}, d) && RG.px.tw({PLSr("r")}, {V1}, d, {Lp})',
            HOFFx(f'({Q} + 1 : U32)', NMi(1, Q, 'hQMN', 'hQP'), True),
            A(f'RG.tw.q({Lp}, {RQ}, {Q}, {V1}, d)', f'RG.px.tw({PLSr("r")}, {V1}, d, {Lp})',
              f"tw_app({L0}, {PLS}, {RQ}, {Q}, {V1}, d, twl({L0}, {HARG}, GP.sub_refl({L0})), twp({PLS}, {HARG}, GP.sub_refl({PLS})))",
              f"hptw(r, {CTXA}, {EXA}, {hhr2}, {hsub2})"))}
'''
sec+=sec3
if os.environ.get('CPI_PART')=='3':
    open('glam/proofgen/sv/cpi1.txt','w').write(sec)
    print('part3', len(sec.splitlines()))
# ---- part 4: the live nodes' facing, the core, the entry ----
w0=lambda j: WD(V0,j); w1=lambda j: WD(V1,j)
Z1='(z + 1 : U32)'; Q1='(q + 1 : U32)'
def WF1(z, hz):
    return f"Equal.cong(Maybe<&2, U32>, U32, mm => KMd.word.m(mm), List.get(&2, U32, {V1}, AD.slot(({z} + 1 : U32), d)), List.get(&2, U32, {V0}, AD.slot(({z} + 1 : U32), d)), agree1({CTXA}, {z}, {hz}))"
EL=lambda rz, wq: f'Bool.or(KMd.off.port(d, {rz}, {Q1}), Bool.not(KMd.off.port(d, {wq}, {Z1})))'
sec4=f'''
def ortr(+a: Bool, +b: Bool, +ha: {F_('a')}, +h: {T('Bool.or(a, b)')}) -> {T('b')}:
  ME.subst(Bool, z => {T('Bool.or(z, b)')}, a, False{{}}, ha, h)

# The live nodes' facing after the copy: their words 1 read alike
# (agree1), the ports they face off the holes' words as off every fresh
# node's not live before
def pxo_live(ys: List<&2, U32>, {CTXP}, {EXP}, +hMpMN: {T(f'RG.sub({Mp}, {MN})')}, +hys: {T(f'RG.sub(ys, {L0})')}, +h: {T(f'RG.px.off(ys, {V0}, d, {L0}, {MN})')}) -> {T(f'RG.px.off(ys, {V1}, d, {Lp}, {Mp})')}:
  match ys:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      +hz = {L(f'RG.has({L0}, z)', f'RG.sub(r, {L0})', 'hys')}
      +hpo = po_sub({Mp}, {w0(Z1)}, {L0}, {Lp}, d, {MN}, sub_app_l({L0}, {PLS}), hMpMN, {L(f'RG.po.all({w0(Z1)}, {L0}, d, {MN})', f'RG.px.off(r, {V0}, d, {L0}, {MN})', 'h')})
      {A(f'RG.po.all({w1(Z1)}, {Lp}, d, {Mp})', f'RG.px.off(r, {V1}, d, {Lp}, {Mp})',
        f"ME.subst(U32, qq => {T(f'RG.po.all(qq, {Lp}, d, {Mp})')}, {w0(Z1)}, {w1(Z1)}, Equal.sym(U32, {w1(Z1)}, {w0(Z1)}, {WF1('z','hz')}), hpo)",
        f"pxo_live(r, {CTXA}, {EXA}, hMpMN, {R(f'RG.has({L0}, z)', f'RG.sub(r, {L0})', 'hys')}, {R(f'RG.po.all({w0(Z1)}, {L0}, d, {MN})', f'RG.px.off(r, {V0}, d, {L0}, {MN})', 'h')})")}

def twq_live(Q: List<&2, U32>, {CTXP}, {EXP}, +z: U32, +hz: {T(f'RG.has({L0}, z)')}, +hQ: {T(f'RG.sub(Q, {L0})')}, +h: {T(f'RG.tw.q(Q, {w0(Z1)}, z, {V0}, d)')}) -> {T(f'RG.tw.q(Q, {w1(Z1)}, z, {V1}, d)')}:
  match Q:
    case Nil{{}}:
      {{==}}
    case Con{{+q, +k}}:
      +hq = {L(f'RG.has({L0}, q)', f'RG.sub(k, {L0})', 'hQ')}
      {A(EL(w1(Z1), w1(Q1)), f'RG.tw.q(k, {w1(Z1)}, z, {V1}, d)',
        f"ME.subst(U32, xx => {T(EL(w1(Z1),'xx'))}, {w0(Q1)}, {w1(Q1)}, Equal.sym(U32, {w1(Q1)}, {w0(Q1)}, {WF1('q','hq')}), ME.subst(U32, xx => {T(EL('xx', w0(Q1)))}, {w0(Z1)}, {w1(Z1)}, Equal.sym(U32, {w1(Z1)}, {w0(Z1)}, {WF1('z','hz')}), {L(EL(w0(Z1),w0(Q1)), f'RG.tw.q(k, {w0(Z1)}, z, {V0}, d)', 'h')}))",
        f"twq_live(k, {CTXA}, {EXA}, z, hz, {R(f'RG.has({L0}, q)', f'RG.sub(k, {L0})', 'hQ')}, {R(EL(w0(Z1),w0(Q1)), f'RG.tw.q(k, {w0(Z1)}, z, {V0}, d)', 'h')})")}

def twq_pls(K: List<&2, U32>, {CTXP}, {EXP}, +z: U32, +hz: {T(f'RG.has({L0}, z)')}, +hpo: {T(f'RG.po.all({w0(Z1)}, {L0}, d, {MN})')}, +hnsL0: {T(f'RG.none.in(ns, {L0})')}, +hK: {T(f'RG.sub(K, {PLS})')}) -> {T(f'RG.tw.q(K, {w1(Z1)}, z, {V1}, d)')}:
  match K:
    case Nil{{}}:
      {{==}}
    case Con{{+q, +k}}:
      +hqP = {L(f'RG.has({PLS}, q)', f'RG.sub(k, {PLS})', 'hK')}
      +hqns = GP.sub_has({PLS}, ns, q, hPs, hqP)
      +hpon = po_at({MN}, {w0(Z1)}, {L0}, d, q, hpo, has_app_r(M, ns, q, hqns))
      +hoff = {L(f'KMd.off.port(d, {w0(Z1)}, {Q1})', f'KMd.off.port(d, {w0(Z1)}, (q + 2 : U32)) && KMd.off.port(d, {w0(Z1)}, (q + 3 : U32))', f"ortr(RG.has({L0}, q), {OFF3(w0(Z1),'q')}, GP.none_mem(ns, {L0}, q, hnsL0, hqns), {R(f'KMd.off.port(d, {w0(Z1)}, q)', f'Bool.or(RG.has({L0}, q), {OFF3(w0(Z1),chr(113))})', 'hpon')})")}
      {A(EL(w1(Z1), w1(Q1)), f'RG.tw.q(k, {w1(Z1)}, z, {V1}, d)',
        f"SPP.or_l(KMd.off.port(d, {w1(Z1)}, {Q1}), Bool.not(KMd.off.port(d, {w1(Q1)}, {Z1})), ME.subst(U32, xx => {T(f'KMd.off.port(d, xx, {Q1})')}, {w0(Z1)}, {w1(Z1)}, Equal.sym(U32, {w1(Z1)}, {w0(Z1)}, {WF1('z','hz')}), hoff))",
        f"twq_pls(k, {CTXA}, {EXA}, z, hz, hpo, hnsL0, {R(f'RG.has({PLS}, q)', f'RG.sub(k, {PLS})', 'hK')})")}
'''
C0c=[f'KMd.off.port(d, {w0(Z1)}, {Z1})', f'RG.tw.q({L0}, {w0(Z1)}, z, {V0}, d)', f'RG.px.tw(r, {V0}, d, {L0})']
sec4+=f'''
def ptw_live(ys: List<&2, U32>, {CTXP}, {EXP}, +hnsL0: {T(f'RG.none.in(ns, {L0})')}, +hys: {T(f'RG.sub(ys, {L0})')}, +h: {T(f'RG.px.tw(ys, {V0}, d, {L0})')}, +h16: {T(f'RG.px.off(ys, {V0}, d, {L0}, {MN})')}) -> {T(f'RG.px.tw(ys, {V1}, d, {Lp})')}:
  match ys:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      +hz = {L(f'RG.has({L0}, z)', f'RG.sub(r, {L0})', 'hys')}
      +hpo = {L(f'RG.po.all({w0(Z1)}, {L0}, d, {MN})', f'RG.px.off(r, {V0}, d, {L0}, {MN})', 'h16')}
      {A(f'KMd.off.port(d, {w1(Z1)}, {Z1})', f'RG.tw.q({Lp}, {w1(Z1)}, z, {V1}, d) && RG.px.tw(r, {V1}, d, {Lp})',
        f"ME.subst(U32, xx => {T(f'KMd.off.port(d, xx, {Z1})')}, {w0(Z1)}, {w1(Z1)}, Equal.sym(U32, {w1(Z1)}, {w0(Z1)}, {WF1('z','hz')}), {proj(C0c,0,'h')})",
        A(f'RG.tw.q({Lp}, {w1(Z1)}, z, {V1}, d)', f'RG.px.tw(r, {V1}, d, {Lp})',
          f"tw_app({L0}, {PLS}, {w1(Z1)}, z, {V1}, d, twq_live({L0}, {CTXA}, {EXA}, z, hz, GP.sub_refl({L0}), {proj(C0c,1,'h')}), twq_pls({PLS}, {CTXA}, {EXA}, z, hz, hpo, hnsL0, GP.sub_refl({PLS})))",
          f"ptw_live(r, {CTXA}, {EXA}, hnsL0, {R(f'RG.has({L0}, z)', f'RG.sub(r, {L0})', 'hys')}, {proj(C0c,2,'h')}, {R(f'RG.po.all({w0(Z1)}, {L0}, d, {MN})', f'RG.px.off(r, {V0}, d, {L0}, {MN})', 'h16')})"))}
'''
# the core
nsJ={}
exec(open('glam/proofgen/gen_j1.py').read().split("open('glam/proofgen/j1_part1.txt','w')")[0], nsJ)
PXOK=nsJ['PXOK']
def intro(cs, ps):
    if len(cs)==1: return ps[0]
    return A(cs[0], conj(cs[1:]), ps[0], intro(cs[1:], ps[1:]))
NODI='IM.ix.nodes(I)'; BRI='IM.ix.branches(I)'; LVI='IM.ix.leaves(I)'
C0=PXOK(V0, 'I', '[]', L0, NF, MN)
G=PXOK(V1, 'I', PLS, Lp, 'F', Mp)
lets=''.join(f'  +hp{i} = {proj(C0,i,"hp")}\n' for i in range(18))
SUBL0NS=f'sub_app2({L0}, ns, {MN}, hp12, sub_app_r(M, ns))'
SUBNM=f'sub_app2(ns, M, {MN}, sub_app_r(M, ns), sub_app_l(M, ns))'
lets+=f'''  +hct = SPP.kchain_pre(ns, F, {V0}, d, {w0('P.at_fh()')}, hp8)
  +hdMN = lay_dist({MN}, d, hN)
  +hdns = dist_suf(M, ns, hdMN)
  +hdM = dist_pre(M, ns, hdMN)
  +hnsL0 = none_appl(ns, F, {L0}, hp11)
  +hnsI = none_appl(ns, F, Con{{s, {NODI}}}, hp10)
  +hFL0 = none_appr(ns, F, {L0}, hp11)
  +hFI = none_appr(ns, F, Con{{s, {NODI}}}, hp10)
  +hdF = dist_suf(ns, F, hp9)
  +hL0M = sub_left({L0}, M, ns, hp12, hnsL0)
  +hIM = sub_left({NODI}, M, ns, hp14, GP.none_sub(ns, Con{{s, {NODI}}}, {NODI}, hnsI, GP.sub_cons_r({NODI}, s, {NODI}, GP.sub_refl({NODI}))))
  +hFM = sub_left(F, M, ns, GP.sub_trans(F, {NF}, {MN}, sub_app_r(ns, F), hp13), none_of_dist(ns, F, hp9))
  +hsM = GP.sub_has({L0}, M, s, hL0M, GP.has_head(s, t))
  +hlay = GP.lay_sub({AP(L0,'ns')}, {MN}, d, {SUBL0NS}, hN, apall_of({AP(L0,'ns')}, {MN}, d, {SUBL0NS}, hN, distinct_app({L0}, ns, hLd, hdns, hnsL0)))
  +hbs = GP.bases_sub(ns, {MN}, sub_app_r(M, ns), hB)
  +hpa = kpast_sub({AP(L0,'ns')}, {MN}, d, {SUBL0NS}, hpaMN)
  +hapNM = kap_of_lay({NM}, d, GP.lay_sub({NM}, {MN}, d, {SUBNM}, hN, apall_of({NM}, {MN}, d, {SUBNM}, hN, distinct_app(ns, M, hdns, hdM, none_of_dist(M, ns, hdMN)))))
  +hpns = kpast_sub(ns, {MN}, d, sub_app_r(M, ns), hpaMN)
  +hha = {L('SV.sl.apart(SV.ats(cs), dm)','SV.holes.ok(SV.ats(cs), ls, ts, dm, SV.ats(cs))','hcp')}
  +hh = {R('SV.sl.apart(SV.ats(cs), dm)','SV.holes.ok(SV.ats(cs), ls, ts, dm, SV.ats(cs))','hcp')}
  +hPs = holes_sub(cs, SV.ats(cs), {CTXA}, hh)
  +hMpMN = sub_app2(M, {PLS}, {MN}, sub_app_l(M, ns), GP.sub_trans({PLS}, ns, {MN}, hPs, sub_app_r(M, ns)))
'''
prfs=[f'rf_ix(I, {CTXA}, M, hapNM, hpaMN, hsM, hIM, hp0)', 'hp1', 'hp2',
  f'GP.sub_trans(Con{{s, {LVI}}}, {L0}, {Lp}, hp3, sub_app_l({L0}, {PLS}))', f'sub_app_r({L0}, {PLS})',
  f'GP.none_subl({PLS}, ns, Con{{s, {NODI}}}, hPs, hnsI)', f'holes_dist(cs, SV.ats(cs), {CTXA}, hh, hha)',
  f'none_app({L0}, {PLS}, {BRI}, hp7, GP.none_subl({PLS}, ns, {BRI}, hPs, GP.none_sub(ns, Con{{s, {NODI}}}, {BRI}, hnsI, ixbr_sub(I, s))))',
  f'SPL.splice_free({T0}, {TA}, {TM}, d, dm, ts, ls, by, ns, F, hft, hd32, hfmt, hdm, hp8, hl, kap_of_lay({NF}, d, GP.lay_sub({NF}, {MN}, d, hp13, hN, apall_of({NF}, {MN}, d, hp13, hN, hp9))), kpast_sub({NF}, {MN}, d, hp13, hpaMN), hhd, ht)',
  'hdF', 'hFI', f'none_in_app(F, {L0}, {PLS}, hFL0, GP.none_sub(F, ns, {PLS}, none_flip(ns, F, none_of_dist(ns, F, hp9)), hPs))',
  f'sub_app2({L0}, {PLS}, {Mp}, GP.sub_trans({L0}, M, {Mp}, hL0M, sub_app_l(M, {PLS})), sub_app_r(M, {PLS}))',
  f'GP.sub_trans(F, M, {Mp}, hFM, sub_app_l(M, {PLS}))', f'GP.sub_trans({NODI}, M, {Mp}, hIM, sub_app_l(M, {PLS}))',
  f'faces_app({L0}, {PLS}, {V1}, d, {Lp}, faces_agree({L0}, {Lp}, {CTXA}, faces_two({L0}, {V0}, d, {L0}, {PLS}, hp15, faces_tsub({L0}, {V0}, d, ns, {PLS}, hPs, hfr)), GP.sub_refl({L0})), holes_faces(cs, cs, {CTXA}, hh, hh, GP.sub_refl(SV.ats(cs))))',
  f'px_off_app({L0}, {PLS}, {V1}, d, {Lp}, {Mp}, pxo_live({L0}, {CTXA}, {EXA}, hMpMN, GP.sub_refl({L0}), hp16), hpxo(cs, {CTXA}, {EXA}, hh, GP.sub_refl(SV.ats(cs))))',
  f'px_tw_app({L0}, {PLS}, {V1}, d, {Lp}, ptw_live({L0}, {CTXA}, {EXA}, hnsL0, GP.sub_refl({L0}), hp17, hp16), hptw(cs, {CTXA}, {EXA}, hh, GP.sub_refl(SV.ats(cs))))']
CORE_P=(f"+t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +tm: LAT.Tree<U32>, +d: Nat, +dm: Nat, +ts: List<&2, T.TNode>, +ls: List<&2, T.TLink>, +by: U32, +ns: List<&2, U32>, +s: U32, +t: List<&2, U32>, +cs: List<&2, R.FzC>,\n"
        f"  +I: IM.Ix, +F: List<&2, U32>, +M: List<&2, U32>, +hft: {{AD.full(U32, {T0}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hfmt: {{AD.full(U32, {TM}, dm) == True{{}} : Bool}}, +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}},\n"
        f"  +hN: {T(f'RG.layout({MN}, d)')}, +hB: {T(f'RG.bases({MN})')}, +hp: {T(conj(C0))}, +hl: {{SM.made(ts) == List.length(&2, U32, ns) : Nat}}, +hdy: {T('SV.dyn(ns)')}, +hpaMN: {T(f'KMd.past({MN}, d)')},\n"
        f"  +hhd: {T('KMd.off.words(KMd.hdr_words(), d, P.at_fh())')}, +hfr: {T(f'RG.faces({L0}, {V0}, d, ns)')}, +hLd: {T(f'RG.distinct({L0})')}, +ht: {T('SM.tpl.ok(ls, ts, dm)')}, +hcp: {T('SV.copy.ok(cs, ls, ts, dm)')}")
SPNt=SPN; W1=f'KMd.words(SM.heap({SPL}))'; A1=f'KMd.vals(SM.heap({SPL}))'; MAP1=f'SM.map({SPL})'
CORE_A='t0, ta, tm, d, dm, ts, ls, by, ns, s, t, cs, I, F, M, hft, hd32, hfmt, hdm, hN, hB, hp, hl, hdy, hpaMN, hhd, hfr, hLd, ht, hcp'
MAPFULL=(f"ME.subst(Array<U32>, zz => {{AD.full(U32, zz, dm) == True{{}} : Bool}}, SM.map({SPNt}), {MAP1}, Equal.sym(Array<U32>, {MAP1}, SM.map({SPNt}), lmap(ls, {SPNt})), "
         f"SPP.mfull_go(ts, SPP.hd_era(ts), {{==}}, {T0}, {TA}, {TM}, dm, 0, by, hfmt, LAT.mirror(U32, {T0}), LAT.mirror(V.Val, {TA}), LAT.mirror(U32, {TM})))")
DMP=f"distinct_app(M, {PLS}, hdM, holes_dist(cs, SV.ats(cs), {CTXA}, hh, hha), GP.none_subl({PLS}, ns, M, hPs, none_flip(M, ns, none_of_dist(M, ns, hdMN))))"
sec4+=f'''
# the invariant after the copy, its parts
def cpi.core({CORE_P}) ->
  {T(conj(G))}:
{lets}  {intro(G, prfs)}
'''
CPF=[f'RG.px.ok({V1}, d, s, I, {PLS}, {Lp}, F, {Mp})', f'AD.full(U32, {W1}, d)', f'AD.full(U32, {MAP1}, dm)', f'RG.layout({Mp}, d)', f'RG.bases({Mp})']
sec4+=f'''
# the fresh nodes no statics, each its own base (IndexPremises P3)
def dyn_of_bases(ns: List<&2, U32>, +hB: {{RG.bases(ns) == True{{}} : Bool}}) -> {{SV.dyn(ns) == True{{}} : Bool}}:
  match ns:
    case Nil{{}}:
      {{==}}
    case Con{{+n, r}}:
      MB.and_eq_true(Bool.not(P.is_static(n)), SV.dyn(r), ME.subst(Bool, b => {{Bool.not(b) == True{{}} : Bool}}, False{{}}, P.is_static(n), Equal.sym(Bool, P.is_static(n), False{{}}, GP.dyn_one(n, MB.eq_true_of_and_left(U32.is_eq(P.base(n), n), RG.bases(r), hB))), {{==}}),
        dyn_of_bases(r, MB.eq_true_of_and_right(U32.is_eq(P.base(n), n), RG.bases(r), hB)))

# the copy's invariant, and what the crossings ask besides: the words and
# the map full, the tracked nodes after (M, then the holes) laid out
# apart, each its own base (IndexPremises P1)
def cpf.core({CORE_P}) ->
  {T(conj(CPF))}:
{lets}  +hpx = cpi.core({CORE_A})
  {intro(CPF, ['hpx', f'copy_full({CTXA})', MAPFULL, f'GP.lay_sub({Mp}, {MN}, d, hMpMN, hN, apall_of({Mp}, {MN}, d, hMpMN, hN, {DMP}))', f'GP.bases_sub({Mp}, {MN}, hMpMN, hB)'])}
'''
# the entry, the heap's parts mirrored
W='w'
SPLw=lambda w,a,m: f'S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{{P.H{{KM.MG{{{w}}}, {a}}}, {m}}}, by))'

# the materializer's composition (glam/serve.bend, SC.serve) and the
# forms the proofs take of it (serve_false, serve_true): the serve's laws
# state the one, each entry rewrites it to the other (cursor-laws.materializer)
OLDF=lambda w,a,m: f'Pair.snd(Array<U32>, P.H, R.crossings(cs, (SM.map({SPLw(w,a,m)}), SM.heap({SPLw(w,a,m)})), s))'
NEWF=lambda w,a,m: f'SC.serve({SPLw(w,a,m)}, cs, T.TE{{rn, rp}}, s, nc, False{{}})'
def OLDT(w,a,m):
    crh=f'R.crossings(cs, (SM.map({SPLw(w,a,m)}), SM.heap({SPLw(w,a,m)})), s)'
    return f'R.leave(Pair.snd(Array<U32>, P.H, {crh}), (Pair.snd(Array<U32>, U32, Array.get(U32, Pair.fst(Array<U32>, P.H, {crh}), rn)) + rp : U32), nc)'
NEWT=lambda w,a,m: f'SC.serve({SPLw(w,a,m)}, cs, T.TE{{rn, rp}}, s, nc, True{{}})'
def swap(goal, old, new):
    assert old in goal, (old[:80], goal[:80])
    return goal.replace(old, new)
GOALw0=lambda w,a,m: f"RG.px.ok(AD.view(U32, KMd.words(SM.heap({SPLw(w,a,m)}))), d, s, I, RG.pls(cs, AD.view(U32, SM.map({SPLw(w,a,m)})), dm), {AP(L0, f'RG.pls(cs, AD.view(U32, SM.map({SPLw(w,a,m)})), dm)')}, F, {AP('M', f'RG.pls(cs, AD.view(U32, SM.map({SPLw(w,a,m)})), dm)')})"
PLSw=lambda w,a,m: f'RG.pls(cs, AD.view(U32, SM.map({SPLw(w,a,m)})), dm)'
CPFw=lambda w,a,m: [GOALw0(w,a,m), f'AD.full(U32, KMd.words(SM.heap({SPLw(w,a,m)})), d)', f'AD.full(U32, SM.map({SPLw(w,a,m)}), dm)', f"RG.layout({AP('M', PLSw(w,a,m))}, d)", f"RG.bases({AP('M', PLSw(w,a,m))})"]
GOALw=lambda w,a,m: T(conj(CPFw(w,a,m)))
HPw=lambda w: T(f'RG.px.ok(AD.view(U32, {w}), d, s, I, [], {L0}, {NF}, {MN})')
sec4+=f'''
def cpi.go(-w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +ts: List<&2, T.TNode>, +ls: List<&2, T.TLink>, +by: U32, +ns: List<&2, U32>, +s: U32, +t: List<&2, U32>, +cs: List<&2, R.FzC>,
  +I: IM.Ix, +F: List<&2, U32>, +M: List<&2, U32>, hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, hfm: {{AD.full(U32, map, dm) == True{{}} : Bool}}, +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}},
  +hN: {T(f'RG.layout({MN}, d)')}, +hB: {T(f'RG.bases({MN})')}, hp: {HPw('w')}, +hl: {{SM.made(ts) == List.length(&2, U32, ns) : Nat}}, +hpaMN: {T(f'KMd.past({MN}, d)')},
  +hhd: {T('KMd.off.words(KMd.hdr_words(), d, P.at_fh())')}, +hLd: {T(f'RG.distinct({L0})')}, +ht: {T('SM.tpl.ok(ls, ts, dm)')}, +hcp: {T('SV.copy.ok(cs, ls, ts, dm)')},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) -> {GOALw('w','a','map')}:
  (+t0, +ew) = mw
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, w, t0, d, ew, hf)
  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
  +hpT = LAB.subst(Array<U32>, qq => {HPw('qq')}, w, {T0}, Equal.sym(Array<U32>, {T0}, w, ew), hp)
  +hfrT = GP.faces_fresh({L0}, t0, d, {L0}, {MN}, ns, hft, hd32, {proj(C0,16,'hpT')}, sub_app_r(M, ns), none_appl(ns, F, {L0}, {proj(C0,11,'hpT')}), hN, hB)
  +hdy = dyn_of_bases(ns, GP.bases_sub(ns, {MN}, sub_app_r(M, ns), hB))
  %ew : {GOALw('_','a','map')}
  %ea : {GOALw(T0,'_','map')}
  %em : {GOALw(T0,TA,'_')}
  cpf.core(t0, ta, tm, d, dm, ts, ls, by, ns, s, t, cs, I, F, M, hft, hd32, hfmt, hdm, hN, hB, hpT, hl, hdy, hpaMN, hhd, hfrT, hLd, ht, hcp)

def Laws.copy_pend(w, a, map, d, dm, ts, ls, by, ns, s, t, cs, I, F, M, hf, hd32, hfm, hdm, hN, hB, hp, hl, hpa, hhd, hLd, ht, hcp):
  cpi.go(w, a, map, d, dm, ts, ls, by, ns, s, t, cs, I, F, M, hf, hd32, hfm, hdm, hN, hB, hp, hl, hpa, hhd, hLd, ht, hcp, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))
'''

# a serve away from the source's root, its copy then its crossings:
# copy_pend, then crossings_pend on what it gives, the laws composed as
# laws (IndexPremises P1); the arrays mirrored, each read more than once
MAPx=lambda w,a,m: f'SM.map({SPLw(w,a,m)})'
CXx=lambda w,a,m: f"RG.cxs(cs, AD.view(U32, {MAPx(w,a,m)}), dm, I, {AP(L0, PLSw(w,a,m))}, F)"
CRx=lambda w,a,m,h: f'Pair.snd(Array<U32>, P.H, R.crossings(cs, ({MAPx(w,a,m)}, {h}), s))'
def SPG(w,a,m,h=None):
    h=h or f'SM.heap({SPLw(w,a,m)})'; cx=CXx(w,a,m); cr=CRx(w,a,m,h)
    return T(conj([f"RG.px.ok(AD.view(U32, RG.words({cr})), d, s, RG.cxs.I({cx}), Nil{{}}, RG.cxs.L({cx}), RG.cxs.F({cx}), {AP('M', PLSw(w,a,m))})", f'AD.full(U32, RG.words({cr}), d)']))
HOK=lambda w,a,m: T(f'RG.cxs.ok(cs, AD.view(U32, {MAPx(w,a,m)}), dm, I, F)')
CPt=CPFw(T0,TA,TM); SPLt=SPLw(T0,TA,TM)
sec4+=f"""
# a serve away from the source's root, its copy then its crossings:
# copy_pend, then crossings_pend on what it gives (IndexPremises P1)
def sp.go(-w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +ts: List<&2, T.TNode>, +ls: List<&2, T.TLink>, +by: U32, +ns: List<&2, U32>, +s: U32, +t: List<&2, U32>, +cs: List<&2, R.FzC>,
  +I: IM.Ix, +F: List<&2, U32>, +M: List<&2, U32>, +nc: U32, +rn: U32, +rp: U32, hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, hfm: {{AD.full(U32, map, dm) == True{{}} : Bool}}, +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}},
  +hN: {T(f'RG.layout({MN}, d)')}, +hB: {T(f'RG.bases({MN})')}, hp: {HPw('w')}, +hl: {{SM.made(ts) == List.length(&2, U32, ns) : Nat}}, +hpa: {T(f'KMd.past({MN}, d)')},
  +hhd: {T('KMd.off.words(KMd.hdr_words(), d, P.at_fh())')}, +hLd: {T(f'RG.distinct({L0})')}, +ht: {T('SM.tpl.ok(ls, ts, dm)')}, +hcp: {T('SV.copy.ok(cs, ls, ts, dm)')},
  hok: {HOK('w','a','map')}, mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) ->
  {swap(SPG('w','a','map'), OLDF('w','a','map'), NEWF('w','a','map'))}:
  (+t0, +ew) = mw
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, w, t0, d, ew, hf)
  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
  +hpT = LAB.subst(Array<U32>, qq => {HPw('qq')}, w, {T0}, Equal.sym(Array<U32>, {T0}, w, ew), hp)
  +hok1 = LAB.subst(Array<U32>, qq => {HOK('qq','a','map')}, w, {T0}, Equal.sym(Array<U32>, {T0}, w, ew), hok)
  +hok2 = LAB.subst(Array<V.Val>, qq => {HOK(T0,'qq','map')}, a, {TA}, Equal.sym(Array<V.Val>, {TA}, a, ea), hok1)
  +hok3 = LAB.subst(Array<U32>, qq => {HOK(T0,TA,'qq')}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hok2)
  %ew : {swap(SPG('_','a','map'), OLDF('_','a','map'), NEWF('_','a','map'))}
  %ea : {swap(SPG(T0,'_','map'), OLDF(T0,'_','map'), NEWF(T0,'_','map'))}
  %em : {swap(SPG(T0,TA,'_'), OLDF(T0,TA,'_'), NEWF(T0,TA,'_'))}
  %Equal.sym(P.H, {NEWF(T0,TA,TM)}, {OLDF(T0,TA,TM)}, serve_false({SPLt}, cs, T.TE{{rn, rp}}, s, nc)) : {swap(SPG(T0,TA,TM), OLDF(T0,TA,TM), '_')}
  +hc = Laws.copy_pend({T0}, {TA}, {TM}, d, dm, ts, ls, by, ns, s, t, cs, I, F, M, hft, hd32, hfmt, hdm, hN, hB, hpT, hl, hpa, hhd, hLd, ht, hcp)
  %SPP.heta(SM.heap({SPLt})) : {SPG(T0,TA,TM,'_')}
  GL.crossings_pend(KMd.words(SM.heap({SPLt})), KMd.vals(SM.heap({SPLt})), SM.map({SPLt}), d, dm, s, I, {AP(L0, PLSw(T0,TA,TM))}, F, {AP('M', PLSw(T0,TA,TM))}, cs,
    {proj(CPt,1,'hc')}, hd32, {proj(CPt,2,'hc')}, hdm, {proj(CPt,3,'hc')}, {proj(CPt,4,'hc')}, {proj(CPt,0,'hc')}, hok3)

def Laws.serve_pend(w, a, map, d, dm, ts, ls, by, ns, s, t, cs, I, F, M, nc, rn, rp, hf, hd32, hfm, hdm, hN, hB, hp, hl, hpa, hhd, hLd, ht, hcp, hok):
  sp.go(w, a, map, d, dm, ts, ls, by, ns, s, t, cs, I, F, M, nc, rn, rp, hf, hd32, hfm, hdm, hN, hB, hp, hl, hpa, hhd, hLd, ht, hcp, hok, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))
"""
sec+=sec4
if os.environ.get('CPI_PART')=='4':
    open('glam/proofgen/sv/cpi1.txt','w').write(sec)
    print('part4', len(sec.splitlines()))
# ---- part 5: serve_keeps over the index ----
H0t=f'P.H{{KM.MG{{{T0}}}, {TA}}}'
CR=lambda heap: f'Pair.snd(Array<U32>, P.H, R.crossings(cs, ({MAP1}, {heap}), s))'
RDj=lambda h: f'Pair.snd(P.H, U32, P.rd({h}, j))'
JP_=(f"+hok: {T(f'RG.cxs.ok(cs, {MAPV}, dm, I, F)')}, +j: U32, +hj: {T('KMd.nodes.off(ns, d, j)')}, +hjM: {T('RG.off.nodes(M, d, j)')}, "
     f"+hjh: {T('KMd.off.words(KMd.hdr_all(), d, j)')}, +hjf: {T(f'RG.off.ports(RG.faced({L0}, {V0}, d), d, j)')}")
FCED=lambda v: f'RG.faced({L0}, {v}, d)'
hjf2=(f"ME.subst(List<&2, U32>, zz => {T('RG.off.ports(zz, d, j)')}, List.append(&2, U32, RG.faced({L0}, {V1}, d), RG.faced({PLS}, {V1}, d)), RG.faced({Lp}, {V1}, d), "
      f"Equal.sym(List<&2, U32>, RG.faced({Lp}, {V1}, d), List.append(&2, U32, RG.faced({L0}, {V1}, d), RG.faced({PLS}, {V1}, d)), faced_app({L0}, {PLS}, {V1}, d)), "
      f"ops_app(RG.faced({L0}, {V1}, d), RG.faced({PLS}, {V1}, d), d, j, ME.subst(List<&2, U32>, zz => {T('RG.off.ports(zz, d, j)')}, {FCED(V0)}, {FCED(V1)}, Equal.sym(List<&2, U32>, {FCED(V1)}, {FCED(V0)}, faced_agree({L0}, {CTXA}, GP.sub_refl({L0}))), hjf), "
      f"holes_offp(cs, cs, {CTXA}, j, hj, hh, hh, GP.sub_refl(SV.ats(cs)))))")
sec5=f'''
# a serve's writes, the copy's then the crossings': their frames composed,
# the crossings' premises the copy's invariant
def sk.core({CORE_P}, {JP_}) ->
  {{{RDj(CR(f'SM.heap({SPL})'))} == {RDj(H0t)} : U32}}:
{lets}  +hpx = cpi.core({CORE_A})
  %SPP.heta(SM.heap({SPL})) : {{{RDj(CR('_'))} == {RDj(H0t)} : U32}}
  ME.trans3(U32, {RDj(CR(f'P.H{{KM.MG{{{W1}}}, {A1}}}'))}, {RDj(f'P.H{{KM.MG{{{W1}}}, {A1}}}')}, {RDj(f'SM.heap({SPL})')}, {RDj(H0t)},
    GL.crossings_keeps({W1}, {A1}, {MAP1}, d, dm, s, I, {Lp}, F, {Mp}, cs, j, copy_full({CTXA}), hd32, {MAPFULL}, hdm,
      GP.lay_sub({Mp}, {MN}, d, hMpMN, hN, apall_of({Mp}, {MN}, d, hMpMN, hN, {DMP})), GP.bases_sub({Mp}, {MN}, hMpMN, hB), hpx, hok,
      offn_app(M, {PLS}, d, j, hjM, GP.off_nodes_sub({PLS}, ns, d, j, hPs, rn_of(ns, d, j, hj))),
      MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)), {L('Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)))','KMd.off.words(KMd.hdr_words(), d, j)','hjh')}), {hjf2}),
    ME.subst(P.H, qq => {{{RDj(f'P.H{{KM.MG{{{W1}}}, {A1}}}')} == {RDj('qq')} : U32}}, P.H{{KM.MG{{{W1}}}, {A1}}}, SM.heap({SPL}), SPP.heta(SM.heap({SPL})), {{==}}),
    SPL.splice_keeps({T0}, {TA}, {TM}, d, dm, ts, ls, by, ns, j, hft, hd32, hfmt, hdm, hct, hl, kap_of_lay(ns, d, lay_suffix({L0}, ns, d, hlay)), past_suffix({L0}, ns, d, hpa), hj, hjh, hhd, ht))
'''
SPLw2=lambda w,a,m: f'S.sp.links(ls, S.sp.nodes(ts, 0, S.Sp{{P.H{{KM.MG{{{w}}}, {a}}}, {m}}}, by))'
GOALk=lambda w,a,m: f"{{{RDj(f'Pair.snd(Array<U32>, P.H, R.crossings(cs, (SM.map({SPLw2(w,a,m)}), SM.heap({SPLw2(w,a,m)})), s))')} == {RDj(f'P.H{{KM.MG{{{w}}}, {a}}}')} : U32}}"
HOKw=lambda m: T(f"RG.cxs.ok(cs, AD.view(U32, SM.map({SPLw2('w','a',m) if m=='map' else SPLw2(T0,TA,m)})), dm, I, F)")
sec5+=f'''
def sk.go(-w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +ts: List<&2, T.TNode>, +ls: List<&2, T.TLink>, +by: U32, +ns: List<&2, U32>, +s: U32, +t: List<&2, U32>, +cs: List<&2, R.FzC>,
  +I: IM.Ix, +F: List<&2, U32>, +M: List<&2, U32>, +nc: U32, +rn: U32, +rp: U32, +j: U32, hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, hfm: {{AD.full(U32, map, dm) == True{{}} : Bool}}, +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}},
  +hN: {T(f'RG.layout({MN}, d)')}, +hB: {T(f'RG.bases({MN})')}, hp: {HPw('w')}, +hl: {{SM.made(ts) == List.length(&2, U32, ns) : Nat}}, +hpaMN: {T(f'KMd.past({MN}, d)')},
  +hhd: {T('KMd.off.words(KMd.hdr_words(), d, P.at_fh())')}, +hLd: {T(f'RG.distinct({L0})')}, +ht: {T('SM.tpl.ok(ls, ts, dm)')}, +hcp: {T('SV.copy.ok(cs, ls, ts, dm)')},
  hok: {T(f"RG.cxs.ok(cs, AD.view(U32, SM.map({SPLw2('w','a','map')})), dm, I, F)")}, +hj: {T('KMd.nodes.off(ns, d, j)')}, +hjM: {T('RG.off.nodes(M, d, j)')}, +hjh: {T('KMd.off.words(KMd.hdr_all(), d, j)')},
  hjf: {T(f'RG.off.ports(RG.faced({L0}, AD.view(U32, w), d), d, j)')}, mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) -> {swap(GOALk('w','a','map'), OLDF('w','a','map'), NEWF('w','a','map'))}:
  (+t0, +ew) = mw
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, w, t0, d, ew, hf)
  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
  +hpT = LAB.subst(Array<U32>, qq => {HPw('qq')}, w, {T0}, Equal.sym(Array<U32>, {T0}, w, ew), hp)
  +hfrT = GP.faces_fresh({L0}, t0, d, {L0}, {MN}, ns, hft, hd32, {proj(C0,16,'hpT')}, sub_app_r(M, ns), none_appl(ns, F, {L0}, {proj(C0,11,'hpT')}), hN, hB)
  +hdy = dyn_of_bases(ns, GP.bases_sub(ns, {MN}, sub_app_r(M, ns), hB))
  +hjfT = LAB.subst(Array<U32>, qq => {T(f'RG.off.ports(RG.faced({L0}, AD.view(U32, qq), d), d, j)')}, w, {T0}, Equal.sym(Array<U32>, {T0}, w, ew), hjf)
  +hok1 = LAB.subst(Array<U32>, qq => {T(f"RG.cxs.ok(cs, AD.view(U32, SM.map({SPLw2('qq','a','map')})), dm, I, F)")}, w, {T0}, Equal.sym(Array<U32>, {T0}, w, ew), hok)
  +hok2 = LAB.subst(Array<V.Val>, qq => {T(f"RG.cxs.ok(cs, AD.view(U32, SM.map({SPLw2(T0,'qq','map')})), dm, I, F)")}, a, {TA}, Equal.sym(Array<V.Val>, {TA}, a, ea), hok1)
  +hok3 = LAB.subst(Array<U32>, qq => {T(f"RG.cxs.ok(cs, AD.view(U32, SM.map({SPLw2(T0,TA,'qq')})), dm, I, F)")}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hok2)
  %ew : {swap(GOALk('_','a','map'), OLDF('_','a','map'), NEWF('_','a','map'))}
  %ea : {swap(GOALk(T0,'_','map'), OLDF(T0,'_','map'), NEWF(T0,'_','map'))}
  %em : {swap(GOALk(T0,TA,'_'), OLDF(T0,TA,'_'), NEWF(T0,TA,'_'))}
  %Equal.sym(P.H, {NEWF(T0,TA,TM)}, {OLDF(T0,TA,TM)}, serve_false({SPLt}, cs, T.TE{{rn, rp}}, s, nc)) : {swap(GOALk(T0,TA,TM), OLDF(T0,TA,TM), '_')}
  sk.core({CORE_A.replace('hp, hl','hpT, hl').replace('hfr, hLd','hfrT, hLd')}, hok3, j, hj, hjM, hjh, hjfT)

def Laws.serve_keeps(w, a, map, d, dm, ts, ls, by, ns, s, t, cs, I, F, M, nc, rn, rp, j, hf, hd32, hfm, hdm, hN, hB, hp, hl, hpa, hhd, hLd, ht, hcp, hok, hj, hjM, hjh, hjf):
  sk.go(w, a, map, d, dm, ts, ls, by, ns, s, t, cs, I, F, M, nc, rn, rp, j, hf, hd32, hfm, hdm, hN, hB, hp, hl, hpa, hhd, hLd, ht, hcp, hok, hj, hjM, hjh, hjf, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))
'''
sec+=sec5
if os.environ.get('CPI_PART')=='5':
    open('glam/proofgen/sv/cpi1.txt','w').write(sec)
    print('part5', len(sec.splitlines()))
# ---- part 6: serve_ring_exact over the index ----
sec6=''
for i in (2,3):
    x=P1('q',i)
    sec6+=f'''
def nmk{i}(+e: Bool, +x: U32, +r: List<&2, U32>, +ys: List<&2, U32>, +N: List<&2, U32>, +d: Nat, +q: U32, +he: {{RG.has(ys, x) == e : Bool}}, +hN: {T('RG.layout(N, d)')}, +hxN: {T('RG.has(N, x)')},
  +hqN: {T('RG.has(N, q)')}, +hq: {T('RG.has(ys, q)')}, +hih: {T(f'KMd.nodes.off(RG.minus(r, ys), d, {x})')}) -> {T(f'KMd.nodes.off(RG.minus.k(e, x, RG.minus(r, ys)), d, {x})')}:
  match e:
    case True{{}}:
      hih
    case False{{}}:
      {A(OWS('x',x), f'KMd.nodes.off(RG.minus(r, ys), d, {x})', proj(DISJ('q','x'), i, f"MB.eq_true_of_and_left(IM.nd.disj(d, q, x), IM.nd.disj(d, x, q), XL.layout_sep(N, d, q, x, hN, hqN, hxN, GP.nhas(ys, q, x, hq, he)))"), 'hih')}

def noff_minus{i}(xs: List<&2, U32>, +ys: List<&2, U32>, +N: List<&2, U32>, +d: Nat, +q: U32, +hN: {T('RG.layout(N, d)')}, +hs: {T('RG.sub(xs, N)')}, +hqN: {T('RG.has(N, q)')}, +hq: {T('RG.has(ys, q)')}) ->
  {T(f'KMd.nodes.off(RG.minus(xs, ys), d, {x})')}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +r}}:
      nmk{i}(RG.has(ys, x), x, r, ys, N, d, q, {{==}}, hN, {L('RG.has(N, x)','RG.sub(r, N)','hs')}, hqN, hq, noff_minus{i}(r, ys, N, d, q, hN, {R('RG.has(N, x)','RG.sub(r, N)','hs')}, hqN, hq))
'''
# the crossings' live nodes among those before
sec6+=f'''
# The served cursor leaving at the source's root over the index
# (serve_ring_exact; cells-freeze.sharing.cursors.index.ring.leave). The
# crossings' live nodes among those before
def cxl_sub(m: Maybe<&2, U32>, +x: U32, +L: List<&2, U32>) -> {T('RG.sub(RG.cx.L(m, x, L), L)')}:
  match m:
    case Some{{+y}}:
      GP.sub_trans(RG.without(RG.without(L, x), y), RG.without(L, x), L, GP.sub_without(RG.without(L, x), y), GP.sub_without(L, x))
    case None{{}}:
      GP.sub_refl(L)

def cxs_lsub(cs: List<&2, R.FzC>, +vm: List<&2, U32>, +dm: Nat, +I: IM.Ix, +L: List<&2, U32>, +F: List<&2, U32>) -> {T('RG.sub(RG.cxs.L(RG.cxs(cs, vm, dm, I, L, F)), L)')}:
  match cs:
    case Nil{{}}:
      GP.sub_refl(L)
    case Con{{c, +r}}:
      match c:
        case R.FzC{{+at, +src, neg, +far}}:
          GP.sub_trans(RG.cxs.L(RG.cxs(r, vm, dm, RG.cx.I(IM.ix.look(I, far), I, RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), src, RG.cx.hd(F), far), RG.cx.L(IM.ix.look(I, far), RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), L), RG.cx.F1(IM.ix.look(I, far), I, RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), far, RG.cx.tl(IM.ix.look(I, far), I, F)))),
            RG.cx.L(IM.ix.look(I, far), RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), L), L,
            cxs_lsub(r, vm, dm, RG.cx.I(IM.ix.look(I, far), I, RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), src, RG.cx.hd(F), far), RG.cx.L(IM.ix.look(I, far), RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), L), RG.cx.F1(IM.ix.look(I, far), I, RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), far, RG.cx.tl(IM.ix.look(I, far), I, F))),
            cxl_sub(IM.ix.look(I, far), RG.pl.of(List.get(&2, U32, vm, AD.slot(at, dm))), L))
'''
# the root port: a fresh node's that is no hole, its link word off every
# tracked node's words and the head
PW=f'(KMd.word(AD.view(U32, SM.map({SPN})), dm, rn) + rp : U32)'
ROOTP=f"+rn: U32, +rp: U32, +hk1: {T('SV.node.at(ts, dm, rn)')}, +hp3: {T('SM.port3(rp)')}, +hnin: {F_('SV.sl.in(SV.ats(cs), dm, rn)')}"
ROOTA='rn, rp, hk1, hp3, hnin'
OFR=lambda j,hj: f'off_fresh({CTXA}, {j}, {hj}, rn, rp, hk1, hp3)'
OFR2=lambda j,hj: f'off_fresh2(cs, {CTXA}, {j}, {hj}, rn, rp, hk1, hp3, hnin, hh)'
RPAR=f'{CTXP}, {EXP}, {ROOTP}'
RARG=f'{CTXA}, {EXA}, {ROOTA}'
def rp_body(Kl, nm, fresh2):
    v='q' if fresh2 else 'n'
    hv='hqP' if fresh2 else 'hnM'
    off=(lambda i: OFR2(P1(v,i), NMi(i,v,'hqMN','hqP'))) if fresh2 else (lambda i: OFR(P1(v,i), NSi(i,v,'hnM')))
    lets_=(f"      +hqP = {L(f'RG.has({PLS}, q)','RG.sub(k, '+PLS+')','hK')}\n      +hqMN = has_app_r(M, ns, q, GP.sub_has({PLS}, ns, q, hPs, hqP))\n" if fresh2
           else f"      +hnM = {L('RG.has(M, n)','RG.sub(k, M)','hK')}\n")
    rest=R(f'RG.has({PLS}, q)','RG.sub(k, '+PLS+')','hK') if fresh2 else R('RG.has(M, n)','RG.sub(k, M)','hK')
    return f'''  match K:
    case Nil{{}}:
      {OFR('P.at_fh()','SPP.npast(ns, d, hpns)')}
    case Con{{+{v}, +k}}:
{lets_}      {A(PON(PW,'[]',v), f'RG.po.all({PW}, [], d, k)',
        A(f'KMd.off.port(d, {PW}, {v})', f'Bool.or(RG.has([], {v}), {OFF3(PW,v)})', off(0),
          f"SPP.or_r(RG.has([], {v}), {OFF3(PW,v)}, {A(f'KMd.off.port(d, {PW}, ({v} + 1 : U32))', f'KMd.off.port(d, {PW}, ({v} + 2 : U32)) && KMd.off.port(d, {PW}, ({v} + 3 : U32))', off(1), A(f'KMd.off.port(d, {PW}, ({v} + 2 : U32))', f'KMd.off.port(d, {PW}, ({v} + 3 : U32))', off(2), off(3)))})"),
        f"{nm}(k, {RARG}, {rest})")}
'''
sec6+=f'''
# the copy's root port, its node no hole: its link word off every word of
# the tracked nodes, of the holes, and off the head
def rpom(K: List<&2, U32>, {RPAR}, +hK: {T('RG.sub(K, M)')}) -> {T(f'RG.po.all({PW}, [], d, K)')}:
{rp_body('M','rpom',False)}
def rpop(K: List<&2, U32>, {RPAR}, +hK: {T(f'RG.sub(K, {PLS})')}) -> {T(f'RG.po.all({PW}, [], d, K)')}:
{rp_body(PLS,'rpop',True)}'''
# the core
HE=f'P.H{{KM.MG{{{W1}}}, {A1}}}'
CX=f'RG.cxs(cs, {MAPV}, dm, I, {Lp}, F)'; CXI=f'RG.cxs.I({CX})'; CXL=f'RG.cxs.L({CX})'; CXF=f'RG.cxs.F({CX})'
PEXP=lambda heap: f'(Pair.snd(Array<U32>, U32, Array.get(U32, Pair.fst(Array<U32>, P.H, R.crossings(cs, ({MAP1}, {heap}), s)), rn)) + rp : U32)'
H2=CR(HE)
# the invariant after the leave and the words full (IndexPremises P1)
LVc=lambda heap, leave_h=None: f"R.leave({leave_h if leave_h else CR(heap)}, {PEXP(heap)}, nc)"
CONC=lambda heap, leave_h=None: (f"RG.px.ok(AD.view(U32, RG.words({LVc(heap, leave_h)})), d, s, IM.ix.del({CXI}, nc, k), [], RG.without({CXL}, nc), "
                                 f"Con{{nc, IM.mb.cons(IM.ix.par({CXI}, nc, k), {CXF})}}, {Mp}) && AD.full(U32, RG.words({LVc(heap, leave_h)}), d)")
MFULLN=f'SPP.mfull_go(ts, SPP.hd_era(ts), {{==}}, {T0}, {TA}, {TM}, dm, 0, by, hfmt, LAT.mirror(U32, {T0}), LAT.mirror(V.Val, {TA}), LAT.mirror(U32, {TM}))'
def RPC(pred, prf):
    FST=f'Pair.fst(Array<U32>, P.H, R.crossings(cs, ({MAP1}, {HE}), s))'
    PEz=lambda z: f'(Pair.snd(Array<U32>, U32, Array.get(U32, {z}, rn)) + rp : U32)'
    SOME=f'Some{{Pair.snd(Array<U32>, U32, Array.get(U32, SM.map({SPN}), rn))}}'
    LG=f'List.get(&2, U32, AD.view(U32, SM.map({SPN})), AD.slot(rn, dm))'
    return (f"ME.subst(Array<U32>, zz => {pred(PEz('zz'))}, {MAP1}, {FST}, Equal.sym(Array<U32>, {FST}, {MAP1}, cr_map(cs, {MAP1}, {HE}, s, LAT.mirror(U32, {MAP1}))), "
            f"ME.subst(Array<U32>, zz => {pred(PEz('zz'))}, SM.map({SPN}), {MAP1}, Equal.sym(Array<U32>, {MAP1}, SM.map({SPN}), lmap(ls, {SPN})), "
            f"ME.subst(Maybe<&2, U32>, zz => {pred('(KMd.word.m(zz) + rp : U32)')}, {LG}, {SOME}, Equal.sym(Maybe<&2, U32>, {SOME}, {LG}, LA.get_view(U32, SM.map({SPN}), dm, rn, {MFULLN}, hdm)), {prf})))")
PXc=f'RG.px.ok(AD.view(U32, RG.words({H2})), d, s, {CXI}, [], {CXL}, {CXF}, {Mp})'; FLc=f'AD.full(U32, RG.words({H2}), d)'
NROOT='Bool.not(SV.sl.in(SV.ats(cs), dm, rn)) && SM.port3(rp)'
EP=(f"+hok: {T(f'RG.cxs.ok(cs, {MAPV}, dm, I, F)')}, +nc: U32, +k: U32, +hc0: {{IM.ix.look(I, k) == Some{{nc}} : Maybe<&2, U32>}}, +hu: {T('RG.far.off(cs, k)')}, +rn: U32, +rp: U32, +hro: {T('SV.root.ok(rn, rp, ts, dm, cs)')}")
sec6+=f'''
# the copy, its crossings, then the served cursor's leave, the copy's root
# port joined in its place: leave_pend on crossings_pend on copy_pend
def rx.core({CORE_P}, {EP}) ->
  {T(CONC(f'SM.heap({SPL})'))}:
{lets}  +hk1 = {L('SV.node.at(ts, dm, rn)', NROOT, 'hro')}
  +hnin = MB.eq_false_of_not_eq_true(SV.sl.in(SV.ats(cs), dm, rn), {L('Bool.not(SV.sl.in(SV.ats(cs), dm, rn))', 'SM.port3(rp)', R('SV.node.at(ts, dm, rn)', NROOT, 'hro'))})
  +hp3 = {R('Bool.not(SV.sl.in(SV.ats(cs), dm, rn))', 'SM.port3(rp)', R('SV.node.at(ts, dm, rn)', NROOT, 'hro'))}
  +hpx = cpi.core({CORE_A})
  +hNp = GP.lay_sub({Mp}, {MN}, d, hMpMN, hN, apall_of({Mp}, {MN}, d, hMpMN, hN, {DMP}))
  +hBp = GP.bases_sub({Mp}, {MN}, hMpMN, hB)
  +hc = GP.cxl.m({W1}, {A1}, {MAP1}, d, dm, s, I, {Lp}, F, {Mp}, cs, copy_full({CTXA}), hd32, {MAPFULL}, hdm, hNp, hBp, hpx, hok, k, nc, hc0, hu, LAT.mirror(U32, {W1}), LAT.mirror(V.Val, {A1}), LAT.mirror(U32, {MAP1}))
  +hcx = GP.crf.go(cs, {W1}, {A1}, {MAP1}, d, dm, s, I, {Lp}, F, {Mp}, copy_full({CTXA}), hd32, {MAPFULL}, hdm, hNp, hBp, hpx, hok, LAT.mirror(U32, {W1}), LAT.mirror(V.Val, {A1}), LAT.mirror(U32, {MAP1}))
  +hp2 = ME.subst(Array<U32>, zz => {T(f'RG.px.ok(AD.view(U32, zz), d, s, {CXI}, [], {CXL}, {CXF}, {Mp})')}, RG.words({H2}), KMd.words({H2}), GP.rw_kw({H2}), {L(PXc, FLc, 'hcx')})
  +hf2 = ME.subst(Array<U32>, zz => {{AD.full(U32, zz, d) == True{{}} : Bool}}, RG.words({H2}), KMd.words({H2}), GP.rw_kw({H2}), {R(PXc, FLc, 'hcx')})
  +hpo = {RPC(lambda pe: T(f'RG.po.all({pe}, [], d, {Mp})'), f"po_app(M, {PLS}, {PW}, [], d, rpom(M, {RARG}, GP.sub_refl(M)), rpop({PLS}, {RARG}, GP.sub_refl({PLS})))")}
  %SPP.heta(SM.heap({SPL})) : {T(CONC('_'))}
  %SPP.heta({H2}) : {T(CONC(HE, '_'))}
  GL.leave_pend(KMd.words({H2}), KMd.vals({H2}), d, s, {CXI}, [], {CXL}, {CXF}, {Mp}, {PEXP(HE)}, nc, k, hf2, hd32, hNp, hBp, hp2, hc, hpo)
'''
# the entry, the heap's parts mirrored
SPLx=lambda w,a,m: SPLw2(w,a,m)
def CONCw(w,a,m):
    spl=SPLx(w,a,m); mapv=f'AD.view(U32, SM.map({spl}))'; pls=f'RG.pls(cs, {mapv}, dm)'
    cx=f'RG.cxs(cs, {mapv}, dm, I, {AP(L0, pls)}, F)'
    crh=f'R.crossings(cs, (SM.map({spl}), SM.heap({spl})), s)'
    lv=f"R.leave(Pair.snd(Array<U32>, P.H, {crh}), (Pair.snd(Array<U32>, U32, Array.get(U32, Pair.fst(Array<U32>, P.H, {crh}), rn)) + rp : U32), nc)"
    return (f"RG.px.ok(AD.view(U32, RG.words({lv})), d, s, "
            f"IM.ix.del(RG.cxs.I({cx}), nc, k), [], RG.without(RG.cxs.L({cx}), nc), Con{{nc, IM.mb.cons(IM.ix.par(RG.cxs.I({cx}), nc, k), RG.cxs.F({cx}))}}, {AP('M', pls)}) && AD.full(U32, RG.words({lv}), d)")
HCw=lambda w,a,m: (lambda mapv: f"{{IM.ix.look(RG.cxs.I(RG.cxs(cs, {mapv}, dm, I, {AP(L0, f'RG.pls(cs, {mapv}, dm)')}, F)), k) == Some{{nc}} : Maybe<&2, U32>}}")(f'AD.view(U32, SM.map({SPLx(w,a,m)}))')
sec6+=f'''
def rx.go(-w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +ts: List<&2, T.TNode>, +ls: List<&2, T.TLink>, +by: U32, +ns: List<&2, U32>, +s: U32, +t: List<&2, U32>, +cs: List<&2, R.FzC>,
  +I: IM.Ix, +F: List<&2, U32>, +M: List<&2, U32>, +nc: U32, +k: U32, +rn: U32, +rp: U32, hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, hfm: {{AD.full(U32, map, dm) == True{{}} : Bool}}, +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}},
  +hN: {T(f'RG.layout({MN}, d)')}, +hB: {T(f'RG.bases({MN})')}, hp: {HPw('w')}, +hl: {{SM.made(ts) == List.length(&2, U32, ns) : Nat}}, +hpaMN: {T(f'KMd.past({MN}, d)')},
  +hhd: {T('KMd.off.words(KMd.hdr_words(), d, P.at_fh())')}, +hLd: {T(f'RG.distinct({L0})')}, +ht: {T('SM.tpl.ok(ls, ts, dm)')}, +hcp: {T('SV.copy.ok(cs, ls, ts, dm)')},
  hok: {T(f"RG.cxs.ok(cs, AD.view(U32, SM.map({SPLw2('w','a','map')})), dm, I, F)")}, +hc: {{IM.ix.look(I, k) == Some{{nc}} : Maybe<&2, U32>}}, +hu: {T('RG.far.off(cs, k)')}, +hro: {T('SV.root.ok(rn, rp, ts, dm, cs)')},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) -> {T(swap(CONCw('w','a','map'), OLDT('w','a','map'), NEWT('w','a','map')))}:
  (+t0, +ew) = mw
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, w, t0, d, ew, hf)
  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
  +hpT = LAB.subst(Array<U32>, qq => {HPw('qq')}, w, {T0}, Equal.sym(Array<U32>, {T0}, w, ew), hp)
  +hfrT = GP.faces_fresh({L0}, t0, d, {L0}, {MN}, ns, hft, hd32, {proj(C0,16,'hpT')}, sub_app_r(M, ns), none_appl(ns, F, {L0}, {proj(C0,11,'hpT')}), hN, hB)
  +hdy = dyn_of_bases(ns, GP.bases_sub(ns, {MN}, sub_app_r(M, ns), hB))
  +hok1 = LAB.subst(Array<U32>, qq => {T(f"RG.cxs.ok(cs, AD.view(U32, SM.map({SPLw2('qq','a','map')})), dm, I, F)")}, w, {T0}, Equal.sym(Array<U32>, {T0}, w, ew), hok)
  +hok2 = LAB.subst(Array<V.Val>, qq => {T(f"RG.cxs.ok(cs, AD.view(U32, SM.map({SPLw2(T0,'qq','map')})), dm, I, F)")}, a, {TA}, Equal.sym(Array<V.Val>, {TA}, a, ea), hok1)
  +hok3 = LAB.subst(Array<U32>, qq => {T(f"RG.cxs.ok(cs, AD.view(U32, SM.map({SPLw2(T0,TA,'qq')})), dm, I, F)")}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hok2)
  %ew : {T(swap(CONCw('_','a','map'), OLDT('_','a','map'), NEWT('_','a','map')))}
  %ea : {T(swap(CONCw(T0,'_','map'), OLDT(T0,'_','map'), NEWT(T0,'_','map')))}
  %em : {T(swap(CONCw(T0,TA,'_'), OLDT(T0,TA,'_'), NEWT(T0,TA,'_')))}
  %Equal.sym(P.H, {NEWT(T0,TA,TM)}, {OLDT(T0,TA,TM)}, serve_true({SPLt}, cs, rn, rp, s, nc)) : {T(swap(CONCw(T0,TA,TM), OLDT(T0,TA,TM), '_'))}
  rx.core({CORE_A.replace('hp, hl','hpT, hl').replace('hfr, hLd','hfrT, hLd')}, hok3, nc, k, hc, hu, rn, rp, hro)

def Laws.serve_ring_exact(w, a, map, d, dm, ts, ls, by, ns, s, t, cs, I, F, M, nc, k, rn, rp, hf, hd32, hfm, hdm, hN, hB, hp, hl, hpa, hhd, hLd, ht, hcp, hok, hc, hu, hro):
  rx.go(w, a, map, d, dm, ts, ls, by, ns, s, t, cs, I, F, M, nc, k, rn, rp, hf, hd32, hfm, hdm, hN, hB, hp, hl, hpa, hhd, hLd, ht, hcp, hok, hc, hu, hro, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))
'''
SRE_LAW=f'''law serve_ring_exact:
  for w: Array<U32>
  for a: Array<V.Val>
  for map: Array<U32>
  for +d: Nat
  for +dm: Nat
  for +ts: List<&2, T.TNode>
  for +ls: List<&2, T.TLink>
  for +by: U32
  for +ns: List<&2, U32>
  for +s: U32
  for +t: List<&2, U32>
  for +cs: List<&2, R.FzC>
  for +I: IM.Ix
  for +F: List<&2, U32>
  for +M: List<&2, U32>
  for +nc: U32
  for +k: U32
  for +rn: U32
  for +rp: U32
  for +hf: {{AD.full(U32, w, d) == True{{}} : Bool}}
  for +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}
  for +hfm: {{AD.full(U32, map, dm) == True{{}} : Bool}}
  for +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}}
  for +hN: {{RG.layout(List.append(&2, U32, M, ns), d) == True{{}} : Bool}}
  for +hB: {{RG.bases(List.append(&2, U32, M, ns)) == True{{}} : Bool}}
  for +hp: {{RG.px.ok(AD.view(U32, w), d, s, I, Nil{{}}, Con{{s, t}}, List.append(&2, U32, ns, F), List.append(&2, U32, M, ns)) == True{{}} : Bool}}
  for +hl: {{SM.made(ts) == List.length(&2, U32, ns) : Nat}}
  for +hpa: {{KMd.past(List.append(&2, U32, M, ns), d) == True{{}} : Bool}}
  for +hhd: {{KMd.off.words(KMd.hdr_words(), d, P.at_fh()) == True{{}} : Bool}}
  for +hLd: {{RG.distinct(Con{{s, t}}) == True{{}} : Bool}}
  for +ht: {{SM.tpl.ok(ls, ts, dm) == True{{}} : Bool}}
  for +hcp: {{SV.copy.ok(cs, ls, ts, dm) == True{{}} : Bool}}
  for +hok: {{RG.cxs.ok(cs, AD.view(U32, SM.map({SPLw2('w','a','map')})), dm, I, F) == True{{}} : Bool}}
  for +hc: {{IM.ix.look(I, k) == Some{{nc}} : Maybe<&2, U32>}}
  for +hu: {{RG.far.off(cs, k) == True{{}} : Bool}}
  for +hro: {{SV.root.ok(rn, rp, ts, dm, cs) == True{{}} : Bool}}
  {{{CONCw('w','a','map').replace('[], RG.without','Nil{}, RG.without')} == True{{}} : Bool}}'''
if os.environ.get('CPI_PART')=='6':
    open('glam/proofgen/sv/cpi6.txt','w').write(sec6)
    open('glam/proofgen/sv/sre_law.txt','w').write(SRE_LAW)
    print('part6', len(sec6.splitlines()))
# ---- part 7: serve_root_keeps over the index ----
trans=nsJ['trans']
FP1=f'RG.faced({Lp}, {V1}, d)'
RDj=lambda h: f'Pair.snd(P.H, U32, P.rd({h}, j))'
H2E=f'P.H{{KM.MG{{KMd.words({H2})}}, KMd.vals({H2})}}'
C2=PXOK(f'AD.view(U32, KMd.words({H2}))', CXI, '[]', CXL, CXF, Mp)
LVX=f'IM.ix.leaves({CXI})'
GK7=lambda heap, lh=None: f"{{{RDj(f'R.leave({lh if lh else CR(heap)}, {PEXP(heap)}, nc)')} == {RDj(H0t)} : U32}}"
sec7=f'''
# The served cursor's leave at the source's root, its frame
# (serve_root_keeps; cells-freeze.sharing.cursors.index.ring.leave): the
# port a node faces among Fp, its link word off j where Fp's all are
def fin_off(m: Maybe<&2, U32>, +d: Nat, +Fp: List<&2, U32>, +j: U32, +h: {T('GP.fin.m(m, d, Fp)')}, +hops: {T('RG.off.ports(Fp, d, j)')}) -> {T('KMd.off.port(d, KMd.word.m(m), j)')}:
  match m:
    case Some{{+r}}:
      GP.ops_at(Fp, d, j, r, hops, h)
    case None{{}}:
      Empty.absurd({T('KMd.off.port(d, KMd.word.m(None{}), j)')}, MB.false_ne_true()(h))

# the copy, its crossings, then the leave: serve_keeps's frame, then
# leave_keeps's, the port the served cursor faces after the crossings
# among those the live nodes faced after the copy (cfi.m)
def rk.core({CORE_P}, {EP}, +j: U32, +hj: {T('KMd.nodes.off(ns, d, j)')}, +hjM: {T('RG.off.nodes(M, d, j)')}, +hjh: {T('KMd.off.words(KMd.hdr_all(), d, j)')}, +hjf: {T(f'RG.off.ports(RG.faced({L0}, {V0}, d), d, j)')}) ->
  {GK7(f'SM.heap({SPL})')}:
{lets}  +hk1 = {L('SV.node.at(ts, dm, rn)', NROOT, 'hro')}
  +hnin = MB.eq_false_of_not_eq_true(SV.sl.in(SV.ats(cs), dm, rn), {L('Bool.not(SV.sl.in(SV.ats(cs), dm, rn))', 'SM.port3(rp)', R('SV.node.at(ts, dm, rn)', NROOT, 'hro'))})
  +hp3 = {R('Bool.not(SV.sl.in(SV.ats(cs), dm, rn))', 'SM.port3(rp)', R('SV.node.at(ts, dm, rn)', NROOT, 'hro'))}
  +hpx = cpi.core({CORE_A})
  +hNp = GP.lay_sub({Mp}, {MN}, d, hMpMN, hN, apall_of({Mp}, {MN}, d, hMpMN, hN, {DMP}))
  +hBp = GP.bases_sub({Mp}, {MN}, hMpMN, hB)
  +hc = GP.cxl.m({W1}, {A1}, {MAP1}, d, dm, s, I, {Lp}, F, {Mp}, cs, copy_full({CTXA}), hd32, {MAPFULL}, hdm, hNp, hBp, hpx, hok, k, nc, hc0, hu, LAT.mirror(U32, {W1}), LAT.mirror(V.Val, {A1}), LAT.mirror(U32, {MAP1}))
  +hcx = GP.crf.go(cs, {W1}, {A1}, {MAP1}, d, dm, s, I, {Lp}, F, {Mp}, copy_full({CTXA}), hd32, {MAPFULL}, hdm, hNp, hBp, hpx, hok, LAT.mirror(U32, {W1}), LAT.mirror(V.Val, {A1}), LAT.mirror(U32, {MAP1}))
  +hp2 = ME.subst(Array<U32>, zz => {T(f'RG.px.ok(AD.view(U32, zz), d, s, {CXI}, [], {CXL}, {CXF}, {Mp})')}, RG.words({H2}), KMd.words({H2}), GP.rw_kw({H2}), {L(PXc, FLc, 'hcx')})
  +hf2 = ME.subst(Array<U32>, zz => {{AD.full(U32, zz, d) == True{{}} : Bool}}, RG.words({H2}), KMd.words({H2}), GP.rw_kw({H2}), {R(PXc, FLc, 'hcx')})
  +hpo = {RPC(lambda pe: T(f'RG.po.all({pe}, [], d, {Mp})'), f"po_app(M, {PLS}, {PW}, [], d, rpom(M, {RARG}, GP.sub_refl(M)), rpop({PLS}, {RARG}, GP.sub_refl({PLS})))")}
  +hjMp = offn_app(M, {PLS}, d, j, hjM, GP.off_nodes_sub({PLS}, ns, d, j, hPs, rn_of(ns, d, j, hj)))
  +hjh2 = MB.eq_false_of_not_eq_true(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)), {L('Bool.not(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot(j, d)))','KMd.off.words(KMd.hdr_words(), d, j)','hjh')})
  +hjf2 = {hjf2}
  +hjp = {RPC(lambda pe: T(f'KMd.off.port(d, {pe}, j)'), OFR('j','hj'))}
  +hfi = GP.cfi.m({W1}, {A1}, {MAP1}, d, dm, s, I, {Lp}, F, {Mp}, cs, copy_full({CTXA}), hd32, {MAPFULL}, hdm, hNp, hBp, hpx, hok, LAT.mirror(U32, {W1}), LAT.mirror(V.Val, {A1}), LAT.mirror(U32, {MAP1}))
  +hncL = GP.sub_has({LVX}, {CXL}, nc, {R(f'RG.has({CXL}, s)', f'RG.sub({LVX}, {CXL})', proj(C2,3,'hp2'))}, XL.look_leaf({CXI}, k, nc, hc))
  +hjw = ME.subst(Array<U32>, zz => {T('KMd.off.port(d, KMd.word(AD.view(U32, zz), d, (nc + 1 : U32)), j)')}, RG.words({H2}), KMd.words({H2}), GP.rw_kw({H2}),
    fin_off(List.get(&2, U32, AD.view(U32, RG.words({H2})), AD.slot((nc + 1 : U32), d)), d, {FP1}, j, GP.fi_at({CXL}, AD.view(U32, RG.words({H2})), d, {FP1}, nc, hfi, hncL), hjf2))
  +hsk = sk.core({CORE_A}, hok, j, hj, hjM, hjh, hjf)
  %SPP.heta(SM.heap({SPL})) : {GK7('_')}
  %SPP.heta({H2}) : {GK7(HE, '_')}
  {trans('U32', [RDj(f'R.leave({H2E}, {PEXP(HE)}, nc)'), RDj(H2E), RDj(H2), RDj(H0t)],
    [f"GL.leave_keeps(KMd.words({H2}), KMd.vals({H2}), d, s, {CXI}, [], {CXL}, {CXF}, {Mp}, {PEXP(HE)}, nc, k, j, hf2, hd32, hNp, hBp, hp2, hc, hpo, hjMp, hjh2, hjp, hjw)",
     f"Equal.cong(P.H, U32, hh => {RDj('hh')}, {H2E}, {H2}, SPP.heta({H2}))",
     f"ME.subst(P.H, hh => {{{RDj(CR('hh'))} == {RDj(H0t)} : U32}}, SM.heap({SPL}), {HE}, Equal.sym(P.H, {HE}, SM.heap({SPL}), SPP.heta(SM.heap({SPL}))), hsk)"])}
'''
def GK7w(w,a,m):
    spl=SPLx(w,a,m); crh=f'R.crossings(cs, (SM.map({spl}), SM.heap({spl})), s)'
    return f"{{{RDj(f'R.leave(Pair.snd(Array<U32>, P.H, {crh}), (Pair.snd(Array<U32>, U32, Array.get(U32, Pair.fst(Array<U32>, P.H, {crh}), rn)) + rp : U32), nc)')} == {RDj(f'P.H{{KM.MG{{{w}}}, {a}}}')} : U32}}"
sec7+=f'''
def rk.go(-w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +ts: List<&2, T.TNode>, +ls: List<&2, T.TLink>, +by: U32, +ns: List<&2, U32>, +s: U32, +t: List<&2, U32>, +cs: List<&2, R.FzC>,
  +I: IM.Ix, +F: List<&2, U32>, +M: List<&2, U32>, +nc: U32, +k: U32, +rn: U32, +rp: U32, +j: U32, hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, hfm: {{AD.full(U32, map, dm) == True{{}} : Bool}}, +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}},
  +hN: {T(f'RG.layout({MN}, d)')}, +hB: {T(f'RG.bases({MN})')}, hp: {HPw('w')}, +hl: {{SM.made(ts) == List.length(&2, U32, ns) : Nat}}, +hpaMN: {T(f'KMd.past({MN}, d)')},
  +hhd: {T('KMd.off.words(KMd.hdr_words(), d, P.at_fh())')}, +hLd: {T(f'RG.distinct({L0})')}, +ht: {T('SM.tpl.ok(ls, ts, dm)')}, +hcp: {T('SV.copy.ok(cs, ls, ts, dm)')},
  hok: {T(f"RG.cxs.ok(cs, AD.view(U32, SM.map({SPLw2('w','a','map')})), dm, I, F)")}, +hc: {{IM.ix.look(I, k) == Some{{nc}} : Maybe<&2, U32>}}, +hu: {T('RG.far.off(cs, k)')}, +hro: {T('SV.root.ok(rn, rp, ts, dm, cs)')},
  +hj: {T('KMd.nodes.off(ns, d, j)')}, +hjM: {T('RG.off.nodes(M, d, j)')}, +hjh: {T('KMd.off.words(KMd.hdr_all(), d, j)')}, hjf: {T(f'RG.off.ports(RG.faced({L0}, AD.view(U32, w), d), d, j)')},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) -> {swap(GK7w('w','a','map'), OLDT('w','a','map'), NEWT('w','a','map'))}:
  (+t0, +ew) = mw
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, w, t0, d, ew, hf)
  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
  +hpT = LAB.subst(Array<U32>, qq => {HPw('qq')}, w, {T0}, Equal.sym(Array<U32>, {T0}, w, ew), hp)
  +hfrT = GP.faces_fresh({L0}, t0, d, {L0}, {MN}, ns, hft, hd32, {proj(C0,16,'hpT')}, sub_app_r(M, ns), none_appl(ns, F, {L0}, {proj(C0,11,'hpT')}), hN, hB)
  +hdy = dyn_of_bases(ns, GP.bases_sub(ns, {MN}, sub_app_r(M, ns), hB))
  +hjfT = LAB.subst(Array<U32>, qq => {T(f'RG.off.ports(RG.faced({L0}, AD.view(U32, qq), d), d, j)')}, w, {T0}, Equal.sym(Array<U32>, {T0}, w, ew), hjf)
  +hok1 = LAB.subst(Array<U32>, qq => {T(f"RG.cxs.ok(cs, AD.view(U32, SM.map({SPLw2('qq','a','map')})), dm, I, F)")}, w, {T0}, Equal.sym(Array<U32>, {T0}, w, ew), hok)
  +hok2 = LAB.subst(Array<V.Val>, qq => {T(f"RG.cxs.ok(cs, AD.view(U32, SM.map({SPLw2(T0,'qq','map')})), dm, I, F)")}, a, {TA}, Equal.sym(Array<V.Val>, {TA}, a, ea), hok1)
  +hok3 = LAB.subst(Array<U32>, qq => {T(f"RG.cxs.ok(cs, AD.view(U32, SM.map({SPLw2(T0,TA,'qq')})), dm, I, F)")}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hok2)
  %ew : {swap(GK7w('_','a','map'), OLDT('_','a','map'), NEWT('_','a','map'))}
  %ea : {swap(GK7w(T0,'_','map'), OLDT(T0,'_','map'), NEWT(T0,'_','map'))}
  %em : {swap(GK7w(T0,TA,'_'), OLDT(T0,TA,'_'), NEWT(T0,TA,'_'))}
  %Equal.sym(P.H, {NEWT(T0,TA,TM)}, {OLDT(T0,TA,TM)}, serve_true({SPLt}, cs, rn, rp, s, nc)) : {swap(GK7w(T0,TA,TM), OLDT(T0,TA,TM), '_')}
  rk.core({CORE_A.replace('hp, hl','hpT, hl').replace('hfr, hLd','hfrT, hLd')}, hok3, nc, k, hc, hu, rn, rp, hro, j, hj, hjM, hjh, hjfT)

def Laws.serve_root_keeps(w, a, map, d, dm, ts, ls, by, ns, s, t, cs, I, F, M, nc, k, rn, rp, j, hf, hd32, hfm, hdm, hN, hB, hp, hl, hpa, hhd, hLd, ht, hcp, hok, hc, hu, hro, hj, hjM, hjh, hjf):
  rk.go(w, a, map, d, dm, ts, ls, by, ns, s, t, cs, I, F, M, nc, k, rn, rp, j, hf, hd32, hfm, hdm, hN, hB, hp, hl, hpa, hhd, hLd, ht, hcp, hok, hc, hu, hro, hj, hjM, hjh, hjf, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))
'''
SRK_LAW=SRE_LAW.replace('law serve_ring_exact:','law serve_root_keeps:').replace('  for +rp: U32\n','  for +rp: U32\n  for +j: U32\n')
i=SRK_LAW.index('\n  {'); SRK_LAW=SRK_LAW[:i]+f'''
  for +hj: {{KMd.nodes.off(ns, d, j) == True{{}} : Bool}}
  for +hjM: {{RG.off.nodes(M, d, j) == True{{}} : Bool}}
  for +hjh: {{KMd.off.words(KMd.hdr_all(), d, j) == True{{}} : Bool}}
  for +hjf: {{RG.off.ports(RG.faced(Con{{s, t}}, AD.view(U32, w), d), d, j) == True{{}} : Bool}}
  {GK7w('w','a','map')}'''
if os.environ.get('CPI_PART')=='7':
    open('glam/proofgen/sv/cpi7.txt','w').write(sec7)
    open('glam/proofgen/sv/srk_law.txt','w').write(SRK_LAW)
    print('part7', len(sec7.splitlines()))
