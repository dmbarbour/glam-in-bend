# authoring aid: cursor_pend over the index (glam/PROOF.bend)
import re
p='glam/PROOF.bend'; s=open(p).read()
xp=open('glam/INDEX_PROOF.bend').read()
T=lambda h: f'{{{h} == True{{}} : Bool}}'
F_=lambda h: f'{{{h} == False{{}} : Bool}}'
FH='P.at_fh()'
SL=lambda a: f'AD.slot({a}, d)'
def P1(x,i): return x if i==0 else f'({x} + {i} : U32)'
AS=lambda A,j,v: f'Array.set(U32, {A}, {j}, {v})'
GET=lambda A,i: f'Pair.snd(Array<U32>, U32, Array.get(U32, {A}, {i}))'
WD=lambda A,i: f'KMd.word(AD.view(U32, {A}), d, {i})'
LS=lambda v,j,val: f'List.set(&2, U32, {v}, AD.slot({j}, d), {val})'
OW=lambda a,j: f'KMd.off.words(KMd.nw({a}), d, {j})'
RGOFF=lambda a,j: f'RG.off(RG.nw({a}), d, {j})'
def conj(terms):
    if len(terms)==1: return terms[0]
    return f'{terms[0]} && ({conj(terms[1:])})' if len(terms)>2 else f'{terms[0]} && {terms[1]}'
def proj(terms, n, h):
    e=h
    for m in range(n): e=f'and_r({terms[m]}, {conj(terms[m+1:])}, {e})'
    if n<len(terms)-1: e=f'and_l({terms[n]}, {conj(terms[n+1:])}, {e})'
    return e
def intro(terms, proofs):
    if len(terms)==1: return proofs[0]
    return f'and_intro({terms[0]}, {conj(terms[1:])}, {proofs[0]}, {intro(terms[1:], proofs[1:])})'
def OWt(b,j): return [f'Bool.not(Nat.is_eq({SL(P1(b,q))}, {SL(j)}))' for q in range(4)]+['True{}']
DISJ=lambda a,b: [OW(b,P1(a,i)) for i in range(4)]
SEP=lambda a,b: [f'IM.nd.disj(d, {a}, {b})', f'IM.nd.disj(d, {b}, {a})']
def disj_of_sep(a,b,h): return proj(SEP(a,b),0,h)
NDOK=lambda a: ['U32.is_eq(P.base('+a+'), '+a+')', f'IM.ws.apart(KMd.nw({a}), d)', OW(a,FH)]
def PXOK(v,I,ps,L,F,N):
    return [f'IM.ix.real({v}, d, s, {I})', f'IM.ix.inv({I})', f'IM.ix.lay({I}, s, d)', f'RG.sub(Con{{s, IM.ix.leaves({I})}}, {L})', f'RG.sub({ps}, {L})',
      f'RG.none.in({ps}, Con{{s, IM.ix.nodes({I})}})', f'RG.distinct({ps})', f'RG.none.in({L}, IM.ix.branches({I}))', f'KMd.chain({F}, {v}, d, KMd.word({v}, d, P.at_fh()))',
      f'RG.distinct({F})', f'RG.none.in({F}, Con{{s, IM.ix.nodes({I})}})', f'RG.none.in({F}, {L})', f'RG.sub({L}, {N})', f'RG.sub({F}, {N})', f'RG.sub(IM.ix.nodes({I}), {N})',
      f'RG.faces({L}, {v}, d, {L})', f'RG.px.off({L}, {v}, d, {L}, {N})', f'RG.px.tw({L}, {v}, d, {L})']
TRI=lambda v: [f'RG.faces(L, {v}, d, L)', f'RG.px.off(L, {v}, d, L, N)', f'RG.px.tw(L, {v}, d, L)']
out='''
# The pending placeholders over the index
# =======================================
#
# cells-freeze.sharing.cursors.index.ring.inv: the invariant RG.px.ok,
# every node a serve touches in one list N laid out once, apartness
# taken from it (XL.layout_ok, XL.layout_sep), roles by membership.

def and_intro(+p: Bool, +q: Bool, +hp: {p == True{} : Bool}, +hq: {q == True{} : Bool}) -> {Bool.and(p, q) == True{} : Bool}:
  XP.and_intro(p, q, hp, hq)

def and_l(+a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  XP.and_l(a, b, h)

def and_r(+a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  XP.and_r(a, b, h)

def not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  XP.not_true(b, h)

def neq_comm2(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  XP.neq_comm(a, b, h)

def has_head(+x: U32, +xs: List<&2, U32>) -> {RG.has(Con{x, xs}, x) == True{} : Bool}:
  has_self(x, xs)

def rw_kw(h: P.H) -> {RG.words(h) == KMd.words(h) : Array<U32>}:
  match h:
    case P.H{m, a}:
      match m:
        case KM.MG{w}:
          {==}

def branch_hd(+neg: Bool) -> {X.ix.branch(P.hd2(18, R.cur.form(neg), 0)) == False{} : Bool}:
  match neg:
    case True{}:
      {==}
    case False{}:
      {==}

def nf2(+b: Bool, +h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  not_t(b, h)

# x in L, b not: two nodes
def nhas.k(+e: Bool, +L: List<&2, U32>, +x: U32, +b: U32, +he: {U32.is_eq(x, b) == e : Bool}, +hx: {RG.has(L, x) == True{} : Bool}, +hb: {RG.has(L, b) == False{} : Bool}) ->
  {U32.is_eq(x, b) == False{} : Bool}:
  match e:
    case True{}:
      Empty.absurd({U32.is_eq(x, b) == False{} : Bool}, MB.true_ne_false()(Equal.trans(Bool, True{}, RG.has(L, b), False{},
        Equal.sym(Bool, RG.has(L, b), True{}, ME.subst(U32, z => {RG.has(L, z) == True{} : Bool}, x, b, MS.u32_eq_of_is_eq(x, b, he), hx)), hb)))
    case False{}:
      he

def nhas(+L: List<&2, U32>, +x: U32, +b: U32, +hx: {RG.has(L, x) == True{} : Bool}, +hb: {RG.has(L, b) == False{} : Bool}) -> {U32.is_eq(x, b) == False{} : Bool}:
  nhas.k(U32.is_eq(x, b), L, x, b, {==}, hx, hb)

def none_nil(L: List<&2, U32>) -> {RG.none.in(L, Nil{}) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      and_intro(Bool.not(RG.has(Nil{}, z)), RG.none.in(r, Nil{}), {==}, none_nil(r))
'''
out+=f'''
# none of L b, and none of it of X: none of it of b and X
def none_cons2(L: List<&2, U32>, +b: U32, +X: List<&2, U32>, +hn: {T('RG.none.in(L, X)')}, +hb: {F_('RG.has(L, b)')}) -> {T('RG.none.in(L, Con{b, X})')}:
  match L:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      and_intro(Bool.not(RG.has(Con{{b, X}}, z)), RG.none.in(r, Con{{b, X}}),
        not_t(RG.has(Con{{b, X}}, z), or_ff(U32.is_eq(b, z), RG.has(X, z), ueq_ne(z, b, or_false_l(U32.is_eq(z, b), RG.has(r, b), hb)),
          MB.eq_false_of_not_eq_true(RG.has(X, z), and_l(Bool.not(RG.has(X, z)), RG.none.in(r, X), hn)))),
        none_cons2(r, b, X, and_r(Bool.not(RG.has(X, z)), RG.none.in(r, X), hn), or_false_r(U32.is_eq(z, b), RG.has(r, b), hb)))

# none of ps s nor of X, nor x nor b: none of them
def none_ext(ps: List<&2, U32>, +s: U32, +x: U32, +b: U32, +X: List<&2, U32>, +hn: {T('RG.none.in(ps, Con{s, X})')}, +hx: {F_('RG.has(ps, x)')}, +hb: {F_('RG.has(ps, b)')}) ->
  {T('RG.none.in(ps, Con{s, Con{x, Con{b, X}}})')}:
  match ps:
    case Nil{{}}:
      {{==}}
    case Con{{+q, +r}}:
      +hq = MB.eq_false_of_not_eq_true(RG.has(Con{{s, X}}, q), and_l(Bool.not(RG.has(Con{{s, X}}, q)), RG.none.in(r, Con{{s, X}}), hn))
      and_intro(Bool.not(RG.has(Con{{s, Con{{x, Con{{b, X}}}}}}, q)), RG.none.in(r, Con{{s, Con{{x, Con{{b, X}}}}}}),
        not_t(RG.has(Con{{s, Con{{x, Con{{b, X}}}}}}, q), or_ff(U32.is_eq(s, q), RG.has(Con{{x, Con{{b, X}}}}, q), or_false_l(U32.is_eq(s, q), RG.has(X, q), hq),
          or_ff(U32.is_eq(x, q), RG.has(Con{{b, X}}, q), ueq_ne(q, x, or_false_l(U32.is_eq(q, x), RG.has(r, x), hx)),
            or_ff(U32.is_eq(b, q), RG.has(X, q), ueq_ne(q, b, or_false_l(U32.is_eq(q, b), RG.has(r, b), hb)), or_false_r(U32.is_eq(s, q), RG.has(X, q), hq))))),
        none_ext(r, s, x, b, X, and_r(Bool.not(RG.has(Con{{s, X}}, q)), RG.none.in(r, Con{{s, X}}), hn), or_false_r(U32.is_eq(q, x), RG.has(r, x), hx), or_false_r(U32.is_eq(q, b), RG.has(r, b), hb)))
'''
NODES=lambda t: f'IM.tr.nodes({t})'; BRS=lambda t: f'IM.tr.branches({t})'
AP=lambda a,b: f'List.append(&2, U32, {a}, {b})'
out+=f'''
# a tree of N's nodes and a node n of N not of the tree: n apart from it
def offn_of(t: IM.Tr, +N: List<&2, U32>, +d: Nat, +n: U32, +hN: {T('RG.layout(N, d)')}, +hs: {T(f"RG.sub({NODES('t')}, N)")}, +hn: {T('RG.has(N, n)')},
  +hno: {F_(f"RG.has({NODES('t')}, n)")}) -> {T('IM.tr.offn(t, d, n)')}:
  match t:
    case IM.Lf{{+y, +ky}}:
      XL.layout_sep(N, d, y, n, hN, and_l(RG.has(N, y), RG.sub(Nil{{}}, N), hs), hn, or_false_l(U32.is_eq(y, n), RG.has(Nil{{}}, n), hno))
    case IM.Br{{+b, +i, +l, +r}}:
      +hsa = and_r(RG.has(N, b), RG.sub({AP(NODES('l'),NODES('r'))}, N), hs)
      +hor = Equal.trans(Bool, Bool.or(RG.has({NODES('l')}, n), RG.has({NODES('r')}, n)), RG.has({AP(NODES('l'),NODES('r'))}, n), False{{}},
        Equal.sym(Bool, RG.has({AP(NODES('l'),NODES('r'))}, n), Bool.or(RG.has({NODES('l')}, n), RG.has({NODES('r')}, n)), XP.has_app({NODES('l')}, {NODES('r')}, n)),
        or_false_r(U32.is_eq(b, n), RG.has({AP(NODES('l'),NODES('r'))}, n), hno))
      and_intro(IM.nd.sep(d, b, n), IM.tr.offn(l, d, n) && IM.tr.offn(r, d, n),
        XL.layout_sep(N, d, b, n, hN, and_l(RG.has(N, b), RG.sub({AP(NODES('l'),NODES('r'))}, N), hs), hn, or_false_l(U32.is_eq(b, n), RG.has({AP(NODES('l'),NODES('r'))}, n), hno)),
        and_intro(IM.tr.offn(l, d, n), IM.tr.offn(r, d, n),
          offn_of(l, N, d, n, hN, XP.sub_app_l({NODES('l')}, {NODES('r')}, N, hsa), hn, or_false_l(RG.has({NODES('l')}, n), RG.has({NODES('r')}, n), hor)),
          offn_of(r, N, d, n, hN, XP.sub_app_r({NODES('l')}, {NODES('r')}, N, hsa), hn, or_false_r(RG.has({NODES('l')}, n), RG.has({NODES('r')}, n), hor))))

# a node m of N no branch of a tree of N's nodes: its word 1 off the branches'
def offb_of(t: IM.Tr, +N: List<&2, U32>, +d: Nat, +m: U32, +hN: {T('RG.layout(N, d)')}, +hs: {T(f"RG.sub({NODES('t')}, N)")}, +hm: {T('RG.has(N, m)')},
  +hnb: {F_(f"RG.has({BRS('t')}, m)")}) -> {T('IM.tr.offb(t, d, (m + 1 : U32))')}:
  match t:
    case IM.Lf{{+y, +ky}}:
      {{==}}
    case IM.Br{{+b, +i, +l, +r}}:
      +hsa = and_r(RG.has(N, b), RG.sub({AP(NODES('l'),NODES('r'))}, N), hs)
      +hor = Equal.trans(Bool, Bool.or(RG.has({BRS('l')}, m), RG.has({BRS('r')}, m)), RG.has({AP(BRS('l'),BRS('r'))}, m), False{{}},
        Equal.sym(Bool, RG.has({AP(BRS('l'),BRS('r'))}, m), Bool.or(RG.has({BRS('l')}, m), RG.has({BRS('r')}, m)), XP.has_app({BRS('l')}, {BRS('r')}, m)),
        or_false_r(U32.is_eq(b, m), RG.has({AP(BRS('l'),BRS('r'))}, m), hnb))
      +D = lay_pair(N, d, m, b, hN, hm, and_l(RG.has(N, b), RG.sub({AP(NODES('l'),NODES('r'))}, N), hs), ueq_ne(b, m, or_false_l(U32.is_eq(b, m), RG.has({AP(BRS('l'),BRS('r'))}, m), hnb)))
      and_intro({OW('b','(m + 1 : U32)')}, IM.tr.offb(l, d, (m + 1 : U32)) && IM.tr.offb(r, d, (m + 1 : U32)), {proj(DISJ('m','b'),1,'D')},
        and_intro(IM.tr.offb(l, d, (m + 1 : U32)), IM.tr.offb(r, d, (m + 1 : U32)),
          offb_of(l, N, d, m, hN, XP.sub_app_l({NODES('l')}, {NODES('r')}, N, hsa), hm, or_false_l(RG.has({BRS('l')}, m), RG.has({BRS('r')}, m), hor)),
          offb_of(r, N, d, m, hN, XP.sub_app_r({NODES('l')}, {NODES('r')}, N, hsa), hm, or_false_r(RG.has({BRS('l')}, m), RG.has({BRS('r')}, m), hor))))

def flok_of(F: List<&2, U32>, +N: List<&2, U32>, +d: Nat, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, +hs: {T('RG.sub(F, N)')}) -> {T('IM.fl.ok(F, d)')}:
  match F:
    case Nil{{}}:
      {{==}}
    case Con{{+n, +r}}:
      and_intro(IM.nd.ok(n, d), IM.fl.ok(r, d), XL.layout_ok(N, d, n, hN, hB, and_l(RG.has(N, n), RG.sub(r, N), hs)), flok_of(r, N, d, hN, hB, and_r(RG.has(N, n), RG.sub(r, N), hs)))

def flsep_of(F: List<&2, U32>, +N: List<&2, U32>, +d: Nat, +a: U32, +hN: {T('RG.layout(N, d)')}, +hs: {T('RG.sub(F, N)')}, +ha: {T('RG.has(N, a)')}, +hna: {F_('RG.has(F, a)')}) ->
  {T('IM.fl.sep(F, d, a)')}:
  match F:
    case Nil{{}}:
      {{==}}
    case Con{{+n, +r}}:
      and_intro(IM.nd.sep(d, a, n), IM.fl.sep(r, d, a),
        XL.layout_sep(N, d, a, n, hN, ha, and_l(RG.has(N, n), RG.sub(r, N), hs), ueq_ne(n, a, or_false_l(U32.is_eq(n, a), RG.has(r, a), hna))),
        flsep_of(r, N, d, a, hN, and_r(RG.has(N, n), RG.sub(r, N), hs), ha, or_false_r(U32.is_eq(n, a), RG.has(r, a), hna)))

def offt_of(F: List<&2, U32>, +t: IM.Tr, +N: List<&2, U32>, +d: Nat, +hN: {T('RG.layout(N, d)')}, +hs: {T('RG.sub(F, N)')}, +hst: {T(f"RG.sub({NODES('t')}, N)")},
  +hn: {T(f"RG.none.in(F, {NODES('t')})")}) -> {T('IM.fl.offt(F, t, d)')}:
  match F:
    case Nil{{}}:
      {{==}}
    case Con{{+n, +r}}:
      and_intro(IM.tr.offn(t, d, n), IM.fl.offt(r, t, d),
        offn_of(t, N, d, n, hN, hst, and_l(RG.has(N, n), RG.sub(r, N), hs), MB.eq_false_of_not_eq_true(RG.has({NODES('t')}, n), and_l(Bool.not(RG.has({NODES('t')}, n)), RG.none.in(r, {NODES('t')}), hn))),
        offt_of(r, t, N, d, hN, and_r(RG.has(N, n), RG.sub(r, N), hs), hst, and_r(Bool.not(RG.has({NODES('t')}, n)), RG.none.in(r, {NODES('t')}), hn)))
'''
for i in (0,2):
    xi=P1('x',i)
    out+=f'''
# word {i} of a node of N none of ys's, of N: off their words
def nodesoff_of{i}(ys: List<&2, U32>, +N: List<&2, U32>, +d: Nat, +x: U32, +hN: {T('RG.layout(N, d)')}, +hs: {T('RG.sub(ys, N)')}, +hx: {T('RG.has(N, x)')}, +hxn: {F_('RG.has(ys, x)')}) ->
  {T(f'KMd.nodes.off(ys, d, {xi})')}:
  match ys:
    case Nil{{}}:
      {{==}}
    case Con{{+n, +r}}:
      +D = lay_pair(N, d, x, n, hN, hx, and_l(RG.has(N, n), RG.sub(r, N), hs), ueq_ne(n, x, or_false_l(U32.is_eq(n, x), RG.has(r, x), hxn)))
      and_intro({OW('n',xi)}, KMd.nodes.off(r, d, {xi}), {proj(DISJ('x','n'),i,'D')},
        nodesoff_of{i}(r, N, d, x, hN, and_r(RG.has(N, n), RG.sub(r, N), hs), hx, or_false_r(U32.is_eq(n, x), RG.has(r, x), hxn)))
'''
ONE=lambda i: f'Bool.not(Nat.is_eq(AD.slot({i}, d), AD.slot((m + 1 : U32), d)))'
out+=f'''
# the head off the words 1 of nodes laid out
def ones_fh(L: List<&2, U32>, +N: List<&2, U32>, +d: Nat, +hs: {T('RG.sub(L, N)')}, +hN: {T('RG.layout(N, d)')}) -> {T('ones(L, d, P.at_fh())')}:
  match L:
    case Nil{{}}:
      {{==}}
    case Con{{+m, +r}}:
      and_intro({ONE(FH)}, ones(r, d, P.at_fh()), nf2(Nat.is_eq(AD.slot(P.at_fh(), d), AD.slot((m + 1 : U32), d)), XP.off1(m, d, P.at_fh(), lay_head(N, d, m, hN, and_l(RG.has(N, m), RG.sub(r, N), hs)))),
        ones_fh(r, N, d, and_r(RG.has(N, m), RG.sub(r, N), hs), hN))
'''
for i in range(4):
    bi=P1('b',i)
    out+=f'''
# a node b of N none of L's: its word {i} off their words 1
def ones_b{i}(L: List<&2, U32>, +N: List<&2, U32>, +d: Nat, +b: U32, +hs: {T('RG.sub(L, N)')}, +hN: {T('RG.layout(N, d)')}, +hbN: {T('RG.has(N, b)')}, +hbL: {F_('RG.has(L, b)')}) ->
  {T(f'ones(L, d, {bi})')}:
  match L:
    case Nil{{}}:
      {{==}}
    case Con{{+m, +r}}:
      +D = lay_pair(N, d, m, b, hN, and_l(RG.has(N, m), RG.sub(r, N), hs), hbN, or_false_l(U32.is_eq(m, b), RG.has(r, b), hbL))
      and_intro({ONE(bi)}, ones(r, d, {bi}), nf2(Nat.is_eq(AD.slot({bi}, d), AD.slot((m + 1 : U32), d)), neq_comm2(AD.slot((m + 1 : U32), d), AD.slot({bi}, d), XP.off{i}(b, d, (m + 1 : U32), {proj(DISJ('m','b'),1,'D')}))),
        ones_b{i}(r, N, d, b, and_r(RG.has(N, m), RG.sub(r, N), hs), hN, hbN, or_false_r(U32.is_eq(m, b), RG.has(r, b), hbL)))
'''
PLO='XP.plc.lo(IM.tr.plc(t, c, k, (s + 3 : U32)))'
SELF_S=f'lay_self(N, d, s, hN, hsN)'
out+=f'''
# a node m of N's word 1 off the situating node's word 3
def m13.k(+e: Bool, +m: U32, +s: U32, +N: List<&2, U32>, +d: Nat, +he: {{U32.is_eq(m, s) == e : Bool}}, +hN: {T('RG.layout(N, d)')}, +hmN: {T('RG.has(N, m)')}, +hsN: {T('RG.has(N, s)')}) ->
  {{Nat.is_eq(AD.slot((m + 1 : U32), d), AD.slot((s + 3 : U32), d)) == False{{}} : Bool}}:
  match e:
    case True{{}}:
      %Equal.sym(U32, m, s, MS.u32_eq_of_is_eq(m, s, he)) : {{Nat.is_eq(AD.slot((_ + 1 : U32), d), AD.slot((s + 3 : U32), d)) == False{{}} : Bool}}
      neq_comm2(AD.slot((s + 3 : U32), d), AD.slot((s + 1 : U32), d), not_true(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((s + 1 : U32), d)),
        and_l(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((s + 1 : U32), d))), True{{}}, and_r(Bool.not(Nat.is_eq(AD.slot((s + 2 : U32), d), AD.slot((s + 1 : U32), d))), RG.off([(s + 3 : U32)], d, (s + 1 : U32)),
          and_l(RG.off([(s + 2 : U32), (s + 3 : U32)], d, (s + 1 : U32)), RG.apartw([(s + 2 : U32), (s + 3 : U32)], d), and_r(RG.off([(s + 1 : U32), (s + 2 : U32), (s + 3 : U32)], d, s), RG.apartw([(s + 1 : U32), (s + 2 : U32), (s + 3 : U32)], d), {SELF_S}))))))
    case False{{}}:
      XP.off3(s, d, (m + 1 : U32), {proj(DISJ('m','s'),1,'lay_pair(N, d, m, s, hN, hmN, hsN, he)')})

# the word an insert writes its new branch's pointer at off the live nodes' words 1
def ones_plo(L: List<&2, U32>, +N: List<&2, U32>, +d: Nat, +t: IM.Tr, +c: Nat, +k: U32, +s: U32, +hs: {T('RG.sub(L, N)')}, +hN: {T('RG.layout(N, d)')}, +hsN: {T('RG.has(N, s)')},
  +htN: {T(f"RG.sub({NODES('t')}, N)")}, +hLb: {T(f"RG.none.in(L, {BRS('t')})")}) -> {T(f'ones(L, d, {PLO})')}:
  match L:
    case Nil{{}}:
      {{==}}
    case Con{{+m, +r}}:
      +hmN = and_l(RG.has(N, m), RG.sub(r, N), hs)
      and_intro({ONE(PLO)}, ones(r, d, {PLO}), nf2(Nat.is_eq(AD.slot({PLO}, d), AD.slot((m + 1 : U32), d)), neq_comm2(AD.slot((m + 1 : U32), d), AD.slot({PLO}, d),
        XP.plc2b(t, c, k, (s + 3 : U32), d, (m + 1 : U32), offb_of(t, N, d, m, hN, htN, hmN, MB.eq_false_of_not_eq_true(RG.has({BRS('t')}, m), and_l(Bool.not(RG.has({BRS('t')}, m)), RG.none.in(r, {BRS('t')}), hLb))),
          m13.k(U32.is_eq(m, s), m, s, N, d, {{==}}, hN, hmN, hsN)))),
        ones_plo(r, N, d, t, c, k, s, and_r(RG.has(N, m), RG.sub(r, N), hs), hN, hsN, htN, and_r(Bool.not(RG.has({BRS('t')}, m)), RG.none.in(r, {BRS('t')}), hLb)))
'''
# frame lemmas
VJ=LS('v','j','val')
ONEJ=lambda z: f'Bool.not(Nat.is_eq(AD.slot(j, d), AD.slot(({z} + 1 : U32), d)))'
WL=lambda z,h: f'XP.wl_ne(v, d, j, ({z} + 1 : U32), val, not_true(Nat.is_eq(AD.slot(j, d), AD.slot(({z} + 1 : U32), d)), {h}))'
out+=f'''
# a write off the live nodes' words 1 keeps what they face
def px_off_keep(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +L: List<&2, U32>, +N: List<&2, U32>, +j: U32, +val: U32,
  +h: {T('RG.px.off(ys, v, d, L, N)')}, +ho: {T('ones(ys, d, j)')}) -> {T(f'RG.px.off(ys, {VJ}, d, L, N)')}:
  match ys:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      %{WL('z', f"and_l({ONEJ('z')}, ones(r, d, j), ho)")} : {T(f'RG.po.all(_, L, d, N) && RG.px.off(r, {VJ}, d, L, N)')}
      and_intro(RG.po.all(KMd.word(v, d, (z + 1 : U32)), L, d, N), RG.px.off(r, {VJ}, d, L, N), and_l(RG.po.all(KMd.word(v, d, (z + 1 : U32)), L, d, N), RG.px.off(r, v, d, L, N), h),
        px_off_keep(r, v, d, L, N, j, val, and_r(RG.po.all(KMd.word(v, d, (z + 1 : U32)), L, d, N), RG.px.off(r, v, d, L, N), h), and_r({ONEJ('z')}, ones(r, d, j), ho)))

def tw_q_keep(Q: List<&2, U32>, +r0: U32, +z: U32, +v: List<&2, U32>, +d: Nat, +j: U32, +val: U32,
  +h: {T('RG.tw.q(Q, r0, z, v, d)')}, +ho: {T('ones(Q, d, j)')}) -> {T(f'RG.tw.q(Q, r0, z, {VJ}, d)')}:
  match Q:
    case Nil{{}}:
      {{==}}
    case Con{{+q, +t}}:
      %{WL('q', f"and_l({ONEJ('q')}, ones(t, d, j), ho)")} : {T(f'Bool.or(KMd.off.port(d, r0, (q + 1 : U32)), Bool.not(KMd.off.port(d, _, (z + 1 : U32)))) && RG.tw.q(t, r0, z, {VJ}, d)')}
      and_intro(Bool.or(KMd.off.port(d, r0, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, (q + 1 : U32)), (z + 1 : U32)))), RG.tw.q(t, r0, z, {VJ}, d),
        and_l(Bool.or(KMd.off.port(d, r0, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, (q + 1 : U32)), (z + 1 : U32)))), RG.tw.q(t, r0, z, v, d), h),
        tw_q_keep(t, r0, z, v, d, j, val, and_r(Bool.or(KMd.off.port(d, r0, (q + 1 : U32)), Bool.not(KMd.off.port(d, KMd.word(v, d, (q + 1 : U32)), (z + 1 : U32)))), RG.tw.q(t, r0, z, v, d), h), and_r({ONEJ('q')}, ones(t, d, j), ho)))
'''
WZ='KMd.word(v, d, (z + 1 : U32))'
TWR=f'RG.tw.q(L, {WZ}, z, v, d) && RG.px.tw(r, v, d, L)'
NSZ=lambda X: f'KMd.off.port(d, {X}, (z + 1 : U32))'
out+=f'''
def px_tw_keep(ys: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +L: List<&2, U32>, +j: U32, +val: U32,
  +h: {T('RG.px.tw(ys, v, d, L)')}, +ho: {T('ones(ys, d, j)')}, +hoL: {T('ones(L, d, j)')}) -> {T(f'RG.px.tw(ys, {VJ}, d, L)')}:
  match ys:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      %{WL('z', f"and_l({ONEJ('z')}, ones(r, d, j), ho)")} : {T(f'{NSZ("_")} && (RG.tw.q(L, _, z, {VJ}, d) && RG.px.tw(r, {VJ}, d, L))')}
      and_intro({NSZ(WZ)}, RG.tw.q(L, {WZ}, z, {VJ}, d) && RG.px.tw(r, {VJ}, d, L), and_l({NSZ(WZ)}, {TWR}, h),
        and_intro(RG.tw.q(L, {WZ}, z, {VJ}, d), RG.px.tw(r, {VJ}, d, L),
          tw_q_keep(L, {WZ}, z, v, d, j, val, and_l(RG.tw.q(L, {WZ}, z, v, d), RG.px.tw(r, v, d, L), and_r({NSZ(WZ)}, {TWR}, h)), hoL),
          px_tw_keep(r, v, d, L, j, val, and_r(RG.tw.q(L, {WZ}, z, v, d), RG.px.tw(r, v, d, L), and_r({NSZ(WZ)}, {TWR}, h)), and_r({ONEJ('z')}, ones(r, d, j), ho), hoL)))

# the three facing clauses kept by such a write
def fr3(+L: List<&2, U32>, +v: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +j: U32, +val: U32, +h: {T(conj(TRI('v')))}, +ho: {T('ones(L, d, j)')}) -> {T(conj(TRI(VJ)))}:
  and_intro(RG.faces(L, {VJ}, d, L), {conj(TRI(VJ)[1:])}, faces_keep(L, v, d, L, j, val, {proj(TRI('v'),0,'h')}, ho),
    and_intro(RG.px.off(L, {VJ}, d, L, N), RG.px.tw(L, {VJ}, d, L), px_off_keep(L, v, d, L, N, j, val, {proj(TRI('v'),1,'h')}, ho), px_tw_keep(L, v, d, L, j, val, {proj(TRI('v'),2,'h')}, ho, ho)))
'''
def frstep(Aprev, j, val, fprev, cprev, hones):
    v=f'AD.view(U32, {Aprev})'
    return (f"ME.subst(List<&2, U32>, z => {T(conj(TRI('z')))}, {LS(v,j,val)}, AD.view(U32, {AS(Aprev,j,val)}), "
      f"Equal.sym(List<&2, U32>, AD.view(U32, {AS(Aprev,j,val)}), {LS(v,j,val)}, LA.set_view(U32, {Aprev}, d, {j}, {val}, {fprev}, hd32)), "
      f"fr3(L, {v}, d, N, {j}, {val}, {cprev}, {hones}))")
def sfull(A,i,v,hf): return f'LA.set_full(U32, {A}, d, {i}, {v}, {hf})'
def gso(A,i,j,v,hf,hij): return f'LA.get_set_other(U32, {A}, d, {i}, {j}, {v}, {hf}, hd32, {hij})'
def gss(A,i,v): return f'LA.get_set_same(U32, {A}, {i}, {v})'
def trans(Ty, pts, prfs):
    if len(prfs)==1: return prfs[0]
    return f'Equal.trans({Ty}, {pts[0]}, {pts[1]}, {pts[-1]}, {prfs[0]}, {trans(Ty, pts[1:], prfs[1:])})'

# the two cases
HD='P.hd2(18, R.cur.form(neg), 0)'
A0='LAT.fromT(U32, t0)'; A1=AS(A0,'x',HD); A2=AS(A1,'(x + 2 : U32)','src')
f1=sfull(A0,'x',HD,'hft'); f2=sfull(A1,'(x + 2 : U32)','src',f1)
V0=f'AD.view(U32, {A0})'
INS=lambda w: f'X.ix.insert(P.H{{KM.MG{{{w}}}, a}}, s, x)'
V3=lambda w: f'AD.view(U32, KMd.words({INS(w)}))'
CASE_LETS={}
def case(has):
    I0='IM.Has{t}' if has else 'IM.Ept{}'
    F0='Con{b, F}' if has else 'F'
    bE='b' if has else 's'
    I1=f'IM.ix.put({I0}, x, src, b)'
    nm='cpx.has' if has else 'cpx.ept'
    tparam='+t: IM.Tr, ' if has else ''
    targ='t, ' if has else ''
    C0=PXOK(V0,I0,'Con{x, ps}','L',F0,'N')
    H=[f'hp{i}' for i in range(18)]
    lets=''.join(f'  +{H[i]} = {proj(C0,i,"hp")}\n' for i in range(18))
    NOD=f'IM.ix.nodes({I0})'; BR=f'IM.ix.branches({I0})'; LV=f'IM.ix.leaves({I0})'
    L=f'''  +hsL = and_l(RG.has(L, s), RG.sub({LV}, L), hp3)
  +hlL = and_r(RG.has(L, s), RG.sub({LV}, L), hp3)
  +hxL = and_l(RG.has(L, x), RG.sub(ps, L), hp4)
  +hps = and_r(RG.has(L, x), RG.sub(ps, L), hp4)
  +hxo = MB.eq_false_of_not_eq_true(RG.has(Con{{s, {NOD}}}, x), and_l(Bool.not(RG.has(Con{{s, {NOD}}}, x)), RG.none.in(ps, Con{{s, {NOD}}}), hp5))
  +hpsn = and_r(Bool.not(RG.has(Con{{s, {NOD}}}, x)), RG.none.in(ps, Con{{s, {NOD}}}), hp5)
  +hxs = ueq_ne(s, x, or_false_l(U32.is_eq(s, x), RG.has({NOD}, x), hxo))
  +hxt = or_false_r(U32.is_eq(s, x), RG.has({NOD}, x), hxo)
  +hxps = MB.eq_false_of_not_eq_true(RG.has(ps, x), and_l(Bool.not(RG.has(ps, x)), RG.distinct(ps), hp6))
  +hpsd = and_r(Bool.not(RG.has(ps, x)), RG.distinct(ps), hp6)
  +hsN = sub_has(L, N, s, hp12, hsL)
  +hxN = sub_has(L, N, x, hp12, hxL)
  +hokx = XL.layout_ok(N, d, x, hN, hB, hxN)
  +hoks = XL.layout_ok(N, d, s, hN, hB, hsN)
  +hsxs = XL.layout_sep(N, d, x, s, hN, hxN, hsN, hxs)
  +hsps = none_has(ps, Con{{s, {NOD}}}, s, hpsn, has_head(s, {NOD}))
'''
    if has:
        L+=f'''  +hbo = MB.eq_false_of_not_eq_true(RG.has(Con{{s, {NOD}}}, b), and_l(Bool.not(RG.has(Con{{s, {NOD}}}, b)), RG.none.in(F, Con{{s, {NOD}}}), hp10))
  +hfnr = and_r(Bool.not(RG.has(Con{{s, {NOD}}}, b)), RG.none.in(F, Con{{s, {NOD}}}), hp10)
  +hbs = ueq_ne(s, b, or_false_l(U32.is_eq(s, b), RG.has({NOD}, b), hbo))
  +hbt = or_false_r(U32.is_eq(s, b), RG.has({NOD}, b), hbo)
  +hbF = MB.eq_false_of_not_eq_true(RG.has(F, b), and_l(Bool.not(RG.has(F, b)), RG.distinct(F), hp9))
  +hFd = and_r(Bool.not(RG.has(F, b)), RG.distinct(F), hp9)
  +hbL = MB.eq_false_of_not_eq_true(RG.has(L, b), and_l(Bool.not(RG.has(L, b)), RG.none.in(F, L), hp11))
  +hFL = and_r(Bool.not(RG.has(L, b)), RG.none.in(F, L), hp11)
  +hbN = and_l(RG.has(N, b), RG.sub(F, N), hp13)
  +hFN = and_r(RG.has(N, b), RG.sub(F, N), hp13)
  +hxb = nhas(L, x, b, hxL, hbL)
  +hokb = XL.layout_ok(N, d, b, hN, hB, hbN)
  +hsxb = XL.layout_sep(N, d, x, b, hN, hxN, hbN, hxb)
  +hsbs = XL.layout_sep(N, d, b, s, hN, hbN, hsN, hbs)
  +hlayt = and_r(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hp2))
  +hofs = and_l(IM.tr.offn(t, d, s), IM.tr.lay(t, d), and_r(IM.nd.ok(s, d), IM.tr.offn(t, d, s) && IM.tr.lay(t, d), hp2))
  +hofx = offn_of(t, N, d, x, hN, hp14, hxN, hxt)
  +hofb = offn_of(t, N, d, b, hN, hp14, hbN, hbt)
  +hbps = notin_sub(ps, L, b, hps, hbL)
'''
        FR=['IM.nd.ok(x, d)','IM.nd.ok(b, d)','IM.nd.sep(d, x, b)','IM.nd.sep(d, x, s)','IM.nd.sep(d, b, s)','IM.tr.offn(t, d, x)','IM.tr.offn(t, d, b)']
        L+=f'  +hfr = {intro(FR,["hokx","hokb","hsxb","hsxs","hsbs","hofx","hofb"])}\n'
    else:
        L+=f'''  +hfnr = hp10
  +hFd = hp9
  +hFL = hp11
  +hFN = hp13
  +hfr = and_intro(IM.nd.ok(x, d), IM.nd.sep(d, x, s), hokx, hsxs)
'''
    L+=f'''  +hsF = none_has(F, Con{{s, {NOD}}}, s, hfnr, has_head(s, {NOD}))
  +hxF = none_has(F, L, x, hFL, hxL)
'''
    # offall for x and x+2
    D_xs=f'and_l(IM.nd.disj(d, x, s), IM.nd.disj(d, s, x), hsxs)'
    s3x=lambda i: proj(OWt('s',P1('x',i)),3,proj(DISJ('x','s'),i,D_xs))
    if has:
        oa=lambda i: f'and_intro(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot({P1("x",i)}, d))), IM.tr.off(t, d, {P1("x",i)}), {s3x(i)}, {proj(["IM.tr.off(t, d, x)","IM.tr.off(t, d, (x + 1 : U32))","IM.tr.off(t, d, (x + 2 : U32))","IM.tr.off(t, d, (x + 3 : U32))"],i,"XP.onw(t, d, x, hofx)")})'
    else:
        oa=lambda i: s3x(i)
    Ft=F0
    hFtx=f'none_has({Ft}, L, x, hp11, hxL)'
    okx3=proj(NDOK('x'),2,'hokx')
    xfh=lambda i: f'not_true(Nat.is_eq(AD.slot({P1("x",i)}, d), AD.slot(P.at_fh(), d)), {proj(OWt("x",FH),i,okx3)})'
    hk2=trans('U32',[WD(A2,'(x + 2 : U32)'),GET(A2,'(x + 2 : U32)'),'src'],[f'XP.wg({A2}, d, (x + 2 : U32), {f2}, hd32)', gss(A1,'(x + 2 : U32)','src')])
    apx=proj(NDOK('x'),1,'hokx')
    x2x=f'not_true(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(x, d)), and_l(Bool.not(Nat.is_eq(AD.slot((x + 2 : U32), d), AD.slot(x, d))), RG.off([(x + 3 : U32)], d, x), and_r(Bool.not(Nat.is_eq(AD.slot((x + 1 : U32), d), AD.slot(x, d))), RG.off([(x + 2 : U32), (x + 3 : U32)], d, x), and_l(RG.off([(x + 1 : U32), (x + 2 : U32), (x + 3 : U32)], d, x), RG.apartw([(x + 1 : U32), (x + 2 : U32), (x + 3 : U32)], d), {apx}))))'
    hx2w=trans('U32',[WD(A2,'x'),GET(A2,'x'),GET(A1,'x'),HD],[f'XP.wg({A2}, d, x, {f2}, hd32)', gso(A1,'(x + 2 : U32)','x','src',f1,x2x), gss(A0,'x',HD)])
    TR0=intro(TRI(V0),['hp15','hp16','hp17'])
    tr1=frstep(A0,'x',HD,'hft',TR0,'ones_p0(L, N, d, x, hp12, hN, hxN)')
    tr2=frstep(A1,'(x + 2 : U32)','src',f1,tr1,'ones_p2(L, N, d, x, hp12, hN, hxN)')
    L+=f'''  +hre2 = XL.real_kept({A1}, a, d, s, {I0}, (x + 2 : U32), src, {f1}, hd32, {oa(2)}, XL.real_kept({A0}, a, d, s, {I0}, x, {HD}, hft, hd32, {oa(0)}, hp0))
  +hch2 = XL.chain_kept({A1}, a, d, (x + 2 : U32), src, {Ft}, {f1}, hd32, {xfh(2)}, nodesoff_of2({Ft}, N, d, x, hN, hp13, hxN, {hFtx}),
    XL.chain_kept({A0}, a, d, x, {HD}, {Ft}, hft, hd32, {xfh(0)}, nodesoff_of0({Ft}, N, d, x, hN, hp13, hxN, {hFtx}), hp8))
  +hk2 = {hk2}
  +hnb2 = ME.subst(U32, z => {{X.ix.branch(z) == False{{}} : Bool}}, {HD}, {WD(A2,'x')}, Equal.sym(U32, {WD(A2,'x')}, {HD}, {hx2w}), branch_hd(neg))
  +htr2 = {tr2}
'''
    CASE_LETS[has]=(lets, L)
    nm2=nm+'2'
    goal=lambda v,I: T('(' + conj(PXOK(v,I,'ps','L','F','N')) + ') && AD.full(U32, ' + v[len('AD.view(U32, '):-1] + ', d)')
    G0=goal(f'AD.view(U32, RG.words(R.cursor(P.H{{KM.MG{{{A0}}}, a}}, s, x, src, neg)))', I1)
    vparams=f'+hlL: {T("RG.sub("+LV+", L)")}, +hps: {T("RG.sub(ps, L)")}, +hpsn: {T("RG.none.in(ps, Con{s, "+NOD+"})")}, +hxps: {F_("RG.has(ps, x)")}, +hpsd: {T("RG.distinct(ps)")}, +hsps: {F_("RG.has(ps, s)")}'
    vargs='hlL, hps, hpsn, hxps, hpsd, hsps'
    if has:
        vparams+=f', +hbps: {F_("RG.has(ps, b)")}, +hbF: {F_("RG.has(F, b)")}, +hbL: {F_("RG.has(L, b)")}, +hbN: {T("RG.has(N, b)")}, +hlayt: {T("IM.tr.lay(t, d)")}, +hofs: {T("IM.tr.offn(t, d, s)")}'
        vargs+=', hbps, hbF, hbL, hbN, hlayt, hofs'
    vparams+=f', +hsL: {T("RG.has(L, s)")}, +hxL: {T("RG.has(L, x)")}, +hsN: {T("RG.has(N, s)")}, +hxN: {T("RG.has(N, x)")}, +hoks: {T("IM.nd.ok(s, d)")}, +hokx: {T("IM.nd.ok(x, d)")}, +hsxs: {T("IM.nd.sep(d, x, s)")}'
    vargs+=', hsL, hxL, hsN, hxN, hoks, hokx, hsxs'
    vparams+=f', +hfnr: {T("RG.none.in(F, Con{s, "+NOD+"})")}, +hFd: {T("RG.distinct(F)")}, +hFL: {T("RG.none.in(F, L)")}, +hFN: {T("RG.sub(F, N)")}, +hsF: {F_("RG.has(F, s)")}, +hxF: {F_("RG.has(F, x)")}'
    vargs+=', hfnr, hFd, hFL, hFN, hsF, hxF'
    FRx=('IM.ix.fresh('+I0+', s, x, b, d)') if has else ('IM.ix.fresh('+I0+', s, x, s, d)')
    vparams+=f', +hfr: {T(FRx)}, +hinv: {T("IM.ix.inv("+I0+")")}, +hlay: {T("IM.ix.lay("+I0+", s, d)")}, +hbr: {T("RG.none.in(L, "+BR+")")}, +hLN: {T("RG.sub(L, N)")}, +hIN: {T("RG.sub("+NOD+", N)")}'
    vargs+=', hfr, hp1, hp2, hp7, hp12, hp14'
    W2='LAT.fromT(U32, t2)'
    sub2=lambda q_t, h: f'LAB.subst(Array<U32>, q => {q_t}, w2, {W2}, ew2, {h})'
    p2=f'''
def {nm2}({tparam}-w2: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +b: U32,
  hf2: {{AD.full(U32, w2, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, +ha: {{IM.ix.look({I0}, src) == None{{}} : Maybe<&2, U32>}},
  {vparams},
  hre2: {T(f'IM.ix.real(AD.view(U32, w2), d, s, {I0})')}, hch2: {T(f'KMd.chain({F0}, AD.view(U32, w2), d, KMd.word(AD.view(U32, w2), d, P.at_fh()))')},
  hk2: {{KMd.word(AD.view(U32, w2), d, (x + 2 : U32)) == src : U32}}, hnb2: {{X.ix.branch(KMd.word(AD.view(U32, w2), d, x)) == False{{}} : Bool}},
  htr2: {T(conj(TRI('AD.view(U32, w2)')))}, m2: LAT.Mirror(U32, w2)) -> {goal(V3('w2'),I1)}:
  (+t2, +e2) = m2
  +hft2 = LAP.full_t(U32, w2, t2, d, e2, hf2)
  +ew2 = Equal.sym(Array<U32>, {W2}, w2, e2)
  +hreT = {sub2(T(f'IM.ix.real(AD.view(U32, q), d, s, {I0})'),'hre2')}
  +hchT = {sub2(T(f'KMd.chain({F0}, AD.view(U32, q), d, KMd.word(AD.view(U32, q), d, P.at_fh()))'),'hch2')}
  +hkT = {sub2('{KMd.word(AD.view(U32, q), d, (x + 2 : U32)) == src : U32}','hk2')}
  +hnbT = {sub2('{X.ix.branch(KMd.word(AD.view(U32, q), d, x)) == False{} : Bool}','hnb2')}
  +htrT = {sub2(T(conj(TRI('AD.view(U32, q)'))),'htr2')}
  %e2 : {goal(V3('_'),I1)}
'''
    WW=WD(W2,FH)
    if has:
        RESTC=f'U32.is_eq(KMd.at_idx({WW}), b) && KMd.chain(F, AD.view(U32, {W2}), d, KMd.word(AD.view(U32, {W2}), d, (b + 1 : U32)))'
        p2+=f'''  +hroom = and_intro(Bool.not(U32.is_eq({WW}, 0)), Bool.and(U32.is_eq(KMd.at_idx({WW}), b), True{{}}), and_l(Bool.not(U32.is_eq({WW}, 0)), {RESTC}, hchT),
    and_intro(U32.is_eq(KMd.at_idx({WW}), b), True{{}}, and_l(U32.is_eq(KMd.at_idx({WW}), b), KMd.chain(F, AD.view(U32, {W2}), d, KMd.word(AD.view(U32, {W2}), d, (b + 1 : U32))), and_r(Bool.not(U32.is_eq({WW}, 0)), {RESTC}, hchT)), {{==}}))
'''
        room='hroom'
    else:
        room='{==}'
    p2+=f'''  +hre3 = XL.insert_tree({W2}, a, d, s, {I0}, x, src, {bE}, hft2, hd32, hreT, hinv, hlay, hfr, {room}, hkT, hnbT, ha)
  +hFok = flok_of(F, N, d, hN, hB, hFN)
  +hFsep = {('and_intro(IM.fl.sep(F, d, s), IM.fl.offt(F, t, d), flsep_of(F, N, d, s, hN, hFN, hsN, hsF), offt_of(F, t, N, d, hN, hFN, hIN, none_sub(F, Con{s, IM.tr.nodes(t)}, IM.tr.nodes(t), hfnr, sub_cons_r(IM.tr.nodes(t), s, IM.tr.nodes(t), sub_refl(IM.tr.nodes(t))))))') if has else 'flsep_of(F, N, d, s, hN, hFN, hsN, hsF)'}
  +hch3 = XL.insert_free({W2}, a, d, s, {I0}, x, src, {bE}, F, hft2, hd32, hreT, hinv, hlay, hfr, hkT, hnbT, ha, hFok, hFsep, flsep_of(F, N, d, x, hN, hFN, hxN, hxF), {('flsep_of(F, N, d, b, hN, hFN, hbN, hbF)') if has else 'flsep_of(F, N, d, s, hN, hFN, hsN, hsF)'}, hchT)
'''
    # the insert's writes, the frame through them
    if has:
        i=xp.index('def ins.heap.has('); j=xp.index(':\n',xp.index('->',i)); sig=xp[i:j]
        k_=sig.rindex('== P.H{KM.MG{'); A7H=sig[k_+len('== P.H{KM.MG{'):]; A7H=A7H[:A7H.rindex('}, a} : P.H}')]
        A7H=re.sub(r'(?<![A-Za-z0-9_.])(plc\.(?:lo|cu))\(', r'XP.\1(', A7H).replace('LAT.fromT(U32, t0)', W2).replace('IM.tr.near(T, k)','IM.tr.near(t, src)').replace('X.ix.diff(k, ','X.ix.diff(src, ').replace('X.ix.side(k, ','X.ix.side(src, ').replace('IM.tr.plc(T, ','IM.tr.plc(t, ').replace(', k, (s + 3 : U32))',', src, (s + 3 : U32))')
        C='IM.cr.i(X.ix.diff(src, IM.tr.near(t, src)))'
        HDb=f'X.ix.hd({C})'
        V3b=f'X.ix.pick(X.ix.side(src, {C}), x, XP.plc.cu(IM.tr.plc(t, {C}, src, (s + 3 : U32))))'
        V2b=f'X.ix.pick(X.ix.side(src, {C}), XP.plc.cu(IM.tr.plc(t, {C}, src, (s + 3 : U32))), x)'
        PLOt=f'XP.plc.lo(IM.tr.plc(t, {C}, src, (s + 3 : U32)))'
        W=[(FH,GET(W2,'(b + 1 : U32)'),'ones_fh(L, N, d, hLN, hN)'),('b',HDb,'ones_b0(L, N, d, b, hLN, hN, hbN, hbL)'),('(b + 3 : U32)',V3b,'ones_b3(L, N, d, b, hLN, hN, hbN, hbL)'),
           ('(b + 1 : U32)','P.era()','ones_b1(L, N, d, b, hLN, hN, hbN, hbL)'),('(b + 2 : U32)',V2b,'ones_b2(L, N, d, b, hLN, hN, hbN, hbL)'),
           (PLOt,'b',f'ones_plo(L, N, d, t, {C}, src, s, hLN, hN, hsN, hIN, hbr)'),('(x + 3 : U32)','s','ones_p3(L, N, d, x, hLN, hN, hxN)')]
        EQ=f'XP.ins.heap.has(t, t2, a, d, s, x, src, b, hft2, hd32, hreT, hinv, hoks, hofs, hlayt, hfr, hroom, hkT, hnbT, ha)'
    else:
        A7H=AS(AS(W2,'(s + 3 : U32)','x'),'(x + 3 : U32)','s')
        W=[('(s + 3 : U32)','x','ones_p3(L, N, d, s, hLN, hN, hsN)'),('(x + 3 : U32)','s','ones_p3(L, N, d, x, hLN, hN, hxN)')]
        EQ=f'XP.ins.heap.ept(t2, a, d, s, x, src, hft2, hd32, hreT, hokx, hsxs, hkT, hnbT)'
    arrs=[W2]; fulls=['hft2']
    for (jj,v,_) in W:
        arrs.append(AS(arrs[-1],jj,v)); fulls.append(sfull(arrs[-2],jj,v,fulls[-1]))
    assert arrs[-1]==A7H, (arrs[-1][:300], A7H[:300])
    tr='htrT'
    for m,(jj,v,ho) in enumerate(W):
        tr=frstep(arrs[m],jj,v,fulls[m],tr,ho)
    p2+=f'''  +htr7 = {tr}
  +htr3 = ME.subst(P.H, h => {T(conj(TRI('AD.view(U32, KMd.words(h))')))}, P.H{{KM.MG{{{A7H}}}, a}}, {INS(W2)}, Equal.sym(P.H, {INS(W2)}, P.H{{KM.MG{{{A7H}}}, a}}, {EQ}), htr7)
'''
    M=f'Con{{s, Con{{x, Con{{{bE}, {NOD}}}}}}}'
    hsubM=f'sub_cons_r({NOD}, s, Con{{x, Con{{{bE}, {NOD}}}}}, sub_cons_r({NOD}, x, Con{{{bE}, {NOD}}}, sub_cons_r({NOD}, {bE}, {NOD}, sub_refl({NOD}))))'
    hMx=f'has_cons(s, Con{{x, Con{{{bE}, {NOD}}}}}, x, has_head(x, Con{{{bE}, {NOD}}}))'
    hMb=f'has_cons(s, Con{{x, Con{{{bE}, {NOD}}}}}, {bE}, has_cons(x, Con{{{bE}, {NOD}}}, {bE}, has_head({bE}, {NOD})))'
    NOD1=f'IM.ix.nodes({I1})'
    p2+=f'''  +hsub1 = and_intro(RG.has({M}, s), RG.sub({NOD1}, {M}), has_head(s, Con{{x, Con{{{bE}, {NOD}}}}}), XL.put_sub({I0}, x, src, {bE}, {M}, {hsubM}, {hMx}, {hMb}))
'''
    BR1=f'IM.ix.branches({I1})'
    if has:
        c8=f'none_sub(L, Con{{b, {BR}}}, {BR1}, none_cons2(L, b, {BR}, hbr, hbL), XL.put_bsub({I0}, x, src, b, Con{{b, {BR}}}, sub_cons_r({BR}, b, {BR}, sub_refl({BR})), has_head(b, {BR})))'
    else:
        c8='none_nil(L)'
    V3W=V3(W2)
    C1=PXOK(V3W,I1,'ps','L','F','N')
    proofs=['hre3', f'XL.put_inv({I0}, x, src, {bE}, hinv, ha)', f'XL.put_lay({I0}, s, x, src, {bE}, d, hlay, hfr)',
      f'and_intro(RG.has(L, s), RG.sub(IM.ix.leaves({I1}), L), hsL, XL.put_lsub({I0}, x, src, {bE}, L, hlL, hxL))', 'hps',
      f'none_sub(ps, {M}, Con{{s, {NOD1}}}, none_ext(ps, s, x, {bE}, {NOD}, hpsn, hxps, {"hbps" if has else "hsps"}), hsub1)', 'hpsd', c8, 'hch3', 'hFd',
      f'none_sub(F, {M}, Con{{s, {NOD1}}}, none_ext(F, s, x, {bE}, {NOD}, hfnr, hxF, {"hbF" if has else "hsF"}), hsub1)', 'hFL', 'hLN', 'hFN',
      f'XL.put_sub({I0}, x, src, {bE}, N, hIN, hxN, {"hbN" if has else "hsN"})',
      proj(TRI(V3W),0,'htr3'), proj(TRI(V3W),1,'htr3'), proj(TRI(V3W),2,'htr3')]
    p2+=f'  and_intro({conj(C1)}, AD.full(U32, KMd.words({INS(W2)}), d), {intro(C1,proofs)}, XL.insert_full({W2}, a, d, s, {I0}, x, src, {bE}, hft2, hd32, hreT, hinv, hlay, hfr, {room}, hkT, hnbT, ha))\n'
    p1=f'''
def {nm}({tparam}+t0: LAT.Tree<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +b: U32,
  +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  +hp: {T(conj(C0))}, +ha: {{IM.ix.look({I0}, src) == None{{}} : Maybe<&2, U32>}}) -> {G0}:
{lets}{L}  %Equal.sym(Array<U32>, RG.words(R.cursor(P.H{{KM.MG{{{A0}}}, a}}, s, x, src, neg)), KMd.words(R.cursor(P.H{{KM.MG{{{A0}}}, a}}, s, x, src, neg)), rw_kw(R.cursor(P.H{{KM.MG{{{A0}}}, a}}, s, x, src, neg))) :
    {goal('AD.view(U32, _)',I1)}
  {nm2}({targ}{A2}, ta, d, s, ps, L, F, N, x, src, neg, b, {f2}, hd32, hN, hB, ha, {vargs}, hre2, hch2, hk2, hnb2, htr2, LAT.mirror(U32, {A2}))
'''
    return p2+p1
AA='LAT.fromT(V.Val, ta)'
def ta_of(txt):
    txt=txt.replace('-a: Array<V.Val>','+ta: LAT.Tree<V.Val>')
    return re.sub(r'(?<=, )a(?=[,}])', AA, txt)
out+=ta_of(case(False)+case(True))
out=re.sub(r'(?<!case )Nil\{\}', '[]', out)
CK=lambda I,F: conj(PXOK('AD.view(U32, LAT.fromT(U32, t0))',I,'Con{x, ps}','L',F,'N'))
out+=f'''
def cpx.k(I: IM.Ix, +t0: LAT.Tree<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +b: U32,
  +hft: {{AD.full(U32, {A0}, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  +hp: {T(f'RG.px.ok(AD.view(U32, {A0}), d, s, I, Con{{x, ps}}, L, IM.ix.take(I, b, F), N)')}, +ha: {{IM.ix.look(I, src) == None{{}} : Maybe<&2, U32>}}) ->
  {T(f'RG.px.ok(AD.view(U32, RG.words(R.cursor(P.H{{KM.MG{{{A0}}}, LAT.fromT(V.Val, ta)}}, s, x, src, neg))), d, s, IM.ix.put(I, x, src, b), ps, L, F, N) && AD.full(U32, RG.words(R.cursor(P.H{{KM.MG{{{A0}}}, LAT.fromT(V.Val, ta)}}, s, x, src, neg)), d)')}:
  match I:
    case IM.Ept{{}}:
      cpx.ept(t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, ha)
    case IM.Has{{+t}}:
      cpx.has(t, t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, hp, ha)

def cpx.m(-w: Array<U32>, -a: Array<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +ps: List<&2, U32>, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +x: U32, +src: U32, +neg: Bool, +b: U32,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')},
  hp: {T('RG.px.ok(AD.view(U32, w), d, s, I, Con{x, ps}, L, IM.ix.take(I, b, F), N)')}, +ha: {{IM.ix.look(I, src) == None{{}} : Maybe<&2, U32>}}, m: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a)) ->
  {T('RG.px.ok(AD.view(U32, RG.words(R.cursor(P.H{KM.MG{w}, a}, s, x, src, neg))), d, s, IM.ix.put(I, x, src, b), ps, L, F, N)')}:
  (+t0, +e) = m
  (+ta, +ea) = ma
  +hft = LAP.full_t(U32, w, t0, d, e, hf)
  +ew = Equal.sym(Array<U32>, LAT.fromT(U32, t0), w, e)
  %e : {T('RG.px.ok(AD.view(U32, RG.words(R.cursor(P.H{KM.MG{_}, a}, s, x, src, neg))), d, s, IM.ix.put(I, x, src, b), ps, L, F, N)')}
  %ea : {T('RG.px.ok(AD.view(U32, RG.words(R.cursor(P.H{KM.MG{LAT.fromT(U32, t0)}, _}, s, x, src, neg))), d, s, IM.ix.put(I, x, src, b), ps, L, F, N)')}
  and_l(RG.px.ok(AD.view(U32, RG.words(R.cursor(P.H{{KM.MG{{{A0}}}, LAT.fromT(V.Val, ta)}}, s, x, src, neg))), d, s, IM.ix.put(I, x, src, b), ps, L, F, N), AD.full(U32, RG.words(R.cursor(P.H{{KM.MG{{{A0}}}, LAT.fromT(V.Val, ta)}}, s, x, src, neg)), d),
    cpx.k(I, t0, ta, d, s, ps, L, F, N, x, src, neg, b, hft, hd32, hN, hB, LAB.subst(Array<U32>, q => {T('RG.px.ok(AD.view(U32, q), d, s, I, Con{x, ps}, L, IM.ix.take(I, b, F), N)')}, w, LAT.fromT(U32, t0), ew, hp), ha))
'''
# the law's proof replaced
i=s.index('def Laws.cursor_pend('); j=s.index('\n\n',i)
s=s[:i]+s[j+2:]
out+='''
def Laws.cursor_pend(w, a, d, s, I, ps, L, F, N, x, src, neg, b, hf, hd32, hN, hB, hp, ha):
  cpx.m(w, a, d, s, I, ps, L, F, N, x, src, neg, b, hf, hd32, hN, hB, hp, ha, LAT.mirror(U32, w), LAT.mirror(V.Val, a))
'''
for imp in ['import ./index_model.bend as IM','import ./INDEX_LAWS.bend as XL','import ./INDEX_PROOF.bend as XP','import ./index.bend as X']:
    if imp not in s:
        s=s.replace('import ./witness.bend as WB\n', 'import ./witness.bend as WB\n'+imp+'\n',1)
out=re.sub(r'(?<!case )Nil\{\}', '[]', out)
s=s.rstrip('\n')+'\n'+out
open(p,'w').write(s)
print('ok', len(out.splitlines()))
