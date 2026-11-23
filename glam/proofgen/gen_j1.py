# authoring aid: join1_pend over the index (glam/PROOF.bend)
import re
p='glam/PROOF.bend'
s=open('glam/proofgen/PROOF.before_j1.bend').read()
xp=open('glam/INDEX_PROOF.bend').read()
T=lambda h: f'{{{h} == True{{}} : Bool}}'
F_=lambda h: f'{{{h} == False{{}} : Bool}}'
NE=lambda a,b: F_(f'U32.is_eq({a}, {b})')
FH='P.at_fh()'
def P1(x,i): return x if i==0 else f'({x} + {i} : U32)'
SL=lambda a: f'AD.slot({a}, d)'
AS=lambda A,j,v: f'Array.set(U32, {A}, {j}, {v})'
GET=lambda A,i: f'Pair.snd(Array<U32>, U32, Array.get(U32, {A}, {i}))'
WD=lambda v,i: f'KMd.word({v}, d, {i})'
LS=lambda v,j,val: f'List.set(&2, U32, {v}, AD.slot({j}, d), {val})'
OW=lambda a,j: f'KMd.off.words(KMd.nw({a}), d, {j})'
OP=lambda r,j: f'KMd.off.port(d, {r}, {j})'
def conj(t):
    return t[0] if len(t)==1 else (f'{t[0]} && ({conj(t[1:])})' if len(t)>2 else f'{t[0]} && {t[1]}')
def proj(t, n, h):
    e=h
    for m in range(n): e=f'and_r({t[m]}, {conj(t[m+1:])}, {e})'
    if n<len(t)-1: e=f'and_l({t[n]}, {conj(t[n+1:])}, {e})'
    return e
def intro(terms, proofs):
    if len(terms)==1: return proofs[0]
    return f'and_intro({terms[0]}, {conj(terms[1:])}, {proofs[0]}, {intro(terms[1:], proofs[1:])})'
def trans(Ty, pts, prfs):
    if len(prfs)==1: return prfs[0]
    return f'Equal.trans({Ty}, {pts[0]}, {pts[1]}, {pts[-1]}, {prfs[0]}, {trans(Ty, pts[1:], prfs[1:])})'
def sfull(A,i,v,hf): return f'LA.set_full(U32, {A}, d, {i}, {v}, {hf})'
def PXOK(v,I,ps,L,F,N):
    return [f'IM.ix.real({v}, d, s, {I})', f'IM.ix.inv({I})', f'IM.ix.lay({I}, s, d)', f'RG.sub(Con{{s, IM.ix.leaves({I})}}, {L})', f'RG.sub({ps}, {L})',
      f'RG.none.in({ps}, Con{{s, IM.ix.nodes({I})}})', f'RG.distinct({ps})', f'RG.none.in({L}, IM.ix.branches({I}))', f'KMd.chain({F}, {v}, d, KMd.word({v}, d, P.at_fh()))',
      f'RG.distinct({F})', f'RG.none.in({F}, Con{{s, IM.ix.nodes({I})}})', f'RG.none.in({F}, {L})', f'RG.sub({L}, {N})', f'RG.sub({F}, {N})', f'RG.sub(IM.ix.nodes({I}), {N})',
      f'RG.faces({L}, {v}, d, {L})', f'RG.px.off({L}, {v}, d, {L}, {N})', f'RG.px.tw({L}, {v}, d, {L})']
L2='RG.without(RG.without(L, x), y)'
TRI=lambda v: [f'RG.faces({L2}, {v}, d, {L2})', f'RG.px.off({L2}, {v}, d, {L2}, N)', f'RG.px.tw({L2}, {v}, d, {L2})']
def frstep(Aprev, j, val, fprev, cprev, hones):
    v=f'AD.view(U32, {Aprev})'
    return (f"ME.subst(List<&2, U32>, z => {T(conj(TRI('z')))}, {LS(v,j,val)}, AD.view(U32, {AS(Aprev,j,val)}), "
      f"Equal.sym(List<&2, U32>, AD.view(U32, {AS(Aprev,j,val)}), {LS(v,j,val)}, LA.set_view(U32, {Aprev}, d, {j}, {val}, {fprev}, hd32)), "
      f"fr3({L2}, {v}, d, N, {j}, {val}, {cprev}, {hones}))")
out='''
# The pending placeholders over the index: a join
# ===============================================
'''
# ---- generic list lemmas ----
AP=lambda a,b: f'List.append(&2, U32, {a}, {b})'
out+=f'''
def sub_appl(xs: List<&2, U32>, +ys: List<&2, U32>) -> {T(f"RG.sub(xs, {AP('xs','ys')})")}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +t}}:
      and_intro(RG.has(Con{{z, {AP('t','ys')}}}, z), RG.sub(t, Con{{z, {AP('t','ys')}}}), has_head(z, {AP('t','ys')}), sub_cons_r(t, z, {AP('t','ys')}, sub_appl(t, ys)))

def sub_appr(xs: List<&2, U32>, +ys: List<&2, U32>) -> {T(f"RG.sub(ys, {AP('xs','ys')})")}:
  match xs:
    case Nil{{}}:
      sub_refl(ys)
    case Con{{+z, +t}}:
      sub_cons_r(ys, z, {AP('t','ys')}, sub_appr(t, ys))

# none of L the head of a list none of L's
def none_head(L: List<&2, U32>, +b: U32, +X: List<&2, U32>, +h: {T('RG.none.in(L, Con{b, X})')}) -> {F_('RG.has(L, b)')}:
  match L:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      +hz = MB.eq_false_of_not_eq_true(RG.has(Con{{b, X}}, z), and_l(Bool.not(RG.has(Con{{b, X}}, z)), RG.none.in(r, Con{{b, X}}), h))
      or_ff(U32.is_eq(z, b), RG.has(r, b), ueq_ne(b, z, or_false_l(U32.is_eq(b, z), RG.has(X, z), hz)), none_head(r, b, X, and_r(Bool.not(RG.has(Con{{b, X}}, z)), RG.none.in(r, Con{{b, X}}), h)))

# a list's members each x, y, or of L without both
def sub_back.k(+ex: Bool, +ey: Bool, +z: U32, +L: List<&2, U32>, +x: U32, +y: U32, +hex: {{U32.is_eq(x, z) == ex : Bool}}, +hey: {{U32.is_eq(y, z) == ey : Bool}}, +hz: {T('RG.has(L, z)')}) ->
  {T(f'RG.has(Con{{x, Con{{y, {L2}}}}}, z)')}:
  match ex:
    case True{{}}:
      %Equal.sym(Bool, U32.is_eq(x, z), True{{}}, hex) : {T(f'Bool.or(_, RG.has(Con{{y, {L2}}}, z))')}
      {{==}}
    case False{{}}:
      match ey:
        case True{{}}:
          has_cons(x, Con{{y, {L2}}}, z, ME.subst(Bool, q => {T(f'Bool.or(q, RG.has({L2}, z))')}, True{{}}, U32.is_eq(y, z), Equal.sym(Bool, U32.is_eq(y, z), True{{}}, hey), {{==}}))
        case False{{}}:
          has_cons(x, Con{{y, {L2}}}, z, has_cons(y, {L2}, z, has_without(RG.without(L, x), y, z, hey, has_without(L, x, z, hex, hz))))

def sub_back(K: List<&2, U32>, +L: List<&2, U32>, +x: U32, +y: U32, +hK: {T('RG.sub(K, L)')}) -> {T(f'RG.sub(K, Con{{x, Con{{y, {L2}}}}})')}:
  match K:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      and_intro(RG.has(Con{{x, Con{{y, {L2}}}}}, z), RG.sub(r, Con{{x, Con{{y, {L2}}}}}), sub_back.k(U32.is_eq(x, z), U32.is_eq(y, z), z, L, x, y, {{==}}, {{==}}, and_l(RG.has(L, z), RG.sub(r, L), hK)),
        sub_back(r, L, x, y, and_r(RG.has(L, z), RG.sub(r, L), hK)))

# none of a part of L none of M's, nor of a part of M
def none_subl(K: List<&2, U32>, +L: List<&2, U32>, +M: List<&2, U32>, +hs: {T('RG.sub(K, L)')}, +hn: {T('RG.none.in(L, M)')}) -> {T('RG.none.in(K, M)')}:
  match K:
    case Nil{{}}:
      {{==}}
    case Con{{+z, +r}}:
      and_intro(Bool.not(RG.has(M, z)), RG.none.in(r, M), nf2(RG.has(M, z), none_mem(L, M, z, hn, and_l(RG.has(L, z), RG.sub(r, L), hs))), none_subl(r, L, M, and_r(RG.has(L, z), RG.sub(r, L), hs), hn))

def none_mem.k(+e: Bool, +y: U32, +t: List<&2, U32>, +M: List<&2, U32>, +z: U32, +he: {{U32.is_eq(y, z) == e : Bool}}, +hn: {T('RG.none.in(Con{y, t}, M)')}, +hz: {T('Bool.or(U32.is_eq(y, z), RG.has(t, z))')},
  ih: {T('RG.has(t, z)')} -> {F_('RG.has(M, z)')}) -> {F_('RG.has(M, z)')}:
  match e:
    case True{{}}:
      %MS.u32_eq_of_is_eq(y, z, he) : {F_('RG.has(M, _)')}
      MB.eq_false_of_not_eq_true(RG.has(M, y), and_l(Bool.not(RG.has(M, y)), RG.none.in(t, M), hn))
    case False{{}}:
      ih(XP.ort_r(U32.is_eq(y, z), RG.has(t, z), he, hz))

def none_mem(L: List<&2, U32>, +M: List<&2, U32>, +z: U32, +hn: {T('RG.none.in(L, M)')}, +hz: {T('RG.has(L, z)')}) -> {F_('RG.has(M, z)')}:
  match L:
    case Nil{{}}:
      Empty.absurd({F_('RG.has(M, z)')}, MB.false_ne_true()(hz))
    case Con{{+y, +t}}:
      none_mem.k(U32.is_eq(y, z), y, t, M, z, {{==}}, hn, hz, hzt => none_mem(t, M, z, and_r(Bool.not(RG.has(M, y)), RG.none.in(t, M), hn), hzt))

# the leaves of a tree among its nodes
def leaf_node(t: IM.Tr, +z: U32, +h: {T('RG.has(IM.tr.leaves(t), z)')}) -> {T('RG.has(IM.tr.nodes(t), z)')}:
  match t:
    case IM.Lf{{+y, +ky}}:
      h
    case IM.Br{{+b, +i, +l, +r}}:
      has_cons(b, {AP('IM.tr.nodes(l)','IM.tr.nodes(r)')}, z, ln.k(RG.has(IM.tr.leaves(l), z), l, r, z, {{==}},
        Equal.trans(Bool, Bool.or(RG.has(IM.tr.leaves(l), z), RG.has(IM.tr.leaves(r), z)), RG.has({AP('IM.tr.leaves(l)','IM.tr.leaves(r)')}, z), True{{}},
          Equal.sym(Bool, RG.has({AP('IM.tr.leaves(l)','IM.tr.leaves(r)')}, z), Bool.or(RG.has(IM.tr.leaves(l), z), RG.has(IM.tr.leaves(r), z)), XP.has_app(IM.tr.leaves(l), IM.tr.leaves(r), z)), h),
        hl => leaf_node(l, z, hl), hr => leaf_node(r, z, hr)))

def ln.k(+e: Bool, +l: IM.Tr, +r: IM.Tr, +z: U32, +he: {{RG.has(IM.tr.leaves(l), z) == e : Bool}}, +h: {T('Bool.or(RG.has(IM.tr.leaves(l), z), RG.has(IM.tr.leaves(r), z))')},
  ihl: {T('RG.has(IM.tr.leaves(l), z)')} -> {T('RG.has(IM.tr.nodes(l), z)')}, ihr: {T('RG.has(IM.tr.leaves(r), z)')} -> {T('RG.has(IM.tr.nodes(r), z)')}) ->
  {T(f"RG.has({AP('IM.tr.nodes(l)','IM.tr.nodes(r)')}, z)")}:
  match e:
    case True{{}}:
      XP.has_app_l(IM.tr.nodes(l), IM.tr.nodes(r), z, ihl(he))
    case False{{}}:
      XP.has_app_r(IM.tr.nodes(l), IM.tr.nodes(r), z, ihr(XP.ort_r(RG.has(IM.tr.leaves(l), z), RG.has(IM.tr.leaves(r), z), he, h)))
'''
# order: none_mem.k, none_mem before none_subl; ln.k before leaf_node
def mv(o, first, before):
    i=o.index(first); j=o.index('\ndef ', i+5) if '\ndef ' in o[i+5:] else len(o)
    blk=o[i:j]; o=o[:i]+o[j:]
    k=o.index(before); return o[:k]+blk+'\n'+o[k:]
out=mv(out,'def none_mem.k(','def none_subl(')
out=mv(out,'def none_mem(L:','def none_subl(')
out=mv(out,'def ln.k(','def leaf_node(')
# ---- po facts ----
PN=lambda r,n: f'RG.po.n({r}, L, d, {n})'
W3=lambda r,n: f"{OP(r,f'({n} + 1 : U32)')} && ({OP(r,f'({n} + 2 : U32)')} && {OP(r,f'({n} + 3 : U32)')})"
out+=f'''
# what the port r a live node faces asks of a tracked node n
def po_at.k(+e: Bool, +m: U32, +t: List<&2, U32>, +r: U32, +L: List<&2, U32>, +d: Nat, +n: U32, +he: {{U32.is_eq(m, n) == e : Bool}},
  +h: {T('RG.po.all(r, L, d, Con{m, t})')}, +hn: {T('Bool.or(U32.is_eq(m, n), RG.has(t, n))')}, ih: {T('RG.has(t, n)')} -> {T(PN('r','n'))}) -> {T(PN('r','n'))}:
  match e:
    case True{{}}:
      %MS.u32_eq_of_is_eq(m, n, he) : {T(PN('r','_'))}
      and_l({PN('r','m')}, RG.po.all(r, L, d, t), h)
    case False{{}}:
      ih(XP.ort_r(U32.is_eq(m, n), RG.has(t, n), he, hn))

def po_at(N: List<&2, U32>, +r: U32, +L: List<&2, U32>, +d: Nat, +n: U32, +h: {T('RG.po.all(r, L, d, N)')}, +hn: {T('RG.has(N, n)')}) -> {T(PN('r','n'))}:
  match N:
    case Nil{{}}:
      Empty.absurd({T(PN('r','n'))}, MB.false_ne_true()(hn))
    case Con{{+m, +t}}:
      po_at.k(U32.is_eq(m, n), m, t, r, L, d, n, {{==}}, h, hn, hnt => po_at(t, r, L, d, n, and_r({PN('r','m')}, RG.po.all(r, L, d, t), h), hnt))

def po_fh(N: List<&2, U32>, +r: U32, +L: List<&2, U32>, +d: Nat, +h: {T('RG.po.all(r, L, d, N)')}) -> {T(OP('r','P.at_fh()'))}:
  match N:
    case Nil{{}}:
      h
    case Con{{+m, +t}}:
      po_fh(t, r, L, d, and_r({PN('r','m')}, RG.po.all(r, L, d, t), h))

# a non-static port's off.port as its link word, r + 1, off j
def opf(+r: U32, +d: Nat, +j: U32, +hst: {{P.is_static(r) == False{{}} : Bool}}, +h: {T(OP('r','j'))}) -> {F_('Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(j, d))')}:
  not_true(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(j, d)), ME.subst(Bool, q => {T('KMd.off.lw(KMd.lw.k(q, r), d, j)')}, P.is_static(r), False{{}}, hst, h))

# flipped, as KMd.off.words reads it
def opw(+r: U32, +d: Nat, +j: U32, +hst: {{P.is_static(r) == False{{}} : Bool}}, +h: {T(OP('r','j'))}) -> {T('Bool.not(Nat.is_eq(AD.slot(j, d), AD.slot((r + 1 : U32), d)))')}:
  nf2(Nat.is_eq(AD.slot(j, d), AD.slot((r + 1 : U32), d)), neq_comm2(AD.slot((r + 1 : U32), d), AD.slot(j, d), opf(r, d, j, hst, h)))

# a node n of N not live: r's link word off its four words
def ow_po(+r: U32, +L: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +n: U32, +hst: {{P.is_static(r) == False{{}} : Bool}}, +hpo: {T('RG.po.all(r, L, d, N)')},
  +hn: {T('RG.has(N, n)')}, +hnl: {F_('RG.has(L, n)')}) -> {T(OW('n','(r + 1 : U32)'))}:
  +hp = po_at(N, r, L, d, n, hpo, hn)
  +hw = ME.subst(Bool, q => {T(f"Bool.or(q, {W3('r','n')})")}, RG.has(L, n), False{{}}, hnl, and_r({OP('r','n')}, Bool.or(RG.has(L, n), {W3('r','n')}), hp))
  and_intro(Bool.not(Nat.is_eq(AD.slot(n, d), AD.slot((r + 1 : U32), d))), {conj([f"Bool.not(Nat.is_eq(AD.slot({P1('n',i)}, d), AD.slot((r + 1 : U32), d)))" for i in (1,2,3)]+['True{}'])},
    opw(r, d, n, hst, and_l({OP('r','n')}, Bool.or(RG.has(L, n), {W3('r','n')}), hp)),
    and_intro(Bool.not(Nat.is_eq(AD.slot((n + 1 : U32), d), AD.slot((r + 1 : U32), d))), {conj([f"Bool.not(Nat.is_eq(AD.slot({P1('n',i)}, d), AD.slot((r + 1 : U32), d)))" for i in (2,3)]+['True{}'])},
      opw(r, d, (n + 1 : U32), hst, and_l({OP('r','(n + 1 : U32)')}, {OP('r','(n + 2 : U32)')} && {OP('r','(n + 3 : U32)')}, hw)),
      and_intro(Bool.not(Nat.is_eq(AD.slot((n + 2 : U32), d), AD.slot((r + 1 : U32), d))), {conj([f"Bool.not(Nat.is_eq(AD.slot({P1('n',3)}, d), AD.slot((r + 1 : U32), d)))", 'True{}'])},
        opw(r, d, (n + 2 : U32), hst, and_l({OP('r','(n + 2 : U32)')}, {OP('r','(n + 3 : U32)')}, and_r({OP('r','(n + 1 : U32)')}, {OP('r','(n + 2 : U32)')} && {OP('r','(n + 3 : U32)')}, hw))),
        and_intro(Bool.not(Nat.is_eq(AD.slot((n + 3 : U32), d), AD.slot((r + 1 : U32), d))), True{{}},
          opw(r, d, (n + 3 : U32), hst, and_r({OP('r','(n + 2 : U32)')}, {OP('r','(n + 3 : U32)')}, and_r({OP('r','(n + 1 : U32)')}, {OP('r','(n + 2 : U32)')} && {OP('r','(n + 3 : U32)')}, hw))), {{==}}))))

# the free list's first nodes, none live: r's link word off all their words
def nodesoff_po(F: List<&2, U32>, +r: U32, +L: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +hst: {{P.is_static(r) == False{{}} : Bool}}, +hpo: {T('RG.po.all(r, L, d, N)')},
  +hFN: {T('RG.sub(F, N)')}, +hFL: {T('RG.none.in(F, L)')}) -> {T('KMd.nodes.off(F, d, (r + 1 : U32))')}:
  match F:
    case Nil{{}}:
      {{==}}
    case Con{{+n, +t}}:
      and_intro({OW('n','(r + 1 : U32)')}, KMd.nodes.off(t, d, (r + 1 : U32)),
        ow_po(r, L, d, N, n, hst, hpo, and_l(RG.has(N, n), RG.sub(t, N), hFN), MB.eq_false_of_not_eq_true(RG.has(L, n), and_l(Bool.not(RG.has(L, n)), RG.none.in(t, L), hFL))),
        nodesoff_po(t, r, L, d, N, hst, hpo, and_r(RG.has(N, n), RG.sub(t, N), hFN), and_r(Bool.not(RG.has(L, n)), RG.none.in(t, L), hFL)))
'''
# offr from po for the link's write
OFFR=lambda t,j: f'IM.tr.offr({t}, d, {j})'
NODES=lambda t: f'IM.tr.nodes({t})'; LVS=lambda t: f'IM.tr.leaves({t})'; BRS=lambda t: f'IM.tr.branches({t})'
OLK=lambda M: f'RG.off.links({M}, d, (r + 1 : U32))'; OPS=lambda M: f'RG.off.pos({M}, d, (r + 1 : U32))'
def flipw(w_, h):  # Bool.not(is_eq(slot(r+1), slot(w))) == True  ->  Bool.not(is_eq(slot(w), slot(r+1))) == True
    return f'nf2(Nat.is_eq(AD.slot({w_}, d), AD.slot((r + 1 : U32), d)), neq_comm2(AD.slot((r + 1 : U32), d), AD.slot({w_}, d), not_true(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot({w_}, d)), {h})))'
LFW=lambda y: [f'Bool.not(Nat.is_eq(AD.slot({y}, d), AD.slot((r + 1 : U32), d)))', f'Bool.not(Nat.is_eq(AD.slot(({y} + 2 : U32), d), AD.slot((r + 1 : U32), d)))', f'Bool.not(Nat.is_eq(AD.slot(({y} + 3 : U32), d), AD.slot((r + 1 : U32), d)))', 'True{}']
out+=f'''
# the link's write at r + 1 off the words the realization reads
def offr_po(t: IM.Tr, +r: U32, +L: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +hst: {{P.is_static(r) == False{{}} : Bool}}, +hpo: {T('RG.po.all(r, L, d, N)')},
  +hpk: {T('RG.port.ok(L, d, r)')}, +hsN: {T(f"RG.sub({NODES('t')}, N)")}, +hsL: {T(f"RG.sub({LVS('t')}, L)")}, +hbL: {T(f"RG.none.in(L, {BRS('t')})")}) -> {T(OFFR('t','(r + 1 : U32)'))}:
  match t:
    case IM.Lf{{+y, +ky}}:
      +hyL = and_l(RG.has(L, y), RG.sub([], L), hsL)
      {intro(LFW('y'), [f"opw(r, d, y, hst, and_l({OP('r','y')}, Bool.or(RG.has(L, y), {W3('r','y')}), po_at(N, r, L, d, y, hpo, and_l(RG.has(N, y), RG.sub([], N), hsN))))",
        flipw('(y + 2 : U32)', f"JP.opos_at(L, d, (r + 1 : U32), y, and_r({OLK('L')}, {OPS('L')}, hpk), hyL)"),
        flipw('(y + 3 : U32)', f"JP.ol_at(L, d, (r + 1 : U32), y, and_l({OLK('L')}, {OPS('L')}, hpk), hyL)"), '{==}'])}
    case IM.Br{{+b, +i, +l, +r2}}:
      +hsa = and_r(RG.has(N, b), RG.sub({AP(NODES('l'),NODES('r2'))}, N), hsN)
      +hba = none_sub(L, Con{{b, {AP(BRS('l'),BRS('r2'))}}}, {AP(BRS('l'),BRS('r2'))}, hbL, sub_cons_r({AP(BRS('l'),BRS('r2'))}, b, {AP(BRS('l'),BRS('r2'))}, sub_refl({AP(BRS('l'),BRS('r2'))})))
      and_intro({OW('b','(r + 1 : U32)')}, {OFFR('l','(r + 1 : U32)')} && {OFFR('r2','(r + 1 : U32)')},
        ow_po(r, L, d, N, b, hst, hpo, and_l(RG.has(N, b), RG.sub({AP(NODES('l'),NODES('r2'))}, N), hsN), none_head(L, b, {AP(BRS('l'),BRS('r2'))}, hbL)),
        and_intro({OFFR('l','(r + 1 : U32)')}, {OFFR('r2','(r + 1 : U32)')},
          offr_po(l, r, L, d, N, hst, hpo, hpk, XP.sub_app_l({NODES('l')}, {NODES('r2')}, N, hsa), XP.sub_app_l({LVS('l')}, {LVS('r2')}, L, hsL), none_sub(L, {AP(BRS('l'),BRS('r2'))}, {BRS('l')}, hba, sub_appl({BRS('l')}, {BRS('r2')}))),
          offr_po(r2, r, L, d, N, hst, hpo, hpk, XP.sub_app_r({NODES('l')}, {NODES('r2')}, N, hsa), XP.sub_app_r({LVS('l')}, {LVS('r2')}, L, hsL), none_sub(L, {AP(BRS('l'),BRS('r2'))}, {BRS('r2')}, hba, sub_appr({BRS('l')}, {BRS('r2')})))))

# and the situating node's word 3
def offr3(+r: U32, +L: List<&2, U32>, +d: Nat, +s: U32, +hpk: {T('RG.port.ok(L, d, r)')}, +hsL: {T('RG.has(L, s)')}) -> {T('Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((r + 1 : U32), d)))')}:
  {flipw('(s + 3 : U32)', f"JP.ol_at(L, d, (r + 1 : U32), s, and_l({OLK('L')}, {OPS('L')}, hpk), hsL)")}
'''
# real_lk and chain_lk
OFFIX=lambda I,j: f'IM.ix.offr({I}, s, d, {j})'
out+=f'''
# a link's write kept off the realization and the free list
def real_lk(+st: Bool, A: Array<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +s: U32, +I: IM.Ix, +r: U32, +val: U32, +hst: {{P.is_static(r) == st : Bool}},
  +hj: {T(f"Bool.or(st, {OFFIX('I','(r + 1 : U32)')})")}, hf: {{AD.full(U32, A, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}},
  hr: {T('IM.ix.real(AD.view(U32, A), d, s, I)')}) -> {T('IM.ix.real(AD.view(U32, JP.lk(st, A, r, val)), d, s, I)')}:
  match st:
    case True{{}}:
      hr
    case False{{}}:
      XL.real_kept1(A, LAT.fromT(V.Val, ta), d, s, I, (r + 1 : U32), val, hf, hd32, hj, hr)

def chain_lk(+st: Bool, A: Array<U32>, +ta: LAT.Tree<V.Val>, +d: Nat, +r: U32, +val: U32, +ns: List<&2, U32>, +hst: {{P.is_static(r) == st : Bool}},
  +hj: {T("Bool.or(st, KMd.nodes.off(ns, d, (r + 1 : U32)))")}, +hjh: {T("Bool.or(st, Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(P.at_fh(), d))))")},
  hf: {{AD.full(U32, A, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}},
  hc: {T('KMd.chain(ns, AD.view(U32, A), d, KMd.word(AD.view(U32, A), d, P.at_fh()))')}) -> {T('KMd.chain(ns, AD.view(U32, JP.lk(st, A, r, val)), d, KMd.word(AD.view(U32, JP.lk(st, A, r, val)), d, P.at_fh()))')}:
  match st:
    case True{{}}:
      hc
    case False{{}}:
      XL.chain_kept(A, LAT.fromT(V.Val, ta), d, (r + 1 : U32), val, ns, hf, hd32, not_true(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(P.at_fh(), d)), hjh), hj, hc)

# the three, for a faced port, from what the invariant asks of it
def lk_off.k(+st: Bool, +r: U32, +I: IM.Ix, +s: U32, +L: List<&2, U32>, +F: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +hst: {{P.is_static(r) == st : Bool}},
  +hpo: {T('RG.po.all(r, L, d, N)')}, +hpk: {T('RG.port.ok(L, d, r)')}, +hsL: {T('RG.has(L, s)')}, +hIN: {T('RG.sub(IM.ix.nodes(I), N)')}, +hlL: {T('RG.sub(IM.ix.leaves(I), L)')},
  +hbL: {T('RG.none.in(L, IM.ix.branches(I))')}, +hFN: {T('RG.sub(F, N)')}, +hFL: {T('RG.none.in(F, L)')}) ->
  {T(f"Bool.or(st, {OFFIX('I','(r + 1 : U32)')}) && (Bool.or(st, KMd.nodes.off(F, d, (r + 1 : U32))) && Bool.or(st, Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(P.at_fh(), d)))))")}:
  match st:
    case True{{}}:
      {{==}}
    case False{{}}:
      and_intro({OFFIX('I','(r + 1 : U32)')}, KMd.nodes.off(F, d, (r + 1 : U32)) && Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(P.at_fh(), d))),
        offr_ix(I, r, L, d, N, s, hst, hpo, hpk, hsL, hIN, hlL, hbL),
        and_intro(KMd.nodes.off(F, d, (r + 1 : U32)), Bool.not(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(P.at_fh(), d))), nodesoff_po(F, r, L, d, N, hst, hpo, hFN, hFL),
          nf2(Nat.is_eq(AD.slot((r + 1 : U32), d), AD.slot(P.at_fh(), d)), opf(r, d, P.at_fh(), hst, po_fh(N, r, L, d, hpo)))))

def offr_ix(I: IM.Ix, +r: U32, +L: List<&2, U32>, +d: Nat, +N: List<&2, U32>, +s: U32, +hst: {{P.is_static(r) == False{{}} : Bool}}, +hpo: {T('RG.po.all(r, L, d, N)')},
  +hpk: {T('RG.port.ok(L, d, r)')}, +hsL: {T('RG.has(L, s)')}, +hIN: {T('RG.sub(IM.ix.nodes(I), N)')}, +hlL: {T('RG.sub(IM.ix.leaves(I), L)')}, +hbL: {T('RG.none.in(L, IM.ix.branches(I))')}) ->
  {T(OFFIX('I','(r + 1 : U32)'))}:
  match I:
    case IM.Ept{{}}:
      offr3(r, L, d, s, hpk, hsL)
    case IM.Has{{+t}}:
      and_intro(Bool.not(Nat.is_eq(AD.slot((s + 3 : U32), d), AD.slot((r + 1 : U32), d))), {OFFR('t','(r + 1 : U32)')}, offr3(r, L, d, s, hpk, hsL), offr_po(t, r, L, d, N, hst, hpo, hpk, hIN, hlL, hbL))
'''
out=mv(out,'def offr_ix(','def lk_off.k(')
# offr after a removal for a tracked node's words and the head
out+=f'''
# a node apart from a tree: its words off the words the tree's realization reads
'''
for i in range(4):
    ni=P1('n',i)
    LFn=lambda y: [f'Bool.not(Nat.is_eq(AD.slot({y}, d), AD.slot({ni}, d)))', f'Bool.not(Nat.is_eq(AD.slot(({y} + 2 : U32), d), AD.slot({ni}, d)))', f'Bool.not(Nat.is_eq(AD.slot(({y} + 3 : U32), d), AD.slot({ni}, d)))', 'True{}']
    OWt=lambda b: [f'Bool.not(Nat.is_eq(AD.slot({P1(b,q)}, d), AD.slot({ni}, d)))' for q in range(4)]+['True{}']
    DJ=lambda a,b: [OW(b,P1(a,q)) for q in range(4)]
    DISJ2=lambda y: proj(DJ('n',y), i, f'and_r(IM.nd.disj(d, {y}, n), IM.nd.disj(d, n, {y}), h)')
    out+=f'''
def offr_sep{i}(t: IM.Tr, +d: Nat, +n: U32, +h: {T('IM.tr.offn(t, d, n)')}) -> {T(OFFR('t',ni))}:
  match t:
    case IM.Lf{{+y, +ky}}:
      +D = {DISJ2('y')}
      {intro(LFn('y'), [proj(OWt('y'),0,'D'), proj(OWt('y'),2,'D'), proj(OWt('y'),3,'D'), '{==}'])}
    case IM.Br{{+b, +i2, +l, +r}}:
      +hlr = and_r(IM.nd.sep(d, b, n), IM.tr.offn(l, d, n) && IM.tr.offn(r, d, n), h)
      and_intro({OW('b',ni)}, {OFFR('l',ni)} && {OFFR('r',ni)}, {proj(DJ('n','b'), i, f'and_r(IM.nd.disj(d, b, n), IM.nd.disj(d, n, b), and_l(IM.nd.sep(d, b, n), IM.tr.offn(l, d, n) && IM.tr.offn(r, d, n), h))')},
        and_intro({OFFR('l',ni)}, {OFFR('r',ni)}, offr_sep{i}(l, d, n, and_l(IM.tr.offn(l, d, n), IM.tr.offn(r, d, n), hlr)), offr_sep{i}(r, d, n, and_r(IM.tr.offn(l, d, n), IM.tr.offn(r, d, n), hlr))))
'''
NDOKt=lambda a: ['U32.is_eq(P.base('+a+'), '+a+')', f'IM.ws.apart(KMd.nw({a}), d)', OW(a,FH)]
LFh=lambda y: [f'Bool.not(Nat.is_eq(AD.slot({y}, d), AD.slot(P.at_fh(), d)))', f'Bool.not(Nat.is_eq(AD.slot(({y} + 2 : U32), d), AD.slot(P.at_fh(), d)))', f'Bool.not(Nat.is_eq(AD.slot(({y} + 3 : U32), d), AD.slot(P.at_fh(), d)))', 'True{}']
OWh=lambda b: [f'Bool.not(Nat.is_eq(AD.slot({P1(b,q)}, d), AD.slot(P.at_fh(), d)))' for q in range(4)]+['True{}']
LAYB=lambda b,l,r: ['IM.nd.ok('+b+', d)', f'IM.tr.offn({l}, d, {b})', f'IM.tr.offn({r}, d, {b})', f'IM.tr.apart({l}, {r}, d)', f'IM.tr.lay({l}, d)', f'IM.tr.lay({r}, d)']
out+=f'''
def offr_fh(t: IM.Tr, +d: Nat, +h: {T('IM.tr.lay(t, d)')}) -> {T(OFFR('t','P.at_fh()'))}:
  match t:
    case IM.Lf{{+y, +ky}}:
      +D = {proj(NDOKt('y'),2,'h')}
      {intro(LFh('y'), [proj(OWh('y'),0,'D'), proj(OWh('y'),2,'D'), proj(OWh('y'),3,'D'), '{==}'])}
    case IM.Br{{+b, +i, +l, +r}}:
      and_intro({OW('b','P.at_fh()')}, {OFFR('l','P.at_fh()')} && {OFFR('r','P.at_fh()')}, {proj(NDOKt('b'),2,proj(LAYB('b','l','r'),0,'h'))},
        and_intro({OFFR('l','P.at_fh()')}, {OFFR('r','P.at_fh()')}, offr_fh(l, d, {proj(LAYB('b','l','r'),4,'h')}), offr_fh(r, d, {proj(LAYB('b','l','r'),5,'h')})))
'''
open('glam/proofgen/j1_part1.txt','w').write(out)
print('part 1', len(out.splitlines()))
