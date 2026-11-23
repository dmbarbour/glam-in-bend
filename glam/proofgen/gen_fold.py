# authoring aid: crossings_pend over the index (glam/PROOF.bend), run
# after gen_cx.py by regen.sh
p='glam/PROOF.bend'; s=open(p).read()
T=lambda h: f'{{{h} == True{{}} : Bool}}'
def drop(s, head):
    i=s.index(head); j=s.index('\n\n',i); return s[:i]+s[j+2:]
s=drop(s,'def crossings_pend.m(')
s=drop(s,'def Laws.crossings_pend(')
TW='LAT.fromT(U32, tw)'; TA='LAT.fromT(V.Val, ta)'; TM='LAT.fromT(U32, tm)'
H0=f'P.H{{KM.MG{{{TW}}}, {TA}}}'
def CODE(cl, mp, heap): return f'Pair.snd(Array<U32>, P.H, R.crossings({cl}, ({mp}, {heap}), s))'
def CODEr(rest_q): return f'Pair.snd(Array<U32>, P.H, R.crossings(rest, {rest_q}, s))'
def MOD(S): return f'RG.cxs.I({S}), [], RG.cxs.L({S}), RG.cxs.F({S})'
def GL(code, S, full=True):
    g=f'RG.px.ok(AD.view(U32, RG.words({code})), d, s, {MOD(S)}, N)'
    return T(g + (f' && AD.full(U32, RG.words({code}), d)' if full else ''))
def S0(cl, vm, I='I', L='L', F='F'): return f'RG.cxs({cl}, {vm}, dm, {I}, {L}, {F})'
CL='Con{R.FzC{at, src, neg, far}, rest}'
M='IM.ix.look(I, far)'; HD='RG.cx.hd(F)'; TL=f'RG.cx.tl({M}, I, F)'
F0E=f'RG.cx.F0({M}, I, {HD}, {TL})'
XM=f'RG.pl.of(List.get(&2, U32, AD.view(U32, {TM}), AD.slot(at, dm)))'
X=f'Pair.snd(Array<U32>, U32, Array.get(U32, {TM}, at))'
PSR=f'RG.pls(rest, AD.view(U32, {TM}), dm)'
I1=lambda x: f'RG.cx.I({M}, I, {x}, src, {HD}, far)'
L1=lambda x: f'RG.cx.L({M}, {x}, L)'
F1=lambda x: f'RG.cx.F1({M}, I, {x}, far, {TL})'
SR=lambda x: S0('rest', f'AD.view(U32, {TM})', I1(x), L1(x), F1(x))
H1=f'R.cross({H0}, s, {X}, src, neg, far)'
PX1=f'RG.px.ok(AD.view(U32, RG.words({H1})), d, s, {I1(X)}, {PSR}, {L1(X)}, {F1(X)}, N)'
FU1=f'AD.full(U32, RG.words({H1}), d)'
AB=f'RG.cx.ab({M}, I, src)'; RM=f'RG.cx.room({M}, I, F)'
OKR=lambda vm, x: f'RG.cxs.ok(rest, {vm}, dm, {I1(x)}, {F1(x)})'
HPX=lambda v, ps: T(f'RG.px.ok({v}, d, s, I, {ps}, L, F, N)')
XMq=lambda q: f'RG.pl.of(List.get(&2, U32, AD.view(U32, {q}), AD.slot(at, dm)))'
I1q=lambda q,x: f'RG.cx.I({M}, I, {x}, src, {HD}, far)'
out=f'''
# A copy's crossings over the index
# =================================
#
# cells-freeze.sharing.cursors.index.ring.fold: crossings_pend by the
# crossings in turn, each by cxp.t (the invariant after a crossing and
# its words full), the heap after it rebuilt from its parts (heta2) for
# the next; the model's placeholder the code's (LA.get_view), its free
# list as the crossing's law takes it (cx_f0).

# any heap in its parts (as glam/SPLICE_PROOF.bend's heta, by RG.words)
def heta2(h: P.H) -> {{P.H{{KM.MG{{RG.words(h)}}, KMd.vals(h)}} == h : P.H}}:
  match h:
    case P.H{{w, a}}:
      match w:
        case KM.MG{{x}}:
          {{==}}

# the free list's first nodes as a crossing's law takes them, where there
# is room: the branch a cursor made in a tree takes, then the rest
def cx_f0(m: Maybe<&2, U32>, +I: IM.Ix, F: List<&2, U32>, +h: {T('RG.cx.room(m, I, F)')}) -> {{RG.cx.F0(m, I, RG.cx.hd(F), RG.cx.tl(m, I, F)) == F : List<&2, U32>}}:
  match m:
    case Some{{+y}}:
      {{==}}
    case None{{}}:
      match I:
        case IM.Ept{{}}:
          {{==}}
        case IM.Has{{+t}}:
          match F:
            case Nil{{}}:
              Empty.absurd({{RG.cx.F0(None{{}}, IM.Has{{t}}, RG.cx.hd([]), RG.cx.tl(None{{}}, IM.Has{{t}}, [])) == [] : List<&2, U32>}}, MB.false_ne_true()(h))
            case Con{{+b, +r}}:
              {{==}}

# the crossings in turn: the invariant after them, and their words full
def crf.go(cl: List<&2, R.FzC>, -w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +s: U32, +I: IM.Ix, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, hfm: {{AD.full(U32, map, dm) == True{{}} : Bool}}, +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}},
  +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, hp: {HPX('AD.view(U32, w)', 'RG.pls(cl, AD.view(U32, map), dm)')}, hok: {T('RG.cxs.ok(cl, AD.view(U32, map), dm, I, F)')},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) -> {GL(CODE('cl','map','P.H{KM.MG{w}, a}'), S0('cl','AD.view(U32, map)'))}:
  match cl:
    case Nil{{}}:
      (+tw, +ew) = mw
      +hft = LAP.full_t(U32, w, tw, d, ew, hf)
      +hpT = LAB.subst(Array<U32>, qq => {HPX('AD.view(U32, qq)','[]')}, w, {TW}, Equal.sym(Array<U32>, {TW}, w, ew), hp)
      %ew : {T("RG.px.ok(AD.view(U32, _), d, s, I, [], L, F, N) && AD.full(U32, _, d)")}
      and_intro(RG.px.ok(AD.view(U32, {TW}), d, s, I, [], L, F, N), AD.full(U32, {TW}, d), hpT, hft)
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
          +hC = cxp.t(tw, ta, d, s, I, {PSR}, L, {TL}, N, {X}, src, neg, far, {HD}, hft, hd32, hN, hB, hpF, hab)
          %ew : {GL(CODE(CL,'map','P.H{KM.MG{_}, a}'), S0(CL,'AD.view(U32, map)'))}
          %ea : {GL(CODE(CL,'map',f'P.H{{KM.MG{{{TW}}}, _}}'), S0(CL,'AD.view(U32, map)'))}
          %em : {GL(CODE(CL,'_',H0), S0(CL,'AD.view(U32, _)'))}
          %Equal.sym(Array<U32> & U32, Array.get(U32, {TM}, at), ({TM}, {X}), LA.get_pair(U32, {TM}, at)) :
            {GL(CODEr(f'R.crossing.pl(_, {H0}, s, src, neg, far)'), SR(XM))}
          %Equal.sym(U32, {XM}, {X}, ePL) :
            {GL(CODEr(f'({TM}, {H1})'), SR('_'))}
          %heta2({H1}) :
            {GL(CODEr(f'({TM}, _)'), SR(X))}
          crf.go(rest, RG.words({H1}), KMd.vals({H1}), {TM}, d, dm, s, {I1(X)}, {L1(X)}, {F1(X)}, N, and_r({PX1}, {FU1}, hC), hd32, hfmt, hdm, hN, hB, and_l({PX1}, {FU1}, hC), hokr,
            LAT.mirror(U32, RG.words({H1})), LAT.mirror(V.Val, KMd.vals({H1})), LAT.mirror(U32, {TM}))

def crossings_pend.m(-w: Array<U32>, -a: Array<V.Val>, -map: Array<U32>, +d: Nat, +dm: Nat, +s: U32, +I: IM.Ix, +L: List<&2, U32>, +F: List<&2, U32>, +N: List<&2, U32>, +cs: List<&2, R.FzC>,
  hf: {{AD.full(U32, w, d) == True{{}} : Bool}}, +hd32: {{Nat.is_lt(d, 32n) == True{{}} : Bool}}, hfm: {{AD.full(U32, map, dm) == True{{}} : Bool}}, +hdm: {{Nat.is_lt(dm, 32n) == True{{}} : Bool}},
  +hN: {T('RG.layout(N, d)')}, +hB: {T('RG.bases(N)')}, hp: {HPX('AD.view(U32, w)', 'RG.pls(cs, AD.view(U32, map), dm)')}, hok: {T('RG.cxs.ok(cs, AD.view(U32, map), dm, I, F)')},
  mw: LAT.Mirror(U32, w), ma: LAT.Mirror(V.Val, a), mm: LAT.Mirror(U32, map)) -> {GL(CODE('cs','map','P.H{KM.MG{w}, a}'), S0('cs','AD.view(U32, map)'), False)}:
  (+tw, +ew) = mw
  (+ta, +ea) = ma
  (+tm, +em) = mm
  +hft = LAP.full_t(U32, w, tw, d, ew, hf)
  +hfmt = LAP.full_t(U32, map, tm, dm, em, hfm)
  +hpa = LAB.subst(Array<U32>, qq => {HPX('AD.view(U32, qq)', 'RG.pls(cs, AD.view(U32, map), dm)')}, w, {TW}, Equal.sym(Array<U32>, {TW}, w, ew), hp)
  +hpb = LAB.subst(Array<U32>, qq => {HPX(f'AD.view(U32, {TW})', 'RG.pls(cs, AD.view(U32, qq), dm)')}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hpa)
  +hoT = LAB.subst(Array<U32>, qq => {T('RG.cxs.ok(cs, AD.view(U32, qq), dm, I, F)')}, map, {TM}, Equal.sym(Array<U32>, {TM}, map, em), hok)
  %ew : {GL(CODE('cs','map','P.H{KM.MG{_}, a}'), S0('cs','AD.view(U32, map)'), False)}
  %ea : {GL(CODE('cs','map',f'P.H{{KM.MG{{{TW}}}, _}}'), S0('cs','AD.view(U32, map)'), False)}
  %em : {GL(CODE('cs','_',H0), S0('cs','AD.view(U32, _)'), False)}
  and_l(RG.px.ok(AD.view(U32, RG.words({CODE('cs',TM,H0)})), d, s, {MOD(S0('cs',f'AD.view(U32, {TM})'))}, N), AD.full(U32, RG.words({CODE('cs',TM,H0)}), d),
    crf.go(cs, {TW}, {TA}, {TM}, d, dm, s, I, L, F, N, hft, hd32, hfmt, hdm, hN, hB, hpb, hoT, LAT.mirror(U32, {TW}), LAT.mirror(V.Val, {TA}), LAT.mirror(U32, {TM})))

def Laws.crossings_pend(w, a, map, d, dm, s, I, L, F, N, cs, hf, hd32, hfm, hdm, hN, hB, hp, hok):
  crossings_pend.m(w, a, map, d, dm, s, I, L, F, N, cs, hf, hd32, hfm, hdm, hN, hB, hp, hok, LAT.mirror(U32, w), LAT.mirror(V.Val, a), LAT.mirror(U32, map))
'''
s=s.rstrip('\n')+'\n'+out
open(p,'w').write(s)
print('fold', len(out.splitlines()))
