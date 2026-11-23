# authoring aid (cells-freeze.sharing.cursors.index.ring.premises.compose,
# IndexPremises P1): each step law's conclusion the invariant and the
# words full, which its proof's core already gives: the six entries
# (cpx.m, jpx.m, cxp.m, crossings_pend.m, lpx.m, jnpx.m) keep their core's
# pair instead of projecting the invariant, and the laws of glam/LAWS.bend
# state it. Run by regen.sh after the generators, before the cut;
# idempotent.
import re, importlib.util
spec=importlib.util.spec_from_file_location('ol','scripts/one_law.py')
ol=importlib.util.module_from_spec(spec); spec.loader.exec_module(ol)
G='glam/'
ENTRIES={'cursor_pend':'cpx.m','join1_pend':'jpx.m','cross_pend':'cxp.m','crossings_pend':'crossings_pend.m','leave_pend':'lpx.m','join_pend':'jnpx.m'}
def balanced(s, i):
    # s[i] == '(' ; the index after its matching ')'
    depth=0
    for j in range(i, len(s)):
        c=s[j]
        if c in '([{': depth+=1
        elif c in ')]}':
            depth-=1
            if depth==0: return j+1
    raise ValueError('unbalanced')
def args(s, i):
    # s[i] == '(' : the top-level arguments' spans
    out=[]; depth=0; start=i+1
    for j in range(i, len(s)):
        c=s[j]
        if c in '([{': depth+=1
        elif c in ')]}':
            depth-=1
            if depth==0: out.append(s[start:j]); return out, j+1
        elif c==',' and depth==1: out.append(s[start:j]); start=j+1
def words_of(inner):
    i=inner.index('AD.view(U32, RG.words(')+len('AD.view(U32, ')
    return inner[i:balanced(inner, i+len('RG.words'))]
def widen(inner):
    if 'AD.full(U32, RG.words(' in inner: return inner
    # a lone call parenthesized parses as an annotation: only a
    # conjunction takes parentheses, as the cores write it
    depth=0; conj=False
    for j,c in enumerate(inner):
        if c in '([{': depth+=1
        elif c in ')]}': depth-=1
        elif depth==0 and inner.startswith(' && ', j): conj=True
    w=f'({inner})' if conj else inner
    return f'{w} && AD.full(U32, {words_of(inner)}, d)'
TYPE=re.compile(r'\{((?:(?!\{[^{}]*: Bool\}).)*?) == True\{\} : Bool\}', re.S)
def goal_spans(text):
    # the goal types: the return type, and each rewrite's
    spans=[]
    m=re.search(r'\) ->\s*\{', text); i=m.end()-1; j=balanced(text, i); spans.append((i, j))
    for m in re.finditer(r'(?m)^  %.*? : \{', text):
        i=m.end()-1; spans.append((i, balanced(text, i)))
    return spans
p=G+'PROOF.bend'; s=open(p).read()
head, its = ol.items(s)
changed=0
new=[]
for n, t in its:
    if n in ENTRIES.values() and 'and_l(' in t.split('\n')[-1] + ''.join(l for l in t.split('\n') if l.startswith('  and_l(')):
        for (i, j) in reversed(goal_spans(t)):
            ty=t[i:j]
            assert ty.endswith(' == True{} : Bool}'), ty[-40:]
            inner=ty[1:-len(' == True{} : Bool}')]
            t=t[:i]+'{'+widen(inner)+' == True{} : Bool}'+t[j:]
        k=t.index('\n  and_l(')+1
        a, e=args(t, k+len('  and_l'))
        t=t[:k]+'  '+a[2].strip()+t[e:]
        changed+=1
    new.append(t)
s='\n'.join([head]+new)
open(p,'w').write(s)
lp=G+'LAWS.bend'; l=open(lp).read()
for law in ENTRIES:
    i=l.index(f'law {law}:'); j=l.index('\n  {', i)+3; e=balanced(l, j)
    ty=l[j:e]; inner=ty[1:-len(' == True{} : Bool}')]
    l=l[:j]+'{'+widen(inner)+' == True{} : Bool}'+l[e:]
open(lp,'w').write(l)
print('compose', changed)
