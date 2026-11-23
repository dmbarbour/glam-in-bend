# authoring aid: what a join's link does to the live nodes' facing
# (glam/JOIN_LAWS.bend, glam/JOIN_PROOF.bend)
import itertools
T=lambda h: f'{{{h} == True{{}} : Bool}}'
F_=lambda h: f'{{{h} == False{{}} : Bool}}'
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
# ---- a propositional prover emitting Bend case trees ----
# formulas: ('v',name) | ('t',) | ('f',) | ('not',a) | ('or',a,b) | ('and',a,b) | ('sel3',B,A,pf,pw,pu)
def ev(f, env):
    k=f[0]
    if k=='v': return env.get(f[1])
    if k=='t': return True
    if k=='f': return False
    if k=='not':
        a=ev(f[1],env); return None if a is None else (not a)
    if k=='or':
        a=ev(f[1],env)
        if a is None: return None
        return True if a else ev(f[2],env)
    if k=='and':
        a=ev(f[1],env)
        if a is None: return None
        return ev(f[2],env) if a else False
    if k=='sel3':
        B=ev(f[1],env)
        if B is None: return None
        if not B: return ev(f[5],env)
        A=ev(f[2],env)
        if A is None: return None
        return ev(f[3],env) if A else ev(f[4],env)
def stuck(f, env):
    # the atom Bend's evaluation of f waits on, or None
    k=f[0]
    if k=='v': return f[1] if f[1] not in env else None
    if k in ('t','f'): return None
    if k=='not': return stuck(f[1],env)
    if k in ('or','and'):
        a=ev(f[1],env)
        if a is None: return stuck(f[1],env)
        if (k=='or' and a) or (k=='and' and not a): return None
        return stuck(f[2],env)
    if k=='sel3':
        B=ev(f[1],env)
        if B is None: return stuck(f[1],env)
        if not B: return stuck(f[5],env)
        A=ev(f[2],env)
        if A is None: return stuck(f[2],env)
        return stuck(f[3] if A else f[4],env)
def bend(f, env):
    k=f[0]
    if k=='v': return ('True{}' if env[f[1]] else 'False{}') if f[1] in env else f[1]
    if k=='t': return 'True{}'
    if k=='f': return 'False{}'
    if k=='not': return f'Bool.not({bend(f[1],env)})'
    if k=='or': return f'Bool.or({bend(f[1],env)}, {bend(f[2],env)})'
    if k=='and': return f'Bool.and({bend(f[1],env)}, {bend(f[2],env)})'
    if k=='sel3': return f'sel3({bend(f[1],env)}, {bend(f[2],env)}, {bend(f[3],env)}, {bend(f[4],env)}, {bend(f[5],env)})'
def allvals(f, atoms, env):
    free=[a for a in atoms if a not in env]
    for vals in itertools.product([True,False],repeat=len(free)):
        e=dict(env); e.update(zip(free,vals))
        yield e
def tree(goal, hyps, atoms, env, ind):
    g=ev(goal,env)
    if g is True: return f'{ind}{{==}}\n'
    for (hn,hf) in hyps:
        if ev(hf,env) is False:
            return f'{ind}Empty.absurd({{{bend(goal,env)} == True{{}} : Bool}}, MB.false_ne_true()({hn}))\n'
    # the next atom in parameter order: Bend matches binders in the order bound
    a=next(x for x in atoms if x not in env)
    out=f'{ind}match {a}:\n'
    for v in (True,False):
        e=dict(env); e[a]=v
        out+=f'{ind}  case {"True{}" if v else "False{}"}:\n'+tree(goal,hyps,atoms,e,ind+'    ')
    return out
def prop_lemma(name, atoms, hyps, goal):
    # check it first
    for e in allvals(goal, atoms, {}):
        if all(ev(hf,e) for _,hf in hyps):
            assert ev(goal,e), (name, e)
    sig=', '.join(f'+{a}: Bool' for a in atoms)
    hs=', '.join(f'+{hn}: {{{bend(hf,{})} == True{{}} : Bool}}' for hn,hf in hyps)
    return f'def {name}({sig}, {hs}) -> {{{bend(goal,{})} == True{{}} : Bool}}:\n'+tree(goal,hyps,atoms,{},'  ')
V=lambda n: ('v',n)
OR=lambda a,b: ('or',a,b); NOT=lambda a: ('not',a); AND=lambda a,b: ('and',a,b)
S3=lambda B,A,pf,pw,pu: ('sel3',B,A,pf,pw,pu)
props=''
# per z: atoms Az (u off z+1), Bz (w off z+1), pfx (fz off x+1), pfy, pwx (w off x+1), puy (u off y+1), pux, pwy, pfz
Az,Bz,pfx,pfy,pwx,puy,pux,pwy,pfz=map(V,['az','bz','pfx','pfy','pwx','puy','pux','pwy','pfz'])
H_z=[('nsx',pux),('nsy',pwy),('nsz',pfz),('tzx',OR(pfx,NOT(Az))),('tzy',OR(pfy,NOT(Bz))),('txz',OR(Az,NOT(pfx))),('tyz',OR(Bz,NOT(pfy))),
     ('txy',OR(puy,NOT(pwx))),('tyx',OR(pwx,NOT(puy))),('o_uyz',OR(puy,Az)),('o_wxz',OR(pwx,Bz)),('o_fxy',OR(pfx,pfy))]
atz=['bz','az','pfx','pfy','pwx','puy','pux','pwy','pfz']
props+=prop_lemma('g2x', atz, H_z, S3(Bz,Az,pfx,pwx,pux))+'\n'
props+=prop_lemma('g2y', atz, H_z, S3(Bz,Az,pfy,pwy,puy))+'\n'
props+=prop_lemma('g3', atz, H_z, S3(Bz,Az,pfz,Bz,Az))+'\n'
# per (z, q): atoms
names=['bz','az','bq','aq','pzq','pqz','pzx','pzy','pqx','pqy']
bz,az,bq,aq,pzq,pqz,pzx,pzy,pqx,pqy=map(V,names)
H_zq=[('tzq',OR(pzq,NOT(pqz))),('tqz',OR(pqz,NOT(pzq))),('txz',OR(az,NOT(pzx))),('txq',OR(aq,NOT(pqx))),('tyz',OR(bz,NOT(pzy))),('tyq',OR(bq,NOT(pqy))),
      ('tzx',OR(pzx,NOT(az))),('tqx',OR(pqx,NOT(aq))),('tzy',OR(pzy,NOT(bz))),('tqy',OR(pqy,NOT(bq))),
      ('o_qzy',OR(pqz,pqy)),('o_qzx',OR(pqz,pqx)),('o_qxy',OR(pqx,pqy)),('o_zxy',OR(pzx,pzy)),('o_zqy',OR(pzq,pzy)),('o_zqx',OR(pzq,pzx))]
props+=prop_lemma('g4', names, H_zq, OR(S3(bz,az,pzq,bq,aq),NOT(S3(bq,aq,pqz,bz,az))))+'\n'
open('glam/proofgen/link_props.bend','w').write(props)
print(len(props.splitlines()), 'lines of case trees')
