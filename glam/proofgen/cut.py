# glam/proofgen (generated-outputs-checked-in): the proof files cut to
# what their laws reach, regen.sh's last stage: glam/SERVE_PROOF.bend to
# the definitions its Laws.* reach, then glam/PROOF.bend to those its
# laws and SERVE_PROOF.bend's GP.* names reach. Each definition's
# comment lines are left out of what it names (docs/Proving.md, "A survey
# by name reads words in comments"). Run from the run's root.
import re, os, importlib.util
spec=importlib.util.spec_from_file_location('ol','scripts/one_law.py')
ol=importlib.util.module_from_spec(spec); spec.loader.exec_module(ol)
G='glam/'
def rd(f): return open(G+f).read()
def wr(f, s): open(G+f,'w').write(s.rstrip('\n')+'\n')
def reach(its, roots):
    body={n:t for n,t in its if n}
    keep=set(); todo=[r for r in roots if r in body]
    while todo:
        n=todo.pop()
        if n in keep: continue
        code='\n'.join(l for l in body[n].split('\n') if not l.lstrip().startswith('#'))
        keep.add(n); todo+=[t for t in ol.NAME.findall(code) if t in body and t not in keep]
    return keep
def cut(f, roots):
    head, its = ol.items(rd(f))
    keep=reach(its, roots)
    out=[t for n,t in its if n is None or n in keep]
    dropped=[n for n,t in its if n and n not in keep]
    wr(f, '\n'.join([head]+out))
    return dropped
def cut_proofs():
    laws=re.findall(r'(?m)^law (\S+):', rd('LAWS.bend'))
    d1=cut('SERVE_PROOF.bend', [n for n,_ in ol.items(rd('SERVE_PROOF.bend'))[1] if n and n.startswith('Laws.')])
    sp=rd('SERVE_PROOF.bend')
    gp=set(re.findall(r'(?<![\w.])GP\.([A-Za-z_][A-Za-z0-9_.]*)\(', sp))
    d2=cut('PROOF.bend', ['Laws.'+l for l in laws]+sorted(gp))
    return d1, d2
d1, d2 = cut_proofs(); print('cut', len(d1), len(d2))
