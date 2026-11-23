# authoring aid (cells-freeze.sharing.cursors.index.ring.premises.implied,
# IndexPremises P3): glam/PROOF.bend's alignment section, from the
# lemmas of align/ALIGN.bend beside it (its lemmas checked
# there): a static port's link word off a base's words 2 and 3 at a
# depth of 2 or more (st_off, d2), port_of_po, faces_fresh, po_static,
# dyn_one; dyn_of_bases goes to SERVE_PROOF.bend (the serve's model).
# Run by regen.sh before the leave's stage; lawful-words imported.
import re
A=open('glam/proofgen/align/ALIGN.bend').read()
p='glam/PROOF.bend'; s=open(p).read()
if 'def port_of_po(' in s:
    print('align: present'); raise SystemExit
# the prototype's definitions, those PROOF.bend has already left out
body=A[A.index('\n# a static\'s word modulo 4 is 3'):A.index('\ndef main()')]
blocks=re.split(r'(?m)^(?=(?:# [^\n]*\n)*def )', body)
DROP=('ort_r', 'bases_at.k', 'bases_at', 'po_at.k', 'po_at', 'none_nil', 'dyn_of_bases')
keep=[]
for b in blocks:
    m=re.search(r'(?m)^def ([\w.]+)\(', b)
    if m and m.group(1) in DROP: continue
    keep.append(b)
sec=''.join(keep).replace('ort_r(', 'XP.ort_r(')
sec=re.sub(r'(?<![\w.])XP\.XP\.', 'XP.', sec)
HDR='''
# Alignment (cells-freeze.sharing.cursors.index.ring.premises.implied,
# IndexPremises P3): a static port's link word, r + 1 with r ending in
# 11, ends in 00, and a base's words 2 and 3 in 10 and 11; a slot of a
# heap of depth 2 or more keeps a word's low two bits, and a node's four
# words apart give the depth (d2). Bit facts through lawful-words
# (hub-laws-reused): 2^32 abstracted as m where a law states it, the
# mask ~3 written U32.not(3) where a bit of it is read, as the checker
# expands either in unary. port_of_po, faces_fresh and po_static fold
# them over the tracked nodes: what leave_pend's and the copy's
# premises hpk, hfr and the eraser's hpo asked, implied.
'''
s=s.rstrip('\n')+'\n'+HDR+sec.rstrip('\n')+'\n'
IMP=['import 0x96ab58f86121cb4f3fb48b3c8a045989/LAWS.bend as WL\n', 'import 0x96ab58f86121cb4f3fb48b3c8a045989/PROOF.bend as WP\n',
     'import 0x96ab58f86121cb4f3fb48b3c8a045989/defs.bend as WD\n']
anchor='import 0x8ae61ec3a6615abd35f196c07232ad28/u32.bend as MU\n'
assert anchor in s
s=s.replace(anchor, anchor+''.join(i for i in IMP if i not in s))
open(p,'w').write(s)
print('align', len(sec.splitlines()))
