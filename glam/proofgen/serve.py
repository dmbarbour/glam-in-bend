# glam/proofgen (generated-outputs-checked-in): glam/SERVE_PROOF.bend
# assembled, its hand-kept part (SERVE_PROOF.bend.in) then the copy's
# sections over the index, which sv/gen_cpi.py writes in parts (CPI_PART
# 5: parts 1 to 5; 6 and 7). Run from the run's root, after them.
P='glam/proofgen/'
head=open(P+'SERVE_PROOF.bend.in').read()
t=open(P+'sv/cpi1.txt').read()
first=t[t.index("# The copy's hand-off over the index (copy_pend; the Cells plan's"):]
rest=open(P+'sv/cpi6.txt').read()+open(P+'sv/cpi7.txt').read()
s=head+first.rstrip('\n')+'\n'+rest.lstrip('\n')
open('glam/SERVE_PROOF.bend','w').write(s.rstrip('\n')+'\n')
