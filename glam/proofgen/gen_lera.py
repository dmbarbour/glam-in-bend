# authoring aid (cells-freeze.sharing.cursors.index.ring.premises.implied,
# IndexPremises P3): leave_era_pend, the leave at the eraser's site
# (R.leave(h, P.era(), nc), glam/materialize.bend), leave_pend with no
# port premise, po_static giving the eraser's link words off. Run by
# regen.sh after the leave's stages; the law added to LAWS.bend if missing.
import re
lp='glam/LAWS.bend'; l=open(lp).read()
if 'law leave_era_pend:' not in l:
    i=l.index('law leave_pend:\n'); j=l.index('\n\n', i)
    blk=l[i:j]
    blk=blk.replace('law leave_pend:', 'law leave_era_pend:', 1).replace('  for +p: U32\n', '', 1)
    blk=re.sub(r'(?m)^  for hpo: .*\n', '', blk)
    blk=blk.replace(', p, c)', ', P.era(), c)')
    assert ' p,' not in blk and '(p,' not in blk, blk
    LAW='''# LAW: a cursor c the index finds at k leaving with the eraser linked in
# its place (R.leave(h, P.era(), c): the materializer's erasing site)
# keeps the pending placeholders' invariant over the index and the words
# full, as leave_pend has it: a static has no link word, so that the
# port's premise holds of the eraser by computation (po_static;
# IndexPremises P3). Not claimed: the leave's frame, leave_keeps': a
# static written a "link word" (the mutant leave_links_static) leaves
# this invariant whole.
# Record: copy-reduced-function-nets
# Record: cursors-indexed
# Record: static-links-count-as-nodes
'''
    l=l[:j]+'\n\n'+LAW+blk+l[j:]
    open(lp,'w').write(l)
p='glam/PROOF.bend'; s=open(p).read()
if 'def Laws.leave_era_pend(' not in s:
    s=s.rstrip('\n')+'''

# the eraser's leave: leave_pend, the eraser's link words off by
# computation (po_static)
def Laws.leave_era_pend(w, a, d, s, I, ps, L, F, N, c, k, hf, hd32, hN, hB, hp, hc):
  Laws.leave_pend(w, a, d, s, I, ps, L, F, N, P.era(), c, k, hf, hd32, hN, hB, hp, hc, AL.po_static([], d, N))
'''
    open(p,'w').write(s)
print('lera')
