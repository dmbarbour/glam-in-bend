# glam/proofgen (generated-outputs-checked-in): glam/JOIN_PROOF.bend
# assembled, link_live's proof (gen_link2.py writes the file) then
# link_leave's (gen_lvlink.py's lv_part1.txt). Run from the run's root.
p='glam/JOIN_PROOF.bend'
s=open(p).read()+open('glam/proofgen/lv_part1.txt').read()
open(p,'w').write(s)
