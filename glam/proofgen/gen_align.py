# authoring aid (cells-freeze.sharing.cursors.index.ring.premises.implied,
# IndexPremises P3): glam/PROOF.bend imports the alignment lemmas of
# align/ALIGN.bend, checked there, rather than holding copies of them
# (cursor-laws.proofs.shared.align): a static port's link word off a
# base's words 2 and 3 at a depth of 2 or more (st_off, d2), port_of_po,
# faces_fresh, po_static, dyn_one, which the leave's stages call as AL's;
# with SERVE_PROOF.bend's dyn_of_bases and faces_fresh (gen_cpi.py). Run by regen.sh
# before the leave's stage; lawful-words comes with the import.
p='glam/PROOF.bend'; s=open(p).read()
IMP='import ./proofgen/align/ALIGN.bend as AL\n'
if IMP in s:
    print('align: present'); raise SystemExit
anchor='import 0x8ae61ec3a6615abd35f196c07232ad28/u32.bend as MU\n'
assert anchor in s
s=s.replace(anchor, anchor+IMP)
open(p,'w').write(s)
print('align: imported')
