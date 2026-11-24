# Laws of positioned demand (glam/position.bend), stated over
# glam/position_model.bend; proved in glam/POSITION_PROOF.bend.

import Base
import ../spike/kprim.bend as P
import ./position.bend as Q
import ./position_model.bend as QM

# LAW: positioned demand's frontier faces the position
# (cursor-laws.noself.frontier.faces): when a source demanded at a
# position ends at the frontier (Q.PdFront), its port is the position's
# link word in the frontier's own heap, however many walks ran. Any heap.
# So the cursor a serve finds there is at the port the position faces;
# with the source wired (wired_port), never the position itself
# (.frontier.apart). Not claimed: anything of the other ends.
# Record: copy-reduced-function-nets
# Record: cursors-indexed
law front_faces:
  for h: P.H
  for +pos: U32
  for +g: Nat
  for +f: Nat
  {QM.front.at(Q.positioned(h, pos, g, f), pos) == True{} : Bool}
