# Written by Blend from laws.blend; do not edit.
import Base
import ./laws.bend as Blend_0

# blend: laws.blend:15
law NatAdd.right_id:
  for +x: Blend_0.NatAdd.T()
  {Blend_0.NatAdd.op(x, Blend_0.NatAdd.zero()) == x : Blend_0.NatAdd.T()}

# blend: laws.blend:18
law NatAdd.double_op:
  for +x: Blend_0.NatAdd.T()
  {Blend_0.NatAdd.double(x) == Blend_0.NatAdd.op(x, x) : Blend_0.NatAdd.T()}

# blend: laws.blend:15
law AnyOf.right_id:
  for +x: Blend_0.AnyOf.T()
  {Blend_0.AnyOf.op(x, Blend_0.AnyOf.zero()) == x : Blend_0.AnyOf.T()}

# blend: laws.blend:18
law AnyOf.double_op:
  for +x: Blend_0.AnyOf.T()
  {Blend_0.AnyOf.double(x) == Blend_0.AnyOf.op(x, x) : Blend_0.AnyOf.T()}
