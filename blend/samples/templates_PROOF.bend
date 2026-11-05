# Written by Blend from templates.blend; do not edit.
import Base
import ./templates.bend as Blend_0

# blend: templates.blend:13
def Twice.apply.as_declared(~f: U32 -> U32, x: U32) -> U32:
  Blend_0.Twice.apply(~f, x)

# blend: templates.blend:14
def Twice.count.as_declared(-A: Data, xs: List<&2, A>) -> U32:
  Blend_0.Twice.count(A, xs)
