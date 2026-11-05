# Written by Blend from declares.blend; do not edit.
import Base
import ./declares.bend as Blend_0

# blend: declares.blend:11
def Listed.S.as_declared() -> Data:
  Blend_0.Listed.S()

# blend: declares.blend:12
def Listed.push.as_declared(st: Blend_0.Listed.S(), +x: U32) -> Blend_0.Listed.S():
  Blend_0.Listed.push(st, x)

# blend: declares.blend:13
def Listed.empty.as_declared() -> Blend_0.Listed.S():
  Blend_0.Listed.empty()

# blend: declares.blend:11
def Counted.S.as_declared() -> Data:
  Blend_0.Counted.S()

# blend: declares.blend:12
def Counted.push.as_declared(st: Blend_0.Counted.S(), +x: U32) -> Blend_0.Counted.S():
  Blend_0.Counted.push(st, x)

# blend: declares.blend:13
def Counted.empty.as_declared() -> Blend_0.Counted.S():
  Blend_0.Counted.empty()
