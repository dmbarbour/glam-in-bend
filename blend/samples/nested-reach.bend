# Written by Blend from nested-reach.blend; do not edit.
import Base

# blend: nested-reach.blend:9
def Outer.name() -> String:
  "outer"

# blend: nested-reach.blend:12
def Outer.Inner.a() -> String:
  Outer.name()

# blend: nested-reach.blend:12
def Outer.Sub.a() -> String:
  Outer.name()

# blend: nested-reach.blend:15
def Outer.Sub.s() -> String:
  Outer.Sub.a() ++ "+"

# blend: nested-reach.blend:19
def Outer2.name() -> String:
  "outer2"

# blend: nested-reach.blend:22
def Outer2.Inner.b() -> String:
  Outer2.name()

# blend: nested-reach.blend:12
def Outer2.Inner.a() -> String:
  Outer2.name()

# blend: nested-reach.blend:12
def Outer2.Sub.a() -> String:
  Outer2.name()

# blend: nested-reach.blend:15
def Outer2.Sub.s() -> String:
  Outer2.Sub.a() ++ "+"

# blend: nested-reach.blend:22
def Outer2.Sub.b() -> String:
  Outer2.name()

# blend: nested-reach.blend:26
def Outer3.name() -> String:
  "outer3"

# blend: nested-reach.blend:12
def Outer3.Inner.a() -> String:
  Outer3.name()

# blend: nested-reach.blend:12
def Outer3.Sub.a() -> String:
  Outer3.name()

# blend: nested-reach.blend:15
def Outer3.Sub.s() -> String:
  Outer3.Sub.a() ++ "+"

# blend: nested-reach.blend:19
def Both.name() -> String:
  "outer2"

# blend: nested-reach.blend:22
def Both.Inner.b() -> String:
  Both.name()

# blend: nested-reach.blend:12
def Both.Inner.a() -> String:
  Both.name()

# blend: nested-reach.blend:12
def Both.Sub.a() -> String:
  Both.name()

# blend: nested-reach.blend:15
def Both.Sub.s() -> String:
  Both.Sub.a() ++ "+"

# blend: nested-reach.blend:22
def Both.Sub.b() -> String:
  Both.name()

# blend: nested-reach.blend:12
def Y.a() -> String:
  Outer2.name()

# blend: nested-reach.blend:22
def Y.b() -> String:
  Outer2.name()

# blend: nested-reach.blend:32
def Y.ab() -> String:
  Y.a() ++ "/" ++ Y.b()

# blend: nested-reach.blend:35
def main() -> IO(Unit):
  IO.print(Y.ab() ++ " " ++ Outer2.Sub.s() ++ " " ++ Outer3.Sub.s() ++ " " ++ Both.Inner.a())
