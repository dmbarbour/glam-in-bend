# Written by Blend from nested-reach.blend; do not edit.
import Base

# blend: nested-reach.blend:11
def Outer.name() -> String:
  "outer"

# blend: nested-reach.blend:14
def Outer.Inner.a() -> String:
  Outer.name()

# blend: nested-reach.blend:14
def Outer.Sub.a() -> String:
  Outer.name()

# blend: nested-reach.blend:17
def Outer.Sub.s() -> String:
  Outer.Sub.a() ++ "+"

# blend: nested-reach.blend:20
def Outer.Tag.tag() -> String:
  "#" ++ Outer.name()

# blend: nested-reach.blend:24
def Outer2.name() -> String:
  "outer2"

# blend: nested-reach.blend:27
def Outer2.Inner.b() -> String:
  Outer2.name()

# blend: nested-reach.blend:14
def Outer2.Inner.a() -> String:
  Outer2.name()

# blend: nested-reach.blend:14
def Outer2.Sub.a() -> String:
  Outer2.name()

# blend: nested-reach.blend:17
def Outer2.Sub.s() -> String:
  Outer2.Sub.a() ++ "+"

# blend: nested-reach.blend:27
def Outer2.Sub.b() -> String:
  Outer2.name()

# blend: nested-reach.blend:20
def Outer2.Tag.tag() -> String:
  "#" ++ Outer2.name()

# blend: nested-reach.blend:31
def Outer3.name() -> String:
  "outer3"

# blend: nested-reach.blend:14
def Outer3.Inner.a() -> String:
  Outer3.name()

# blend: nested-reach.blend:14
def Outer3.Sub.a() -> String:
  Outer3.name()

# blend: nested-reach.blend:17
def Outer3.Sub.s() -> String:
  Outer3.Sub.a() ++ "+"

# blend: nested-reach.blend:20
def Outer3.Tag.tag() -> String:
  "#" ++ Outer3.name()

# blend: nested-reach.blend:24
def Both.name() -> String:
  "outer2"

# blend: nested-reach.blend:27
def Both.Inner.b() -> String:
  Both.name()

# blend: nested-reach.blend:14
def Both.Inner.a() -> String:
  Both.name()

# blend: nested-reach.blend:14
def Both.Sub.a() -> String:
  Both.name()

# blend: nested-reach.blend:17
def Both.Sub.s() -> String:
  Both.Sub.a() ++ "+"

# blend: nested-reach.blend:27
def Both.Sub.b() -> String:
  Both.name()

# blend: nested-reach.blend:20
def Both.Tag.tag() -> String:
  "#" ++ Both.name()

# blend: nested-reach.blend:14
def Y.a() -> String:
  Outer2.name()

# blend: nested-reach.blend:27
def Y.b() -> String:
  Outer2.name()

# blend: nested-reach.blend:37
def Y.ab() -> String:
  Y.a() ++ "/" ++ Y.b()

# blend: nested-reach.blend:14
def W.a() -> String:
  Outer2.name()

# blend: nested-reach.blend:20
def W.tag() -> String:
  "#" ++ Outer3.name()

# blend: nested-reach.blend:41
def W.at() -> String:
  W.a() ++ W.tag()

# blend: nested-reach.blend:27
def W.b() -> String:
  Outer2.name()

# blend: nested-reach.blend:44
def main() -> IO(Unit):
  IO.print(Y.ab() ++ " " ++ Outer2.Sub.s() ++ " " ++ Outer3.Sub.s() ++ " " ++ Both.Inner.a() ++ " " ++ W.at())
