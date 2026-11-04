# Written by Blend from family-nested.blend; do not edit.
import Base

# blend: family-nested.blend:9
def Outer.name() -> String:
  "outer"

# blend: family-nested.blend:12
def Outer.Inner.name() -> String:
  "inner"

# blend: family-nested.blend:14
def Outer.Inner.path() -> String:
  Outer.name() ++ "." ++ Outer.Inner.name()

# blend: family-nested.blend:18
def Outer2.name() -> String:
  "outer2"

# blend: family-nested.blend:21
def Outer2.Inner.name() -> String:
  "inner2"

# blend: family-nested.blend:14
def Outer2.Inner.path() -> String:
  Outer2.name() ++ "." ++ Outer2.Inner.name()

# blend: family-nested.blend:25
def Outer3.name() -> String:
  "outer3"

# blend: family-nested.blend:12
def Outer3.Inner.name() -> String:
  "inner"

# blend: family-nested.blend:14
def Outer3.Inner.path() -> String:
  Outer3.name() ++ "." ++ Outer3.Inner.name()

# blend: family-nested.blend:18
def Outer4.name() -> String:
  "outer2"

# blend: family-nested.blend:21
def Outer4.Inner.name.Outer2.Inner() -> String:
  "inner2"

# blend: family-nested.blend:30
def Outer4.Inner.name() -> String:
  Outer4.Inner.name.Outer2.Inner() ++ "+"

# blend: family-nested.blend:14
def Outer4.Inner.path() -> String:
  Outer4.name() ++ "." ++ Outer4.Inner.name()

# blend: family-nested.blend:33
def main() -> IO(Unit):
  IO.print(Outer.Inner.path() ++ " " ++ Outer2.Inner.path() ++ " " ++ Outer3.Inner.path() ++ " " ++ Outer4.Inner.path())
