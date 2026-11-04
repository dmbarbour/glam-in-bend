# Written by Blend from nested.blend; do not edit.
import Base

# blend: nested.blend:7
def unit() -> String:
  "m"

# blend: nested.blend:11
def Outer.name() -> String:
  "outer"

# blend: nested.blend:14
def Outer.Inner.name() -> String:
  "inner"

# blend: nested.blend:16
def Outer.Inner.path() -> String:
  Outer.name() ++ "." ++ Outer.Inner.name() ++ "." ++ unit()

# blend: nested.blend:19
def main() -> IO(Unit):
  IO.print(Outer.Inner.path())
