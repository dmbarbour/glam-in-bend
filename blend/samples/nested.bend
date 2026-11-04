# Written by Blend from nested.blend; do not edit.
import Base

def unit() -> String:
  "m"

def Outer.name() -> String:
  "outer"

def Outer.Inner.name() -> String:
  "inner"

def Outer.Inner.path() -> String:
  Outer.name() ++ "." ++ Outer.Inner.name() ++ "." ++ unit()

def main() -> IO(Unit):
  IO.print(Outer.Inner.path())
