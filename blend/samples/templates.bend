# Written by Blend from templates.blend; do not edit.
import Base

# blend: templates.blend:23
def Twice.apply(~f: U32 -> U32, x: U32) -> U32:
  f(f(x))

# blend: templates.blend:25
def Twice.count(-A: Data, xs: List<&2, A>) -> U32:
  U32.from_nat(List.length(&2, A, xs))

# blend: templates.blend:15
def Twice.inc(x: U32) -> U32:
  (x + 1 : U32)

# blend: templates.blend:17
def Twice.bumped(x: U32) -> U32:
  Twice.apply(~Twice.inc, x)

# blend: templates.blend:19
def Twice.doubled(x: U32) -> U32:
  Twice.apply(~(y => (y * 2 : U32)), x)

# blend: templates.blend:28
def main() -> IO(Unit):
  IO.print(U32.show(Twice.bumped(1)) ++ " " ++ U32.show(Twice.doubled(1)) ++ " " ++ U32.show(Twice.count(U32, [7, 8])))
