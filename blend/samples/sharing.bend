# Written by Blend from sharing.blend; do not edit.
import Base

# blend: sharing.blend:10
def Arith.inc(+n: U32) -> U32:
  (n + 1 : U32)

# blend: sharing.blend:10
def Arith.inc.c1(+n: U32) -> U32:
  (n + 1 : U32)

# blend: sharing.blend:10
def Arith.inc.c2(+n: U32) -> U32:
  (n + 1 : U32)

# blend: sharing.blend:12
def Arith.show(+n: U32) -> String:
  U32.show(n)

# blend: sharing.blend:14
def Arith.twice(+n: U32) -> U32:
  Arith.inc.c1(Arith.inc.c2(n))

# blend: sharing.blend:16
def Arith.report(+n: U32) -> String:
  Arith.show(n) ++ " -> " ++ Arith.show(Arith.twice(n))

# blend: sharing.blend:19
def main() -> IO(Unit):
  IO.print(Arith.report(5))
