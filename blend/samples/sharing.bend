# Written by Blend from sharing.blend; do not edit.
import Base

def Arith.inc.c1(+n: U32) -> U32:
  (n + 1 : U32)

def Arith.inc.c2(+n: U32) -> U32:
  (n + 1 : U32)

def Arith.show(+n: U32) -> String:
  U32.show(n)

def Arith.twice(+n: U32) -> U32:
  Arith.inc.c1(Arith.inc.c2(n))

def Arith.report(+n: U32) -> String:
  Arith.show(n) ++ " -> " ++ Arith.show(Arith.twice(n))

def main() -> IO(Unit):
  IO.print(Arith.report(5))
