# Written by Blend from declares.blend; do not edit.
import Base

# blend: declares.blend:19
def Listed.S() -> Data: List<&2, U32>

# blend: declares.blend:20
def Listed.empty() -> Listed.S():
  Nil{}

# blend: declares.blend:22
def Listed.push(st: Listed.S(), +x: U32) -> Listed.S():
  Con{x, st}

# blend: declares.blend:24
def Listed.size(st: Listed.S()) -> U32:
  U32.from_nat(List.length(&2, U32, st))

# blend: declares.blend:15
def Listed.one(+x: U32) -> Listed.S():
  Listed.push(Listed.empty(), x)

# blend: declares.blend:28
def Counted.S() -> Data: U32

# blend: declares.blend:29
def Counted.empty() -> Counted.S():
  0

# blend: declares.blend:31
def Counted.push(+st: Counted.S(), +x: U32) -> Counted.S():
  (st + x : U32)

# blend: declares.blend:33
def Counted.size(+st: Counted.S()) -> U32:
  st

# blend: declares.blend:15
def Counted.one(+x: U32) -> Counted.S():
  Counted.push(Counted.empty(), x)

# blend: declares.blend:36
def main() -> IO(Unit):
  IO.print(U32.show(Listed.size(Listed.one(5))) ++ " " ++ U32.show(Counted.size(Counted.one(5))))
