# Written by Blend from types.blend; do not edit.
import Base

# blend: types.blend:11
type Box<-A: Data> is Data:
  Box{+x: A}

# blend: types.blend:26
def Sum.S() -> Data: U32

# blend: types.blend:27
def Sum.start() -> Sum.S():
  7

# blend: types.blend:29
def Sum.add(+st: Sum.S(), +n: U32) -> Sum.S():
  (st + n : U32)

# blend: types.blend:31
def Sum.count(+st: Sum.S()) -> U32:
  st

# blend: types.blend:17
def Sum.Boxed() -> Data: Box<Sum.S()>

# blend: types.blend:18
def Sum.boxed(+n: U32) -> Sum.Boxed():
  Box{Sum.add(Sum.start(), n)}

# blend: types.blend:20
def Sum.total(b: Sum.Boxed()) -> U32:
  match b:
    case Box{+x}:
      Sum.count(x)

# blend: types.blend:35
def Seen.S() -> Data: List<&2, U32>

# blend: types.blend:36
def Seen.start() -> Seen.S():
  [1, 2]

# blend: types.blend:38
def Seen.add(+st: Seen.S(), +n: U32) -> Seen.S():
  Con{n, st}

# blend: types.blend:40
def Seen.count(st: Seen.S()) -> U32:
  U32.from_nat(List.length(&2, U32, st))

# blend: types.blend:17
def Seen.Boxed() -> Data: Box<Seen.S()>

# blend: types.blend:18
def Seen.boxed(+n: U32) -> Seen.Boxed():
  Box{Seen.add(Seen.start(), n)}

# blend: types.blend:20
def Seen.total(b: Seen.Boxed()) -> U32:
  match b:
    case Box{+x}:
      Seen.count(x)

# blend: types.blend:43
def main() -> IO(Unit):
  IO.print(U32.show(Sum.total(Sum.boxed(5))) ++ " " ++ U32.show(Seen.total(Seen.boxed(5))))
