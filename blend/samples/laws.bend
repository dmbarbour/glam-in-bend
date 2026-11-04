# Written by Blend from laws.blend; do not edit.
import Base

# blend: laws.blend:28
def NatAdd.T() -> Data: Nat

# blend: laws.blend:29
def NatAdd.zero() -> NatAdd.T():
  0n

# blend: laws.blend:31
def NatAdd.op(+a: NatAdd.T(), +b: NatAdd.T()) -> NatAdd.T():
  Nat.add(a, b)

# blend: laws.blend:16
def NatAdd.double(+x: NatAdd.T()) -> NatAdd.T():
  NatAdd.op(x, x)

# blend: laws.blend:55
def AnyOf.T() -> Data: Bool

# blend: laws.blend:56
def AnyOf.zero() -> AnyOf.T():
  False{}

# blend: laws.blend:58
def AnyOf.op(+a: AnyOf.T(), +b: AnyOf.T()) -> AnyOf.T():
  a || b

# blend: laws.blend:60
def AnyOf.double(+x: AnyOf.T()) -> AnyOf.T():
  x

# blend: laws.blend:75
def main() -> IO(Unit):
  IO.print(Nat.show(NatAdd.double(3n)) ++ " " ++ Bool.show(AnyOf.double(True{})))
