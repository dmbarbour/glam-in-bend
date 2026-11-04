# Written by Blend from laws-imported.blend; do not edit.
import Base
import ./lib/adds.bend as A

# blend: laws-imported.blend:10
def Zero.zero() -> Nat:
  0n

# blend: lib/adds.blend:8
def Zero.plus(+a: Nat, +b: Nat) -> Nat:
  Nat.add(a, b)

# blend: laws-imported.blend:20
def Again.zero() -> Nat:
  0n

# blend: lib/adds.blend:8
def Again.plus(+a: Nat, +b: Nat) -> Nat:
  Nat.add(a, b)

# blend: laws-imported.blend:25
def main() -> IO(Unit):
  IO.print(Nat.show(Zero.plus(2n, Again.plus(1n, Zero.zero()))))
