# Written by Blend from family.blend; do not edit.
import Base

# blend: family.blend:20
def Plain.after(+n: U32) -> U32:
  n

# blend: family.blend:10
def Plain.step(+n: U32) -> U32:
  Plain.after((n * 2 : U32))

# blend: family.blend:12
def Plain.run(k: Nat, +n: U32) -> U32:
  match k:
    case 0n:
      n
    case 1n+p:
      Plain.run(p, Plain.step(n))

# blend: family.blend:24
def Counted.after(+n: U32) -> U32:
  (n + 1 : U32)

# blend: family.blend:10
def Counted.step(+n: U32) -> U32:
  Counted.after((n * 2 : U32))

# blend: family.blend:12
def Counted.run(k: Nat, +n: U32) -> U32:
  match k:
    case 0n:
      n
    case 1n+p:
      Counted.run(p, Counted.step(n))

# blend: family.blend:27
def main() -> IO(Unit):
  IO.print(U32.show(Plain.run(3n, 1)) ++ " " ++ U32.show(Counted.run(3n, 1)))
