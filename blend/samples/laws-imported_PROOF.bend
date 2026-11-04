# Written by Blend from laws-imported.blend; do not edit.
import Base
import ./lib/adds.bend as A
import ./laws-imported.bend as Blend_0
import ./laws-imported_LAWS.bend as Blend_Laws

# blend: lib/adds.blend:13
def Blend_Laws.Zero.plus_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Blend_Laws.Zero.plus_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# blend: laws-imported.blend:15
def Blend_Laws.Zero.plus_zero_twice(x):
  %Blend_Laws.Zero.plus_zero(x) : {Nat.add(Nat.add(x, 0n), 0n) == _ : Nat}
  Blend_Laws.Zero.plus_zero(Nat.add(x, 0n))

# blend: lib/adds.blend:13
def Blend_Laws.Again.plus_zero.Adds(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Blend_Laws.Again.plus_zero.Adds(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# blend: laws-imported.blend:22
def Blend_Laws.Again.plus_zero(x):
  Blend_Laws.Again.plus_zero.Adds(x)
