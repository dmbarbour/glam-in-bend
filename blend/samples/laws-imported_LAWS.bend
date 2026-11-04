# Written by Blend from laws-imported.blend; do not edit.
import Base
import ./lib/adds.bend as A
import ./laws-imported.bend as Blend_0

# blend: laws-imported.blend:12
law Zero.plus_zero_twice:
  for +x: Nat
  {Blend_0.Zero.plus(Blend_0.Zero.plus(x, Blend_0.Zero.zero()), Blend_0.Zero.zero()) == x : Nat}

# blend: lib/adds.blend:10
law Zero.plus_zero:
  for +x: Nat
  {Blend_0.Zero.plus(x, Blend_0.Zero.zero()) == x : Nat}

# blend: lib/adds.blend:10
law Again.plus_zero.Adds:
  for +x: Nat
  {Blend_0.Again.plus(x, Blend_0.Again.zero()) == x : Nat}

# blend: lib/adds.blend:10
law Again.plus_zero:
  for +x: Nat
  {Blend_0.Again.plus(x, Blend_0.Again.zero()) == x : Nat}
