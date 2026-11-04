# Written by Blend from imports.blend; do not edit.
import Base
import ./lib/shapes.bend as S
import ./lib/units.bend as Blend_1

# blend: lib/shapes.blend:29
def Big.side.Square() -> U32:
  3

# blend: imports.blend:11
def Big.side() -> U32:
  (Big.side.Square() * 10 : U32)

# blend: lib/shapes.blend:17
def Big.perimeter() -> U32:
  S.twice(S.twice(Big.side()))

# blend: lib/shapes.blend:19
def Big.dims.of(+s: U32) -> S.Dim:
  S.Dim{s, s}

# blend: lib/shapes.blend:21
def Big.area.of(d: S.Dim) -> U32:
  match d:
    case S.Dim{+w, +h}:
      Blend_1.cm2((w * h : U32))

# blend: lib/shapes.blend:25
def Big.area() -> U32:
  Big.area.of(Big.dims.of(Big.side()))

# blend: imports.blend:14
def main() -> IO(Unit):
  IO.print(U32.show(S.Square.perimeter()) ++ " " ++ U32.show(Big.perimeter()) ++ " " ++ U32.show(Big.area()))
