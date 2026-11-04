# Written by Blend from shapes.blend; do not edit.
import Base
import ./units.bend as U

# blend: shapes.blend:9
type Dim is Data:
  Dim{+w: U32, +h: U32}

# blend: shapes.blend:12
def twice(+n: U32) -> U32:
  (n * 2 : U32)

# blend: shapes.blend:29
def Square.side() -> U32:
  3

# blend: shapes.blend:17
def Square.perimeter() -> U32:
  twice(twice(Square.side()))

# blend: shapes.blend:19
def Square.dims.of(+s: U32) -> Dim:
  Dim{s, s}

# blend: shapes.blend:21
def Square.area.of(d: Dim) -> U32:
  match d:
    case Dim{+w, +h}:
      U.cm2((w * h : U32))

# blend: shapes.blend:25
def Square.area() -> U32:
  Square.area.of(Square.dims.of(Square.side()))
