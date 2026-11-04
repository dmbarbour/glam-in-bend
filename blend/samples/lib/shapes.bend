# Written by Blend from shapes.blend; do not edit.
import Base

# blend: shapes.blend:6
def twice(+n: U32) -> U32:
  (n * 2 : U32)

# blend: shapes.blend:15
def Square.side() -> U32:
  3

# blend: shapes.blend:11
def Square.perimeter() -> U32:
  twice(twice(Square.side()))
