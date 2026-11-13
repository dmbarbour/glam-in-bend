language g0

# A live function whose kept work applies another to its argument
# (cells-freeze.nested): `g`'s source holds a copy of `p`, a live
# function too, and the argument a use passes into `g`'s source passes on
# into `p`'s, through the cursors that copy chains in `g`'s source. The
# application in `g`'s source leaves the place a use's copy holds facing
# one of those cursors, served there before `g` is.
k x y = x
p = (\a s -> a ++ s) "Hello, "
g = (\a y -> p y) ""
use x = k (g "World!") x
asm.result = use ""
