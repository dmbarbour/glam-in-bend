language g0

# A function-valued cell whose work erases its arguments: `g`, a value
# the function `use` names, is `f id`, whose four arguments `k` drops
# once applied. The first use reduces `g`'s body in its source, where
# each dropped argument leaves its binder facing a static; every later
# use serves that body again, each static frozen as an eraser node and
# made static again where it is spliced
# (cells-freeze.nested.host.splice.single).
k x y = x
id x = x
c2 h x = h (h x)
f a x1 x2 x3 x4 = k (k (k (k (c2 c2 c2 id a) x1) x2) x3) x4
g = f id
use x = g x x x x x
asm.result = use "Hello, World!"
