language g0

# Live functions whose work applies another (the Cells plan's
# cells-freeze.nested): `p` holds work, `c2 c2 c2 id id`, and each
# `g{i}`, a function-valued cell of its own, applies `p` in its work.
# Each added `g{i}` should cost little more than it does linked, `p`'s
# work done once however many sources need it.
c2 h x = h (h x)
id x = x
k x y = x
f a = k (c2 c2 c2 id a)
p = f id
g{i} = k (p id)
use x = g{i} x "Hello, World!"
asm.result = use ""
