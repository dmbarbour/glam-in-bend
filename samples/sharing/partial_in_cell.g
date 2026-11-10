language g0

# A partial application held in a root cell: `g`, a value the function
# `use` names, is `f id`, whose work `c2 c2 c2 id id` needs no further
# argument, so however many times `use` applies `g`, it is done once.
c2 h x = h (h x)
id x = x
k x y = x
f a = k (c2 c2 c2 id a)
g = f id
use x = g id x
asm.result = use "Hello, World!"
