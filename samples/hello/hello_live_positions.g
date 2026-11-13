language g0

# A function-valued cell is kept live, its work done once at each place
# it is needed (cells-freeze.cells). `g`'s first part needs `c`, which
# takes `g`'s second part: served at one place while the first waits on
# `c`, so no cycle.
pair a b f = f a b
first p = p (\a b -> a)
second p = p (\a b -> b)
k x y = x
g = k (pair (c ++ "!") ("Hello, " ++ "World"))
c = second (g "")
use x = first (g x)
asm.result = use ""
