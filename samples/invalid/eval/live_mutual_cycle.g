language g0

# `g`'s work needs `p`'s, which needs `g`'s at the same place, both
# function-valued cells kept live (cells-freeze.nested): a cycle, found
# when `g`'s source, held below, is given back and served at that place
# again
k x y = x
id x = x
g = k (p id ++ "")
p = k (g id ++ "")
use x = g x
asm.result = use ""
