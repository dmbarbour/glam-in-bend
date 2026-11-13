language g0

# `g`'s work needs `g`'s own value at the same place, `g` a
# function-valued cell kept live (cells-freeze.nested.self): a cycle,
# found when the copy of `g` in its own source is served at the place
# that waits
k x y = x
id x = x
g = k (g id ++ "")
use x = g x
asm.result = use ""
