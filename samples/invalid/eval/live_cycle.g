language g0

# `c` needs itself through the work kept in `g`, a function-valued cell
# kept live: a cycle, found when the same place in `g` is needed again
k x y = x
g = k (c ++ "!")
c = g ""
use x = g x
asm.result = use ""
