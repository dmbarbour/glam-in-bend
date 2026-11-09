language g0

# `x` needs its own value: a cycle, found when `f` demands it
x = x ++ "a"
f y = x
asm.result = f "q"
