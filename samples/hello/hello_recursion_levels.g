language g0

# Top-level functions applied inside boxes: `twice` applies its argument,
# a lambda whose body applies `g` a level deeper than asm.result's own
# applications, so each copy of `g` is raised to the level where it is
# applied.
tt t e = t
ff t e = e
g b = b "Hello, World" (g tt)
twice f = f "!"
asm.result = twice (\p -> g ff ++ p)
