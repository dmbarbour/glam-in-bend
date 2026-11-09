language g0

# A top-level function that names itself. Conditionals are effects, not
# built yet, so Church booleans choose: `g ff` takes its second branch,
# `g tt`, which takes its first; the recursive call in that copy of `g`
# is never demanded.
tt t e = t
ff t e = e
g b = b "Hello, World!" (g tt)
asm.result = g ff
