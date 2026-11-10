language g0

# Closed work in a top-level function's body: `c2 c2 c2 id "!"` needs no
# argument, so however many times `f` is applied, it is done once. The
# ladder's sharing check applies `f` 1, 2, 4 and 8 times
# (glam/sharing.txt).
c2 h x = h (h x)
id x = x
f s = s ++ c2 c2 c2 id "!"
asm.result = f "Hello, World"
