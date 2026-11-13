language g0

# A live function whose kept work uses its own value
# (cells-freeze.nested.self, self-copies-are-cursors): `g`'s first part
# takes `g`'s second part from a copy of `g` in its own source, served
# there from itself at another place than the one waiting: no cycle.
k x y = x
pick a b s = s a b
fst a b = a
snd a b = b
g = pick ((g snd) ++ "") "Hello, World!"
use x = k (g fst) x
asm.result = use ""
