language g0

# A copy of a live function served into another's source forces a cell
# whose work forces another, which uses that other source
# (cells-freeze.nested): `g`'s first part needs `p`'s work, which needs
# `q`, which needs `r`, which takes `g`'s second part. Forcing `q` gives
# back every source a frame holds, so `g` is served to `r` at another
# place while its first place waits: no cycle.
pick a b s = s a b
fst a b = a
snd a b = b
k x y = x
id x = x
g = pick ((p id) ++ "") "Hello, World!"
p = k (q ++ "")
q = r ++ ""
r = g snd
use x = k (g fst) x
asm.result = use ""
