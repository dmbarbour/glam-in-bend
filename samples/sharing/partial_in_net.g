language g0

# The same partial application made inside one net: `run`'s `g` is
# `f id`, shared by fans wherever `run` applies it, so its work is done
# once. A control: templates share it as linking does.
c2 h x = h (h x)
id x = x
k x y = x
f a = k (c2 c2 c2 id a)
run g = g id "Hello, World!"
asm.result = run (f id)
