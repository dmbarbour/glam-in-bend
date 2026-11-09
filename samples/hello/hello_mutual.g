language g0

# Two top-level functions naming each other: `f ff` asks `h`, which asks
# `f` again, which answers.
tt t e = t
ff t e = e
f b = b "Hello, World!" (h ff)
h b = b "nope" (f tt)
asm.result = f ff
