language g0

# `add` names a value, `suffix`, so it is linked into asm.result's net;
# `g` names no value, so it is a template, and may name itself.
tt t e = t
ff t e = e
suffix = "!"
add x = x ++ suffix
g b = b "Hello, World" (g tt)
asm.result = add (g ff)
