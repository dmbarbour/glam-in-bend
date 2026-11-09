language g0

# The values a top-level function names are cells: `bang` is computed
# once, where `shout` first needs it, and `hello`, whose value is a
# function, is spliced where it is applied, as a top-level function is.
add x y = x ++ y
hello = add "Hello, "
bang = "!"
shout x = hello (x ++ bang)
asm.result = shout "World"
