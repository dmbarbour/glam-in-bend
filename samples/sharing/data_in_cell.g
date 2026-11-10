language g0

# A data-valued cell: `w`, a value the function `f` names, is computed
# once, where `f` first needs it, and kept. A control.
c2 h x = h (h x)
id x = x
w = c2 c2 c2 id "!"
f s = s ++ w
asm.result = f "Hello, World"
