language g0

# A Scott-encoded list walked by a recursion through a lambda, each call
# spliced a level deeper than the last: each step once left a unit drop
# on the tail's wire, unfused, and each later step's controls crossed
# every one, quadratic in the list's length, until drops at one index
# fused into a run that a control crosses whole (the Cells plan's
# cells-recursion.depth, `drop-runs-fuse`). glam/growth.txt nests the
# list's `cons ""` 16, 32 and 64 deep and bounds what an element costs.
cons h t c n = c h t
nil c n = n
walk l = l (\h t -> walk t) ""
asm.result = walk (cons "" (nil)) ++ "Hello, World!"
