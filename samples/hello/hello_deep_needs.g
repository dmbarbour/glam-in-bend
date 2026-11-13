language g0

# A function-valued cell whose kept work meets a need at each level of a
# nesting thirteen deep, each a call of a top-level function spliced in
# the cell's source. Each need is met on the spot, and the walk goes on
# where it stopped (cells-freeze.rewalk): the ladder checks that no step
# is walked again.
k x y = x
c x = x
g = k (c "H" ++ (c "e" ++ (c "l" ++ (c "l" ++ (c "o" ++ (c ", " ++ (c "W" ++ (c "o" ++ (c "r" ++ (c "l" ++ (c "d" ++ (c "!" ++ (c "" ++ "")))))))))))))
use x = g x
asm.result = use ""
