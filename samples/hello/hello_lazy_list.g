language g0

# A function-valued cell holding a lazy list, walked by one use: each
# cons cell and each head a computation the source reduces where the
# copy first needs it, served through a cursor, about two serves an
# element, one open at a time (cells-freeze.sharing.cursors).
cons h t c n = c h (t c n)
nil c n = n
lit s = s ++ ""
cat h acc = h ++ acc
mk u = \f -> f (cons (lit "H") (cons (lit "e") (cons (lit "l") (cons (lit "l") (cons (lit "o") (cons (lit ",") (cons (lit " ") (cons (lit "W") (cons (lit "o") (cons (lit "r") (cons (lit "l") (cons (lit "d") (cons (lit "!") (nil))))))))))))))
g = mk ""
use x = g (\l -> l cat x)
asm.result = use ""
