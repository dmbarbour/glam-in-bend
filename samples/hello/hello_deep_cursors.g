language g0

# The lazy list of hello_lazy_list.g folded from its end: each head's
# cursor stays open while the fold descends to the list's end, so the
# copy's ring holds the whole frontier at once, every crossing found
# among them (cells-freeze.sharing.cursors). The list is spelled
# backwards, the fold's appends reversing it again.
cons h t c n = c h (t c n)
nil c n = n
lit s = s ++ ""
cat h acc = acc ++ h
mk u = \f -> f (cons (lit "!") (cons (lit "d") (cons (lit "l") (cons (lit "r") (cons (lit "o") (cons (lit "W") (cons (lit " ") (cons (lit ",") (cons (lit "o") (cons (lit "l") (cons (lit "l") (cons (lit "e") (cons (lit "H") (nil))))))))))))))
g = mk ""
use x = g (\l -> l cat x)
asm.result = use ""
