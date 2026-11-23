import Base
import ../spike/kprim.bend as P
import ./index.bend as X

# A copy's index of cursors (glam/index.bend; the Cells plan's
# cells-freeze.sharing.cursors.index): a situating node and cursors made
# in a fresh heap, put in the tree, found, taken out, the tree empty at
# the end; a key put twice an error, the tree unchanged. Run by
# scripts/ladder.py, which expects `ok` alone.
#
#   bend glam/test_index.bend

def sn.w(r: P.H & U32) -> P.H & U32:
  (h, +s) = r
  (P.wr(h, (s + 3 : U32), s), s)

# a situating node, its tree empty
def situ(h: P.H) -> P.H & U32:
  sn.w(P.node(h, P.hd2(18, 2, 0), 0))

# a cursor at position k
def cur.w(r: P.H & U32, +k: U32) -> P.H & U32:
  (h, +x) = r
  (P.wr(h, (x + 2 : U32), k), x)

def cur(h: P.H, +k: U32) -> P.H & U32:
  cur.w(P.node(h, P.hd2(18, 0, 0), 0), k)

def show_y(+same: Bool) -> String:
  match same:
    case True{}:
      "y"
    case False{}:
      "w"

def show_m(m: Maybe<&2, U32>, +want: U32) -> String:
  match m:
    case Some{+x}:
      show_y(U32.is_eq(x, want))
    case None{}:
      "n"

def look(r: P.H & Maybe<&2, U32>, +want: U32) -> P.H & String:
  (h, m) = r
  (h, show_m(m, want))

def errs.r(r: P.H & P.HS) -> U32:
  (h, hs) = r
  match hs:
    case P.HS{+itrs, +errs, +cap}:
      errs

def errs(h: P.H) -> U32:
  errs.r(P.stats(h))

def root.k(+same: Bool) -> String:
  match same:
    case True{}:
      "empty"
    case False{}:
      "not empty"

def root.r(r: P.H & U32, +s: U32) -> String:
  (h, +root) = r
  root.k(U32.is_eq(root, s))

# five cursors at positions sharing prefixes and not, each found; a
# position absent not found; the second and fourth taken out, the rest
# still found and those not; all taken out, the tree empty
type St is Type:
  St{h: P.H, +s: U32, +a: U32, +b: U32, +c: U32, +d: U32, +e: U32}

def build.e(r: P.H & U32, +s: U32, +a: U32, +b: U32, +c: U32, +d: U32) -> St:
  (h, +e) = r
  St{X.ix.insert(h, s, e), s, a, b, c, d, e}

def build.d(r: P.H & U32, +s: U32, +a: U32, +b: U32, +c: U32) -> St:
  (h, +d) = r
  build.e(cur(X.ix.insert(h, s, d), 37), s, a, b, c, d)

def build.c(r: P.H & U32, +s: U32, +a: U32, +b: U32) -> St:
  (h, +c) = r
  build.d(cur(X.ix.insert(h, s, c), 100), s, a, b, c)

def build.b(r: P.H & U32, +s: U32, +a: U32) -> St:
  (h, +b) = r
  build.c(cur(X.ix.insert(h, s, b), 33), s, a, b)

def build.a(r: P.H & U32, +s: U32) -> St:
  (h, +a) = r
  build.b(cur(X.ix.insert(h, s, a), 44), s, a)

def build.s(r: P.H & U32) -> St:
  (h, +s) = r
  build.a(cur(h, 40), s)

def build() -> St:
  build.s(situ(P.h_new()))

def f5.z(r: P.H & String, acc: String) -> String:
  (h, rz) = r
  acc ++ rz ++ " " ++ U32.show(errs(h))

def f5.e(r: P.H & String, acc: String, +s: U32) -> String:
  (h, re) = r
  f5.z(look(X.ix.find(h, s, 41), 0), acc ++ re)

def f5.d(r: P.H & String, acc: String, +s: U32, +e: U32) -> String:
  (h, rd) = r
  f5.e(look(X.ix.find(h, s, 37), e), acc ++ rd, s)

def f5.c(r: P.H & String, acc: String, +s: U32, +d: U32, +e: U32) -> String:
  (h, rc) = r
  f5.d(look(X.ix.find(h, s, 100), d), acc ++ rc, s, e)

def f5.b(r: P.H & String, ra: String, +s: U32, +c: U32, +d: U32, +e: U32) -> String:
  (h, rb) = r
  f5.c(look(X.ix.find(h, s, 33), c), ra ++ rb, s, d, e)

def f5.a(r: P.H & String, +s: U32, +b: U32, +c: U32, +d: U32, +e: U32) -> String:
  (h, ra) = r
  f5.b(look(X.ix.find(h, s, 44), b), ra, s, c, d, e)

def find5(st: St) -> String:
  match st:
    case St{h, +s, +a, +b, +c, +d, +e}:
      f5.a(look(X.ix.find(h, s, 40), a), s, b, c, d, e)

# b and d taken out
def removed(st: St) -> String:
  match st:
    case St{h, +s, +a, +b, +c, +d, +e}:
      find5(St{X.ix.remove(X.ix.remove(h, s, b), s, d), s, a, b, c, d, e})

def emp.k(r: P.H & U32, +s: U32) -> String:
  (h, +root) = r
  root.k(U32.is_eq(root, s)) ++ " " ++ U32.show(errs(h))

def emp.r(h: P.H, +s: U32) -> String:
  emp.k(P.rd(h, (s + 3 : U32)), s)

# all taken out
def emptied(st: St) -> String:
  match st:
    case St{h, +s, +a, +b, +c, +d, +e}:
      emp.r(X.ix.remove(X.ix.remove(X.ix.remove(X.ix.remove(X.ix.remove(h, s, c), s, a), s, e), s, b), s, d), s)

# a key put twice: an error, the tree unchanged, the first still found
def twice.f(r: P.H & String) -> String:
  (h, got) = r
  got ++ " " ++ U32.show(errs(h))

def twice.w(r: P.H & U32, +s: U32, +a: U32) -> String:
  (h, +x) = r
  twice.f(look(X.ix.find(X.ix.insert(h, s, x), s, 40), a))

def twice(st: St) -> String:
  match st:
    case St{h, +s, +a, +b, +c, +d, +e}:
      twice.w(cur(h, 40), s, a)

def home.k(+same: Bool) -> String:
  match same:
    case True{}:
      "home"
    case False{}:
      "lost"

def home.r(r: P.H & U32, +s: U32) -> String:
  (h, +x) = r
  home.k(U32.is_eq(x, s))

# a lone cursor's home, one read
def home(st: St) -> String:
  match st:
    case St{h, +s, +a, +b, +c, +d, +e}:
      home.r(X.ix.home(h, c), s)

def check.k(+same: Bool, got: String, want: String, name: String) -> String:
  match same:
    case True{}:
      ""
    case False{}:
      name ++ ": got " ++ got ++ ", want " ++ want ++ "\n"

def check(+got: String, +want: String, name: String) -> String:
  check.k(String.eq(got, want), got, want, name)

def report.k(+none: Bool, s: String) -> String:
  match none:
    case True{}:
      "ok"
    case False{}:
      s

def report(+s: String) -> String:
  report.k(String.eq(s, ""), s)

def main() -> String:
  report(
    check(find5(build()), "yyyyyn 0", "five found, one absent not") ++
    check(removed(build()), "ynynyn 0", "two taken out") ++
    check(emptied(build()), "empty 0", "all taken out") ++
    check(twice(build()), "y 1", "a key put twice") ++
    check(home(build()), "home", "a cursor's home"))
