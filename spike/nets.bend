import Base
import ./val.bend as V
import ./rules.bend as R
import ./tpl.bend as T

# Test nets with known results, built as templates: Church numerals
# applied to each other (where fan pairing decides the answer), a
# numeral applied to itself, and a long chain for throughput. Most are
# built without levels, so their fans pair as static labels; t_pow_lvl is
# built with them, as spike/tools/terms.py lowers terms.

def l(+a: U32, +pa: U32, +b: U32, +pb: U32) -> T.TLink:
  T.TL{T.TE{a, pa}, T.TE{b, pb}}

def fn() -> T.TNode:
  T.TN{R.KFn{}, V.PNone{}}

def ap() -> T.TNode:
  T.TN{R.KAp{}, V.PNone{}}

def cp(+site: U32) -> T.TNode:
  T.TF{R.KCopy{}, site, V.nolvl()}

# with levels (spike/tools/terms.py lowers terms with them)
def fnl(+n: U32) -> T.TNode:
  T.TN{R.KFn{}, V.PLvl{n}}

def apl(+n: U32) -> T.TNode:
  T.TN{R.KAp{}, V.PLvl{n}}

def cpl(+site: U32, +n: U32) -> T.TNode:
  T.TF{R.KCopy{}, site, n}

def br(+n: U32) -> T.TNode:
  T.TN{R.KLift{}, V.PLift{n, True{}, 1}}

def cr(+n: U32) -> T.TNode:
  T.TN{R.KLift{}, V.PLift{n, False{}, 1}}

# a fused control: levels above n move up by `by`, or down by it
def ctl(+n: U32, +up: Bool, +by: U32) -> T.TNode:
  T.TN{R.KLift{}, V.PLift{n, up, by}}

# a control facing consumers
def ctlc(+n: U32, +up: Bool, +by: U32) -> T.TNode:
  T.TN{R.KLiftC{}, V.PLift{n, up, by}}

def era() -> T.TNode:
  T.TN{R.KEraN{}, V.PNone{}}

def num(+n: U32) -> T.TNode:
  T.TN{R.KData{}, V.PVal{V.VNum{n}}}

def succ() -> T.TNode:
  T.TN{R.KData{}, V.PVal{V.VFun{1, 1, Nil{}}}}

# the builtin add, curried: two arguments
def plus() -> T.TNode:
  T.TN{R.KData{}, V.PVal{V.VFun{2, 2, Nil{}}}}

# the builtin fma, a * b + c, curried: three arguments
def fma() -> T.TNode:
  T.TN{R.KData{}, V.PVal{V.VFun{3, 3, Nil{}}}}

def sel(b: Bool, +x: U32, +y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

# A Church numeral n >= 1, \f -> \x -> f (... (f x)), at node offset b:
# F b, X b+1, copies b+2 .. b+n, applications b+n+1 .. b+2n. Its exposed
# port is F's principal. Copies take sites site .. site+n-2.
def copies(n: Nat, +site: U32) -> List<&2, T.TNode>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      cp(site) <> copies(p, (site + 1 : U32))

def aps(n: Nat) -> List<&2, T.TNode>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      ap() <> aps(p)

def numeral_nodes(+n: U32, +site: U32) -> List<&2, T.TNode>:
  List.append(&2, T.TNode, [fn(), fn()], List.append(&2, T.TNode, copies(U32.to_nat((n - 1 : U32)), site), aps(U32.to_nat(n))))

def copy_links(n: Nat, +k: U32, +nn: U32, +b: U32) -> List<&2, T.TLink>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      l(((b + 1 : U32) + k : U32), 1, ((b + nn : U32) + k : U32), 0) <>
      l(((b + 1 : U32) + k : U32), 2, sel(U32.is_eq(k, (nn - 1 : U32)), ((b + nn : U32) + nn : U32), ((b + 2 : U32) + k : U32)), 0) <>
      copy_links(p, (k + 1 : U32), nn, b)

def app_links(n: Nat, +k: U32, +nn: U32, +b: U32) -> List<&2, T.TLink>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      l(((b + nn : U32) + k : U32), 1, sel(U32.is_eq(k, nn), (b + 1 : U32), (((b + nn : U32) + k : U32) + 1 : U32)), 2) <>
      app_links(p, (k + 1 : U32), nn, b)

def numeral_links(+n: U32, +b: U32) -> List<&2, T.TLink>:
  List.append(&2, T.TLink,
    [l(b, 1, (b + 1 : U32), 0), l(b, 2, (b + 2 : U32), 0), l(((b + n : U32) + 1 : U32), 2, (b + 1 : U32), 1)],
    List.append(&2, T.TLink, copy_links(U32.to_nat((n - 1 : U32)), 1, n, b), app_links(U32.to_nat(n), 1, n, b)))

def nsize(+n: U32) -> U32:
  ((2 * n : U32) + 1 : U32)

# m n succ 0: numeral m at 0, numeral n after it, then the applications
def t_pow(+m: U32, +n: U32) -> T.Tpl:
  +b = nsize(m)
  +c = (b + nsize(n) : U32)
  T.Tpl{List.append(&2, T.TNode, numeral_nodes(m, 1), List.append(&2, T.TNode, numeral_nodes(n, 100),
      [ap(), ap(), succ(), ap(), num(0)])),
    List.append(&2, T.TLink, numeral_links(m, 0), List.append(&2, T.TLink, numeral_links(n, b),
      [l(c, 0, 0, 0), l(c, 1, b, 0), l(c, 2, (c + 1 : U32), 0), l((c + 1 : U32), 1, (c + 2 : U32), 0),
       l((c + 1 : U32), 2, (c + 3 : U32), 0), l((c + 3 : U32), 1, (c + 4 : U32), 0)])),
    T.TE{(c + 3 : U32), 2}, (c + 5 : U32)}

# m n (plus 1) 0: as t_pow, but adding 1 by a partial application of
# the builtin add, which every copy duplicates and every call consumes
def t_pow_plus(+m: U32, +n: U32) -> T.Tpl:
  +b = nsize(m)
  +c = (b + nsize(n) : U32)
  T.Tpl{List.append(&2, T.TNode, numeral_nodes(m, 1), List.append(&2, T.TNode, numeral_nodes(n, 100),
      [ap(), ap(), ap(), ap(), num(0), plus(), num(1)])),
    List.append(&2, T.TLink, numeral_links(m, 0), List.append(&2, T.TLink, numeral_links(n, b),
      [l(c, 0, 0, 0), l(c, 1, b, 0), l(c, 2, (c + 1 : U32), 0), l((c + 1 : U32), 1, (c + 2 : U32), 2),
       l((c + 2 : U32), 0, (c + 5 : U32), 0), l((c + 2 : U32), 1, (c + 6 : U32), 0),
       l((c + 1 : U32), 2, (c + 3 : U32), 0), l((c + 3 : U32), 1, (c + 4 : U32), 0)])),
    T.TE{(c + 3 : U32), 2}, (c + 7 : U32)}

# A Church numeral n >= 2 with levels, as spike/tools/terms.py lowers it
# under lv boxes, at node offset b: F b, X b+1, applications b+2 ..
# b+n+1 at levels lv .. lv+n-1, a control raising x by n-1 into the
# innermost, then for each fan i < n-1 (level lv+i, site site+i) the fan,
# a control lowering its first copy into application i and, but for the
# last fan, one raising its second into the next fan, which the last
# feeds to the innermost application directly. Exposed: F's principal.
def lnum_aps(n: Nat, +lv: U32) -> List<&2, T.TNode>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      apl(lv) <> lnum_aps(p, (lv + 1 : U32))

def lnum_up(b: Bool, +n: U32, rest: List<&2, T.TNode>) -> List<&2, T.TNode>:
  match b:
    case True{}:
      ctl(n, True{}, 1) <> rest
    case False{}:
      rest

def lnum_fans(n: Nat, +i: U32, +last: U32, +lv: U32, +site: U32) -> List<&2, T.TNode>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      cpl((site + i : U32), (lv + i : U32)) <> ctl((lv + i : U32), False{}, 1) <>
        lnum_up(U32.is_lt(i, last), (lv + i : U32), lnum_fans(p, (i + 1 : U32), last, lv, site))

def lnum_nodes(+n: U32, +lv: U32, +site: U32) -> List<&2, T.TNode>:
  List.append(&2, T.TNode, [fnl(lv), fnl(lv)], List.append(&2, T.TNode, lnum_aps(U32.to_nat(n), lv),
    ctl(lv, True{}, (n - 1 : U32)) <> lnum_fans(U32.to_nat((n - 1 : U32)), 0, (n - 2 : U32), lv, site)))

def lnum_second(more: Bool, +f: U32, +last: U32, rest: List<&2, T.TLink>) -> List<&2, T.TLink>:
  match more:
    case True{}:
      l(f, 2, (f + 2 : U32), 0) <> l((f + 2 : U32), 1, (f + 3 : U32), 0) <> rest
    case False{}:
      l(f, 2, last, 0) <> rest

# fan i of numeral n at b sits at b + n + 3 + 3i
def lnum_fan_links(k: Nat, +i: U32, +n: U32, +b: U32) -> List<&2, T.TLink>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      +f = (((b + n : U32) + 3 : U32) + (3 * i : U32) : U32)
      l(f, 1, (f + 1 : U32), 0) <> l((f + 1 : U32), 1, ((b + 2 : U32) + i : U32), 0) <>
        lnum_second(U32.is_lt(i, (n - 2 : U32)), f, ((b + n : U32) + 1 : U32), lnum_fan_links(p, (i + 1 : U32), n, b))

def lnum_app_links(k: Nat, +i: U32, +b: U32) -> List<&2, T.TLink>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      l(((b + 3 : U32) + i : U32), 2, ((b + 2 : U32) + i : U32), 1) <> lnum_app_links(p, (i + 1 : U32), b)

def lnum_links(+n: U32, +b: U32) -> List<&2, T.TLink>:
  List.append(&2, T.TLink, lnum_app_links(U32.to_nat((n - 1 : U32)), 0, b),
    List.append(&2, T.TLink,
      [l((b + 2 : U32), 2, (b + 1 : U32), 1), l((b + 1 : U32), 2, ((b + n : U32) + 2 : U32), 0),
       l(((b + n : U32) + 2 : U32), 1, ((b + n : U32) + 1 : U32), 1), l((b + 1 : U32), 0, b, 1),
       l(b, 2, ((b + n : U32) + 3 : U32), 0)],
      lnum_fan_links(U32.to_nat((n - 1 : U32)), 0, n, b)))

def lnum_size(+n: U32) -> U32:
  ((4 * n : U32) - 1 : U32)

# m n succ 0 with levels (m, n >= 2), as terms.py lowers `#m #n succ 0`:
# the applications at 0 .. 2, numeral m, numeral n a box deeper
def t_pow_lvl(+m: U32, +n: U32) -> T.Tpl:
  +b = (lnum_size(m) + 3 : U32)
  +c = (b + lnum_size(n) : U32)
  T.Tpl{List.append(&2, T.TNode, [apl(0), apl(0), apl(0)], List.append(&2, T.TNode, lnum_nodes(m, 0, 1),
      List.append(&2, T.TNode, lnum_nodes(n, 1, m), [succ(), num(0)]))),
    List.append(&2, T.TLink, lnum_links(m, 3), List.append(&2, T.TLink, lnum_links(n, b),
      [l(3, 0, 2, 0), l(b, 0, 2, 1), l(2, 2, 1, 0), l(c, 0, 1, 1), l(1, 2, 0, 0), l((c + 1 : U32), 0, 0, 1)])),
    T.TE{0, 2}, (c + 2 : U32)}

# m n (fma 1 1) 0: as t_pow, adding 1 as 1 * 1 + x by a partial
# application that holds two numbers, too many for a node: a data table
# entry, which every copy duplicates and every call consumes
def t_pow_fma(+m: U32, +n: U32) -> T.Tpl:
  +b = nsize(m)
  +c = (b + nsize(n) : U32)
  T.Tpl{List.append(&2, T.TNode, numeral_nodes(m, 1), List.append(&2, T.TNode, numeral_nodes(n, 100),
      [ap(), ap(), ap(), ap(), num(0), fma(), num(1), ap(), num(1)])),
    List.append(&2, T.TLink, numeral_links(m, 0), List.append(&2, T.TLink, numeral_links(n, b),
      [l(c, 0, 0, 0), l(c, 1, b, 0), l(c, 2, (c + 1 : U32), 0), l((c + 1 : U32), 1, (c + 2 : U32), 2),
       l((c + 2 : U32), 0, (c + 7 : U32), 2), l((c + 2 : U32), 1, (c + 6 : U32), 0),
       l((c + 7 : U32), 0, (c + 5 : U32), 0), l((c + 7 : U32), 1, (c + 8 : U32), 0),
       l((c + 1 : U32), 2, (c + 3 : U32), 0), l((c + 3 : U32), 1, (c + 4 : U32), 0)])),
    T.TE{(c + 3 : U32), 2}, (c + 9 : U32)}

# two (two two) succ 0
def t_two_two_two() -> T.Tpl:
  +b = nsize(2)
  +c = (b + b : U32)
  +d = (c + b : U32)
  T.Tpl{List.append(&2, T.TNode, numeral_nodes(2, 1), List.append(&2, T.TNode, numeral_nodes(2, 100),
      List.append(&2, T.TNode, numeral_nodes(2, 200), [ap(), ap(), ap(), succ(), ap(), num(0)]))),
    List.append(&2, T.TLink, numeral_links(2, 0), List.append(&2, T.TLink, numeral_links(2, b),
      List.append(&2, T.TLink, numeral_links(2, c),
        [l(d, 0, b, 0), l(d, 1, c, 0), l(d, 2, (d + 1 : U32), 1),
         l((d + 1 : U32), 0, 0, 0), l((d + 1 : U32), 2, (d + 2 : U32), 0), l((d + 2 : U32), 1, (d + 3 : U32), 0),
         l((d + 2 : U32), 2, (d + 4 : U32), 0), l((d + 4 : U32), 1, (d + 5 : U32), 0)]))),
    T.TE{(d + 4 : U32), 2}, (d + 6 : U32)}

# (\t -> t t) n succ 0: one numeral, duplicated by a fan
def t_self(+n: U32) -> T.Tpl:
  +b = nsize(n)
  T.Tpl{List.append(&2, T.TNode, numeral_nodes(n, 100), [fn(), cp(9), ap(), ap(), ap(), succ(), ap(), num(0)]),
    List.append(&2, T.TLink, numeral_links(n, 0),
      [l(b, 2, (b + 1 : U32), 0), l((b + 1 : U32), 1, (b + 2 : U32), 0), l((b + 1 : U32), 2, (b + 2 : U32), 1),
       l((b + 2 : U32), 2, b, 1),
       l((b + 3 : U32), 0, b, 0), l((b + 3 : U32), 1, 0, 0), l((b + 3 : U32), 2, (b + 4 : U32), 0),
       l((b + 4 : U32), 1, (b + 5 : U32), 0), l((b + 4 : U32), 2, (b + 6 : U32), 0), l((b + 6 : U32), 1, (b + 7 : U32), 0)]),
    T.TE{(b + 6 : U32), 2}, (b + 8 : U32)}

# n succ 0, for throughput: n uses of succ in one numeral
def t_chain(+n: U32) -> T.Tpl:
  +b = nsize(n)
  T.Tpl{List.append(&2, T.TNode, numeral_nodes(n, 1), [ap(), succ(), ap(), num(0)]),
    List.append(&2, T.TLink, numeral_links(n, 0),
      [l(b, 0, 0, 0), l(b, 1, (b + 1 : U32), 0), l(b, 2, (b + 2 : U32), 0), l((b + 2 : U32), 1, (b + 3 : U32), 0)]),
    T.TE{(b + 2 : U32), 2}, (b + 4 : U32)}

