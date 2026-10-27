import Base
import ./val.bend as V
import ./rules.bend as R
import ./tpl.bend as T

# Test nets with known results, built as templates: Church numerals
# applied to each other (where fan pairing decides the answer), a
# numeral applied to itself, and a long chain for throughput. They are
# built without levels, so their fans pair as static labels;
# spike/tools/terms.py lowers terms with levels.

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

def era() -> T.TNode:
  T.TN{R.KEraN{}, V.PNone{}}

def num(+n: U32) -> T.TNode:
  T.TN{R.KData{}, V.PVal{V.VNum{n}}}

def succ() -> T.TNode:
  T.TN{R.KData{}, V.PVal{V.VFun{1, 1, Nil{}}}}

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

