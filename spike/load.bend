import Base
import ./tpl.bend as T
import ./nets.bend as X

# Loading nets (heap-strategies.measure.loader): a program built once
# reads its nets from a file at run time (spike/runterms.bend), where a
# program with its nets compiled in is built for each set, the spike
# compiled again each time. The file is decimal numbers apart by anything
# else; spike/tools/terms.py writes it. A file of n rows is n, then each
# row: the value wanted (2^32 - 1 for none); the name's length and its
# characters' codes; the nodes' count and each node, its tag and then its
# fields; the links' count and each link, a node and its port, then
# another; the exposed port, a node and its port.
#
# Node tags, after nets.bend's constructors: 0 fn, 1 fnl n, 2 ap, 3 apl
# n, 4 cp site, 5 cpl site n, 6 ctl n up by, 7 ctlc n up by (up 1 for a
# raise), 8 era, 9 num v, 10 succ, 11 plus, 12 fma, 13 void.

# Numbers
# =======

def is_digit(+b: U32) -> Bool:
  U32.is_ge(b, 48) && U32.is_lt(b, 58)

def nums.push(+end: Bool, +acc: U32, out: List<&2, U32>) -> List<&2, U32>:
  match end:
    case True{}:
      Con{acc, out}
    case False{}:
      out

def nums.acc(+d: Bool, +b: U32, +acc: U32) -> U32:
  match d:
    case True{}:
      ((acc * 10 : U32) + (b - 48 : U32) : U32)
    case False{}:
      0

# the numbers in a file's bytes, in a digit's run acc so far: a number
# ends where something else follows a digit
def nums.go(bs: List<&2, U32>, +acc: U32, +in: Bool, out: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      List.reverse(&2, U32, nums.push(in, acc, out))
    case Con{+b, t}:
      nums.go(t, nums.acc(is_digit(b), b, acc), is_digit(b), nums.push(in && Bool.not(is_digit(b)), acc, out))

# the next number, 0 past the end
def take(ts: List<&2, U32>) -> U32 & List<&2, U32>:
  match ts:
    case Nil{}:
      (0, Nil{})
    case Con{+x, t}:
      (x, t)

# Nets
# ====
#
# A bind takes apart a parameter only, so each field read is a step of
# its own, given the last step's number and the rest.

def node.fnl(r: U32 & List<&2, U32>) -> T.TNode & List<&2, U32>:
  (+n, t) = r
  (X.fnl(n), t)

def node.apl(r: U32 & List<&2, U32>) -> T.TNode & List<&2, U32>:
  (+n, t) = r
  (X.apl(n), t)

def node.cp(r: U32 & List<&2, U32>) -> T.TNode & List<&2, U32>:
  (+s, t) = r
  (X.cp(s), t)

def node.cpl.n(+s: U32, r: U32 & List<&2, U32>) -> T.TNode & List<&2, U32>:
  (+n, t) = r
  (X.cpl(s, n), t)

def node.cpl(r: U32 & List<&2, U32>) -> T.TNode & List<&2, U32>:
  (+s, t) = r
  node.cpl.n(s, take(t))

def node.num(r: U32 & List<&2, U32>) -> T.TNode & List<&2, U32>:
  (+v, t) = r
  (X.num(v), t)

# a control, or with c false a co-control
def node.ctl.mk(c: Bool, +n: U32, +up: Bool, +by: U32) -> T.TNode:
  match c:
    case True{}:
      X.ctl(n, up, by)
    case False{}:
      X.ctlc(n, up, by)

def node.ctl.by(c: Bool, +n: U32, +up: U32, r: U32 & List<&2, U32>) -> T.TNode & List<&2, U32>:
  (+by, t) = r
  (node.ctl.mk(c, n, U32.is_ne(up, 0), by), t)

def node.ctl.up(c: Bool, +n: U32, r: U32 & List<&2, U32>) -> T.TNode & List<&2, U32>:
  (+up, t) = r
  node.ctl.by(c, n, up, take(t))

def node.ctl(c: Bool, r: U32 & List<&2, U32>) -> T.TNode & List<&2, U32>:
  (+n, t) = r
  node.ctl.up(c, n, take(t))

def node.k(+tag: U32, ts: List<&2, U32>) -> T.TNode & List<&2, U32>:
  match tag:
    case 0:
      (X.fn(), ts)
    case 1:
      node.fnl(take(ts))
    case 2:
      (X.ap(), ts)
    case 3:
      node.apl(take(ts))
    case 4:
      node.cp(take(ts))
    case 5:
      node.cpl(take(ts))
    case 6:
      node.ctl(True{}, take(ts))
    case 7:
      node.ctl(False{}, take(ts))
    case 8:
      (X.era(), ts)
    case 9:
      node.num(take(ts))
    case 10:
      (X.succ(), ts)
    case 11:
      (X.plus(), ts)
    case 13:
      (X.void(), ts)
    case _:
      (X.fma(), ts)

def node(ts: List<&2, U32>) -> T.TNode & List<&2, U32>:
  match ts:
    case Nil{}:
      (X.era(), Nil{})
    case Con{+tag, t}:
      node.k(tag, t)

def nodes.add(acc: List<&2, T.TNode>, r: T.TNode & List<&2, U32>) -> List<&2, T.TNode> & List<&2, U32>:
  (x, t) = r
  (Con{x, acc}, t)

def nodes.fin(st: List<&2, T.TNode> & List<&2, U32>) -> List<&2, T.TNode> & List<&2, U32>:
  (acc, ts) = st
  (List.reverse(&2, T.TNode, acc), ts)

def nodes.step(st: List<&2, T.TNode> & List<&2, U32>) -> List<&2, T.TNode> & List<&2, U32>:
  (acc, ts) = st
  nodes.add(acc, node(ts))

# n more nodes, st the nodes so far, reversed, and the rest
def nodes.go(n: Nat, st: List<&2, T.TNode> & List<&2, U32>) -> List<&2, T.TNode> & List<&2, U32>:
  match n:
    case 0n:
      nodes.fin(st)
    case 1n+p:
      nodes.go(p, nodes.step(st))

def link.d(+a: U32, +pa: U32, +b: U32, r: U32 & List<&2, U32>) -> T.TLink & List<&2, U32>:
  (+pb, t) = r
  (X.l(a, pa, b, pb), t)

def link.c(+a: U32, +pa: U32, r: U32 & List<&2, U32>) -> T.TLink & List<&2, U32>:
  (+b, t) = r
  link.d(a, pa, b, take(t))

def link.b(+a: U32, r: U32 & List<&2, U32>) -> T.TLink & List<&2, U32>:
  (+pa, t) = r
  link.c(a, pa, take(t))

def link.a(r: U32 & List<&2, U32>) -> T.TLink & List<&2, U32>:
  (+a, t) = r
  link.b(a, take(t))

def links.add(acc: List<&2, T.TLink>, r: T.TLink & List<&2, U32>) -> List<&2, T.TLink> & List<&2, U32>:
  (x, t) = r
  (Con{x, acc}, t)

def links.fin(st: List<&2, T.TLink> & List<&2, U32>) -> List<&2, T.TLink> & List<&2, U32>:
  (acc, ts) = st
  (List.reverse(&2, T.TLink, acc), ts)

def links.step(st: List<&2, T.TLink> & List<&2, U32>) -> List<&2, T.TLink> & List<&2, U32>:
  (acc, ts) = st
  links.add(acc, link.a(take(ts)))

def links.go(n: Nat, st: List<&2, T.TLink> & List<&2, U32>) -> List<&2, T.TLink> & List<&2, U32>:
  match n:
    case 0n:
      links.fin(st)
    case 1n+p:
      links.go(p, links.step(st))

def name.add(acc: List<&2, Char>, r: U32 & List<&2, U32>) -> List<&2, Char> & List<&2, U32>:
  (+c, t) = r
  (Con{Char.from_u32(c), acc}, t)

def name.fin(st: List<&2, Char> & List<&2, U32>) -> String & List<&2, U32>:
  (acc, ts) = st
  (String.from_list(List.reverse(&2, Char, acc)), ts)

def name.step(st: List<&2, Char> & List<&2, U32>) -> List<&2, Char> & List<&2, U32>:
  (acc, ts) = st
  name.add(acc, take(ts))

def name.go(n: Nat, st: List<&2, Char> & List<&2, U32>) -> String & List<&2, U32>:
  match n:
    case 0n:
      name.fin(st)
    case 1n+p:
      name.go(p, name.step(st))

# Rows
# ====

# a net, the value its reduction must reach, and its name
type Row is Data:
  Row{t: T.Tpl, +want: U32, name: String}

def row.rp(+want: U32, name: String, +nn: U32, ns: List<&2, T.TNode>, ls: List<&2, T.TLink>, +rn: U32, r: U32 & List<&2, U32>) -> Row & List<&2, U32>:
  (+rp, t) = r
  (Row{T.Tpl{ns, ls, T.TE{rn, rp}, nn}, want, name}, t)

def row.rn(+want: U32, name: String, +nn: U32, ns: List<&2, T.TNode>, ls: List<&2, T.TLink>, r: U32 & List<&2, U32>) -> Row & List<&2, U32>:
  (+rn, t) = r
  row.rp(want, name, nn, ns, ls, rn, take(t))

def row.ls(+want: U32, name: String, +nn: U32, ns: List<&2, T.TNode>, r: List<&2, T.TLink> & List<&2, U32>) -> Row & List<&2, U32>:
  (ls, t) = r
  row.rn(want, name, nn, ns, ls, take(t))

def row.nk(+want: U32, name: String, +nn: U32, ns: List<&2, T.TNode>, r: U32 & List<&2, U32>) -> Row & List<&2, U32>:
  (+nk, t) = r
  row.ls(want, name, nn, ns, links.go(U32.to_nat(nk), (Nil{}, t)))

def row.ns(+want: U32, name: String, +nn: U32, r: List<&2, T.TNode> & List<&2, U32>) -> Row & List<&2, U32>:
  (ns, t) = r
  row.nk(want, name, nn, ns, take(t))

def row.nn(+want: U32, name: String, r: U32 & List<&2, U32>) -> Row & List<&2, U32>:
  (+nn, t) = r
  row.ns(want, name, nn, nodes.go(U32.to_nat(nn), (Nil{}, t)))

def row.name(+want: U32, r: String & List<&2, U32>) -> Row & List<&2, U32>:
  (name, t) = r
  row.nn(want, name, take(t))

def row.nl(+want: U32, r: U32 & List<&2, U32>) -> Row & List<&2, U32>:
  (+nl, t) = r
  row.name(want, name.go(U32.to_nat(nl), (Nil{}, t)))

def row.want(r: U32 & List<&2, U32>) -> Row & List<&2, U32>:
  (+want, t) = r
  row.nl(want, take(t))

def rows.add(acc: List<&2, Row>, r: Row & List<&2, U32>) -> List<&2, Row> & List<&2, U32>:
  (x, t) = r
  (Con{x, acc}, t)

def rows.fin(st: List<&2, Row> & List<&2, U32>) -> List<&2, Row>:
  (acc, ts) = st
  List.reverse(&2, Row, acc)

def rows.step(st: List<&2, Row> & List<&2, U32>) -> List<&2, Row> & List<&2, U32>:
  (acc, ts) = st
  rows.add(acc, row.want(take(ts)))

def rows.go(n: Nat, st: List<&2, Row> & List<&2, U32>) -> List<&2, Row>:
  match n:
    case 0n:
      rows.fin(st)
    case 1n+p:
      rows.go(p, rows.step(st))

def rows.n(r: U32 & List<&2, U32>) -> List<&2, Row>:
  (+n, ts) = r
  rows.go(U32.to_nat(n), (Nil{}, ts))

# a file's rows, from its bytes
def rows(bs: List<&2, U32>) -> List<&2, Row>:
  rows.n(take(nums.go(bs, 0, False{}, Nil{})))
