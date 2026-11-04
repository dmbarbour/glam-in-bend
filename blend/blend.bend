import Base

# Blend: static objects for Bend (blend/README.md; the plan,
# docs/plans/Blend_2026-11-04.md). This first step reads a `.blend` file
# into its structure (`blend-read`):
#
#   bend blend.bend read FILE.blend    the structure, one item a line,
#                                      each body's names under it
#
# Bend has no mutual recursion, so the source is read in two passes: the
# lines into a flat list of items, each with its line and indentation (an
# import, an object's header, a declaration, a definition's header with
# its body's lines), then the items into a tree, objects nesting by
# indentation, a stack of the objects being read; each body's lines become
# Bend's tokens as its definition joins the tree. A line Blend cannot read
# is kept as such (`?` when printed), for a later step to report: reading
# never fails. Loops that would call each other are written as one loop
# over a state record, a step function deciding each turn, on fuel.

# Text
# ====
#
# Source text is a list of byte codes, made a String only for output.

def codes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Con{Char.to_u32(c), codes(t)}

def text(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{+h, t}:
      SCon{Char.from_u32(h), text(t)}

# whether xs begins with p
def starts(xs: List<&2, U32>, p: List<&2, U32>) -> Bool:
  match xs p:
    case _ Nil{}:
      True{}
    case Nil{} Con{ph, pt}:
      False{}
    case Con{+xh, xt} Con{+ph, pt}:
      U32.is_eq(xh, ph) && starts(xt, pt)

def same(xs: List<&2, U32>, p: List<&2, U32>) -> Bool:
  match xs p:
    case Nil{} Nil{}:
      True{}
    case Con{+xh, xt} Con{+ph, pt}:
      U32.is_eq(xh, ph) && same(xt, pt)
    case _ _:
      False{}

def drop(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+k:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          drop(k, t)

# xs without its leading spaces, and how many there were
def ltrim.go(xs: List<&2, U32>, +n: U32) -> U32 & List<&2, U32>:
  match xs:
    case Nil{}:
      (n, Nil{})
    case Con{+h, t}:
      match h:
        case 32:
          ltrim.go(t, (n + 1 : U32))
        case _:
          (n, Con{h, t})

def ltrim.fin(r: U32 & List<&2, U32>) -> List<&2, U32>:
  (+n, xs) = r
  xs

def ltrim(xs: List<&2, U32>) -> List<&2, U32>:
  ltrim.fin(ltrim.go(xs, 0))

# xs without its trailing spaces
def rtrim(xs: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, ltrim(List.reverse(&2, U32, xs)))

def trim(xs: List<&2, U32>) -> List<&2, U32>:
  rtrim(ltrim(xs))

# whether each of xs is c
def eqs(xs: List<&2, U32>, +c: U32) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{U32.is_eq(h, c), eqs(t, c)}

def until.go(xs: List<&2, U32>, bs: List<&2, Bool>, acc: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match xs bs:
    case Con{+h, t} Con{+b, bt}:
      match b:
        case True{}:
          (List.reverse(&2, U32, acc), t)
        case False{}:
          until.go(t, bt, Con{h, acc})
    case _ _:
      (List.reverse(&2, U32, acc), Nil{})

# xs up to the first c, and what follows it (c dropped)
def until(+xs: List<&2, U32>, +c: U32) -> List<&2, U32> & List<&2, U32>:
  until.go(xs, eqs(xs, c), Nil{})

# xs split at its commas outside any bracket, each part trimmed
def commas.add(x: List<&2, U32>, out: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match x:
    case Nil{}:
      out
    case Con{h, t}:
      Con{Con{h, t}, out}

def commas.end(cur: List<&2, U32>, out: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  commas.add(trim(List.reverse(&2, U32, cur)), out)

# a closer at depth 0 leaves it there: the text is Bend's to judge
def depth.dec(+d: U32) -> U32:
  match d:
    case 0:
      0
    case _:
      (d - 1 : U32)

# a `>` after `-` is an arrow, not a bracket
def depth.gt(+prev: U32, +d: U32) -> U32:
  match prev:
    case 45:
      d
    case _:
      depth.dec(d)

# the bracket depth after h, prev the byte before it
def depth.next(+prev: U32, +h: U32, +d: U32) -> U32:
  match h:
    case 40:
      (d + 1 : U32)
    case 60:
      (d + 1 : U32)
    case 123:
      (d + 1 : U32)
    case 91:
      (d + 1 : U32)
    case 41:
      depth.dec(d)
    case 62:
      depth.gt(prev, d)
    case 125:
      depth.dec(d)
    case 93:
      depth.dec(d)
    case _:
      d

type Cs is Type:
  Cs{xs: List<&2, U32>, +prev: U32, +depth: U32, cur: List<&2, U32>, out: List<&2, List<&2, U32>>}

def commas.c(+split: Bool, +h: U32, t: List<&2, U32>, +prev: U32, +depth: U32, cur: List<&2, U32>, out: List<&2, List<&2, U32>>) -> Cs:
  match split:
    case True{}:
      Cs{t, h, depth, Nil{}, commas.end(cur, out)}
    case False{}:
      Cs{t, h, depth.next(prev, h, depth), Con{h, cur}, out}

def commas.step(s: Cs) -> Cs:
  match s:
    case Cs{xs, +prev, +depth, cur, out}:
      match xs:
        case Nil{}:
          Cs{Nil{}, prev, depth, cur, out}
        case Con{+h, t}:
          commas.c(U32.is_eq(h, 44) && U32.is_eq(depth, 0), h, t, prev, depth, cur, out)

def commas.go(n: Nat, s: Cs) -> List<&2, List<&2, U32>>:
  match n:
    case 0n:
      match s:
        case Cs{xs, +prev, +depth, cur, out}:
          List.reverse(&2, List<&2, U32>, commas.end(cur, out))
    case 1n+k:
      commas.go(k, commas.step(s))

def commas(+xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  commas.go(List.length(&2, U32, xs), Cs{xs, 0, 0, Nil{}, Nil{}})

# Lines
# =====

# a line of the source: its number, its indentation, its text after it;
# a carriage return dropped wherever it is
type Ln is Data:
  Ln{+no: U32, +ind: U32, txt: List<&2, U32>}

def lines.fin(r: U32 & List<&2, U32>, +no: U32) -> Ln:
  (+n, xs) = r
  Ln{no, n, xs}

def lines.line(cur: List<&2, U32>, +no: U32) -> Ln:
  lines.fin(ltrim.go(List.reverse(&2, U32, cur), 0), no)

def lines.go(bs: List<&2, U32>, cur: List<&2, U32>, +no: U32, out: List<&2, Ln>) -> List<&2, Ln>:
  match bs:
    case Nil{}:
      List.reverse(&2, Ln, Con{lines.line(cur, no), out})
    case Con{+b, t}:
      match b:
        case 10:
          lines.go(t, Nil{}, (no + 1 : U32), Con{lines.line(cur, no), out})
        case 13:
          lines.go(t, cur, no, out)
        case _:
          lines.go(t, Con{b, cur}, no, out)

def lines(bs: List<&2, U32>) -> List<&2, Ln>:
  lines.go(bs, Nil{}, 1, Nil{})

def blank(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

def comment(xs: List<&2, U32>) -> Bool:
  starts(xs, codes("#"))

# Tokens
# ======
#
# A body's lines as Bend's tokens, so that its references can be found and
# rewritten while the rest passes through as written: a name, the dots
# within it and its mark (`_` begins a name; `^`, `^^` and `~` are kept
# with the name they mark); a number with its suffix (`0n`); a string or a
# char; a comment, the rest of its line; a run of spaces; any other byte
# alone.

type Tok is Data:
  TName{txt: List<&2, U32>}
  TNum{txt: List<&2, U32>}
  TStr{txt: List<&2, U32>}
  TCom{txt: List<&2, U32>}
  TSp{txt: List<&2, U32>}
  TSym{+c: U32}

# a body's line: its number, its indentation, its tokens
type Bl is Data:
  Bl{+no: U32, +ind: U32, toks: List<&2, Tok>}

# a byte's class: 0 a space, 1 a letter or `_`, 2 a digit, 3 `.`, 4 `"`,
# 5 `#`, 6 `^`, 7 `~`, 8 a backslash, 9 any other, 10 `'`
def cls.of(+alpha: Bool, +digit: Bool, +h: U32) -> U32:
  match alpha digit:
    case True{} _:
      1
    case False{} True{}:
      2
    case False{} False{}:
      match h:
        case 32:
          0
        case 9:
          0
        case 95:
          1
        case 46:
          3
        case 34:
          4
        case 35:
          5
        case 94:
          6
        case 126:
          7
        case 92:
          8
        case 39:
          10
        case _:
          9

def cls(+h: U32) -> U32:
  cls.of((U32.is_ge(h, 65) && U32.is_le(h, 90)) || (U32.is_ge(h, 97) && U32.is_le(h, 122)),
    U32.is_ge(h, 48) && U32.is_le(h, 57), h)

def classes(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{cls(h), classes(t)}

def name.rest(cs: List<&2, U32>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      match c:
        case 1:
          name.rest(t)
        case 2:
          name.rest(t)
        case 3:
          name.rest(t)
        case _:
          False{}

def name.first(cs: List<&2, U32>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{+c, t}:
      match c:
        case 1:
          name.rest(t)
        case _:
          False{}

# a name as Bend's: a letter or `_`, then letters, digits, `_` and `.`
def name.ok(xs: List<&2, U32>) -> Bool:
  name.first(classes(xs))

def names.ok(ns: List<&2, List<&2, U32>>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{n, t}:
      name.ok(n) && names.ok(t)

# a run read: its bytes, reversed, and the bytes after it with their classes
type Rn is Type:
  Rn{acc: List<&2, U32>, xs: List<&2, U32>, cs: List<&2, U32>}

# a name's rest: letters, digits, `_` and `.`
def run.name(xs: List<&2, U32>, cs: List<&2, U32>, acc: List<&2, U32>) -> Rn:
  match xs cs:
    case Con{+h, t} Con{+c, ct}:
      match c:
        case 1:
          run.name(t, ct, Con{h, acc})
        case 2:
          run.name(t, ct, Con{h, acc})
        case 3:
          run.name(t, ct, Con{h, acc})
        case _:
          Rn{acc, Con{h, t}, Con{c, ct}}
    case _ _:
      Rn{acc, Nil{}, Nil{}}

# a number's rest: digits and letters, its suffix among them
def run.num(xs: List<&2, U32>, cs: List<&2, U32>, acc: List<&2, U32>) -> Rn:
  match xs cs:
    case Con{+h, t} Con{+c, ct}:
      match c:
        case 1:
          run.num(t, ct, Con{h, acc})
        case 2:
          run.num(t, ct, Con{h, acc})
        case _:
          Rn{acc, Con{h, t}, Con{c, ct}}
    case _ _:
      Rn{acc, Nil{}, Nil{}}

# a run of spaces
def run.sp(xs: List<&2, U32>, cs: List<&2, U32>, acc: List<&2, U32>) -> Rn:
  match xs cs:
    case Con{+h, t} Con{+c, ct}:
      match c:
        case 0:
          run.sp(t, ct, Con{h, acc})
        case _:
          Rn{acc, Con{h, t}, Con{c, ct}}
    case _ _:
      Rn{acc, Nil{}, Nil{}}

# a run of `^`
def run.carets(xs: List<&2, U32>, cs: List<&2, U32>, acc: List<&2, U32>) -> Rn:
  match xs cs:
    case Con{+h, t} Con{+c, ct}:
      match c:
        case 6:
          run.carets(t, ct, Con{h, acc})
        case _:
          Rn{acc, Con{h, t}, Con{c, ct}}
    case _ _:
      Rn{acc, Nil{}, Nil{}}

# a string's rest, to its closing quote; esc, a backslash read before
def run.str(xs: List<&2, U32>, cs: List<&2, U32>, acc: List<&2, U32>, +esc: Bool) -> Rn:
  match xs cs:
    case Con{+h, t} Con{+c, ct}:
      match c:
        case 4:
          match esc:
            case True{}:
              run.str(t, ct, Con{h, acc}, False{})
            case False{}:
              Rn{Con{h, acc}, t, ct}
        case 8:
          run.str(t, ct, Con{h, acc}, Bool.not(esc))
        case _:
          run.str(t, ct, Con{h, acc}, False{})
    case _ _:
      Rn{acc, Nil{}, Nil{}}

# a char's rest, to its closing quote, as a string's
def run.chr(xs: List<&2, U32>, cs: List<&2, U32>, acc: List<&2, U32>, +esc: Bool) -> Rn:
  match xs cs:
    case Con{+h, t} Con{+c, ct}:
      match c:
        case 10:
          match esc:
            case True{}:
              run.chr(t, ct, Con{h, acc}, False{})
            case False{}:
              Rn{Con{h, acc}, t, ct}
        case 8:
          run.chr(t, ct, Con{h, acc}, Bool.not(esc))
        case _:
          run.chr(t, ct, Con{h, acc}, False{})
    case _ _:
      Rn{acc, Nil{}, Nil{}}

# the name after a run of `^`
def run.host(r: Rn) -> Rn:
  match r:
    case Rn{acc, xs, cs}:
      run.name(xs, cs, acc)

type Tk is Type:
  Tk{xs: List<&2, U32>, cs: List<&2, U32>, out: List<&2, Tok>}

def tok.make(+k: U32, txt: List<&2, U32>) -> Tok:
  match k:
    case 0:
      TSp{txt}
    case 1:
      TName{txt}
    case 2:
      TNum{txt}
    case _:
      TStr{txt}

def tok.add(r: Rn, +k: U32, out: List<&2, Tok>) -> Tk:
  match r:
    case Rn{acc, xs, cs}:
      Tk{xs, cs, Con{tok.make(k, List.reverse(&2, U32, acc)), out}}

def tok.step(s: Tk) -> Tk:
  match s:
    case Tk{xs, cs, out}:
      match xs cs:
        case Con{+h, t} Con{+c, ct}:
          match c:
            case 0:
              tok.add(run.sp(t, ct, Con{h, Nil{}}), 0, out)
            case 1:
              tok.add(run.name(t, ct, Con{h, Nil{}}), 1, out)
            case 2:
              tok.add(run.num(t, ct, Con{h, Nil{}}), 2, out)
            case 4:
              tok.add(run.str(t, ct, Con{h, Nil{}}, False{}), 4, out)
            case 5:
              Tk{Nil{}, Nil{}, Con{TCom{Con{h, t}}, out}}
            case 6:
              tok.add(run.host(run.carets(t, ct, Con{h, Nil{}})), 1, out)
            case 7:
              tok.add(run.name(t, ct, Con{h, Nil{}}), 1, out)
            case 10:
              tok.add(run.chr(t, ct, Con{h, Nil{}}, False{}), 4, out)
            case _:
              Tk{t, ct, Con{TSym{h}, out}}
        case _ _:
          Tk{Nil{}, Nil{}, out}

# fuel: the line's length, as each step takes a byte at least
def tok.go(n: Nat, s: Tk) -> List<&2, Tok>:
  match n:
    case 0n:
      match s:
        case Tk{xs, cs, out}:
          List.reverse(&2, Tok, out)
    case 1n+k:
      tok.go(k, tok.step(s))

def toks(+xs: List<&2, U32>) -> List<&2, Tok>:
  tok.go(List.length(&2, U32, xs), Tk{xs, classes(xs), Nil{}})

def toks.lines(ls: List<&2, Ln>) -> List<&2, Bl>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Ln{+no, +ind, +txt}:
          Con{Bl{no, ind, toks(txt)}, toks.lines(t)}

# Items
# =====

# sharing: 0 affine, the default; 1 shared; 2 copied
type Item is Data:
  IImport{txt: List<&2, U32>, +no: U32, +ind: U32}
  IObj{+abs: Bool, name: List<&2, U32>, parents: List<&2, List<&2, U32>>, +no: U32, +ind: U32}
  IDecl{names: List<&2, List<&2, U32>>, +no: U32, +ind: U32}
  IDef{+share: U32, +upd: Bool, name: List<&2, U32>, rest: List<&2, U32>, params: List<&2, List<&2, U32>>, body: List<&2, Ln>, +no: U32, +ind: U32}
  IBad{txt: List<&2, U32>, +no: U32, +ind: U32}

# a parameter's name: its marks (+ - ~ @) dropped, up to its colon; a
# template's (~) or an erased one's (-) marked by a leading ~ kept
def param.first(r: List<&2, U32> & List<&2, U32>) -> List<&2, U32>:
  (nm, rest) = r
  trim(nm)

def param.plain(p: List<&2, U32>) -> List<&2, U32>:
  param.first(until(p, 58))

def param.m(+h: U32, t: List<&2, U32>) -> List<&2, U32>:
  match h:
    case 43:
      param.plain(t)
    case 64:
      param.plain(t)
    case 126:
      Con{126, param.plain(t)}
    case 45:
      Con{126, param.plain(t)}
    case _:
      param.plain(Con{h, t})

def param.name(p: List<&2, U32>) -> List<&2, U32>:
  match p:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      param.m(h, t)

def params.go(ps: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{param.name(p), params.go(t)}

# the parameter list between a header's first parenthesis and its match
type Ps is Type:
  Ps{xs: List<&2, U32>, +prev: U32, +depth: U32, acc: List<&2, U32>, +done: Bool}

def parens.c(+close: Bool, +h: U32, t: List<&2, U32>, +prev: U32, +depth: U32, acc: List<&2, U32>) -> Ps:
  match close:
    case True{}:
      Ps{t, h, depth, acc, True{}}
    case False{}:
      Ps{t, h, depth.next(prev, h, depth), Con{h, acc}, False{}}

def parens.step(s: Ps) -> Ps:
  match s:
    case Ps{xs, +prev, +depth, acc, +done}:
      match xs done:
        case _ True{}:
          Ps{xs, prev, depth, acc, True{}}
        case Nil{} False{}:
          Ps{Nil{}, prev, depth, acc, True{}}
        case Con{+h, t} False{}:
          parens.c(U32.is_eq(h, 41) && U32.is_eq(depth, 0), h, t, prev, depth, acc)

def parens.go(n: Nat, s: Ps) -> List<&2, U32>:
  match n:
    case 0n:
      match s:
        case Ps{xs, +prev, +depth, acc, +done}:
          List.reverse(&2, U32, acc)
    case 1n+k:
      parens.go(k, parens.step(s))

def parens(+xs: List<&2, U32>) -> List<&2, U32>:
  parens.go(List.length(&2, U32, xs), Ps{xs, 0, 0, Nil{}, False{}})

def def.named(+ok: Bool, name: List<&2, U32>, +rest: List<&2, U32>, xs: List<&2, U32>, +share: U32, +upd: Bool, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  match ok:
    case True{}:
      IDef{share, upd, name, Con{40, rest}, params.go(commas(parens(rest))), body, no, ind}
    case False{}:
      IBad{xs, no, ind}

# a name, then its parameters: the parenthesis found
def def.r(r: List<&2, U32> & List<&2, U32>, xs: List<&2, U32>, +share: U32, +upd: Bool, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  (+name, +rest) = r
  def.named(name.ok(trim(name)) && Bool.not(blank(rest)), trim(name), rest, xs, share, upd, body, no, ind)

# after `def ` or `upd `: the name up to its parenthesis, the rest kept
def def.item(+xs: List<&2, U32>, +share: U32, +upd: Bool, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  def.r(until(xs, 40), xs, share, upd, body, no, ind)

def def.kw.d(+d: Bool, +u: Bool, xs: List<&2, U32>, +share: U32, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  match d u:
    case True{} _:
      def.item(drop(4n, xs), share, False{}, body, no, ind)
    case False{} True{}:
      def.item(drop(4n, xs), share, True{}, body, no, ind)
    case False{} False{}:
      IBad{xs, no, ind}

def def.kw(+xs: List<&2, U32>, +share: U32, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  def.kw.d(starts(xs, codes("def ")), starts(xs, codes("upd ")), xs, share, body, no, ind)

def def.share.s(+s: Bool, +c: Bool, xs: List<&2, U32>, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  match s c:
    case True{} _:
      def.kw(drop(7n, xs), 1, body, no, ind)
    case False{} True{}:
      def.kw(drop(7n, xs), 2, body, no, ind)
    case False{} False{}:
      def.kw(xs, 0, body, no, ind)

# a definition's header, its sharing first if stated
def def.share(+xs: List<&2, U32>, body: List<&2, Ln>, +no: U32, +ind: U32) -> Item:
  def.share.s(starts(xs, codes("shared ")), starts(xs, codes("copied ")), xs, body, no, ind)

def is_def(+xs: List<&2, U32>) -> Bool:
  starts(xs, codes("def ")) || starts(xs, codes("upd ")) || starts(xs, codes("shared ")) || starts(xs, codes("copied "))

def obj.with.s(+w: Bool, rx: List<&2, U32>) -> List<&2, U32>:
  match w:
    case True{}:
      drop(5n, rx)
    case False{}:
      rx

def obj.with.r(+rx: List<&2, U32>) -> List<&2, U32>:
  obj.with.s(starts(rx, codes("htiw ")), rx)

# the parents' text, ` with` at its end dropped
def obj.with(xs: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, obj.with.r(List.reverse(&2, U32, xs)))

def obj.parents.e(+e: Bool, rest: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match e:
    case True{}:
      commas(obj.with(drop(8n, rest)))
    case False{}:
      Nil{}

def obj.parents(+rest: List<&2, U32>) -> List<&2, List<&2, U32>>:
  obj.parents.e(starts(rest, codes("extends ")), rest)

def obj.named(+ok: Bool, name: List<&2, U32>, ps: List<&2, List<&2, U32>>, xs: List<&2, U32>, +abs: Bool, +no: U32, +ind: U32) -> Item:
  match ok:
    case True{}:
      IObj{abs, name, ps, no, ind}
    case False{}:
      IBad{xs, no, ind}

# after the name: `with`, or `extends A, B with`, each parent a name
def obj.rest(+rest: List<&2, U32>, +name: List<&2, U32>, xs: List<&2, U32>, +abs: Bool, +no: U32, +ind: U32) -> Item:
  obj.named(name.ok(name) && (same(rest, codes("with")) ||
      (starts(rest, codes("extends ")) && starts(List.reverse(&2, U32, rest), codes("htiw ")) && names.ok(obj.parents(rest)))),
    name, obj.parents(rest), xs, abs, no, ind)

def obj.ext(r: List<&2, U32> & List<&2, U32>, xs: List<&2, U32>, +abs: Bool, +no: U32, +ind: U32) -> Item:
  (name, rest) = r
  obj.rest(rtrim(rest), name, xs, abs, no, ind)

# `object Name [extends A, B] with`, `abstract` before it or not
def obj.item(xs: List<&2, U32>, line: List<&2, U32>, +abs: Bool, +no: U32, +ind: U32) -> Item:
  obj.ext(until(xs, 32), line, abs, no, ind)

def decl.named(+ok: Bool, ns: List<&2, List<&2, U32>>, line: List<&2, U32>, +no: U32, +ind: U32) -> Item:
  match ok:
    case True{}:
      IDecl{ns, no, ind}
    case False{}:
      IBad{line, no, ind}

def decl.some(ns: List<&2, List<&2, U32>>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{n, t}:
      True{}

# `declare a, b`, each a name
def decl.item(+ns: List<&2, List<&2, U32>>, line: List<&2, U32>, +no: U32, +ind: U32) -> Item:
  decl.named(decl.some(ns) && names.ok(ns), ns, line, no, ind)

# a line's body lines: those after it, blank or indented deeper; its
# trailing blank lines left out
type Bd is Type:
  Bd{ls: List<&2, Ln>, +ind: U32, acc: List<&2, Ln>, +done: Bool}

def body.in(+inside: Bool, l: Ln, t: List<&2, Ln>, +ind: U32, acc: List<&2, Ln>) -> Bd:
  match inside:
    case True{}:
      Bd{t, ind, Con{l, acc}, False{}}
    case False{}:
      Bd{Con{l, t}, ind, acc, True{}}

def body.l(l: Ln, t: List<&2, Ln>, +ind: U32, acc: List<&2, Ln>) -> Bd:
  match l:
    case Ln{+no, +li, +txt}:
      body.in(blank(txt) || U32.is_gt(li, ind), Ln{no, li, txt}, t, ind, acc)

def body.step(s: Bd) -> Bd:
  match s:
    case Bd{ls, +ind, acc, +done}:
      match ls done:
        case _ True{}:
          Bd{ls, ind, acc, True{}}
        case Nil{} False{}:
          Bd{Nil{}, ind, acc, True{}}
        case Con{l, t} False{}:
          body.l(l, t, ind, acc)

# the reversed lines' leading blanks dropped
type Tr is Type:
  Tr{rs: List<&2, Ln>, +stop: Bool}

def body.lead(+b: Bool, l: Ln, t: List<&2, Ln>) -> Tr:
  match b:
    case True{}:
      Tr{t, False{}}
    case False{}:
      Tr{Con{l, t}, True{}}

def body.blank1(rs: List<&2, Ln>) -> Tr:
  match rs:
    case Nil{}:
      Tr{Nil{}, True{}}
    case Con{l, t}:
      match l:
        case Ln{+no, +ind, +txt}:
          body.lead(blank(txt), Ln{no, ind, txt}, t)

def body.trim.go(n: Nat, r: Tr) -> List<&2, Ln>:
  match n r:
    case 0n Tr{rs, +stop}:
      rs
    case 1n+k Tr{rs, +stop}:
      match stop:
        case True{}:
          rs
        case False{}:
          body.trim.go(k, body.blank1(rs))

def body.trim(+ls: List<&2, Ln>) -> List<&2, Ln>:
  List.reverse(&2, Ln, body.trim.go(List.length(&2, Ln, ls), Tr{List.reverse(&2, Ln, ls), False{}}))

def body.go(n: Nat, s: Bd) -> List<&2, Ln> & List<&2, Ln>:
  match n:
    case 0n:
      match s:
        case Bd{ls, +ind, acc, +done}:
          (List.reverse(&2, Ln, acc), ls)
    case 1n+k:
      body.go(k, body.step(s))

# The flat pass
# -------------

type Fl is Type:
  Fl{ls: List<&2, Ln>, out: List<&2, Item>}

def flat.def(r: List<&2, Ln> & List<&2, Ln>, txt: List<&2, U32>, +no: U32, +ind: U32, out: List<&2, Item>) -> Fl:
  (body, rest) = r
  Fl{rest, Con{def.share(txt, body.trim(body), no, ind), out}}

def flat.k(+skip: Bool, +imp: Bool, +abs: Bool, +obj: Bool, +decl: Bool, +df: Bool, +txt: List<&2, U32>, +no: U32, +ind: U32, t: List<&2, Ln>, out: List<&2, Item>, +k: Nat) -> Fl:
  match skip imp abs obj decl df:
    case True{} _ _ _ _ _:
      Fl{t, out}
    case False{} True{} _ _ _ _:
      Fl{t, Con{IImport{txt, no, ind}, out}}
    case False{} False{} True{} _ _ _:
      Fl{t, Con{obj.item(drop(16n, txt), txt, True{}, no, ind), out}}
    case False{} False{} False{} True{} _ _:
      Fl{t, Con{obj.item(drop(7n, txt), txt, False{}, no, ind), out}}
    case False{} False{} False{} False{} True{} _:
      Fl{t, Con{decl.item(commas(drop(8n, txt)), txt, no, ind), out}}
    case False{} False{} False{} False{} False{} True{}:
      flat.def(body.go(k, Bd{t, ind, Nil{}, False{}}), txt, no, ind, out)
    case False{} False{} False{} False{} False{} False{}:
      Fl{t, Con{IBad{txt, no, ind}, out}}

def flat.kind(+txt: List<&2, U32>, +no: U32, +ind: U32, t: List<&2, Ln>, out: List<&2, Item>, +k: Nat) -> Fl:
  flat.k(blank(txt) || comment(txt), starts(txt, codes("import ")), starts(txt, codes("abstract object ")),
    starts(txt, codes("object ")), starts(txt, codes("declare ")), is_def(txt), txt, no, ind, t, out, k)

def flat.step(s: Fl, +k: Nat) -> Fl:
  match s:
    case Fl{ls, out}:
      match ls:
        case Nil{}:
          Fl{Nil{}, out}
        case Con{l, t}:
          match l:
            case Ln{+no, +ind, txt}:
              flat.kind(txt, no, ind, t, out, k)

# the items, a line read at least each step, as many steps as lines
def flat.go(n: Nat, +k: Nat, s: Fl) -> List<&2, Item>:
  match n:
    case 0n:
      match s:
        case Fl{ls, out}:
          List.reverse(&2, Item, out)
    case 1n+m:
      flat.go(m, k, flat.step(s, k))

def flat(+ls: List<&2, Ln>) -> List<&2, Item>:
  flat.go(List.length(&2, Ln, ls), List.length(&2, Ln, ls), Fl{ls, Nil{}})

# The tree
# --------

type Node is Data:
  NImport{txt: List<&2, U32>, +no: U32}
  NDecl{names: List<&2, List<&2, U32>>, +no: U32}
  NDef{+share: U32, +upd: Bool, name: List<&2, U32>, rest: List<&2, U32>, params: List<&2, List<&2, U32>>, body: List<&2, Bl>, +no: U32}
  NObj{+abs: Bool, name: List<&2, U32>, parents: List<&2, List<&2, U32>>, kids: List<&2, Node>, +no: U32}
  NBad{txt: List<&2, U32>, +no: U32}

# an object being read: its header and its members so far, reversed; the
# module is the frame at the stack's bottom, never closed
type Fr is Data:
  Fr{+top: Bool, +ind: U32, +abs: Bool, name: List<&2, U32>, parents: List<&2, List<&2, U32>>, kids: List<&2, Node>, +no: U32}

def fr.add(f: Fr, n: Node) -> Fr:
  match f:
    case Fr{+top, +ind, +abs, name, parents, kids, +no}:
      Fr{top, ind, abs, name, parents, Con{n, kids}, no}

def fr.node(f: Fr) -> Node:
  match f:
    case Fr{+top, +ind, +abs, name, parents, kids, +no}:
      NObj{abs, name, parents, List.reverse(&2, Node, kids), no}

def fr.closes(f: Fr, +i: U32) -> Bool & Fr:
  match f:
    case Fr{+top, +ind, +abs, name, parents, kids, +no}:
      (Bool.not(top) && U32.is_ge(ind, i), Fr{top, ind, abs, name, parents, kids, no})

def close.into(st: List<&2, Fr>, n: Node) -> List<&2, Fr>:
  match st:
    case Nil{}:
      Nil{}
    case Con{f, rest}:
      Con{fr.add(f, n), rest}

type Cl is Type:
  Cl{st: List<&2, Fr>, +i: U32, +done: Bool}

def close.f(r: Bool & Fr, rest: List<&2, Fr>, +i: U32) -> Cl:
  (+c, f) = r
  match c:
    case True{}:
      Cl{close.into(rest, fr.node(f)), i, False{}}
    case False{}:
      Cl{Con{f, rest}, i, True{}}

def close.step(s: Cl) -> Cl:
  match s:
    case Cl{st, +i, +done}:
      match st done:
        case _ True{}:
          Cl{st, i, True{}}
        case Nil{} False{}:
          Cl{Nil{}, i, True{}}
        case Con{f, rest} False{}:
          close.f(fr.closes(f, i), rest, i)

# objects closed while the top one starts at or right of column i
def close.go(n: Nat, s: Cl) -> List<&2, Fr>:
  match n:
    case 0n:
      match s:
        case Cl{st, +i, +done}:
          st
    case 1n+k:
      close.go(k, close.step(s))

def close(+st: List<&2, Fr>, +i: U32) -> List<&2, Fr>:
  close.go(List.length(&2, Fr, st), Cl{st, i, False{}})

def item.ind(it: Item) -> U32 & Item:
  match it:
    case IImport{txt, +no, +ind}:
      (ind, IImport{txt, no, ind})
    case IObj{+abs, name, parents, +no, +ind}:
      (ind, IObj{abs, name, parents, no, ind})
    case IDecl{names, +no, +ind}:
      (ind, IDecl{names, no, ind})
    case IDef{+share, +upd, name, rest, params, body, +no, +ind}:
      (ind, IDef{share, upd, name, rest, params, body, no, ind})
    case IBad{txt, +no, +ind}:
      (ind, IBad{txt, no, ind})

def tree.put(st: List<&2, Fr>, it: Item) -> List<&2, Fr>:
  match it:
    case IImport{txt, +no, +ind}:
      close.into(st, NImport{txt, no})
    case IObj{+abs, name, parents, +no, +ind}:
      Con{Fr{False{}, ind, abs, name, parents, Nil{}, no}, st}
    case IDecl{names, +no, +ind}:
      close.into(st, NDecl{names, no})
    case IDef{+share, +upd, name, rest, params, body, +no, +ind}:
      close.into(st, NDef{share, upd, name, rest, params, toks.lines(body), no})
    case IBad{txt, +no, +ind}:
      close.into(st, NBad{txt, no})

def tree.item(r: U32 & Item, st: List<&2, Fr>) -> List<&2, Fr>:
  (+i, it) = r
  tree.put(close(st, i), it)

def tree.go(its: List<&2, Item>, st: List<&2, Fr>) -> List<&2, Fr>:
  match its:
    case Nil{}:
      close(st, 0)
    case Con{it, t}:
      tree.go(t, tree.item(item.ind(it), st))

def tree.fin(st: List<&2, Fr>) -> List<&2, Node>:
  match st:
    case Nil{}:
      Nil{}
    case Con{f, rest}:
      match f:
        case Fr{+top, +ind, +abs, name, parents, kids, +no}:
          List.reverse(&2, Node, kids)

# the module's members, its objects nested
def tree(its: List<&2, Item>) -> List<&2, Node>:
  tree.fin(tree.go(its, [Fr{True{}, 0, False{}, Nil{}, Nil{}, Nil{}, 0}]))

def read(bs: List<&2, U32>) -> List<&2, Node>:
  tree(flat(lines(bs)))

# The structure, printed
# ======================

def show.names(ns: List<&2, List<&2, U32>>) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{n, t}:
      match t:
        case Nil{}:
          text(n)
        case Con{h, r}:
          text(n) ++ ", " ++ show.names(Con{h, r})

def show.share(+s: U32) -> String:
  match s:
    case 1:
      "shared "
    case 2:
      "copied "
    case _:
      ""

def show.kw(+u: Bool) -> String:
  match u:
    case True{}:
      "upd "
    case False{}:
      "def "

def show.abs(+a: Bool) -> String:
  match a:
    case True{}:
      "abstract object "
    case False{}:
      "object "

def show.ext(ps: List<&2, List<&2, U32>>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{p, t}:
      " extends " ++ show.names(Con{p, t})

# the names a body's tokens hold, in order, as found
def show.toks(ts: List<&2, Tok>, rest: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      rest
    case Con{tk, t}:
      match tk:
        case TName{txt}:
          Con{txt, show.toks(t, rest)}
        case _:
          show.toks(t, rest)

def show.uses(bs: List<&2, Bl>) -> List<&2, List<&2, U32>>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      match b:
        case Bl{+no, +ind, ts}:
          show.toks(ts, show.uses(t))

def show.used(ns: List<&2, List<&2, U32>>, ind: String) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{n, t}:
      ind ++ "  uses " ++ show.names(Con{n, t}) ++ "\n"

def show.line(+no: U32) -> String:
  "  (line " ++ U32.show(no) ++ ")"

# the tree, an item a line, members indented under their object; fuel,
# the items' count, as the walk enters a member list from its object
def show.go(n: Nat, ns: List<&2, Node>, +ind: String) -> String:
  match n:
    case 0n:
      ""
    case 1n++k:
      match ns:
        case Nil{}:
          ""
        case Con{nd, t}:
          match nd:
            case NImport{txt, +no}:
              ind ++ text(txt) ++ show.line(no) ++ "\n" ++ show.go(k, t, ind)
            case NDecl{names, +no}:
              ind ++ "declare " ++ show.names(names) ++ show.line(no) ++ "\n" ++ show.go(k, t, ind)
            case NDef{+share, +upd, name, rest, params, +body, +no}:
              ind ++ show.share(share) ++ show.kw(upd) ++ text(name) ++ " [" ++ show.names(params) ++ "], " ++
                U32.show(U32.from_nat(List.length(&2, Bl, body))) ++ " body lines" ++ show.line(no) ++ "\n" ++
                show.used(show.uses(body), ind) ++ show.go(k, t, ind)
            case NObj{+abs, name, parents, kids, +no}:
              ind ++ show.abs(abs) ++ text(name) ++ show.ext(parents) ++ show.line(no) ++ "\n" ++
                show.go(k, kids, ind ++ "  ") ++ show.go(k, t, ind)
            case NBad{txt, +no}:
              ind ++ "? " ++ text(txt) ++ show.line(no) ++ "\n" ++ show.go(k, t, ind)

def show(ns: List<&2, Node>, +n: Nat) -> String:
  show.go(n, ns, "")

# The command line
# ================

def run(+bs: List<&2, U32>) -> String:
  show(read(bs), List.length(&2, U32, bs))

def main.read(fr: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Unit):
  (f, r) = fr
  match r:
    case Done{bs}:
      do IO<Unit>:
        File.close(f)
        IO.print(run(bs))
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print("blend: cannot read the file")

def main.size(fs: File & Result<&1, &1, U32 & String, U32>) -> IO(Unit):
  (f, r) = fs
  match r:
    case Done{+n}:
      do IO<Unit>:
        fr : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, n)
        main.read(fr)
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print("blend: cannot size the file")

def main.file(path: String) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "r"))
    fs : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    main.size(fs)

def usage() -> String:
  "usage: bend blend.bend read FILE.blend"

def main.flag(+read: Bool, xs: List<String>) -> IO(Unit):
  match read xs:
    case True{} Con{path, r}:
      main.file(path)
    case _ _:
      IO.print(usage())

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{p, r}:
      match r:
        case Con{+flag, r2}:
          main.flag(String.eq(flag, "read"), r2)
        case Nil{}:
          IO.print(usage())
    case Nil{}:
      IO.print(usage())

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
